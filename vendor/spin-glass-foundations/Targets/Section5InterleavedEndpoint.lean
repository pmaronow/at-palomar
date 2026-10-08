module

public import Targets.Section5MixedCascade
public import Targets.Section5InterleavedOverlaps
public import Targets.Section5InterleavingFilter
public import Targets.CoupledReindex
public import Targets.CoupledCascadeVariance

@[expose] public section

/-!
# Exact removal of zero-variance levels from mixed Gaussian cascades

The list order is outermost first, as in Talagrand's forward indexing. No
growth hypotheses are needed for deletion: a zero increment is the identity
for every input and every mass, including mass zero.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- One actual paired Gaussian operator, using the raw logarithmic-Laplace mass. -/
noncomputable def mixedVectorStep (n : ℕ) (mode : Section5GaussianMode) (m v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  match mode with
  | .independent => AT.gtVectorStep n m (Real.sqrt v) 0
      (AT.gtVectorStep n m 0 (Real.sqrt v) F)
  | .shared => AT.gtVectorStep n m (Real.sqrt v) (Real.sqrt v) F
  | .opposite => AT.gtVectorStep n m (Real.sqrt v) (-Real.sqrt v) F

theorem gtVectorStep_zero_coefficients (n : ℕ) (m : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : AT.gtVectorStep n m 0 0 F = F := by
  funext x y
  by_cases hm : m = 0 <;>
    simp [AT.gtVectorStep, GeneralizedLatala.gaussianProduct, hm]

theorem mixedVectorStep_zero_variance (n : ℕ) (mode : Section5GaussianMode) (m : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : mixedVectorStep n mode m 0 F = F := by
  cases mode <;> simp [mixedVectorStep, gtVectorStep_zero_coefficients]

/-- Mixed operators composed in outermost-first order, retaining source tags. -/
noncomputable def mixedVectorListCascade {α : Type*} (n : ℕ)
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :=
  l.foldr (fun a G => mixedVectorStep n (mode a) (m a) (v a) G) F

theorem mixedVectorListCascade_filter {α : Type*} (n : ℕ)
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (keep : α → Bool) (hzero : ∀ a ∈ l, keep a = false → v a = 0)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m v l F =
      mixedVectorListCascade n mode m v (l.filter keep) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hzero b (List.mem_cons_of_mem a hb))
    cases hk : keep a with
    | false =>
      have hz := hzero a List.mem_cons_self hk
      simpa [mixedVectorListCascade, hk, hz, mixedVectorStep_zero_variance] using ih'
    | true => simpa [mixedVectorListCascade, hk] using
        congrArg (mixedVectorStep n (mode a) (m a) (v a)) ih'

theorem mixedVectorListCascade_map {α γ : Type*} (n : ℕ)
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (f : γ → α) (l : List γ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m v (l.map f) F =
      mixedVectorListCascade n (mode ∘ f) (m ∘ f) (v ∘ f) l F := by
  simp [mixedVectorListCascade, List.foldr_map]

/-- The recursively defined mixed cascade is precisely a reversed-index list
composition. This fixes the direction of all later tag transports. -/
theorem mixedVectorCascade_eq_list (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorCascade n mode m v F j =
      mixedVectorListCascade n mode m v (List.range j).reverse F := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, mixedVectorListCascade, List.foldr_cons]
    change mixedVectorStep n (mode j) (m j) (v j)
      (mixedVectorCascade n mode m v F j) = _
    rw [ih]
    rfl

/-- A suffix of a forward-ordered list matches the genuine bottom-up recursion. -/
theorem mixedVectorListCascade_forward_suffix (n N : ℕ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (L : ℕ) (hL : L ≤ N) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m v (List.ofFn (fun p : Fin L => N - L + p)) F =
      mixedVectorCascade n (fun j => mode (N - 1 - j))
        (fun j => m (N - 1 - j)) (fun j => v (N - 1 - j)) F L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.ofFn_succ]
    change mixedVectorStep n (mode (N - (L + 1) + 0)) (m (N - (L + 1) + 0))
      (v (N - (L + 1) + 0))
      (mixedVectorListCascade n mode m v (List.ofFn (fun p : Fin L => N - (L + 1) + p.succ)) F) = _
    have he : (fun p : Fin L => N - (L + 1) + p.succ) =
        (fun p : Fin L => N - L + p) := by
      funext p
      simp only [Fin.val_succ]
      omega
    rw [he, ih (by omega)]
    simp only [Nat.add_zero, show N - (L + 1) = N - 1 - L by omega]
    rfl

theorem mixedVectorListCascade_forward (n N : ℕ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m v (List.ofFn (fun p : Fin N => p.val)) F =
      mixedVectorCascade n (fun j => mode (N - 1 - j))
        (fun j => m (N - 1 - j)) (fun j => v (N - 1 - j)) F N := by
  simpa only [Nat.sub_self, zero_add] using
    mixedVectorListCascade_forward_suffix n N mode m v N le_rfl F

/-- Only visited mixed levels matter; no assumptions are made about padding. -/
theorem mixedVectorCascade_congr (n : ℕ) (mode mode' : ℕ → Section5GaussianMode)
    (m v m' v' : ℕ → ℝ) (j : ℕ)
    (hmode : ∀ i < j, mode i = mode' i)
    (hm : ∀ i < j, m i = m' i) (hv : ∀ i < j, v i = v' i)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorCascade n mode m v F j = mixedVectorCascade n mode' m' v' F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mixedVectorCascade, hmode j (by omega), hm j (by omega), hv j (by omega),
      ih (fun i hi => hmode i (by omega)) (fun i hi => hm i (by omega))
        (fun i hi => hv i (by omega))]

/-- The mixed recursion specializes to the previously checked one-cut cascade.
The independent case uses the proved Gaussian Fubini bridge, so its growth
hypotheses are retained instead of identifying totalized integrals formally. -/
theorem mixedVectorCascade_eq_fieldCascade (n : ℕ) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) :
    mixedVectorCascade n (fun l => if l < d then .independent else .shared) m v F j =
      coupledFieldCascade n m v d F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mixedVectorCascade, coupledFieldCascade, ih]
    split_ifs with hj
    · funext x y
      exact (independentStepPi_eq_gtVectorSteps (m j) (v j)
        (hF.fieldCascade m v hm hv d j) x y).symm
    · funext x y
      simpa only [show 2 * m j / 2 = m j by ring] using
        (sharedStepPi_eq_gtVectorStep n (2 * m j) (v j)
          (coupledFieldCascade n m v d F j) x y).symm

/-- At each tag only the interpolating variance changes with the second time.
Physical variances stay frozen. The argument `u` is the nonnegative trial overlap. -/
noncomputable def section5TaggedPathVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (j : ℕ) (w : ℝ) : Section5MassTag k → ℝ :=
  Sum.elim (fun p => section5TaggedVariance s β t u j (Sum.inl p))
    (fun p => (1 - w) * section5TaggedVariance s β t u j (Sum.inr p))

theorem section5TaggedPathVariance_zero {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (j : ℕ) :
    section5TaggedPathVariance s β t u j 0 = section5TaggedVariance s β t u j := by
  funext tag
  cases tag <;> simp [section5TaggedPathVariance]

theorem section5TaggedPathVariance_one {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (j : ℕ) (p : Fin (k + 3)) :
    section5TaggedPathVariance s β t u j 1 (Sum.inr p) = 0 := by
  simp [section5TaggedPathVariance]

theorem section5TaggedPathVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u w : ℝ} {j : ℕ} (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w ≤ 1) (tag : Section5MassTag k) :
    0 ≤ section5TaggedPathVariance s β t u j w tag := by
  cases tag with
  | inl p =>
    exact section5TaggedVariance_nonneg s β ht hj hu (Sum.inl p)
  | inr p =>
    exact mul_nonneg (sub_nonneg.mpr hw)
      (section5TaggedVariance_nonneg s β ht hj hu (Sum.inr p))

/-- The actual variance velocity is precisely the cumulative trial increment;
physical tags have zero velocity, regardless of their sharing mode. -/
theorem hasDerivAt_section5TaggedPathVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    (i : Fin ((k + 2) + (k + 3))) (w : ℝ) :
    HasDerivAt (fun w => section5TaggedPathVariance s β t u j w (section5Interleaving s r j i))
      (-(t * β ^ 2 * (section5InterleavedRho s r j u (i + 1) -
        section5InterleavedRho s r j u i))) w := by
  rw [section5InterleavedRho_increment s r hj]
  cases htag : section5Interleaving s r j i with
  | inl p =>
    simpa only [section5TaggedPathVariance, Sum.elim_inl, mul_zero, neg_zero] using
      hasDerivAt_const w (section5TaggedVariance s β t u j (Sum.inl p))
  | inr p =>
    simpa only [section5TaggedPathVariance, section5TaggedVariance, Sum.elim_inr,
      zero_sub, neg_mul, one_mul, mul_assoc] using!
      ((hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id w)).mul_const
        (section5TaggedVariance s β t u j (Sum.inr p))

/-- Every visited variance is positive in the interior or identically zero
as a function of the second interpolation time. -/
theorem section5TaggedPathVariance_pos_or_eq_zero {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u w : ℝ} {j : ℕ} (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w < 1) (tag : Section5MassTag k) :
    0 < section5TaggedPathVariance s β t u j w tag ∨
      ∀ w', section5TaggedPathVariance s β t u j w' tag = 0 := by
  have hv := section5TaggedVariance_nonneg s β ht hj hu tag
  rcases hv.eq_or_lt with hz | hp
  · right
    cases tag <;> intro w' <;> simp [section5TaggedPathVariance, hz.symm]
  · left
    cases tag with
    | inl p => exact hp
    | inr p => exact mul_pos (sub_pos.mpr hw) hp

/-- All interpolating levels disappear exactly at `w = 1`, with no mass,
variance-positivity or distinctness assumptions. -/
theorem section5TaggedPathCascade_one_filter {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β t u : ℝ) (j : ℕ) (mode : Section5MassTag k → Section5GaussianMode)
    (m : Section5MassTag k → ℝ) (l : List (Section5MassTag k))
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m (section5TaggedPathVariance s β t u j 1) l F =
      mixedVectorListCascade n mode m (section5TaggedPathVariance s β t u j 1)
        (l.filter Sum.isLeft) F := by
  apply mixedVectorListCascade_filter
  intro a _ ha
  cases a with
  | inl p => simp at ha
  | inr p => exact section5TaggedPathVariance_one s β t u j p

/-- Physical sharing remains positive even for negative target overlap;
only the interpolating shared coordinates change sign. -/
def section5TaggedMode {k : ℕ} (r j : ℕ) (negative : Bool) :
    Section5MassTag k → Section5GaussianMode :=
  Sum.elim (fun p => if p.val < r then .shared else .independent)
    (fun p => if p.val < j then (if negative then .opposite else .shared) else .independent)

/-- The surviving physical list is exactly the original one-cut field cascade. -/
theorem section5PhysicalList_eq_fieldCascade {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) {t : ℝ} (ht : t ≤ 1) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) :
    mixedVectorListCascade n (fun p => if p < r then .shared else .independent)
      (section5PhysicalMass s r) (fun p => (1 - t) * (β ^ 2 * (s.q (p + 1) - s.q p)))
      (List.ofFn (fun p : Fin (k + 2) => p.val)) F =
      coupledFieldCascade n
        (fun l => if l < k + 2 - r then s.m (k + 1 - l) else s.m (k + 1 - l) / 2)
        (fun l => (1 - t) * (β ^ 2 * (s.q (k + 2 - l) - s.q (k + 1 - l))))
        (k + 2 - r) F (k + 2) := by
  rw [mixedVectorListCascade_forward]
  let M := fun l => if l < k + 2 - r then s.m (k + 1 - l) else s.m (k + 1 - l) / 2
  let V := fun l => (1 - t) * (β ^ 2 * (s.q (k + 2 - l) - s.q (k + 1 - l)))
  have hmode (l : ℕ) : (if k + 2 - 1 - l < r then Section5GaussianMode.shared else .independent) =
      (if l < k + 2 - r then .independent else .shared) := by split_ifs <;> first | rfl | omega
  have hmass (l : ℕ) : section5PhysicalMass s r (k + 2 - 1 - l) = M l := by
    dsimp [section5PhysicalMass, M]
    split_ifs <;> first | rfl | omega
  rw [mixedVectorCascade_congr n _ _ _ _ M V (k + 2)
    (fun l _ => hmode l) (fun l _ => hmass l)
    (fun l hl => by
      dsimp [V]
      rw [show k + 1 - l + 1 = k + 2 - l by omega])]
  apply mixedVectorCascade_eq_fieldCascade
  · intro l
    dsimp [M]
    split_ifs
    · exact s.m_nonneg (by omega)
    · exact div_nonneg (s.m_nonneg (by omega)) (by norm_num)
  · intro l
    exact mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' (k + 2 - l) (by omega) (k + 1 - l) (by omega))))
  · exact hF

/-- The actual merged cascade at `w=1` is the original physical field cascade.
This holds for either sign of the target overlap, without changing physical
sharing or relying on a generic-position assumption. -/
theorem section5InterleavedCascade_one_eq_fieldCascade {k : ℕ} (n : ℕ)
    (s : RSBScheme k) (β u : ℝ) {t : ℝ} (ht : t ≤ 1)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (j : ℕ) (negative : Bool)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) :
    mixedVectorListCascade n (section5TaggedMode r j negative) (section5TaggedMass s r j)
      (section5TaggedPathVariance s β t u j 1) (List.ofFn (section5Interleaving s r j)) F =
      coupledFieldCascade n
        (fun l => if l < k + 2 - r then s.m (k + 1 - l) else s.m (k + 1 - l) / 2)
        (fun l => (1 - t) * (β ^ 2 * (s.q (k + 2 - l) - s.q (k + 1 - l))))
        (k + 2 - r) F (k + 2) := by
  rw [section5TaggedPathCascade_one_filter, section5Interleaving_filter_physical,
    mixedVectorListCascade_map]
  have H := section5PhysicalList_eq_fieldCascade n s β ht hr0 hr hF
  rw [List.ofFn_eq_map, mixedVectorListCascade_map] at H
  exact H

/-- The full interleaved second interpolation with frozen physical fields.
The two signs are encoded only at interpolating shared tags. -/
noncomputable def section5InterleavedInterpolation {Ω : Type*} [MeasureSpace Ω]
    {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r j : ℕ) (t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    mixedVectorListCascade n (section5TaggedMode r j (decide (u < 0)))
      (section5TaggedMass s r j) (section5TaggedPathVariance s β t |u| j w)
      (List.ofFn (section5Interleaving s r j))
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (fun _ => h) (fun _ => h)

/-- Exact original-free-energy endpoint, for either sign and both physical
time endpoints. The merged list has genuinely been integrated and deleted. -/
theorem section5InterleavedInterpolation_one {Ω : Type*} [MeasureSpace Ω]
    {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (j : ℕ) {t : ℝ} (ht : t ≤ 1)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)] :
    section5InterleavedInterpolation n s β h U r j t u 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  unfold section5InterleavedInterpolation constrainedPhi
  simp only [one_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  have hF : CoupledGrowth (constrainedPairFieldBase n (Real.sqrt t • U ω) u) :=
    constrainedPairFieldCascade_growth _ u (fun _ => 0) (fun _ => 0)
      (fun _ => le_rfl) (fun _ => le_rfl) 0 0
  rw [section5InterleavedCascade_one_eq_fieldCascade n s β |u| ht hr0 hr j _ hF]
  let d := k + 2 - r
  let M := fun l => if l < d then s.m (k + 1 - l) else s.m (k + 1 - l) / 2
  let V := fun l => β ^ 2 * (s.q (k + 2 - l) - s.q (k + 1 - l))
  have hv : (fun l => (1 - t) * V l) = fun l => (Real.sqrt (1 - t)) ^ 2 * V l := by
    simp only [Real.sq_sqrt (sub_nonneg.mpr ht)]
  change coupledFieldCascade n M (fun l => (1 - t) * V l) d
    (constrainedPairFieldBase n (Real.sqrt t • U ω) u) (k + 2) (fun _ => h) (fun _ => h) = _
  rw [hv]
  have H := coupledFieldCascade_affine n M V d (k + 2) (Real.sqrt (1 - t)) h
    (Real.sqrt_nonneg _) (constrainedPairFieldBase n (Real.sqrt t • U ω) u) 0 0
  simp only [Pi.zero_apply, mul_zero, zero_add] at H
  rw [H]
  rw [show (fun x y => constrainedPairFieldBase n (Real.sqrt t • U ω) u
    (fun i => Real.sqrt (1 - t) * x i + h) (fun i => Real.sqrt (1 - t) * y i + h)) =
      constrainedBase n (U ω) h t u from funext fun x => funext fun y =>
        (constrainedBase_eq_pairFieldBase n (U ω) h t u x y).symm]
  exact congrFun (congrFun (coupledCascade_eq_fieldCascade n s β d (k + 2) _).symm 0) 0

end SpinGlass.Targets
