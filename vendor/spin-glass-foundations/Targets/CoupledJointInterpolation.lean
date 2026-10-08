module

public import Targets.CoupledVariancePressure
public import Targets.ConstrainedJointTerminal
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-!
# Joint variation of the actual constrained cascade

The checked individual variance derivatives provide finite-profile comparison
bounds. These discharge anchored domination in a direct Fréchet derivative
proof through every actual Gaussian level. The disorder path, all visited
variance coordinates, and both replica fields are differentiated together.
Zero masses and locally constant zero variances are included.

The normalized successor derivative is retained explicitly, before integration
by parts. Passing this simultaneous derivative through the outer disorder
average and identifying its covariance/replica expression remain separate
tasks. Partial derivatives alone are never used to infer joint differentiability.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem constrainedLevelHeatBound_nonneg (n : ℕ) (m : ℕ → ℝ) (d l : ℕ) :
    0 ≤ constrainedLevelHeatBound n m d l := by
  rw [constrainedLevelHeatBound_eq]
  positivity

/-- A single positive variance coordinate is Lipschitz, uniformly in the
disorder and the two fields. The other variances and all masses may vanish. -/
theorem constrainedFieldCascade_variance_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d l j : ℕ) (x y : Fin n → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |coupledFieldCascade n m (Function.update v l a) d (constrainedPairFieldBase n U u)
        (l + 1 + j) x y -
      coupledFieldCascade n m (Function.update v l b) d (constrainedPairFieldBase n U u)
        (l + 1 + j) x y| ≤ constrainedLevelHeatBound n m d l * |a - b| := by
  let F := fun z => coupledFieldCascade n m (Function.update v l z) d
    (constrainedPairFieldBase n U u) (l + 1 + j) x y
  have h := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := F) (C := constrainedLevelHeatBound n m d l)
    (fun z hz => (hasDerivAt_constrainedFieldCascade_variance U u m v hm hv d l j x y hz).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using
      constrainedFieldCascade_variance_deriv_abs_le U u m v hm hv d l j x y hz) hb ha
  simpa only [Real.norm_eq_abs] using h

theorem coupledFieldCascade_congr_variance (m v v' : ℕ → ℝ) (d j : ℕ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (he : ∀ l < j, v l = v' l) :
    coupledFieldCascade n m v d F j = coupledFieldCascade n m v' d F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [coupledFieldCascade, he j (by omega), ih (fun l hl => he l (by omega))]

/-- Simultaneously changing any finite collection of positive variances has
the sum of the single-coordinate bounds. Coordinates left unchanged can be
zero. This is a comparison theorem, not yet a joint derivative theorem. -/
theorem constrainedFieldCascade_variances_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v v' : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hv : ∀ j, 0 ≤ v j) (hv' : ∀ j, 0 ≤ v' j)
    (d j : ℕ) (hface : ∀ l < j, v l = v' l ∨ (0 < v l ∧ 0 < v' l))
    (x y : Fin n → ℝ) :
    |coupledFieldCascade n m v' d (constrainedPairFieldBase n U u) j x y -
      coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y| ≤
      ∑ l ∈ Finset.range j, constrainedLevelHeatBound n m d l * |v' l - v l| := by
  classical
  let V (i l : ℕ) := if l < i then v' l else v l
  let F (w : ℕ → ℝ) := coupledFieldCascade n m w d (constrainedPairFieldBase n U u) j x y
  have hV (i l : ℕ) : 0 ≤ V i l := by
    dsimp [V]
    split_ifs <;> first | exact hv' l | exact hv l
  have H {i : ℕ} (hi : i ≤ j) : |F (V i) - F v| ≤
      ∑ l ∈ Finset.range i, constrainedLevelHeatBound n m d l * |v' l - v l| := by
    induction i with
    | zero => simp [V]
    | succ i ih =>
      have hstep : |F (V (i + 1)) - F (V i)| ≤
          constrainedLevelHeatBound n m d i * |v' i - v i| := by
        have hleft : V (i + 1) = Function.update (V i) i (v' i) := by
          funext l
          by_cases hl : l = i
          · subst l; simp [V]
          · simp only [Function.update_of_ne hl, V,
              show (l < i + 1) = (l < i) by apply propext; omega]
        have hright : V i = Function.update (V i) i (v i) := by
          symm
          apply Function.update_eq_self_iff.mpr
          simp [V]
        rcases hface i (by omega) with he | hp
        · rw [hleft, ← he, ← hright]
          simp
        · have H := constrainedFieldCascade_variance_dist_le U u m (V i) hm (hV i)
            d i (j - (i + 1)) x y hp.2 hp.1
          have hj : i + 1 + (j - (i + 1)) = j := by omega
          rw [hj, ← hleft, ← hright] at H
          exact H
      rw [Finset.sum_range_succ]
      exact (abs_sub_le (F (V (i + 1))) (F (V i)) (F v)).trans
        (by linarith [ih (by omega)])
  have he : F (V j) = F v' := congrFun (congrFun
    (coupledFieldCascade_congr_variance m (V j) v' d j (constrainedPairFieldBase n U u)
      (fun l hl => by simp [V, hl])) x) y
  simpa only [he] using H (i := j) le_rfl

/-- The actual full cascade is one-Lipschitz in the sum of the replica field
norms, with no dependence on the disorder or remaining depth. -/
theorem constrainedFieldCascade_fields_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y x' y' : Fin n → ℝ) :
    |coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y -
      coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x' y'| ≤
      l1 (x - x') + l1 (y - y') := by
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun a _ => (hasDerivAt_constrainedPairCascadeSpatialLine U u m v hm hv d j
      (x - x') (y - y') x' y' a).hasDerivWithinAt)
    (C := l1 (x - x') + l1 (y - y'))
    (fun a _ => by
      simpa only [Real.norm_eq_abs] using
        (constrainedPairCascadeSpatialFirst_abs_le U u m v hm hv d j
          (x - x') (y - y') (x' + a • (x - x')) (y' + a • (y - y'))))
  simpa only [zero_smul, one_smul, add_zero, show x' + (x - x') = x by abel,
    show y' + (y - y') = y by abel, Real.norm_eq_abs] using H

theorem constrainedFieldCascade_joint_dist_le (U U' : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v v' : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hv : ∀ j, 0 ≤ v j) (hv' : ∀ j, 0 ≤ v' j)
    (d j : ℕ) (hface : ∀ l < j, v l = v' l ∨ (0 < v l ∧ 0 < v' l))
    (x y x' y' : Fin n → ℝ) :
    |coupledFieldCascade n m v' d (constrainedPairFieldBase n U' u) j x' y' -
      coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y| ≤
      2 * Fintype.card (Config n) * ‖U' - U‖ +
        (∑ l ∈ Finset.range j, constrainedLevelHeatBound n m d l * |v' l - v l|) +
        l1 (x' - x) + l1 (y' - y) := by
  have h1 := constrainedPairFieldCascade_disorder_dist_le U' U u m v' hm hv' d j x' y'
  have h2 := constrainedFieldCascade_variances_dist_le U u m v v' hm hv hv' d j hface x' y'
  have h3 := constrainedFieldCascade_fields_dist_le U u m v hm hv d j x' y' x y
  have h4 := abs_sub_le
    (coupledFieldCascade n m v' d (constrainedPairFieldBase n U' u) j x' y')
    (coupledFieldCascade n m v' d (constrainedPairFieldBase n U u) j x' y')
    (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y)
  have h5 := abs_sub_le
    (coupledFieldCascade n m v' d (constrainedPairFieldBase n U u) j x' y')
    (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x' y')
    (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y)
  nlinarith [uAbs_le_card_mul_norm n (U' - U)]

/-- Differentiable coefficient paths have the actual field-uniform anchored
bound needed for the joint Gaussian-integral derivative. Zero coordinates
must be locally constant; no derivative at a varying zero variance is used. -/
theorem constrainedFieldCascade_path_anchored_bound
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ a in 𝓝 w, ∀ x y : Fin n → ℝ,
      |coupledFieldCascade n m (fun l => v l a) d (constrainedPairFieldBase n (U a) u) j x y -
        coupledFieldCascade n m (fun l => v l w) d (constrainedPairFieldBase n (U w) u) j x y| ≤
        K * |a - w| := by
  classical
  obtain ⟨CU, hCU, hbU⟩ := hU.isBigO_sub.exists_pos
  have hvl (l : Fin j) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ a in 𝓝 w, |v l a - v l w| ≤ C * |a - w| := by
    obtain ⟨C, hC, hb⟩ := (hv l l.isLt).isBigO_sub.exists_pos
    exact ⟨C, hC, by simpa only [Real.norm_eq_abs] using hb.bound⟩
  choose Cv hCv hbv using hvl
  have hbvs : ∀ᶠ a in 𝓝 w, ∀ l : Fin j, |v l a - v l w| ≤ Cv l * |a - w| :=
    Filter.eventually_all.mpr hbv
  have hf (l : Fin j) : ∀ᶠ a in 𝓝 w,
      v l w = v l a ∨ (0 < v l w ∧ 0 < v l a) := by
    rcases hface l l.isLt with hp | hz
    · filter_upwards [(hv l l.isLt).continuousAt.eventually (lt_mem_nhds hp)] with a ha
      exact Or.inr ⟨hp, ha⟩
    · have hzw := hz.self_of_nhds
      filter_upwards [hz] with a ha
      exact Or.inl (hzw.trans ha.symm)
  let K := 2 * Fintype.card (Config n) * CU +
    ∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l
  refine ⟨K, add_nonneg (by positivity) (Finset.sum_nonneg fun l _ =>
    mul_nonneg (constrainedLevelHeatBound_nonneg n m d l) (hCv l).le), ?_⟩
  filter_upwards [hbU.bound, hbvs, Filter.eventually_all.mpr hf, hnonneg] with a haU hav haf han
  intro x y
  have H := constrainedFieldCascade_joint_dist_le (U w) (U a) u m
    (fun l => v l w) (fun l => v l a) hm hnonneg.self_of_nhds han d j
    (fun l hl => haf ⟨l, hl⟩) x y x y
  simp only [sub_self, l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at H
  rw [← Fin.sum_univ_eq_sum_range] at H
  have hsum : (∑ l : Fin j, constrainedLevelHeatBound n m d l * |v l a - v l w|) ≤
      (∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l) * |a - w| := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hav l)
        (constrainedLevelHeatBound_nonneg n m d l)
  change ‖U a - U w‖ ≤ CU * ‖a - w‖ at haU
  rw [Real.norm_eq_abs] at haU
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_left haU (show 0 ≤ 2 * (Fintype.card (Config n) : ℝ) by positivity)]

private theorem abs_exp_sub_exp_le_of_le {a b R : ℝ} (ha : a ≤ R) (hb : b ≤ R) :
    |Real.exp a - Real.exp b| ≤ Real.exp R * |a - b| := by
  have H := (convex_Iic R).norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (C := Real.exp R) (fun _ _ => Real.differentiableAt_exp)
    (fun z hz => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hz) hb ha
  simpa only [Real.norm_eq_abs] using H

section FrechetIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalized Gaussian expectation of a linear-map-valued derivative. The
zero-mass branch is the ordinary expectation, exactly as in `parisiStepPi`. -/
noncomputable def gaussianLogLaplaceD {p : ℕ} (mass : ℝ)
    (F : (Fin p → ℝ) → ℝ) (D : (Fin p → ℝ) → E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  if mass = 0 then ∫ z, D z ∂(piGauss p)
  else (∫ z, Real.exp (mass * F z) ∂(piGauss p))⁻¹ •
    ∫ z, Real.exp (mass * F z) • D z ∂(piGauss p)

/-- Direct Fréchet differentiation of a Gaussian log-Laplace integral. The
domination is anchored at the differentiation point, not a postulated joint
regularity property. The local growth and difference bounds will be supplied
by the actual cascade comparison estimates. -/
theorem hasFDerivAt_gaussianLogLaplace
    {p : ℕ} {F : E → (Fin p → ℝ) → ℝ} {D : (Fin p → ℝ) → E →L[ℝ] ℝ}
    {q : E} {s : Set E} (hs : s ∈ 𝓝 q) (mass : ℝ)
    (hderiv : ∀ z, HasFDerivAt (fun q => F q z) (D z) q)
    (hmeas : ∀ q ∈ s, Measurable (F q)) (hDmeas : AEStronglyMeasurable D (piGauss p))
    {C L A B : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ q ∈ s, ∀ z, |F q z| ≤ C + L * l1 z)
    (hbound : ∀ q' ∈ s, ∀ z, |F q' z - F q z| ≤ (A + B * l1 z) * ‖q' - q‖) :
    HasFDerivAt (fun q => parisiStepPi p mass 1 (F q) 0)
      (gaussianLogLaplaceD mass (F q) D) q := by
  have hq := mem_of_mem_nhds hs
  have hint : Integrable (F q) (piGauss p) := by
    simpa only [Real.sqrt_one, Pi.zero_apply, zero_add, one_mul] using
      (integrable_shift_pi (v := 1) hL (hgrowth q hq) (hmeas q hq) (0 : Fin p → ℝ))
  by_cases hm : mass = 0
  · have H := hasFDerivAt_integral_of_dominated_loc_of_lip' hs
      (bound := fun z => A + B * l1 z)
      (fun q hq => (hmeas q hq).aestronglyMeasurable) hint hDmeas
      (Eventually.of_forall fun z q' hq' => by
        simpa only [Real.norm_eq_abs] using hbound q' hq' z)
      ((integrable_const A).add (integrable_l1.const_mul B))
      (Eventually.of_forall hderiv)
    simpa only [parisiStepPi, gaussianLogLaplaceD, hm, if_true, Real.sqrt_one,
      Pi.zero_apply, zero_add, one_mul] using! H.2
  · have hFexp : Integrable (fun z => Real.exp (mass * F q z)) (piGauss p) := by
      simpa only [Real.sqrt_one, Pi.zero_apply, zero_add, one_mul] using
        (integrable_exp_shift_pi (m := mass) (v := 1) hL (hgrowth q hq) (hmeas q hq)
          (0 : Fin p → ℝ))
    let K := Real.exp (|mass| * C) * |mass|
    have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    have hbi : Integrable (fun z : Fin p → ℝ =>
        K * ((A + B * l1 z) * Real.exp ((|mass| * L) * l1 z))) (piGauss p) :=
      (integrable_poly_mul_exp_l1 hA hB (mul_nonneg (abs_nonneg mass) hL)).const_mul K
    have H := hasFDerivAt_integral_of_dominated_loc_of_lip' hs
      (fun q hq => ((hmeas q hq).const_mul mass).exp.aestronglyMeasurable) hFexp
      (((hmeas q hq).const_mul mass).exp.aestronglyMeasurable.smul (hDmeas.const_smul mass))
      (bound := fun z => K * ((A + B * l1 z) * Real.exp ((|mass| * L) * l1 z)))
      (Eventually.of_forall fun z q' hq' => by
        have hb (q'' : E) (hq'' : q'' ∈ s) : mass * F q'' z ≤ |mass| * (C + L * l1 z) := by
          calc
            _ ≤ |mass| * |F q'' z| := by rw [← abs_mul]; exact le_abs_self _
            _ ≤ _ := mul_le_mul_of_nonneg_left (hgrowth q'' hq'' z) (abs_nonneg mass)
        have H := abs_exp_sub_exp_le_of_le (hb q' hq') (hb q hq)
        rw [← mul_sub, abs_mul] at H
        have HH := H.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbound q' hq' z) (abs_nonneg mass)) (Real.exp_pos _).le)
        rw [mul_add, Real.exp_add] at HH
        simpa only [Real.norm_eq_abs, K, mul_assoc, mul_left_comm, mul_comm] using HH)
      hbi (Eventually.of_forall fun z => ((hderiv z).const_mul mass).exp)
    have hd := (H.2.log (integral_exp_pos hFexp).ne').const_mul (1 / mass)
    simp only [Pi.smul_apply', Pi.smul_apply] at hd
    have he : (∫ z, Real.exp (mass * F q z) • mass • D z ∂(piGauss p)) =
        mass • ∫ z, Real.exp (mass * F q z) • D z ∂(piGauss p) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      module
    rw [he, smul_smul, smul_smul] at hd
    have hc (I : ℝ) : (1 / mass * I⁻¹) * mass = I⁻¹ := by field_simp [hm]
    simp only [hc] at hd
    simpa only [parisiStepPi, gaussianLogLaplaceD, if_neg hm, Real.sqrt_one,
      Pi.zero_apply, zero_add, one_mul]
      using! hd

end FrechetIntegral

abbrev CoupledJointField (n : ℕ) := ℝ × ((Fin n → ℝ) × (Fin n → ℝ))

noncomputable def jointFieldVector {p : ℕ} (A B : Fin p → Fin n → ℝ)
    (z : Fin p → ℝ) : CoupledJointField n :=
  (0, pairedFieldLinear A z, pairedFieldLinear B z)

noncomputable def jointFieldShift {p : ℕ} (b : ℝ → ℝ) (A B : Fin p → Fin n → ℝ)
    (q : CoupledJointField n) (z : Fin p → ℝ) : CoupledJointField n :=
  q + b q.1 • jointFieldVector A B z

theorem jointFieldShift_eq {p : ℕ} (b : ℝ → ℝ) (A B : Fin p → Fin n → ℝ)
    (q : CoupledJointField n) (z : Fin p → ℝ) :
    jointFieldShift b A B q z =
      (q.1, q.2.1 + b q.1 • pairedFieldLinear A z, q.2.2 + b q.1 • pairedFieldLinear B z) := by
  ext <;> simp [jointFieldShift, jointFieldVector]

noncomputable def jointFieldShiftD {p : ℕ} (b' : ℝ) (A B : Fin p → Fin n → ℝ)
    (z : Fin p → ℝ) : CoupledJointField n →L[ℝ] CoupledJointField n :=
  ContinuousLinearMap.id ℝ _ +
    (ContinuousLinearMap.fst ℝ ℝ ((Fin n → ℝ) × (Fin n → ℝ))).smulRight
      (b' • jointFieldVector A B z)

theorem hasFDerivAt_jointFieldShift {p : ℕ} {b : ℝ → ℝ} {b' w : ℝ}
    (hb : HasDerivAt b b' w) (A B : Fin p → Fin n → ℝ)
    (x y : Fin n → ℝ) (z : Fin p → ℝ) :
    HasFDerivAt (fun q => jointFieldShift b A B q z) (jointFieldShiftD b' A B z) (w, x, y) := by
  have H := (hasFDerivAt_id (𝕜 := ℝ) (w, x, y)).add
    ((hb.hasFDerivAt.comp (w, x, y) (ContinuousLinearMap.fst ℝ ℝ
      ((Fin n → ℝ) × (Fin n → ℝ))).hasFDerivAt).smul_const (jointFieldVector A B z))
  convert! H using 1
  apply ContinuousLinearMap.ext
  intro q
  change q + q.1 • (b' • jointFieldVector A B z) = q + (q.1 * b') • jointFieldVector A B z
  module

theorem measurable_jointFieldShiftD {p : ℕ} (b' : ℝ) (A B : Fin p → Fin n → ℝ) :
    Measurable (jointFieldShiftD b' A B) := by
  have hvec : Measurable (jointFieldVector A B) :=
    measurable_const.prodMk ((measurable_pairedFieldLinear A).prodMk (measurable_pairedFieldLinear B))
  exact measurable_const.add (((ContinuousLinearMap.smulRightL ℝ (CoupledJointField n) (CoupledJointField n)
    (ContinuousLinearMap.fst ℝ ℝ ((Fin n → ℝ) × (Fin n → ℝ)))).continuous.measurable).comp
      (hvec.const_smul b'))

private theorem l1_le_card_norm (x : Fin n → ℝ) : l1 x ≤ n * ‖x‖ := by
  simpa only [l1, Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using
    Pi.sum_norm_apply_le_norm x

private theorem l1_smul' (c : ℝ) (x : Fin n → ℝ) : l1 (c • x) = |c| * l1 x :=
  l1_const_smul c x

noncomputable def jointGaussianStepD {p : ℕ} (F : CoupledJointField n → ℝ)
    (b : ℝ → ℝ) (mass : ℝ) (A B : Fin p → Fin n → ℝ) (q : CoupledJointField n) :
    CoupledJointField n →L[ℝ] ℝ :=
  gaussianLogLaplaceD mass (fun z => F (jointFieldShift b A B q z))
    (fun z => (fderiv ℝ F (jointFieldShift b A B q z)).comp
      (jointFieldShiftD (deriv b q.1) A B z))

/-- A joint moving-field Gaussian transform preserves actual differentiability.
Only coefficient differentiability and the established anchored and spatial
comparison bounds are used to discharge domination. -/
theorem hasFDerivAt_jointGaussianStep {p : ℕ}
    (F : CoupledJointField n → ℝ) {b : ℝ → ℝ} {w : ℝ} (hb : DifferentiableAt ℝ b w)
    (mass : ℝ) (A B : Fin p → Fin n → ℝ)
    (hFdiff : ∀ x y, DifferentiableAt ℝ F (w, x, y))
    (hFmeas : ∀ᶠ a in 𝓝 w, Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)))
    (hFgrowth : CoupledGrowth (fun x y => F (w, x, y)))
    (hspace : ∀ x y x' y', |F (w, x, y) - F (w, x', y')| ≤ l1 (x - x') + l1 (y - y'))
    {K : ℝ} (hK : 0 ≤ K)
    (hparam : ∀ᶠ a in 𝓝 w, ∀ x y, |F (a, x, y) - F (w, x, y)| ≤ K * |a - w|)
    (x y : Fin n → ℝ) :
    HasFDerivAt (fun q => parisiStepPi p mass 1
      (fun z => F (jointFieldShift b A B q z)) 0)
      (jointGaussianStepD F b mass A B (w, x, y)) (w, x, y) := by
  classical
  let q : CoupledJointField n := (w, x, y)
  obtain ⟨Cb, hCb, hbb⟩ := hb.isBigO_sub.exists_pos
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hzbound (z : Fin p → ℝ) : l1 (pairedFieldLinear A z) + l1 (pairedFieldLinear B z) ≤ L * l1 z := by
    dsimp [L]
    rw [Finset.sum_add_distrib]
    nlinarith [l1_pairedFieldLinear_le A z, l1_pairedFieldLinear_le B z]
  have hevent : ∀ᶠ q' : CoupledJointField n in 𝓝 q,
      Measurable (fun r : (Fin n → ℝ) × (Fin n → ℝ) => F (q'.1, r)) ∧
      (∀ x y, |F (q'.1, x, y) - F (w, x, y)| ≤ K * |q'.1 - w|) ∧
      |b q'.1 - b w| ≤ Cb * |q'.1 - w| ∧ ‖q' - q‖ < 1 := by
    have ht := (continuous_fst.tendsto q).eventually
      (hFmeas.and (hparam.and hbb.bound))
    filter_upwards [ht, Metric.ball_mem_nhds q zero_lt_one] with q' hq' hball
    exact ⟨hq'.1, hq'.2.1, by simpa only [Real.norm_eq_abs] using hq'.2.2,
      by simpa only [Metric.mem_ball, dist_eq_norm] using hball⟩
  let s := {q' : CoupledJointField n |
      Measurable (fun r : (Fin n → ℝ) × (Fin n → ℝ) => F (q'.1, r)) ∧
      (∀ x y, |F (q'.1, x, y) - F (w, x, y)| ≤ K * |q'.1 - w|) ∧
      |b q'.1 - b w| ≤ Cb * |q'.1 - w| ∧ ‖q' - q‖ < 1}
  have hs : s ∈ 𝓝 q := hevent
  have hdist (q' : CoupledJointField n) (hq' : q' ∈ s) (z : Fin p → ℝ) :
      |F (jointFieldShift b A B q' z) - F (jointFieldShift b A B q z)| ≤
        (K + 2 * n + Cb * L * l1 z) * ‖q' - q‖ := by
    have ht : |q'.1 - w| ≤ ‖q' - q‖ := norm_fst_le (q' - q)
    have hx : l1 (q'.2.1 - x) ≤ n * ‖q' - q‖ := (l1_le_card_norm _).trans
      (mul_le_mul_of_nonneg_left ((norm_fst_le (q' - q).2).trans (norm_snd_le (q' - q))) (by positivity))
    have hy : l1 (q'.2.2 - y) ≤ n * ‖q' - q‖ := (l1_le_card_norm _).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le (q' - q).2).trans (norm_snd_le (q' - q))) (by positivity))
    have hcoef : |b q'.1 - b w| ≤ Cb * ‖q' - q‖ := hq'.2.2.1.trans
      (mul_le_mul_of_nonneg_left ht hCb.le)
    have hxp := l1_add_le (q'.2.1 - x) ((b q'.1 - b w) • pairedFieldLinear A z)
    have hyp := l1_add_le (q'.2.2 - y) ((b q'.1 - b w) • pairedFieldLinear B z)
    rw [l1_smul'] at hxp hyp
    have hsp := hspace (q'.2.1 + b q'.1 • pairedFieldLinear A z)
      (q'.2.2 + b q'.1 • pairedFieldLinear B z)
      (x + b w • pairedFieldLinear A z) (y + b w • pairedFieldLinear B z)
    have hex (a a' Z : Fin n → ℝ) : a' + b q'.1 • Z - (a + b w • Z) =
        (a' - a) + (b q'.1 - b w) • Z := by module
    rw [hex, hex] at hsp
    have htri := abs_sub_le
      (F (q'.1, q'.2.1 + b q'.1 • pairedFieldLinear A z, q'.2.2 + b q'.1 • pairedFieldLinear B z))
      (F (w, q'.2.1 + b q'.1 • pairedFieldLinear A z, q'.2.2 + b q'.1 • pairedFieldLinear B z))
      (F (w, x + b w • pairedFieldLinear A z, y + b w • pairedFieldLinear B z))
    have hp := hq'.2.1 (q'.2.1 + b q'.1 • pairedFieldLinear A z)
      (q'.2.2 + b q'.1 • pairedFieldLinear B z)
    have hprod := mul_le_mul hcoef (hzbound z)
      (add_nonneg (l1_nonneg _) (l1_nonneg _)) (mul_nonneg hCb.le (norm_nonneg _))
    rw [jointFieldShift_eq, jointFieldShift_eq]
    dsimp only [q] at *
    nlinarith [mul_le_mul_of_nonneg_left ht hK]
  let G (q' : CoupledJointField n) (z : Fin p → ℝ) := F (jointFieldShift b A B q' z)
  let D (z : Fin p → ℝ) :=
    (fderiv ℝ F (jointFieldShift b A B q z)).comp (jointFieldShiftD (deriv b w) A B z)
  have hD (z : Fin p → ℝ) : HasFDerivAt (fun q' => G q' z) (D z) q := by
    have H := (hFdiff (x + b w • pairedFieldLinear A z) (y + b w • pairedFieldLinear B z)).hasFDerivAt
    have H' : HasFDerivAt F (fderiv ℝ F (jointFieldShift b A B q z)) (jointFieldShift b A B q z) := by
      simpa only [jointFieldShift, jointFieldVector, q, Prod.mk_add_mk, Prod.smul_mk,
        smul_zero, add_zero] using! H
    exact H'.comp q (hasFDerivAt_jointFieldShift hb.hasDerivAt A B x y z)
  have hmshift (q' : CoupledJointField n) : Measurable (jointFieldShift b A B q') := by
    change Measurable (fun z => q' + b q'.1 • (0, pairedFieldLinear A z, pairedFieldLinear B z))
    exact measurable_const.add ((measurable_const.prodMk
      ((measurable_pairedFieldLinear A).prodMk (measurable_pairedFieldLinear B))).const_smul (b q'.1))
  have hDm : Measurable D := by
    have hc : Continuous (fun P : (CoupledJointField n →L[ℝ] ℝ) ×
        (CoupledJointField n →L[ℝ] CoupledJointField n) => P.1.comp P.2) :=
      ((ContinuousLinearMap.compL ℝ (CoupledJointField n) (CoupledJointField n) ℝ).continuous.comp
        continuous_fst).clm_apply continuous_snd
    exact hc.measurable.comp (((measurable_fderiv ℝ F).comp (hmshift q)).prodMk
      (measurable_jointFieldShiftD _ A B))
  obtain ⟨C, L0, hL0, hg⟩ := hFgrowth.bound
  have hg0 (z : Fin p → ℝ) : |G q z| ≤ C + L0 * (l1 x + l1 y) +
      (L0 * |b w| * L) * l1 z := by
    have hx := l1_add_le x (b w • pairedFieldLinear A z)
    have hy := l1_add_le y (b w • pairedFieldLinear B z)
    rw [l1_smul'] at hx hy
    have hprod := mul_le_mul_of_nonneg_left (hzbound z) (mul_nonneg hL0 (abs_nonneg (b w)))
    have H := hg (x + b w • pairedFieldLinear A z) (y + b w • pairedFieldLinear B z)
    simp only [G, jointFieldShift, jointFieldVector, q, Prod.mk_add_mk, Prod.smul_mk,
      smul_zero, add_zero]
    nlinarith
  apply hasFDerivAt_gaussianLogLaplace hs mass hD
    (fun q' hq' => ?_) hDm.aestronglyMeasurable
    (C := C + L0 * (l1 x + l1 y) + (K + 2 * n))
    (L := L0 * |b w| * L + Cb * L) (A := K + 2 * n) (B := Cb * L)
    (by positivity) (by positivity) (by positivity) (fun q' hq' z => ?_) hdist
  · simp only [G, jointFieldShift_eq]
    exact hq'.1.comp ((measurable_const.add ((measurable_pairedFieldLinear A).const_smul (b q'.1))).prodMk
      (measurable_const.add ((measurable_pairedFieldLinear B).const_smul (b q'.1))))
  · have H := abs_sub_le (G q' z) (G q z) 0
    simp only [sub_zero] at H
    have hd := hdist q' hq' z
    have hn := hq'.2.2.2.le
    have hprod := mul_le_mul_of_nonneg_left hn
      (show 0 ≤ K + 2 * (n : ℝ) + Cb * L * l1 z by positivity)
    nlinarith [hg0 z]

theorem differentiableAt_jointGaussianStep {p : ℕ}
    (F : CoupledJointField n → ℝ) {b : ℝ → ℝ} {w : ℝ} (hb : DifferentiableAt ℝ b w)
    (mass : ℝ) (A B : Fin p → Fin n → ℝ)
    (hFdiff : ∀ x y, DifferentiableAt ℝ F (w, x, y))
    (hFmeas : ∀ᶠ a in 𝓝 w, Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)))
    (hFgrowth : CoupledGrowth (fun x y => F (w, x, y)))
    (hspace : ∀ x y x' y', |F (w, x, y) - F (w, x', y')| ≤ l1 (x - x') + l1 (y - y'))
    {K : ℝ} (hK : 0 ≤ K)
    (hparam : ∀ᶠ a in 𝓝 w, ∀ x y, |F (a, x, y) - F (w, x, y)| ≤ K * |a - w|)
    (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q => parisiStepPi p mass 1
      (fun z => F (jointFieldShift b A B q z)) 0) (w, x, y) :=
  (hasFDerivAt_jointGaussianStep F hb mass A B hFdiff hFmeas hFgrowth hspace hK hparam x y).differentiableAt

theorem pairedFieldLinear_const_mul {p : ℕ} (A : Fin p → Fin n → ℝ)
    (c : ℝ) (z : Fin p → ℝ) :
    pairedFieldLinear A (fun i => c * z i) = c • pairedFieldLinear A z := by
  simp only [pairedFieldLinear, Finset.smul_sum, smul_smul]

theorem jointGaussianStep_eq_linearStep {p : ℕ}
    (F : CoupledJointField n → ℝ) (mass : ℝ) (v : ℝ → ℝ)
    (A B : Fin p → Fin n → ℝ) (q : CoupledJointField n) :
    parisiStepPi p mass 1 (fun z => F (jointFieldShift (fun a => Real.sqrt (v a)) A B q z)) 0 =
      coupledLinearStep mass (v q.1) A B (fun x y => F (q.1, x, y)) q.2.1 q.2.2 := by
  simp only [coupledLinearStep, parisiStepPi, Real.sqrt_one, Pi.zero_apply, zero_add,
    one_mul, jointFieldShift_eq, pairedFieldLinear_const_mul]

/-- Genuine full joint differentiability in the interpolation parameter and
both replica fields. All finite variance coordinates vary together with the
disorder. A zero coordinate is permitted when locally constant, including
coincident-overlap levels; positive coordinates use their actual square-root
derivative. No partial-to-total differentiability assumption is made. -/
theorem differentiableAt_constrainedFieldCascade_joint
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : CoupledJointField n =>
      coupledFieldCascade n m (fun l => v l q.1) d
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y) := by
  induction j generalizing x y with
  | zero => exact differentiableAt_constrainedPairFieldBase_joint u hU x y
  | succ j ih =>
    let F : CoupledJointField n → ℝ := fun q => coupledFieldCascade n m (fun l => v l q.1) d
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
    have hvj (l : ℕ) (hl : l < j) := hv l (show l < j + 1 by omega)
    have hfj (l : ℕ) (hl : l < j) := hface l (show l < j + 1 by omega)
    have hFd (x y : Fin n → ℝ) : DifferentiableAt ℝ F (w, x, y) := ih hvj hfj x y
    have hFm : ∀ᶠ a in 𝓝 w,
        Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)) := by
      filter_upwards [hnonneg] with a ha
      exact (constrainedPairFieldCascade_growth (U a) u m (fun l => v l a) hm ha d j).measurable
    have hFg : CoupledGrowth (fun x y => F (w, x, y)) :=
      constrainedPairFieldCascade_growth (U w) u m (fun l => v l w) hm hnonneg.self_of_nhds d j
    have hFs (x y x' y' : Fin n → ℝ) : |F (w, x, y) - F (w, x', y')| ≤
        l1 (x - x') + l1 (y - y') :=
      constrainedFieldCascade_fields_dist_le (U w) u m (fun l => v l w) hm
        hnonneg.self_of_nhds d j x y x' y'
    obtain ⟨K, hK, hKbound⟩ := constrainedFieldCascade_path_anchored_bound U u m v hm d j hU hvj hnonneg hfj
    have hb : DifferentiableAt ℝ (fun a => Real.sqrt (v j a)) w := by
      rcases hface j (by omega) with hp | hz
      · exact (Real.hasDerivAt_sqrt hp.ne').differentiableAt.comp w (hv j (by omega))
      · apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hz] with a ha
        simp [ha]
    have H {p : ℕ} (A B : Fin p → Fin n → ℝ) :=
      differentiableAt_jointGaussianStep F hb (m j) A B hFd hFm hFg hFs hK hKbound x y
    by_cases hj : j < d
    · have H' := H (independentLeftDirection n) (independentRightDirection n)
      simp only [jointGaussianStep_eq_linearStep, coupledLinearStep_independent] at H'
      simpa only [coupledFieldCascade, if_pos hj] using H'
    · have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
      simp only [jointGaussianStep_eq_linearStep, coupledLinearStep_shared] at H'
      simpa only [coupledFieldCascade, if_neg hj] using H'

/-- Consequently the actual simultaneously varying cascade has a real path
derivative. The derivative is the time component of its proved joint Fréchet
derivative, not a sum of independently assumed partial identities. -/
theorem hasDerivAt_constrainedFieldCascade_path_fderiv
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasDerivAt (fun a => coupledFieldCascade n m (fun l => v l a) d
      (constrainedPairFieldBase n (U a) u) j x y)
      ((fderiv ℝ (fun q : CoupledJointField n => coupledFieldCascade n m (fun l => v l q.1) d
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y)) (1, 0, 0)) w := by
  exact (differentiableAt_constrainedFieldCascade_joint U u m v hm d j hU hv hnonneg hface x y).hasFDerivAt.comp_hasDerivAt w
    ((hasDerivAt_id w).prodMk ((hasDerivAt_const w x).prodMk (hasDerivAt_const w y)))

/-- The explicit next-level joint derivative: a normalized Gaussian mean of
the actual inner joint derivative composed with the changing field shift.
This is before integration by parts, so square-root coefficient derivatives
and Gaussian coordinates are still visible. -/
noncomputable def constrainedJointStepD (U : ℝ → EnergySpace n) (u : ℝ)
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (d j : ℕ) (q : CoupledJointField n) :
    CoupledJointField n →L[ℝ] ℝ :=
  let F : CoupledJointField n → ℝ := fun q => coupledFieldCascade n m (fun l => v l q.1) d
    (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
  if j < d then jointGaussianStepD F (fun a => Real.sqrt (v j a)) (m j)
    (independentLeftDirection n) (independentRightDirection n) q
  else jointGaussianStepD F (fun a => Real.sqrt (v j a)) (m j)
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) q

/-- Actual normalized derivative recursion for the simultaneously varying
constrained cascade. The inner derivative exists by the full joint theorem;
it is not supplied as an assumption. All masses, including zero, are kept. -/
theorem hasFDerivAt_constrainedFieldCascade_joint_succ
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w)
    (hv : ∀ l < j + 1, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j + 1, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasFDerivAt (fun q : CoupledJointField n =>
      coupledFieldCascade n m (fun l => v l q.1) d
        (constrainedPairFieldBase n (U q.1) u) (j + 1) q.2.1 q.2.2)
      (constrainedJointStepD U u m v d j (w, x, y)) (w, x, y) := by
  let F : CoupledJointField n → ℝ := fun q => coupledFieldCascade n m (fun l => v l q.1) d
    (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
  have hvj (l : ℕ) (hl : l < j) := hv l (show l < j + 1 by omega)
  have hfj (l : ℕ) (hl : l < j) := hface l (show l < j + 1 by omega)
  have hFd (x y : Fin n → ℝ) : DifferentiableAt ℝ F (w, x, y) :=
    differentiableAt_constrainedFieldCascade_joint U u m v hm d j hU hvj hnonneg hfj x y
  have hFm : ∀ᶠ a in 𝓝 w,
      Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)) := by
    filter_upwards [hnonneg] with a ha
    exact (constrainedPairFieldCascade_growth (U a) u m (fun l => v l a) hm ha d j).measurable
  have hFg : CoupledGrowth (fun x y => F (w, x, y)) :=
    constrainedPairFieldCascade_growth (U w) u m (fun l => v l w) hm hnonneg.self_of_nhds d j
  have hFs (x y x' y' : Fin n → ℝ) : |F (w, x, y) - F (w, x', y')| ≤
      l1 (x - x') + l1 (y - y') :=
    constrainedFieldCascade_fields_dist_le (U w) u m (fun l => v l w) hm
      hnonneg.self_of_nhds d j x y x' y'
  obtain ⟨K, hK, hKbound⟩ := constrainedFieldCascade_path_anchored_bound U u m v hm d j hU hvj hnonneg hfj
  have hb : DifferentiableAt ℝ (fun a => Real.sqrt (v j a)) w := by
    rcases hface j (by omega) with hp | hz
    · exact (Real.hasDerivAt_sqrt hp.ne').differentiableAt.comp w (hv j (by omega))
    · apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hz] with a ha
      simp [ha]
  have H {p : ℕ} (A B : Fin p → Fin n → ℝ) :=
    hasFDerivAt_jointGaussianStep F hb (m j) A B hFd hFm hFg hFs hK hKbound x y
  by_cases hj : j < d
  · have H' := H (independentLeftDirection n) (independentRightDirection n)
    simp only [jointGaussianStep_eq_linearStep, coupledLinearStep_independent] at H'
    simpa only [coupledFieldCascade, constrainedJointStepD, if_pos hj] using H'
  · have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
    simp only [jointGaussianStep_eq_linearStep, coupledLinearStep_shared] at H'
    simpa only [coupledFieldCascade, constrainedJointStepD, if_neg hj] using H'

theorem hasDerivAt_constrainedFieldCascade_path_succ
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w)
    (hv : ∀ l < j + 1, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j + 1, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasDerivAt (fun a => coupledFieldCascade n m (fun l => v l a) d
      (constrainedPairFieldBase n (U a) u) (j + 1) x y)
      (constrainedJointStepD U u m v d j (w, x, y) (1, 0, 0)) w := by
  exact (hasFDerivAt_constrainedFieldCascade_joint_succ U u m v hm d j hU hv hnonneg hface x y).comp_hasDerivAt w
    ((hasDerivAt_id w).prodMk ((hasDerivAt_const w x).prodMk (hasDerivAt_const w y)))

end SpinGlass.Targets
