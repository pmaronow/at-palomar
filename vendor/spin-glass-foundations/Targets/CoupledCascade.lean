module

/-
# The coupled cascade in Talagrand's Lemma 2.7

The Gaussian increments of the two replicas are independent at inner levels and
shared at outer levels. Shared levels use half the original mass. The split `d`
counts independent levels from the Gibbs base; it corresponds to `k + 2 - r`
in this project's indexing (the paper's number of levels is `k + 1`).

The independent step is an integral against the product Gaussian measure, not
an assumption of factorisation. The full two-replica partition function is also
defined before proving its factorisation. Zero masses are handled explicitly.
-/
public import Targets.TalagrandCore

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-! ## The two kinds of Gaussian step -/

/-- Independent increments in the two replica fields. -/
noncomputable def independentStepPi (n : ℕ) (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  if m = 0 then
    ∫ z, A (fun i => x i + Real.sqrt v * z.1 i)
      (fun i => y i + Real.sqrt v * z.2 i) ∂(piGauss n).prod (piGauss n)
  else
    (1 / m) * Real.log (∫ z, Real.exp (m * A
      (fun i => x i + Real.sqrt v * z.1 i)
      (fun i => y i + Real.sqrt v * z.2 i)) ∂(piGauss n).prod (piGauss n))

/-- A shared Gaussian increment; the mass is halved as in (2.25). -/
noncomputable def sharedStepPi (n : ℕ) (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  parisiStepPi n (m / 2) v (fun z => A (x + z) (y + z)) 0

theorem independentStepPi_add {n : ℕ} (m v : ℝ)
    {A B : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (hB : GuerraGrowth B)
    (x y : Fin n → ℝ) :
    independentStepPi n m v (fun x y => A x + B y) x y =
      parisiStepPi n m v A x + parisiStepPi n m v B y := by
  obtain ⟨a, b, hb, hAb⟩ := hA.bound
  obtain ⟨c, d, hd, hBb⟩ := hB.bound
  by_cases hm : m = 0
  · simp only [independentStepPi, parisiStepPi, if_pos hm]
    rw [integral_add
      ((integrable_shift_pi (v := v) hb hAb hA.measurable x).comp_fst (piGauss n))
      ((integrable_shift_pi (v := v) hd hBb hB.measurable y).comp_snd (piGauss n))]
    rw [integral_fun_fst (fun z : Fin n → ℝ => A (fun i => x i + Real.sqrt v * z i)),
      integral_fun_snd (fun z : Fin n → ℝ => B (fun i => y i + Real.sqrt v * z i))]
    simp
  · simp only [independentStepPi, parisiStepPi, if_neg hm]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_prod_mul
      (fun z : Fin n → ℝ => Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
      (fun z : Fin n → ℝ => Real.exp (m * B (fun i => y i + Real.sqrt v * z i))),
      Real.log_mul
        (integral_exp_shift_pi_pos (m := m) (v := v) hb hAb hA.measurable x).ne'
        (integral_exp_shift_pi_pos (m := m) (v := v) hd hBb hB.measurable y).ne']
    ring

/-- Halving the mass cancels doubling the diagonal free energy, including at mass zero. -/
theorem sharedStepPi_diag {n : ℕ} (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (B : (Fin n → ℝ) → ℝ)
    (hAB : ∀ x, A x x = 2 * B x) (x : Fin n → ℝ) :
    sharedStepPi n m v A x x = 2 * parisiStepPi n m v B x := by
  unfold sharedStepPi parisiStepPi
  simp only [Pi.zero_apply, zero_add, hAB, Pi.add_def]
  by_cases hm : m = 0
  · simp [hm, integral_const_mul]
  · simp only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, hm, if_false]
    simp_rw [show ∀ a : ℝ, m / 2 * (2 * a) = m * a by intro a; ring]
    ring

/-- Growth of the single-replica cascade at each depth, including interpolation endpoints. -/
theorem guerraGrowth_cascade {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    GuerraGrowth (cascadeT n s β 1 (guerraBase n U h t) j) := by
  obtain ⟨a, D, hD, hp⟩ := guerra_cascade_continuous_Icc n s β h j
  exact ⟨(hp U).1 t ht, a + uAbs n U, D, hD, (hp U).2.1 t ht⟩

/-! ## The unconstrained two-replica pressure -/

/-- The actual unrestricted two-replica log partition function. -/
noncomputable def coupledBase (n : ℕ) (U : EnergySpace n) (h t : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, ∑ τ : Config n,
    Real.exp (guerraH n U h t x σ + guerraH n U h t y τ))

theorem coupledBase_eq (n : ℕ) (U : EnergySpace n) (h t : ℝ) (x y : Fin n → ℝ) :
    coupledBase n U h t x y = guerraBase n U h t x + guerraBase n U h t y := by
  unfold coupledBase guerraBase
  simp_rw [Real.exp_add, ← Finset.mul_sum, ← Finset.sum_mul]
  exact Real.log_mul (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
    (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-- Coupled recursion: `d` independent inner levels, followed by shared levels. -/
noncomputable def coupledCascade {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (d : ℕ) (base : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => base
  | j + 1 =>
    if j < d then independentStepPi n (s.m (k + 1 - j))
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
      (coupledCascade n s β d base j)
    else sharedStepPi n (s.m (k + 1 - j))
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
      (coupledCascade n s β d base j)

/-- Equation (2.40) before the branching point: the two fields may differ. -/
theorem coupledCascade_independent {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d j : ℕ) (hjd : j ≤ d) (x y : Fin n → ℝ) :
    coupledCascade n s β d (coupledBase n U h t) j x y =
      cascadeT n s β 1 (guerraBase n U h t) j x +
      cascadeT n s β 1 (guerraBase n U h t) j y := by
  induction j generalizing x y with
  | zero => exact coupledBase_eq n U h t x y
  | succ j ih =>
    have hj : j < d := by omega
    have heq := funext (fun x => funext (fun y => ih (by omega) x y))
    simp only [coupledCascade, if_pos hj, heq, cascadeT]
    exact independentStepPi_add _ _ (guerraGrowth_cascade n s β U h ht j)
      (guerraGrowth_cascade n s β U h ht j) x y

/-- Equation (2.40) on the shared diagonal, at every depth. -/
theorem coupledCascade_diag {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d j : ℕ) (x : Fin n → ℝ) :
    coupledCascade n s β d (coupledBase n U h t) j x x =
      2 * cascadeT n s β 1 (guerraBase n U h t) j x := by
  induction j generalizing x with
  | zero => simpa [coupledCascade, cascadeT, two_mul] using coupledBase_eq n U h t x x
  | succ j ih =>
    by_cases hj : j < d
    · rw [coupledCascade_independent n s β U h ht d (j + 1) (by omega), two_mul]
    · simp only [coupledCascade, if_neg hj, cascadeT]
      exact sharedStepPi_diag _ _ _ _ ih x

variable {Ω : Type*} [MeasureSpace Ω]

/-- Expected unrestricted coupled pressure (the left side of (2.38)). -/
noncomputable def coupledPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (d : ℕ) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledCascade n s β d (coupledBase n (U ω) h t) (k + 2) 0 0 ∂ℙ

/-- **Lemma 2.7, equation (2.38)**: the unrestricted coupled pressure is `2φ(t)`.
No near-minimality, strict-mass, or positive-variance assumption is needed. -/
theorem coupledPhi_eq_two_guerraPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (d : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    coupledPhi n s β h U d t = 2 * guerraPhi n s β h U t := by
  unfold coupledPhi guerraPhi
  simp_rw [coupledCascade_diag n s β _ h ht, integral_const_mul]
  ring

/-! ## Tilt densities and observables -/

/-- Normalized exponential density for an independent two-replica step. -/
noncomputable def independentTiltWeightPi (n : ℕ) (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  if m = 0 then 1 else
    Real.exp (m * A (fun i => x i + Real.sqrt v * z.1 i)
      (fun i => y i + Real.sqrt v * z.2 i)) /
    ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w.1 i)
      (fun i => y i + Real.sqrt v * w.2 i)) ∂(piGauss n).prod (piGauss n)

/-- Normalized exponential density for a shared, half-mass step. -/
noncomputable def sharedTiltWeightPi (n : ℕ) (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y z : Fin n → ℝ) : ℝ :=
  tiltWeightPi n (m / 2) v (fun w => A (x + w) (y + w)) 0 z

/-- The independent-level density is the product of the single-replica densities. -/
theorem independentTiltWeightPi_add {n : ℕ} (m v : ℝ)
    (A B : (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    independentTiltWeightPi n m v (fun x y => A x + B y) x y z =
      tiltWeightPi n m v A x z.1 * tiltWeightPi n m v B y z.2 := by
  by_cases hm : m = 0
  · simp [independentTiltWeightPi, tiltWeightPi, hm]
  · simp only [independentTiltWeightPi, tiltWeightPi, if_neg hm]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_prod_mul
      (fun z : Fin n → ℝ => Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
      (fun z : Fin n → ℝ => Real.exp (m * B (fun i => y i + Real.sqrt v * z i)))]
    exact mul_div_mul_comm _ _ _ _

/-- The shared-level density is a single-replica density, not its square. -/
theorem sharedTiltWeightPi_diag {n : ℕ} (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (B : (Fin n → ℝ) → ℝ)
    (hAB : ∀ x, A x x = 2 * B x) (x z : Fin n → ℝ) :
    sharedTiltWeightPi n m v A x x z = tiltWeightPi n m v B x z := by
  unfold sharedTiltWeightPi tiltWeightPi
  simp only [Pi.zero_apply, zero_add, hAB, Pi.add_def]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, hm, if_false]
    simp_rw [show ∀ a : ℝ, m / 2 * (2 * a) = m * a by intro a; ring]

/-- A normalized conditional expectation using independent increments. -/
noncomputable def independentTiltAvg (n : ℕ) (m v : ℝ)
    (A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∫ z, F (fun i => x i + Real.sqrt v * z.1 i)
    (fun i => y i + Real.sqrt v * z.2 i) *
    independentTiltWeightPi n m v A x y z ∂(piGauss n).prod (piGauss n)

/-- A normalized conditional expectation using a shared increment. -/
noncomputable def sharedTiltAvg (n : ℕ) (m v : ℝ)
    (A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∫ z, F (fun i => x i + Real.sqrt v * z i)
    (fun i => y i + Real.sqrt v * z i) * sharedTiltWeightPi n m v A x y z ∂piGauss n

/-- Product-Gaussian integration of a finite sum of factored observables.
The integrability hypotheses justify distributing the finite sums. -/
theorem independentTiltAvg_sum_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (m v : ℝ) (A B : (Fin n → ℝ) → ℝ)
    (f : ι → (Fin n → ℝ) → ℝ) (g : κ → (Fin n → ℝ) → ℝ)
    (K : ι → κ → ℝ) (x y : Fin n → ℝ)
    (hf : ∀ a, Integrable (fun z => f a (fun i => x i + Real.sqrt v * z i) *
      tiltWeightPi n m v A x z) (piGauss n))
    (hg : ∀ b, Integrable (fun z => g b (fun i => y i + Real.sqrt v * z i) *
      tiltWeightPi n m v B y z) (piGauss n)) :
    independentTiltAvg n m v (fun x y => A x + B y)
      (fun x y => ∑ a, ∑ b, f a x * g b y * K a b) x y =
      ∑ a, ∑ b,
        (∫ z, f a (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z ∂piGauss n) *
        (∫ z, g b (fun i => y i + Real.sqrt v * z i) * tiltWeightPi n m v B y z ∂piGauss n) *
        K a b := by
  let F := fun a z => f a (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z
  let G := fun b z => g b (fun i => y i + Real.sqrt v * z i) * tiltWeightPi n m v B y z
  have hi : ∀ a b, Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      F a z.1 * G b z.2 * K a b) ((piGauss n).prod (piGauss n)) :=
    fun a b => ((hf a).mul_prod (hg b)).mul_const _
  unfold independentTiltAvg
  simp_rw [independentTiltWeightPi_add, Finset.sum_mul]
  have heq : ∀ a b (z : (Fin n → ℝ) × (Fin n → ℝ)),
      f a (fun i => x i + Real.sqrt v * z.1 i) *
        g b (fun i => y i + Real.sqrt v * z.2 i) * K a b *
        (tiltWeightPi n m v A x z.1 * tiltWeightPi n m v B y z.2) =
      F a z.1 * G b z.2 * K a b := by intros; dsimp [F, G]; ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_finsetSum _ (fun b _ => hi a b)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [integral_mul_const, integral_prod_mul (F a) (G b)]

/-- Gibbs expectation of a two-replica observable, with the original joint partition sum. -/
noncomputable def coupledGibbsAvg (n : ℕ) (U : EnergySpace n) (h t : ℝ)
    (K : Config n → Config n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ σ : Config n, ∑ τ : Config n,
    (Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) /
      ∑ ρ : Config n, ∑ υ : Config n,
        Real.exp (guerraH n U h t x ρ + guerraH n U h t y υ)) * K σ τ

theorem coupledGibbsAvg_eq {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (K : Config n → Config n → ℝ) (x y : Fin n → ℝ) :
    coupledGibbsAvg n U h t K x y = ∑ σ : Config n, ∑ τ : Config n,
      guerraProb n s β U h t 0 σ x * guerraProb n s β U h t 0 τ y * K σ τ := by
  unfold coupledGibbsAvg guerraProb
  simp_rw [Real.exp_add, ← Finset.mul_sum, ← Finset.sum_mul, mul_div_mul_comm]

/-- Iterated tilted expectation, equivalently `E(V₁ … Vₖ ⟨K⟩)` in (2.39). -/
noncomputable def coupledObservable {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (d : ℕ) (K : Config n → Config n → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => coupledGibbsAvg n U h t K
  | j + 1 =>
    if j < d then independentTiltAvg n (s.m (k + 1 - j))
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
      (coupledCascade n s β d (coupledBase n U h t) j)
      (coupledObservable n s β U h t d K j)
    else sharedTiltAvg n (s.m (k + 1 - j))
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
      (coupledCascade n s β d (coupledBase n U h t) j)
      (coupledObservable n s β U h t d K j)

/-- The independently propagated replicas have product conditional probabilities. -/
theorem coupledObservable_independent {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) (K : Config n → Config n → ℝ) (j : ℕ) (hjd : j ≤ d) (x y : Fin n → ℝ) :
    coupledObservable n s β U h t d K j x y = ∑ σ : Config n, ∑ τ : Config n,
      guerraProb n s β U h t j σ x * guerraProb n s β U h t j τ y * K σ τ := by
  induction j generalizing x y with
  | zero => exact coupledGibbsAvg_eq n s β U h t K x y
  | succ j ih =>
    have hj : j < d := by omega
    have hobs := funext (fun x => funext (fun y => ih (by omega) x y))
    have henergy := funext (fun x => funext (fun y =>
      coupledCascade_independent n s β U h ⟨ht.1.le, ht.2.le⟩ d j (by omega) x y))
    have hi : ∀ σ (x : Fin n → ℝ), Integrable (fun z =>
        guerraProb n s β U h t j σ (fun i => x i + Real.sqrt
          (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i) *
        tiltWeightPi n (s.m (k + 1 - j))
          (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
          (cascadeT n s β 1 (guerraBase n U h t) j) x z) (piGauss n) := by
      intro σ x
      apply integrable_guerraStepAvg_integrand n s β U h ht j
        ((measurable_guerraProb_joint s β h t j σ).comp
          (measurable_const.prodMk measurable_id)) (a := 1) (b := 0) le_rfl
      intro y
      simp only [zero_mul, add_zero]
      obtain ⟨hp, hsum⟩ := guerraProb_nonneg_sum_one n s β U h ht j
      change |guerraProb n s β U h t j σ y| ≤ 1
      rw [abs_of_nonneg (hp σ y), ← hsum y]
      exact Finset.single_le_sum (fun τ _ => hp τ y) (Finset.mem_univ σ)
    simp only [coupledObservable, if_pos hj, hobs, henergy, guerraProb]
    exact independentTiltAvg_sum_mul _ _ _ _ _ _ K x y (fun σ => hi σ x) (fun τ => hi τ y)

/-- Propagate an observable at depth `d` through `l` remaining single-replica levels. -/
noncomputable def guerraOuterAvg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (d : ℕ) (F : (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → ℝ
  | 0 => F
  | l + 1 => guerraStepAvg n s β U h t (d + l) (guerraOuterAvg n s β U h t d F l)

/-- The pointwise conditional-expectation identity underlying (2.39). -/
theorem coupledObservable_diag {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) (K : Config n → Config n → ℝ) (l : ℕ) (x : Fin n → ℝ) :
    coupledObservable n s β U h t d K (d + l) x x =
      guerraOuterAvg n s β U h t d (guerraReplicaAvg n s β U h t d K) l x := by
  induction l generalizing x with
  | zero => exact coupledObservable_independent n s β U h ht d K d le_rfl x x
  | succ l ih =>
    have hj : ¬d + l < d := by omega
    rw [show d + (l + 1) = (d + l) + 1 by omega, coupledObservable, if_neg hj]
    simp only [sharedTiltAvg, guerraOuterAvg]
    simp_rw [sharedTiltWeightPi_diag _ _ _ _
      (coupledCascade_diag n s β U h ⟨ht.1.le, ht.2.le⟩ d (d + l)), ih]
    rfl

/-- The paper's `μ_r(K)`, where `d = k + 2 - r`.
The product conditional Gibbs measure at depth `d` is averaged through all outer levels. -/
noncomputable def guerraReplicaMeasure {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) (d : ℕ) (K : Config n → Config n → ℝ) : ℝ :=
  ∫ ω, guerraOuterAvg n s β (U ω) h t d
    (guerraReplicaAvg n s β (U ω) h t d K) (k + 2 - d) 0 ∂ℙ

/-- **Lemma 2.7, equation (2.39)** in iterated conditional-expectation form. -/
theorem coupledObservable_eq_replicaMeasure {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) (hd : d ≤ k + 2) (K : Config n → Config n → ℝ) :
    (∫ ω, coupledObservable n s β (U ω) h t d K (k + 2) 0 0 ∂ℙ) =
      guerraReplicaMeasure n s β h U t d K := by
  unfold guerraReplicaMeasure
  apply integral_congr_ae
  filter_upwards with ω
  simpa only [Nat.add_sub_of_le hd] using
    coupledObservable_diag n s β (U ω) h ht d K (k + 2 - d) 0

end SpinGlass.Targets
