module

public import Targets.Section4UEndpoints
public import Targets.TalagrandLambdaGain

@[expose] public section

/-!
# The zero-lambda derivative and Talagrand's U prime

At zero lambda, independent levels propagate a product of the two scalar
spatial slopes. After branching, shared levels propagate its diagonal square
by exactly the normalized scalar tilts defining the actual Section 4 factor Q.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

private theorem finiteStep_second_zero {P : Type*} {F : P → ℝ → ℝ × ℝ → ℝ}
    {A B : ℝ → ℝ} (hB : HasLinearGrowth B) (hBm : Measurable B)
    (p : P) (hF : ∀ x y, F p 0 (x, y) = A x + B y) (m v x y : ℝ) :
    GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => 0) (fun _ => Real.sqrt v) F p 0 (x, y) =
      A x + parisiStep m v B y := by
  have H := parisiStep_const_add (A x) m v hB hBm y
  simpa only [GTFrame.finiteStep, ite_apply, GTFrame.step0, GTFrame.stepM, parisiStep,
    zero_mul, add_zero, hF] using H

private theorem finiteStep_first_zero {P : Type*} {F : P → ℝ → ℝ × ℝ → ℝ}
    {A B : ℝ → ℝ} (hA : HasLinearGrowth A) (hAm : Measurable A)
    (p : P) (hF : ∀ x y, F p 0 (x, y) = A x + B y) (m v x y : ℝ) :
    GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => Real.sqrt v) (fun _ => 0) F p 0 (x, y) =
      parisiStep m v A x + B y := by
  have H := finiteStep_second_zero (F := fun p l z => F p l (z.2, z.1)) hA hAm p
    (fun x y => (hF y x).trans (add_comm _ _)) m v y x
  simpa only [GTFrame.finiteStep, ite_apply, GTFrame.step0, GTFrame.stepM, add_comm] using H

private theorem finiteStepD_second_zero {P : Type*} {F D : P → ℝ → ℝ × ℝ → ℝ}
    {A B C E : ℝ → ℝ} (p : P)
    (hF : ∀ x y, F p 0 (x, y) = A x + B y)
    (hD : ∀ x y, D p 0 (x, y) = C x * E y) (m v x y : ℝ) :
    GTFrame.finiteStepD (gaussianReal 0 1) m (fun _ => 0) (fun _ => Real.sqrt v) F D p 0 (x, y) =
      C x * stepD1 B E m v y := by
  rw [finiteStepD_eq_stepMD]
  simp only [GTFrame.stepMD, zero_mul, add_zero, hF, hD, mul_add, Real.exp_add]
  have hn : (fun z => (C x * E (y + Real.sqrt v * z)) *
      (Real.exp (m * A x) * Real.exp (m * B (y + Real.sqrt v * z)))) =
      fun z => (C x * Real.exp (m * A x)) *
        (E (y + Real.sqrt v * z) * Real.exp (m * B (y + Real.sqrt v * z))) := by
    funext z; ring
  rw [hn, integral_const_mul, integral_const_mul]
  simp only [stepD1, tiltP, tiltE]
  field_simp [(Real.exp_pos (m * A x)).ne']

private theorem finiteStepD_first_zero {P : Type*} {F D : P → ℝ → ℝ × ℝ → ℝ}
    {A B C E : ℝ → ℝ} (p : P)
    (hF : ∀ x y, F p 0 (x, y) = A x + B y)
    (hD : ∀ x y, D p 0 (x, y) = C x * E y) (m v x y : ℝ) :
    GTFrame.finiteStepD (gaussianReal 0 1) m (fun _ => Real.sqrt v) (fun _ => 0) F D p 0 (x, y) =
      stepD1 A C m v x * E y := by
  have H := finiteStepD_second_zero
    (F := fun p l z => F p l (z.2, z.1)) (D := fun p l z => D p l (z.2, z.1)) p
    (fun x y => (hF y x).trans (add_comm _ _))
    (fun x y => (hD y x).trans (mul_comm _ _)) m v y x
  simpa only [finiteStepD_eq_stepMD, GTFrame.stepMD, mul_comm] using H

/-- The scalar spatial-slope recursion, used here only to expose the independent
prefix's exact product. Actual inputs are identified below with parisiFDeriv. -/
noncomputable def scalarFieldCascadeSlope (m v : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.sinh x / Real.cosh x
  | j + 1 => stepD1 (scalarFieldCascade m v j) (scalarFieldCascadeSlope m v j) (m j) (v j)

/-- Before the shared branch, the actual zero-lambda derivative is exactly the
product of the two scalar slopes; zero masses require no separate assumption. -/
theorem splitScalarCascade_independent_zero {P : Type*} (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (d : ℕ) {j : ℕ} (hj : j ≤ d) (p : P) (x y : ℝ) :
    splitScalarCascade m v d j p 0 (x, y) =
        scalarFieldCascade m (fun i => v i p) j x + scalarFieldCascade m (fun i => v i p) j y ∧
      splitScalarCascadeD m v d j p 0 (x, y) =
        scalarFieldCascadeSlope m (fun i => v i p) j x * scalarFieldCascadeSlope m (fun i => v i p) j y := by
  induction j generalizing x y with
  | zero =>
    refine ⟨coupledSite_zero x y, ?_⟩
    have H := (GTFrame.goodFam_fLbase (P := Unit)).hasDeriv () 0 (x, y)
    have H' := hasDerivAt_coupledSite_zero x y
    exact H.unique (by simpa only [GTFrame.fLbase, coupledSite_eq_gtTerminal, scalarFieldCascadeSlope] using! H')
  | succ j ih =>
    have hlt : j < d := by omega
    have hF (x y : ℝ) := (ih (by omega) x y).1
    have hD (x y : ℝ) := (ih (by omega) x y).2
    have hA := (scalarFieldCascade_props m (fun i => v i p) j).2.1
    have hAm := (scalarFieldCascade_props m (fun i => v i p) j).1
    have hF' (x y : ℝ) := finiteStep_second_zero hA hAm p hF (m j) (v j p) x y
    have hD' (x y : ℝ) := finiteStepD_second_zero p hF hD (m j) (v j p) x y
    constructor
    · simpa only [splitScalarCascade, if_pos hlt, scalarFieldCascade, GTFrame.finiteStep,
        ite_apply, GTFrame.step0, GTFrame.stepM] using!
        finiteStep_first_zero hA hAm p hF' (m j) (v j p) x y
    · simpa only [splitScalarCascadeD, if_pos hlt, scalarFieldCascadeSlope,
        finiteStepD_eq_stepMD, GTFrame.stepMD, GTFrame.finiteStep, ite_apply,
        GTFrame.step0, GTFrame.stepM] using!
        finiteStepD_first_zero p hF' hD' (m j) (v j p) x y

theorem section5_scalar_prefix {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m v : ℝ) {j : ℕ} (hj : j ≤ k + 2 - r) :
    scalarFieldCascade (fun i => section5Mass s r m (k + 2 - i))
        (fun i => section5Variance s β r (k + 2 - i) v) j = parisiF s β j ∧
      scalarFieldCascadeSlope (fun i => section5Mass s r m (k + 2 - i))
        (fun i => section5Variance s β r (k + 2 - i) v) j = parisiFDeriv s β j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hF, hD⟩ := ih (by omega)
    have hp : r < k + 2 - j := by omega
    have he : k + 2 - j - 1 = k + 1 - j := by omega
    simp only [scalarFieldCascade, scalarFieldCascadeSlope, hF, hD]
    simp only [section5Mass, section5Variance, if_pos hp, if_neg (not_lt.mpr hp.le),
      if_neg (Ne.symm (Nat.ne_of_lt hp)), he, parisiF, parisiFDeriv, and_self]

/-- At the end of the independent prefix the inserted inner slope has been
formed separately in each replica, with no restriction on the inserted mass. -/
theorem splitScalarCascadeD_inserted_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 2) (m v x y : ℝ) :
    splitScalarCascadeD (fun i => section5Mass s r m (k + 2 - i))
      (fun i => section5Variance s β r (k + 2 - i)) (k + 3 - r) (k + 2 - r + 1) v 0 (x, y) =
      stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) m v x *
        stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) m v y := by
  rw [(splitScalarCascade_independent_zero _ _ (k + 3 - r) (by omega) v x y).2]
  have H := section5_scalar_prefix s β r m v (j := k + 2 - r) le_rfl
  simp only [scalarFieldCascadeSlope, H.1, H.2]
  simp only [Nat.sub_sub_self hr,
    section5Mass, lt_self_iff_false, if_false, if_true, section5Variance]

private theorem section5_mass_diag {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    (fun i => if i < k + 3 - r then section5Mass s r m (k + 2 - i)
      else 2 * section5Mass s r m (k + 2 - i)) =
      fun i => section4Mass s r m (k + 2 - i) := by
  funext i
  by_cases hi : i < k + 3 - r
  · have hp : ¬k + 2 - i < r := by omega
    simp only [if_pos hi, section5Mass, section4Mass, if_neg hp]
  · have hp : k + 2 - i < r := by omega
    simp only [if_neg hi, section5Mass, section4Mass, if_pos hp]
    ring

private theorem section5_zero_diag {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (j : ℕ) (x : ℝ) :
    splitScalarCascade (fun i => section5Mass s r m (k + 2 - i))
      (fun i => section5Variance s β r (k + 2 - i)) (k + 3 - r) j v 0 (x, x) =
      2 * scalarFieldCascade (fun i => section4Mass s r m (k + 2 - i))
        (fun i => section5Variance s β r (k + 2 - i) v) j x := by
  rw [splitScalarCascade_zero_diag _ _ (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j)) _ _ _
    (fun j => section5Variance_nonneg s β hr (by omega) hv), section5_mass_diag s hr0 hr m]

private theorem pairedSecondMean_scalar_ratio {A G : ℝ → ℝ}
    (hA : Measurable A) (hG : Measurable G) (m v x : ℝ) :
    pairedSecondMean m v (fun (_ y : Fin 1 → ℝ) => A (y 0))
      (fun _ y => G (y 0)) 0 (fun _ => x) =
      (∫ z, G (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1) /
        ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1 := by
  simp only [pairedSecondMean, pairedTiltMean, tiltWeightPi_eq_exp_div, ← mul_div_assoc]
  rw [integral_div]
  have hs : Measurable (fun z : ℝ => x + Real.sqrt v * z) := by fun_prop
  rw [integral_piGauss_eval (0 : Fin 1)
    (fun z => G (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)))
    (((hG.comp hs).mul (((hA.comp hs).const_mul m).exp)).aestronglyMeasurable)]
  rw [integral_piGauss_eval (0 : Fin 1)
    (fun z => Real.exp (m * A (x + Real.sqrt v * z)))
    (((hA.comp (by fun_prop)).const_mul m).exp.aestronglyMeasurable)]

private theorem finiteStepD_diag_scalar {P : Type*} {F D : P → ℝ → ℝ × ℝ → ℝ}
    {A G : ℝ → ℝ} (hA : Measurable A) (hG : Measurable G) (p : P)
    (hF : ∀ x, F p 0 (x, x) = 2 * A x) (hD : ∀ x, D p 0 (x, x) = G x)
    (m v x : ℝ) :
    GTFrame.finiteStepD (gaussianReal 0 1) m (fun _ => Real.sqrt v) (fun _ => Real.sqrt v)
      F D p 0 (x, x) =
      pairedSecondMean (2 * m) v (fun (_ y : Fin 1 → ℝ) => A (y 0))
        (fun _ y => G (y 0)) 0 (fun _ => x) := by
  rw [finiteStepD_eq_stepMD, pairedSecondMean_scalar_ratio hA hG]
  have he (y : ℝ) : m * (2 * A y) = (2 * m) * A y := by ring
  simp only [GTFrame.stepMD, hF, hD, he]

private theorem finOne_const_eval (y : Fin 1 → ℝ) : (fun _ : Fin 1 => y 0) = y := by
  funext i
  exact congrArg y (Subsingleton.elim 0 i)

private theorem finOne_shift_const_eval (x c : ℝ) (z : Fin 1 → ℝ) :
    (fun _ : Fin 1 => x + c * z 0) = (fun i => x + c * z i) :=
  finOne_const_eval (fun i => x + c * z i)

/-- Each shared level is exactly the corresponding normalized scalar mean.
The first shared level averages the square of the inserted inner slope. -/
theorem splitScalarCascadeD_shared_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    {j : ℕ} (hj : j ≤ r - 1) (x : ℝ) :
    splitScalarCascadeD (fun i => section5Mass s r m (k + 2 - i))
      (fun i => section5Variance s β r (k + 2 - i))
      (k + 3 - r) (k + 2 - r + 2 + j) v 0 (x, x) =
      section4VarianceQ s β r m j v 0 (fun _ => x) := by
  induction j generalizing x with
  | zero =>
    have hd : ¬ k + 2 - r + 1 < k + 3 - r := by omega
    have hp : k + 2 - (k + 2 - r + 1) = r - 1 := by omega
    have hpr : r - 1 < r := by omega
    have hpr' : ¬ r < r - 1 := by omega
    have hpre : r - 1 ≠ r := by omega
    have hpre' : r - 1 + 1 = r := by omega
    have hF (y : ℝ) := section5_zero_diag s β hr0 hr hm hv (k + 2 - r + 1) y
    simp only [section4Cascade_inserted s β (r := r) (by omega)] at hF
    have hD (y : ℝ) :
        splitScalarCascadeD (fun i => section5Mass s r m (k + 2 - i))
          (fun i => section5Variance s β r (k + 2 - i)) (k + 3 - r)
          (k + 2 - r + 1) v 0 (y, y) =
        (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) m v y) ^ 2 := by
      rw [splitScalarCascadeD_inserted_zero s β (by omega), pow_two]
    have H := finiteStepD_diag_scalar
      (measurable_parisiStep (parisiF_measurable s β _) m v)
      ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 m v).pow_const 2)
      v hF hD (s.m (r - 1) / 2) (β ^ 2 * (s.q r - s.q (r - 1)) - v) x
    have he : 2 * (s.m (r - 1) / 2) = s.m (r - 1) := by ring
    simp only [he] at H
    simpa only [Nat.add_zero, show k + 2 - r + 2 = (k + 2 - r + 1) + 1 by omega,
      splitScalarCascadeD, if_neg hd, hp, section5Mass, if_pos hpr,
      section5Variance, if_neg hpr', if_neg hpre, hpre', if_true,
      finiteStepD_eq_stepMD, GTFrame.stepMD, section4VarianceQ] using H
  | succ j ih =>
    have hd : ¬ k + 2 - r + 2 + j < k + 3 - r := by omega
    have hp : k + 2 - (k + 2 - r + 2 + j) < r - 1 := by omega
    have hp' : k + 2 - (k + 2 - r + 2 + j) < r := by omega
    have hpr : ¬ r < k + 2 - (k + 2 - r + 2 + j) := by omega
    have hpre : k + 2 - (k + 2 - r + 2 + j) ≠ r := by omega
    have hpre' : k + 2 - (k + 2 - r + 2 + j) + 1 ≠ r := by omega
    have hF (y : ℝ) := section5_zero_diag s β hr0 hr hm hv (k + 2 - r + 2 + j) y
    have hD (y : ℝ) := ih (by omega) y
    have hG : Measurable (fun z : ℝ => section4VarianceQ s β r m j v 0 (fun _ => z)) :=
      (measurable_section4VarianceQ s β r m j v).comp
        (show Measurable (fun z : ℝ => ((0 : Fin 1 → ℝ), fun _ : Fin 1 => z)) by fun_prop)
    have H := finiteStepD_diag_scalar (scalarFieldCascade_props _ _ _).1 hG v hF hD
      (s.m (k + 2 - (k + 2 - r + 2 + j)) / 2)
      (β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) -
        s.q (k + 2 - (k + 2 - r + 2 + j)))) x
    have he (z : ℝ) : 2 * (z / 2) = z := by ring
    simp only [he] at H
    change splitScalarCascadeD _ _ _ ((k + 2 - r + 2 + j) + 1) v 0 (x, x) = _
    rw [splitScalarCascadeD, if_neg hd]
    simpa only [section5Mass, if_pos hp', section5Variance,
      if_neg hpr, if_neg hpre, if_neg hpre', finiteStepD_eq_stepMD, GTFrame.stepMD,
      section4VarianceQ, pairedSecondMean, pairedTiltMean, finOne_shift_const_eval] using H

/-- The actual lambda derivative at zero is the full normalized squared-slope
average, on the closed physical split interval. No upper mass bound is needed. -/
theorem hasDerivAt_section5V_zero_Q {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section5V s β h r m v) (section4TVarianceQ s β h r m v) 0 := by
  have he : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  have H := splitScalarCascadeD_shared_zero s β hr0 hr hm hv (j := r - 1) le_rfl h
  simp only [he] at H
  rw [section4TVarianceQ, ← H]
  exact hasDerivAt_section5V s β h hr hm v 0

theorem deriv_section5V_zero_eq_Q {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (section5V s β h r m v) 0 = section4TVarianceQ s β h r m v :=
  (hasDerivAt_section5V_zero_Q s β h hr0 hr hm hv).deriv

/-- Talagrand Lemma 5.8 on the interior: the zero-lambda derivative of the
actual paired transform is the ordinary variance derivative of the actual U. -/
theorem talagrand_lemma_5_8 {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (section5V s β h r (s.m (r - 1)) v) 0 = deriv (section4U s β h r) v := by
  rw [deriv_section5V_zero_eq_Q s β h hr0 hr (s.m_nonneg (by omega)) ⟨hv.1.le, hv.2.le⟩,
    (hasDerivAt_section4U s β h hr0 hr hm hv).deriv]

/-- Endpoint-safe form of Lemma 5.8. This statement also covers a degenerate
split interval, without asserting uniqueness of its within derivative. -/
theorem hasDerivWithinAt_section4U_eq_section5V_lambda {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivWithinAt (section4U s β h r)
      (deriv (section5V s β h r (s.m (r - 1)) v) 0)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v := by
  rw [deriv_section5V_zero_eq_Q s β h hr0 hr (s.m_nonneg (by omega)) hv]
  exact hasDerivWithinAt_section4U s β h hr0 hr hm hv

/-- Numerical inward-derivative version of Lemma 5.8 at either endpoint,
with the nondegenerate interval hypothesis needed for uniqueness. -/
theorem talagrand_lemma_5_8_within {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1)
    (ha : 0 < β ^ 2 * (s.q r - s.q (r - 1))) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (section5V s β h r (s.m (r - 1)) v) 0 =
      derivWithin (section4U s β h r) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v := by
  rw [deriv_section5V_zero_eq_Q s β h hr0 hr (s.m_nonneg (by omega)) hv,
    derivWithin_section4U_eq s β h hr0 hr hm ha hv]

/-- The optimized scalar gain with its derivative identified as the actual Q.
This remains valid for all baseline masses, including zero and one. -/
theorem section5V_baseline_lambda_gain_Q {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (u : ℝ) :
    ∃ l : ℝ, section5V s β h r (s.m (r - 1)) v l - l * u ≤
      2 * parisiF s β (k + 2) h -
        (section4TVarianceQ s β h r (s.m (r - 1)) v - u) ^ 2 / 2 := by
  simpa only [deriv_section5V_zero_eq_Q s β h hr0 hr (m := s.m (r - 1))
    (s.m_nonneg (by omega)) hv] using
    section5V_baseline_lambda_gain s β h hr0 hr hv u

/-- The actual second interpolation's time-zero quadratic gain, with the
Lemma 5.8 normalized factor substituted. Transport in interpolation time and
the uniform optimality estimates remain separate obligations. -/
theorem section5Interpolation_zero_lambda_gain_Q
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5Interpolation n s β h U r (s.m (r - 1)) t u 0 ≤
      2 * (Real.log 2 + parisiF s β (k + 2) h) -
        (section4TVarianceQ s β h r (s.m (r - 1)) (t * (β ^ 2 * (s.q r - u))) - u) ^ 2 / 2 := by
  simpa only [deriv_section5V_zero_eq_Q s β h hr0 hr (m := s.m (r - 1)) (s.m_nonneg (by omega))
    (section5SplitVariance_mem s β ht hu)] using
    section5Interpolation_zero_lambda_gain hn s β h U hr0 hr ht hu hu'

end SpinGlass.Targets
