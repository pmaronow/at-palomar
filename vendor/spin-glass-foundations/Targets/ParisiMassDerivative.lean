module

public import Targets.CascadeDeriv
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-!
# Mass differentiation of the scalar Parisi step

The first mass-variation ingredient for Talagrand's Section 4. Mathlib's analytic
moment-generating-function theorem supplies differentiation under the integral;
the existing Gaussian linear-growth estimates discharge its hypotheses for the
actual scalar `parisiStep`, including all actual `parisiF` input levels.

This file does not assert the nested Section 4 optimality identities. The mass
being varied is one smoothing mass, with its input function held fixed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

theorem parisiStep_integrableExpSet {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    integrableExpSet (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) = Set.univ := by
  ext m
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v

theorem hasDerivAt_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) {m : ℝ} (hm : m ≠ 0) (v x : ℝ) :
    HasDerivAt (fun a => parisiStep a v A x)
      (((∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1))
        - parisiStep m v A x) / m) m := by
  have hmem : m ∈ interior (integrableExpSet
      (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
    rw [parisiStep_integrableExpSet hA hmeas, interior_univ]
    trivial
  have hpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
    smoothing_integral_pos hA hmeas x
  have hd := ((hasDerivAt_mgf hmem).log hpos.ne').div (hasDerivAt_id m) hm
  have heq : (fun a => parisiStep a v A x) =ᶠ[𝓝 m]
      fun a => Real.log (mgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) a) / a := by
    filter_upwards [eventually_ne_nhds hm] with a ha
    simp [parisiStep, ha, mgf, div_eq_mul_inv, mul_comm]
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  simp only [tiltWeight, if_neg hm, ← mul_div_assoc, integral_div, parisiStep, mgf, id_eq]
  field_simp
  simp only [mul_comm]

/-- The genuine normalized Gaussian tilt has integrable density. -/
theorem integrable_tiltWeight_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v x : ℝ) :
      Integrable (tiltWeight m v A x) (gaussianReal 0 1) := by
  change Integrable (fun z => tiltWeight m v A x z) (gaussianReal 0 1)
  by_cases hm : m = 0
  · simp [tiltWeight, hm]
  · simpa only [tiltWeight, if_neg hm] using
      (integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v).div_const
        (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))

/-- The tilted first moment is integrable, without a bounded-input assumption. -/
theorem integrable_self_mul_tiltWeight_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v x : ℝ) :
    Integrable (fun z => A (x + Real.sqrt v * z) * tiltWeight m v A x z)
      (gaussianReal 0 1) := by
  by_cases hm : m = 0
  · simpa [tiltWeight, hm] using integrable_of_hasLinearGrowth hA hmeas x v
  · have hmem : m ∈ interior (integrableExpSet
        (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
      rw [parisiStep_integrableExpSet hA hmeas, interior_univ]
      trivial
    simpa only [tiltWeight, if_neg hm, mul_div_assoc, pow_one] using
      (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1).div_const
        (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))

theorem log_tiltWeight_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) {m : ℝ} (hm : m ≠ 0) (v x z : ℝ) :
    Real.log (tiltWeight m v A x z) = m * (A (x + Real.sqrt v * z) - parisiStep m v A x) := by
  have hpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
    smoothing_integral_pos hA hmeas x
  rw [tiltWeight, if_neg hm, Real.log_div (Real.exp_ne_zero _) hpos.ne', Real.log_exp,
    parisiStep, if_neg hm]
  field_simp

/-- Integrability of the density times its logarithm is proved from Gaussian moments. -/
theorem integrable_tiltWeight_mul_log_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v x : ℝ) :
    Integrable (fun z => tiltWeight m v A x z * Real.log (tiltWeight m v A x z))
      (gaussianReal 0 1) := by
  by_cases hm : m = 0
  · simp [tiltWeight, hm]
  · have hi := ((integrable_self_mul_tiltWeight_mass hA hmeas m v x).sub
        ((integrable_tiltWeight_mass hA hmeas m v x).const_mul (parisiStep m v A x))).const_mul m
    refine hi.congr (Eventually.of_forall fun z => ?_)
    dsimp only [Pi.sub_apply]
    rw [log_tiltWeight_mass hA hmeas hm]
    ring

/-- The entropy identity for the actual exponential density of a scalar step. -/
theorem integral_tiltWeight_mul_log_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) {m : ℝ} (hm : m ≠ 0) (v x : ℝ) :
    (∫ z, tiltWeight m v A x z * Real.log (tiltWeight m v A x z) ∂(gaussianReal 0 1)) =
      m * ((∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1))
        - parisiStep m v A x) := by
  have heq : (fun z => tiltWeight m v A x z * Real.log (tiltWeight m v A x z)) =
      fun z => m * (A (x + Real.sqrt v * z) * tiltWeight m v A x z -
        parisiStep m v A x * tiltWeight m v A x z) := by
    funext z
    rw [log_tiltWeight_mass hA hmeas hm]
    ring
  rw [heq, integral_const_mul,
    integral_sub (integrable_self_mul_tiltWeight_mass hA hmeas m v x)
      ((integrable_tiltWeight_mass hA hmeas m v x).const_mul _),
    integral_const_mul, tiltWeight_integral_one hA hmeas, mul_one]

theorem integral_tiltWeight_mul_log_nonneg {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v x : ℝ) :
    0 ≤ ∫ z, tiltWeight m v A x z * Real.log (tiltWeight m v A x z) ∂(gaussianReal 0 1) := by
  have hle := integral_mono
    ((integrable_tiltWeight_mass hA hmeas m v x).sub (integrable_const 1))
    (integrable_tiltWeight_mul_log_mass hA hmeas m v x)
    (fun z => Real.self_sub_one_le_mul_log (tiltWeight_nonneg hA hmeas x z))
  simpa only [Pi.sub_apply,
    integral_sub (integrable_tiltWeight_mass hA hmeas m v x) (integrable_const 1),
    tiltWeight_integral_one hA hmeas, integral_const, probReal_univ, one_smul, sub_self] using hle

/-- Mass differentiation is the normalized entropy divided by the square of the mass. -/
theorem hasDerivAt_parisiStep_mass_entropy {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) {m : ℝ} (hm : m ≠ 0) (v x : ℝ) :
    HasDerivAt (fun a => parisiStep a v A x)
      ((∫ z, tiltWeight m v A x z * Real.log (tiltWeight m v A x z)
        ∂(gaussianReal 0 1)) / m ^ 2) m := by
  apply (hasDerivAt_parisiStep_mass hA hmeas hm v x).congr_deriv
  rw [integral_tiltWeight_mul_log_mass hA hmeas hm]
  field_simp

theorem deriv_parisiStep_mass_nonneg {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) {m : ℝ} (hm : m ≠ 0) (v x : ℝ) :
    0 ≤ deriv (fun a => parisiStep a v A x) m := by
  rw [(hasDerivAt_parisiStep_mass_entropy hA hmeas hm v x).deriv]
  exact div_nonneg (integral_tiltWeight_mul_log_nonneg hA hmeas m v x) (sq_nonneg m)

/-- In particular the actual log-Laplace step increases with its positive mass. -/
theorem monotoneOn_parisiStep_mass_pos {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    MonotoneOn (fun m => parisiStep m v A x) (Set.Ioi 0) := by
  have hd : ∀ m ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun a => parisiStep a v A x) m :=
    fun m hm => (hasDerivAt_parisiStep_mass hA hmeas (ne_of_gt hm) v x).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun m hm => (hd m hm).continuousAt.continuousWithinAt)
    (fun m hm => (hd m (interior_subset hm)).differentiableWithinAt) ?_
  intro m hm
  exact deriv_parisiStep_mass_nonneg hA hmeas (ne_of_gt (interior_subset hm)) v x

/-- Specialization to the actual input at any level of the Parisi recursion. -/
theorem hasDerivAt_parisiStep_parisiF_mass {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ≠ 0) (v x : ℝ) :
    HasDerivAt (fun a => parisiStep a v (parisiF s β j) x)
      (((∫ z, parisiF s β j (x + Real.sqrt v * z) *
        tiltWeight m v (parisiF s β j) x z ∂(gaussianReal 0 1))
        - parisiStep m v (parisiF s β j) x) / m) m :=
  hasDerivAt_parisiStep_mass (parisiF_hasLinearGrowth s β j) (parisiF_measurable s β j) hm v x

end SpinGlass.Targets
