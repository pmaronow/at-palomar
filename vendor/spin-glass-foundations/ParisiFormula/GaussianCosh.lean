module

/-
# Gaussian integrals of `cosh` and `log cosh`

New work for the ParisiFormula project (not vendored).

These are the analytic ingredients of **Target 2a** (`parisiFunctional_rsScheme`), the
replica-symmetric sanity check of the Parisi functional in `Targets/Milestones.lean`.

The three facts needed there are:

* `integral_cosh_add_mul_stdGaussian` : `∫ cosh (x + σ z) dγ(z) = cosh x · exp (σ²/2)`.
  This is what turns the `m = 1` smoothing step `T_{1, β²(1-q)}` applied to `log cosh`
  into `log cosh x + β²(1-q)/2`.

* `integrable_log_cosh_stdGaussian` : `z ↦ log cosh (a z + b)` is `γ`-integrable, which
  is what lets the `m = 0` step be split as
  `∫ (log cosh (h + c z) + const) dγ = ∫ log cosh (h + c z) dγ + const`.

* `integral_reflect_stdGaussian` : `∫ f (b - a z) dγ = ∫ f (b + a z) dγ`.
  This is needed because `√(β² q) = |β| √q`, while Target 2a is stated with `β √q` and
  *no* sign hypothesis on `β`; the two agree under the (symmetric) Gaussian.

Throughout, `γ = gaussianReal 0 1` is the standard Gaussian on `ℝ`.
-/
public import ParisiFormula.AnnealedBound
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass

/-! ## 1. The Gaussian exponential moment -/

/-- `∫ exp (t z) dγ(z) = exp (t²/2)` for the standard Gaussian `γ`. -/
theorem integral_exp_mul_stdGaussian (t : ℝ) :
    (∫ z, Real.exp (t * z) ∂(gaussianReal 0 1)) = Real.exp (t ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id_eq] at h
  rw [h]
  norm_num

/-- `exp (t · )` is `γ`-integrable. -/
theorem integrable_exp_mul_stdGaussian (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t * z)) (gaussianReal 0 1) :=
  integrable_exp_mul_gaussianReal t

/-! ## 2. The Gaussian integral of `cosh` -/

/--
**The key Gaussian `cosh` integral**: `∫ cosh (x + σ z) dγ(z) = cosh x · exp (σ²/2)`.

This is the identity behind the `m = 1` replica-symmetric smoothing step.
-/
theorem integral_cosh_add_mul_stdGaussian (x σ : ℝ) :
    (∫ z, Real.cosh (x + σ * z) ∂(gaussianReal 0 1))
      = Real.cosh x * Real.exp (σ ^ 2 / 2) := by
  have hpt : ∀ z : ℝ, Real.cosh (x + σ * z)
      = Real.exp x / 2 * Real.exp (σ * z)
        + Real.exp (-x) / 2 * Real.exp (-σ * z) := by
    intro z
    rw [Real.cosh_eq]
    rw [show x + σ * z = x + σ * z from rfl]
    rw [Real.exp_add, show -(x + σ * z) = -x + -σ * z by ring, Real.exp_add]
    ring
  have hint1 : Integrable (fun z : ℝ => Real.exp x / 2 * Real.exp (σ * z))
      (gaussianReal 0 1) := (integrable_exp_mul_stdGaussian σ).const_mul _
  have hint2 : Integrable (fun z : ℝ => Real.exp (-x) / 2 * Real.exp (-σ * z))
      (gaussianReal 0 1) := (integrable_exp_mul_stdGaussian (-σ)).const_mul _
  calc
    (∫ z, Real.cosh (x + σ * z) ∂(gaussianReal 0 1))
        = ∫ z, (Real.exp x / 2 * Real.exp (σ * z)
              + Real.exp (-x) / 2 * Real.exp (-σ * z)) ∂(gaussianReal 0 1) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z, Real.exp x / 2 * Real.exp (σ * z) ∂(gaussianReal 0 1))
          + ∫ z, Real.exp (-x) / 2 * Real.exp (-σ * z) ∂(gaussianReal 0 1) :=
          integral_add hint1 hint2
    _ = Real.exp x / 2 * Real.exp (σ ^ 2 / 2)
          + Real.exp (-x) / 2 * Real.exp ((-σ) ^ 2 / 2) := by
          rw [integral_const_mul, integral_const_mul,
              integral_exp_mul_stdGaussian σ, integral_exp_mul_stdGaussian (-σ)]
    _ = Real.cosh x * Real.exp (σ ^ 2 / 2) := by
          rw [Real.cosh_eq]
          rw [show (-σ) ^ 2 = σ ^ 2 by ring]
          ring

/-! ## 3. Integrability of `log cosh` -/

/-- `0 ≤ log (cosh y)`, since `1 ≤ cosh y`. -/
theorem log_cosh_nonneg (y : ℝ) : 0 ≤ Real.log (Real.cosh y) :=
  Real.log_nonneg (Real.one_le_cosh y)

/-- `log (cosh y) ≤ |y|`, since `cosh y ≤ exp |y|`. -/
theorem log_cosh_le_abs (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
  have hcosh : Real.cosh y ≤ Real.exp |y| := by
    rw [Real.cosh_eq]
    have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
    have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.2 (neg_le_abs y)
    linarith
  calc
    Real.log (Real.cosh y) ≤ Real.log (Real.exp |y|) :=
      Real.log_le_log (Real.cosh_pos y) hcosh
    _ = |y| := Real.log_exp _

/--
`z ↦ log cosh (b + a z)` is continuous.  (`fun_prop` cannot do this on its own: `Real.log`
is not continuous at `0`, so it needs `cosh > 0`.)
-/
theorem continuous_log_cosh_affine (a b : ℝ) :
    Continuous (fun z : ℝ => Real.log (Real.cosh (b + a * z))) :=
  (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => ne_of_gt (Real.cosh_pos _))

/-- `z ↦ z` is `γ`-integrable. -/
theorem integrable_id_stdGaussian :
    Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (le_refl 1)

/-- `z ↦ log cosh (b + a z)` is `γ`-integrable, by `0 ≤ log cosh y ≤ |y|`. -/
theorem integrable_log_cosh_stdGaussian (a b : ℝ) :
    Integrable (fun z : ℝ => Real.log (Real.cosh (b + a * z))) (gaussianReal 0 1) := by
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => Real.log (Real.cosh (b + a * z))) (gaussianReal 0 1) :=
    (continuous_log_cosh_affine a b).aestronglyMeasurable
  have hdom : Integrable (fun z : ℝ => |b + a * z|) (gaussianReal 0 1) :=
    ((integrable_const b).add (integrable_id_stdGaussian.const_mul a)).abs
  refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg _)]
  exact log_cosh_le_abs _

/-! ## 4. Reflection symmetry of the standard Gaussian -/

/--
`∫ f (b + a z) dγ(z) = ∫ f (b - a z) dγ(z)`: the standard Gaussian is symmetric.

Needed because `√(β² q) = |β| √q`, while Target 2a is stated with `β √q` and no sign
hypothesis on `β`.
-/
theorem integral_reflect_stdGaussian {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    (∫ z, f (b + a * z) ∂(gaussianReal 0 1))
      = ∫ z, f (b + -a * z) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hcont : Continuous (fun z : ℝ => f (b + a * z)) :=
    hf.comp (continuous_const.add (continuous_const.mul continuous_id))
  calc
    (∫ z, f (b + a * z) ∂(gaussianReal 0 1))
        = ∫ z, f (b + a * z) ∂((gaussianReal 0 1).map (fun x : ℝ => -x)) := by
          rw [hmap]
    _ = ∫ z, f (b + a * -z) ∂(gaussianReal 0 1) := by
          rw [integral_map measurable_neg.aemeasurable hcont.aestronglyMeasurable]
    _ = ∫ z, f (b + -a * z) ∂(gaussianReal 0 1) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          show f (b + a * -z) = f (b + -a * z)
          congr 1
          ring

/-! ## 5. Gaussian rescaling -/

/--
**Rescaling a standard Gaussian**: `∫ f (x + √v z) dγ_{0,1}(z) = ∫ f (x + w) dγ_{0,v}(w)`.

This is the identity that reconciles `Targets.parisiStep` (which smooths against the
*standard* Gaussian after scaling the variable by `√v`) with `SpinGlass.Parisi.T` (which
smooths against `γ_{0,v}` directly).
-/
theorem integral_comp_sqrt_mul_gaussianReal (v : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f)
    (x : ℝ) :
    (∫ z, f (x + Real.sqrt (v : ℝ) * z) ∂(gaussianReal 0 1))
      = ∫ w, f (x + w) ∂(gaussianReal 0 v) := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z)
      = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    -- `congr 1` splits into the mean and variance components; this avoids having to
    -- match `NNReal.mk` syntactically (proof terms are handled by irrelevance).
    congr 1
    · ring
    · rw [mul_one]
      exact NNReal.coe_injective (by simpa using Real.sq_sqrt v.coe_nonneg)
  have hcomp : Measurable (fun w : ℝ => f (x + w)) := hf.comp (measurable_const_add x)
  have h := integral_map (μ := gaussianReal (0 : ℝ) 1)
    (φ := fun z : ℝ => Real.sqrt (v : ℝ) * z) (by fun_prop)
    (f := fun w : ℝ => f (x + w)) hcomp.aestronglyMeasurable
  rw [hmap] at h
  exact h.symm

/-! ## 6. Linear growth and the integrability it buys

Target 2b's inductive engine (`Targets.parisiStep_dist_le`) carries integrability
hypotheses.  Discharging them for `parisiF` at every level is the "moderate growth" item of
Phase 2 in `docs/ROADMAP.md`.  The right invariant is *linear* growth: the base of the Parisi
recursion is `log cosh`, which satisfies `0 ≤ log cosh y ≤ |y|`, and each smoothing step
preserves linear growth.
-/

/-- `exp (a |z|)` is `γ`-integrable, for every real `a`. -/
theorem integrable_exp_abs_mul_stdGaussian (a : ℝ) :
    Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 1) := by
  have hdom : Integrable
      (fun z : ℝ => Real.exp (a * z) + Real.exp (-a * z)) (gaussianReal 0 1) :=
    (integrable_exp_mul_stdGaussian a).add (integrable_exp_mul_stdGaussian (-a))
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 1) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have : 0 < Real.exp (-a * z) := Real.exp_pos _
    linarith
  · rw [abs_of_neg hz, show a * -z = -a * z by ring]
    have : 0 < Real.exp (a * z) := Real.exp_pos _
    linarith

/-- `A` has at most linear growth: `|A y| ≤ C + D |y|` for some `C, D ≥ 0`. -/
def HasLinearGrowth (A : ℝ → ℝ) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ y, |A y| ≤ C + D * |y|

/-- The base of the Parisi recursion has linear growth: `|log cosh y| ≤ |y|`. -/
theorem hasLinearGrowth_log_cosh :
    HasLinearGrowth (fun y => Real.log (Real.cosh y)) := by
  refine ⟨0, 1, le_rfl, zero_le_one, fun y => ?_⟩
  rw [abs_of_nonneg (log_cosh_nonneg y)]
  simpa using log_cosh_le_abs y

/-- A linearly growing measurable function is `γ`-integrable along `z ↦ x + √v z`. -/
theorem integrable_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x v : ℝ) :
    Integrable (fun z : ℝ => A (x + Real.sqrt v * z)) (gaussianReal 0 1) := by
  obtain ⟨C, D, hC, hD, hbound⟩ := hA
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ => A (x + Real.sqrt v * z)) (gaussianReal 0 1) :=
    (hmeas.comp (measurable_const_add x |>.comp (measurable_id.const_mul _)))
      |>.aestronglyMeasurable
  have hdom : Integrable
      (fun z : ℝ => (C + D * |x|) + (D * |Real.sqrt v|) * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add
      ((integrable_id_stdGaussian.abs).const_mul _)
  refine hdom.mono' hmeas' (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs]
  refine (hbound (x + Real.sqrt v * z)).trans ?_
  have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
    calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
      _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
  nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]

/-- The exponential of a linearly growing measurable function is `γ`-integrable. -/
theorem integrable_exp_mul_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m x v : ℝ) :
    Integrable (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) := by
  obtain ⟨C, D, hC, hD, hbound⟩ := hA
  set a : ℝ := |m| * (D * |Real.sqrt v|) with ha
  set b : ℝ := |m| * (C + D * |x|) with hb
  have hmeas' : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) :=
    ((Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_const_add x |>.comp (measurable_id.const_mul _))).const_mul m))
      |>.aestronglyMeasurable
  have hdom : Integrable
      (fun z : ℝ => Real.exp b * Real.exp (a * |z|)) (gaussianReal 0 1) :=
    (integrable_exp_abs_mul_stdGaussian a).const_mul _
  refine hdom.mono' hmeas' (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
    calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
      _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
  have h1 : m * A (x + Real.sqrt v * z) ≤ |m| * |A (x + Real.sqrt v * z)| := by
    calc m * A (x + Real.sqrt v * z) ≤ |m * A (x + Real.sqrt v * z)| := le_abs_self _
      _ = |m| * |A (x + Real.sqrt v * z)| := abs_mul _ _
  have h2 : |A (x + Real.sqrt v * z)| ≤ C + D * (|x| + |Real.sqrt v| * |z|) := by
    refine (hbound (x + Real.sqrt v * z)).trans ?_
    nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]
  have h3 : |m| * |A (x + Real.sqrt v * z)| ≤ |m| * (C + D * (|x| + |Real.sqrt v| * |z|)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg m)
  have h4 : |m| * (C + D * (|x| + |Real.sqrt v| * |z|)) = b + a * |z| := by
    rw [ha, hb]; ring
  linarith

/-! ## 7. `log cosh` is 1-Lipschitz

Linear growth (§6) buys integrability.  For Target 2b one also needs *Lipschitz* control:
when the scheme parameter `q_p` moves, the variance of the smoothing step moves, and the
argument `x + √v z` moves by `(√v - √v') z` — which is not uniformly small, so
`parisiStep_dist_le` cannot be applied to it unless the function being smoothed is Lipschitz.

The base of the Parisi recursion is 1-Lipschitz, and (via `parisiStep_dist_le`, applied after
translating the argument) the smoothing step does not increase the Lipschitz constant.  So
every level `F_p` of the recursion is 1-Lipschitz.
-/

/-- `cosh a ≤ cosh b · exp |a - b|`. -/
theorem cosh_le_cosh_mul_exp_abs (a b : ℝ) :
    Real.cosh a ≤ Real.cosh b * Real.exp |a - b| := by
  rw [Real.cosh_eq, Real.cosh_eq]
  rcases le_or_gt b a with hab | hab
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    have e1 : Real.exp b * Real.exp (a - b) = Real.exp a := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-b) * Real.exp (a - b) = Real.exp (a - 2 * b) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : (Real.exp b + Real.exp (-b)) / 2 * Real.exp (a - b)
        = (Real.exp a + Real.exp (a - 2 * b)) / 2 := by
      rw [div_mul_eq_mul_div, add_mul, e1, e2]
    rw [hexp]
    have h : Real.exp (-a) ≤ Real.exp (a - 2 * b) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · rw [abs_of_neg (by linarith : a - b < 0)]
    have e1 : Real.exp b * Real.exp (-(a - b)) = Real.exp (2 * b - a) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-b) * Real.exp (-(a - b)) = Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : (Real.exp b + Real.exp (-b)) / 2 * Real.exp (-(a - b))
        = (Real.exp (2 * b - a) + Real.exp (-a)) / 2 := by
      rw [div_mul_eq_mul_div, add_mul, e1, e2]
    rw [hexp]
    have h : Real.exp a ≤ Real.exp (2 * b - a) :=
      Real.exp_le_exp.2 (by linarith)
    linarith

/-- **`log cosh` is 1-Lipschitz.**  This is the base case of the Lipschitz induction. -/
theorem log_cosh_dist_le (a b : ℝ) :
    |Real.log (Real.cosh a) - Real.log (Real.cosh b)| ≤ |a - b| := by
  have hone : ∀ u w : ℝ,
      Real.log (Real.cosh u) - Real.log (Real.cosh w) ≤ |u - w| := by
    intro u w
    have h := Real.log_le_log (Real.cosh_pos u) (cosh_le_cosh_mul_exp_abs u w)
    rw [Real.log_mul (ne_of_gt (Real.cosh_pos w)) (Real.exp_ne_zero _), Real.log_exp] at h
    linarith
  refine abs_le.2 ⟨?_, hone a b⟩
  have h := hone b a
  rw [abs_sub_comm] at h
  linarith

/-! ## 8. Shifting a Lipschitz function by a Gaussian

The remaining quantitative input for Target 2b is a bound on `|T_{m,w} A - A|` for small
variance `w`, which via the semigroup law `Parisi.T_add` controls a change of the scheme
parameter `q_p`.

This section proves the `m = 0` case, which is also the *mean* term of the general case:
writing `g z = A (x + √w z) - A x`, the general bound is `|𝔼 g| + |m| L² w / 2`, with the
second term coming from the Herbst bound of §`GaussianConcentration1D` and the first from
the estimate here.
-/

/--
**Shifting a Lipschitz function by a centred Gaussian moves its mean by at most
`L √w 𝔼|Z|`.**

This is exactly the `m = 0` branch of `parisiStep`, and simultaneously the mean term of the
`m ≠ 0` branch.
-/
theorem abs_integral_shift_sub_le {A : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x w : ℝ) :
    |(∫ z, A (x + Real.sqrt w * z) ∂(gaussianReal 0 1)) - A x|
      ≤ L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := by
  classical
  have hint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z)) (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth hA hmeas x w
  have hdom : Integrable
      (fun z : ℝ => L * Real.sqrt w * |z|) (gaussianReal 0 1) :=
    (integrable_id_stdGaussian.abs).const_mul _
  have hpt : ∀ z : ℝ, |A (x + Real.sqrt w * z) - A x| ≤ L * Real.sqrt w * |z| := by
    intro z
    have h := hLip (x + Real.sqrt w * z) x
    have hrw : |x + Real.sqrt w * z - x| = Real.sqrt w * |z| := by
      rw [show x + Real.sqrt w * z - x = Real.sqrt w * z by ring, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg w)]
    rw [hrw] at h
    calc |A (x + Real.sqrt w * z) - A x| ≤ L * (Real.sqrt w * |z|) := h
      _ = L * Real.sqrt w * |z| := by ring
  calc |(∫ z, A (x + Real.sqrt w * z) ∂(gaussianReal 0 1)) - A x|
      = |∫ z, (A (x + Real.sqrt w * z) - A x) ∂(gaussianReal 0 1)| := by
        rw [integral_sub hint (integrable_const _)]
        simp [probReal_univ]
    _ ≤ ∫ z, |A (x + Real.sqrt w * z) - A x| ∂(gaussianReal 0 1) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (gaussianReal 0 1))
            (f := fun z => A (x + Real.sqrt w * z) - A x)
    _ ≤ ∫ z, L * Real.sqrt w * |z| ∂(gaussianReal 0 1) :=
        integral_mono (hint.sub (integrable_const _)).abs hdom hpt
    _ = L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := integral_const_mul _ _


/-! ## 9. The second-order invariant of the Parisi recursion

Target 2b asks for a **Lipschitz** bound in `q` (Talagrand's actual statement, not a weaker
Hölder one).  That needs the first-order term of the variance perturbation to vanish:

  `∫ A (x + √w z) dγ - A x = (w/2) A''(x) + O(w²)`,

which requires control of `A''`.  A *uniform* bound `|A''| ≤ M` is the obvious candidate and
**it does not work**: differentiating the smoothing step gives

  `(T_{m,v} A)'' = ⟨A''⟩ + m · Var_tilt(A')`,

so `M` increases by `|m| L²` at every level and grows linearly in `k`, destroying the
uniformity in `k` that Target 2b requires.

The invariant that *is* preserved is the coupled one

  `0 ≤ A'' ≤ 1 - (A')²`,

because with `⟨·⟩` the tilted average,

  `(T A)'' = ⟨A''⟩ + m Var(A') ≤ (1 - ⟨(A')²⟩) + m (⟨(A')²⟩ - ⟨A'⟩²)`
           `= 1 - (T A)'² - (1 - m)·Var(A') ≤ 1 - (T A)'²`,

using `Var ≥ 0` and — crucially — `m ≤ 1`, which every RSB scheme satisfies
(`RSBScheme.m_le_one`).  In particular it gives `|A''| ≤ 1` uniformly in the level and in `k`.

`log cosh` satisfies it with *equality*: `(log cosh)'' = 1/cosh² = 1 - tanh²`.
-/

/-- `A` is twice differentiable with derivatives `A'`, `A''` satisfying the coupled
second-order bound `0 ≤ A'' ≤ 1 - (A')²` that the Parisi recursion preserves. -/
def HasParisiC2 (A A' A'' : ℝ → ℝ) : Prop :=
  (∀ x, HasDerivAt A (A' x) x) ∧ (∀ x, HasDerivAt A' (A'' x) x)
    ∧ (∀ x, 0 ≤ A'' x) ∧ (∀ x, A'' x ≤ 1 - (A' x) ^ 2)

/-- `log cosh` has derivative `tanh = sinh / cosh`. -/
theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.sinh x / Real.cosh x) x :=
  (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))

/-- `tanh` has derivative `1 - tanh²`. -/
theorem hasDerivAt_sinh_div_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
      (1 - (Real.sinh x / Real.cosh x) ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hid : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
      = 1 - (Real.sinh x / Real.cosh x) ^ 2 := by
    have hpyth : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    field_simp
    try nlinarith [hpyth]
  rwa [hid] at h

/-- **The base of the Parisi recursion satisfies the second-order invariant**, with
equality: `(log cosh)'' = 1 - (log cosh)'²`. -/
theorem hasParisiC2_log_cosh :
    HasParisiC2 (fun y : ℝ => Real.log (Real.cosh y))
      (fun y : ℝ => Real.sinh y / Real.cosh y)
      (fun y : ℝ => 1 - (Real.sinh y / Real.cosh y) ^ 2) := by
  refine ⟨hasDerivAt_log_cosh, hasDerivAt_sinh_div_cosh, fun x => ?_, fun x => le_rfl⟩
  have hpyth : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  have hc : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
  -- beta-reduce before rewriting: the goal arrives as `0 ≤ (fun y => …) x`
  show (0 : ℝ) ≤ 1 - (Real.sinh x / Real.cosh x) ^ 2
  have hsq : (Real.sinh x / Real.cosh x) ^ 2 = Real.sinh x ^ 2 / Real.cosh x ^ 2 := by
    rw [div_pow]
  rw [hsq, sub_nonneg, div_le_one (by positivity)]
  linarith

/-- The invariant bounds the second derivative by `1`, uniformly. -/
theorem HasParisiC2.abs_second_le_one {A A' A'' : ℝ → ℝ} (h : HasParisiC2 A A' A'') (x : ℝ) :
    |A'' x| ≤ 1 := by
  obtain ⟨_, _, hnn, hle⟩ := h
  rw [abs_of_nonneg (hnn x)]
  nlinarith [hle x, sq_nonneg (A' x)]

/-- The invariant also bounds the first derivative by `1` — so every level is 1-Lipschitz,
consistently with `Targets.parisiF_lipschitz`. -/
theorem HasParisiC2.abs_first_le_one {A A' A'' : ℝ → ℝ} (h : HasParisiC2 A A' A'') (x : ℝ) :
    |A' x| ≤ 1 := by
  obtain ⟨_, _, hnn, hle⟩ := h
  have h1 : (A' x) ^ 2 ≤ 1 := by nlinarith [hnn x, hle x]
  nlinarith [abs_nonneg (A' x), sq_abs (A' x), h1]


/-! ## 10. Differentiating the smoothing integral

The propagation step for the second-order invariant needs

  `(T_{m,v} A)'' = ⟨A''⟩ + m · Var_tilt(A')`,

which is obtained by differentiating `G(x) = ∫ exp (m A (x + √v z)) dγ(z)` twice under the
integral sign.  This section does the first derivative; the domination is uniform over a ball
because `A` has linear growth and `A'` is bounded.
-/

/-- Uniform domination of `exp (m A (t + √v z))` for `t` in a ball around `x`. -/
theorem exp_mul_shift_ball_le {A : ℝ → ℝ} {C D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ y, |A y| ≤ C + D * |y|) (m x v : ℝ) {t : ℝ} (ht : |t - x| ≤ 1) (z : ℝ) :
    Real.exp (m * A (t + Real.sqrt v * z))
      ≤ Real.exp (|m| * (C + D * (|x| + 1)))
        * Real.exp ((|m| * (D * |Real.sqrt v|)) * |z|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have habs : |t + Real.sqrt v * z| ≤ (|x| + 1) + |Real.sqrt v| * |z| := by
    have h1 : |t| ≤ |x| + 1 := by
      have := abs_sub_abs_le_abs_sub t x
      have h2 : |t - x| ≤ 1 := ht
      linarith
    calc |t + Real.sqrt v * z| ≤ |t| + |Real.sqrt v * z| := abs_add_le _ _
      _ = |t| + |Real.sqrt v| * |z| := by rw [abs_mul]
      _ ≤ (|x| + 1) + |Real.sqrt v| * |z| := by linarith
  have h1 : m * A (t + Real.sqrt v * z) ≤ |m| * |A (t + Real.sqrt v * z)| := by
    calc m * A (t + Real.sqrt v * z) ≤ |m * A (t + Real.sqrt v * z)| := le_abs_self _
      _ = |m| * |A (t + Real.sqrt v * z)| := abs_mul _ _
  have h2 : |A (t + Real.sqrt v * z)| ≤ C + D * ((|x| + 1) + |Real.sqrt v| * |z|) := by
    refine (hb _).trans ?_
    nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]
  have h3 : |m| * |A (t + Real.sqrt v * z)|
      ≤ |m| * (C + D * ((|x| + 1) + |Real.sqrt v| * |z|)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg m)
  have h4 : |m| * (C + D * ((|x| + 1) + |Real.sqrt v| * |z|))
      = |m| * (C + D * (|x| + 1)) + (|m| * (D * |Real.sqrt v|)) * |z| := by ring
  linarith

/--
**First derivative of the smoothing integral.**

`d/dx ∫ exp (m A (x + √v z)) dγ(z) = ∫ m A' (x + √v z) exp (m A (x + √v z)) dγ(z)`.

Hypotheses: `A` is differentiable with derivative `A'`, `A'` is bounded by `1` (which the
second-order invariant supplies, via `HasParisiC2.abs_first_le_one`), and `A` has linear
growth (which gives the integrable dominating function).
-/
theorem hasDerivAt_integral_exp_mul {A A' : ℝ → ℝ} {m v : ℝ}
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ z, Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      (∫ z, m * A' (x + Real.sqrt v * z)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) x := by
  classical
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  set b : ℝ := |m| * (C + D * (|x| + 1)) with hbdef
  set a : ℝ := |m| * (D * |Real.sqrt v|) with hadef
  -- the parametrised integrand and its derivative
  set F : ℝ → ℝ → ℝ := fun t z => Real.exp (m * A (t + Real.sqrt v * z)) with hFdef
  set F' : ℝ → ℝ → ℝ := fun t z =>
    m * A' (t + Real.sqrt v * z) * Real.exp (m * A (t + Real.sqrt v * z)) with hF'def
  -- the shift `z ↦ t + √v z`; note this is *not* `measurable_const_add`, which would be
  -- `fun x => t + x` without the scaling
  have hshift_meas : ∀ t : ℝ, Measurable (fun z : ℝ => t + Real.sqrt v * z) :=
    fun t => (measurable_id.const_mul (Real.sqrt v)).const_add t
  have hAshift : ∀ t : ℝ, Measurable (fun z : ℝ => A (t + Real.sqrt v * z)) :=
    fun t => hmeas.comp (hshift_meas t)
  have hA'shift : ∀ t : ℝ, Measurable (fun z : ℝ => A' (t + Real.sqrt v * z)) :=
    fun t => hmeas'.comp (hshift_meas t)
  have hFmeas : ∀ t : ℝ, Measurable (F t) := fun t =>
    (Real.continuous_exp.measurable).comp ((hAshift t).const_mul m)
  have hF'meas : ∀ t : ℝ, Measurable (F' t) := fun t =>
    ((hA'shift t).const_mul m).mul
      ((Real.continuous_exp.measurable).comp ((hAshift t).const_mul m))
  -- the dominating function
  set bound : ℝ → ℝ := fun z => |m| * (Real.exp b * Real.exp (a * |z|)) with hbounddef
  have hbound_int : Integrable bound (gaussianReal 0 1) :=
    ((integrable_exp_abs_mul_stdGaussian a).const_mul _).const_mul _
  have hdom : ∀ᵐ z ∂(gaussianReal 0 1), ∀ t ∈ Metric.ball x 1, ‖F' t z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall (fun z t ht => ?_)
    have ht' : |t - x| ≤ 1 := by
      have := Metric.mem_ball.mp ht
      rw [Real.dist_eq] at this
      linarith
    have hexp : Real.exp (m * A (t + Real.sqrt v * z)) ≤ Real.exp b * Real.exp (a * |z|) := by
      rw [hbdef, hadef]
      exact exp_mul_shift_ball_le hD hb m x v ht' z
    rw [Real.norm_eq_abs, hF'def]
    have habs : |m * A' (t + Real.sqrt v * z) * Real.exp (m * A (t + Real.sqrt v * z))|
        = |m| * |A' (t + Real.sqrt v * z)| * Real.exp (m * A (t + Real.sqrt v * z)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    rw [habs, hbounddef]
    have h1 : |A' (t + Real.sqrt v * z)| ≤ 1 := hA'bd _
    have h2 : (0 : ℝ) ≤ |m| := abs_nonneg m
    have hep : (0 : ℝ) < Real.exp (m * A (t + Real.sqrt v * z)) := Real.exp_pos _
    calc |m| * |A' (t + Real.sqrt v * z)| * Real.exp (m * A (t + Real.sqrt v * z))
        ≤ |m| * 1 * Real.exp (m * A (t + Real.sqrt v * z)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hep.le
      _ = |m| * Real.exp (m * A (t + Real.sqrt v * z)) := by ring
      _ ≤ |m| * (Real.exp b * Real.exp (a * |z|)) := mul_le_mul_of_nonneg_left hexp h2
  have hdiff : ∀ᵐ z ∂(gaussianReal 0 1), ∀ t ∈ Metric.ball x 1,
      HasDerivAt (fun t : ℝ => F t z) (F' t z) t := by
    refine Filter.Eventually.of_forall (fun z t _ => ?_)
    have hshift : HasDerivAt (fun s : ℝ => s + Real.sqrt v * z) 1 t := by
      simpa using (hasDerivAt_id t).add_const (Real.sqrt v * z)
    -- ascribe the type so elaboration resolves `A ∘ (· + √v z)` against
    -- `fun s => A (s + √v z)` by defeq; `simpa` instead rewrites the `Module`
    -- instances into a different but equal form and then fails to match
    have hcomp0 : HasDerivAt (fun s : ℝ => A (s + Real.sqrt v * z))
        (A' (t + Real.sqrt v * z) * 1) t := (hderiv (t + Real.sqrt v * z)).comp t hshift
    have hcomp : HasDerivAt (fun s : ℝ => A (s + Real.sqrt v * z))
        (A' (t + Real.sqrt v * z)) t := by
      rw [mul_one] at hcomp0
      exact hcomp0
    have hmul : HasDerivAt (fun s : ℝ => m * A (s + Real.sqrt v * z))
        (m * A' (t + Real.sqrt v * z)) t := hcomp.const_mul m
    have hres := hmul.exp
    have heq : Real.exp (m * A (t + Real.sqrt v * z)) * (m * A' (t + Real.sqrt v * z))
        = m * A' (t + Real.sqrt v * z) * Real.exp (m * A (t + Real.sqrt v * z)) := by ring
    rw [heq] at hres
    exact hres
  have hFint : Integrable (F x) (gaussianReal 0 1) :=
    integrable_exp_mul_of_hasLinearGrowth ⟨C, D, hC, hD, hb⟩ hmeas m x v
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x) (bound := bound)
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall (fun t => (hFmeas t).aestronglyMeasurable))
    hFint (hF'meas x).aestronglyMeasurable hdom hbound_int hdiff
  exact hmain.2


/--
**Second derivative of the smoothing integral.**

`d/dx ∫ m A' (x+√v z) exp (m A (x+√v z)) dγ`
  `= ∫ (m A''(x+√v z) + m² A'(x+√v z)²) exp (m A (x+√v z)) dγ`.

Same technique as `hasDerivAt_integral_exp_mul`; the integrand is now a product, so its
derivative picks up the extra `m² (A')²` term.  Domination again uses the linear growth of
`A` together with `|A'| ≤ 1` and `|A''| ≤ 1`, both supplied by the second-order invariant
`HasParisiC2`.
-/
theorem hasDerivAt_integral_exp_mul_deriv {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hderiv' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => ∫ z, m * A' (t + Real.sqrt v * z)
        * Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      (∫ z, (m * A'' (x + Real.sqrt v * z)
          + m ^ 2 * A' (x + Real.sqrt v * z) ^ 2)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) x := by
  classical
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  set b : ℝ := |m| * (C + D * (|x| + 1)) with hbdef
  set a : ℝ := |m| * (D * |Real.sqrt v|) with hadef
  set F : ℝ → ℝ → ℝ := fun t z =>
    m * A' (t + Real.sqrt v * z) * Real.exp (m * A (t + Real.sqrt v * z)) with hFdef
  set F' : ℝ → ℝ → ℝ := fun t z =>
    (m * A'' (t + Real.sqrt v * z) + m ^ 2 * A' (t + Real.sqrt v * z) ^ 2)
      * Real.exp (m * A (t + Real.sqrt v * z)) with hF'def
  have hshift_meas : ∀ t : ℝ, Measurable (fun z : ℝ => t + Real.sqrt v * z) :=
    fun t => (measurable_id.const_mul (Real.sqrt v)).const_add t
  have hAshift : ∀ t : ℝ, Measurable (fun z : ℝ => A (t + Real.sqrt v * z)) :=
    fun t => hmeas.comp (hshift_meas t)
  have hA'shift : ∀ t : ℝ, Measurable (fun z : ℝ => A' (t + Real.sqrt v * z)) :=
    fun t => hmeas'.comp (hshift_meas t)
  have hA''shift : ∀ t : ℝ, Measurable (fun z : ℝ => A'' (t + Real.sqrt v * z)) :=
    fun t => hmeas''.comp (hshift_meas t)
  have hexpmeas : ∀ t : ℝ,
      Measurable (fun z : ℝ => Real.exp (m * A (t + Real.sqrt v * z))) := fun t =>
    (Real.continuous_exp.measurable).comp ((hAshift t).const_mul m)
  have hFmeas : ∀ t : ℝ, Measurable (F t) := fun t =>
    ((hA'shift t).const_mul m).mul (hexpmeas t)
  have hF'meas : ∀ t : ℝ, Measurable (F' t) := fun t =>
    (((hA''shift t).const_mul m).add
      (((hA'shift t).pow_const 2).const_mul (m ^ 2))).mul (hexpmeas t)
  set bound : ℝ → ℝ := fun z =>
    (|m| + m ^ 2) * (Real.exp b * Real.exp (a * |z|)) with hbounddef
  have hbound_int : Integrable bound (gaussianReal 0 1) :=
    ((integrable_exp_abs_mul_stdGaussian a).const_mul _).const_mul _
  have hdom : ∀ᵐ z ∂(gaussianReal 0 1), ∀ t ∈ Metric.ball x 1, ‖F' t z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall (fun z t ht => ?_)
    have ht' : |t - x| ≤ 1 := by
      have h := Metric.mem_ball.mp ht
      rw [Real.dist_eq] at h
      linarith
    have hexp : Real.exp (m * A (t + Real.sqrt v * z)) ≤ Real.exp b * Real.exp (a * |z|) := by
      rw [hbdef, hadef]
      exact exp_mul_shift_ball_le hD hb m x v ht' z
    have hep : (0 : ℝ) < Real.exp (m * A (t + Real.sqrt v * z)) := Real.exp_pos _
    have hcoef : |m * A'' (t + Real.sqrt v * z)
        + m ^ 2 * A' (t + Real.sqrt v * z) ^ 2| ≤ |m| + m ^ 2 := by
      have h1 : |m * A'' (t + Real.sqrt v * z)| ≤ |m| := by
        rw [abs_mul]
        have := hA''bd (t + Real.sqrt v * z)
        nlinarith [abs_nonneg m, abs_nonneg (A'' (t + Real.sqrt v * z))]
      have h2 : |m ^ 2 * A' (t + Real.sqrt v * z) ^ 2| ≤ m ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg m), abs_of_nonneg (sq_nonneg _)]
        have hb1 : A' (t + Real.sqrt v * z) ^ 2 ≤ 1 := by
          nlinarith [hA'bd (t + Real.sqrt v * z), abs_nonneg (A' (t + Real.sqrt v * z)),
            sq_abs (A' (t + Real.sqrt v * z))]
        nlinarith [sq_nonneg m]
      calc |m * A'' (t + Real.sqrt v * z) + m ^ 2 * A' (t + Real.sqrt v * z) ^ 2|
          ≤ |m * A'' (t + Real.sqrt v * z)| + |m ^ 2 * A' (t + Real.sqrt v * z) ^ 2| :=
            abs_add_le _ _
        _ ≤ |m| + m ^ 2 := by linarith
    rw [Real.norm_eq_abs, hF'def, hbounddef, abs_mul,
      abs_of_nonneg (Real.exp_pos _).le]
    calc |m * A'' (t + Real.sqrt v * z) + m ^ 2 * A' (t + Real.sqrt v * z) ^ 2|
          * Real.exp (m * A (t + Real.sqrt v * z))
        ≤ (|m| + m ^ 2) * Real.exp (m * A (t + Real.sqrt v * z)) :=
          mul_le_mul_of_nonneg_right hcoef hep.le
      _ ≤ (|m| + m ^ 2) * (Real.exp b * Real.exp (a * |z|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hdiff : ∀ᵐ z ∂(gaussianReal 0 1), ∀ t ∈ Metric.ball x 1,
      HasDerivAt (fun t : ℝ => F t z) (F' t z) t := by
    refine Filter.Eventually.of_forall (fun z t _ => ?_)
    have hshift : HasDerivAt (fun s : ℝ => s + Real.sqrt v * z) 1 t := by
      simpa using (hasDerivAt_id t).add_const (Real.sqrt v * z)
    have hA0 : HasDerivAt (fun s : ℝ => A (s + Real.sqrt v * z))
        (A' (t + Real.sqrt v * z) * 1) t := (hderiv (t + Real.sqrt v * z)).comp t hshift
    have hAd : HasDerivAt (fun s : ℝ => A (s + Real.sqrt v * z))
        (A' (t + Real.sqrt v * z)) t := by rw [mul_one] at hA0; exact hA0
    have hA'0 : HasDerivAt (fun s : ℝ => A' (s + Real.sqrt v * z))
        (A'' (t + Real.sqrt v * z) * 1) t := (hderiv' (t + Real.sqrt v * z)).comp t hshift
    have hA'd : HasDerivAt (fun s : ℝ => A' (s + Real.sqrt v * z))
        (A'' (t + Real.sqrt v * z)) t := by rw [mul_one] at hA'0; exact hA'0
    have hleft : HasDerivAt (fun s : ℝ => m * A' (s + Real.sqrt v * z))
        (m * A'' (t + Real.sqrt v * z)) t := hA'd.const_mul m
    have hexpd : HasDerivAt (fun s : ℝ => Real.exp (m * A (s + Real.sqrt v * z)))
        (Real.exp (m * A (t + Real.sqrt v * z)) * (m * A' (t + Real.sqrt v * z))) t :=
      (hAd.const_mul m).exp
    have hprod := hleft.mul hexpd
    have heq :
        m * A'' (t + Real.sqrt v * z) * Real.exp (m * A (t + Real.sqrt v * z))
          + m * A' (t + Real.sqrt v * z)
            * (Real.exp (m * A (t + Real.sqrt v * z)) * (m * A' (t + Real.sqrt v * z)))
        = (m * A'' (t + Real.sqrt v * z)
            + m ^ 2 * A' (t + Real.sqrt v * z) ^ 2)
          * Real.exp (m * A (t + Real.sqrt v * z)) := by ring
    rw [heq] at hprod
    exact hprod
  have hFint : Integrable (F x) (gaussianReal 0 1) := by
    have hdomx : Integrable (fun z : ℝ => |m| * (Real.exp b * Real.exp (a * |z|)))
        (gaussianReal 0 1) :=
      ((integrable_exp_abs_mul_stdGaussian a).const_mul _).const_mul _
    refine hdomx.mono' (hFmeas x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    have hexp : Real.exp (m * A (x + Real.sqrt v * z)) ≤ Real.exp b * Real.exp (a * |z|) := by
      rw [hbdef, hadef]
      exact exp_mul_shift_ball_le hD hb m x v (by simp) z
    have hep : (0 : ℝ) < Real.exp (m * A (x + Real.sqrt v * z)) := Real.exp_pos _
    rw [Real.norm_eq_abs, hFdef, abs_mul, abs_mul,
      abs_of_nonneg (Real.exp_pos _).le]
    calc |m| * |A' (x + Real.sqrt v * z)| * Real.exp (m * A (x + Real.sqrt v * z))
        ≤ |m| * 1 * Real.exp (m * A (x + Real.sqrt v * z)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hA'bd _) (abs_nonneg m)) hep.le
      _ = |m| * Real.exp (m * A (x + Real.sqrt v * z)) := by ring
      _ ≤ |m| * (Real.exp b * Real.exp (a * |z|)) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg m)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x) (bound := bound)
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall (fun t => (hFmeas t).aestronglyMeasurable))
    hFint (hF'meas x).aestronglyMeasurable hdom hbound_int hdiff
  exact hmain.2


/-! ## 11. Derivatives of the smoothing step itself

Composing the two differentiations of §10 with `T = (1/m) log G` gives `T'` and `T''`.
Writing `⟨f⟩ = ∫ f e^{mA} / ∫ e^{mA}` for the tilted average, these are

  `T' = ⟨A'⟩`,   `T'' = ⟨A''⟩ + m (⟨(A')²⟩ - ⟨A'⟩²) = ⟨A''⟩ + m Var_tilt(A')`,

and the second is the identity that propagates `0 ≤ A'' ≤ 1 - (A')²`.
-/

/-- The exponential integral `G` is strictly positive. -/
theorem smoothing_integral_pos {A : ℝ → ℝ} {m v : ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
  integral_exp_pos (integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v)

/--
**First derivative of the smoothing step.**  `T' = G'/(mG)`, which is the tilted average
`⟨A'⟩` once the factor `m` is cancelled.
-/
theorem hasDerivAt_smoothing_step {A A' : ℝ → ℝ} {m v : ℝ}
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (1 / m)
        * Real.log (∫ z, Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1)))
      ((1 / m)
        * ((∫ z, m * A' (x + Real.sqrt v * z)
              * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
            / ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))) x := by
  have hGpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
    smoothing_integral_pos hA hmeas x
  have hG := hasDerivAt_integral_exp_mul hderiv hA'bd hA hmeas hmeas' (m := m) (v := v) x
  exact (hG.log (ne_of_gt hGpos)).const_mul (1 / m)

/--
**Second derivative of the smoothing step**, in the raw quotient form
`T'' = (1/m) (G'' G - (G')²)/G²`.

The rearrangement into `⟨A''⟩ + m Var_tilt(A')` is `smoothing_step_second_deriv_eq` below.
-/
theorem hasDerivAt_smoothing_step_deriv {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hderiv' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (1 / m)
        * ((∫ z, m * A' (t + Real.sqrt v * z)
              * Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1))
            / ∫ z, Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1)))
      ((1 / m)
        * (((∫ z, (m * A'' (x + Real.sqrt v * z)
                + m ^ 2 * A' (x + Real.sqrt v * z) ^ 2)
              * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
              * (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
            - (∫ z, m * A' (x + Real.sqrt v * z)
                * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
              * ∫ z, m * A' (x + Real.sqrt v * z)
                * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          / (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) ^ 2)) x := by
  have hGpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
    smoothing_integral_pos hA hmeas x
  have hG := hasDerivAt_integral_exp_mul hderiv hA'bd hA hmeas hmeas' (m := m) (v := v) x
  have hG1 := hasDerivAt_integral_exp_mul_deriv hderiv hderiv' hA'bd hA''bd hA
    hmeas hmeas' hmeas'' (m := m) (v := v) x
  exact ((hG1.div hG (ne_of_gt hGpos))).const_mul (1 / m)

/--
**Cauchy–Schwarz for the tilted average**: `(∫ A' e)² ≤ (∫ (A')² e) (∫ e)`, i.e. the tilted
variance of `A'` is non-negative.  This is the `Var ≥ 0` used in the propagation.
-/
theorem sq_integral_mul_le {A A' : ℝ → ℝ} {m v : ℝ}
    (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    (∫ z, A' (x + Real.sqrt v * z)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) ^ 2
      ≤ (∫ z, A' (x + Real.sqrt v * z) ^ 2
            * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
        * ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) := by
  classical
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  set e : ℝ → ℝ := fun z => Real.exp (m * A (x + Real.sqrt v * z)) with hedef
  set g : ℝ → ℝ := fun z => A' (x + Real.sqrt v * z) with hgdef
  have hepos : ∀ z, 0 < e z := fun z => Real.exp_pos _
  have heint : Integrable e μ := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hshift_meas : Measurable (fun z : ℝ => x + Real.sqrt v * z) :=
    (measurable_id.const_mul (Real.sqrt v)).const_add x
  have hgmeas : Measurable g := hmeas'.comp hshift_meas
  -- `|g| ≤ 1`, so `g² e ≤ e` and `|g e| ≤ e`; all three integrals exist
  have hg2e_int : Integrable (fun z => g z ^ 2 * e z) μ := by
    refine heint.mono' ((hgmeas.pow_const 2).mul
      ((Real.continuous_exp.measurable).comp
        ((hmeas.comp hshift_meas).const_mul m))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hepos z).le]
    have h1 : g z ^ 2 ≤ 1 := by
      have := hA'bd (x + Real.sqrt v * z)
      nlinarith [abs_nonneg (g z), sq_abs (g z)]
    nlinarith [(hepos z).le]
  have hge_int : Integrable (fun z => g z * e z) μ := by
    refine heint.mono' (hgmeas.mul
      ((Real.continuous_exp.measurable).comp
        ((hmeas.comp hshift_meas).const_mul m))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hepos z).le]
    have h1 : |g z| ≤ 1 := hA'bd (x + Real.sqrt v * z)
    nlinarith [(hepos z).le, abs_nonneg (g z)]
  -- Elementary route rather than an L² Cauchy-Schwarz lemma: expand
  -- `∫ (g z - c)² e z ≥ 0` and optimise over the constant `c`.
  have hnonneg : ∀ c : ℝ, 0 ≤ ∫ z, (g z - c) ^ 2 * e z ∂μ := by
    intro c
    refine integral_nonneg (fun z => ?_)
    exact mul_nonneg (sq_nonneg _) (hepos z).le
  have hexpand : ∀ c : ℝ,
      (∫ z, (g z - c) ^ 2 * e z ∂μ)
        = (∫ z, g z ^ 2 * e z ∂μ) - 2 * c * (∫ z, g z * e z ∂μ)
          + c ^ 2 * ∫ z, e z ∂μ := by
    intro c
    have hpt : ∀ z, (g z - c) ^ 2 * e z
        = g z ^ 2 * e z - 2 * c * (g z * e z) + c ^ 2 * e z := by
      intro z; ring
    -- ascribe the integrability facts as explicit lambdas: otherwise `.sub` yields a
    -- `Pi.sub` term and `integral_add`'s pattern does not match the pointwise goal
    have hcm : Integrable (fun z => 2 * c * (g z * e z)) μ := hge_int.const_mul (2 * c)
    have h1 : Integrable (fun z => g z ^ 2 * e z - 2 * c * (g z * e z)) μ :=
      hg2e_int.sub hcm
    have h2 : Integrable (fun z => c ^ 2 * e z) μ := heint.const_mul (c ^ 2)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add h1 h2, integral_sub hg2e_int hcm,
      integral_const_mul, integral_const_mul]
  have hEpos : 0 < ∫ z, e z ∂μ := integral_exp_pos heint
  set S : ℝ := ∫ z, g z ^ 2 * e z ∂μ with hS
  set P : ℝ := ∫ z, g z * e z ∂μ with hP
  set E : ℝ := ∫ z, e z ∂μ with hE
  have hquad : ∀ c : ℝ, 0 ≤ S - 2 * c * P + c ^ 2 * E := by
    intro c
    have := hnonneg c
    rwa [hexpand c] at this
  have hkey := hquad (P / E)
  have hEne : E ≠ 0 := ne_of_gt hEpos
  have hrw : S - 2 * (P / E) * P + (P / E) ^ 2 * E = S - P ^ 2 / E := by
    field_simp
    ring
  rw [hrw] at hkey
  have : P ^ 2 / E ≤ S := by linarith
  calc P ^ 2 = (P ^ 2 / E) * E := by field_simp
    _ ≤ S * E := mul_le_mul_of_nonneg_right this hEpos.le


/-! ## 12. Propagating the second-order invariant

With `Q = ∫ A'' e`, `R = ∫ (A')² e`, `P = ∫ A' e`, `E = ∫ e` (`e = exp (m A(x+√v ·))`), the
second derivative of the smoothing step is

  `T'' = Q/E + m (R/E - (P/E)²)`,   `T' = P/E`.

The invariant `A'' ≤ 1 - (A')²` gives `Q ≤ E - R`; the tilted variance is non-negative,
`P² ≤ R E` (`sq_integral_mul_le`); and `m ≤ 1`.  Those three facts give `T'' ≤ 1 - (T')²`.
-/

/--
The algebraic heart of the propagation, with no measure theory in it.

`Q ≤ E - R` is the invariant, `P² ≤ R E` is `Var ≥ 0`, and `m ≤ 1` is
`RSBScheme.m_le_one`.  Dropping any one of the three breaks the conclusion — in particular
`m ≤ 1` is exactly what makes the `(1-m)·Var` term have the right sign.
-/
theorem tilted_bound_algebra {Q R P E m : ℝ} (hE : 0 < E)
    (hQ : Q ≤ E - R) (hCS : P ^ 2 ≤ R * E) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    Q / E + m * (R / E - (P / E) ^ 2) ≤ 1 - (P / E) ^ 2 := by
  have hr : (P / E) ^ 2 ≤ R / E := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hE]
    nlinarith [hCS, hE.le]
  have hQE : Q / E ≤ 1 - R / E := by
    rw [div_le_iff₀ hE]
    have hrw : (1 - R / E) * E = E - R := by field_simp
    rw [hrw]
    exact hQ
  have hkey : 0 ≤ (R / E - (P / E) ^ 2) * (1 - m) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hQE, hkey]

/--
`∫ A'' e ≤ ∫ e - ∫ (A')² e`, i.e. `Q ≤ E - R`: the pointwise invariant `A'' ≤ 1 - (A')²`
integrated against the tilting weight.
-/
theorem integral_second_le {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hinv : ∀ y, A'' y ≤ 1 - A' y ^ 2)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    (∫ z, A'' (x + Real.sqrt v * z)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      ≤ (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
        - ∫ z, A' (x + Real.sqrt v * z) ^ 2
            * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) := by
  classical
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  set e : ℝ → ℝ := fun z => Real.exp (m * A (x + Real.sqrt v * z)) with hedef
  have hepos : ∀ z, 0 < e z := fun z => Real.exp_pos _
  have heint : Integrable e μ := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hshift_meas : Measurable (fun z : ℝ => x + Real.sqrt v * z) :=
    (measurable_id.const_mul (Real.sqrt v)).const_add x
  have hemeas : Measurable e :=
    (Real.continuous_exp.measurable).comp ((hmeas.comp hshift_meas).const_mul m)
  have hg'meas : Measurable (fun z : ℝ => A' (x + Real.sqrt v * z)) :=
    hmeas'.comp hshift_meas
  have hg''meas : Measurable (fun z : ℝ => A'' (x + Real.sqrt v * z)) :=
    hmeas''.comp hshift_meas
  -- the two integrals exist, both dominated by `e`
  have hRint : Integrable (fun z => A' (x + Real.sqrt v * z) ^ 2 * e z) μ := by
    refine heint.mono' ((hg'meas.pow_const 2).mul hemeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hepos z).le]
    have h1 : A' (x + Real.sqrt v * z) ^ 2 ≤ 1 := by
      have := hA'bd (x + Real.sqrt v * z)
      nlinarith [abs_nonneg (A' (x + Real.sqrt v * z)),
        sq_abs (A' (x + Real.sqrt v * z))]
    nlinarith [(hepos z).le]
  have hQint : Integrable (fun z => A'' (x + Real.sqrt v * z) * e z) μ := by
    refine heint.mono' (hg''meas.mul hemeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hepos z).le]
    have h1 : |A'' (x + Real.sqrt v * z)| ≤ 1 := hA''bd _
    nlinarith [(hepos z).le, abs_nonneg (A'' (x + Real.sqrt v * z))]
  -- pointwise `A'' e ≤ e - (A')² e`
  have hpt : ∀ z, A'' (x + Real.sqrt v * z) * e z
      ≤ e z - A' (x + Real.sqrt v * z) ^ 2 * e z := by
    intro z
    have h := hinv (x + Real.sqrt v * z)
    nlinarith [(hepos z).le]
  have hsub : Integrable (fun z => e z - A' (x + Real.sqrt v * z) ^ 2 * e z) μ :=
    heint.sub hRint
  have hmono := integral_mono hQint hsub hpt
  rwa [integral_sub heint hRint] at hmono


/-! ## 13. The tilted integrals, and `T'' ≤ 1 - (T')²`

The derivative formulas of §11 are stated in terms of four integrals against the tilting
weight `e = exp (m A(x + √v ·))`.  Naming them makes the algebra legible:

  `E = ∫ e`,  `P = ∫ A' e`,  `R = ∫ (A')² e`,  `Q = ∫ A'' e`.

Then `T' = P/E` and `T'' = Q/E + m (R/E - (P/E)²)`, and the invariant is preserved.
-/

/-- `E = ∫ e`, the normalising constant of the tilted measure. -/
noncomputable def tiltE (A : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)

/-- `P = ∫ A' e`. -/
noncomputable def tiltP (A A' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  ∫ z, A' (x + Real.sqrt v * z)
    * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)

/-- `R = ∫ (A')² e`. -/
noncomputable def tiltR (A A' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  ∫ z, A' (x + Real.sqrt v * z) ^ 2
    * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)

/-- `Q = ∫ A'' e`. -/
noncomputable def tiltQ (A A'' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  ∫ z, A'' (x + Real.sqrt v * z)
    * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)

theorem tiltE_pos {A : ℝ → ℝ} {m v : ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    0 < tiltE A m v x :=
  smoothing_integral_pos hA hmeas x

section TiltIntegrability

variable {A A' A'' : ℝ → ℝ} {m v : ℝ}

/-- Measurability of the shift, reused throughout. -/
theorem measurable_tilt_shift (v x : ℝ) :
    Measurable (fun z : ℝ => x + Real.sqrt v * z) :=
  (measurable_id.const_mul (Real.sqrt v)).const_add x

/-- `A' e` is integrable when `|A'| ≤ 1`. -/
theorem integrable_tiltP (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    Integrable (fun z => A' (x + Real.sqrt v * z)
      * Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) := by
  have heint : Integrable (fun z => Real.exp (m * A (x + Real.sqrt v * z)))
      (gaussianReal 0 1) := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hemeas : Measurable (fun z => Real.exp (m * A (x + Real.sqrt v * z))) :=
    (Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_tilt_shift v x)).const_mul m)
  refine heint.mono' ((hmeas'.comp (measurable_tilt_shift v x)).mul
    hemeas).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have h1 : |A' (x + Real.sqrt v * z)| ≤ 1 := hA'bd _
  nlinarith [(Real.exp_pos (m * A (x + Real.sqrt v * z))).le,
    abs_nonneg (A' (x + Real.sqrt v * z))]

/-- `(A')² e` is integrable when `|A'| ≤ 1`. -/
theorem integrable_tiltR (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    Integrable (fun z => A' (x + Real.sqrt v * z) ^ 2
      * Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) := by
  have heint : Integrable (fun z => Real.exp (m * A (x + Real.sqrt v * z)))
      (gaussianReal 0 1) := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hemeas : Measurable (fun z => Real.exp (m * A (x + Real.sqrt v * z))) :=
    (Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_tilt_shift v x)).const_mul m)
  refine heint.mono' (((hmeas'.comp (measurable_tilt_shift v x)).pow_const 2).mul
    hemeas).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.exp_pos _).le]
  have h1 : A' (x + Real.sqrt v * z) ^ 2 ≤ 1 := by
    have := hA'bd (x + Real.sqrt v * z)
    nlinarith [abs_nonneg (A' (x + Real.sqrt v * z)),
      sq_abs (A' (x + Real.sqrt v * z))]
  nlinarith [(Real.exp_pos (m * A (x + Real.sqrt v * z))).le]

/-- `A'' e` is integrable when `|A''| ≤ 1`. -/
theorem integrable_tiltQ (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas'' : Measurable A'') (x : ℝ) :
    Integrable (fun z => A'' (x + Real.sqrt v * z)
      * Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) := by
  have heint : Integrable (fun z => Real.exp (m * A (x + Real.sqrt v * z)))
      (gaussianReal 0 1) := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hemeas : Measurable (fun z => Real.exp (m * A (x + Real.sqrt v * z))) :=
    (Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_tilt_shift v x)).const_mul m)
  refine heint.mono' ((hmeas''.comp (measurable_tilt_shift v x)).mul
    hemeas).aestronglyMeasurable (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have h1 : |A'' (x + Real.sqrt v * z)| ≤ 1 := hA''bd _
  nlinarith [(Real.exp_pos (m * A (x + Real.sqrt v * z))).le,
    abs_nonneg (A'' (x + Real.sqrt v * z))]

end TiltIntegrability

/-- `∫ m A' e = m P`. -/
theorem integral_mul_deriv_eq {A A' : ℝ → ℝ} {m v : ℝ} (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    (∫ z, m * A' (x + Real.sqrt v * z)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      = m * tiltP A A' m v x := by
  rw [tiltP, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show m * A' (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z))
    = m * (A' (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)))
  ring

/-- `∫ (m A'' + m² (A')²) e = m Q + m² R`. -/
theorem integral_second_expand {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    (∫ z, (m * A'' (x + Real.sqrt v * z)
          + m ^ 2 * A' (x + Real.sqrt v * z) ^ 2)
        * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      = m * tiltQ A A'' m v x + m ^ 2 * tiltR A A' m v x := by
  have hQ : Integrable (fun z => m * (A'' (x + Real.sqrt v * z)
      * Real.exp (m * A (x + Real.sqrt v * z)))) (gaussianReal 0 1) :=
    (integrable_tiltQ hA''bd hA hmeas hmeas'' x).const_mul m
  have hR : Integrable (fun z => m ^ 2 * (A' (x + Real.sqrt v * z) ^ 2
      * Real.exp (m * A (x + Real.sqrt v * z)))) (gaussianReal 0 1) :=
    (integrable_tiltR hA'bd hA hmeas hmeas' x).const_mul (m ^ 2)
  have hpt : ∀ z, (m * A'' (x + Real.sqrt v * z)
        + m ^ 2 * A' (x + Real.sqrt v * z) ^ 2)
      * Real.exp (m * A (x + Real.sqrt v * z))
      = m * (A'' (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)))
        + m ^ 2 * (A' (x + Real.sqrt v * z) ^ 2
          * Real.exp (m * A (x + Real.sqrt v * z))) := by
    intro z; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hQ hR,
    integral_const_mul, integral_const_mul, tiltQ, tiltR]

/-- `T' = P/E`. -/
theorem smoothing_first_deriv_eq {A A' : ℝ → ℝ} {m v : ℝ} (hm : m ≠ 0)
    (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    (1 / m) * ((∫ z, m * A' (x + Real.sqrt v * z)
          * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
        / ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      = tiltP A A' m v x / tiltE A m v x := by
  rw [integral_mul_deriv_eq hA'bd hA hmeas hmeas' x]
  show (1 / m) * ((m * tiltP A A' m v x) / tiltE A m v x)
    = tiltP A A' m v x / tiltE A m v x
  field_simp

/-- `T'' = Q/E + m (R/E - (P/E)²)`. -/
theorem smoothing_second_deriv_eq {A A' A'' : ℝ → ℝ} {m v : ℝ} (hm : m ≠ 0)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    (1 / m)
      * (((∫ z, (m * A'' (x + Real.sqrt v * z)
              + m ^ 2 * A' (x + Real.sqrt v * z) ^ 2)
            * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
            * (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - (∫ z, m * A' (x + Real.sqrt v * z)
              * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
            * ∫ z, m * A' (x + Real.sqrt v * z)
              * Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
        / (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) ^ 2)
      = tiltQ A A'' m v x / tiltE A m v x
        + m * (tiltR A A' m v x / tiltE A m v x
          - (tiltP A A' m v x / tiltE A m v x) ^ 2) := by
  have hE : tiltE A m v x ≠ 0 := ne_of_gt (tiltE_pos hA hmeas x)
  rw [integral_second_expand hA'bd hA''bd hA hmeas hmeas' hmeas'' x,
    integral_mul_deriv_eq hA'bd hA hmeas hmeas' x]
  show (1 / m)
      * (((m * tiltQ A A'' m v x + m ^ 2 * tiltR A A' m v x) * tiltE A m v x
          - (m * tiltP A A' m v x) * (m * tiltP A A' m v x))
        / (tiltE A m v x) ^ 2)
    = tiltQ A A'' m v x / tiltE A m v x
      + m * (tiltR A A' m v x / tiltE A m v x
        - (tiltP A A' m v x / tiltE A m v x) ^ 2)
  field_simp
  ring

/--
**The smoothing step preserves the second-order invariant**: `T'' ≤ 1 - (T')²`.

This is the goal of §§10–13.  It combines
`integral_second_le` (`Q ≤ E - R`, the invariant integrated against the tilt),
`sq_integral_mul_le` (`P² ≤ R E`, i.e. `Var ≥ 0`), and `m ≤ 1`, through the pure algebra of
`tilted_bound_algebra`.
-/
theorem smoothing_second_deriv_le {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hinv : ∀ y, A'' y ≤ 1 - A' y ^ 2)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    tiltQ A A'' m v x / tiltE A m v x
        + m * (tiltR A A' m v x / tiltE A m v x
          - (tiltP A A' m v x / tiltE A m v x) ^ 2)
      ≤ 1 - (tiltP A A' m v x / tiltE A m v x) ^ 2 := by
  refine tilted_bound_algebra (tiltE_pos hA hmeas x) ?_ ?_ hm0 hm1
  · exact integral_second_le hA'bd hA''bd hinv hA hmeas hmeas' hmeas'' x
  · exact sq_integral_mul_le hA'bd hA hmeas hmeas' x

/-- The smoothing step's second derivative is also non-negative, the other half of the
invariant: `T'' ≥ 0` follows from `A'' ≥ 0` and `Var ≥ 0`. -/
theorem smoothing_second_deriv_nonneg {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm0 : 0 ≤ m)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA''nn : ∀ y, 0 ≤ A'' y)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    0 ≤ tiltQ A A'' m v x / tiltE A m v x
        + m * (tiltR A A' m v x / tiltE A m v x
          - (tiltP A A' m v x / tiltE A m v x) ^ 2) := by
  have hEpos : 0 < tiltE A m v x := tiltE_pos hA hmeas x
  have hQnn : 0 ≤ tiltQ A A'' m v x := by
    refine integral_nonneg (fun z => ?_)
    exact mul_nonneg (hA''nn _) (Real.exp_pos _).le
  have hCS : tiltP A A' m v x ^ 2 ≤ tiltR A A' m v x * tiltE A m v x :=
    sq_integral_mul_le hA'bd hA hmeas hmeas' x
  have hvar : 0 ≤ tiltR A A' m v x / tiltE A m v x
      - (tiltP A A' m v x / tiltE A m v x) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) hEpos]
    nlinarith [hCS, hEpos.le]
  have h1 : 0 ≤ tiltQ A A'' m v x / tiltE A m v x := div_nonneg hQnn hEpos.le
  nlinarith [mul_nonneg hm0 hvar]

/-- The first derivative of the smoothing step, as a function: `T' = P/E`. -/
noncomputable def stepD1 (A A' : ℝ → ℝ) (m v : ℝ) : ℝ → ℝ := fun x =>
  tiltP A A' m v x / tiltE A m v x

/-- The second derivative of the smoothing step, as a function:
`T'' = Q/E + m (R/E - (P/E)²)`. -/
noncomputable def stepD2 (A A' A'' : ℝ → ℝ) (m v : ℝ) : ℝ → ℝ := fun x =>
  tiltQ A A'' m v x / tiltE A m v x
    + m * (tiltR A A' m v x / tiltE A m v x
      - (tiltP A A' m v x / tiltE A m v x) ^ 2)

/-- `x ↦ (1/m) log (∫ exp (m A (x + √v z)))` has derivative `stepD1`. -/
theorem hasDerivAt_stepD1 {A A' : ℝ → ℝ} {m v : ℝ} (hm : m ≠ 0)
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hA'bd : ∀ y, |A' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A') (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (1 / m)
        * Real.log (∫ z, Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1)))
      (stepD1 A A' m v x) x := by
  have h := hasDerivAt_smoothing_step hderiv hA'bd hA hmeas hmeas' (m := m) (v := v) x
  rwa [smoothing_first_deriv_eq hm hA'bd hA hmeas hmeas' x] at h

/-- `stepD1` has derivative `stepD2`. -/
theorem hasDerivAt_stepD2 {A A' A'' : ℝ → ℝ} {m v : ℝ} (hm : m ≠ 0)
    (hderiv : ∀ y, HasDerivAt A (A' y) y) (hderiv' : ∀ y, HasDerivAt A' (A'' y) y)
    (hA'bd : ∀ y, |A' y| ≤ 1) (hA''bd : ∀ y, |A'' y| ≤ 1)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (x : ℝ) :
    HasDerivAt (stepD1 A A' m v) (stepD2 A A' A'' m v x) x := by
  have h := hasDerivAt_smoothing_step_deriv hderiv hderiv' hA'bd hA''bd hA
    hmeas hmeas' hmeas'' (m := m) (v := v) x
  have hfun : (fun t : ℝ => (1 / m)
      * ((∫ z, m * A' (t + Real.sqrt v * z)
            * Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          / ∫ z, Real.exp (m * A (t + Real.sqrt v * z)) ∂(gaussianReal 0 1)))
      = stepD1 A A' m v := by
    funext t
    exact smoothing_first_deriv_eq hm hA'bd hA hmeas hmeas' t
  rw [hfun, smoothing_second_deriv_eq hm hA'bd hA''bd hA hmeas hmeas' hmeas'' x] at h
  exact h

/-! ## 14. The improved `O(w)` variance estimate

With the second-order invariant in hand (`|A''| ≤ 1`), the first-order term of the variance
perturbation vanishes by symmetry of the Gaussian, upgrading the `√w` of
`abs_integral_shift_sub_le` to `w`:

  `|∫ A (x + √w z) dγ - A x| ≤ w`.

This is what makes Target 2b's **Lipschitz** statement in `q` reachable; the `√w` bound only
gives a 1/2-Hölder modulus, and that `√` is sharp for merely Lipschitz `A`.
-/

/-- If `|A''| ≤ 1` then `A'` is 1-Lipschitz. -/
theorem abs_deriv_sub_le {A' A'' : ℝ → ℝ}
    (hd2 : ∀ t, HasDerivAt A' (A'' t) t) (hA''bd : ∀ t, |A'' t| ≤ 1) (a b : ℝ) :
    |A' a - A' b| ≤ |a - b| := by
  have hg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => A' (b + s * (a - b)))
        ((a - b) * A'' (b + s * (a - b))) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have hlin : HasDerivAt (fun s : ℝ => b + s * (a - b)) (a - b) s := by
      simpa using ((hasDerivAt_id s).mul_const (a - b)).const_add b
    have hcomp : HasDerivAt (fun s : ℝ => A' (b + s * (a - b)))
        (A'' (b + s * (a - b)) * (a - b)) s := (hd2 (b + s * (a - b))).comp s hlin
    have hcomp' : HasDerivAt (fun s : ℝ => A' (b + s * (a - b)))
        ((a - b) * A'' (b + s * (a - b))) s := by
      rw [mul_comm] at hcomp
      exact hcomp
    exact hcomp'.hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖(a - b) * A'' (b + s * (a - b))‖ ≤ |a - b| := by
    intro s _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |A'' (b + s * (a - b))| ≤ 1 := hA''bd _
    nlinarith [abs_nonneg (a - b), abs_nonneg (A'' (b + s * (a - b)))]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hg hbound
  have hone : b + (1 : ℝ) * (a - b) = a := by ring
  have hzero : b + (0 : ℝ) * (a - b) = b := by ring
  rw [Real.norm_eq_abs, hone, hzero] at h
  exact h

/--
**Second-order Taylor bound** (with the crude constant `1` rather than `1/2`, which is all we
need): if `|A''| ≤ 1` then `|A y - A x - A' x (y - x)| ≤ (y - x)²`.
-/
theorem abs_taylor_second_le {A A' A'' : ℝ → ℝ}
    (hd1 : ∀ t, HasDerivAt A (A' t) t) (hd2 : ∀ t, HasDerivAt A' (A'' t) t)
    (hA''bd : ∀ t, |A'' t| ≤ 1) (x y : ℝ) :
    |A y - A x - A' x * (y - x)| ≤ (y - x) ^ 2 := by
  have hLip := abs_deriv_sub_le hd2 hA''bd
  have hh : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt
        (fun s : ℝ => A (x + s * (y - x)) - A x - s * (A' x * (y - x)))
        ((y - x) * A' (x + s * (y - x)) - A' x * (y - x)) (Set.Icc (0 : ℝ) 1) s := by
    intro s _
    have hlin : HasDerivAt (fun s : ℝ => x + s * (y - x)) (y - x) s := by
      simpa using ((hasDerivAt_id s).mul_const (y - x)).const_add x
    have hcomp : HasDerivAt (fun s : ℝ => A (x + s * (y - x)))
        (A' (x + s * (y - x)) * (y - x)) s := (hd1 (x + s * (y - x))).comp s hlin
    have hlin2 : HasDerivAt (fun s : ℝ => s * (A' x * (y - x))) (A' x * (y - x)) s := by
      simpa using (hasDerivAt_id s).mul_const (A' x * (y - x))
    have hsub := (hcomp.sub_const (A x)).sub hlin2
    have heq : A' (x + s * (y - x)) * (y - x) - A' x * (y - x)
        = (y - x) * A' (x + s * (y - x)) - A' x * (y - x) := by ring
    rw [heq] at hsub
    exact hsub.hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖(y - x) * A' (x + s * (y - x)) - A' x * (y - x)‖ ≤ (y - x) ^ 2 := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := le_of_lt hs.2
    have hd : |A' (x + s * (y - x)) - A' x| ≤ |s * (y - x)| := by
      have h := hLip (x + s * (y - x)) x
      have hrw : |x + s * (y - x) - x| = |s * (y - x)| := by
        congr 1
        ring
      rwa [hrw] at h
    have hsy : |s * (y - x)| ≤ |y - x| := by
      rw [abs_mul, abs_of_nonneg hs0]
      nlinarith [abs_nonneg (y - x)]
    rw [Real.norm_eq_abs, show (y - x) * A' (x + s * (y - x)) - A' x * (y - x)
      = (y - x) * (A' (x + s * (y - x)) - A' x) by ring, abs_mul]
    calc |y - x| * |A' (x + s * (y - x)) - A' x| ≤ |y - x| * |y - x| :=
          mul_le_mul_of_nonneg_left (hd.trans hsy) (abs_nonneg _)
      _ = (y - x) ^ 2 := by rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hh hbound
  have hone : A (x + (1 : ℝ) * (y - x)) - A x - (1 : ℝ) * (A' x * (y - x))
      = A y - A x - A' x * (y - x) := by
    rw [show x + (1 : ℝ) * (y - x) = y by ring]
    ring
  have hzero : A (x + (0 : ℝ) * (y - x)) - A x - (0 : ℝ) * (A' x * (y - x)) = 0 := by
    rw [show x + (0 : ℝ) * (y - x) = x by ring]
    ring
  rw [Real.norm_eq_abs, hone, hzero, sub_zero] at h
  exact h

/-- `∫ z² dγ = 1` for the standard Gaussian. -/
theorem integral_sq_stdGaussian :
    (∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1)) = 1 := by
  have h := integral_sq_sub_mean_gaussianReal (0 : ℝ) (1 : ℝ≥0)
  simpa using h

/--
**The improved variance-perturbation estimate.**

`|∫ A (x + √w z) dγ - A x| ≤ w` — order `w`, not `√w`.

The first-order term vanishes because the Gaussian is centred (`∫ z dγ = 0`), and the
remainder is controlled by the second-order Taylor bound, which the invariant `|A''| ≤ 1`
supplies.  This is the estimate that makes Target 2b's Lipschitz statement in `q` reachable;
the earlier `abs_integral_shift_sub_le` gives only `L √w 𝔼|Z|`, and that `√` is sharp for a
merely Lipschitz `A`.
-/
theorem abs_integral_shift_sub_le_second {A A' A'' : ℝ → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (hd1 : ∀ t, HasDerivAt A (A' t) t) (hd2 : ∀ t, HasDerivAt A' (A'' t) t)
    (hA''bd : ∀ t, |A'' t| ≤ 1)
    (hgrow : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    |(∫ z, A (x + Real.sqrt w * z) ∂(gaussianReal 0 1)) - A x| ≤ w := by
  classical
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  have hint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z)) μ :=
    integrable_of_hasLinearGrowth hgrow hmeas x w
  have hidint : Integrable (fun z : ℝ => z) μ := integrable_id_stdGaussian
  have hsqint : Integrable (fun z : ℝ => z ^ 2) μ :=
    integrable_sq_gaussianReal_centered 1
  have hlinint : Integrable (fun z : ℝ => A' x * (Real.sqrt w * z)) μ := by
    have h : Integrable (fun z : ℝ => (A' x * Real.sqrt w) * z) μ :=
      hidint.const_mul _
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    ring
  -- the first-order term integrates to zero
  have hzero : (∫ z : ℝ, A' x * (Real.sqrt w * z) ∂μ) = 0 := by
    have hfun : (fun z : ℝ => A' x * (Real.sqrt w * z))
        = fun z : ℝ => (A' x * Real.sqrt w) * z := by
      funext z; ring
    rw [hfun, integral_const_mul, hμ, integral_id_gaussianReal]
    simp
  have hsplit : (∫ z, (A (x + Real.sqrt w * z) - A x
        - A' x * (Real.sqrt w * z)) ∂μ)
      = (∫ z, A (x + Real.sqrt w * z) ∂μ) - A x := by
    have hAsub : Integrable (fun z : ℝ => A (x + Real.sqrt w * z) - A x) μ :=
      hint.sub (integrable_const (A x))
    rw [integral_sub hAsub hlinint,
      integral_sub hint (integrable_const (A x)), hzero, integral_const]
    simp [hμ, probReal_univ]
  -- pointwise second-order bound
  have hpt : ∀ z : ℝ, |A (x + Real.sqrt w * z) - A x
      - A' x * (Real.sqrt w * z)| ≤ w * z ^ 2 := by
    intro z
    have h := abs_taylor_second_le hd1 hd2 hA''bd x (x + Real.sqrt w * z)
    have hrw : (x + Real.sqrt w * z - x) = Real.sqrt w * z := by ring
    rw [hrw] at h
    have hsq : (Real.sqrt w * z) ^ 2 = w * z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hw]
    rw [hsq] at h
    exact h
  have hdomint : Integrable (fun z : ℝ => w * z ^ 2) μ := hsqint.const_mul w
  have hfullint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z) - A x
      - A' x * (Real.sqrt w * z)) μ :=
    (hint.sub (integrable_const (A x))).sub hlinint
  rw [← hsplit]
  calc |∫ z, (A (x + Real.sqrt w * z) - A x - A' x * (Real.sqrt w * z)) ∂μ|
      ≤ ∫ z, |A (x + Real.sqrt w * z) - A x - A' x * (Real.sqrt w * z)| ∂μ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ)
            (f := fun z => A (x + Real.sqrt w * z) - A x - A' x * (Real.sqrt w * z))
    _ ≤ ∫ z, w * z ^ 2 ∂μ :=
        integral_mono hfullint.abs hdomint hpt
    _ = w := by
        rw [integral_const_mul, hμ, integral_sq_stdGaussian, mul_one]

/-! ## 15. Measurability of the derivative functions

To iterate `hasParisiC2_parisiStep` up the recursion, the derivative functions produced at
each level must themselves be measurable, since they are the `A'`, `A''` of the next level.
They are parametrised Gaussian integrals, so `StronglyMeasurable.integral_prod_right'`
applies.
-/

/-- A parametrised Gaussian integral is measurable in the parameter. -/
theorem measurable_tilt_integral {f : ℝ → ℝ → ℝ}
    (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2)) :
    Measurable (fun x : ℝ => ∫ z, f x z ∂(gaussianReal 0 1)) :=
  (hf.stronglyMeasurable.integral_prod_right').measurable

/-- The shift `(x,z) ↦ x + √v z` is measurable. -/
theorem measurable_shift_prod (v : ℝ) :
    Measurable (fun p : ℝ × ℝ => p.1 + Real.sqrt v * p.2) := by fun_prop

theorem measurable_tiltE {A : ℝ → ℝ} (hmeas : Measurable A) (m v : ℝ) :
    Measurable (tiltE A m v) :=
  measurable_tilt_integral
    ((Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_shift_prod v)).const_mul m))

theorem measurable_tiltP {A A' : ℝ → ℝ} (hmeas : Measurable A) (hmeas' : Measurable A')
    (m v : ℝ) : Measurable (tiltP A A' m v) :=
  measurable_tilt_integral
    ((hmeas'.comp (measurable_shift_prod v)).mul
      ((Real.continuous_exp.measurable).comp
        ((hmeas.comp (measurable_shift_prod v)).const_mul m)))

theorem measurable_tiltR {A A' : ℝ → ℝ} (hmeas : Measurable A) (hmeas' : Measurable A')
    (m v : ℝ) : Measurable (tiltR A A' m v) :=
  measurable_tilt_integral
    (((hmeas'.comp (measurable_shift_prod v)).pow_const 2).mul
      ((Real.continuous_exp.measurable).comp
        ((hmeas.comp (measurable_shift_prod v)).const_mul m)))

theorem measurable_tiltQ {A A'' : ℝ → ℝ} (hmeas : Measurable A) (hmeas'' : Measurable A'')
    (m v : ℝ) : Measurable (tiltQ A A'' m v) :=
  measurable_tilt_integral
    ((hmeas''.comp (measurable_shift_prod v)).mul
      ((Real.continuous_exp.measurable).comp
        ((hmeas.comp (measurable_shift_prod v)).const_mul m)))

theorem measurable_stepD1 {A A' : ℝ → ℝ} (hmeas : Measurable A) (hmeas' : Measurable A')
    (m v : ℝ) : Measurable (stepD1 A A' m v) :=
  (measurable_tiltP hmeas hmeas' m v).div (measurable_tiltE hmeas m v)

theorem measurable_stepD2 {A A' A'' : ℝ → ℝ} (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (m v : ℝ) : Measurable (stepD2 A A' A'' m v) := by
  have hE := measurable_tiltE (A := A) hmeas m v
  have hP := measurable_tiltP hmeas hmeas' m v
  have hR := measurable_tiltR hmeas hmeas' m v
  have hQ := measurable_tiltQ hmeas hmeas'' m v
  exact (hQ.div hE).add (((hR.div hE).sub ((hP.div hE).pow_const 2)).const_mul m)

end SpinGlass
