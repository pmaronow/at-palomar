module

public import Paper.Gaussian
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Gaussian integration by parts

The standard Gaussian Stein identity is derived from the derivative of its
actual probability density and whole-line integration by parts. The bounded
version discharges weighted integrability. Boundary terms are discharged by
Mathlib's whole-line theorem for integrable products; no limiting boundary
identity is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The logarithmic derivative of the standard Gaussian density is `-x`. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
    convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1
    · rfl
    · dsimp
      ring
  have hp : gaussianPDFReal 0 1 =
      (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2)) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [hp]
  convert he.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1
  ring

/-- The first absolute Gaussian moment has an integrable density on `ℝ`. -/
theorem integrable_mul_standardGaussianPDF :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 by ring]
  ring

/-- Stein's identity with its three weighted integrability obligations explicit.

This is a genuine integration-by-parts proof. No Gaussian IBP identity or
boundary-limit assumption appears among the hypotheses.
-/
theorem gaussian_stein_of_weighted_integrable (f df : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hf : Integrable (fun x => gaussianPDFReal 0 1 x * f x))
    (hdf : Integrable (fun x => gaussianPDFReal 0 1 x * df x))
    (hxf : Integrable (fun x => gaussianPDFReal 0 1 x * (x * f x))) :
    gaussianExpectation (fun x => x * f x) = gaussianExpectation df := by
  have hi : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert hxf.neg using 1
    funext x
    dsimp
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := df)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x)
    hi (by
      convert hdf using 1
      funext x
      exact mul_comm _ _)
    (by
      convert hf using 1
      funext x
      exact mul_comm _ _)
  have hl : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x * (x * f x))) := by
    funext x
    ring
  have hr : (fun x => df x * gaussianPDFReal 0 1 x) =
      (fun x => gaussianPDFReal 0 1 x * df x) := by
    funext x
    ring
  rw [hl, hr, integral_neg] at h
  have hs := neg_injective h
  unfold gaussianExpectation
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul] using hs

/-- Standard Gaussian integration by parts for bounded continuously
differentiable observables with bounded derivative.

This proves all weighted integrability and boundary requirements from the
boundedness hypotheses, using Gaussian density moments.
-/
theorem gaussian_stein_of_bounded (f df : ℝ → ℝ) (M K : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖df x‖ ≤ K) :
    gaussianExpectation (fun x => x * f x) = gaussianExpectation df := by
  apply gaussian_stein_of_weighted_integrable f df hd
  · exact (integrable_gaussianPDFReal 0 1).mul_bdd hf.aestronglyMeasurable
      (.of_forall hb)
  · exact (integrable_gaussianPDFReal 0 1).mul_bdd hdf.aestronglyMeasurable
      (.of_forall hdb)
  · have hi := integrable_mul_standardGaussianPDF.mul_bdd hf.aestronglyMeasurable
      (.of_forall hb)
    convert hi using 1
    funext x
    ring

/-- Stein's identity after composing with an arbitrary affine Gaussian field. -/
theorem gaussian_affine_stein (f df : ℝ → ℝ) (h a M K : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖df x‖ ≤ K) :
    gaussianExpectation (fun z => z * f (h + a * z)) =
      a * gaussianExpectation (fun z => df (h + a * z)) := by
  have hc : Continuous (fun z : ℝ => h + a * z) := by fun_prop
  have hderiv : ∀ x, HasDerivAt (fun z => f (h + a * z))
      (a * df (h + a * x)) x := by
    intro x
    have ha : HasDerivAt (fun z : ℝ => h + a * z) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).const_add h
    simpa only [Function.comp_def, mul_comm] using (hd (h + a * x)).comp x ha
  have hbound : ∀ x, ‖a * df (h + a * x)‖ ≤ ‖a‖ * K := by
    intro x
    simpa only [norm_mul] using
      mul_le_mul_of_nonneg_left (hdb (h + a * x)) (norm_nonneg a)
  have hs := gaussian_stein_of_bounded (fun z => f (h + a * z))
    (fun z => a * df (h + a * z)) M (‖a‖ * K)
    (hf.comp hc) (continuous_const.mul (hdf.comp hc)) hderiv
    (fun z => hb (h + a * z)) hbound
  simpa only [gaussianExpectation, integral_const_mul] using hs

/-- Centering the affine field gives its variance `a²` in the IBP identity. -/
theorem gaussian_affine_stein_centered (f df : ℝ → ℝ) (h a M K : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖df x‖ ≤ K) :
    gaussianExpectation (fun z => ((h + a * z) - h) * f (h + a * z)) =
      a ^ 2 * gaussianExpectation (fun z => df (h + a * z)) := by
  have he : gaussianExpectation (fun z => ((h + a * z) - h) * f (h + a * z)) =
      a * gaussianExpectation (fun z => z * f (h + a * z)) := by
    unfold gaussianExpectation
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [he, gaussian_affine_stein f df h a M K hf hdf hd hb hdb]
  ring

/-- The exact Gaussian integration-by-parts formula used in the appendix:
`E[(Y-h) f(Y)] = t E[f'(Y)]`, where `Y=h+√t Z`.
-/
theorem gaussian_variance_stein (f df : ℝ → ℝ) (h t M K : ℝ) (ht : 0 ≤ t)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ M) (hdb : ∀ x, ‖df x‖ ≤ K) :
    gaussianExpectation (fun z => ((h + Real.sqrt t * z) - h) *
      f (h + Real.sqrt t * z)) =
      t * gaussianExpectation (fun z => df (h + Real.sqrt t * z)) := by
  simpa only [Real.sq_sqrt ht] using
    gaussian_affine_stein_centered f df h (Real.sqrt t) M K hf hdf hd hb hdb

end Paper
