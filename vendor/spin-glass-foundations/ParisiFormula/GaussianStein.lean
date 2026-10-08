module

/-
# Stein's identity for the standard Gaussian, with minimal hypotheses

New work for the ParisiFormula project (not vendored).

Gaussian integration by parts (Talagrand's (3.1)) is the engine of the proof of Theorem 2.1.
RSAT's versions (`stein_coord_with_param`, `gaussian_integration_by_parts_hilbert_cov`, …)
require the test function to be Fréchet-`C¹` on the whole Hilbert space, and its one-dimensional
`gaussianReal_stein` requires continuity of the derivative.  The cascade functional of
`Targets/Talagrand.lean` is differentiated *along lines* by the tilted chain rule, which yields
`HasDerivAt` and growth bounds but not continuity of the derivative.  This file proves the
one-dimensional identity

  `∫ x g(x) dγ = ∫ g'(x) dγ`

from `HasDerivAt` and integrability alone, via Mathlib's whole-line integration by parts
`integral_mul_deriv_eq_deriv_mul_of_integrable` against the density `φ`, using `φ' = -x φ`.
-/
public import ParisiFormula.GaussianExpCompare

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped NNReal

namespace SpinGlass

/-- The standard Gaussian density in closed form. -/
theorem gaussianPDFReal_std_eq :
    gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  funext y
  simp [gaussianPDFReal]

/-- `φ' = -x φ` for the standard Gaussian density. -/
theorem hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_std_eq]
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine this.congr_deriv ?_
    norm_num
    ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * π))⁻¹)
  refine h2.congr_deriv ?_
  ring

/-- Integrability against `gaussianReal 0 1` is integrability of `φ · f` against Lebesgue. -/
theorem integrable_gaussianReal_iff_std (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have hfun : (fun x => (gaussianPDF 0 1 x).toReal • f x)
      = fun x => gaussianPDFReal 0 1 x * f x := by
    funext x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]
  rw [hfun]

/--
**Stein's identity, from `HasDerivAt` and integrability alone.**

  `∫ x g(x) dγ = ∫ g'(x) dγ`.
-/
theorem gaussianReal_stein_of_hasDerivAt (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hgi : Integrable g (gaussianReal 0 1))
    (hxg : Integrable (fun x => x * g x) (gaussianReal 0 1))
    (hg'i : Integrable g' (gaussianReal 0 1)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by norm_num
  rw [integral_gaussianReal_eq_integral_smul h1, integral_gaussianReal_eq_integral_smul h1]
  simp only [smul_eq_mul]
  have hA : Integrable (fun x => gaussianPDFReal 0 1 x * (x * g x)) :=
    (integrable_gaussianReal_iff_std _).1 hxg
  have hB : Integrable (fun x => gaussianPDFReal 0 1 x * g' x) :=
    (integrable_gaussianReal_iff_std _).1 hg'i
  have hC : Integrable (fun x => gaussianPDFReal 0 1 x * g x) :=
    (integrable_gaussianReal_iff_std _).1 hgi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal 0 1) (u' := g') (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal_std x) ?_ ?_ ?_
  · have hl : (∫ x, g x * (-x * gaussianPDFReal 0 1 x))
        = -∫ x, gaussianPDFReal 0 1 x * (x * g x) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    have hr : (∫ x, g' x * gaussianPDFReal 0 1 x) = ∫ x, gaussianPDFReal 0 1 x * g' x := by
      congr 1
      funext x
      ring
    rw [hl, hr] at hibp
    linarith
  · refine hA.neg.congr (Filter.Eventually.of_forall fun x => ?_)
    show -(gaussianPDFReal 0 1 x * (x * g x)) = g x * (-x * gaussianPDFReal 0 1 x)
    ring
  · refine hB.congr (Filter.Eventually.of_forall fun x => ?_)
    show gaussianPDFReal 0 1 x * g' x = g' x * gaussianPDFReal 0 1 x
    ring
  · refine hC.congr (Filter.Eventually.of_forall fun x => ?_)
    show gaussianPDFReal 0 1 x * g x = g x * gaussianPDFReal 0 1 x
    ring

/-- Stein's identity under exponential growth bounds on `g` and `g'`, which is the form the
cascade functional satisfies along a coordinate line. -/
theorem gaussianReal_stein_of_bound (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'm : Measurable g') {C c : ℝ}
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hg'b : ∀ x, |g' x| ≤ C * Real.exp (c * |x|)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  have hgm : Measurable g :=
    (continuous_iff_continuousAt.2 fun x => (hg x).continuousAt).measurable
  have hC : 0 ≤ C := by
    have := hgb 0
    have := abs_nonneg (g 0)
    have := Real.exp_pos (c * |(0 : ℝ)|)
    nlinarith
  have hexp := integrable_exp_abs_mul_stdGaussian c
  have hxexp := integrable_abs_mul_exp_abs_stdGaussian c
  have hgi : Integrable g (gaussianReal 0 1) := by
    refine Integrable.mono (hexp.const_mul C) hgm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    exact hgb x
  have hg'i : Integrable g' (gaussianReal 0 1) := by
    refine Integrable.mono (hexp.const_mul C) hg'm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    exact hg'b x
  have hxg : Integrable (fun x => x * g x) (gaussianReal 0 1) := by
    refine Integrable.mono (hxexp.const_mul C) (measurable_id.mul hgm).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mul_nonneg hC (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le))]
    have := mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg x)
    linarith
  exact gaussianReal_stein_of_hasDerivAt g g' hg hgi hxg hg'i


/-! ## Variance `v`, and the product form

The coordinate `c_i` of the disorder has variance `τ_i`, so Stein is needed for `gaussianReal
0 v`, `v ≠ 0`: `∫ x g dγ_v = v ∫ g' dγ_v`.  The product form is Fubini over the complementary
coordinates: for `Φ` on `α × ℝ` differentiable in the second variable, and integrable together
with `p.2 * Φ` and `Φ'` on `μ_Y ⊗ γ_v`, `∫ p.2 Φ(p) = v ∫ Φ'(p)`.
-/

theorem gaussianPDFReal_eq (v : ℝ≥0) :
    gaussianPDFReal 0 v
      = fun y : ℝ => (Real.sqrt (2 * π * v))⁻¹ * Real.exp (-y ^ 2 / (2 * v)) := by
  funext y
  simp [gaussianPDFReal]

/-- `φ_v' = -(x/v) φ_v`. -/
theorem hasDerivAt_gaussianPDFReal (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  rw [gaussianPDFReal_eq]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) (-(x / v)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const (2 * (v : ℝ))
    refine this.congr_deriv ?_
    field_simp
    ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * π * v))⁻¹)
  refine h2.congr_deriv ?_
  ring

theorem integrable_gaussianReal_iff (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 v) ↔ Integrable (fun x => gaussianPDFReal 0 v x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have hfun : (fun x => (gaussianPDF 0 v x).toReal • f x)
      = fun x => gaussianPDFReal 0 v x * f x := by
    funext x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v x), smul_eq_mul]
  rw [hfun]

/-- **Stein's identity for variance `v`**: `∫ x g dγ_v = v ∫ g' dγ_v`. -/
theorem gaussianReal_stein_var (v : ℝ≥0) (hv : v ≠ 0) (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hgi : Integrable g (gaussianReal 0 v))
    (hxg : Integrable (fun x => x * g x) (gaussianReal 0 v))
    (hg'i : Integrable g' (gaussianReal 0 v)) :
    ∫ x, x * g x ∂(gaussianReal 0 v) = (v : ℝ) * ∫ x, g' x ∂(gaussianReal 0 v) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hA : Integrable (fun x => gaussianPDFReal 0 v x * (x * g x)) :=
    (integrable_gaussianReal_iff v hv _).1 hxg
  have hB : Integrable (fun x => gaussianPDFReal 0 v x * g' x) :=
    (integrable_gaussianReal_iff v hv _).1 hg'i
  have hC : Integrable (fun x => gaussianPDFReal 0 v x * g x) :=
    (integrable_gaussianReal_iff v hv _).1 hgi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal 0 v) (u' := g')
    (v' := fun x => -(x / v) * gaussianPDFReal 0 v x)
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal v hv x) ?_ ?_ ?_
  · have hl : (∫ x, g x * (-(x / v) * gaussianPDFReal 0 v x))
        = -((v : ℝ)⁻¹ * ∫ x, gaussianPDFReal 0 v x * (x * g x)) := by
      rw [← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      field_simp
    have hr : (∫ x, g' x * gaussianPDFReal 0 v x) = ∫ x, gaussianPDFReal 0 v x * g' x := by
      congr 1
      funext x
      ring
    rw [hl, hr] at hibp
    have hIJ : ((v : ℝ)⁻¹ * ∫ x, gaussianPDFReal 0 v x * (x * g x))
        = ∫ x, gaussianPDFReal 0 v x * g' x := by linarith
    rw [← hIJ, mul_inv_cancel_left₀ hv']
  · refine (hA.const_mul ((v : ℝ)⁻¹)).neg.congr (Filter.Eventually.of_forall fun x => ?_)
    show -((v : ℝ)⁻¹ * (gaussianPDFReal 0 v x * (x * g x)))
        = g x * (-(x / v) * gaussianPDFReal 0 v x)
    field_simp
  · refine hB.congr (Filter.Eventually.of_forall fun x => ?_)
    show gaussianPDFReal 0 v x * g' x = g' x * gaussianPDFReal 0 v x
    ring
  · refine hC.congr (Filter.Eventually.of_forall fun x => ?_)
    show gaussianPDFReal 0 v x * g x = g x * gaussianPDFReal 0 v x
    ring

/-- **Stein's identity on a product `μ_Y ⊗ γ_v`, along the second coordinate.** -/
theorem stein_prod_of_hasDerivAt {α : Type*} [MeasurableSpace α] (μY : Measure α) [SFinite μY]
    (v : ℝ≥0) (hv : v ≠ 0) (Φ Φ' : α × ℝ → ℝ)
    (hd : ∀ y x, HasDerivAt (fun t => Φ (y, t)) (Φ' (y, x)) x)
    (hΦ : Integrable Φ (μY.prod (gaussianReal 0 v)))
    (hxΦ : Integrable (fun p : α × ℝ => p.2 * Φ p) (μY.prod (gaussianReal 0 v)))
    (hΦ' : Integrable Φ' (μY.prod (gaussianReal 0 v))) :
    ∫ p, p.2 * Φ p ∂(μY.prod (gaussianReal 0 v))
      = (v : ℝ) * ∫ p, Φ' p ∂(μY.prod (gaussianReal 0 v)) := by
  rw [integral_prod _ hxΦ, integral_prod _ hΦ', ← integral_const_mul]
  have h1 := hΦ.prod_right_ae
  have h2 := hxΦ.prod_right_ae
  have h3 := hΦ'.prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  exact gaussianReal_stein_var v hv (fun t => Φ (y, t)) (fun t => Φ' (y, t))
    (fun x => hd y x) hy1 hy2 hy3

end SpinGlass
