module

public import Paper.GaussianIBP
public import Paper.GaussianPositivity
public import Paper.ATAlgebra

@[expose] public section

/-!
# Strict signs on the concrete AT zero set

The Gaussian Stein relation and the pointwise hyperbolic inequality prove
the final strict gap needed for the appendix's inverse-temperature derivative.
Every quantity here is an actual Gaussian expectation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The unweighted pointwise gap in the last Stein argument of the appendix. -/
def tanhSteinGap (y : ℝ) : ℝ :=
  Real.tanh y * (Real.tanh y - y * sech y ^ 2)

/-- Strict positivity of the last Stein gap away from zero. -/
theorem tanhSteinGap_pos (y : ℝ) (hy : y ≠ 0) : 0 < tanhSteinGap y :=
  tanh_mul_tanh_sub_mul_sech_sq_pos hy

/-- Nonnegativity of the last Stein gap on the full real line. -/
theorem tanhSteinGap_nonneg (y : ℝ) : 0 ≤ tanhSteinGap y := by
  by_cases hy : y = 0
  · simp [hy, tanhSteinGap]
  · exact (tanhSteinGap_pos y hy).le

/-- The second mixed pointwise moment is bounded by one. -/
theorem norm_y_tanh_sech_sq_le_one (y : ℝ) :
    ‖y * Real.tanh y * sech y ^ 2‖ ≤ 1 := by
  have hytanh : 0 ≤ y * Real.tanh y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (mul_tanh_pos hy).le
  have hnonneg : 0 ≤ y * Real.tanh y * sech y ^ 2 := mul_nonneg hytanh (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hgap := tanhSteinGap_nonneg y
  unfold tanhSteinGap at hgap
  have ht := tanh_sq_le_one y
  nlinarith

/-- The last Stein gap itself is bounded by one. -/
theorem norm_tanhSteinGap_le_one (y : ℝ) : ‖tanhSteinGap y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (tanhSteinGap_nonneg y)]
  have hytanh : 0 ≤ y * Real.tanh y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (mul_tanh_pos hy).le
  have hprod := mul_nonneg hytanh (sq_nonneg (sech y))
  have ht := tanh_sq_le_one y
  unfold tanhSteinGap
  nlinarith

/-- The mixed second moment used in the appendix's final Stein calculation. -/
def gaussianMixedSecond (h t : ℝ) : ℝ :=
  gaussianExpectation (fun z => (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) *
    sech (h + Real.sqrt t * z) ^ 2)

theorem integrable_gaussianU_integrand (h t : ℝ) :
    Integrable (fun z => Real.tanh (h + Real.sqrt t * z) * sech (h + Real.sqrt t * z) ^ 2)
      (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 2)).comp
      (by fun_prop : Continuous (fun z : ℝ => h + Real.sqrt t * z))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => norm_tanh_mul_sech_pow_le_one _ 2)

theorem integrable_gaussianMixedSecond_integrand (h t : ℝ) :
    Integrable (fun z => (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) *
      sech (h + Real.sqrt t * z) ^ 2) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (((continuous_id.mul gaussian_continuous_tanh).mul
      (gaussian_continuous_sech.pow 2)).comp
      (by fun_prop : Continuous (fun z : ℝ => h + Real.sqrt t * z))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => norm_y_tanh_sech_sq_le_one _)

/-- The derivative in the second Stein calculation is uniformly bounded. -/
theorem norm_tanh_sech_sq_derivative_le_five (y : ℝ) :
    ‖3 * sech y ^ 4 - 2 * sech y ^ 2‖ ≤ 5 := by
  rw [Real.norm_eq_abs]
  have hs2 := sech_sq_le_one y
  have hs4 := sech_fourth_le_one y
  have hp2 := sq_nonneg (sech y)
  have hp4 := pow_nonneg (sech_pos y).le 4
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The genuine Gaussian Stein relation for `tanh*sech²`. -/
theorem gaussianMixedSecond_stein (h t : ℝ) (ht : 0 ≤ t) :
    gaussianMixedSecond h t - h * gaussianU h t = t * (3 * gaussianC h t - 2 * gaussianA h t) := by
  have hs := gaussian_variance_stein (fun y => Real.tanh y * sech y ^ 2)
    (fun y => 3 * sech y ^ 4 - 2 * sech y ^ 2) h t 1 5 ht
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 2))
    (((continuous_const.mul (gaussian_continuous_sech.pow 4)).sub
      (continuous_const.mul (gaussian_continuous_sech.pow 2))))
    hasDerivAt_tanh_mul_sech_sq
    (fun y => norm_tanh_mul_sech_pow_le_one y 2) norm_tanh_sech_sq_derivative_le_five
  have hleft : gaussianExpectation (fun z => ((h + Real.sqrt t * z) - h) *
      (Real.tanh (h + Real.sqrt t * z) * sech (h + Real.sqrt t * z) ^ 2)) =
      gaussianMixedSecond h t - h * gaussianU h t := by
    unfold gaussianMixedSecond gaussianU gaussianExpectation
    rw [← integral_const_mul]
    have hhu : Integrable (fun z => h *
        (Real.tanh (h + Real.sqrt t * z) * sech (h + Real.sqrt t * z) ^ 2))
        (gaussianReal 0 1) := (integrable_gaussianU_integrand h t).const_mul h
    rw [← integral_sub (integrable_gaussianMixedSecond_integrand h t) hhu]
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hright : gaussianExpectation (fun z =>
      3 * sech (h + Real.sqrt t * z) ^ 4 - 2 * sech (h + Real.sqrt t * z) ^ 2) =
      3 * gaussianC h t - 2 * gaussianA h t := by
    unfold gaussianC gaussianA gaussianExpectation
    rw [integral_sub ((integrable_gaussian_sech_pow h (Real.sqrt t) 4).const_mul 3)
      ((integrable_gaussian_sech_pow h (Real.sqrt t) 2).const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hleft, hright] at hs
  exact hs

/-- The squared-tanh expectation is exactly the complement of `A`. -/
theorem gaussian_tanh_sq_expectation_eq_one_sub_A (h t : ℝ) :
    gaussianExpectation (fun z => Real.tanh (h + Real.sqrt t * z) ^ 2) = 1 - gaussianA h t := by
  have htanh : Integrable (fun z => Real.tanh (h + Real.sqrt t * z) ^ 2)
      (gaussianReal 0 1) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((gaussian_continuous_tanh.pow 2).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact tanh_sq_le_one _
  have hi : gaussianExpectation (fun z => Real.tanh (h + Real.sqrt t * z) ^ 2) + gaussianA h t = 1 := by
    unfold gaussianA gaussianExpectation
    rw [← integral_add htanh (integrable_gaussian_sech_pow h (Real.sqrt t) 2)]
    simp_rw [tanh_sq_add_sech_sq]
    simp
  linarith

/-- The last pointwise Stein gap has strictly positive actual expectation. -/
theorem gaussian_tanhSteinGap_pos (h t : ℝ) (ht : 0 < t) :
    0 < gaussianExpectation (fun z => tanhSteinGap (h + Real.sqrt t * z)) := by
  have hc : Continuous tanhSteinGap :=
    gaussian_continuous_tanh.mul (gaussian_continuous_tanh.sub
      (continuous_id.mul (gaussian_continuous_sech.pow 2)))
  rw [gaussianExpectation_shift_eq_integral h t ht.le tanhSteinGap hc.measurable]
  apply gaussian_integral_pos_of_continuous_nonneg h t.toNNReal
    (Real.toNNReal_pos.mpr ht).ne' tanhSteinGap hc (x := 1)
  · apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall norm_tanhSteinGap_le_one
  · exact tanhSteinGap_nonneg
  · exact tanhSteinGap_pos 1 (by norm_num)

/-- On the actual AT zero set, the final gap is an expectation of the
strictly positive pointwise Stein gap. -/
theorem gaussian_zero_curve_gap_identity (h t : ℝ) (ht : 0 ≤ t)
    (hzero : atZeroFunction h t = 0) :
    2 * t * gaussianB h t - h * gaussianU h t =
      gaussianExpectation (fun z => tanhSteinGap (h + Real.sqrt t * z)) := by
  have hs := gaussianMixedSecond_stein h t ht
  have hz : t * gaussianC h t = 1 - gaussianA h t := by
    unfold atZeroFunction at hzero
    linarith
  have hgap : gaussianExpectation (fun z => tanhSteinGap (h + Real.sqrt t * z)) =
      (1 - gaussianA h t) - gaussianMixedSecond h t := by
    rw [← gaussian_tanh_sq_expectation_eq_one_sub_A]
    unfold gaussianMixedSecond gaussianExpectation
    have htanh : Integrable (fun z => Real.tanh (h + Real.sqrt t * z) ^ 2)
        (gaussianReal 0 1) := by
      apply (integrable_const (1 : ℝ)).mono'
        ((gaussian_continuous_tanh.pow 2).comp (by fun_prop)).aestronglyMeasurable
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact tanh_sq_le_one _
    rw [← integral_sub htanh (integrable_gaussianMixedSecond_integrand h t)]
    apply integral_congr_ae
    filter_upwards with z
    unfold tanhSteinGap
    ring
  rw [hgap]
  unfold gaussianB
  linarith

/-- The actual strict sign `2tB-hu>0` on the AT zero set. -/
theorem gaussian_zero_curve_gap_pos (h t : ℝ) (ht : 0 < t)
    (hzero : atZeroFunction h t = 0) :
    0 < 2 * t * gaussianB h t - h * gaussianU h t := by
  rw [gaussian_zero_curve_gap_identity h t ht.le hzero]
  exact gaussian_tanhSteinGap_pos h t ht

/-- Every analytic strict sign needed for the appendix's total derivative
of `C` is discharged for the actual moments on a positive-field zero. -/
theorem gaussian_zero_curve_C_slope_neg (h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hzero : atZeroFunction h t = 0) :
    2 * (h * gaussianV h t - gaussianT h t) / t -
      4 * gaussianV h t * (gaussianB h t - gaussianT h t + h * gaussianV h t) /
        (gaussianU h t + 2 * t * gaussianV h t) < 0 := by
  exact at_curve_derivative_neg h t (gaussianB h t) (gaussianT h t)
    (gaussianU h t) (gaussianV h t) ht (gaussianU_pos h t hh ht)
    (gaussianV_pos h t hh ht) (gaussianT_pos h t ht)
    (gaussian_zero_curve_gap_pos h t ht hzero)

end Paper
