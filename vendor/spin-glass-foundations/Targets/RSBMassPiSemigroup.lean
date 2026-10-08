module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/-
# The N-site Parisi semigroup at arbitrary mass

An adapter from the already checked product Gaussian convolution law. This is
the analytic identity needed to delete equal adjacent masses in (2.19).
-/
public import Targets.RSBZeroMassPiSemigroup

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace SpinGlass.Targets

theorem parisiStepPi_nonzero_eq_integral {n : ℕ} {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0)
    {A : (Fin n → ℝ) → ℝ} (hA : Measurable A) (x : Fin n → ℝ) :
    parisiStepPi n m v A x =
      (1 / m) * Real.log (∫ z, Real.exp (m * A (x + z)) ∂piGaussVariance n v) := by
  have H := parisiStepPi_zero_eq_integral v (hA.const_mul m).exp x
  simp only [parisiStepPi, if_true] at H
  simp only [parisiStepPi, if_neg hm, H]

theorem integrable_exp_piGaussVariance_shift {n : ℕ} (m : ℝ) (v : ℝ≥0)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (x : Fin n → ℝ) :
    Integrable (fun z => Real.exp (m * A (x + z))) (piGaussVariance n v) := by
  rw [← piGauss_map_sqrt_mul n v]
  have hf : Measurable (fun z : Fin n → ℝ => Real.exp (m * A (x + z))) :=
    ((hA.measurable.comp (measurable_const.add measurable_id)).const_mul m).exp
  apply (integrable_map_measure hf.aestronglyMeasurable
    ((Measurable.of_eval fun i => (measurable_pi_apply i).const_mul _).aemeasurable)).mpr
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  exact integrable_exp_shift_pi hD hb hA.measurable x

theorem exp_mul_parisiStepPi_eq_integral {n : ℕ} {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (x : Fin n → ℝ) :
    Real.exp (m * parisiStepPi n m v A x) =
      ∫ z, Real.exp (m * A (x + z)) ∂piGaussVariance n v := by
  rw [parisiStepPi_nonzero_eq_integral hm v hA.measurable, ← mul_assoc,
    mul_one_div_cancel hm, one_mul, Real.exp_log]
  exact integral_exp_pos (integrable_exp_piGaussVariance_shift m v hA x)

/-- Equal adjacent logarithmic-Laplace masses can be merged, including mass
zero and either zero variance, for any measurable affine-growth terminal. -/
theorem parisiStepPi_add {n : ℕ} (m : ℝ) {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) :
    parisiStepPi n m (v₁ + v₂) A = fun x => parisiStepPi n m v₁ (parisiStepPi n m v₂ A) x := by
  by_cases hm : m = 0
  · subst m
    exact parisiStepPi_zero_add hv₁ hv₂ hA
  let w₁ : ℝ≥0 := ⟨v₁, hv₁⟩
  let w₂ : ℝ≥0 := ⟨v₂, hv₂⟩
  funext x
  have hint : Integrable (fun z => Real.exp (m * A (x + z)))
      (piGaussVariance n w₁ ∗ piGaussVariance n w₂) := by
    rw [piGaussVariance_conv]
    exact integrable_exp_piGaussVariance_shift m (w₁ + w₂) hA x
  change parisiStepPi n m ((w₁ + w₂ : ℝ≥0) : ℝ) A x =
    parisiStepPi n m w₁ (parisiStepPi n m w₂ A) x
  rw [parisiStepPi_nonzero_eq_integral hm (w₁ + w₂) hA.measurable,
    ← piGaussVariance_conv n w₁ w₂, integral_conv hint,
    parisiStepPi_nonzero_eq_integral hm w₁ (measurable_parisiStepPi hA.measurable m _)]
  congr 2
  apply integral_congr_ae
  filter_upwards with z
  rw [exp_mul_parisiStepPi_eq_integral hm w₂ hA]
  simp only [add_assoc]

end SpinGlass.Targets
