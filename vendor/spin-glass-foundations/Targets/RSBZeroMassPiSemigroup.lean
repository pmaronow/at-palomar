module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/-
# The N-site zero-mass smoothing semigroup

The leading-zero-mass reduction requires equality of the actual N-site
cascades, not merely their scalar endpoints. The Gaussian law is obtained
coordinatewise from Mathlib's convolution and product-measure reindexing.
-/
public import Targets.TalagrandCore
public import Targets.ParisiStepSemigroup

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

noncomputable abbrev piGaussVariance (n : ℕ) (v : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 v)

theorem piGaussVariance_conv (n : ℕ) (v₁ v₂ : ℝ≥0) :
    piGaussVariance n v₁ ∗ piGaussVariance n v₂ = piGaussVariance n (v₁ + v₂) := by
  have hscalar : ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
      (fun z : ℝ × ℝ => z.1 + z.2) = gaussianReal 0 (v₁ + v₂) := by
    simpa only [Measure.conv, zero_add] using
      (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := v₁) (v₂ := v₂))
  haveI : IsProbabilityMeasure (((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
      (fun z : ℝ × ℝ => z.1 + z.2)) := by rw [hscalar]; infer_instance
  rw [Measure.conv, ← (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => gaussianReal 0 v₁) (fun _ => gaussianReal 0 v₂)).map_eq]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin n => (gaussianReal 0 v₁).prod (gaussianReal 0 v₂))).map
    (fun z i => (z i).1 + (z i).2) = _
  have H := Measure.pi_map_pi
    (μ := fun _ : Fin n => (gaussianReal 0 v₁).prod (gaussianReal 0 v₂))
    (f := fun _ z => z.1 + z.2) (fun _ => by fun_prop)
  simpa only [hscalar] using! H

theorem piGauss_map_sqrt_mul (n : ℕ) (v : ℝ≥0) :
    (piGauss n).map (fun z i => Real.sqrt (v : ℝ) * z i) = piGaussVariance n v := by
  have hscalar : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z)) := by
    rw [hscalar]; infer_instance
  have H := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun _ z => Real.sqrt (v : ℝ) * z) (fun _ => by fun_prop)
  simpa only [hscalar] using! H

theorem parisiStepPi_zero_eq_integral {n : ℕ} (v : ℝ≥0)
    {A : (Fin n → ℝ) → ℝ} (hA : Measurable A) (x : Fin n → ℝ) :
    parisiStepPi n 0 v A x = ∫ z, A (x + z) ∂piGaussVariance n v := by
  rw [← piGauss_map_sqrt_mul n v]
  have hf : Measurable (fun z : Fin n → ℝ => A (x + z)) :=
    hA.comp (measurable_const.add measurable_id)
  have H := integral_map (μ := piGauss n)
    (φ := fun z i => Real.sqrt (v : ℝ) * z i)
    ((Measurable.of_eval fun i => (measurable_pi_apply i).const_mul _).aemeasurable)
    hf.aestronglyMeasurable
  simpa only [parisiStepPi, if_pos rfl, Pi.add_apply] using! H.symm

theorem integrable_piGaussVariance_shift {n : ℕ} (v : ℝ≥0)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (x : Fin n → ℝ) :
    Integrable (fun z => A (x + z)) (piGaussVariance n v) := by
  rw [← piGauss_map_sqrt_mul n v]
  have hf : Measurable (fun z : Fin n → ℝ => A (x + z)) :=
    hA.measurable.comp (measurable_const.add measurable_id)
  apply (integrable_map_measure hf.aestronglyMeasurable
    ((Measurable.of_eval fun i => (measurable_pi_apply i).const_mul _).aemeasurable)).mpr
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  exact integrable_shift_pi hD hb hA.measurable x

/-- The genuine expectation branch has the variance-addition semigroup law. -/
theorem parisiStepPi_zero_add {n : ℕ} {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) :
    parisiStepPi n 0 (v₁ + v₂) A = fun x => parisiStepPi n 0 v₁ (parisiStepPi n 0 v₂ A) x := by
  let w₁ : ℝ≥0 := ⟨v₁, hv₁⟩
  let w₂ : ℝ≥0 := ⟨v₂, hv₂⟩
  funext x
  have hint : Integrable (fun z => A (x + z)) (piGaussVariance n w₁ ∗ piGaussVariance n w₂) := by
    rw [piGaussVariance_conv]
    exact integrable_piGaussVariance_shift (w₁ + w₂) hA x
  change parisiStepPi n 0 ((w₁ + w₂ : ℝ≥0) : ℝ) A x =
    parisiStepPi n 0 w₁ (parisiStepPi n 0 w₂ A) x
  rw [parisiStepPi_zero_eq_integral (w₁ + w₂) hA.measurable,
    ← piGaussVariance_conv n w₁ w₂, integral_conv hint,
    parisiStepPi_zero_eq_integral w₁ (measurable_parisiStepPi hA.measurable 0 _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [parisiStepPi_zero_eq_integral w₂ hA.measurable]
  simp only [add_assoc]

end SpinGlass.Targets
