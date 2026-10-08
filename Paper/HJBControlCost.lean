module

public import Paper.ParisiControlledState
public import Paper.HJBVerification

@[expose] public section

/-! Actual integrability of bounded-control costs over every time cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

lemma norm_hjb_actual_cost_le (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (r : ℝ) (sample : BrownianSample) :
    ‖β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2‖ ≤ β ^ 2 / 2 := by
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2),
    Real.norm_of_nonneg (parisiCDF_nonneg μ r), norm_pow]
  calc
    _ ≤ β ^ 2 / 2 * 1 * 1 := by
      gcongr
      · exact parisiCDF_le_one μ r
      · exact pow_le_one₀ (norm_nonneg _) (hA.bounded r sample)
    _ = _ := by ring

lemma hjb_actual_cost_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (a b : ℝ) (sample : BrownianSample) :
    IntervalIntegrable (fun r => β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2) volume a b := by
  apply (intervalIntegrable_const (c := β ^ 2 / 2)).mono_fun'
  · exact (((parisiCDF_measurable μ).const_mul _).mul
      ((hA.measurable.comp (measurable_id.prodMk measurable_const)).pow_const 2)).aestronglyMeasurable
  · exact .of_forall (fun r => norm_hjb_actual_cost_le β μ A hA r sample)

lemma hjb_actual_cost_integrable (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (a b : ℝ) (hab : a ≤ b) :
    Integrable (fun sample => ∫ r in a..b, β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2)
      canonicalBrownianMeasure := by
  have hmj : Measurable (fun p : ℝ × BrownianSample => β ^ 2 / 2 * parisiCDF μ p.1 * A p.1 p.2 ^ 2) :=
    (measurable_const.mul ((parisiCDF_measurable μ).comp measurable_fst)).mul (hA.measurable.pow_const 2)
  have hi := hmj.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc a b))
  have hmInt : Measurable (fun sample => ∫ r in a..b, β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2) := by
    simpa only [intervalIntegral.integral_of_le hab] using hi.measurable
  apply (integrable_const ((β ^ 2 / 2) * |b - a|)).mono' hmInt.aestronglyMeasurable
  exact .of_forall (fun sample => intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r _ => norm_hjb_actual_cost_le β μ A hA r sample))

end Paper
