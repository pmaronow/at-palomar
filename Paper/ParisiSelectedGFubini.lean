module

public import Paper.ParisiSelectedMoment
public import Paper.JTFubini

@[expose] public section

/-! # Actual stochastic G and its cumulative-measure pairing -/

open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace Paper

theorem selectedParisiMoment_cdf_intervalIntegrable (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) : IntervalIntegrable
      (fun s => β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s) * parisiCDF ν s)
      volume 0 1 := by
  have hc : ContinuousOn (fun s => β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul ((continuousOn_selectedParisiSecondMoment β h hβ μ).sub continuousOn_id)
  simpa only [mul_comm] using (parisiCDF_monotone ν).intervalIntegrable.mul_continuousOn hc

theorem integral_selectedParisiG_eq_cdf (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) :
    (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) =
      ∫ s in (0 : ℝ)..1, β ^ 2 / 2 *
        (selectedParisiSecondMoment β h hβ μ s - s) * parisiCDF ν s := by
  exact parisiG_integral_eq_cdf β (selectedParisiSecondMoment β h hβ μ)
    (continuousOn_selectedParisiSecondMoment β h hβ μ) ν

/-- The actual signed G pairing is precisely the CDF first variation,
with no stochastic moment or measure-continuity hypotheses. -/
theorem integral_selectedParisiG_sub_eq_cdf (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) :
    (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
      (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap)) =
      β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, (parisiCDF ν s - parisiCDF μ s) *
        (selectedParisiSecondMoment β h hβ μ s - s)) := by
  rw [integral_selectedParisiG_eq_cdf β h hβ μ ν, integral_selectedParisiG_eq_cdf β h hβ μ μ,
    ← intervalIntegral.integral_sub
      (selectedParisiMoment_cdf_intervalIntegrable β h hβ μ ν)
      (selectedParisiMoment_cdf_intervalIntegrable β h hβ μ μ),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

theorem integral_selectedParisiG_sub_eq_moment_correction (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) :
    (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
      (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap)) =
      β ^ 2 / 2 * (∫ s in (0 : ℝ)..1,
        (parisiCDF ν s - parisiCDF μ s) * selectedParisiSecondMoment β h hβ μ s) -
      β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
        (∫ s in (0 : ℝ)..1, s * parisiCDF μ s)) := by
  have hm : IntervalIntegrable
      (fun s => (parisiCDF ν s - parisiCDF μ s) * selectedParisiSecondMoment β h hβ μ s)
      volume 0 1 :=
    ((parisiCDF_monotone ν).intervalIntegrable.sub (parisiCDF_monotone μ).intervalIntegrable).mul_continuousOn
      (by simpa only [uIcc_of_le zero_le_one] using continuousOn_selectedParisiSecondMoment β h hβ μ)
  have hc : IntervalIntegrable (fun s => (parisiCDF ν s - parisiCDF μ s) * s) volume 0 1 :=
    ((parisiCDF_monotone ν).intervalIntegrable.sub (parisiCDF_monotone μ).intervalIntegrable).mul_continuousOn
      continuousOn_id
  rw [integral_selectedParisiG_sub_eq_cdf]
  have he : (fun s => (parisiCDF ν s - parisiCDF μ s) *
      (selectedParisiSecondMoment β h hβ μ s - s)) =
      fun s => (parisiCDF ν s - parisiCDF μ s) * selectedParisiSecondMoment β h hβ μ s -
        (parisiCDF ν s - parisiCDF μ s) * s := by funext s; ring
  rw [he, intervalIntegral.integral_sub hm hc]
  have hec : (∫ s in (0 : ℝ)..1, (parisiCDF ν s - parisiCDF μ s) * s) =
      (∫ s in (0 : ℝ)..1, s * parisiCDF ν s) - (∫ s in (0 : ℝ)..1, s * parisiCDF μ s) := by
    rw [← intervalIntegral.integral_sub (parisiCorrection_intervalIntegrable ν 0 1)
      (parisiCorrection_intervalIntegrable μ 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [hec]
  ring

end Paper
