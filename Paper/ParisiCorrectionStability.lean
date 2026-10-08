module

public import Paper.ParisiCDFGrid

@[expose] public section

/-! # Stability of the actual Parisi correction in CDF distance -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem parisiCorrection_integral_sub_le (μ ν : ParisiMeasure) :
    ‖(∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
        (∫ s in (0 : ℝ)..1, s * parisiCDF ν s)‖ ≤ parisiCDFDistance μ ν := by
  have hi := parisiCorrection_intervalIntegrable μ 0 1
  have hj := parisiCorrection_intervalIntegrable ν 0 1
  have hn : IntervalIntegrable (fun s => ‖parisiCDF μ s - parisiCDF ν s‖)
      volume (0 : ℝ) 1 :=
    ((parisiCDF_monotone μ).intervalIntegrable.sub
      (parisiCDF_monotone ν).intervalIntegrable).norm
  rw [← intervalIntegral.integral_sub hi hj]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun s hs => ?_) hn
  have hsnorm : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1.le]
    exact hs.2
  rw [← mul_sub, norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsnorm
    (norm_nonneg (parisiCDF μ s - parisiCDF ν s))

theorem parisiCorrection_sub_le (β : ℝ) (μ ν : ParisiMeasure) :
    ‖β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s) -
        β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF ν s)‖ ≤
      β ^ 2 / 2 * parisiCDFDistance μ ν := by
  rw [← mul_sub, norm_mul,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  exact mul_le_mul_of_nonneg_left (parisiCorrection_integral_sub_le μ ν) (by positivity)

/-- The finite-grid correction converges to the actual probability-measure
correction, with the same CDF mesh as the PDE approximation. -/
theorem tendsto_parisiCorrection_grid (β : ℝ) (μ : ParisiMeasure) :
    Tendsto (fun n => β ^ 2 / 2 *
      (∫ s in (0 : ℝ)..1, s * parisiCDF (parisiGridMeasure μ n) s)) atTop
      (𝓝 (β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ n, ‖β ^ 2 / 2 *
      (∫ s in (0 : ℝ)..1, s * parisiCDF (parisiGridMeasure μ n) s) -
        β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s)‖ ≤
      β ^ 2 / 2 * parisiCDFDistance μ (parisiGridMeasure μ n) := by
    intro n
    rw [norm_sub_rev]
    exact parisiCorrection_sub_le β μ (parisiGridMeasure μ n)
  have hlim : Tendsto (fun n => β ^ 2 / 2 * parisiCDFDistance μ (parisiGridMeasure μ n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_parisiCDFDistance_grid μ)
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

end Paper
