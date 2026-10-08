module

public import Paper.ParisiMeasureStability
public import Paper.ParisiCDFGrid
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Actual atomic-grid convergence of the local Parisi solution -/

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

/-- The actual grid probability measures give uniform convergence of the
corresponding genuine local Duhamel fixed points. -/
theorem tendsto_localParisiGradient_grid (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (w : ℕ → ParisiSlabGradient a b) (hwnorm : ∀ n, ‖w n‖ ≤ 2)
    (hw : ∀ n, parisiSlabGradientOperator β (parisiGridMeasure μ n) hab g hg hgb (w n) = w n) :
    Tendsto w atTop (𝓝 v) := by
  have hδ : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have herr : Tendsto (fun n : ℕ =>
      12 * |β| * gaussianAbsMoment * Real.sqrt (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero] using tendsto_const_nhds.mul hδ.sqrt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herr.eventually (eventually_lt_nhds hε)] with n hn
  have hdist := localParisiGradient_measure_mesh_stability β μ (parisiGridMeasure μ n)
    hab ha hb g hg hgb hshort v (w n) hvnorm (hwnorm n) hv (hw n)
    (1 / ((n + 1 : ℕ) : ℝ)) (by positivity) (parisiCDF_grid_norm_integral_le μ n)
  rw [dist_eq_norm, norm_sub_rev]
  exact hdist.trans_lt hn

/-- The sharp bound for the actual general-measure local gradient follows
from the actual atomic-grid local gradients and their genuine equations. -/
theorem localParisiGradient_norm_le_one_of_grid (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (w : ℕ → ParisiSlabGradient a b) (hwunit : ∀ n, ‖w n‖ ≤ 1)
    (hw : ∀ n, parisiSlabGradientOperator β (parisiGridMeasure μ n) hab g hg hgb (w n) = w n) :
    ‖v‖ ≤ 1 := by
  apply localParisiGradient_norm_le_one_of_mesh_approximants β μ hab ha hb g hg hgb hshort
    v hvnorm hv (parisiGridMeasure μ) w hwunit hw (fun n => 1 / ((n + 1 : ℕ) : ℝ))
  · intro n
    positivity
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact parisiCDF_grid_norm_integral_le μ

end Paper
