module

public import Targets.Section5FarRight
public import Targets.Section5LeftUniform

@[expose] public section

/-!
# A common positive accuracy for Section 5

Continuity at zero supplies a positive near-optimality tolerance satisfying
both the sixth-root curvature condition and the square-root far-overlap
condition. Its choice depends only on beta and the terminal time, not the
scheme, physical level, overlap, system size or disorder.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Both quantitative Section 5 smallness conditions can be met by one
strictly positive accuracy, before any scheme is chosen. -/
theorem exists_section5_common_accuracy (β : ℝ) (hβ : β ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ),
      section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀ ∧
      section5FarLeftBound β * Real.sqrt ε ≤
        (1 - t₀) * (β ^ 2 / 2) *
          ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2 := by
  have hL : 0 < section5LocalLeftConstant β 535 :=
    section5LocalLeftConstant_pos β 535 (by norm_num)
  have hB : 0 < (1 - t₀) * (β ^ 2 / 2) *
      ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2 :=
    mul_pos (mul_pos (sub_pos.mpr ht₀)
      (div_pos (sq_pos_of_ne_zero hβ) (by norm_num)))
      (sq_pos_of_pos (div_pos (sub_pos.mpr ht₀) hL))
  have hc₁ : ContinuousAt
      (fun e : ℝ => section5LocalLeftConstant β 535 * e ^ (1 / 6 : ℝ)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (1 / 6) (by norm_num))
  have hc₂ : ContinuousAt
      (fun e : ℝ => section5FarLeftBound β * Real.sqrt e) 0 :=
    continuousAt_const.mul Real.continuous_sqrt.continuousAt
  have he₁ : ∀ᶠ e : ℝ in 𝓝 0,
      section5LocalLeftConstant β 535 * e ^ (1 / 6 : ℝ) < 1 - t₀ :=
    hc₁.eventually (gt_mem_nhds (by simpa using sub_pos.mpr ht₀))
  have he₂ : ∀ᶠ e : ℝ in 𝓝 0,
      section5FarLeftBound β * Real.sqrt e <
        (1 - t₀) * (β ^ 2 / 2) *
          ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2 :=
    hc₂.eventually (gt_mem_nhds (by simpa using hB))
  obtain ⟨a, ha, H⟩ := Metric.eventually_nhds_iff.mp (he₁.and he₂)
  have hmem : dist (a / 2) (0 : ℝ) < a := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos ha)]
    exact half_lt_self ha
  exact ⟨a / 2, half_pos ha, (H hmem).1.le, (H hmem).2.le⟩

end SpinGlass.Targets
