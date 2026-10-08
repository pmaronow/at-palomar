module

public import Paper.ParisiHJBBase

@[expose] public section

/-! Passing verified rounded-grid payoff estimates to the actual PDE selector.
Both error sequences here are the already-constructed analytic approximation
errors, not assumed small parameters. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

/-- The verified grid upper bound passes to the actual potential. -/
theorem parisiControlObjective_upper_of_grid (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ)
    (hgrid : ∀ n : ℕ,
      parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ ≤
        parisiFinitePotential (parisiGridRSBScheme μ n) β (0, h) +
          (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure μ n)) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ ≤
      parisiPotential β μ (0, h) := by
  have hu := tendsto_actual_finiteParisiPotential β hβ μ 0 h (by norm_num)
  have he := (tendsto_parisiCDFDistance_grid μ).const_mul ((3 / 2 : ℝ) * β ^ 2)
  have hl := hu.add he
  simp only [mul_zero, add_zero] at hl
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hl (.of_forall hgrid)

/-- The verified optimal grid lower bound passes to the actual potential. -/
theorem parisiControlObjective_lower_of_grid (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ)
    (hgrid : ∀ n : ℕ,
      parisiFinitePotential (parisiGridRSBScheme μ n) β (0, h) -
          (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure μ n) -
          β ^ 2 / 2 * parisiHJBGradientError β μ n ^ 2 ≤
        parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ) :
    parisiPotential β μ (0, h) ≤
      parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ := by
  have hu := tendsto_actual_finiteParisiPotential β hβ μ 0 h (by norm_num)
  have he := (tendsto_parisiCDFDistance_grid μ).const_mul ((3 / 2 : ℝ) * β ^ 2)
  have hg := ((tendsto_parisiHJBGradientError β hβ μ).pow 2).const_mul (β ^ 2 / 2)
  have hl := (hu.sub he).sub hg
  simp only [mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0)] at hl
  exact le_of_tendsto hl (.of_forall hgrid)

end Paper
