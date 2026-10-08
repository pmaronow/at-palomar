module

public import Paper.ParisiHJB

@[expose] public section

/-! Identifying the verified optimizer with the feedback used in actual
measure-mixing state stability, including the zero-temperature case. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper

@[simp] theorem selectedParisiControl_eq_feedback (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    selectedParisiControl β h hβ μ = selectedParisiFeedbackControl β h μ := rfl

/-- The actual optimizer used by state-stability is the verified optimizer
for every parameter, without choosing an extra control. -/
theorem parisiControlObjective_feedback_eq_potential (β h : ℝ) (μ : ParisiMeasure) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1)
      (selectedParisiFeedbackControl β h μ) μ = parisiPotential β μ (0, h) := by
  by_cases hβ : β = 0
  · subst β
    simp [parisiControlObjective, parisiControlPayoff, parisiControlDrift,
      parisiControlCost, parisiPotential_zero]
  · rw [← selectedParisiControl_eq_feedback β h hβ μ]
    exact parisiControlObjective_selected_eq_potential β h hβ μ

end Paper
