module

public import Paper.ParisiWeakWellPosed
public import Paper.ParisiTimeRegularity

@[expose] public section

/-! # Proposition 2.1: the complete general-measure weak PDE theorem -/

open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

namespace Paper

/-- The paper's complete weak well-posedness and regularity statement,
expressed using the actual constructed potential and actual derivatives. -/
structure ParisiPDEWellPosedTarget (β : ℝ) (μ : ParisiMeasure) : Prop where
  unique_weak_potential : ∃! U : ParisiPotentialSpace, IsParisiWeakPotential β μ U
  selected_weak_solution : IsParisiWeakSolution β μ (parisiPotential β μ) (parisiGradient β μ)
  positive_spatial_orders : ∀ n : ℕ,
    Continuous (fun p : Icc (0 : ℝ) 1 × ℝ =>
      iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2) ∧
    ∃ M : ℝ, ∀ p : Icc (0 : ℝ) 1 × ℝ,
      ‖iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2‖ ≤ M
  all_weak_time_orders : ∀ n : ℕ, ∃ w : ℝ × ℝ → ℝ, Measurable w ∧
    (∃ M : ℝ, ∀ p, ‖w p‖ ≤ M) ∧ IsParisiWeakTimeDerivative
      (fun p => iteratedDeriv n (fun y => parisiPotential β μ (p.1, y)) p.2) w
  sharp_gradient_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    ‖iteratedDeriv 1 (fun y => parisiPotential β μ (t, y)) x‖ ≤ 1
  sharp_hessian_bounds : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    0 < iteratedDeriv 2 (fun y => parisiPotential β μ (t, y)) x ∧
      iteratedDeriv 2 (fun y => parisiPotential β μ (t, y)) x ≤ 1

/-- The complete Proposition 2.1 for every actual probability measure.
The weak class, spatial bounds, and time derivative regularity are all
proved properties; no supplied PDE solution or analytic hypothesis remains. -/
theorem parisiPDE_wellPosed (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ParisiPDEWellPosedTarget β μ := by
  refine ⟨exists_unique_parisiWeakPotential β hβ μ,
    parisiPotential_isWeakSolution β hβ μ,
    parisiSpatialDerivatives_continuous_bounded β μ,
    parisiPotential_all_weakTimeDerivatives_bounded β hβ μ, ?_, ?_⟩
  · intro t ht x
    rw [iteratedDeriv_parisiPotential_eq_gradient β μ 0 t x ht, iteratedDeriv_zero]
    exact norm_parisiGradient_le_one β μ (t, x)
  · intro t ht x
    have he : iteratedDeriv 2 (fun y => parisiPotential β μ (t, y)) x =
        parisiHessian β μ (t, x) := by
      simpa only [iteratedDeriv_one, parisiHessian] using
        iteratedDeriv_parisiPotential_eq_gradient β μ 1 t x ht
    rw [he]
    exact ⟨parisiHessian_pos β hβ μ t x ht, parisiHessian_le_one β hβ μ (t, x)⟩

end Paper
