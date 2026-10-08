module

public import Paper.ParisiWeakPotentialSpace
public import Paper.BoundedHeatGradientContinuity

@[expose] public section

/-! # Well-posedness in the paper's original weak solution class

Every continuous potential with a bounded measurable distributional spatial
gradient and the actual terminal tested equation equals the constructed
Parisi potential on the closed strip. Its gradient agrees almost everywhere
with the actual continuous mild gradient. Literal uniqueness is stated for
continuous maps on the strip, whose values are exactly the specified data.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem IsParisiWeakSolution.eq_parisiPotential_and_gradient
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0) :
    (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, u p = parisiPotential β μ p) ∧
      v =ᵐ[parisiSpaceTime] parisiGradient β μ := by
  obtain ⟨R, w, _, hw, hb, he, huvw⟩ := huv.exists_bounded_measurable_representative
  have hG : ContinuousOn (boundedVolterraGradient β (parisiNonlinearity μ w))
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
    have hs : (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) =
        {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1} := by ext p; simp
    rw [hs]
    exact continuousOn_boundedVolterraGradient β hβ (parisiNonlinearity μ w)
      (parisiNonlinearity_measurable μ w hw) (R ^ 2) (norm_parisiNonlinearity_le μ w R hb)
  obtain ⟨hu, hg⟩ := huvw.eq_selected_of_gradientSourceContinuous hβ hw R hb hG
  exact ⟨hu, he.trans hg⟩

theorem IsParisiWeakSolution.eq_parisiPotential
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, u p = parisiPotential β μ p :=
  (huv.eq_parisiPotential_and_gradient hβ).1

theorem IsParisiWeakSolution.gradient_ae_eq_parisiGradient
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0) :
    v =ᵐ[parisiSpaceTime] parisiGradient β μ :=
  (huv.eq_parisiPotential_and_gradient hβ).2

/-- Full uniqueness for arbitrary members of the original weak class,
including gradients that are merely almost-everywhere measurable and bounded. -/
theorem parisiWeakSolution_unique (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (u U v V : ℝ × ℝ → ℝ)
    (huv : IsParisiWeakSolution β μ u v) (hUV : IsParisiWeakSolution β μ U V) :
    (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, u p = U p) ∧ v =ᵐ[parisiSpaceTime] V := by
  obtain ⟨hu, hv⟩ := huv.eq_parisiPotential_and_gradient hβ
  obtain ⟨hU, hV⟩ := hUV.eq_parisiPotential_and_gradient hβ
  exact ⟨fun p hp => (hu p hp).trans (hU p hp).symm, hv.trans hV.symm⟩

/-- Existence and literal uniqueness of the continuous weak potential
on the specified closed time strip. No extra growth, differentiability,
source regularity, or mild-equation premise is assumed. -/
theorem exists_unique_parisiWeakPotential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ∃! U : ParisiPotentialSpace, IsParisiWeakPotential β μ U := by
  refine ⟨parisiPotentialOnStrip β μ, parisiPotentialOnStrip_isWeakPotential β hβ μ, ?_⟩
  intro U hU
  obtain ⟨v, huv⟩ := hU
  exact parisiPotentialOnStrip_eq_of_strip_eq β μ U (huv.eq_parisiPotential hβ)

end Paper
