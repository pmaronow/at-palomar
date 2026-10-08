module

public import Paper.ParisiWeakRegularRecovery
public import Paper.ParisiSolutionUniqueness

@[expose] public section

/-! # Identification of recovered weak potentials with the actual selector -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem IsParisiWeakSolution.eq_selected_of_gradientSourceContinuous
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hG : ContinuousOn (boundedVolterraGradient β (parisiNonlinearity μ v))
      (Icc (0 : ℝ) 1 ×ˢ univ)) :
    (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, u p = parisiPotential β μ p) ∧
      v =ᵐ[parisiSpaceTime] parisiGradient β μ := by
  obtain ⟨g, K, hgc, hgb, hvae, hue, heq⟩ :=
    huv.exists_continuous_mildGradient_of_source_regular hβ hv R hb
      (continuous_boundedVolterraPotential β hβ _ (parisiNonlinearity_measurable μ v hv)
        (R ^ 2) (norm_parisiNonlinearity_le μ v R hb)) hG
  let S := max K 1
  have hgbS : ∀ p, ‖g p‖ ≤ S := fun p => (hgb p).trans (le_max_left K 1)
  have hpbS : ∀ p, ‖parisiGradient β μ p‖ ≤ S := fun p =>
    (norm_parisiGradient_le_one β μ p).trans (le_max_right K 1)
  have hpg := parisiMildGradient_unique β μ Real.tanh g (parisiGradient β μ)
    hgc (continuous_parisiGradient β μ) S hgbS hpbS heq
    (fun t ht x => parisiGradient_equation β μ t x ht)
  have hpu := parisiDuhamelPotential_eq_of_mildGradients β μ Real.tanh g
    (parisiGradient β μ) hgc (continuous_parisiGradient β μ) S hgbS hpbS heq
    (fun t ht x => parisiGradient_equation β μ t x ht)
  constructor
  · intro p hp
    rcases p with ⟨t, x⟩
    rw [hue t hp.1 x, hpu t hp.1 x, parisiPotential_eq_duhamel β μ t x hp.1.2]
  · filter_upwards [hvae, ae_parisiSpaceTime_openStrip] with p hp hs
    exact hp.trans (hpg p.1 ⟨hs.1.le, hs.2.le⟩ p.2)

end Paper
