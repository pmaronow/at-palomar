module

public import Paper.ParisiGradientTerminalPairing
public import Paper.ParisiControlEnvelope

@[expose] public section

/-! # Actual general Parisi first variation

The HJB envelope, actual optimal-gradient terminal pairing, and genuine
CDF Fubini formula discharge every analytic and stochastic first-variation
input for the literally constructed PDE functional.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper

/-- The actual first variation on the probability-mixture interval. -/
theorem hasDerivWithinAt_parisiPDEFunctional_mix_G_Icc
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε => parisiPDEFunctional β h (parisiMix μ ν ε))
      ((∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
        ∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap))
      (Icc (0 : ℝ) 1) 0 := by
  have hd := hasDerivWithinAt_parisiPDEFunctional_mix_control β h μ ν
  rw [integral_selectedParisiControlDerivative_sub_correction_of_terminal_pairing β h hβ μ ν
    (fun s hs => selectedParisiFeedbackControl_terminal_pairing β h hβ μ s hs)] at hd
  exact hd

/-- Proposition 2.3's genuine right first derivative in every probability
measure direction, with no supplied PDE, martingale or regularity premise. -/
theorem hasDerivWithinAt_parisiPDEFunctional_mix_G
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε => parisiPDEFunctional β h (parisiMix μ ν ε))
      ((∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
        ∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap))
      (Ioi (0 : ℝ)) 0 :=
  hasDerivWithinAt_right_of_Icc (hasDerivWithinAt_parisiPDEFunctional_mix_G_Icc β h hβ μ ν)

end Paper
