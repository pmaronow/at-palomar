module

public import Paper.ParisiGradientTerminalPairing

@[expose] public section

/-! # Genuine martingale law for the constructed general Parisi gradient

The weighted terminal identity implies actual conditional expectations by
uniqueness on every past-measurable event, and hence a Mathlib martingale.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper

def selectedParisiGradientProcess (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  parisiGradient β μ (t, selectedParisiItoState β h hβ μ t ω)

lemma stronglyAdapted_selectedParisiGradientProcess (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    StronglyAdapted canonicalBrownianFiltration (selectedParisiGradientProcess β h hβ μ) := by
  intro t
  exact (continuous_parisiGradient β μ).comp_stronglyMeasurable
    (stronglyMeasurable_const.prodMk
      (stronglyAdapted_canonicalParisiItoState β h μ _ _ _ _ t))

lemma integrable_selectedParisiGradientProcess (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) : Integrable (selectedParisiGradientProcess β h hβ μ t) canonicalBrownianMeasure :=
  (integrable_const (1 : ℝ)).mono'
    (((stronglyAdapted_selectedParisiGradientProcess β h hβ μ t).mono
      (canonicalBrownianFiltration.le t)).aestronglyMeasurable)
    (.of_forall fun ω => norm_parisiGradient_le_one β μ
      (t, selectedParisiItoState β h hβ μ t ω))

private lemma integral_gradient_indicator (A : Set BrownianSample) (hA : MeasurableSet A)
    (f : BrownianSample → ℝ) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * f ω ∂canonicalBrownianMeasure) =
      ∫ ω in A, f ω ∂canonicalBrownianMeasure := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω]

/-- Every actual future gradient has conditional expectation equal to the
actual present gradient in the original Brownian past filtration. -/
theorem condExp_selectedParisiGradientProcess
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (s t : ℝ≥0)
    (hst : s ≤ t) (ht : (t : ℝ) ≤ 1) :
    canonicalBrownianMeasure[selectedParisiGradientProcess β h hβ μ t |
      canonicalBrownianFiltration s] =ᵐ[canonicalBrownianMeasure]
      selectedParisiGradientProcess β h hβ μ s := by
  have hs : (s : ℝ) ≤ 1 := (NNReal.coe_le_coe.mpr hst).trans ht
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (canonicalBrownianFiltration.le s)
    (integrable_selectedParisiGradientProcess β h hβ μ t)
  · intro A hA hfinite
    exact (integrable_selectedParisiGradientProcess β h hβ μ s).integrableOn
  · intro A hA hfinite
    let Z : BrownianSample → ℝ := A.indicator (fun _ => (1 : ℝ))
    have hZ : StronglyMeasurable[canonicalBrownianFiltration s] Z :=
      stronglyMeasurable_const.indicator hA
    have hZt : StronglyMeasurable[canonicalBrownianFiltration t] Z :=
      hZ.mono (canonicalBrownianFiltration.mono hst)
    have hZb : ∀ ω, ‖Z ω‖ ≤ 1 := by
      intro ω
      dsimp only [Z]
      by_cases hω : ω ∈ A <;> simp [hω]
    have hs' := selectedParisiGradient_terminal_weighted_expectation β h hβ μ s hs Z hZ hZb
    have ht' := selectedParisiGradient_terminal_weighted_expectation β h hβ μ t ht Z hZt hZb
    have he := hs'.symm.trans ht'
    have hAg : MeasurableSet A := (canonicalBrownianFiltration.le s) A hA
    simpa only [Z, selectedParisiGradientProcess,
      integral_gradient_indicator A hAg] using he
  · exact (stronglyAdapted_selectedParisiGradientProcess β h hβ μ s).aestronglyMeasurable

/-- The genuinely constructed optimal gradient is a Mathlib martingale on
all physical times, including both endpoints and arbitrary CDF atoms. -/
theorem martingale_selectedParisiGradient
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Martingale (fun (t : Icc (0 : ℝ≥0) 1) ω => selectedParisiGradientProcess β h hβ μ t.1 ω)
      (monotoneReindexFiltration canonicalBrownianFiltration
        (fun t : Icc (0 : ℝ≥0) 1 => t.1) (fun _ _ h => h)) canonicalBrownianMeasure := by
  refine ⟨fun t => stronglyAdapted_selectedParisiGradientProcess β h hβ μ t.1, ?_⟩
  intro s t hst
  exact condExp_selectedParisiGradientProcess β h hβ μ s.1 t.1 hst
    (NNReal.coe_le_coe.mpr t.2.2)

end Paper
