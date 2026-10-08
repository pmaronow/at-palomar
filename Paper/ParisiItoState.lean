module

public import Paper.ParisiBrownianState
public import Paper.DiracShift
public import Paper.ItoStateIntegrability

@[expose] public section

/-! Genuine Itô characteristics of the pathwise constructed Parisi state.
All stochastic premises are proved; the analytic gradient assumptions are
explicit here and are supplied by the constructed PDE in the application. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal ENNReal
namespace Paper

section State
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ 1)
    (hl : ∀ t, LipschitzWith 1 (v t))

theorem boundedDriftItoCharacteristics_canonicalParisiState :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure
      canonicalBrownianFiltration (canonicalParisiItoState β h μ v hv hb hl)
      (canonicalParisiItoDrift β h μ v hv hb hl) (canonicalDiracShiftMartingale β 0) β := by
  refine ⟨continuous_canonicalParisiItoState β h μ v hv hb hl,
    stronglyAdapted_canonicalParisiItoState β h μ v hv hb hl,
    measurable_canonicalParisiItoDrift β h μ v hv hb hl, ?_, ?_, ?_,
    memLp_canonicalDiracShiftMartingale β 0, ?_⟩
  · refine ⟨(β ^ 2).toNNReal, ?_⟩
    intro s ω
    rw [Real.coe_toNNReal _ (sq_nonneg β)]
    exact norm_canonicalParisiItoDrift_le β h μ v hv hb hl s ω
  · intro s ω
    simpa only [canonicalDiracShiftMartingale, zero_add, canonicalBrownian_zero,
      sub_zero] using canonicalParisiItoState_decomposition β h μ v hv hb hl s ω
  · have hF : canonicalBrownianShiftFiltration 0 = canonicalBrownianFiltration := by
      apply Filtration.ext
      funext t
      change canonicalBrownianFiltration (0 + t) = canonicalBrownianFiltration t
      rw [zero_add]
    rw [← hF]
    exact martingale_canonicalDiracShiftMartingale β 0
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale β 0 T r using 1
    ext ω
    simp [integral_const, Measure.real, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul,
      ENNReal.toReal_min, mul_comm]

theorem integrable_canonicalParisiItoState (T : ℝ≥0) :
    Integrable (canonicalParisiItoState β h μ v hv hb hl T) canonicalBrownianMeasure := by
  apply (boundedDriftItoCharacteristics_canonicalParisiState β h μ v hv hb hl).integrable_state
  have he : canonicalParisiItoState β h μ v hv hb hl 0 = fun _ => h :=
    funext (canonicalParisiItoState_zero β h μ v hv hb hl)
  rw [he]
  exact integrable_const h

end State
end Paper
