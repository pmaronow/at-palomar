module

public import Paper.ParisiSelectedState

@[expose] public section

/-! # Actual deterministic-time shifts of the general Parisi state

The shifted filtration retains the whole past. Every Brownian martingale and
quadratic-variation premise is supplied by the concrete canonical process.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace Paper

section State
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ 1)
    (hl : ∀ t, LipschitzWith 1 (v t))

def canonicalParisiShiftState (a s : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalParisiItoState β h μ v hv hb hl (a + s) ω

def canonicalParisiShiftDrift (a s : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalParisiItoDrift β h μ v hv hb hl (a + s) ω

theorem continuous_canonicalParisiShiftState (a : ℝ≥0) (ω : BrownianSample) :
    Continuous (fun s => canonicalParisiShiftState β h μ v hv hb hl a s ω) :=
  (continuous_canonicalParisiItoState β h μ v hv hb hl ω).comp
    (continuous_const.add continuous_id)

theorem stronglyAdapted_canonicalParisiShiftState (a : ℝ≥0) :
    StronglyAdapted (canonicalBrownianShiftFiltration a)
      (canonicalParisiShiftState β h μ v hv hb hl a) :=
  fun s => stronglyAdapted_canonicalParisiItoState β h μ v hv hb hl (a + s)

theorem measurable_canonicalParisiShiftDrift (a : ℝ≥0) :
    Measurable (Function.uncurry (canonicalParisiShiftDrift β h μ v hv hb hl a)) :=
  (measurable_canonicalParisiItoDrift β h μ v hv hb hl).comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)

theorem norm_canonicalParisiShiftDrift_le (a s : ℝ≥0) (ω : BrownianSample) :
    ‖canonicalParisiShiftDrift β h μ v hv hb hl a s ω‖ ≤ β ^ 2 :=
  norm_canonicalParisiItoDrift_le β h μ v hv hb hl (a + s) ω


end State

/-- Time translation of the actual finite-variation contribution. -/
theorem integratedDrift_canonicalParisiShiftDrift (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ 1)
    (hl : ∀ t, LipschitzWith 1 (v t))
    (a s : ℝ≥0) (ω : BrownianSample) :
    integratedDrift (canonicalParisiShiftDrift β h μ v hv hb hl a) s ω =
      integratedDrift (canonicalParisiItoDrift β h μ v hv hb hl) (a + s) ω -
        integratedDrift (canonicalParisiItoDrift β h μ v hv hb hl) a ω := by
  let d : ℝ → ℝ := fun r => canonicalParisiItoDrift β h μ v hv hb hl r.toNNReal ω
  have hint (r : ℝ≥0) : integratedDrift (canonicalParisiItoDrift β h μ v hv hb hl) r ω =
      ∫ u in (0 : ℝ)..(r : ℝ), d u := by
    rw [integratedDrift, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le r.coe_nonneg]
  have hshift : integratedDrift (canonicalParisiShiftDrift β h μ v hv hb hl a) s ω =
      ∫ u in (0 : ℝ)..(s : ℝ), d ((a : ℝ) + u) := by
    rw [integratedDrift, intervalIntegral.integral_of_le s.coe_nonneg,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp [canonicalParisiShiftDrift, d]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal u hu.1,
      Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hu.1)]
  rw [hshift, intervalIntegral.integral_comp_add_left, hint, hint]
  simp only [add_zero, NNReal.coe_add]
  have hInt : IntervalIntegrable d volume 0 ((a : ℝ) + s) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
    exact integrableOn_canonicalParisiItoDrift β h μ v hv hb hl (a + s) ω
  have hIntA : IntervalIntegrable d volume 0 (a : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le a.coe_nonneg]
    exact integrableOn_canonicalParisiItoDrift β h μ v hv hb hl a ω
  exact (intervalIntegral.integral_interval_sub_left hInt hIntA).symm


section State
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ 1)
    (hl : ∀ t, LipschitzWith 1 (v t))

theorem canonicalParisiShiftState_decomposition (a s : ℝ≥0) (ω : BrownianSample) :
    canonicalParisiShiftState β h μ v hv hb hl a s ω =
      canonicalParisiShiftState β h μ v hv hb hl a 0 ω +
      integratedDrift (canonicalParisiShiftDrift β h μ v hv hb hl a) s ω +
      canonicalDiracShiftMartingale β a s ω := by
  rw [integratedDrift_canonicalParisiShiftDrift]
  dsimp [canonicalParisiShiftState, canonicalDiracShiftMartingale]
  rw [add_zero]
  have hs := canonicalParisiItoState_decomposition β h μ v hv hb hl (a + s) ω
  have ha := canonicalParisiItoState_decomposition β h μ v hv hb hl a ω
  linarith

theorem boundedDriftItoCharacteristics_canonicalParisiShift (a : ℝ≥0) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure
      (canonicalBrownianShiftFiltration a) (canonicalParisiShiftState β h μ v hv hb hl a)
      (canonicalParisiShiftDrift β h μ v hv hb hl a) (canonicalDiracShiftMartingale β a) β := by
  refine ⟨continuous_canonicalParisiShiftState β h μ v hv hb hl a,
    stronglyAdapted_canonicalParisiShiftState β h μ v hv hb hl a,
    measurable_canonicalParisiShiftDrift β h μ v hv hb hl a, ?_,
    canonicalParisiShiftState_decomposition β h μ v hv hb hl a,
    martingale_canonicalDiracShiftMartingale β a,
    memLp_canonicalDiracShiftMartingale β a, ?_⟩
  · refine ⟨(β ^ 2).toNNReal, ?_⟩
    intro s ω
    rw [Real.coe_toNNReal _ (sq_nonneg β)]
    exact norm_canonicalParisiShiftDrift_le β h μ v hv hb hl a s ω
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale β a T r using 1
    ext ω
    simp [integral_const, Measure.real, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul,
      ENNReal.toReal_min, mul_comm]

end State
end Paper
