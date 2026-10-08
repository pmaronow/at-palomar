module

public import Paper.DiracStateLaw
public import Paper.ItoExpectation

@[expose] public section

/-! Actual shifted state and martingale characteristics for conditional Itô identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace Paper

def canonicalBrownianFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianSample) :=
  Filtration.natural canonicalBrownian (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)

def canonicalBrownianShiftFiltration (a : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianSample) :=
  monotoneReindexFiltration canonicalBrownianFiltration (fun s => a + s)
    (fun _ _ h => add_le_add le_rfl h)

def canonicalDiracShiftState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (a : ℝ≥0)
    (s : ℝ≥0) (ω : BrownianSample) : ℝ := canonicalDiracItoState β h q hq (a + s) ω

def canonicalDiracShiftDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (a : ℝ≥0)
    (s : ℝ≥0) (ω : BrownianSample) : ℝ := canonicalDiracItoDrift β h q hq (a + s) ω

def canonicalDiracShiftMartingale (β : ℝ) (a : ℝ≥0)
    (s : ℝ≥0) (ω : BrownianSample) : ℝ := β * (canonicalBrownian (a + s) ω - canonicalBrownian a ω)

theorem continuous_canonicalDiracShiftState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a : ℝ≥0) (ω : BrownianSample) : Continuous (fun s => canonicalDiracShiftState β h q hq a s ω) :=
  (continuous_canonicalDiracItoState β h q hq ω).comp (continuous_const.add continuous_id)

theorem stronglyAdapted_canonicalDiracShiftState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a : ℝ≥0) : StronglyAdapted (canonicalBrownianShiftFiltration a)
      (canonicalDiracShiftState β h q hq a) :=
  fun s => stronglyAdapted_canonicalDiracItoState β h q hq (a + s)

theorem measurable_canonicalDiracShiftDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a : ℝ≥0) : Measurable (Function.uncurry (canonicalDiracShiftDrift β h q hq a)) :=
  (measurable_canonicalDiracItoDrift β h q hq).comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)

theorem norm_canonicalDiracShiftDrift_le (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a s : ℝ≥0) (ω : BrownianSample) : ‖canonicalDiracShiftDrift β h q hq a s ω‖ ≤ β ^ 2 :=
  norm_canonicalDiracItoDrift_le β h q hq (a + s) ω

theorem integrableOn_canonicalDiracShiftDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a : ℝ≥0) (T : ℝ) (ω : BrownianSample) :
    IntegrableOn (fun s : ℝ => canonicalDiracShiftDrift β h q hq a s.toNNReal ω) (Icc 0 T) := by
  apply (integrableOn_const (isCompact_Icc.measure_ne_top) (C := β ^ 2)).mono'
  · exact ((measurable_canonicalDiracShiftDrift β h q hq a).comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with s
    exact norm_canonicalDiracShiftDrift_le β h q hq a s.toNNReal ω

/-- Shifted Brownian increments remain a martingale in the shifted original
filtration, which retains all information known at the shift time. -/
theorem martingale_canonicalDiracShiftMartingale (β : ℝ) (a : ℝ≥0) :
    Martingale (canonicalDiracShiftMartingale β a)
      (canonicalBrownianShiftFiltration a) canonicalBrownianMeasure := by
  have hB := martingale_brownian_natural isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
  have hshift := martingale_comp_monotone hB (fun s => a + s)
    (fun _ _ h => add_le_add le_rfl h)
  have hconst : Martingale (fun _ : ℝ≥0 => canonicalBrownian a)
      (canonicalBrownianShiftFiltration a) canonicalBrownianMeasure := by
    apply martingale_const_fun
    · change StronglyMeasurable[canonicalBrownianFiltration (a + 0)] (canonicalBrownian a)
      rw [add_zero]
      exact Filtration.stronglyAdapted_natural
        (fun t => (measurable_canonicalBrownian t).stronglyMeasurable) a
    · exact isBrownianReal_canonicalBrownian.toIsPreBrownianReal.integrable_eval a
  exact (hshift.sub hconst).smul β

theorem memLp_canonicalDiracShiftMartingale (β : ℝ) (a s : ℝ≥0) :
    MemLp (canonicalDiracShiftMartingale β a s) 2 canonicalBrownianMeasure :=
  ((isBrownianReal_canonicalBrownian.toIsPreBrownianReal.shift a).isGaussianProcess.hasGaussianLaw_eval s).memLp_two.const_mul β

theorem quadraticVariation_canonicalDiracShiftMartingale (β : ℝ) (a : ℝ≥0) :
    HasQuadraticVariationBeforeStopProcessInProbability (canonicalDiracShiftMartingale β a)
      (fun s _ => β ^ 2 * (s : ℝ)) canonicalBrownianMeasure :=
  (hasQuadraticVariationBeforeStop_preBrownianReal
    (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.shift a)).const_mul β

/-- Time translation of the actual finite-variation contribution. -/
theorem integratedDrift_canonicalDiracShiftDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a s : ℝ≥0) (ω : BrownianSample) :
    integratedDrift (canonicalDiracShiftDrift β h q hq a) s ω =
      integratedDrift (canonicalDiracItoDrift β h q hq) (a + s) ω -
        integratedDrift (canonicalDiracItoDrift β h q hq) a ω := by
  let d : ℝ → ℝ := fun r => canonicalDiracItoDrift β h q hq r.toNNReal ω
  have hint (r : ℝ≥0) : integratedDrift (canonicalDiracItoDrift β h q hq) r ω =
      ∫ u in (0 : ℝ)..(r : ℝ), d u := by
    rw [integratedDrift, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le r.coe_nonneg]
  have hshift : integratedDrift (canonicalDiracShiftDrift β h q hq a) s ω =
      ∫ u in (0 : ℝ)..(s : ℝ), d ((a : ℝ) + u) := by
    rw [integratedDrift, intervalIntegral.integral_of_le s.coe_nonneg,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp [canonicalDiracShiftDrift, d]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal u hu.1,
      Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hu.1)]
  rw [hshift, intervalIntegral.integral_comp_add_left, hint, hint]
  simp only [add_zero, NNReal.coe_add]
  have hInt : IntervalIntegrable d volume 0 ((a : ℝ) + s) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)]
    exact integrableOn_canonicalDiracItoDrift β h q hq (a + s) ω
  have hIntA : IntervalIntegrable d volume 0 (a : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le a.coe_nonneg]
    exact integrableOn_canonicalDiracItoDrift β h q hq a ω
  exact (intervalIntegral.integral_interval_sub_left hInt hIntA).symm

/-- Actual characteristic decomposition after any deterministic shift. -/
theorem canonicalDiracShiftState_decomposition (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a s : ℝ≥0) (ω : BrownianSample) :
    canonicalDiracShiftState β h q hq a s ω = canonicalDiracShiftState β h q hq a 0 ω +
      integratedDrift (canonicalDiracShiftDrift β h q hq a) s ω +
      canonicalDiracShiftMartingale β a s ω := by
  rw [integratedDrift_canonicalDiracShiftDrift]
  dsimp [canonicalDiracShiftState, canonicalDiracShiftMartingale]
  rw [add_zero]
  have hs := canonicalDiracItoState_decomposition β h q hq (a + s) ω
  have ha := canonicalDiracItoState_decomposition β h q hq a ω
  linarith

/-- Every stochastic characteristic in the generic conditional Itô theorem
is discharged by the actual shifted Brownian-driven state. -/
theorem boundedDriftItoCharacteristics_canonicalDiracShift
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (a : ℝ≥0) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure
      (canonicalBrownianShiftFiltration a) (canonicalDiracShiftState β h q hq a)
      (canonicalDiracShiftDrift β h q hq a) (canonicalDiracShiftMartingale β a) β := by
  refine ⟨continuous_canonicalDiracShiftState β h q hq a,
    stronglyAdapted_canonicalDiracShiftState β h q hq a,
    measurable_canonicalDiracShiftDrift β h q hq a, ?_,
    canonicalDiracShiftState_decomposition β h q hq a,
    martingale_canonicalDiracShiftMartingale β a,
    memLp_canonicalDiracShiftMartingale β a, ?_⟩
  · refine ⟨(β ^ 2).toNNReal, ?_⟩
    intro s ω
    rw [Real.coe_toNNReal _ (sq_nonneg β)]
    exact norm_canonicalDiracShiftDrift_le β h q hq a s ω
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale β a T r using 1
    ext ω
    simp [integral_const, Measure.real, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul,
      ENNReal.toReal_min, mul_comm]

end Paper
