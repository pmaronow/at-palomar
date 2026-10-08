module

public import Paper.ItoExpectation

@[expose] public section

/-! Absolute integrability of a bounded-drift Itô state follows from its
actual characteristic decomposition and the martingale's second moment. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal
namespace Paper

theorem BoundedDriftItoCharacteristics.norm_integratedDrift_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β) (D : ℝ≥0)
    (hD : ∀ s ω, ‖μ s ω‖ ≤ D) (T : ℝ≥0) (ω : Ω) :
    ‖integratedDrift μ T ω‖ ≤ D * (T : ℝ) := by
  rw [integratedDrift, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le T.coe_nonneg]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (C := (D : ℝ))
    (f := fun s => μ s.toNNReal ω) (fun s _ => hD s.toNNReal ω)
  simpa only [sub_zero, abs_of_nonneg T.coe_nonneg] using hn

theorem BoundedDriftItoCharacteristics.integrable_integratedDrift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β) (T : ℝ≥0) :
    Integrable (integratedDrift μ T) P := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  exact (integrable_const ((D : ℝ) * (T : ℝ))).mono'
    (stronglyMeasurable_integratedDrift hc.measurable_drift T).aestronglyMeasurable
    (.of_forall fun ω => hc.norm_integratedDrift_le D hD T ω)

theorem BoundedDriftItoCharacteristics.integrable_state
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β)
    (hi : Integrable (X 0) P) (T : ℝ≥0) : Integrable (X T) P := by
  have hj := (hc.memLp_two T).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact ((hi.add (hc.integrable_integratedDrift T)).add hj).congr
    (.of_forall fun ω => (hc.decomposition T ω).symm)

end Paper
