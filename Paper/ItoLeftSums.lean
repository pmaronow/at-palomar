module

public import Paper.ItoExpectation

@[expose] public section

/-! # Identifying the actual stochastic term by Brownian left sums -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology

namespace Paper

/-- The stochastic remainder in Itô's formula is the actual limit in
probability of the adapted martingale left sums. -/
theorem ito_stochastic_leftSums_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformAdaptedMartingaleLeftSumProcess J
      (fun s ω => itoSpaceDerivative f s (X s ω)) t (n + 1) t) atTop
      (fun ω => f t (X t ω) - f 0 (X 0 ω) - generalItoTimeIntegral f X t ω -
        itoDriftIntegral X μ f t ω - generalItoQuadraticIntegral f X
          (fun _ _ => β) t ω) := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  have hXmeas (s : ℝ≥0) : AEStronglyMeasurable (X s) P :=
    ((hc.adapted_state s).mono (V.le s)).aestronglyMeasurable
  have hJmeas (s : ℝ≥0) : AEStronglyMeasurable (J s) P :=
    ((hc.martingale.stronglyAdapted s).mono (V.le s)).aestronglyMeasurable
  have hmuInt (T : ℝ) (ω : Ω) : IntegrableOn
      (fun s : ℝ => μ s.toNNReal ω) (Set.Icc 0 T) := by
    apply (integrableOn_const isCompact_Icc.measure_lt_top.ne (C := (D : ℝ))).mono'
    · exact (hc.measurable_drift.comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards with s
      exact hD s.toNNReal ω
  have hmod : IsContinuousProcessModification X X P :=
    ⟨fun _ => EventuallyEq.rfl, Eventually.of_forall hc.continuous_state⟩
  have hσint (T : ℝ≥0) : ∀ᵐ ω ∂P, IntegrableOn (fun _ : ℝ≥0 => β ^ 2)
      (Set.Ioc 0 T) nonnegativeLebesgueMeasure :=
    Eventually.of_forall fun _ =>
      integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)
  obtain ⟨I, hI, hformula⟩ := exists_ito_formula_of_characteristics X μ
    (fun _ _ => β) J X hXmeas hJmeas hc.measurable_drift hmuInt hmod
    (fun s => Eventually.of_forall (hc.decomposition s)) hc.quadratic_variation hσint
    f hf htdiff hslice hdt hdx hsecond t
  have hconv := hI.sub_real_noMeas (itoDriftApprox_tendstoInMeasure hc f hdx t)
  have hleft (n : ℕ) (ω : Ω) :
      generalItoSpaceApprox f X t (n + 1) ω - itoDriftApprox X μ f t (n + 1) ω =
        uniformAdaptedMartingaleLeftSumProcess J
          (fun s ω => itoSpaceDerivative f s (X s ω)) t (n + 1) t ω := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
    unfold generalItoSpaceApprox itoDriftApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc.decomposition (uniformPartitionTime t (n + 1) (i + 1)) ω,
      hc.decomposition (uniformPartitionTime t (n + 1) i) ω]
    ring
  have hconv' := hconv.congr_left (fun n => Eventually.of_forall (hleft n))
  apply TendstoInMeasure.congr_right _ hconv'
  filter_upwards [hformula] with ω hω
  linarith

end Paper
