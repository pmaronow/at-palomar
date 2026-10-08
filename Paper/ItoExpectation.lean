module

public import Paper.DiracStateLaw

@[expose] public section

/-! # Weighted expectations for bounded-drift Itô characteristics

This generic form permits a random initial value and an initial-filtration
multiplier.  Its stochastic term is centered by actual adapted left sums
and a uniform second-moment bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology

namespace Paper

structure BoundedDriftItoCharacteristics
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X μ J : ℝ≥0 → Ω → ℝ) (β : ℝ) : Prop where
  continuous_state : ∀ ω, Continuous (fun s => X s ω)
  adapted_state : StronglyAdapted V X
  measurable_drift : Measurable (Function.uncurry μ)
  bounded_drift : ∃ D : ℝ≥0, ∀ s ω, ‖μ s ω‖ ≤ D
  decomposition : ∀ s ω, X s ω = X 0 ω + integratedDrift μ s ω + J s ω
  martingale : Martingale J V P
  memLp_two : ∀ s, MemLp (J s) 2 P
  quadratic_variation : ∀ T a, TendstoInMeasure P
    (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a) atTop
    (fun _ : Ω => ∫ _s in Set.Ioc (0 : ℝ≥0) (min T a),
      β ^ 2 ∂nonnegativeLebesgueMeasure)

def itoDriftIntegral {Ω : Type*} (X μ : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoSpaceDerivative f s (X s.toNNReal ω) * μ s.toNNReal ω

def itoDriftApprox {Ω : Type*} (X μ : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoSpaceDerivative f (uniformPartitionTime t n i) (X (uniformPartitionTime t n i) ω) *
      (integratedDrift μ (uniformPartitionTime t n (i + 1)) ω -
        integratedDrift μ (uniformPartitionTime t n i) ω)

theorem itoDriftApprox_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β)
    (f : ℝ → ℝ → ℝ)
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2)) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => itoDriftApprox X μ f t (n + 1)) atTop
      (itoDriftIntegral X μ f t) := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  have hmeas (s : ℝ≥0) : StronglyMeasurable (X s) :=
    (hc.adapted_state s).mono (V.le s)
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    apply StronglyMeasurable.aestronglyMeasurable
    unfold itoDriftApprox
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact (hdx.comp_stronglyMeasurable
      (stronglyMeasurable_const.prodMk (hmeas _))).mul
      ((stronglyMeasurable_integratedDrift hc.measurable_drift _).sub
        (stronglyMeasurable_integratedDrift hc.measurable_drift _))
  · apply Eventually.of_forall
    intro ω
    let d : ℝ≥0 → ℝ := fun s => μ s ω
    let w : ℝ≥0 → ℝ := fun s => itoSpaceDerivative f s (X s ω)
    have hd : IntegrableOn d (Set.Ioc 0 t) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)
        (C := (D : ℝ))).mono'
      · exact (hc.measurable_drift.comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · filter_upwards with s
        exact hD s ω
    have hw : Continuous w := hdx.comp
      (NNReal.continuous_coe.prodMk (hc.continuous_state ω))
    have hl := uniformPartition_weighted_integral_tendsto_signed d w t hd hw
    have hint (r : ℝ≥0) :
        (∫ s in Set.Ioc 0 r, d s ∂nonnegativeLebesgueMeasure) = integratedDrift μ r ω :=
      integral_nonnegative_Ioc_eq_real_Icc μ r ω
    have htarget : (∫ s in Set.Ioc 0 t, w s * d s ∂nonnegativeLebesgueMeasure) =
        itoDriftIntegral X μ f t ω := by
      rw [integral_nonnegative_Ioc_eq_real_Icc
        (fun s ω => itoSpaceDerivative f s (X s ω) * μ s ω) t ω]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      simp only [Real.coe_toNNReal s hs.1]
    simpa only [itoDriftApprox, w, hint, htarget] using hl

/-- A bounded initial-filtration multiplier has zero pairing with the
stochastic term in the genuine Itô formula. -/
theorem ito_centered_weighted_of_boundedDrift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (K : ℝ≥0)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V 0] Z) (C : ℝ≥0)
    (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    ∃ N : Ω → ℝ, Integrable N P ∧ Integrable (fun ω => Z ω * N ω) P ∧
      (∫ ω, Z ω * N ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, f t (X t ω) = f 0 (X 0 ω) + generalItoTimeIntegral f X t ω +
        itoDriftIntegral X μ f t ω + N ω +
        generalItoQuadraticIntegral f X (fun _ _ => β) t ω := by
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
  let H : ℝ≥0 → Ω → ℝ := fun s ω => itoSpaceDerivative f (min s t) (X (min s t) ω)
  have hH : StronglyAdapted V H := by
    intro s
    exact hdx.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk
      ((hc.adapted_state (min s t)).mono (V.mono (min_le_left s t))))
  have hHK (s : ℝ≥0) (ω : Ω) : ‖H s ω‖ ≤ K :=
    hK (min s t) ⟨(min s t).coe_nonneg, NNReal.coe_le_coe.mpr (min_le_right s t)⟩ _
  have hconv := hI.sub_real_noMeas (itoDriftApprox_tendstoInMeasure hc f hdx t)
  have hleft (n : ℕ) (ω : Ω) :
      generalItoSpaceApprox f X t (n + 1) ω - itoDriftApprox X μ f t (n + 1) ω =
        uniformAdaptedMartingaleLeftSumProcess J H t (n + 1) t ω := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
    unfold generalItoSpaceApprox itoDriftApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have htime := (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos n)
      (Nat.le_of_lt (Finset.mem_range.mp hi))).2
    simp only [H, min_eq_left htime,
      min_eq_left (NNReal.coe_le_coe.mpr htime)]
    rw [hc.decomposition (uniformPartitionTime t (n + 1) (i + 1)) ω,
      hc.decomposition (uniformPartitionTime t (n + 1) i) ω]
    ring
  have hconv' : TendstoInMeasure P
      (fun n => uniformAdaptedMartingaleLeftSumProcess J H t (n + 1) t) atTop
      (fun ω => I ω - itoDriftIntegral X μ f t ω) :=
    hconv.congr_left (fun n => Eventually.of_forall (hleft n))
  obtain ⟨hNint, _⟩ := integrable_and_centered_of_bounded_martingale_leftSums
    hc.martingale hc.memLp_two hH K hHK t hconv'
  have hseqMeas (n : ℕ) : AEStronglyMeasurable
      (uniformAdaptedMartingaleLeftSumProcess J H t (n + 1) t) P := by
    have hmart := martingale_uniformAdaptedMartingaleLeftSumProcess
      hc.martingale hH K hHK t (n + 1)
    exact ((hmart.stronglyAdapted t).mono (V.le t)).aestronglyMeasurable
  let HZ : ℝ≥0 → Ω → ℝ := fun s ω => Z ω * H s ω
  have hHZ : StronglyAdapted V HZ := fun s =>
    (hZ.mono (V.mono (bot_le : (0 : ℝ≥0) ≤ s))).mul (hH s)
  have hHZbound (s : ℝ≥0) (ω : Ω) : ‖HZ s ω‖ ≤ C * K := by
    change ‖Z ω * H s ω‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hC ω) (hHK s ω) (norm_nonneg _) C.coe_nonneg
  have hweighted := hconv'.mul_fixed_real hseqMeas ((hZ.mono (V.le 0)).aestronglyMeasurable)
  have hweightedLeft (n : ℕ) (ω : Ω) :
      Z ω * uniformAdaptedMartingaleLeftSumProcess J H t (n + 1) t ω =
        uniformAdaptedMartingaleLeftSumProcess J HZ t (n + 1) t ω := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal,
      uniformAdaptedMartingaleLeftSumProcess_terminal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [HZ]
    ring
  have hwconv := hweighted.congr_left
    (fun n => Eventually.of_forall (hweightedLeft n))
  obtain ⟨hWNint, hWNzero⟩ := integrable_and_centered_of_bounded_martingale_leftSums
    hc.martingale hc.memLp_two hHZ (C * K) hHZbound t hwconv
  refine ⟨_, hNint, hWNint, hWNzero, ?_⟩
  filter_upwards [hformula] with ω hω
  rw [hω]
  ring

/-- A genuine backward equation along the state conserves all bounded
initial-filtration weighted expectations. -/
theorem backward_weighted_expectation_of_boundedDrift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X μ J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X μ J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (K : ℝ≥0)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V 0] Z) (C : ℝ≥0)
    (hC : ∀ ω, ‖Z ω‖ ≤ C)
    (hPDE : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
      itoTimeDerivative f s (X s.toNNReal ω) +
        itoSpaceDerivative f s (X s.toNNReal ω) * μ s.toNNReal ω +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f s (X s.toNNReal ω) * β ^ 2 = 0)
    (hint0 : Integrable (fun ω => Z ω * f 0 (X 0 ω)) P)
    (hintt : Integrable (fun ω => Z ω * f t (X t ω)) P) :
    (∫ ω, Z ω * f t (X t ω) ∂P) = ∫ ω, Z ω * f 0 (X 0 ω) ∂P := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  obtain ⟨N, _hNint, _hZNint, hZNzero, hformula⟩ :=
    ito_centered_weighted_of_boundedDrift hc f hf htdiff hslice hdt hdx hsecond t K hK
      Z hZ C hC
  have hgenerator (ω : Ω) : generalItoTimeIntegral f X t ω +
      itoDriftIntegral X μ f t ω + generalItoQuadraticIntegral f X
        (fun _ _ => β) t ω = 0 := by
    have hpath : Continuous (fun s : ℝ => (s, X s.toNNReal ω)) :=
      continuous_id.prodMk ((hc.continuous_state ω).comp continuous_real_toNNReal)
    have hti := (hdt.comp hpath).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
    have hxi := (hdx.comp hpath).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
    have hdi := hxi.mul_bdd ((hc.measurable_drift.comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun s => hD s.toNNReal ω)
    have hxxi := (((hsecond.comp hpath).const_mul (1 / 2)).mul_const (β ^ 2)).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
    unfold generalItoTimeIntegral itoDriftIntegral generalItoQuadraticIntegral
    rw [← integral_const_mul]
    have hquadratic : (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        (1 / 2 : ℝ) * (itoSpaceSecondDerivative f s (X s.toNNReal ω) * β ^ 2)) =
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f s (X s.toNNReal ω) * β ^ 2 := by
      apply integral_congr_ae
      filter_upwards with s
      ring
    have hsplit := integral_add hti hdi
    have hsplit2 := integral_add (hti.add hdi) hxxi
    simp only [Function.comp_apply, Function.uncurry, Pi.add_apply] at hsplit hsplit2
    rw [hquadratic, ← hsplit, ← hsplit2]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    exact hPDE ω s hs
  have hae : (fun ω => Z ω * f t (X t ω) - Z ω * f 0 (X 0 ω)) =ᵐ[P]
      fun ω => Z ω * N ω := by
    filter_upwards [hformula] with ω hω
    have hg := hgenerator ω
    have he : f t (X t ω) - f 0 (X 0 ω) = N ω := by linarith
    rw [← mul_sub, he]
  have he := (integral_congr_ae hae).trans hZNzero
  rw [integral_sub hintt hint0] at he
  exact sub_eq_zero.mp he

end Paper
