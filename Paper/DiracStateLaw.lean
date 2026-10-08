module

public import Paper.DiracItoState
public import Paper.StateDiffusion
public import Paper.WeightedDrift
public import StochasticCalculus.GirsanovTheorem

@[expose] public section

/-!
# Integrating the actual Dirac state equation

The stochastic integral term is recovered as a limit in probability of
bounded adapted martingale left sums. Its vanishing expectation follows
from a proved uniform second-moment bound and Vitali convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology

namespace Paper

/-- A uniformly `L²` bounded limit in probability of centered random
variables is integrable and centered. -/
theorem integrable_and_centered_of_tendstoInMeasure_uniform_L2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Ω → ℝ} {I : Ω → ℝ}
    (hF : ∀ n, MemLp (F n) 2 P) (C : ℝ≥0)
    (hC : ∀ n, eLpNorm (F n) 2 P ≤ C)
    (hcenter : ∀ n, ∫ ω, F n ω ∂P = 0)
    (hconv : TendstoInMeasure P F atTop I) :
    Integrable I P ∧ (∫ ω, I ω ∂P) = 0 := by
  have hUI := uniformIntegrable_one_of_uniform_eLpNorm_two
    (fun n => (hF n).aestronglyMeasurable) C hC
  have hI : MemLp I 1 P := hUI.memLp_of_tendstoInMeasure hconv
  have hL1 : Tendsto (fun n => eLpNorm (F n - I) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (by simp) (by simp)
      (fun n => (hF n).aestronglyMeasurable) hI hUI.unifIntegrable hconv
  have hint := tendsto_integral_of_L1' I
    (Eventually.of_forall fun n => (hF n).integrable (by norm_num)) hL1
  have hzero : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    simpa only [hcenter] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact ⟨(memLp_one_iff_integrable.mp hI), tendsto_nhds_unique hint hzero⟩

/-- Every bounded adapted martingale left sum has zero expectation. -/
theorem integral_uniformMartingaleLeftSum_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {M H : ℝ≥0 → Ω → ℝ} (hM : Martingale M V P)
    (hH : StronglyAdapted V H) (K : ℝ)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, uniformAdaptedMartingaleLeftSumProcess M H T n T ω ∂P) = 0 := by
  have hmart := martingale_uniformAdaptedMartingaleLeftSumProcess hM hH K hK T n
  have h := hmart.setIntegral_eq (i := 0) (j := T) bot_le MeasurableSet.univ
  simpa [uniformAdaptedMartingaleLeftSumProcess, elementaryMartingaleIntegralSum,
    elementaryMartingaleIntegralProcess, Measure.restrict_univ] using h.symm

/-- Uniformly bounded adapted integrands produce centered stochastic limits.
The conclusion follows from the proved martingale `L²` estimate, rather than
an assumption about the limiting stochastic integral. -/
theorem integrable_and_centered_of_bounded_martingale_leftSums
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {M H : ℝ≥0 → Ω → ℝ} (hM : Martingale M V P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hH : StronglyAdapted V H)
    (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) {I : Ω → ℝ}
    (hconv : TendstoInMeasure P
      (fun n => uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) atTop I) :
    Integrable I P ∧ (∫ ω, I ω ∂P) = 0 := by
  have hfin := ((hM2 T).sub (hM2 0)).eLpNorm_ne_top
  let C : ℝ≥0 := K * (eLpNorm (M T - M 0) 2 P).toNNReal
  have hbound (n : ℕ) :
      eLpNorm (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P ≤ C := by
    simpa only [C, ENNReal.coe_mul, ENNReal.coe_toNNReal hfin] using
      eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le hM hM2 hH K hK T n
  have hL2 (n : ℕ) : MemLp
      (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P := by
    exact lt_of_le_of_lt (hbound n) ENNReal.coe_lt_top
  exact integrable_and_centered_of_tendstoInMeasure_uniform_L2 hL2 C hbound
    (fun n => integral_uniformMartingaleLeftSum_eq_zero hM hH K hK T (n + 1)) hconv

/-- The actual canonical Dirac state admits the genuine Itô formula.
All stochastic characteristics are proved for the constructed Brownian state;
only the usual regularity of the deterministic test function is required. -/
theorem canonicalDiracItoState_ito
    (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∃ I : BrownianSample → ℝ,
      TendstoInMeasure canonicalBrownianMeasure
        (fun n => generalItoSpaceApprox f (canonicalDiracItoState β h q hq)
          t (n + 1)) atTop I ∧
      ∀ᵐ ω ∂canonicalBrownianMeasure,
        f t (canonicalDiracItoState β h q hq t ω) = f 0 h +
          generalItoTimeIntegral f (canonicalDiracItoState β h q hq) t ω + I ω +
          generalItoQuadraticIntegral f (canonicalDiracItoState β h q hq)
            (fun _ _ => β) t ω := by
  have hmeas (s : ℝ≥0) : AEStronglyMeasurable (canonicalDiracItoState β h q hq s)
      canonicalBrownianMeasure :=
    (((stronglyAdapted_canonicalDiracItoState β h q hq s).mono
      ((Filtration.natural canonicalBrownian
        (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)).le s))).aestronglyMeasurable
  have hJmeas (s : ℝ≥0) : AEStronglyMeasurable (fun ω => β * canonicalBrownian s ω)
      canonicalBrownianMeasure := (measurable_canonicalBrownian s).aestronglyMeasurable.const_mul β
  have hmod : IsContinuousProcessModification (canonicalDiracItoState β h q hq)
      (canonicalDiracItoState β h q hq) canonicalBrownianMeasure :=
    ⟨fun _ => Filter.EventuallyEq.rfl,
      Filter.Eventually.of_forall (continuous_canonicalDiracItoState β h q hq)⟩
  have hbefore := (hasQuadraticVariationBeforeStop_preBrownianReal
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal).const_mul β
  have hbefore' (T a : ℝ≥0) : TendstoInMeasure canonicalBrownianMeasure
      (fun n => quadraticVariationBeforeStopApprox (fun s ω => β * canonicalBrownian s ω)
        T (n + 1) a) atTop
      (fun _ : BrownianSample => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        β ^ 2 ∂nonnegativeLebesgueMeasure) := by
    convert hbefore T a using 1
    ext ω
    simp [integral_const, Measure.real, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul,
      ENNReal.toReal_min, mul_comm]
  have hσint (T : ℝ≥0) : ∀ᵐ ω ∂canonicalBrownianMeasure,
      IntegrableOn (fun _ : ℝ≥0 => β ^ 2) (Set.Ioc 0 T) nonnegativeLebesgueMeasure :=
    Filter.Eventually.of_forall fun _ =>
      integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)
  have hmuInt (T : ℝ) (ω : BrownianSample) : IntegrableOn
      (fun s : ℝ => canonicalDiracItoDrift β h q hq s.toNNReal ω) (Set.Icc 0 T) := by
    by_cases hT : 0 ≤ T
    · simpa only [Real.coe_toNNReal T hT] using
        integrableOn_canonicalDiracItoDrift β h q hq T.toNNReal ω
    · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hT)]
      exact integrableOn_empty
  obtain ⟨I, hI, hformula⟩ := exists_ito_formula_of_characteristics
    (canonicalDiracItoState β h q hq) (canonicalDiracItoDrift β h q hq)
    (fun _ _ => β) (fun s ω => β * canonicalBrownian s ω)
    (canonicalDiracItoState β h q hq) hmeas hJmeas
    (measurable_canonicalDiracItoDrift β h q hq)
    hmuInt hmod
    (fun s => Filter.Eventually.of_forall (canonicalDiracItoState_decomposition β h q hq s))
    hbefore' hσint f hf htdiff hslice hdt hdx hsecond t
  exact ⟨I, hI, by simpa only [canonicalDiracItoState_zero] using hformula⟩


/-- The ordinary drift contribution to Itô's formula for the actual state. -/
def canonicalDiracItoDriftIntegral (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoSpaceDerivative f s (canonicalDiracItoState β h q hq s.toNNReal ω) *
      canonicalDiracItoDrift β h q hq s.toNNReal ω

/-- Weighted finite-variation increments on the actual drift. -/
def canonicalDiracItoDriftApprox (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) (ω : BrownianSample) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoSpaceDerivative f (uniformPartitionTime t n i)
      (canonicalDiracItoState β h q hq (uniformPartitionTime t n i) ω) *
      (integratedDrift (canonicalDiracItoDrift β h q hq) (uniformPartitionTime t n (i + 1)) ω -
        integratedDrift (canonicalDiracItoDrift β h q hq) (uniformPartitionTime t n i) ω)

/-- The actual drift sums converge pathwise and hence in probability. -/
theorem canonicalDiracItoDriftApprox_tendstoInMeasure
    (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ)
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => canonicalDiracItoDriftApprox β h q hq f t (n + 1)) atTop
      (canonicalDiracItoDriftIntegral β h q hq f t) := by
  have hmeas (s : ℝ≥0) : StronglyMeasurable (canonicalDiracItoState β h q hq s) :=
    (stronglyAdapted_canonicalDiracItoState β h q hq s).mono
      ((Filtration.natural canonicalBrownian
        (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)).le s)
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    apply StronglyMeasurable.aestronglyMeasurable
    unfold canonicalDiracItoDriftApprox
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (hdx.comp_stronglyMeasurable
      (stronglyMeasurable_const.prodMk (hmeas _))).mul
      ((stronglyMeasurable_integratedDrift (measurable_canonicalDiracItoDrift β h q hq) _).sub
        (stronglyMeasurable_integratedDrift (measurable_canonicalDiracItoDrift β h q hq) _))
  · apply Eventually.of_forall
    intro ω
    let d : ℝ≥0 → ℝ := fun s => canonicalDiracItoDrift β h q hq s ω
    let w : ℝ≥0 → ℝ := fun s =>
      itoSpaceDerivative f s (canonicalDiracItoState β h q hq s ω)
    have hd : IntegrableOn d (Set.Ioc 0 t) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)
        (C := β ^ 2)).mono'
      · exact ((measurable_canonicalDiracItoDrift β h q hq).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · filter_upwards [] with s
        exact norm_canonicalDiracItoDrift_le β h q hq s ω
    have hw : Continuous w := hdx.comp
      (NNReal.continuous_coe.prodMk (continuous_canonicalDiracItoState β h q hq ω))
    have hl := uniformPartition_weighted_integral_tendsto_signed d w t hd hw
    have hint (r : ℝ≥0) :
        (∫ s in Set.Ioc 0 r, d s ∂nonnegativeLebesgueMeasure) =
          integratedDrift (canonicalDiracItoDrift β h q hq) r ω :=
      integral_nonnegative_Ioc_eq_real_Icc (canonicalDiracItoDrift β h q hq) r ω
    have htarget : (∫ s in Set.Ioc 0 t, w s * d s ∂nonnegativeLebesgueMeasure) =
        canonicalDiracItoDriftIntegral β h q hq f t ω := by
      rw [integral_nonnegative_Ioc_eq_real_Icc
        (fun s ω => itoSpaceDerivative f s (canonicalDiracItoState β h q hq s ω) *
          canonicalDiracItoDrift β h q hq s ω) t ω]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      simp only [Real.coe_toNNReal s hs.1, canonicalDiracItoDriftIntegral]
    simpa only [canonicalDiracItoDriftApprox, w, hint, htarget] using hl

/-- Itô's formula for the actual state with a genuinely centered stochastic
term. The deterministic derivative bound is needed only on the given horizon. -/
theorem canonicalDiracItoState_ito_centered
    (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (K : ℝ≥0)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K) :
    ∃ N : BrownianSample → ℝ, Integrable N canonicalBrownianMeasure ∧
      (∫ ω, N ω ∂canonicalBrownianMeasure) = 0 ∧
      ∀ᵐ ω ∂canonicalBrownianMeasure,
        f t (canonicalDiracItoState β h q hq t ω) = f 0 h +
          generalItoTimeIntegral f (canonicalDiracItoState β h q hq) t ω +
          canonicalDiracItoDriftIntegral β h q hq f t ω + N ω +
          generalItoQuadraticIntegral f (canonicalDiracItoState β h q hq)
            (fun _ _ => β) t ω := by
  obtain ⟨I, hI, hformula⟩ := canonicalDiracItoState_ito β h q hq f
    hf htdiff hslice hdt hdx hsecond t
  let V := Filtration.natural canonicalBrownian
    (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
  let M : ℝ≥0 → BrownianSample → ℝ := fun s ω => β * canonicalBrownian s ω
  let H : ℝ≥0 → BrownianSample → ℝ := fun s ω =>
    itoSpaceDerivative f (min s t) (canonicalDiracItoState β h q hq (min s t) ω)
  have hM : Martingale M V canonicalBrownianMeasure :=
    (martingale_brownian_natural isBrownianReal_canonicalBrownian.toIsPreBrownianReal
      (fun s => (measurable_canonicalBrownian s).stronglyMeasurable)).smul β
  have hM2 (s : ℝ≥0) : MemLp (M s) 2 canonicalBrownianMeasure :=
    ((isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval s).memLp_two).const_mul β
  have hH : StronglyAdapted V H := by
    intro s
    exact hdx.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk
      ((stronglyAdapted_canonicalDiracItoState β h q hq (min s t)).mono
        (V.mono (min_le_left s t))))
  have hHK (s : ℝ≥0) (ω : BrownianSample) : ‖H s ω‖ ≤ K :=
    hK (min s t) ⟨(min s t).coe_nonneg, NNReal.coe_le_coe.mpr (min_le_right s t)⟩ _
  have hconv := hI.sub_real_noMeas
    (canonicalDiracItoDriftApprox_tendstoInMeasure β h q hq f hdx t)
  have hleft (n : ℕ) (ω : BrownianSample) :
      generalItoSpaceApprox f (canonicalDiracItoState β h q hq) t (n + 1) ω -
        canonicalDiracItoDriftApprox β h q hq f t (n + 1) ω =
      uniformAdaptedMartingaleLeftSumProcess M H t (n + 1) t ω := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
    unfold generalItoSpaceApprox canonicalDiracItoDriftApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have htime := (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos n)
      (Nat.le_of_lt hi')).2
    simp only [H, min_eq_left htime, NNReal.coe_min,
      min_eq_left (NNReal.coe_le_coe.mpr htime), M]
    have ha := canonicalDiracItoState_decomposition β h q hq
      (uniformPartitionTime t (n + 1) (i + 1)) ω
    have hb := canonicalDiracItoState_decomposition β h q hq
      (uniformPartitionTime t (n + 1) i) ω
    rw [ha, hb]
    ring
  have hconv' : TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess M H t (n + 1) t) atTop
      (fun ω => I ω - canonicalDiracItoDriftIntegral β h q hq f t ω) :=
    hconv.congr_left (fun n => Eventually.of_forall (hleft n))
  obtain ⟨hNint, hNzero⟩ := integrable_and_centered_of_bounded_martingale_leftSums
    hM hM2 hH K hHK t hconv'
  refine ⟨_, hNint, hNzero, ?_⟩
  filter_upwards [hformula] with ω hω
  rw [hω]
  ring


/-- A backward equation for the actual tanh-drift state preserves expectation
between post-interface times. This is an actual stochastic statement on the
constructed Brownian probability space. -/
theorem canonicalDiracItoState_backward_expectation
    (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hqa : q ≤ (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) ≤ 1)
    (K : ℝ≥0)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (hPDE : ∀ s ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ x,
      itoTimeDerivative f s x + itoSpaceDerivative f s x * (β ^ 2 * Real.tanh x) +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f s x * β ^ 2 = 0)
    (hintA : Integrable (fun ω => f a (canonicalDiracItoState β h q hq a ω))
      canonicalBrownianMeasure)
    (hintB : Integrable (fun ω => f b (canonicalDiracItoState β h q hq b ω))
      canonicalBrownianMeasure) :
    (∫ ω, f b (canonicalDiracItoState β h q hq b ω) ∂canonicalBrownianMeasure) =
      ∫ ω, f a (canonicalDiracItoState β h q hq a ω) ∂canonicalBrownianMeasure := by
  obtain ⟨Nb, hNbint, hNbzero, hfb⟩ := canonicalDiracItoState_ito_centered β h q hq f
    hf htdiff hslice hdt hdx hsecond b K hK
  have hKa : ∀ s ∈ Set.Icc (0 : ℝ) (a : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K :=
    fun s hs x => hK s ⟨hs.1, hs.2.trans (NNReal.coe_le_coe.mpr hab)⟩ x
  obtain ⟨Na, hNaint, hNazero, hfa⟩ := canonicalDiracItoState_ito_centered β h q hq f
    hf htdiff hslice hdt hdx hsecond a K hKa
  let L : BrownianSample → ℝ → ℝ := fun ω s =>
    itoTimeDerivative f s (canonicalDiracItoState β h q hq s.toNNReal ω) +
    itoSpaceDerivative f s (canonicalDiracItoState β h q hq s.toNNReal ω) *
      canonicalDiracItoDrift β h q hq s.toNNReal ω +
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s
      (canonicalDiracItoState β h q hq s.toNNReal ω) * β ^ 2
  have hLint (ω : BrownianSample) (r : ℝ≥0) : IntegrableOn (L ω) (Set.Icc 0 (r : ℝ)) := by
    have hpath : Continuous (fun s : ℝ => canonicalDiracItoState β h q hq s.toNNReal ω) :=
      (continuous_canonicalDiracItoState β h q hq ω).comp continuous_real_toNNReal
    have hp : Continuous (fun s : ℝ => (s, canonicalDiracItoState β h q hq s.toNNReal ω)) :=
      continuous_id.prodMk hpath
    have ht : IntegrableOn (fun s => itoTimeDerivative f s
        (canonicalDiracItoState β h q hq s.toNNReal ω)) (Set.Icc 0 (r : ℝ)) :=
      (hdt.comp hp).integrableOn_Icc
    have hx : IntegrableOn (fun s => itoSpaceDerivative f s
        (canonicalDiracItoState β h q hq s.toNNReal ω)) (Set.Icc 0 (r : ℝ)) :=
      (hdx.comp hp).integrableOn_Icc
    have hμmeas : AEStronglyMeasurable
        (fun s : ℝ => canonicalDiracItoDrift β h q hq s.toNNReal ω)
        (volume.restrict (Set.Icc 0 (r : ℝ))) :=
      ((measurable_canonicalDiracItoDrift β h q hq).comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
    have hxd := hx.mul_bdd hμmeas
      (Eventually.of_forall fun s => norm_canonicalDiracItoDrift_le β h q hq s.toNNReal ω)
    have hxx : IntegrableOn (fun s => (1 / 2 : ℝ) * itoSpaceSecondDerivative f s
        (canonicalDiracItoState β h q hq s.toNNReal ω) * β ^ 2) (Set.Icc 0 (r : ℝ)) :=
      (((hsecond.comp hp).const_mul (1 / 2)).mul_const (β ^ 2)).integrableOn_Icc
    exact (ht.add hxd).add hxx
  have hLformula (ω : BrownianSample) (r : ℝ≥0) :
      (∫ s in Set.Icc 0 (r : ℝ), L ω s) =
        generalItoTimeIntegral f (canonicalDiracItoState β h q hq) r ω +
        canonicalDiracItoDriftIntegral β h q hq f r ω +
        generalItoQuadraticIntegral f (canonicalDiracItoState β h q hq)
          (fun _ _ => β) r ω := by
    have hpath : Continuous (fun s : ℝ => (s, canonicalDiracItoState β h q hq s.toNNReal ω)) :=
      continuous_id.prodMk ((continuous_canonicalDiracItoState β h q hq ω).comp continuous_real_toNNReal)
    have ht := (hdt.comp hpath).integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (r : ℝ))
    have hx := (hdx.comp hpath).integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (r : ℝ))
    have hxd := hx.mul_bdd (((measurable_canonicalDiracItoDrift β h q hq).comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun s => norm_canonicalDiracItoDrift_le β h q hq s.toNNReal ω)
    have hxx := (((hsecond.comp hpath).const_mul (1 / 2)).mul_const (β ^ 2)).integrableOn_Icc
      (μ := volume) (a := (0 : ℝ)) (b := (r : ℝ))
    dsimp only [L]
    have hsplit := integral_add (ht.add hxd) hxx
    have hsplit' := integral_add ht hxd
    simp only [Function.comp_apply, Function.uncurry, Pi.add_apply] at hsplit hsplit'
    rw [hsplit, hsplit']
    unfold generalItoTimeIntegral canonicalDiracItoDriftIntegral generalItoQuadraticIntegral
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    ring
  have hLdiff (ω : BrownianSample) :
      (∫ s in Set.Icc 0 (b : ℝ), L ω s) - (∫ s in Set.Icc 0 (a : ℝ), L ω s) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      integral_Ioc_sub_integral_Ioc_eq_integral_Ioc a.coe_nonneg
        (NNReal.coe_le_coe.mpr hab) le_rfl
        ((hLint ω b).mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    have hs0 : 0 ≤ s := a.coe_nonneg.trans hs.1.le
    have hsq : q ≤ s := hqa.trans hs.1.le
    have hs1 : s ≤ 1 := hs.2.trans hb
    dsimp [L]
    unfold canonicalDiracItoDrift
    rw [Real.coe_toNNReal s hs0, if_pos ⟨hsq, hs1⟩]
    exact hPDE s ⟨hs.1.le, hs.2⟩ _
  have hAE : (fun ω => f b (canonicalDiracItoState β h q hq b ω) -
      f a (canonicalDiracItoState β h q hq a ω)) =ᵐ[canonicalBrownianMeasure]
      fun ω => Nb ω - Na ω := by
    filter_upwards [hfb, hfa] with ω hωb hωa
    have hd := hLdiff ω
    rw [hLformula ω b, hLformula ω a] at hd
    linarith
  have hzero : (∫ ω, Nb ω - Na ω ∂canonicalBrownianMeasure) = 0 := by
    rw [integral_sub hNbint hNaint, hNbzero, hNazero, sub_self]
  have hv := (integral_congr_ae hAE).trans hzero
  rw [integral_sub hintB hintA] at hv
  exact sub_eq_zero.mp hv

end Paper
