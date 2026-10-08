module

public import Paper.ParisiStateShift
public import Paper.HJBVerification
public import Paper.HJBEndpoint
public import Paper.ParisiTimeShiftTest

@[expose] public section

/-! # Weighted Itô increments for the actual Parisi gradient

The finite Cole--Hopf gradients will be tested on the genuine selected state.
The multiplier is measurable in the initial shifted Brownian filtration.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper

set_option maxHeartbeats 1000000 in
theorem ito_weighted_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hab : a ≤ b) (K : ℝ≥0)
    (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V 0] Z) (C : ℝ≥0)
    (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    ∃ N : Ω → ℝ, Integrable N P ∧ Integrable (fun ω => Z ω * N ω) P ∧
      (∫ sample, Z sample * N sample ∂P) = 0 ∧
      ∀ᵐ sample ∂P, f b (X b sample) = f a (X a sample) +
        (∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) + N sample := by
  have hKa : ∀ s ∈ Icc (0 : ℝ) (a : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K :=
    fun s hs x => hK s ⟨hs.1, hs.2.trans (NNReal.coe_le_coe.mpr hab)⟩ x
  obtain ⟨Na, hNa, hNa1, hNazero, hfa⟩ := ito_centered_weighted_of_boundedDrift hc f hf htdiff hslice
    hdt hdx hsecond a K hKa Z hZ C hC
  obtain ⟨Nb, hNb, hNb1, hNbzero, hfb⟩ := ito_centered_weighted_of_boundedDrift hc f hf htdiff hslice
    hdt hdx hsecond b K hK Z hZ C hC
  have hsub : (fun ω => Z ω * (Nb ω - Na ω)) =
      (fun ω => Z ω * Nb ω - Z ω * Na ω) := by funext ω; ring
  refine ⟨fun sample => Nb sample - Na sample, hNb.sub hNa, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hNb1.sub hNa1
  · rw [hsub, integral_sub hNb1 hNa1, hNbzero, hNazero, sub_self]
  · filter_upwards [hfa, hfb] with sample hsamplea hsampleb
    have hai : IntervalIntegrable (fun s => hjbGenerator X d β f s sample) volume 0 a :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le a.coe_nonneg] using hjbGenerator_integrableOn hc f hdt hdx hsecond 0 a sample)
    have hbi : IntervalIntegrable (fun s => hjbGenerator X d β f s sample) volume 0 b :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le b.coe_nonneg] using hjbGenerator_integrableOn hc f hdt hdx hsecond 0 b sample)
    have he : (∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) =
        (∫ s in (0 : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) -
        ∫ s in (0 : ℝ)..(a : ℝ), hjbGenerator X d β f s sample :=
      (intervalIntegral.integral_interval_sub_left hbi hai).symm
    rw [he, hjbGenerator_integral_eq hc f hdt hdx hsecond b sample,
      hjbGenerator_integral_eq hc f hdt hdx hsecond a sample, hsamplea, hsampleb]
    ring


set_option maxHeartbeats 1000000 in
/-- An integrable deterministic generator error bounds every actual weighted
expectation increment. The stochastic contribution is genuinely centered. -/
theorem ito_weighted_expectation_error {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hab : a ≤ b) (K : ℝ≥0)
    (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V 0] Z) (C : ℝ≥0)
    (hC : ∀ ω, ‖Z ω‖ ≤ C) (E : ℝ → ℝ) (hE : IntervalIntegrable E volume a b)
    (hgen : ∀ ω, ∀ s ∈ Icc (a : ℝ) (b : ℝ), ‖hjbGenerator X d β f s ω‖ ≤ E s)
    (hia : Integrable (fun ω => Z ω * f a (X a ω)) P)
    (hib : Integrable (fun ω => Z ω * f b (X b ω)) P) :
    ‖(∫ ω, Z ω * f b (X b ω) ∂P) - ∫ ω, Z ω * f a (X a ω) ∂P‖ ≤
      C * ∫ s in (a : ℝ)..(b : ℝ), E s := by
  obtain ⟨N, _hN, hZN, hzero, hformula⟩ := ito_weighted_increment hc f hf htdiff hslice
    hdt hdx hsecond a b hab K hK Z hZ C hC
  let G : Ω → ℝ := fun ω => Z ω * ∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s ω
  have heq : G =ᵐ[P] (fun ω => Z ω * f b (X b ω) - Z ω * f a (X a ω) - Z ω * N ω) := by
    filter_upwards [hformula] with ω hω
    dsimp only [G]
    rw [hω]
    ring
  have hiG : Integrable G P := ((hib.sub hia).sub hZN).congr heq.symm
  have hbound : ∀ᵐ ω ∂P, ‖G ω‖ ≤ (C : ℝ) * ∫ s in (a : ℝ)..(b : ℝ), E s := by
    exact .of_forall fun ω => by
      dsimp only [G]
      rw [norm_mul]
      have hi := intervalIntegral.norm_integral_le_of_norm_le (NNReal.coe_le_coe.mpr hab)
        (.of_forall fun s hs => hgen ω s ⟨hs.1.le, hs.2⟩) hE
      have hn : 0 ≤ ∫ s in (a : ℝ)..(b : ℝ), E s := (norm_nonneg _).trans hi
      exact mul_le_mul (hC ω) hi (norm_nonneg _) C.coe_nonneg
  have he : (∫ ω, G ω ∂P) =
      (∫ ω, Z ω * f b (X b ω) ∂P) - ∫ ω, Z ω * f a (X a ω) ∂P := by
    rw [integral_congr_ae heq]
    have hbi : Integrable (fun ω => Z ω * f b (X b ω) - Z ω * f a (X a ω)) P := hib.sub hia
    rw [integral_sub hbi hZN, integral_sub hib hia, hzero, sub_zero]
  rw [← he]
  simpa [Measure.real] using
    (norm_integral_le_of_norm_le_const hbound)


set_option maxHeartbeats 600000 in
/-- Removing the actual time cap from the weighted bounded gradient requires
only measurability of the random endpoint. -/
theorem tendsto_integral_parisiSlabGradient_terminalCap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {k : ℕ} (s : SpinGlass.Targets.RSBScheme k) (β : ℝ) (j : ℕ) (m : ℝ)
    (hm : m ∈ Icc (0 : ℝ) 1) (b : ℝ)
    (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (C : ℝ) (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    Tendsto (fun c => ∫ ω, Z ω * parisiSlabGradient s β j m b
      (hjbTimeCap c ((b - c) / 2) b) (Y ω) ∂P) (𝓝[<] b)
      (𝓝 (∫ ω, Z ω * parisiSlabGradient s β j m b b (Y ω) ∂P)) := by
  have hG := (continuous_parisiSlab s β j hm.1 b).2.1
  have hmeas : ∀ᶠ c in 𝓝[<] b, AEStronglyMeasurable
      (fun ω => Z ω * parisiSlabGradient s β j m b
        (hjbTimeCap c ((b - c) / 2) b) (Y ω)) P := by
    exact .of_forall fun c => (hZ.mul (hG.measurable.comp
      (measurable_const.prodMk hY))).aestronglyMeasurable
  have hbound : ∀ᶠ c in 𝓝[<] b, ∀ᵐ ω ∂P,
      ‖Z ω * parisiSlabGradient s β j m b (hjbTimeCap c ((b - c) / 2) b) (Y ω)‖ ≤ C := by
    exact .of_forall fun c => .of_forall fun ω => by
      rw [norm_mul]
      have hg : ‖parisiSlabGradient s β j m b (hjbTimeCap c ((b - c) / 2) b) (Y ω)‖ ≤ 1 := by
        simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b (hjbTimeCap c ((b - c) / 2) b) (Y ω)
      exact (mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans (by simpa using hC ω)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun c => Z ω * parisiSlabGradient s β j m b (hjbTimeCap c ((b - c) / 2) b) (Y ω))
      (𝓝[<] b) (𝓝 (Z ω * parisiSlabGradient s β j m b b (Y ω))) := by
    exact .of_forall fun ω => tendsto_const_nhds.mul (hG.continuousAt.tendsto.comp
      ((tendsto_hjbTerminalCap b).prodMk_nhds (tendsto_const_nhds (x := Y ω))))
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    hmeas hbound (integrable_const C) hlim


set_option maxHeartbeats 1000000 in
/-- The actual shifted Brownian state supplies weighted Itô estimates with
multipliers from any earlier deterministic time. -/
theorem canonicalParisiState_weighted_expectation_error
    (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvbound : ∀ t x, ‖v t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t))
    (r a b : ℝ≥0) (hra : r ≤ a) (hab : a ≤ b)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (K : ℝ≥0) (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration r] Z)
    (C : ℝ≥0) (hC : ∀ ω, ‖Z ω‖ ≤ C) (E : ℝ → ℝ)
    (hE : IntervalIntegrable E volume a b)
    (hgen : ∀ ω, ∀ s ∈ Icc (a : ℝ) (b : ℝ),
      ‖hjbGenerator (canonicalParisiItoState β h μ v hv hvbound hvlip)
        (canonicalParisiItoDrift β h μ v hv hvbound hvlip) β f s ω‖ ≤ E s)
    (hia : Integrable (fun ω => Z ω * f a (canonicalParisiItoState β h μ v hv hvbound hvlip a ω))
      canonicalBrownianMeasure)
    (hib : Integrable (fun ω => Z ω * f b (canonicalParisiItoState β h μ v hv hvbound hvlip b ω))
      canonicalBrownianMeasure) :
    ‖(∫ ω, Z ω * f b (canonicalParisiItoState β h μ v hv hvbound hvlip b ω) ∂canonicalBrownianMeasure) -
      ∫ ω, Z ω * f a (canonicalParisiItoState β h μ v hv hvbound hvlip a ω) ∂canonicalBrownianMeasure‖ ≤
      C * ∫ s in (a : ℝ)..(b : ℝ), E s := by
  have hrb : r ≤ b := hra.trans hab
  have ha' : r + (a - r) = a := add_tsub_cancel_of_le hra
  have hb' : r + (b - r) = b := add_tsub_cancel_of_le hrb
  have hcont := continuous_itoTimeShift f hf r
  have htd := differentiable_itoTimeShift f htdiff r
  have hslice' : ∀ s, ContDiff ℝ 2 (itoTimeShift f r s) := fun s => hslice (r + s)
  have hdt' := continuous_itoTimeShift_timeDerivative f htdiff hdt r
  have hdx' := continuous_itoTimeShift_spaceDerivative f hdx r
  have hxx' := continuous_itoTimeShift_spaceSecondDerivative f hsecond r
  have hK' : ∀ s ∈ Icc (0 : ℝ) ((b - r : ℝ≥0) : ℝ), ∀ x,
      ‖itoSpaceDerivative (itoTimeShift f r) s x‖ ≤ K := by
    intro s hs x
    apply hK (r + s) ⟨add_nonneg r.coe_nonneg hs.1, ?_⟩ x
    rw [NNReal.coe_sub hrb] at hs
    linarith [hs.2]
  have hZ' : StronglyMeasurable[canonicalBrownianShiftFiltration r 0] Z := by
    change StronglyMeasurable[canonicalBrownianFiltration (r + 0)] Z
    rw [add_zero]
    exact hZ
  have hE' : IntervalIntegrable (fun s => E (r + s)) volume (a - r : ℝ≥0) (b - r : ℝ≥0) := by
    simpa only [NNReal.coe_sub hra, NNReal.coe_sub hrb] using hE.comp_add_left (r : ℝ)
  have hgen' : ∀ ω, ∀ s ∈ Icc ((a - r : ℝ≥0) : ℝ) ((b - r : ℝ≥0) : ℝ),
      ‖hjbGenerator (canonicalParisiShiftState β h μ v hv hvbound hvlip r)
        (canonicalParisiShiftDrift β h μ v hv hvbound hvlip r) β (itoTimeShift f r) s ω‖ ≤ E (r + s) := by
    intro ω s hs
    have hs0 : 0 ≤ s := (a - r : ℝ≥0).coe_nonneg.trans hs.1
    have htime : ((r : ℝ) + s).toNNReal = r + s.toNNReal := by
      rw [Real.toNNReal_add r.coe_nonneg hs0, Real.toNNReal_coe]
    have hsr : r + s ∈ Icc (a : ℝ) (b : ℝ) := by
      rw [NNReal.coe_sub hra, NNReal.coe_sub hrb] at hs
      constructor <;> linarith [hs.1, hs.2]
    have hh := hgen ω (r + s) hsr
    simpa only [hjbGenerator, itoTimeShift_timeDerivative f htdiff,
      itoTimeShift_spaceDerivative, itoTimeShift_spaceSecondDerivative,
      canonicalParisiShiftState, canonicalParisiShiftDrift, htime] using hh
  have hia' : Integrable (fun ω => Z ω * itoTimeShift f r (a - r : ℝ≥0)
      (canonicalParisiShiftState β h μ v hv hvbound hvlip r (a - r) ω)) canonicalBrownianMeasure := by
    simpa only [itoTimeShift, canonicalParisiShiftState, ← NNReal.coe_add, ha'] using hia
  have hib' : Integrable (fun ω => Z ω * itoTimeShift f r (b - r : ℝ≥0)
      (canonicalParisiShiftState β h μ v hv hvbound hvlip r (b - r) ω)) canonicalBrownianMeasure := by
    simpa only [itoTimeShift, canonicalParisiShiftState, ← NNReal.coe_add, hb'] using hib
  have hh := ito_weighted_expectation_error
    (boundedDriftItoCharacteristics_canonicalParisiShift β h μ v hv hvbound hvlip r)
    (itoTimeShift f r) hcont htd hslice' hdt' hdx' hxx' (a - r) (b - r)
    (tsub_le_tsub_right hab r) K hK' Z hZ' C hC (fun s => E (r + s)) hE' hgen' hia' hib'
  simpa only [itoTimeShift, canonicalParisiShiftState, ← NNReal.coe_add, ha', hb',
    intervalIntegral.integral_comp_add_left] using hh

end Paper
