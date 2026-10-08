module

public import Paper.DiracShift
public import Paper.DiracLawIdentification

@[expose] public section

/-! Genuine conditional transition laws of the constructed tanh-drift state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace Paper

/-- Conditional Fourier identity, tested against any bounded information known
at the earlier time. The shifted Brownian martingale discharges centering. -/
theorem canonicalDiracItoState_weighted_cos
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1)
    (ξ : ℝ) (Z : BrownianSample → ℝ)
    (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    (∫ ω, Z ω * Real.cos (ξ * canonicalDiracItoState β h q hq (a + T) ω)
      ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * doobOperator (β ^ 2 * (T : ℝ)).toNNReal
        (fun y => Real.cos (ξ * y)) (canonicalDiracItoState β h q hq a ω)
        ∂canonicalBrownianMeasure := by
  let X := canonicalDiracShiftState β h q hq a
  let μ := canonicalDiracShiftDrift β h q hq a
  have hZ0 : StronglyMeasurable[canonicalBrownianShiftFiltration a 0] Z := by
    change StronglyMeasurable[canonicalBrownianFiltration (a + 0)] Z
    rw [add_zero]
    exact hZ
  have hZglob := hZ.mono (canonicalBrownianFiltration.le a)
  have hvalue (r : ℝ≥0) (hr : r ≤ T) :
      Integrable (fun ω => Z ω * backwardDoobCos β T ξ r (X r ω)) canonicalBrownianMeasure := by
    apply (integrable_const ((C : ℝ) * 2)).mono'
    · exact (hZglob.mul ((contDiff_backwardDoobCos_joint β T ξ 2).continuous.comp_stronglyMeasurable
        (stronglyMeasurable_const.prodMk
          ((stronglyAdapted_canonicalDiracShiftState β h q hq a r).mono
            ((canonicalBrownianShiftFiltration a).le r))))).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [norm_mul]
      exact mul_le_mul (hC ω)
        (norm_backwardDoobCos_le β T ξ r (X r ω) (NNReal.coe_le_coe.mpr hr))
        (norm_nonneg _) C.coe_nonneg
  have hK : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ∀ x,
      ‖itoSpaceDerivative (backwardDoobCos β T ξ) s x‖ ≤ (1 + 2 * |ξ|).toNNReal := by
    intro s hs x
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_backwardDoobCos_spaceDerivative_le β T ξ s x hs.2
  have hPDE : ∀ ω, ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
      itoTimeDerivative (backwardDoobCos β T ξ) s (X s.toNNReal ω) +
        itoSpaceDerivative (backwardDoobCos β T ξ) s (X s.toNNReal ω) * μ s.toNNReal ω +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative (backwardDoobCos β T ξ) s (X s.toNNReal ω) * β ^ 2 = 0 := by
    intro ω s hs
    have hsq : q ≤ (a : ℝ) + s := hqa.trans (le_add_of_nonneg_right hs.1)
    have hs1 : (a : ℝ) + s ≤ 1 := (add_le_add le_rfl hs.2).trans haT
    have hμ : μ s.toNNReal ω = β ^ 2 * Real.tanh (X s.toNNReal ω) := by
      have hp : q ≤ ((a + s.toNNReal : ℝ≥0) : ℝ) ∧
          ((a + s.toNNReal : ℝ≥0) : ℝ) ≤ 1 := by
        simpa only [NNReal.coe_add, Real.coe_toNNReal s hs.1] using (And.intro hsq hs1)
      dsimp [μ, X, canonicalDiracShiftDrift, canonicalDiracShiftState, canonicalDiracItoDrift]
      exact ite_eq_left hp
    rw [hμ]
    unfold itoTimeDerivative itoSpaceDerivative itoSpaceSecondDerivative
    convert backwardDoobCos_pde β T ξ s (X s.toNNReal ω) using 1 <;> ring
  have he := backward_weighted_expectation_of_boundedDrift
    (boundedDriftItoCharacteristics_canonicalDiracShift β h q hq a)
    (backwardDoobCos β T ξ) (contDiff_backwardDoobCos_joint β T ξ 2).continuous
    (fun x => fun s => (hasDerivAt_backwardDoobCos_time β T ξ s x).differentiableAt)
    (fun s => contDiff_backwardDoobCos_spatial β T ξ s 2)
    (continuous_backwardDoobCos_timeDerivative β T ξ)
    (continuous_backwardDoobCos_spaceDerivative β T ξ)
    (continuous_backwardDoobCos_spaceSecondDerivative β T ξ)
    T _ hK Z hZ0 C hC hPDE (hvalue 0 bot_le) (hvalue T le_rfl)
  simp only [backwardDoobCos_terminal, X, canonicalDiracShiftState, add_zero] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with ω
  congr 1
  rw [doobOperator_cos, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) T.coe_nonneg)]
  simp only [backwardDoobCos, sub_zero]

/-- Conditional Fourier identity, tested against any bounded information known
at the earlier time. The shifted Brownian martingale discharges centering. -/
theorem canonicalDiracItoState_weighted_sin
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1)
    (ξ : ℝ) (Z : BrownianSample → ℝ)
    (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    (∫ ω, Z ω * Real.sin (ξ * canonicalDiracItoState β h q hq (a + T) ω)
      ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * doobOperator (β ^ 2 * (T : ℝ)).toNNReal
        (fun y => Real.sin (ξ * y)) (canonicalDiracItoState β h q hq a ω)
        ∂canonicalBrownianMeasure := by
  let X := canonicalDiracShiftState β h q hq a
  let μ := canonicalDiracShiftDrift β h q hq a
  have hZ0 : StronglyMeasurable[canonicalBrownianShiftFiltration a 0] Z := by
    change StronglyMeasurable[canonicalBrownianFiltration (a + 0)] Z
    rw [add_zero]
    exact hZ
  have hZglob := hZ.mono (canonicalBrownianFiltration.le a)
  have hvalue (r : ℝ≥0) (hr : r ≤ T) :
      Integrable (fun ω => Z ω * backwardDoobSin β T ξ r (X r ω)) canonicalBrownianMeasure := by
    apply (integrable_const ((C : ℝ) * 2)).mono'
    · exact (hZglob.mul ((contDiff_backwardDoobSin_joint β T ξ 2).continuous.comp_stronglyMeasurable
        (stronglyMeasurable_const.prodMk
          ((stronglyAdapted_canonicalDiracShiftState β h q hq a r).mono
            ((canonicalBrownianShiftFiltration a).le r))))).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [norm_mul]
      exact mul_le_mul (hC ω)
        (norm_backwardDoobSin_le β T ξ r (X r ω) (NNReal.coe_le_coe.mpr hr))
        (norm_nonneg _) C.coe_nonneg
  have hK : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ∀ x,
      ‖itoSpaceDerivative (backwardDoobSin β T ξ) s x‖ ≤ (1 + 2 * |ξ|).toNNReal := by
    intro s hs x
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_backwardDoobSin_spaceDerivative_le β T ξ s x hs.2
  have hPDE : ∀ ω, ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
      itoTimeDerivative (backwardDoobSin β T ξ) s (X s.toNNReal ω) +
        itoSpaceDerivative (backwardDoobSin β T ξ) s (X s.toNNReal ω) * μ s.toNNReal ω +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative (backwardDoobSin β T ξ) s (X s.toNNReal ω) * β ^ 2 = 0 := by
    intro ω s hs
    have hsq : q ≤ (a : ℝ) + s := hqa.trans (le_add_of_nonneg_right hs.1)
    have hs1 : (a : ℝ) + s ≤ 1 := (add_le_add le_rfl hs.2).trans haT
    have hμ : μ s.toNNReal ω = β ^ 2 * Real.tanh (X s.toNNReal ω) := by
      have hp : q ≤ ((a + s.toNNReal : ℝ≥0) : ℝ) ∧
          ((a + s.toNNReal : ℝ≥0) : ℝ) ≤ 1 := by
        simpa only [NNReal.coe_add, Real.coe_toNNReal s hs.1] using (And.intro hsq hs1)
      dsimp [μ, X, canonicalDiracShiftDrift, canonicalDiracShiftState, canonicalDiracItoDrift]
      exact ite_eq_left hp
    rw [hμ]
    unfold itoTimeDerivative itoSpaceDerivative itoSpaceSecondDerivative
    convert backwardDoobSin_pde β T ξ s (X s.toNNReal ω) using 1 <;> ring
  have he := backward_weighted_expectation_of_boundedDrift
    (boundedDriftItoCharacteristics_canonicalDiracShift β h q hq a)
    (backwardDoobSin β T ξ) (contDiff_backwardDoobSin_joint β T ξ 2).continuous
    (fun x => fun s => (hasDerivAt_backwardDoobSin_time β T ξ s x).differentiableAt)
    (fun s => contDiff_backwardDoobSin_spatial β T ξ s 2)
    (continuous_backwardDoobSin_timeDerivative β T ξ)
    (continuous_backwardDoobSin_spaceDerivative β T ξ)
    (continuous_backwardDoobSin_spaceSecondDerivative β T ξ)
    T _ hK Z hZ0 C hC hPDE (hvalue 0 bot_le) (hvalue T le_rfl)
  simp only [backwardDoobSin_terminal, X, canonicalDiracShiftState, add_zero] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with ω
  congr 1
  rw [doobOperator_sin, Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) T.coe_nonneg)]
  simp only [backwardDoobSin, sub_zero]


/-- The normalized Doob expectation is a measurable function of the state. -/
theorem stronglyMeasurable_doobOperator (v : ℝ≥0) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    StronglyMeasurable (doobOperator v ψ) := by
  have hm := ((hψ.comp measurable_snd).stronglyMeasurable).integral_kernel_prod_right'
    (κ := coshStateKernel v)
  simpa only [Function.comp_apply, integral_coshStateKernel] using hm

/-- A bounded kernel observable can be integrated against any finite initial
law, including the restriction to an earlier information event. -/
theorem integral_coshStateKernel_comp_bounded
    (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    (∫ y, ψ y ∂(coshStateKernel v ∘ₘ μ)) = ∫ x, doobOperator v ψ x ∂μ := by
  have hint : Integrable ψ (coshStateKernel v ∘ₘ μ) :=
    (integrable_const C).mono' hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint]
  simp only [Kernel.const_apply, integral_coshStateKernel]

private theorem integral_indicator_one_mul_eq_setIntegral
    (P : Measure BrownianSample) (A : Set BrownianSample) (hA : MeasurableSet A)
    (f : BrownianSample → ℝ) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P) = ∫ ω in A, f ω ∂P := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hω : ω ∈ A <;> simp [hω]

/-- Genuine transition-kernel identity on every event known at the earlier
time. This is stronger than equality of marginal state distributions. -/
theorem canonicalDiracItoState_restricted_transitionLaw
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1)
    (A : Set BrownianSample) (hA : MeasurableSet[canonicalBrownianFiltration a] A) :
    (canonicalBrownianMeasure.restrict A).map (canonicalDiracItoState β h q hq (a + T)) =
      coshStateKernel (β ^ 2 * (T : ℝ)).toNNReal ∘ₘ
        (canonicalBrownianMeasure.restrict A).map (canonicalDiracItoState β h q hq a) := by
  have hAg : MeasurableSet A := canonicalBrownianFiltration.le a A hA
  have hZ : StronglyMeasurable[canonicalBrownianFiltration a]
      (A.indicator (fun _ => (1 : ℝ))) := stronglyMeasurable_const.indicator hA
  have hZbound (ω : BrownianSample) : ‖A.indicator (fun _ => (1 : ℝ)) ω‖ ≤ (1 : ℝ≥0) := by
    by_cases hω : ω ∈ A <;> simp [hω]
  apply measure_eq_of_cos_sin_integrals
  · intro ξ
    have he := canonicalDiracItoState_weighted_cos β h q hq a T hqa haT ξ
      (A.indicator (fun _ => (1 : ℝ))) hZ 1 hZbound
    rw [integral_indicator_one_mul_eq_setIntegral _ A hAg,
      integral_indicator_one_mul_eq_setIntegral _ A hAg] at he
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq (a + T)).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => Real.cos (ξ * y))
        ((canonicalBrownianMeasure.restrict A).map (canonicalDiracItoState β h q hq (a + T))))]
    rw [integral_coshStateKernel_comp_bounded _ _ (fun y => Real.cos (ξ * y))
      (by fun_prop) 1 (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * y))]
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq a).aemeasurable
      (stronglyMeasurable_doobOperator _ _ (by fun_prop)).aestronglyMeasurable]
    exact he
  · intro ξ
    have he := canonicalDiracItoState_weighted_sin β h q hq a T hqa haT ξ
      (A.indicator (fun _ => (1 : ℝ))) hZ 1 hZbound
    rw [integral_indicator_one_mul_eq_setIntegral _ A hAg,
      integral_indicator_one_mul_eq_setIntegral _ A hAg] at he
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq (a + T)).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => Real.sin (ξ * y))
        ((canonicalBrownianMeasure.restrict A).map (canonicalDiracItoState β h q hq (a + T))))]
    rw [integral_coshStateKernel_comp_bounded _ _ (fun y => Real.sin (ξ * y))
      (by fun_prop) 1 (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * y))]
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq a).aemeasurable
      (stronglyMeasurable_doobOperator _ _ (by fun_prop)).aestronglyMeasurable]
    exact he


/-- Actual conditional expectation formula for every bounded measurable
observable of the future state. -/
theorem condExp_canonicalDiracItoState_after
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    canonicalBrownianMeasure[(fun ω => ψ (canonicalDiracItoState β h q hq (a + T) ω)) |
      canonicalBrownianFiltration a] =ᵐ[canonicalBrownianMeasure]
      fun ω => doobOperator (β ^ 2 * (T : ℝ)).toNNReal ψ
        (canonicalDiracItoState β h q hq a ω) := by
  let v := (β ^ 2 * (T : ℝ)).toNNReal
  have hstate : StronglyMeasurable[canonicalBrownianFiltration a]
      (canonicalDiracItoState β h q hq a) := stronglyAdapted_canonicalDiracItoState β h q hq a
  have hkernel := stronglyMeasurable_doobOperator v ψ hψ
  have hcandidate : StronglyMeasurable[canonicalBrownianFiltration a]
      (fun ω => doobOperator v ψ (canonicalDiracItoState β h q hq a ω)) :=
    hkernel.comp_measurable hstate.measurable
  have hint : Integrable (fun ω => ψ (canonicalDiracItoState β h q hq (a + T) ω))
      canonicalBrownianMeasure :=
    (integrable_const C).mono'
      ((hψ.comp (measurable_canonicalDiracItoState_fixed β h q hq (a + T))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => hC _)
  have hcandidateInt : Integrable
      (fun ω => doobOperator v ψ (canonicalDiracItoState β h q hq a ω)) canonicalBrownianMeasure :=
    (integrable_const C).mono'
      (hcandidate.mono (canonicalBrownianFiltration.le a)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => norm_doobOperator_le v ψ hψ C hC _)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (canonicalBrownianFiltration.le a) hint
  · intro A hA hfinite
    exact hcandidateInt.integrableOn
  · intro A hA hfinite
    have hl := canonicalDiracItoState_restricted_transitionLaw β h q hq a T hqa haT A hA
    have he : (∫ y, ψ y ∂(canonicalBrownianMeasure.restrict A).map
        (canonicalDiracItoState β h q hq (a + T))) =
        ∫ y, ψ y ∂(coshStateKernel v ∘ₘ (canonicalBrownianMeasure.restrict A).map
          (canonicalDiracItoState β h q hq a)) := by rw [hl]
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq (a + T)).aemeasurable
      hψ.aestronglyMeasurable,
      integral_coshStateKernel_comp_bounded _ v ψ hψ C hC,
      integral_map (measurable_canonicalDiracItoState_fixed β h q hq a).aemeasurable
        hkernel.aestronglyMeasurable] at he
    exact he.symm
  · exact hcandidate.aestronglyMeasurable

end Paper
