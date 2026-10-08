module

public import Paper.DiracStateLaw
public import Paper.DoobFourier
public import Paper.FourierMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Identifying the constructed Dirac state's law by genuine Itô calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace Paper

theorem measurable_canonicalDiracItoState_fixed (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) : Measurable (canonicalDiracItoState β h q hq t) :=
  (measurable_canonicalDiracItoState β h q hq).comp (measurable_const.prodMk measurable_id)

/-- The actual state distribution on the canonical Brownian space. -/
def canonicalDiracMarginal (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ≥0) : Measure ℝ :=
  canonicalBrownianMeasure.map (canonicalDiracItoState β h q hq t)

instance canonicalDiracMarginal_isProbability (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ≥0) :
    IsProbabilityMeasure (canonicalDiracMarginal β h q hq t) := by
  unfold canonicalDiracMarginal
  infer_instance

/-- Gaussian evolution to the interface, followed by the actual normalized
cosh Doob kernel. This definition will be identified with the SDE state law. -/
def gaussianDoobMarginal (β h q : ℝ) (t : ℝ≥0) : Measure ℝ :=
  coshStateKernel (β ^ 2 * ((t : ℝ) - q)).toNNReal ∘ₘ gaussianReal h (β ^ 2 * q).toNNReal

instance gaussianDoobMarginal_isProbability (β h q : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (gaussianDoobMarginal β h q t) := by
  unfold gaussianDoobMarginal
  infer_instance

/-- The actual state at the interface has the exact Gaussian law. -/
theorem hasLaw_canonicalDiracItoState_interface (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    HasLaw (canonicalDiracItoState β h q hq q.toNNReal)
      (gaussianReal h (β ^ 2 * q).toNNReal) canonicalBrownianMeasure := by
  have he : canonicalDiracItoState β h q hq q.toNNReal =
      fun ω => canonicalDiracStateReal β h q hq ω q := by
    funext ω
    rw [canonicalDiracItoState_eq β h q hq (by simpa only [Real.coe_toNNReal q hq.1] using hq.2)]
    rw [Real.coe_toNNReal q hq.1]
  rw [he]
  exact hasLaw_canonicalDiracState_before β h q hq ⟨hq.1, le_rfl⟩


/-- The constructed stochastic state obeys the explicit backward cos equation. -/
theorem canonicalDiracItoState_backward_cos
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (ξ : ℝ)
    (a b : ℝ≥0) (hqa : q ≤ (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) ≤ 1) :
    (∫ ω, Real.cos (ξ * canonicalDiracItoState β h q hq b ω) ∂canonicalBrownianMeasure) =
      ∫ ω, backwardDoobCos β b ξ a (canonicalDiracItoState β h q hq a ω) ∂canonicalBrownianMeasure := by
  have hvalue (r : ℝ≥0) (hr : r ≤ b) :
      Integrable (fun ω => backwardDoobCos β b ξ r (canonicalDiracItoState β h q hq r ω))
        canonicalBrownianMeasure := by
    apply (integrable_const (2 : ℝ)).mono'
    · exact ((contDiff_backwardDoobCos_joint β b ξ 2).continuous.measurable.comp
        (measurable_const.prodMk (measurable_canonicalDiracItoState_fixed β h q hq r))).aestronglyMeasurable
    · filter_upwards [] with ω
      simpa only [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
        norm_backwardDoobCos_le β b ξ r (canonicalDiracItoState β h q hq r ω)
          (NNReal.coe_le_coe.mpr hr)
  have hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x,
      ‖itoSpaceDerivative (backwardDoobCos β b ξ) s x‖ ≤ (1 + 2 * |ξ|).toNNReal := by
    intro s hs x
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_backwardDoobCos_spaceDerivative_le β b ξ s x hs.2
  have hPDE : ∀ s ∈ Icc (a : ℝ) (b : ℝ), ∀ x,
      itoTimeDerivative (backwardDoobCos β b ξ) s x +
        itoSpaceDerivative (backwardDoobCos β b ξ) s x * (β ^ 2 * Real.tanh x) +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative (backwardDoobCos β b ξ) s x * β ^ 2 = 0 := by
    intro s hs x
    unfold itoTimeDerivative itoSpaceDerivative itoSpaceSecondDerivative
    convert backwardDoobCos_pde β b ξ s x using 1 <;> ring
  have he := canonicalDiracItoState_backward_expectation β h q hq
    (backwardDoobCos β b ξ) (contDiff_backwardDoobCos_joint β b ξ 2).continuous
    (fun x => fun s => (hasDerivAt_backwardDoobCos_time β b ξ s x).differentiableAt)
    (fun s => contDiff_backwardDoobCos_spatial β b ξ s 2)
    (continuous_backwardDoobCos_timeDerivative β b ξ)
    (continuous_backwardDoobCos_spaceDerivative β b ξ)
    (continuous_backwardDoobCos_spaceSecondDerivative β b ξ)
    a b hqa hab hb _ hK hPDE (hvalue a hab) (hvalue b le_rfl)
  simpa only [backwardDoobCos_terminal] using he

/-- The constructed stochastic state obeys the explicit backward sin equation. -/
theorem canonicalDiracItoState_backward_sin
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (ξ : ℝ)
    (a b : ℝ≥0) (hqa : q ≤ (a : ℝ)) (hab : a ≤ b) (hb : (b : ℝ) ≤ 1) :
    (∫ ω, Real.sin (ξ * canonicalDiracItoState β h q hq b ω) ∂canonicalBrownianMeasure) =
      ∫ ω, backwardDoobSin β b ξ a (canonicalDiracItoState β h q hq a ω) ∂canonicalBrownianMeasure := by
  have hvalue (r : ℝ≥0) (hr : r ≤ b) :
      Integrable (fun ω => backwardDoobSin β b ξ r (canonicalDiracItoState β h q hq r ω))
        canonicalBrownianMeasure := by
    apply (integrable_const (2 : ℝ)).mono'
    · exact ((contDiff_backwardDoobSin_joint β b ξ 2).continuous.measurable.comp
        (measurable_const.prodMk (measurable_canonicalDiracItoState_fixed β h q hq r))).aestronglyMeasurable
    · filter_upwards [] with ω
      simpa only [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
        norm_backwardDoobSin_le β b ξ r (canonicalDiracItoState β h q hq r ω)
          (NNReal.coe_le_coe.mpr hr)
  have hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x,
      ‖itoSpaceDerivative (backwardDoobSin β b ξ) s x‖ ≤ (1 + 2 * |ξ|).toNNReal := by
    intro s hs x
    rw [Real.coe_toNNReal _ (by positivity)]
    exact norm_backwardDoobSin_spaceDerivative_le β b ξ s x hs.2
  have hPDE : ∀ s ∈ Icc (a : ℝ) (b : ℝ), ∀ x,
      itoTimeDerivative (backwardDoobSin β b ξ) s x +
        itoSpaceDerivative (backwardDoobSin β b ξ) s x * (β ^ 2 * Real.tanh x) +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative (backwardDoobSin β b ξ) s x * β ^ 2 = 0 := by
    intro s hs x
    unfold itoTimeDerivative itoSpaceDerivative itoSpaceSecondDerivative
    convert backwardDoobSin_pde β b ξ s x using 1 <;> ring
  have he := canonicalDiracItoState_backward_expectation β h q hq
    (backwardDoobSin β b ξ) (contDiff_backwardDoobSin_joint β b ξ 2).continuous
    (fun x => fun s => (hasDerivAt_backwardDoobSin_time β b ξ s x).differentiableAt)
    (fun s => contDiff_backwardDoobSin_spatial β b ξ s 2)
    (continuous_backwardDoobSin_timeDerivative β b ξ)
    (continuous_backwardDoobSin_spaceDerivative β b ξ)
    (continuous_backwardDoobSin_spaceSecondDerivative β b ξ)
    a b hqa hab hb _ hK hPDE (hvalue a hab) (hvalue b le_rfl)
  simpa only [backwardDoobSin_terminal] using he


/-- Integrals against a Doob-evolved Gaussian law are actual iterated kernel
integrals; the boundedness input discharges Fubini integrability. -/
theorem integral_gaussianDoobMarginal_bounded (β h q : ℝ) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, f y ∂gaussianDoobMarginal β h q t) =
      ∫ x, doobOperator (β ^ 2 * ((t : ℝ) - q)).toNNReal f x
        ∂gaussianReal h (β ^ 2 * q).toNNReal := by
  have hint : Integrable f (gaussianDoobMarginal β h q t) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  unfold gaussianDoobMarginal at hint ⊢
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint]
  simp only [Kernel.const_apply, integral_coshStateKernel]

/-- The physical post-interface state has exactly the Gaussian/cosh-Doob
marginal law. This identifies the actual Brownian-driven integral-equation
solution, rather than defining its law through a semigroup. -/
theorem canonicalDiracMarginal_eq_gaussianDoobMarginal
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ≥0)
    (hqt : q ≤ (t : ℝ)) (ht : (t : ℝ) ≤ 1) :
    canonicalDiracMarginal β h q hq t = gaussianDoobMarginal β h q t := by
  have hqt' : q.toNNReal ≤ t := by
    exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal q hq.1] using hqt)
  have hvariance : 0 ≤ β ^ 2 * ((t : ℝ) - q) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hqt)
  have hqtime : (q.toNNReal : ℝ) = q := Real.coe_toNNReal q hq.1
  apply measure_eq_of_cos_sin_integrals
  · intro ξ
    have he := canonicalDiracItoState_backward_cos β h q hq ξ q.toNNReal t
      (by rw [hqtime]) hqt' ht
    have hl := (hasLaw_canonicalDiracItoState_interface β h q hq).integral_comp
      (((contDiff_backwardDoobCos_spatial β t ξ q 2).continuous.measurable).aestronglyMeasurable)
    simp only [Function.comp_apply] at hl
    rw [hqtime] at he
    change (∫ y, Real.cos (ξ * y) ∂canonicalBrownianMeasure.map
      (canonicalDiracItoState β h q hq t)) = _
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq t).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => Real.cos (ξ * y))
        (canonicalBrownianMeasure.map (canonicalDiracItoState β h q hq t)))]
    rw [integral_gaussianDoobMarginal_bounded β h q t (fun y => Real.cos (ξ * y))
      (by fun_prop) 1 (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * y))]
    rw [he]
    change (∫ ω, backwardDoobCos β t ξ q (canonicalDiracItoState β h q hq q.toNNReal ω)
      ∂canonicalBrownianMeasure) = _
    rw [hl]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [doobOperator_cos, Real.coe_toNNReal _ hvariance]
    rfl
  · intro ξ
    have he := canonicalDiracItoState_backward_sin β h q hq ξ q.toNNReal t
      (by rw [hqtime]) hqt' ht
    have hl := (hasLaw_canonicalDiracItoState_interface β h q hq).integral_comp
      (((contDiff_backwardDoobSin_spatial β t ξ q 2).continuous.measurable).aestronglyMeasurable)
    simp only [Function.comp_apply] at hl
    rw [hqtime] at he
    change (∫ y, Real.sin (ξ * y) ∂canonicalBrownianMeasure.map
      (canonicalDiracItoState β h q hq t)) = _
    rw [integral_map (measurable_canonicalDiracItoState_fixed β h q hq t).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => Real.sin (ξ * y))
        (canonicalBrownianMeasure.map (canonicalDiracItoState β h q hq t)))]
    rw [integral_gaussianDoobMarginal_bounded β h q t (fun y => Real.sin (ξ * y))
      (by fun_prop) 1 (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * y))]
    rw [he]
    change (∫ ω, backwardDoobSin β t ξ q (canonicalDiracItoState β h q hq q.toNNReal ω)
      ∂canonicalBrownianMeasure) = _
    rw [hl]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [doobOperator_sin, Real.coe_toNNReal _ hvariance]
    rfl


/-- The actual SDE state satisfies the paper's Gaussian/Doob expectation
formula for every bounded measurable observable. -/
theorem integral_canonicalDiracItoState_eq_gaussianDoob
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ≥0)
    (hqt : q ≤ (t : ℝ)) (ht : (t : ℝ) ≤ 1)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    (∫ ω, ψ (canonicalDiracItoState β h q hq t ω) ∂canonicalBrownianMeasure) =
      ∫ x, doobOperator (β ^ 2 * ((t : ℝ) - q)).toNNReal ψ x
        ∂gaussianReal h (β ^ 2 * q).toNNReal := by
  have hmap : (∫ ω, ψ (canonicalDiracItoState β h q hq t ω) ∂canonicalBrownianMeasure) =
      ∫ y, ψ y ∂canonicalDiracMarginal β h q hq t := by
    unfold canonicalDiracMarginal
    exact (integral_map (measurable_canonicalDiracItoState_fixed β h q hq t).aemeasurable
      hψ.aestronglyMeasurable).symm
  rw [hmap, canonicalDiracMarginal_eq_gaussianDoobMarginal β h q hq t hqt ht]
  exact integral_gaussianDoobMarginal_bounded β h q t ψ hψ C hC

/-- The actual physical state in the paper has the identified post-interface law. -/
theorem hasLaw_canonicalDiracState_after
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    HasLaw (fun ω => canonicalDiracStateReal β h q hq ω t)
      (gaussianDoobMarginal β h q t.toNNReal) canonicalBrownianMeasure := by
  have ht0 : 0 ≤ t := hq.1.trans ht.1
  have he : (fun ω => canonicalDiracStateReal β h q hq ω t) =
      canonicalDiracItoState β h q hq t.toNNReal := by
    funext ω
    rw [canonicalDiracItoState_eq β h q hq
      (by simpa only [Real.coe_toNNReal t ht0] using ht.2)]
    rw [Real.coe_toNNReal t ht0]
  rw [he]
  refine ⟨(measurable_canonicalDiracItoState_fixed β h q hq t.toNNReal).aemeasurable, ?_⟩
  exact canonicalDiracMarginal_eq_gaussianDoobMarginal β h q hq t.toNNReal
    (by simpa only [Real.coe_toNNReal t ht0] using ht.1)
    (by simpa only [Real.coe_toNNReal t ht0] using ht.2)

end Paper
