module

public import Paper.ParisiTerminalWeak

@[expose] public section

/-! # Verification of the weak equation for actual mild gradients

This module combines the proved source and terminal heat identities.  Its
input is the concrete gradient Duhamel equation, rather than a hypothesis
asserting that the potential solves the weak PDE.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem parisiSpaceTime_eq_timeProd :
    parisiSpaceTime = parisiTimeMeasure.prod volume := by
  unfold parisiSpaceTime parisiTimeMeasure
  rw [restrict_Ioc_eq_restrict_Icc]

theorem ae_parisiTime_fst_mem :
    ∀ᵐ p : ℝ × ℝ ∂parisiTimeMeasure.prod volume, p.1 ∈ Ioc (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_fst measurableSet_Ioc)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact .of_forall fun _ => ht

noncomputable def parisiNonlinearity (μ : ParisiMeasure) (v : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ := parisiCDF μ p.1 * v p ^ 2

theorem parisiNonlinearity_measurable (μ : ParisiMeasure) (v : ℝ × ℝ → ℝ)
    (hv : Measurable v) : Measurable (parisiNonlinearity μ v) :=
  ((parisiCDF_measurable μ).comp measurable_fst).mul (hv.pow_const 2)

theorem norm_parisiNonlinearity_le (μ : ParisiMeasure) (v : ℝ × ℝ → ℝ)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (p : ℝ × ℝ) :
    ‖parisiNonlinearity μ v p‖ ≤ R ^ 2 := by
  have hm : ‖parisiCDF μ p.1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ p.1)]
    exact parisiCDF_le_one μ p.1
  calc
    _ = ‖parisiCDF μ p.1‖ * ‖v p‖ ^ 2 := by
      simp only [parisiNonlinearity, norm_mul, norm_pow]
    _ ≤ 1 * R ^ 2 := mul_le_mul hm
      (pow_le_pow_left₀ (norm_nonneg _) (hb _) 2) (by positivity) (by norm_num)
    _ = _ := one_mul _

theorem boundedHeatSource_parisiNonlinearity (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t s x : ℝ) :
    boundedHeatSource β (parisiNonlinearity μ v) t s x = parisiHeatSource β μ v t x s := by
  simp only [boundedHeatSource, parisiNonlinearity, parisiHeatSource,
    heatSemigroup, gaussianExpectation, integral_const_mul]

theorem parisiContinuousPotential_eq_terminalVolterra (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiContinuousPotential β μ v (t, x) = parisiTerminalHeat β (t, x) +
      β ^ 2 / 2 * boundedVolterraPotential β (parisiNonlinearity μ v) (t, x) := by
  rw [parisiContinuousPotential_eq β μ v t x ht.2,
    boundedVolterraPotential_eq β (parisiNonlinearity μ v) t x ht]
  unfold parisiDuhamelPotential parisiDuhamelCorrection parisiTerminalHeat
  simp_rw [boundedHeatSource_parisiNonlinearity]

theorem integral_parisiContinuousPotential_adjointSource (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (v : ℝ × ℝ → ℝ) (hv : Continuous v)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) :
    (∫ p, parisiContinuousPotential β μ v p * parisiAdjointSource β φ p
      ∂parisiSpaceTime) = -(∫ x, Real.log (Real.cosh x) * φ (1, x)) -
      β ^ 2 / 2 * (∫ p, parisiNonlinearity μ v p * φ p ∂parisiSpaceTime) := by
  rw [parisiSpaceTime_eq_timeProd]
  have hψ := continuous_parisiAdjointSource β φ hφ
  have hψc := hasCompactSupport_parisiAdjointSource β φ hφ hc
  have hi : Integrable (fun p => parisiTerminalHeat β p * parisiAdjointSource β φ p)
      (parisiTimeMeasure.prod volume) :=
    ((continuous_parisiTerminalHeat β).mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  have hj := integrable_boundedVolterra_test β (parisiNonlinearity μ v)
    (parisiNonlinearity_measurable μ v hv.measurable) (R ^ 2)
    (norm_parisiNonlinearity_le μ v R hb) _ hψ hψc
  calc
    _ = ∫ p, parisiTerminalHeat β p * parisiAdjointSource β φ p + β ^ 2 / 2 *
        (boundedVolterraPotential β (parisiNonlinearity μ v) p * parisiAdjointSource β φ p)
        ∂parisiTimeMeasure.prod volume := by
      apply integral_congr_ae
      filter_upwards [ae_parisiTime_fst_mem] with p hp
      rcases p with ⟨t, x⟩
      rw [parisiContinuousPotential_eq_terminalVolterra β μ v t x ⟨hp.1.le, hp.2⟩]
      ring
    _ = _ := by
      rw [integral_add hi (hj.const_mul _), integral_const_mul,
        integral_parisiTerminalHeat_adjointSource β hβ φ hφ hc hsupp,
        integral_boundedVolterra_adjointSource β hβ (parisiNonlinearity μ v)
          (parisiNonlinearity_measurable μ v hv.measurable) (R ^ 2)
          (norm_parisiNonlinearity_le μ v R hb) φ hφ hc hsupp]
      ring

/-- A bounded continuous solution of the actual gradient Duhamel equation
supplies a solution in the paper's distributional terminal-value class. -/
theorem isParisiWeakSolution_of_boundedContinuous_mildGradient
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (v : ℝ × ℝ → ℝ)
    (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
        parisiGradientCorrection β μ v 1 t x) :
    IsParisiWeakSolution β μ (parisiContinuousPotential β μ v) v := by
  have hu := continuous_parisiContinuousPotential β μ v hv R hb
  refine ⟨hu.continuousOn, hv.aestronglyMeasurable, ⟨R, .of_forall hb⟩, ?_, ?_, ?_⟩
  · apply isParisiWeakGradient_of_hasDerivAt _ _ hu hv
    intro t ht x
    have hd := hasDerivAt_parisiDuhamelPotential_spatial β μ v hv.measurable R hb t x ht.2 hβ
    rw [← heq t ht x] at hd
    exact hd.congr_of_eventuallyEq (.of_forall fun y =>
      parisiContinuousPotential_eq β μ v t y ht.2)
  · intro x
    rw [parisiContinuousPotential_eq β μ v 1 x le_rfl, parisiDuhamelPotential_terminal]
  · intro φ hφ hc hsupp
    have hT := continuous_parisiTestT φ hφ
    have hTc := hasCompactSupport_parisiTestT φ hφ hc
    have hXX := continuous_parisiTestXX φ hφ
    have hXXc := hasCompactSupport_parisiTestXX φ hφ hc
    have hi : Integrable (fun p => -parisiContinuousPotential β μ v p * parisiTestT φ p)
        parisiSpaceTime := (hu.neg.mul hT).integrable_of_hasCompactSupport hTc.mul_left
    have hj : Integrable (fun p => parisiContinuousPotential β μ v p * parisiTestXX φ p)
        parisiSpaceTime := (hu.mul hXX).integrable_of_hasCompactSupport hXXc.mul_left
    have hφi : Integrable φ parisiSpaceTime := hφ.continuous.integrable_of_hasCompactSupport hc
    have hk : Integrable (fun p => parisiNonlinearity μ v p * φ p) parisiSpaceTime := by
      exact (hφi.mul_bdd (parisiNonlinearity_measurable μ v hv.measurable).aestronglyMeasurable
        (.of_forall (norm_parisiNonlinearity_le μ v R hb))).congr (.of_forall fun p => mul_comm _ _)
    refine ⟨hi.add ((hj.add hk).const_mul _),
      integrable_parisiTest_logCosh_terminal φ hφ hc 1, ?_⟩
    have hψi : Integrable (fun p => parisiContinuousPotential β μ v p * parisiAdjointSource β φ p)
        parisiSpaceTime := (hu.mul (continuous_parisiAdjointSource β φ hφ)).integrable_of_hasCompactSupport
          (hasCompactSupport_parisiAdjointSource β φ hφ hc).mul_left
    calc
      _ = (∫ p, parisiContinuousPotential β μ v p * parisiAdjointSource β φ p
          ∂parisiSpaceTime) + β ^ 2 / 2 * (∫ p, parisiNonlinearity μ v p * φ p ∂parisiSpaceTime) +
          (∫ x, φ (1, x) * Real.log (Real.cosh x)) := by
        congr 1
        rw [← integral_const_mul, ← integral_add hψi (hk.const_mul _)]
        apply integral_congr_ae
        exact .of_forall fun p => by unfold parisiAdjointSource parisiNonlinearity; ring
      _ = 0 := by
        rw [integral_parisiContinuousPotential_adjointSource β hβ μ v hv R hb φ hφ hc hsupp]
        have he : (∫ x, φ (1, x) * Real.log (Real.cosh x)) =
            ∫ x, Real.log (Real.cosh x) * φ (1, x) := by
          apply integral_congr_ae
          exact .of_forall fun x => mul_comm _ _
        rw [he]
        ring

end Paper
