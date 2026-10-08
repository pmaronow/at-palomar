module

public import Paper.BCFTranslation
public import Paper.ParisiTerminalOperator

@[expose] public section

/-! # Genuine translation covariance and smoothness on short Parisi slabs -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff

namespace Paper

private theorem bilinearOperatorNorm_le_of_apply_le {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] X) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v w, ‖B v w‖ ≤ C * ‖v‖ * ‖w‖) : bilinearOperatorNorm B ≤ C := by
  apply B.opNorm_le_bound hC
  intro v
  exact (B v).opNorm_le_bound (mul_nonneg hC (norm_nonneg v)) (hb v)

theorem parisiSlabBilinearOperator_norm_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) :
    bilinearOperatorNorm (parisiSlabBilinearOperator β μ hab) ≤
      parisiSlabContractionConstant β a b :=
  bilinearOperatorNorm_le_of_apply_le _ (parisiSlabContractionConstant_nonneg β a b)
    (norm_parisiSlabBilinearOperator_apply_le β μ hab)

theorem parisiSlabQuadraticOperator_translate (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (ξ : ℝ) :
    bcfTranslate ξ (parisiSlabQuadraticOperator β μ hab v) =
      parisiSlabQuadraticOperator β μ hab (bcfTranslate ξ v) := by
  ext p
  rw [bcfTranslate_apply, parisiSlabQuadraticOperator_apply,
    parisiSlabQuadraticOperator_apply]
  unfold parisiNormalizedGradientCorrection parisiNormalizedGradientSource
    parisiGradientGaussianAverage gaussianExpectation
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [parisiSlabExtend, bcfTranslate_apply]
  congr 2
  congr 1
  ring_nf

theorem parisiSlabBilinearOperator_translate_diagonal (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (ξ : ℝ) :
    bcfTranslate ξ (parisiSlabBilinearOperator β μ hab v v) =
      parisiSlabBilinearOperator β μ hab (bcfTranslate ξ v) (bcfTranslate ξ v) := by
  simpa only [← parisiSlabQuadraticOperator_eq_bilinear] using
    parisiSlabQuadraticOperator_translate β μ hab v ξ

noncomputable def bcfLineTranslate (ξ : ℝ) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x + ξ, by fun_prop⟩

@[simp] theorem bcfLineTranslate_apply (ξ : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    bcfLineTranslate ξ f x = f (x + ξ) := rfl

theorem parisiSlabTerminalHeatOperator_translate (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ →ᵇ ℝ) (ξ : ℝ) :
    bcfTranslate ξ (parisiSlabTerminalHeatOperator β hab g) =
      parisiSlabTerminalHeatOperator β hab (bcfLineTranslate ξ g) := by
  ext p
  rw [bcfTranslate_apply, parisiSlabTerminalHeatOperator_apply,
    parisiSlabTerminalHeatOperator_apply]
  unfold heatSemigroup gaussianExpectation
  congr 1
  funext z
  dsimp only
  rw [bcfLineTranslate_apply]
  congr 1
  ring

noncomputable def parisiLineTanhBCF : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.tanh
    gaussian_continuous_tanh 1 (fun x => by
      rw [Real.norm_eq_abs]
      nlinarith [tanh_sq_le_one x, sq_abs (Real.tanh x), abs_nonneg (Real.tanh x)])

@[simp] theorem parisiLineTanhBCF_apply (x : ℝ) :
    parisiLineTanhBCF x = Real.tanh x := rfl

theorem parisiSlabTerminalHeatOperator_tanh (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    parisiSlabTerminalHeatOperator β hab parisiLineTanhBCF =
      tanhGaussianBCF Polynomial.X
        (fun t : Icc a b => Real.sqrt (β ^ 2 * (b - t))) (by fun_prop) := by
  ext p
  simp only [parisiSlabTerminalHeatOperator_apply, tanhGaussianBCF_apply,
    heatSemigroup, gaussianPolynomialMoment, parisiLineTanhBCF_apply,
    pow_zero, one_mul, Polynomial.eval_X]

theorem contDiff_bcfTranslate_parisiSlabTerminalTanh (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ
      (parisiSlabTerminalHeatOperator β hab parisiLineTanhBCF)) := by
  rw [parisiSlabTerminalHeatOperator_tanh]
  exact contDiff_bcfTranslate_tanhGaussian _ _ _

/-- The smoothness of terminal translations propagates through the actual
short-slab nonlinear Gaussian operator. -/
theorem contDiff_bcfTranslate_parisiSlab_fixedPoint (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ →ᵇ ℝ) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) {K : ℝ≥0}
    (hvL : ∀ t, LipschitzWith K (fun x => v (t, x)))
    (hgSmooth : ContDiff ℝ ∞ (fun ξ => bcfLineTranslate ξ g))
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (hfix : parisiSlabGradientOperator β μ hab g g.continuous hgb v = v) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v) := by
  apply contDiff_bcfTranslate_quadratic_fixedPoint
    (parisiSlabBilinearOperator β μ hab) (parisiSlabTerminalHeatOperator β hab g) v
  · have h := (parisiSlabTerminalHeatOperator β hab).contDiff.comp hgSmooth
    simpa only [Function.comp_def, ← parisiSlabTerminalHeatOperator_translate] using h
  · exact hvL
  · rw [parisiSlabGradientOperator_eq_terminalHeat_add_quadratic,
      parisiSlabQuadraticOperator_eq_bilinear] at hfix
    exact hfix.symm
  · exact parisiSlabBilinearOperator_translate_diagonal β μ hab v
  · have hb := parisiSlabBilinearOperator_norm_le β μ hab
    have hprod := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    have hprod' := mul_le_mul_of_nonneg_right hshort (norm_nonneg v)
    nlinarith [norm_nonneg v]

end Paper
