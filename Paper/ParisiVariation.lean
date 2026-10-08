module

public import Paper.ParisiMeasureStability
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

/-!
# Linearizing the actual local Parisi Duhamel fixed point

The linear operator below is obtained from the genuine Gaussian quadratic
operator by polarization. Its integral representation and operator norm are
proved before it is used to linearize a probability mixing variation.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

noncomputable def parisiSlabQuadraticOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) : ParisiSlabGradient a b :=
  parisiSlabGradientOperator β μ hab (fun _ => 0) continuous_const (by simp) v

@[simp] theorem parisiSlabQuadraticOperator_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (p : Icc a b × ℝ) :
    parisiSlabQuadraticOperator β μ hab v p =
      parisiNormalizedGradientCorrection β μ (parisiSlabExtend hab v) b p.1 p.2 := by
  change heatSemigroup (β ^ 2 * (b - p.1)) (fun _ => 0) p.2 + _ = _
  simp [heatSemigroup, gaussianExpectation]

/-- Polarization yields the linear Gaussian-gradient averaging operator. -/
noncomputable def parisiSlabLinearValue (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) : ParisiSlabGradient a b :=
  (1 / 4 : ℝ) • (parisiSlabQuadraticOperator β μ hab (v + 1) -
    parisiSlabQuadraticOperator β μ hab (v - 1))

noncomputable def parisiLinearGaussianAverage (v : ℝ × ℝ → ℝ) (s x ell : ℝ) : ℝ :=
  gaussianExpectation (fun z => z * v (s, x + Real.sqrt ell * z))

theorem integrable_parisiLinearGaussianAverage (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (s x ell : ℝ) :
    Integrable (fun z : ℝ => z * v (s, x + Real.sqrt ell * z)) (gaussianReal 0 1) :=
  integrable_heatGradient_integrand ell (fun y => v (s, y))
    (hv.comp (by fun_prop)) R (fun y => hb _) x

theorem norm_parisiLinearGaussianAverage_le (v : ℝ × ℝ → ℝ)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (s x ell : ℝ) :
    ‖parisiLinearGaussianAverage v s x ell‖ ≤ gaussianAbsMoment * R := by
  have h := norm_integral_le_of_norm_le (μ := gaussianReal 0 1)
    (f := fun z : ℝ => z * v (s, x + Real.sqrt ell * z))
    (integrable_standardGaussian_id.norm.mul_const R)
    (Filter.Eventually.of_forall fun z : ℝ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg z))
  simpa [parisiLinearGaussianAverage, gaussianExpectation, gaussianAbsMoment,
    integral_mul_const] using h

private theorem parisiLinearGaussianAverage_polarization (v : ℝ × ℝ → ℝ)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (s x ell : ℝ) :
    (1 / 4 : ℝ) * (parisiGradientGaussianAverage (fun p => v p + 1) s x ell -
      parisiGradientGaussianAverage (fun p => v p - 1) s x ell) =
      parisiLinearGaussianAverage v s x ell := by
  have hplus : ∀ y : ℝ, ‖(v (s, y) + 1) ^ 2‖ ≤ (R + 1) ^ 2 := by
    intro y
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hb (s, y)) 1)
  have hminus : ∀ y : ℝ, ‖(v (s, y) - 1) ^ 2‖ ≤ (R + 1) ^ 2 := by
    intro y
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_right (hb (s, y)) 1)
  have hi := integrable_heatGradient_integrand ell (fun y => (v (s, y) + 1) ^ 2)
    ((hv.comp (by fun_prop)).add_const 1 |>.pow_const 2) ((R + 1) ^ 2) hplus x
  have hj := integrable_heatGradient_integrand ell (fun y => (v (s, y) - 1) ^ 2)
    ((hv.comp (by fun_prop)).sub_const 1 |>.pow_const 2) ((R + 1) ^ 2) hminus x
  unfold parisiGradientGaussianAverage parisiLinearGaussianAverage gaussianExpectation
  rw [← integral_sub hi hj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  ring

noncomputable def parisiLinearNormalizedSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x r : ℝ) : ℝ :=
  parisiCDF μ (t + (b - t) * r) * (Real.sqrt r)⁻¹ *
    parisiLinearGaussianAverage v (t + (b - t) * r) x (β ^ 2 * ((b - t) * r))

private theorem parisiLinearNormalizedSource_polarization (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x r : ℝ) :
    parisiLinearNormalizedSource β μ v b t x r =
      (1 / 4 : ℝ) * (parisiNormalizedGradientSource β μ (fun p => v p + 1) b t x r -
        parisiNormalizedGradientSource β μ (fun p => v p - 1) b t x r) := by
  unfold parisiLinearNormalizedSource parisiNormalizedGradientSource
  rw [← parisiLinearGaussianAverage_polarization v hv R hb]
  ring

theorem parisiLinearNormalizedSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) : IntervalIntegrable (parisiLinearNormalizedSource β μ v b t x) volume 0 1 := by
  have hp : ∀ p, ‖v p + 1‖ ≤ R + 1 := fun p =>
    (norm_add_le _ _).trans (by simpa using add_le_add_right (hb p) 1)
  have hm : ∀ p, ‖v p - 1‖ ≤ R + 1 := fun p =>
    (norm_sub_le _ _).trans (by simpa using add_le_add_right (hb p) 1)
  have hi := parisiNormalizedGradientSource_intervalIntegrable β μ (fun p => v p + 1)
    (hv.add continuous_const) (R + 1) hp b t x
  have hj := parisiNormalizedGradientSource_intervalIntegrable β μ (fun p => v p - 1)
    (hv.sub continuous_const) (R + 1) hm b t x
  have heq : (parisiLinearNormalizedSource β μ v b t x) =
      fun r => (1 / 4 : ℝ) * (parisiNormalizedGradientSource β μ (fun p => v p + 1) b t x r -
        parisiNormalizedGradientSource β μ (fun p => v p - 1) b t x r) :=
    funext (parisiLinearNormalizedSource_polarization β μ v hv.measurable R hb b t x)
  rw [heq]
  exact (hi.sub hj).const_mul _

/-- The polarized value is the genuine linear Gaussian time-integral operator. -/
theorem parisiSlabLinearValue_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (p : Icc a b × ℝ) :
    parisiSlabLinearValue β μ hab v p =
      |β| * Real.sqrt (b - (p.1 : ℝ)) / 2 *
        ∫ r in (0 : ℝ)..1,
          parisiLinearNormalizedSource β μ (parisiSlabExtend hab v) b p.1 p.2 r := by
  have hp : ∀ q, ‖parisiSlabExtend hab v q + 1‖ ≤ ‖v‖ + 1 := fun q =>
    (norm_add_le _ _).trans (by simpa using add_le_add_right (norm_parisiSlabExtend_le hab v q) 1)
  have hm : ∀ q, ‖parisiSlabExtend hab v q - 1‖ ≤ ‖v‖ + 1 := fun q =>
    (norm_sub_le _ _).trans (by simpa using add_le_add_right (norm_parisiSlabExtend_le hab v q) 1)
  have hi := parisiNormalizedGradientSource_intervalIntegrable β μ
    (fun q => parisiSlabExtend hab v q + 1)
    ((continuous_parisiSlabExtend hab v).add continuous_const) (‖v‖ + 1) hp b p.1 p.2
  have hj := parisiNormalizedGradientSource_intervalIntegrable β μ
    (fun q => parisiSlabExtend hab v q - 1)
    ((continuous_parisiSlabExtend hab v).sub continuous_const) (‖v‖ + 1) hm b p.1 p.2
  change (1 / 4 : ℝ) * (parisiSlabQuadraticOperator β μ hab (v + 1) p -
    parisiSlabQuadraticOperator β μ hab (v - 1) p) = _
  rw [parisiSlabQuadraticOperator_apply, parisiSlabQuadraticOperator_apply]
  have heplus : parisiSlabExtend hab (v + 1) = fun q => parisiSlabExtend hab v q + 1 := rfl
  have heminus : parisiSlabExtend hab (v - 1) = fun q => parisiSlabExtend hab v q - 1 := rfl
  rw [heplus, heminus]
  unfold parisiNormalizedGradientCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj]
  simp_rw [parisiLinearNormalizedSource_polarization β μ (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v).measurable ‖v‖ (norm_parisiSlabExtend_le hab v)]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem norm_parisiLinearNormalizedSource_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b t x r : ℝ) :
    ‖parisiLinearNormalizedSource β μ v b t x r‖ ≤
      (gaussianAbsMoment * R) * (Real.sqrt r)⁻¹ := by
  have hm : ‖parisiCDF μ (t + (b - t) * r)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ _)]
    exact parisiCDF_le_one μ _
  unfold parisiLinearNormalizedSource
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (1 * (Real.sqrt r)⁻¹) * (gaussianAbsMoment * R) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm (by positivity))
        (norm_parisiLinearGaussianAverage_le v R hb _ _ _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The actual linear Gaussian time operator has the explicit slab norm bound. -/
theorem norm_parisiSlabLinearValue_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) :
    ‖parisiSlabLinearValue β μ hab v‖ ≤ parisiSlabContractionConstant β a b * ‖v‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (parisiSlabContractionConstant_nonneg β a b) (norm_nonneg v))).mpr
  intro p
  rw [parisiSlabLinearValue_apply]
  have hik : IntervalIntegrable (fun r : ℝ => (Real.sqrt r)⁻¹) volume 0 1 := by
    simpa using intervalIntegrable_inv_sqrt_sub 0 1 (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) (.of_forall fun r _ => norm_parisiLinearNormalizedSource_le β μ
      (parisiSlabExtend hab v) ‖v‖ (norm_parisiSlabExtend_le hab v) b p.1 p.2 r)
    (hik.const_mul (gaussianAbsMoment * ‖v‖))
  rw [intervalIntegral.integral_const_mul] at h
  have hkernel : (∫ r in (0 : ℝ)..1, (Real.sqrt r)⁻¹) = 2 := by
    simpa using integral_inv_sqrt_sub 0 1 (by norm_num)
  rw [hkernel] at h
  have hs : Real.sqrt (b - (p.1 : ℝ)) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (sub_le_sub_left p.1.property.1 b)
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ |β| * Real.sqrt (b - (p.1 : ℝ)) / 2 * (gaussianAbsMoment * ‖v‖ * 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (|β| * gaussianAbsMoment * ‖v‖) * Real.sqrt (b - (p.1 : ℝ)) := by ring
    _ ≤ (|β| * gaussianAbsMoment * ‖v‖) * Real.sqrt (b - a) :=
      mul_le_mul_of_nonneg_left hs (by have := gaussianAbsMoment_nonneg; positivity)
    _ = _ := by unfold parisiSlabContractionConstant; ring

private theorem parisiLinearGaussianAverage_add (v w : ℝ × ℝ → ℝ)
    (hv : Measurable v) (hw : Measurable w) (R S : ℝ)
    (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ S) (s x ell : ℝ) :
    parisiLinearGaussianAverage (fun p => v p + w p) s x ell =
      parisiLinearGaussianAverage v s x ell + parisiLinearGaussianAverage w s x ell := by
  have hi := integrable_parisiLinearGaussianAverage v hv R hvb s x ell
  have hj := integrable_parisiLinearGaussianAverage w hw S hwb s x ell
  unfold parisiLinearGaussianAverage gaussianExpectation
  simp_rw [mul_add]
  exact integral_add hi hj

private theorem parisiLinearGaussianAverage_smul (v : ℝ × ℝ → ℝ)
    (c s x ell : ℝ) :
    parisiLinearGaussianAverage (fun p => c * v p) s x ell =
      c * parisiLinearGaussianAverage v s x ell := by
  unfold parisiLinearGaussianAverage gaussianExpectation
  simp_rw [show ∀ z : ℝ, z * (c * v (s, x + Real.sqrt ell * z)) =
    c * (z * v (s, x + Real.sqrt ell * z)) by intro z; ring]
  exact integral_const_mul _ _

theorem parisiSlabLinearValue_add (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    parisiSlabLinearValue β μ hab (v + w) =
      parisiSlabLinearValue β μ hab v + parisiSlabLinearValue β μ hab w := by
  ext p
  rw [BoundedContinuousFunction.add_apply, parisiSlabLinearValue_apply,
    parisiSlabLinearValue_apply, parisiSlabLinearValue_apply]
  have he : parisiSlabExtend hab (v + w) = fun q =>
      parisiSlabExtend hab v q + parisiSlabExtend hab w q := rfl
  rw [he]
  have hi := parisiLinearNormalizedSource_intervalIntegrable β μ (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v) ‖v‖ (norm_parisiSlabExtend_le hab v) b p.1 p.2
  have hj := parisiLinearNormalizedSource_intervalIntegrable β μ (parisiSlabExtend hab w)
    (continuous_parisiSlabExtend hab w) ‖w‖ (norm_parisiSlabExtend_le hab w) b p.1 p.2
  have hsource : parisiLinearNormalizedSource β μ
      (fun q => parisiSlabExtend hab v q + parisiSlabExtend hab w q) b p.1 p.2 =
      fun r => parisiLinearNormalizedSource β μ (parisiSlabExtend hab v) b p.1 p.2 r +
        parisiLinearNormalizedSource β μ (parisiSlabExtend hab w) b p.1 p.2 r := by
    funext r
    unfold parisiLinearNormalizedSource
    rw [parisiLinearGaussianAverage_add _ _ (continuous_parisiSlabExtend hab v).measurable
      (continuous_parisiSlabExtend hab w).measurable ‖v‖ ‖w‖
      (norm_parisiSlabExtend_le hab v) (norm_parisiSlabExtend_le hab w)]
    ring
  rw [hsource, intervalIntegral.integral_add hi hj]
  ring

theorem parisiSlabLinearValue_smul (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) (v : ParisiSlabGradient a b) :
    parisiSlabLinearValue β μ hab (c • v) = c • parisiSlabLinearValue β μ hab v := by
  ext p
  rw [BoundedContinuousFunction.smul_apply, parisiSlabLinearValue_apply, parisiSlabLinearValue_apply]
  have he : parisiSlabExtend hab (c • v) = fun q => c * parisiSlabExtend hab v q := rfl
  rw [he]
  have hsource : parisiLinearNormalizedSource β μ
      (fun q => c * parisiSlabExtend hab v q) b p.1 p.2 =
      fun r => c * parisiLinearNormalizedSource β μ (parisiSlabExtend hab v) b p.1 p.2 r := by
    funext r
    unfold parisiLinearNormalizedSource
    rw [parisiLinearGaussianAverage_smul]
    ring
  rw [hsource, intervalIntegral.integral_const_mul]
  change _ = c * _
  ring

/-- The actual Gaussian-gradient Duhamel linear operator on the complete slab space. -/
noncomputable def parisiSlabLinearOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) : ParisiSlabGradient a b →L[ℝ] ParisiSlabGradient a b :=
  LinearMap.mkContinuous
    { toFun := parisiSlabLinearValue β μ hab
      map_add' := parisiSlabLinearValue_add β μ hab
      map_smul' := parisiSlabLinearValue_smul β μ hab }
    (parisiSlabContractionConstant β a b) (norm_parisiSlabLinearValue_le β μ hab)

@[simp] theorem parisiSlabLinearOperator_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) :
    parisiSlabLinearOperator β μ hab v = parisiSlabLinearValue β μ hab v := rfl

noncomputable def parisiSlabBilinearMap (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) :
    ParisiSlabGradient a b →ₗ[ℝ] ParisiSlabGradient a b →ₗ[ℝ] ParisiSlabGradient a b :=
  LinearMap.mk₂ ℝ (fun v w => parisiSlabLinearOperator β μ hab (v * w))
    (fun v₁ v₂ w => by rw [add_mul, map_add])
    (fun c v w => by rw [smul_mul_assoc, map_smul])
    (fun v w₁ w₂ => by rw [mul_add, map_add])
    (fun c v w => by rw [mul_smul_comm, map_smul])

theorem norm_parisiSlabBilinearMap_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    ‖parisiSlabBilinearMap β μ hab v w‖ ≤
      parisiSlabContractionConstant β a b * ‖v‖ * ‖w‖ := by
  change ‖parisiSlabLinearValue β μ hab (v * w)‖ ≤ _
  refine (norm_parisiSlabLinearValue_le β μ hab (v * w)).trans ?_
  exact (mul_le_mul_of_nonneg_left (norm_mul_le v w)
    (parisiSlabContractionConstant_nonneg β a b)).trans_eq (by ring)

/-- The actual quadratic Duhamel correction is represented by a bounded symmetric bilinear map. -/
noncomputable def parisiSlabBilinearOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) :
    ParisiSlabGradient a b →L[ℝ] ParisiSlabGradient a b →L[ℝ] ParisiSlabGradient a b :=
  (parisiSlabBilinearMap β μ hab).mkContinuous₂
    (parisiSlabContractionConstant β a b) (norm_parisiSlabBilinearMap_le β μ hab)

@[simp] theorem parisiSlabBilinearOperator_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    parisiSlabBilinearOperator β μ hab v w = parisiSlabLinearOperator β μ hab (v * w) := rfl

theorem norm_parisiSlabBilinearOperator_apply_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    ‖parisiSlabBilinearOperator β μ hab v w‖ ≤
      parisiSlabContractionConstant β a b * ‖v‖ * ‖w‖ :=
  norm_parisiSlabBilinearMap_le β μ hab v w

theorem parisiSlabBilinearOperator_symm (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    parisiSlabBilinearOperator β μ hab v w = parisiSlabBilinearOperator β μ hab w v := by
  simp only [parisiSlabBilinearOperator_apply, mul_comm]

theorem parisiSlabQuadraticOperator_eq_bilinear (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) :
    parisiSlabQuadraticOperator β μ hab v = parisiSlabBilinearOperator β μ hab v v := by
  ext p
  rw [parisiSlabQuadraticOperator_apply, parisiSlabBilinearOperator_apply,
    parisiSlabLinearOperator_apply, parisiSlabLinearValue_apply]
  unfold parisiNormalizedGradientCorrection parisiNormalizedGradientSource
    parisiLinearNormalizedSource parisiGradientGaussianAverage parisiLinearGaussianAverage
  simp only [parisiSlabExtend, BoundedContinuousFunction.mul_apply, pow_two]

theorem parisiSlabLinearValue_mix (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (ε : ℝ)
    (hε : ε ∈ Icc (0 : ℝ) 1) :
    parisiSlabLinearValue β (parisiMix μ ν ε) hab v =
      (1 - ε) • parisiSlabLinearValue β μ hab v + ε • parisiSlabLinearValue β ν hab v := by
  ext p
  rw [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.smul_apply, parisiSlabLinearValue_apply,
    parisiSlabLinearValue_apply, parisiSlabLinearValue_apply]
  have hi := parisiLinearNormalizedSource_intervalIntegrable β μ (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v) ‖v‖ (norm_parisiSlabExtend_le hab v) b p.1 p.2
  have hj := parisiLinearNormalizedSource_intervalIntegrable β ν (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v) ‖v‖ (norm_parisiSlabExtend_le hab v) b p.1 p.2
  have hsource : parisiLinearNormalizedSource β (parisiMix μ ν ε) (parisiSlabExtend hab v) b p.1 p.2 =
      fun r => (1 - ε) * parisiLinearNormalizedSource β μ (parisiSlabExtend hab v) b p.1 p.2 r +
        ε * parisiLinearNormalizedSource β ν (parisiSlabExtend hab v) b p.1 p.2 r := by
    funext r
    unfold parisiLinearNormalizedSource
    rw [parisiCDF_mix μ ν ε _ hε]
    ring
  rw [hsource, intervalIntegral.integral_add (hi.const_mul (1 - ε)) (hj.const_mul ε),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change _ = (1 - ε) * _ + ε * _
  ring

theorem parisiSlabBilinearOperator_mix_apply (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (v w : ParisiSlabGradient a b) :
    parisiSlabBilinearOperator β (parisiMix μ ν ε) hab v w =
      (1 - ε) • parisiSlabBilinearOperator β μ hab v w +
        ε • parisiSlabBilinearOperator β ν hab v w := by
  exact parisiSlabLinearValue_mix β μ ν hab (v * w) ε hε

noncomputable def parisiLinearGradientSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x s : ℝ) : ℝ :=
  parisiCDF μ s * heatGradient (β ^ 2 * (s - t)) (fun y => v (s, y)) x

private theorem parisiLinearGradientSource_polarization (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (t x s : ℝ) :
    parisiLinearGradientSource β μ v t x s = (1 / 4 : ℝ) *
      (parisiGradientSource β μ (fun p => v p + 1) t x s -
        parisiGradientSource β μ (fun p => v p - 1) t x s) := by
  unfold parisiLinearGradientSource parisiGradientSource heatGradient
  change _ * (_ * parisiLinearGaussianAverage v s x _) =
    (1 / 4 : ℝ) * (_ * (_ * parisiGradientGaussianAverage (fun p => v p + 1) s x _) -
      _ * (_ * parisiGradientGaussianAverage (fun p => v p - 1) s x _))
  rw [← parisiLinearGaussianAverage_polarization v hv R hb]
  ring

theorem parisiLinearGradientSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (t x b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (parisiLinearGradientSource β μ v t x) volume t b := by
  have hp : ∀ p, ‖v p + 1‖ ≤ R + 1 := fun p =>
    (norm_add_le _ _).trans (by simpa using add_le_add_right (hb p) 1)
  have hm : ∀ p, ‖v p - 1‖ ≤ R + 1 := fun p =>
    (norm_sub_le _ _).trans (by simpa using add_le_add_right (hb p) 1)
  have hi := parisiGradientSource_intervalIntegrable β μ (fun p => v p + 1)
    (hv.add_const 1) (R + 1) hp t x b htb
  have hj := parisiGradientSource_intervalIntegrable β μ (fun p => v p - 1)
    (hv.sub_const 1) (R + 1) hm t x b htb
  have he : parisiLinearGradientSource β μ v t x = fun s => (1 / 4 : ℝ) *
      (parisiGradientSource β μ (fun p => v p + 1) t x s -
        parisiGradientSource β μ (fun p => v p - 1) t x s) :=
    funext (parisiLinearGradientSource_polarization β μ v hv R hb t x)
  rw [he]
  exact (hi.sub hj).const_mul _

/-- The polarized operator also has the original physical-time Gaussian gradient integral. -/
theorem parisiSlabLinearValue_apply_physical (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (p : Icc a b × ℝ) :
    parisiSlabLinearValue β μ hab v p = β ^ 2 / 2 *
      ∫ s in (p.1 : ℝ)..b, parisiLinearGradientSource β μ (parisiSlabExtend hab v) p.1 p.2 s := by
  have hp : ∀ q, ‖parisiSlabExtend hab v q + 1‖ ≤ ‖v‖ + 1 := fun q =>
    (norm_add_le _ _).trans (by simpa using add_le_add_right (norm_parisiSlabExtend_le hab v q) 1)
  have hm : ∀ q, ‖parisiSlabExtend hab v q - 1‖ ≤ ‖v‖ + 1 := fun q =>
    (norm_sub_le _ _).trans (by simpa using add_le_add_right (norm_parisiSlabExtend_le hab v q) 1)
  have hi := parisiGradientSource_intervalIntegrable β μ
    (fun q => parisiSlabExtend hab v q + 1)
    ((continuous_parisiSlabExtend hab v).measurable.add_const 1) (‖v‖ + 1) hp
    p.1 p.2 b p.1.property.2
  have hj := parisiGradientSource_intervalIntegrable β μ
    (fun q => parisiSlabExtend hab v q - 1)
    ((continuous_parisiSlabExtend hab v).measurable.sub_const 1) (‖v‖ + 1) hm
    p.1 p.2 b p.1.property.2
  change (1 / 4 : ℝ) * (parisiSlabQuadraticOperator β μ hab (v + 1) p -
    parisiSlabQuadraticOperator β μ hab (v - 1) p) = _
  rw [parisiSlabQuadraticOperator_apply, parisiSlabQuadraticOperator_apply,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2]
  have heplus : parisiSlabExtend hab (v + 1) = fun q => parisiSlabExtend hab v q + 1 := rfl
  have heminus : parisiSlabExtend hab (v - 1) = fun q => parisiSlabExtend hab v q - 1 := rfl
  rw [heplus, heminus]
  unfold parisiGradientCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj]
  simp_rw [parisiLinearGradientSource_polarization β μ (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v).measurable ‖v‖ (norm_parisiSlabExtend_le hab v)]
  rw [intervalIntegral.integral_const_mul]
  ring

end Paper

