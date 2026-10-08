module

public import Paper.ParisiPDE
public import Mathlib.Topology.Order.Monotone
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Continuity of the concrete Parisi gradient Duhamel operator

A fixed unit time interval separates the integrable `r⁻¹ᐟ²` heat singularity
from the length of the physical time interval.  The CDF can have jumps:
monotonicity makes the exceptional normalized times countable, which is
sufficient for dominated convergence.  At the terminal time the square-root
length factor proves continuity directly.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Paper

/-- Gaussian first-moment averaging of the square of a bounded gradient. -/
noncomputable def parisiGradientGaussianAverage (v : ℝ × ℝ → ℝ)
    (s x ell : ℝ) : ℝ :=
  gaussianExpectation (fun z => z * v (s, x + Real.sqrt ell * z) ^ 2)

theorem norm_parisiGradientGaussianAverage_le (v : ℝ × ℝ → ℝ)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (s x ell : ℝ) :
    ‖parisiGradientGaussianAverage v s x ell‖ ≤ gaussianAbsMoment * R ^ 2 := by
  have h := norm_integral_le_of_norm_le (μ := gaussianReal 0 1)
    (f := fun z : ℝ => z * v (s, x + Real.sqrt ell * z) ^ 2)
    (integrable_standardGaussian_id.norm.mul_const (R ^ 2))
    (Filter.Eventually.of_forall fun z : ℝ => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hb _) 2) (norm_nonneg z))
  simpa [parisiGradientGaussianAverage, gaussianExpectation, gaussianAbsMoment,
    integral_mul_const] using h

theorem continuous_parisiGradientGaussianAverage (v : ℝ × ℝ → ℝ)
    (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) :
    Continuous (fun p : ℝ × ℝ × ℝ => parisiGradientGaussianAverage v p.1 p.2.1 p.2.2) := by
  apply continuous_of_dominated (μ := gaussianReal 0 1)
    (F := fun (p : ℝ × ℝ × ℝ) (z : ℝ) => z * v (p.1, p.2.1 + Real.sqrt p.2.2 * z) ^ 2)
    (bound := fun z : ℝ => ‖z‖ * R ^ 2)
  · intro p
    have hc : Continuous (fun z : ℝ => (p.1, p.2.1 + Real.sqrt p.2.2 * z)) := by fun_prop
    exact (continuous_id.mul ((hv.comp hc).pow 2)).aestronglyMeasurable
  · intro p
    filter_upwards with z
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hb _) 2) (norm_nonneg z)
  · exact integrable_standardGaussian_id.norm.mul_const (R ^ 2)
  · filter_upwards with z
    have hc : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1 + Real.sqrt p.2.2 * z)) := by fun_prop
    exact continuous_const.mul ((hv.comp hc).pow 2)

noncomputable def parisiNormalizedGradientSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x r : ℝ) : ℝ :=
  parisiCDF μ (t + (b - t) * r) * (Real.sqrt r)⁻¹ *
    parisiGradientGaussianAverage v (t + (b - t) * r) x (β ^ 2 * ((b - t) * r))

theorem parisiNormalizedGradientSource_measurable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) : Measurable (parisiNormalizedGradientSource β μ v b t x) := by
  have hm := (parisiCDF_measurable μ).comp
    (show Measurable (fun r : ℝ => t + (b - t) * r) by fun_prop)
  have hg := (continuous_parisiGradientGaussianAverage v hv R hb).comp
    (show Continuous (fun r : ℝ => (t + (b - t) * r, x, β ^ 2 * ((b - t) * r))) by fun_prop)
  exact (hm.mul (by fun_prop)).mul hg.measurable

theorem norm_parisiNormalizedGradientSource_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b t x r : ℝ) :
    ‖parisiNormalizedGradientSource β μ v b t x r‖ ≤
      (gaussianAbsMoment * R ^ 2) * (Real.sqrt r)⁻¹ := by
  have hm : ‖parisiCDF μ (t + (b - t) * r)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ _)]
    exact parisiCDF_le_one μ _
  unfold parisiNormalizedGradientSource
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    ‖parisiCDF μ (t + (b - t) * r)‖ * (Real.sqrt r)⁻¹ *
      ‖parisiGradientGaussianAverage v (t + (b - t) * r) x (β ^ 2 * ((b - t) * r))‖ ≤
        (1 * (Real.sqrt r)⁻¹) * (gaussianAbsMoment * R ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hm (by positivity))
            (norm_parisiGradientGaussianAverage_le v R hb _ _ _) (norm_nonneg _) (by positivity)
    _ = (gaussianAbsMoment * R ^ 2) * (Real.sqrt r)⁻¹ := by ring

theorem parisiNormalizedGradientSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) :
    IntervalIntegrable (parisiNormalizedGradientSource β μ v b t x) volume 0 1 := by
  have hi : IntervalIntegrable (fun r : ℝ => (Real.sqrt r)⁻¹) volume 0 1 := by
    simpa using intervalIntegrable_inv_sqrt_sub 0 1 (by norm_num)
  exact (hi.const_mul (gaussianAbsMoment * R ^ 2)).mono_fun'
    (parisiNormalizedGradientSource_measurable β μ v hv R hb b t x).aestronglyMeasurable
    (.of_forall (norm_parisiNormalizedGradientSource_le β μ v R hb b t x))

/-- Unit-interval expression of the nonlinear heat-gradient correction. -/
noncomputable def parisiNormalizedGradientCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) : ℝ :=
  |β| * Real.sqrt (b - t) / 2 * ∫ r in (0 : ℝ)..1,
    parisiNormalizedGradientSource β μ v b t x r

theorem norm_parisiNormalizedGradientCorrection_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b t x : ℝ) :
    ‖parisiNormalizedGradientCorrection β μ v b t x‖ ≤
      |β| * gaussianAbsMoment * R ^ 2 * Real.sqrt (b - t) := by
  have hi : IntervalIntegrable (fun r : ℝ => (Real.sqrt r)⁻¹) volume 0 1 := by
    simpa using intervalIntegrable_inv_sqrt_sub 0 1 (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) (.of_forall fun r _ => norm_parisiNormalizedGradientSource_le β μ v R hb b t x r)
    (hi.const_mul (gaussianAbsMoment * R ^ 2))
  rw [intervalIntegral.integral_const_mul] at h
  have hr : (∫ r in (0 : ℝ)..1, (Real.sqrt r)⁻¹) = 2 := by
    simpa using integral_inv_sqrt_sub 0 1 (by norm_num)
  rw [hr] at h
  unfold parisiNormalizedGradientCorrection
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem continuousAt_parisiNormalizedGradientIntegral (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b : ℝ) (p : ℝ × ℝ) (ht : p.1 < b) :
    ContinuousAt (fun q : ℝ × ℝ => ∫ r in (0 : ℝ)..1,
      parisiNormalizedGradientSource β μ v b q.1 q.2 r) p := by
  have hi : IntervalIntegrable (fun r : ℝ => (Real.sqrt r)⁻¹) volume 0 1 := by
    simpa using intervalIntegrable_inv_sqrt_sub 0 1 (by norm_num)
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun r : ℝ => (gaussianAbsMoment * R ^ 2) * (Real.sqrt r)⁻¹)
  · exact .of_forall fun q =>
      (parisiNormalizedGradientSource_measurable β μ v hv R hb b q.1 q.2).aestronglyMeasurable
  · exact .of_forall fun q => .of_forall fun r _ =>
      norm_parisiNormalizedGradientSource_le β μ v R hb b q.1 q.2 r
  · exact hi.const_mul (gaussianAbsMoment * R ^ 2)
  · have hinj : Function.Injective (fun r : ℝ => p.1 + (b - p.1) * r) := by
      intro r s hrs
      nlinarith
    have hc := ((parisiCDF_monotone μ).countable_not_continuousAt.preimage hinj).ae_notMem volume
    filter_upwards [hc] with r hr _
    have hm : ContinuousAt (fun q : ℝ × ℝ => parisiCDF μ (q.1 + (b - q.1) * r)) p :=
      (show ContinuousAt (parisiCDF μ) (p.1 + (b - p.1) * r) from by
        simpa using hr).comp (f := fun q : ℝ × ℝ => q.1 + (b - q.1) * r) (show ContinuousAt
          (fun q : ℝ × ℝ => q.1 + (b - q.1) * r) p by fun_prop)
    have hg := (continuous_parisiGradientGaussianAverage v hv R hb).continuousAt.comp
      (show ContinuousAt (fun q : ℝ × ℝ =>
        (q.1 + (b - q.1) * r, q.2, β ^ 2 * ((b - q.1) * r))) p by fun_prop)
    exact (hm.mul continuousAt_const).mul hg

/-- The actual normalized nonlinear correction is jointly continuous,
including time one and CDF jump times. -/
theorem continuous_parisiNormalizedGradientCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b : ℝ) :
    Continuous (fun p : ℝ × ℝ => parisiNormalizedGradientCorrection β μ v b p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases ht : p.1 < b
  · exact (show ContinuousAt (fun q : ℝ × ℝ => |β| * Real.sqrt (b - q.1) / 2) p by
      fun_prop).mul (continuousAt_parisiNormalizedGradientIntegral β μ v hv R hb b p ht)
  · have hs : Real.sqrt (b - p.1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have he : parisiNormalizedGradientCorrection β μ v b p.1 p.2 = 0 := by
      simp [parisiNormalizedGradientCorrection, hs]
    rw [ContinuousAt, he]
    apply squeeze_zero_norm (fun q : ℝ × ℝ =>
      norm_parisiNormalizedGradientCorrection_le β μ v R hb b q.1 q.2)
    have hh : ContinuousAt (fun q : ℝ × ℝ =>
      |β| * gaussianAbsMoment * R ^ 2 * Real.sqrt (b - q.1)) p := by fun_prop
    simpa [hs] using hh.tendsto

private theorem parisi_gradient_scale_identity (β δ r : ℝ) (hδ : 0 ≤ δ) :
    β ^ 2 / 2 * δ * (Real.sqrt (β ^ 2 * (δ * r)))⁻¹ =
      |β| * Real.sqrt δ / 2 * (Real.sqrt r)⁻¹ := by
  have hβ : β ^ 2 * |β|⁻¹ = |β| := by
    by_cases hb : β = 0
    · simp [hb]
    · have hb' : |β| ≠ 0 := abs_ne_zero.mpr hb
      rw [← sq_abs β]
      field_simp
  have hd : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
    by_cases hz : δ = 0
    · simp [hz]
    · have hs : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hδ (Ne.symm hz))).ne'
      rw [← div_eq_mul_inv]
      exact (div_eq_iff hs).mpr (Real.mul_self_sqrt hδ).symm
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs,
    Real.sqrt_mul hδ, mul_inv_rev, mul_inv_rev]
  calc
    β ^ 2 / 2 * δ * ((Real.sqrt r)⁻¹ * (Real.sqrt δ)⁻¹ * |β|⁻¹) =
      (β ^ 2 * |β|⁻¹) * (δ * (Real.sqrt δ)⁻¹) / 2 * (Real.sqrt r)⁻¹ := by ring
    _ = |β| * Real.sqrt δ / 2 * (Real.sqrt r)⁻¹ := by rw [hβ, hd]

/-- Normalizing time preserves the genuine gradient Duhamel integral.
This identity requires no smoothness or measurability assumption on `v`. -/
theorem parisiNormalizedGradientCorrection_eq (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) (htb : t ≤ b) :
    parisiNormalizedGradientCorrection β μ v b t x =
      parisiGradientCorrection β μ v b t x := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (f := parisiGradientSource β μ v t x) (a := (0 : ℝ)) (b := 1) (b - t) t
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at he
  unfold parisiGradientCorrection
  rw [← he, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  unfold parisiNormalizedGradientCorrection
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
  unfold parisiNormalizedGradientSource parisiGradientSource heatGradient
    parisiGradientGaussianAverage
  dsimp only
  have htime : t + (b - t) * r - t = (b - t) * r := by ring
  rw [htime]
  have hs := parisi_gradient_scale_identity β (b - t) r (sub_nonneg.mpr htb)
  calc
    |β| * Real.sqrt (b - t) / 2 * (parisiCDF μ (t + (b - t) * r) * (Real.sqrt r)⁻¹ *
      gaussianExpectation (fun z => z * v (t + (b - t) * r,
        x + Real.sqrt (β ^ 2 * ((b - t) * r)) * z) ^ 2)) =
      (|β| * Real.sqrt (b - t) / 2 * (Real.sqrt r)⁻¹) *
        parisiCDF μ (t + (b - t) * r) *
          gaussianExpectation (fun z => z * v (t + (b - t) * r,
            x + Real.sqrt (β ^ 2 * ((b - t) * r)) * z) ^ 2) := by ring
    _ = β ^ 2 / 2 * ((b - t) * (parisiCDF μ (t + (b - t) * r) *
      ((Real.sqrt (β ^ 2 * ((b - t) * r)))⁻¹ * gaussianExpectation
        (fun z => z * v (t + (b - t) * r,
          x + Real.sqrt (β ^ 2 * ((b - t) * r)) * z) ^ 2)))) := by rw [← hs]; ring

theorem continuousOn_parisiGradientCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => parisiGradientCorrection β μ v b p.1 p.2)
      {p : ℝ × ℝ | p.1 ≤ b} := by
  apply (continuous_parisiNormalizedGradientCorrection β μ v hv R hb b).continuousOn.congr
  intro p hp
  exact (parisiNormalizedGradientCorrection_eq β μ v b p.1 p.2 hp).symm

end Paper
