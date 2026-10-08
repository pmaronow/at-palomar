module

public import Paper.HeatGradient
public import Paper.ParisiLocal

@[expose] public section

/-! # The local gradient fixed point is the actual gradient of its potential

Gaussian smoothing differentiates the bounded measurable nonlinear source.
Its `1/√(s-t)` derivative bound is integrable in time, so dominated
differentiation identifies the mild gradient with the spatial derivative of
the genuine potential Duhamel formula.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Paper

theorem lipschitzWith_logcosh :
    LipschitzWith 1 (fun x : ℝ => Real.log (Real.cosh x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_log_cosh x).differentiableAt)
  intro x
  rw [(hasDerivAt_log_cosh x).deriv]
  exact_mod_cast (Real.abs_tanh_lt_one x).le

theorem norm_logcosh_le_abs (x : ℝ) : ‖Real.log (Real.cosh x)‖ ≤ |x| := by
  have h := lipschitzWith_logcosh.dist_le_mul x 0
  simpa [Real.dist_eq, dist_eq_norm] using h

theorem continuous_heatSemigroup_logcosh :
    Continuous (fun p : ℝ × ℝ => heatSemigroup p.2 (fun y => Real.log (Real.cosh y)) p.1) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  apply continuousAt_of_dominated (μ := gaussianReal 0 1)
    (F := fun (p : ℝ × ℝ) (z : ℝ) => Real.log (Real.cosh (p.1 + Real.sqrt p.2 * z)))
    (bound := fun z => |p₀.1| + 1 + Real.sqrt (|p₀.2| + 1) * ‖z‖)
  · exact .of_forall fun p =>
      (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => (Real.cosh_pos _).ne')
        |>.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds p₀ (by norm_num : (0 : ℝ) < 1)] with p hp
    have hdist : max |p.1 - p₀.1| |p.2 - p₀.2| < 1 := by
      simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using hp
    have hx : |p.1| ≤ |p₀.1| + 1 := by
      have htri := abs_add_le (p.1 - p₀.1) p₀.1
      have hsmall := (max_lt_iff.mp hdist).1
      rw [sub_add_cancel] at htri
      linarith
    have ht : p.2 ≤ |p₀.2| + 1 := by
      have hsmall := (max_lt_iff.mp hdist).2
      have := le_abs_self (p.2 - p₀.2)
      have := le_abs_self p₀.2
      linarith
    exact .of_forall fun z => (norm_logcosh_le_abs _).trans <|
      (abs_add_le _ _).trans <| by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), ← Real.norm_eq_abs]
        exact add_le_add hx (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht) (norm_nonneg z))
  · exact (integrable_const (|p₀.1| + 1)).add
      (integrable_standardGaussian_id.norm.const_mul (Real.sqrt (|p₀.2| + 1)))
  · exact .of_forall fun z =>
      (show Continuous (fun p : ℝ × ℝ => Real.log (Real.cosh (p.1 + Real.sqrt p.2 * z))) by
        exact (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => (Real.cosh_pos _).ne')).continuousAt

noncomputable def parisiSourceGaussianAverage (v : ℝ × ℝ → ℝ) (s x ell : ℝ) : ℝ :=
  heatSemigroup ell (fun y => v (s, y) ^ 2) x

theorem norm_parisiSourceGaussianAverage_le (v : ℝ × ℝ → ℝ)
    (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (s x ell : ℝ) :
    ‖parisiSourceGaussianAverage v s x ell‖ ≤ R ^ 2 := by
  apply norm_heatSemigroup_le
  intro y
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2

theorem continuous_parisiSourceGaussianAverage (v : ℝ × ℝ → ℝ)
    (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) :
    Continuous (fun p : ℝ × ℝ × ℝ => parisiSourceGaussianAverage v p.1 p.2.1 p.2.2) := by
  apply continuous_of_dominated (μ := gaussianReal 0 1)
    (F := fun (p : ℝ × ℝ × ℝ) (z : ℝ) => v (p.1, p.2.1 + Real.sqrt p.2.2 * z) ^ 2)
    (bound := fun _ => R ^ 2)
  · intro p
    have hc : Continuous (fun z : ℝ => (p.1, p.2.1 + Real.sqrt p.2.2 * z)) := by fun_prop
    exact ((hv.comp hc).pow 2).aestronglyMeasurable
  · intro p
    exact .of_forall fun z => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  · exact integrable_const _
  · exact .of_forall fun z => (hv.comp
      (show Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1 + Real.sqrt p.2.2 * z)) by fun_prop)).pow 2

noncomputable def parisiNormalizedHeatSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x r : ℝ) : ℝ :=
  parisiCDF μ (t + (b - t) * r) *
    parisiSourceGaussianAverage v (t + (b - t) * r) x (β ^ 2 * ((b - t) * r))

theorem norm_parisiNormalizedHeatSource_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b t x r : ℝ) :
    ‖parisiNormalizedHeatSource β μ v b t x r‖ ≤ R ^ 2 := by
  have hm : ‖parisiCDF μ (t + (b - t) * r)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ _)]
    exact parisiCDF_le_one μ _
  unfold parisiNormalizedHeatSource
  rw [norm_mul]
  exact (mul_le_mul hm (norm_parisiSourceGaussianAverage_le v R hb _ _ _)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem parisiNormalizedHeatSource_measurable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) : Measurable (parisiNormalizedHeatSource β μ v b t x) := by
  exact ((parisiCDF_measurable μ).comp (by fun_prop)).mul
    (((continuous_parisiSourceGaussianAverage v hv R hb).comp
      (show Continuous (fun r : ℝ => (t + (b - t) * r, x, β ^ 2 * ((b - t) * r))) by fun_prop)).measurable)

noncomputable def parisiNormalizedDuhamelCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) : ℝ :=
  β ^ 2 / 2 * Real.sqrt (b - t) ^ 2 * ∫ r in (0 : ℝ)..1,
    parisiNormalizedHeatSource β μ v b t x r

theorem norm_parisiNormalizedDuhamelCorrection_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b t x : ℝ) :
    ‖parisiNormalizedDuhamelCorrection β μ v b t x‖ ≤
      β ^ 2 / 2 * Real.sqrt (b - t) ^ 2 * R ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun r _ => norm_parisiNormalizedHeatSource_le β μ v R hb b t x r)
  norm_num at h
  unfold parisiNormalizedDuhamelCorrection
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem continuousAt_parisiNormalizedHeatIntegral (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b : ℝ) (p : ℝ × ℝ) (ht : p.1 < b) :
    ContinuousAt (fun q : ℝ × ℝ => ∫ r in (0 : ℝ)..1,
      parisiNormalizedHeatSource β μ v b q.1 q.2 r) p := by
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => R ^ 2)
  · exact .of_forall fun q =>
      (parisiNormalizedHeatSource_measurable β μ v hv R hb b q.1 q.2).aestronglyMeasurable
  · exact .of_forall fun q => .of_forall fun r _ =>
      norm_parisiNormalizedHeatSource_le β μ v R hb b q.1 q.2 r
  · exact intervalIntegrable_const
  · have hinj : Function.Injective (fun r : ℝ => p.1 + (b - p.1) * r) := by
      intro r s hrs
      nlinarith
    have hc := ((parisiCDF_monotone μ).countable_not_continuousAt.preimage hinj).ae_notMem volume
    filter_upwards [hc] with r hr _
    have hm : ContinuousAt (fun q : ℝ × ℝ => parisiCDF μ (q.1 + (b - q.1) * r)) p :=
      (show ContinuousAt (parisiCDF μ) (p.1 + (b - p.1) * r) from by
        simpa using hr).comp (f := fun q : ℝ × ℝ => q.1 + (b - q.1) * r) (by fun_prop)
    have hg := (continuous_parisiSourceGaussianAverage v hv R hb).continuousAt.comp
      (show ContinuousAt (fun q : ℝ × ℝ =>
        (q.1 + (b - q.1) * r, q.2, β ^ 2 * ((b - q.1) * r))) p by fun_prop)
    exact hm.mul hg

theorem continuous_parisiNormalizedDuhamelCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (b : ℝ) :
    Continuous (fun p : ℝ × ℝ => parisiNormalizedDuhamelCorrection β μ v b p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases ht : p.1 < b
  · exact (show ContinuousAt (fun q : ℝ × ℝ => β ^ 2 / 2 * Real.sqrt (b - q.1) ^ 2) p by
      fun_prop).mul (continuousAt_parisiNormalizedHeatIntegral β μ v hv R hb b p ht)
  · have hs : Real.sqrt (b - p.1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have he : parisiNormalizedDuhamelCorrection β μ v b p.1 p.2 = 0 := by
      simp [parisiNormalizedDuhamelCorrection, hs]
    rw [ContinuousAt, he]
    apply squeeze_zero_norm (fun q : ℝ × ℝ => norm_parisiNormalizedDuhamelCorrection_le β μ v R hb b q.1 q.2)
    have hh : ContinuousAt (fun q : ℝ × ℝ => β ^ 2 / 2 * Real.sqrt (b - q.1) ^ 2 * R ^ 2) p := by fun_prop
    simpa [hs] using hh.tendsto

theorem parisiNormalizedDuhamelCorrection_eq (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) (htb : t ≤ b) :
    parisiNormalizedDuhamelCorrection β μ v b t x = parisiDuhamelCorrection β μ v b t x := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (f := parisiHeatSource β μ v t x) (a := (0 : ℝ)) (b := 1) (b - t) t
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at he
  unfold parisiNormalizedDuhamelCorrection parisiDuhamelCorrection
  rw [Real.sq_sqrt (sub_nonneg.mpr htb), ← he, mul_assoc]
  congr 2
  apply intervalIntegral.integral_congr_uIoo
  intro r _
  unfold parisiNormalizedHeatSource parisiHeatSource parisiSourceGaussianAverage
  dsimp only
  rw [show t + (b - t) * r - t = (b - t) * r by ring]

theorem continuousOn_parisiDuhamelPotential (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) :
    ContinuousOn (fun p : ℝ × ℝ => parisiDuhamelPotential β μ v p.1 p.2)
      {p : ℝ × ℝ | p.1 ≤ 1} := by
  have hh := continuous_heatSemigroup_logcosh.comp
    (show Continuous (fun p : ℝ × ℝ => (p.2, β ^ 2 * (1 - p.1))) by fun_prop)
  have hc := continuous_parisiNormalizedDuhamelCorrection β μ v hv R hb 1
  apply (hh.add hc).continuousOn.congr
  intro p hp
  exact congrArg (fun a => heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => Real.log (Real.cosh y)) p.2 + a)
    (parisiNormalizedDuhamelCorrection_eq β μ v 1 p.1 p.2 hp).symm

/-- A continuous extension of the genuine terminal Duhamel potential to the
whole plane, agreeing with it on all times at or before the terminal time. -/
noncomputable def parisiContinuousPotential (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => Real.log (Real.cosh y)) p.2 +
    parisiNormalizedDuhamelCorrection β μ v 1 p.1 p.2

theorem continuous_parisiContinuousPotential (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Continuous v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) :
    Continuous (parisiContinuousPotential β μ v) :=
  (continuous_heatSemigroup_logcosh.comp
    (show Continuous (fun p : ℝ × ℝ => (p.2, β ^ 2 * (1 - p.1))) by fun_prop)).add
      (continuous_parisiNormalizedDuhamelCorrection β μ v hv R hb 1)

theorem parisiContinuousPotential_eq (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x : ℝ) (ht : t ≤ 1) :
    parisiContinuousPotential β μ v (t, x) = parisiDuhamelPotential β μ v t x := by
  unfold parisiContinuousPotential parisiDuhamelPotential
  rw [parisiNormalizedDuhamelCorrection_eq β μ v 1 t x ht]

theorem hasDerivAt_parisiDuhamelCorrection_spatial (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) (htb : t ≤ b) (hβ : β ≠ 0) :
    HasDerivAt (fun a => parisiDuhamelCorrection β μ v b t a)
      (parisiGradientCorrection β μ v b t x) x := by
  let ν : Measure ℝ := volume.restrict (Ioc t b)
  have hmeas : ∀ᶠ a in 𝓝 x,
      AEStronglyMeasurable (fun s => parisiHeatSource β μ v t a s) ν :=
    .of_forall fun a => (parisiHeatSource_measurable β μ v hv t a).aestronglyMeasurable
  have hi : Integrable (fun s => parisiHeatSource β μ v t x s) ν :=
    (parisiHeatSource_intervalIntegrable β μ v hv R hb t x t b).1
  have hdm : AEStronglyMeasurable (fun s => parisiGradientSource β μ v t x s) ν :=
    (parisiGradientSource_measurable β μ v hv t x).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂ν, ∀ a ∈ (univ : Set ℝ),
      ‖parisiGradientSource β μ v t a s‖ ≤
        (|β|⁻¹ * gaussianAbsMoment * R ^ 2) * (Real.sqrt (s - t))⁻¹ :=
    .of_forall fun s a _ => norm_parisiGradientSource_le β μ v R hb t a s
  have hbi : Integrable (fun s =>
      (|β|⁻¹ * gaussianAbsMoment * R ^ 2) * (Real.sqrt (s - t))⁻¹) ν :=
    ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
      (|β|⁻¹ * gaussianAbsMoment * R ^ 2)).1
  have hd : ∀ᵐ s ∂ν, ∀ a ∈ (univ : Set ℝ),
      HasDerivAt (fun a => parisiHeatSource β μ v t a s)
        (parisiGradientSource β μ v t a s) a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs a _
    have hell : 0 < β ^ 2 * (s - t) :=
      mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hs.1)
    have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
    exact (hasDerivAt_heatSemigroup_spatial (β ^ 2 * (s - t)) hell
      (fun y => v (s, y) ^ 2) ((hv.comp (by fun_prop)).pow_const 2) (R ^ 2) hsq a).const_mul
        (parisiCDF μ s)
  have hout := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (α := ℝ) (μ := ν) (x₀ := x)
    (F := fun a s => parisiHeatSource β μ v t a s)
    (F' := fun a s => parisiGradientSource β μ v t a s)
    (s := univ) (by simp) hmeas hi hdm hbound hbi hd).2.const_mul (β ^ 2 / 2)
  simpa only [parisiDuhamelCorrection, parisiGradientCorrection,
    intervalIntegral.integral_of_le htb] using hout

theorem hasDerivAt_heatSemigroup_logcosh_spatial (ell x : ℝ) :
    HasDerivAt (heatSemigroup ell (fun y => Real.log (Real.cosh y)))
      (heatSemigroup ell Real.tanh x) x := by
  have hc : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => (Real.cosh_pos y).ne')
  exact hasDerivAt_gaussian_shift (fun y => Real.log (Real.cosh y)) Real.tanh
    (Real.sqrt ell) x 1 hc gaussian_continuous_tanh
    (integrable_gaussian_logcosh_affine x (Real.sqrt ell)) hasDerivAt_log_cosh
    (fun y => (Real.abs_tanh_lt_one y).le)

theorem hasDerivAt_parisiDuhamelPotential_spatial (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (t x : ℝ) (ht : t ≤ 1) (hβ : β ≠ 0) :
    HasDerivAt (parisiDuhamelPotential β μ v t)
      (heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
        parisiGradientCorrection β μ v 1 t x) x :=
  (hasDerivAt_heatSemigroup_logcosh_spatial (β ^ 2 * (1 - t)) x).add
    (hasDerivAt_parisiDuhamelCorrection_spatial β μ v hv R hb 1 t x ht hβ)

/-- Concrete potential of a bounded continuous gradient on a terminal slab. -/
noncomputable def localParisiPotential (β : ℝ) (μ : ParisiMeasure) {a : ℝ}
    (ha : a ≤ 1) (v : ParisiSlabGradient a 1) (t x : ℝ) : ℝ :=
  parisiDuhamelPotential β μ (parisiSlabExtend ha v) t x

/-- The local fixed point is the genuine spatial gradient of its potential,
including the terminal time. -/
theorem hasDerivAt_localParisiPotential_spatial (β : ℝ) (μ : ParisiMeasure)
    {a : ℝ} (ha : a ≤ 1) (v : ParisiSlabGradient a 1)
    (hv : parisiSlabGradientOperator β μ ha Real.tanh gaussian_continuous_tanh
      (fun y => (Real.abs_tanh_lt_one y).le) v = v)
    (hβ : β ≠ 0) (t : Icc a (1 : ℝ)) (x : ℝ) :
    HasDerivAt (localParisiPotential β μ ha v t) (v (t, x)) x := by
  have hd := hasDerivAt_parisiDuhamelPotential_spatial β μ (parisiSlabExtend ha v)
    (continuous_parisiSlabExtend ha v).measurable ‖v‖ (norm_parisiSlabExtend_le ha v)
    t x t.property.2 hβ
  rw [← localParisiGradient_equation β μ ha Real.tanh gaussian_continuous_tanh
    (fun y => (Real.abs_tanh_lt_one y).le) v hv (t, x)] at hd
  exact hd

@[simp] theorem localParisiPotential_terminal (β : ℝ) (μ : ParisiMeasure)
    {a : ℝ} (ha : a ≤ 1) (v : ParisiSlabGradient a 1) (x : ℝ) :
    localParisiPotential β μ ha v 1 x = Real.log (Real.cosh x) :=
  parisiDuhamelPotential_terminal β μ (parisiSlabExtend ha v) x

end Paper
