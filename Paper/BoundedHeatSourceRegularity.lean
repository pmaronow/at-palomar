module

public import Paper.ParisiDuhamelWeak
public import Paper.HeatGradient
public import Paper.GaussianBoundedSmoothing

@[expose] public section

/-!
# Regularity of the heat Volterra potential of a bounded measurable source

The source may be discontinuous in both variables. Spatial differentiation
acts on the genuine Gaussian kernel; the inverse-square-root time singularity
is integrable. The source is never assumed to have a classical derivative.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace Paper

def boundedHeatGradientSource (β : ℝ) (F : ℝ × ℝ → ℝ) (t s x : ℝ) : ℝ :=
  heatGradient (β ^ 2 * (s - t)) (fun y => F (s, y)) x

def boundedVolterraGradient (β : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s, if p.1 < s then boundedHeatGradientSource β F p.1 s p.2 else 0 ∂parisiTimeMeasure

theorem boundedHeatGradientSource_measurable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => boundedHeatGradientSource β F p.1.1 p.1.2 p.2) := by
  have hm : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      p.2 * F (p.1.1.2, p.1.2 + Real.sqrt (β ^ 2 * (p.1.1.2 - p.1.1.1)) * p.2)) :=
    measurable_snd.mul (hF.comp (by fun_prop))
  exact (show Measurable (fun p : (ℝ × ℝ) × ℝ =>
    (Real.sqrt (β ^ 2 * (p.1.2 - p.1.1)))⁻¹) by fun_prop).mul
      ((hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable)

theorem boundedVolterraGradient_measurable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) : Measurable (boundedVolterraGradient β F) := by
  have hm := (boundedHeatGradientSource_measurable β F hF).comp
    (show Measurable (fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.2), p.1.2)) by fun_prop)
  have htri : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 < p.2} :=
    measurableSet_lt (measurable_fst.fst) measurable_snd
  exact ((hm.ite htri measurable_const).stronglyMeasurable.integral_prod_right'
    (ν := parisiTimeMeasure)).measurable

theorem norm_boundedHeatGradientSource_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (t s x : ℝ) :
    ‖boundedHeatGradientSource β F t s x‖ ≤
      (|β|⁻¹ * gaussianAbsMoment * M) * (Real.sqrt (s - t))⁻¹ := by
  have h := norm_heatGradient_le (β ^ 2 * (s - t)) (fun y => F (s, y)) M
    (fun y => hb (s, y)) x
  apply h.trans_eq
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
  ring

theorem boundedHeatSource_intervalIntegrable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (t x a b : ℝ) :
    IntervalIntegrable (fun s => boundedHeatSource β F t s x) volume a b := by
  apply (intervalIntegrable_const (c := M)).mono_fun'
  · exact ((boundedHeatSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((t, s), x)) by fun_prop)).aestronglyMeasurable
  · exact .of_forall (fun s => norm_boundedHeatSource_le β F M hb t s x)

theorem boundedHeatGradientSource_intervalIntegrable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (t x b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (fun s => boundedHeatGradientSource β F t s x) volume t b := by
  apply ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
    (|β|⁻¹ * gaussianAbsMoment * M)).mono_fun'
  · exact ((boundedHeatGradientSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((t, s), x)) by fun_prop)).aestronglyMeasurable
  · exact .of_forall (fun s => norm_boundedHeatGradientSource_le β F M hb t s x)

theorem boundedVolterraGradient_eq (β : ℝ) (F : ℝ × ℝ → ℝ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    boundedVolterraGradient β F (t, x) = ∫ s in t..1, boundedHeatGradientSource β F t s x :=
  integral_parisiTime_lower_triangle (fun s => boundedHeatGradientSource β F t s x) t ht

theorem norm_boundedVolterraGradient_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖boundedVolterraGradient β F (t, x)‖ ≤
      2 * M * gaussianAbsMoment / |β| * Real.sqrt (1 - t) := by
  rw [boundedVolterraGradient_eq β F t x ht]
  have hh := intervalIntegral.norm_integral_le_of_norm_le ht.2
    (.of_forall (fun s _ => norm_boundedHeatGradientSource_le β F M hb t s x))
    ((intervalIntegrable_inv_sqrt_sub t 1 ht.2).const_mul (|β|⁻¹ * gaussianAbsMoment * M))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t 1 ht.2] at hh
  exact hh.trans_eq (by ring)

/-- Actual spatial differentiation, without any continuity of the source. -/
theorem hasDerivAt_boundedVolterraPotential_spatial (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => boundedVolterraPotential β F (t, y))
      (boundedVolterraGradient β F (t, x)) x := by
  let ν : Measure ℝ := volume.restrict (Ioc t 1)
  have hmeas : ∀ᶠ a in 𝓝 x,
      AEStronglyMeasurable (fun s => boundedHeatSource β F t s a) ν :=
    .of_forall (fun a => ((boundedHeatSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((t, s), a)) by fun_prop)).aestronglyMeasurable)
  have hi : Integrable (fun s => boundedHeatSource β F t s x) ν :=
    (boundedHeatSource_intervalIntegrable β F hF M hb t x t 1).1
  have hdm : AEStronglyMeasurable (fun s => boundedHeatGradientSource β F t s x) ν :=
    ((boundedHeatGradientSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((t, s), x)) by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂ν, ∀ a ∈ (univ : Set ℝ),
      ‖boundedHeatGradientSource β F t s a‖ ≤
        (|β|⁻¹ * gaussianAbsMoment * M) * (Real.sqrt (s - t))⁻¹ :=
    .of_forall (fun s a _ => norm_boundedHeatGradientSource_le β F M hb t s a)
  have hbi : Integrable (fun s =>
      (|β|⁻¹ * gaussianAbsMoment * M) * (Real.sqrt (s - t))⁻¹) ν :=
    ((intervalIntegrable_inv_sqrt_sub t 1 ht.2).const_mul (|β|⁻¹ * gaussianAbsMoment * M)).1
  have hd : ∀ᵐ s ∂ν, ∀ a ∈ (univ : Set ℝ),
      HasDerivAt (fun a => boundedHeatSource β F t s a)
        (boundedHeatGradientSource β F t s a) a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs a _
    exact hasDerivAt_heatSemigroup_spatial (β ^ 2 * (s - t))
      (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hs.1))
      (fun y => F (s, y)) (hF.comp (by fun_prop)) M (fun y => hb (s, y)) a
  have hout := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (α := ℝ) (μ := ν) (x₀ := x)
    (F := fun a s => boundedHeatSource β F t s a)
    (F' := fun a s => boundedHeatGradientSource β F t s a)
    (s := univ) (by simp) hmeas hi hdm hbound hbi hd).2
  rw [boundedVolterraGradient_eq β F t x ht]
  have he : (fun y => boundedVolterraPotential β F (t, y)) =
      fun y => ∫ s in t..1, boundedHeatSource β F t s y :=
    funext (fun y => boundedVolterraPotential_eq β F t y ht)
  rw [he]
  simpa only [intervalIntegral.integral_of_le ht.2] using hout

theorem continuousAt_boundedHeatSource (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (s : ℝ) (p : ℝ × ℝ) (hp : p.1 < s) :
    ContinuousAt (fun q : ℝ × ℝ => boundedHeatSource β F q.1 s q.2) p := by
  have hc := continuousAt_heatSemigroup_of_bounded (fun y => F (s, y))
    (hF.comp (show Measurable (fun y : ℝ => (s, y)) by fun_prop)) M
    (fun y => hb (s, y)) (p.2, β ^ 2 * (s - p.1))
    (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hp))
  exact hc.comp (f := fun q : ℝ × ℝ => (q.2, β ^ 2 * (s - q.1)))
    (show ContinuousAt (fun q : ℝ × ℝ => (q.2, β ^ 2 * (s - q.1))) p by fun_prop)

/-- A bounded measurable source has a genuinely continuous Volterra potential
on the whole plane. Its time sections need not be continuous. -/
theorem continuous_boundedVolterraPotential (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) :
    Continuous (boundedVolterraPotential β F) := by
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  rw [continuous_iff_continuousAt]
  intro p
  unfold boundedVolterraPotential
  apply continuousAt_of_dominated (μ := parisiTimeMeasure)
    (F := fun (q : ℝ × ℝ) (s : ℝ) => if q.1 < s then boundedHeatSource β F q.1 s q.2 else 0)
    (bound := fun _ => M)
  · exact .of_forall (fun q => (((boundedHeatSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((q.1, s), q.2)) by fun_prop)).ite
        (measurableSet_lt measurable_const measurable_id) measurable_const).aestronglyMeasurable)
  · exact .of_forall (fun q => .of_forall (fun s => by
      split_ifs
      · exact norm_boundedHeatSource_le β F M hb q.1 s q.2
      · simpa using hM))
  · exact integrable_const M
  · have hs : ∀ᵐ s ∂parisiTimeMeasure, s ≠ p.1 := by
      exact ae_iff.mpr (by simp [parisiTimeMeasure])
    filter_upwards [hs] with s hsp
    rcases lt_or_gt_of_ne hsp with hslt | hsgt
    · have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ¬q.1 < s := by
        filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hslt)] with q hq
        exact not_lt.mpr hq.le
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact if_neg hq
    · have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < s :=
        continuous_fst.continuousAt.eventually (Iio_mem_nhds hsgt)
      apply (continuousAt_boundedHeatSource β hβ F hF M hb s p hsgt).congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact if_pos hq

end Paper
