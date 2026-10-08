module

public import Paper.ParisiDuhamelWeak
public import Paper.HeatGrowth

@[expose] public section

/-! # The linearly growing terminal term in the weak Parisi equation

The terminal datum is `log cosh`.  Spatial self-adjointness and the heat
operator's first absolute moment justify the terminal heat identity without
assuming that this datum is bounded.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem continuous_logcosh : Continuous (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')

theorem integrable_logcosh_heatTest (β : ℝ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2)
      (parisiTimeMeasure.prod volume) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_integral_norm_sections_bound ψ hψ hc
  let χ : ℝ × ℝ → ℝ := fun p => ‖p.2‖ * ψ p
  have hχ : Continuous χ := by unfold χ; fun_prop
  have hχc : HasCompactSupport χ := hc.mul_left
  obtain ⟨D, _hD0, hD⟩ := exists_uniform_integral_norm_sections_bound χ hχ hχc
  have hψmeas : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ψ (p.1.1, p.1.2 + Real.sqrt (β ^ 2 * (1 - p.1.1)) * p.2)) :=
    hψ.measurable.comp (by fun_prop)
  have hh := (hψmeas.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hp : Measurable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2) :=
    (continuous_logcosh.comp continuous_snd).measurable.mul hh
  have hsections (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) := by
    have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
      (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section ψ hc t)
    have hχi : Integrable (fun x : ℝ => ‖x‖ * ψ (t, x)) :=
      (hχ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section χ hχc t)
    have hweighted : Integrable (fun x : ℝ => ‖x‖ * ‖ψ (t, x)‖) := by
      simpa only [norm_mul, norm_norm] using hχi.norm
    exact heatSemigroup_firstMoment (β ^ 2 * (1 - t))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)) (fun y => ψ (t, y))
      ((hψ.comp (by fun_prop)).measurable) hψi hweighted
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫ x, ‖Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖) ≤
        D + |β| * gaussianAbsMoment * B := by
    have hheat := hsections t ht
    have hi : Integrable (fun x : ℝ => Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x) := by
      apply hheat.1.norm.mono'
        ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
      filter_upwards with x
      change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖
      simp only [norm_mul, norm_norm]
      have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
      exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    have hsq : Real.sqrt (β ^ 2 * (1 - t)) ≤ |β| := by
      calc
        _ ≤ Real.sqrt (β ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg β, ht.1.le])
        _ = _ := Real.sqrt_sq_eq_abs β
    calc
      _ ≤ ∫ x, ‖x‖ * ‖heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖ := by
        apply integral_mono hi.norm
          (by simpa only [norm_mul, norm_norm] using hheat.1.norm)
        intro x
        dsimp only
        rw [norm_mul]
        have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ ≤ _ := hheat.2
      _ ≤ D + |β| * gaussianAbsMoment * B := by
        have hDw : (∫ x, ‖x‖ * ‖ψ (t, x)‖) ≤ D := by
          simpa only [χ, norm_mul, norm_norm] using hD t
        calc
          _ ≤ D + Real.sqrt (β ^ 2 * (1 - t)) * gaussianAbsMoment * B :=
            add_le_add hDw (mul_le_mul_of_nonneg_left (hB t)
              (mul_nonneg (Real.sqrt_nonneg _) gaussianAbsMoment_nonneg))
          _ ≤ _ := add_le_add (le_refl D)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq gaussianAbsMoment_nonneg) hB0)
  apply (integrable_prod_iff hp.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (hsections t ht).1.norm.mono'
      ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
    filter_upwards with x
    change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖
    simp only [norm_mul, norm_norm]
    have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_logcosh_le_abs x)
    exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  · apply (integrable_const (D + |β| * gaussianAbsMoment * B)).mono'
      (hp.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using hbound t ht

noncomputable def parisiTerminalHeat (β : ℝ) (p : ℝ × ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => Real.log (Real.cosh y)) p.2

theorem continuous_parisiTerminalHeat (β : ℝ) : Continuous (parisiTerminalHeat β) :=
  continuous_heatSemigroup_logcosh.comp
    (show Continuous (fun p : ℝ × ℝ => (p.2, β ^ 2 * (1 - p.1))) by fun_prop)

theorem integral_parisiTerminalHeat_adjointSource (β : ℝ) (hβ : β ≠ 0)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) :
    (∫ p, parisiTerminalHeat β p * parisiAdjointSource β φ p
      ∂parisiTimeMeasure.prod volume) =
      -(∫ x, Real.log (Real.cosh x) * φ (1, x)) := by
  let ψ := parisiAdjointSource β φ
  have hψ : Continuous ψ := continuous_parisiAdjointSource β φ hφ
  have hψc : HasCompactSupport ψ := hasCompactSupport_parisiAdjointSource β φ hφ hc
  have hi : Integrable (fun p => parisiTerminalHeat β p * ψ p)
      (parisiTimeMeasure.prod volume) :=
    ((continuous_parisiTerminalHeat β).mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  have hj := integrable_logcosh_heatTest β ψ hψ hψc
  rw [integral_prod _ hi]
  calc
    _ = ∫ t, (∫ x, Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x) ∂parisiTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
        (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
          (hasCompactSupport_spatial_section ψ hψc t)
      have hwi : Integrable (fun x : ℝ => ‖x‖ * ‖ψ (t, x)‖) := by
        have hχ : Continuous (fun x : ℝ => ‖x‖ * ψ (t, x)) := by fun_prop
        have hχi : Integrable (fun x : ℝ => ‖x‖ * ψ (t, x)) := hχ.integrable_of_hasCompactSupport
          (hasCompactSupport_spatial_section ψ hψc t).mul_left
        simpa only [norm_mul, norm_norm] using hχi.norm
      exact heatSemigroup_adjoint_linearGrowth _
        (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)) _ _ continuous_logcosh.measurable
        ((hψ.comp (by fun_prop)).measurable) hψi hwi 0 1 (by norm_num)
        (fun x => by simpa only [zero_add, one_mul, Real.norm_eq_abs] using (norm_logcosh_le_abs x))
    _ = ∫ x, Real.log (Real.cosh x) * (∫ t in (0 : ℝ)..1,
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x) := by
      rw [integral_integral_swap hj]
      simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_const_mul]
      rfl
    _ = ∫ x, Real.log (Real.cosh x) * (-φ (1, x)) := by
      congr 1
      funext x
      dsimp [ψ, parisiAdjointSource]
      rw [integral_heat_adjointSource_positiveTimeTest φ hφ hc hsupp β 1 x hβ (by norm_num)]
    _ = _ := by simp only [mul_neg, integral_neg]

end Paper
