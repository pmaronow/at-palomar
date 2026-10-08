module

public import Paper.BoundedHeatSourceRegularity
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

/-! The gradient Volterra operator of a bounded measurable source is jointly
continuous on the closed physical strip. Cut off a short interval after the
initial time; the omitted square-root singularity has a uniform vanishing
integral bound. No time or space continuity of the source is assumed. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace Paper

theorem continuousAt_boundedHeatGradientSource (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (s : ℝ) (p : ℝ × ℝ) (hp : p.1 < s) :
    ContinuousAt (fun q : ℝ × ℝ => boundedHeatGradientSource β F q.1 s q.2) p := by
  have hc := continuousAt_heatGradient_of_bounded (fun y => F (s, y))
    (hF.comp (show Measurable (fun y : ℝ => (s, y)) by fun_prop)) M
    (fun y => hb (s, y)) (p.2, β ^ 2 * (s - p.1))
    (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hp))
  exact hc.comp (f := fun q : ℝ × ℝ => (q.2, β ^ 2 * (s - q.1)))
    (show ContinuousAt (fun q : ℝ × ℝ => (q.2, β ^ 2 * (s - q.1))) p by fun_prop)

def regularizedBoundedVolterraGradient (β : ℝ) (F : ℝ × ℝ → ℝ)
    (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s, if p.1 + ε < s then boundedHeatGradientSource β F p.1 s p.2 else 0 ∂parisiTimeMeasure

theorem continuous_regularizedBoundedVolterraGradient (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) : Continuous (regularizedBoundedVolterraGradient β F ε) := by
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hC : 0 ≤ |β|⁻¹ * gaussianAbsMoment * M := by
    exact mul_nonneg (mul_nonneg (by positivity) gaussianAbsMoment_nonneg) hM
  rw [continuous_iff_continuousAt]
  intro p
  unfold regularizedBoundedVolterraGradient
  apply continuousAt_of_dominated (μ := parisiTimeMeasure)
    (F := fun (q : ℝ × ℝ) (s : ℝ) =>
      if q.1 + ε < s then boundedHeatGradientSource β F q.1 s q.2 else 0)
    (bound := fun _ => (|β|⁻¹ * gaussianAbsMoment * M) * (Real.sqrt ε)⁻¹)
  · exact .of_forall (fun q => (((boundedHeatGradientSource_measurable β F hF).comp
      (show Measurable (fun s : ℝ => ((q.1, s), q.2)) by fun_prop)).ite
        (measurableSet_lt measurable_const measurable_id) measurable_const).aestronglyMeasurable)
  · exact .of_forall (fun q => .of_forall (fun s => by
      split_ifs with hs
      · apply (norm_boundedHeatGradientSource_le β F M hb q.1 s q.2).trans
        apply mul_le_mul_of_nonneg_left _ hC
        apply inv_le_inv₀ (Real.sqrt_pos.mpr (by linarith : 0 < s - q.1))
          (Real.sqrt_pos.mpr hε) |>.mpr
        exact Real.sqrt_le_sqrt (by linarith)
      · simpa using mul_nonneg hC (by positivity : 0 ≤ (Real.sqrt ε)⁻¹)))
  · exact integrable_const _
  · have hne : ∀ᵐ s ∂parisiTimeMeasure, s ≠ p.1 + ε := by
      exact ae_restrict_of_ae (volume.ae_ne (p.1 + ε))
    filter_upwards [hne] with s hsp
    rcases lt_or_gt_of_ne hsp with hslt | hsgt
    · have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ¬q.1 + ε < s := by
        filter_upwards [(show ContinuousAt (fun q : ℝ × ℝ => q.1 + ε) p by fun_prop).eventually
          (Ioi_mem_nhds hslt)] with q hq
        exact not_lt.mpr hq.le
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact ite_eq_right hq
    · have he : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 + ε < s :=
        (show ContinuousAt (fun q : ℝ × ℝ => q.1 + ε) p by fun_prop).eventually
          (Iio_mem_nhds hsgt)
      apply (continuousAt_boundedHeatGradientSource β hβ F hF M hb s p
        (by linarith)).congr_of_eventuallyEq
      filter_upwards [he] with q hq
      exact ite_eq_left hq

theorem norm_boundedHeatGradientSource_integral_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (t x b : ℝ) (htb : t ≤ b) :
    ‖∫ s in t..b, boundedHeatGradientSource β F t s x‖ ≤
      2 * M * gaussianAbsMoment / |β| * Real.sqrt (b - t) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le htb
    (.of_forall (fun s _ => norm_boundedHeatGradientSource_le β F M hb t s x))
    ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul (|β|⁻¹ * gaussianAbsMoment * M))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t b htb] at hh
  exact hh.trans_eq (by ring)

theorem regularizedBoundedVolterraGradient_eq (β : ℝ) (F : ℝ × ℝ → ℝ)
    (ε t x : ℝ) (ht : t + ε ∈ Icc (0 : ℝ) 1) :
    regularizedBoundedVolterraGradient β F ε (t, x) =
      ∫ s in (t + ε)..1, boundedHeatGradientSource β F t s x :=
  integral_parisiTime_lower_triangle (fun s => boundedHeatGradientSource β F t s x) (t + ε) ht

theorem regularizedBoundedVolterraGradient_eq_zero (β : ℝ) (F : ℝ × ℝ → ℝ)
    (ε t x : ℝ) (ht : 1 ≤ t + ε) :
    regularizedBoundedVolterraGradient β F ε (t, x) = 0 := by
  unfold regularizedBoundedVolterraGradient
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact ite_eq_right (not_lt.mpr (hs.2.trans ht))

theorem norm_boundedVolterraGradient_sub_regularized_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (p : ℝ × ℝ) (hp : p.1 ∈ Icc (0 : ℝ) 1) :
    ‖boundedVolterraGradient β F p - regularizedBoundedVolterraGradient β F ε p‖ ≤
      2 * M * gaussianAbsMoment / |β| * Real.sqrt ε := by
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hC : 0 ≤ 2 * M * gaussianAbsMoment / |β| := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hM) gaussianAbsMoment_nonneg) (abs_nonneg _)
  by_cases ha : p.1 + ε ≤ 1
  · have ha0 : 0 ≤ p.1 + ε := by linarith [hp.1]
    rw [show p = (p.1, p.2) from rfl, boundedVolterraGradient_eq β F p.1 p.2 hp,
      regularizedBoundedVolterraGradient_eq β F ε p.1 p.2 ⟨ha0, ha⟩]
    have hi0 := boundedHeatGradientSource_intervalIntegrable β F hF M hb p.1 p.2 (p.1 + ε) (by linarith)
    have hi1 : IntervalIntegrable (fun s => boundedHeatGradientSource β F p.1 s p.2)
        volume (p.1 + ε) 1 :=
      (boundedHeatGradientSource_intervalIntegrable β F hF M hb p.1 p.2 1 hp.2).mono_set (by
        rw [uIcc_of_le ha, uIcc_of_le hp.2]
        exact Icc_subset_Icc_left (by linarith))
    have he := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    rw [← he, add_sub_cancel_right]
    simpa only [add_sub_cancel_left] using
      norm_boundedHeatGradientSource_integral_le β F M hb p.1 p.2 (p.1 + ε) (by linarith)
  · rw [show p = (p.1, p.2) from rfl,
      regularizedBoundedVolterraGradient_eq_zero β F ε p.1 p.2 (by linarith), sub_zero]
    apply (norm_boundedVolterraGradient_le β F hF M hb p.1 p.2 hp).trans
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hC

/-- The genuine spatial derivative is jointly continuous up to both time
endpoints, even for an arbitrary bounded measurable source. -/
theorem continuousOn_boundedVolterraGradient (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) :
    ContinuousOn (boundedVolterraGradient β F) {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1} := by
  let ε := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have ht : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hbound : Tendsto (fun n => 2 * M * gaussianAbsMoment / |β| * Real.sqrt (ε n)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp ht).const_mul
      (2 * M * gaussianAbsMoment / |β|)
  have hu : TendstoUniformlyOn (fun n => regularizedBoundedVolterraGradient β F (ε n))
      (boundedVolterraGradient β F) atTop {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) 1} := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [hbound.eventually (Iio_mem_nhds hδ)] with n hn p hp
    rw [dist_eq_norm]
    exact (norm_boundedVolterraGradient_sub_regularized_le β F hF M hb (ε n) (hε n) p hp).trans_lt hn
  exact hu.continuousOn (.of_forall (fun n =>
    (continuous_regularizedBoundedVolterraGradient β hβ F hF M hb (ε n) (hε n)).continuousOn))

end Paper
