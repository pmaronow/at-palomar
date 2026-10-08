module

public import Paper.RSFunctional
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # The genuine first-moment identity for Parisi CDFs

The identity is an application of Fubini to the measurable triangle `q ≤ t`.
The measures, CDFs, and interval integrals are the actual ones; integrability
is verified before exchanging the order of integration.
-/

open Set MeasureTheory
open scoped Topology ENNReal

namespace Paper

theorem parisiCDF_intervalIntegrable (μ : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (parisiCDF μ) volume a b :=
  (parisiCDF_monotone μ).intervalIntegrable

/-- The CDF is the integral of the actual upper-triangle indicator. -/
theorem parisiCDF_eq_integral_upperIndicator (μ : ParisiMeasure) (t : ℝ) :
    parisiCDF μ t = ∫ q : Overlap, if (q : ℝ) ≤ t then (1 : ℝ) else 0
      ∂(μ : Measure Overlap) := by
  have hs : MeasurableSet {q : Overlap | (q : ℝ) ≤ t} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  have hfun : (fun q : Overlap => if (q : ℝ) ≤ t then (1 : ℝ) else 0) =
      Set.indicator {q : Overlap | (q : ℝ) ≤ t} (fun _ => (1 : ℝ)) := by
    funext q
    simp only [Set.indicator, mem_ofPred_eq]
  rw [hfun, integral_indicator hs]
  simp only [parisiCDF, setIntegral_const, smul_eq_mul, mul_one, Measure.real]

/-- Each vertical section of the upper triangle has length `1-q`. -/
theorem integral_upperIndicator (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, if q ≤ t then (1 : ℝ) else 0) = 1 - q := by
  let f : ℝ → ℝ := fun t => if q ≤ t then 1 else 0
  have heq0 : EqOn f (fun _ => (0 : ℝ)) (uIoo 0 q) := by
    intro t ht
    rw [uIoo_of_le hq.1] at ht
    simp [f, not_le_of_gt ht.2]
  have heq1 : EqOn f (fun _ => (1 : ℝ)) (uIoo q 1) := by
    intro t ht
    rw [uIoo_of_le hq.2] at ht
    simp [f, ht.1.le]
  have hInt0 : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_congr_uIoo heq0).mpr intervalIntegrable_const
  have hInt1 : IntervalIntegrable f volume q 1 :=
    (intervalIntegrable_congr_uIoo heq1).mpr intervalIntegrable_const
  have h0 : (∫ t in (0 : ℝ)..q, f t) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo heq0]
    simp
  have h1 : (∫ t in q..(1 : ℝ), f t) = 1 - q := by
    rw [intervalIntegral.integral_congr_uIoo heq1]
    simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  change (∫ t in (0 : ℝ)..1, f t) = 1 - q
  rw [h0, h1, zero_add] at hadd
  exact hadd.symm

/-- Exact CDF first-moment identity for every actual probability measure on
the overlap interval. It includes arbitrary atoms and singular measures. -/
theorem parisiCDF_integral_eq_firstMoment (μ : ParisiMeasure) :
    (∫ t in (0 : ℝ)..1, parisiCDF μ t) =
      ∫ q : Overlap, 1 - (q : ℝ) ∂(μ : Measure Overlap) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hset : MeasurableSet {p : ℝ × Overlap | (p.2 : ℝ) ≤ p.1} :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_fst).measurableSet
  have hm : Measurable (fun p : ℝ × Overlap =>
      if (p.2 : ℝ) ≤ p.1 then (1 : ℝ) else 0) := by
    exact measurable_const.ite hset measurable_const
  have hF : Integrable (fun p : ℝ × Overlap =>
      if (p.2 : ℝ) ≤ p.1 then (1 : ℝ) else 0)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (μ : Measure Overlap)) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with p
    split <;> norm_num
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp_rw [parisiCDF_eq_integral_upperIndicator μ]
  rw [integral_integral_swap hF]
  apply integral_congr_ae
  filter_upwards with q
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integral_upperIndicator (q : ℝ) q.2

/-- A measurable transport changes the integrated CDF by its exact mean
displacement. This is the identity needed for upward grid quantization. -/
theorem parisiCDF_integral_sub_map (μ : ParisiMeasure) (T : Overlap → Overlap)
    (hT : Measurable T) :
    (∫ t in (0 : ℝ)..1, parisiCDF μ t - parisiCDF (μ.map T) t) =
      ∫ q : Overlap, (T q : ℝ) - (q : ℝ) ∂(μ : Measure Overlap) := by
  let G : Overlap → ℝ := fun q => 1 - (q : ℝ)
  have hG : Continuous G := continuous_const.sub continuous_subtype_val
  have hi : Integrable G (μ : Measure Overlap) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hG.continuousOn.integrableOn_compact (μ := (μ : Measure Overlap)) isCompact_univ
  have hiMap : Integrable G ((μ : Measure Overlap).map T) := by
    change Integrable G ((μ.map T : ParisiMeasure) : Measure Overlap)
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hG.continuousOn.integrableOn_compact (μ := ((μ.map T : ParisiMeasure) : Measure Overlap))
        isCompact_univ
  have hiT : Integrable (fun q => G (T q)) (μ : Measure Overlap) :=
    (integrable_map_measure hG.aestronglyMeasurable hT.aemeasurable).mp hiMap
  rw [intervalIntegral.integral_sub (parisiCDF_intervalIntegrable μ 0 1)
    (parisiCDF_intervalIntegrable (μ.map T) 0 1),
    parisiCDF_integral_eq_firstMoment μ, parisiCDF_integral_eq_firstMoment (μ.map T)]
  change (∫ q, G q ∂(μ : Measure Overlap)) -
    (∫ q, G q ∂((μ : Measure Overlap).map T)) = _
  rw [integral_map hT.aemeasurable hG.aestronglyMeasurable, ← integral_sub hi hiT]
  apply integral_congr_ae
  filter_upwards with q
  dsimp only [G]
  ring

theorem parisiCDF_abs_diff_intervalIntegrable (μ ν : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (fun t => |parisiCDF μ t - parisiCDF ν t|) volume a b :=
  ((parisiCDF_intervalIntegrable μ a b).sub (parisiCDF_intervalIntegrable ν a b)).abs

/-- Moving every overlap upward decreases the actual CDF at every threshold. -/
theorem parisiCDF_map_le (μ : ParisiMeasure) (T : Overlap → Overlap) (hT : Measurable T)
    (hup : ∀ q : Overlap, (q : ℝ) ≤ (T q : ℝ)) (t : ℝ) :
    parisiCDF (μ.map T) t ≤ parisiCDF μ t := by
  have hs : MeasurableSet {q : Overlap | (q : ℝ) ≤ t} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold parisiCDF
  rw [ProbabilityMeasure.map_apply' μ hT.aemeasurable hs]
  apply ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) _)
  exact measure_mono (fun q hq => (hup q).trans hq)

/-- Actual time-L¹ control of the CDF under a measurable upward transport.
No continuity or absolute continuity of the transported measure is required. -/
theorem parisiCDF_map_L1_bound (μ : ParisiMeasure) (T : Overlap → Overlap)
    (hT : Measurable T) (δ : ℝ) (hup : ∀ q : Overlap, (q : ℝ) ≤ (T q : ℝ))
    (hdisp : ∀ q : Overlap, (T q : ℝ) - (q : ℝ) ≤ δ) :
    (∫ t in (0 : ℝ)..1, |parisiCDF μ t - parisiCDF (μ.map T) t|) ≤ δ := by
  have hfun : (fun t : ℝ => |parisiCDF μ t - parisiCDF (μ.map T) t|) =
      (fun t => parisiCDF μ t - parisiCDF (μ.map T) t) := by
    funext t
    exact abs_of_nonneg (sub_nonneg.mpr (parisiCDF_map_le μ T hT hup t))
  rw [hfun, parisiCDF_integral_sub_map μ T hT]
  have hm : Measurable (fun q : Overlap => (T q : ℝ) - (q : ℝ)) :=
    (measurable_subtype_coe.comp hT).sub measurable_subtype_coe
  have hi : Integrable (fun q : Overlap => (T q : ℝ) - (q : ℝ)) (μ : Measure Overlap) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [q.property.1, q.property.2, (T q).property.1, (T q).property.2]
  have hbound := integral_mono hi (integrable_const δ) hdisp
  simpa using hbound

end Paper
