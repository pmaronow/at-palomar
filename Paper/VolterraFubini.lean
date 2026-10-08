module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! # Changing the order of integration on the Volterra time triangle -/

open Set MeasureTheory

namespace Paper

noncomputable def parisiTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance : IsFiniteMeasure parisiTimeMeasure := by
  unfold parisiTimeMeasure
  infer_instance

theorem integral_parisiTime_lower_triangle (F : ℝ → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s, if t < s then F s else 0 ∂parisiTimeMeasure) = ∫ s in t..1, F s := by
  change (∫ s, (Ioi t).indicator F s ∂volume.restrict (Ioc (0 : ℝ) 1)) = _
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    intervalIntegral.integral_of_le ht.2]
  have hs : Ioi t ∩ Ioc (0 : ℝ) 1 = Ioc t 1 := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_of_le_of_lt ht.1 h.1, h.2⟩
  rw [hs]

theorem integral_parisiTime_upper_triangle (F : ℝ → ℝ) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t, if t < s then F t else 0 ∂parisiTimeMeasure) = ∫ t in (0 : ℝ)..s, F t := by
  change (∫ t, (Iio s).indicator F t ∂volume.restrict (Ioc (0 : ℝ) 1)) = _
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    intervalIntegral.integral_of_le hs.1, integral_Ioc_eq_integral_Ioo]
  have ht : Iio s ∩ Ioc (0 : ℝ) 1 = Ioo 0 s := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.le.trans hs.2⟩
  rw [ht]

/-- Fubini on the backward time triangle.  The exact absolute integrability
requirement is the indicator of the genuine two-dimensional triangle. -/
theorem integral_volterra_swap (F : ℝ → ℝ → ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => if p.1 < p.2 then F p.1 p.2 else 0)
      (parisiTimeMeasure.prod parisiTimeMeasure)) :
    (∫ t in (0 : ℝ)..1, ∫ s in t..1, F t s) =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..s, F t s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ t, (∫ s in t..1, F t s) ∂parisiTimeMeasure) =
    ∫ s, (∫ t in (0 : ℝ)..s, F t s) ∂parisiTimeMeasure
  calc
    _ = ∫ t, ∫ s, if t < s then F t s else 0 ∂parisiTimeMeasure ∂parisiTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (integral_parisiTime_lower_triangle (F t) t ⟨ht.1.le, ht.2⟩).symm
    _ = ∫ s, ∫ t, if t < s then F t s else 0 ∂parisiTimeMeasure ∂parisiTimeMeasure :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact integral_parisiTime_upper_triangle (fun t => F t s) s ⟨hs.1.le, hs.2⟩

end Paper
