module

public import Paper.ParisiMeasureStability
public import Paper.ParisiMildDerivative

@[expose] public section

/-! # Genuine potential stability under CDF L1 and gradient convergence -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem norm_parisiHeatSource_measure_L1_point_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (t x s : ℝ) :
    ‖parisiHeatSource β μ v t x s - parisiHeatSource β ν v t x s‖ ≤
      ‖parisiCDF μ s - parisiCDF ν s‖ * R ^ 2 := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  unfold parisiHeatSource
  rw [← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_heatSemigroup_le _ _ _ hsq _)
    (norm_nonneg _)

theorem norm_parisiDuhamelCorrection_measure_L1_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) (ht : 0 ≤ t) (htb : t ≤ b) (hb1 : b ≤ 1) :
    ‖parisiDuhamelCorrection β μ v b t x - parisiDuhamelCorrection β ν v b t x‖ ≤
      β ^ 2 / 2 * R ^ 2 * (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) := by
  have hi := parisiHeatSource_intervalIntegrable β μ v hv R hb t x t b
  have hj := parisiHeatSource_intervalIntegrable β ν v hv R hb t x t b
  have hCDF := parisiCDF_difference_intervalIntegrable μ ν t b
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun s => parisiHeatSource β μ v t x s - parisiHeatSource β ν v t x s) htb
  have hbound : (∫ s in t..b, ‖parisiHeatSource β μ v t x s - parisiHeatSource β ν v t x s‖) ≤
      R ^ 2 * (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) := by
    calc
      _ ≤ ∫ s in t..b, ‖parisiCDF μ s - parisiCDF ν s‖ * R ^ 2 := by
        apply intervalIntegral.integral_mono_on htb (hi.sub hj).norm (hCDF.mul_const _)
        intro s _
        exact norm_parisiHeatSource_measure_L1_point_le β μ ν v R hb t x s
      _ = R ^ 2 * (∫ s in t..b, ‖parisiCDF μ s - parisiCDF ν s‖) := by
        rw [intervalIntegral.integral_mul_const, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval ht htb hb1 (.of_forall fun s => norm_nonneg _)
          (parisiCDF_difference_intervalIntegrable μ ν 0 1)) (sq_nonneg R)
  unfold parisiDuhamelCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
  exact (mul_le_mul_of_nonneg_left (hnorm.trans hbound) (by positivity)).trans_eq (by ring)

theorem norm_parisiDuhamelPotential_measure_gradient_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R D : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (hd : ∀ p, ‖v p - w p‖ ≤ D) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiDuhamelPotential β μ v t x - parisiDuhamelPotential β ν w t x‖ ≤
      β ^ 2 * R * D + β ^ 2 / 2 * R ^ 2 *
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hvb (0, 0))
  have hD : 0 ≤ D := (norm_nonneg _).trans (hd (0, 0))
  unfold parisiDuhamelPotential
  rw [add_sub_add_left_eq_sub]
  calc
    _ ≤ ‖parisiDuhamelCorrection β μ v 1 t x - parisiDuhamelCorrection β μ w 1 t x‖ +
        ‖parisiDuhamelCorrection β μ w 1 t x - parisiDuhamelCorrection β ν w 1 t x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ β ^ 2 * (1 - t) * R * D + β ^ 2 / 2 * R ^ 2 *
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) := add_le_add
      (norm_parisiDuhamelCorrection_sub_le β μ v w hv hw R D hvb hwb hd 1 t x ht.2)
      (norm_parisiDuhamelCorrection_measure_L1_sub_le β μ ν w hw R hwb 1 t x ht.1 ht.2 le_rfl)
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right (sub_le_self 1 ht.1)
        (mul_nonneg (mul_nonneg (sq_nonneg β) hR) hD)
      nlinarith

end Paper
