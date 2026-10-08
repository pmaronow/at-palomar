module

public import Paper.FixedPoint
public import Paper.GaussianCurveSigns
public import Paper.GaussianHeat
public import Paper.ATCoordinates

@[expose] public section

/-! # Uniqueness of the positive-field Gaussian overlap fixed point

A Gaussian Stein identity shows that `(1-A(h,t))/t` strictly decreases
on positive variance. Its derivative has the sign of the negative sum
of a positive hyperbolic Stein gap and a positive odd Gaussian moment.
-/

open MeasureTheory ProbabilityTheory

namespace Paper

theorem gaussian_tanhSteinGap_identity (h t : ℝ) :
    gaussianExpectation (fun z => tanhSteinGap (h + Real.sqrt t * z)) =
      1 - gaussianA h t - gaussianMixedSecond h t := by
  rw [← gaussian_tanh_sq_expectation_eq_one_sub_A]
  unfold gaussianMixedSecond gaussianExpectation
  have hi : Integrable (fun z => Real.tanh (h + Real.sqrt t * z) ^ 2)
      (gaussianReal 0 1) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((gaussian_continuous_tanh.pow 2).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact tanh_sq_le_one _
  rw [← integral_sub hi (integrable_gaussianMixedSecond_integrand h t)]
  apply integral_congr_ae
  filter_upwards with z
  unfold tanhSteinGap
  ring

theorem gaussian_overlap_variance_slope_gap_pos (h t : ℝ) (hh : 0 < h) (ht : 0 < t) :
    0 < (1 - gaussianA h t) - t * (3 * gaussianC h t - 2 * gaussianA h t) := by
  have hs := gaussianMixedSecond_stein h t ht.le
  have hg := gaussian_tanhSteinGap_pos h t ht
  rw [gaussian_tanhSteinGap_identity] at hg
  have hu := mul_pos hh (gaussianU_pos h t hh ht)
  linarith

theorem gaussian_overlap_ratio_strictAntiOn (h : ℝ) (hh : 0 < h) :
    StrictAntiOn (fun t => (1 - gaussianA h t) / t) (Set.Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => (1 - gaussianA h s) / s)
        (((3 * gaussianC h t - 2 * gaussianA h t) * t - (1 - gaussianA h t)) /
          t ^ 2) t := by
    convert ((hasDerivAt_gaussianA_variance h ht).const_sub 1).div
      (hasDerivAt_id t) ht.ne' using 1
    · ext s
      simp only [Pi.div_apply, id_eq]
    · simp only [id_eq]
      ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
    rw [(hd t htpos).deriv]
    apply div_neg_of_neg_of_pos
    · have hg := gaussian_overlap_variance_slope_gap_pos h t hh htpos
      nlinarith
    · exact sq_pos_of_pos htpos

theorem positive_field_fixedPoint_unique (β h q r : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqfixed : q = overlapMap β h q)
    (hrfixed : r = overlapMap β h r) : q = r := by
  have hqp := fixedPoint_pos hh hq hqfixed
  have hrp := fixedPoint_pos hh hr hrfixed
  have hb := sq_pos_of_pos hβ
  have eqA (s : ℝ) : overlapMap β h s = 1 - gaussianA h (β ^ 2 * s) := by
    unfold overlapMap
    simp_rw [gaussianField_eq_time β h s _ hβ.le]
    exact gaussian_tanh_sq_expectation_eq_one_sub_A h (β ^ 2 * s)
  have hqr : (1 - gaussianA h (β ^ 2 * q)) / (β ^ 2 * q) =
      (1 - gaussianA h (β ^ 2 * r)) / (β ^ 2 * r) := by
    rw [← eqA q, ← eqA r, ← hqfixed, ← hrfixed]
    field_simp
  have heq := (gaussian_overlap_ratio_strictAntiOn h hh).injOn
    (show β ^ 2 * q ∈ Set.Ioi 0 from mul_pos hb hqp)
    (show β ^ 2 * r ∈ Set.Ioi 0 from mul_pos hb hrp) hqr
  exact (mul_left_cancel₀ hb.ne' heq)

theorem exists_unique_rs_fixedPoint (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) :
    ∃! q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ q = overlapMap β h q := by
  obtain ⟨q, hq, hfixed⟩ := exists_rs_fixedPoint β h hβ hh
  refine ⟨q, ⟨⟨hq.1.le, hq.2.le⟩, hfixed⟩, ?_⟩
  intro r hr
  exact positive_field_fixedPoint_unique β h r q hβ hh hr.1.1 hq.1.le hr.2 hfixed

end Paper
