module

public import Paper.ATSmoothGraph

@[expose] public section

/-!
# Literal auxiliary displays in the AT appendix

The main curve construction already proves the global conclusion.  This file
exposes centered odd-moment cancellation, the displayed Stein identity, the
normalized total C derivative, and its endpoint limit as standalone results.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem gaussianExpectation_odd_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hodd : ∀ z, f (-z) = -f z) : gaussianExpectation f = 0 := by
  have hm : (gaussianReal (0 : ℝ) 1).map (fun z => -z) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hi := integral_map (μ := gaussianReal (0 : ℝ) 1)
    (φ := fun z : ℝ => -z) (f := f) (by fun_prop) hf.aestronglyMeasurable
  rw [hm] at hi
  have hneg : (fun z : ℝ => f (-z)) = fun z => -f z := funext hodd
  rw [hneg, integral_neg] at hi
  unfold gaussianExpectation
  linarith

theorem gaussianU_zero_mean (t : ℝ) : gaussianU 0 t = 0 := by
  unfold gaussianU
  apply gaussianExpectation_odd_zero
  · exact (gaussian_continuous_tanh.comp (by fun_prop)).mul
      ((gaussian_continuous_sech.comp (by fun_prop)).pow 2)
  · intro z
    simp [mul_neg]

theorem gaussianV_zero_mean (t : ℝ) : gaussianV 0 t = 0 := by
  unfold gaussianV
  apply gaussianExpectation_odd_zero
  · exact (gaussian_continuous_tanh.comp (by fun_prop)).mul
      ((gaussian_continuous_sech.comp (by fun_prop)).pow 4)
  · intro z
    simp [mul_neg]

/-- The appendix's literal expectation of `(m s²)'`, rather than only
the already-proved rearranged moment identity. -/
theorem gaussian_ms_fourth_derivative_stein (h t : ℝ) (ht : 0 < t) :
    gaussianExpectation (fun z => deriv (fun y => Real.tanh y * sech y ^ 4)
      (h + Real.sqrt t * z)) = (gaussianT h t - h * gaussianV h t) / t := by
  have hs := gaussianC_variance_stein_relation h t ht.le
  have he : gaussianExpectation (fun z => deriv (fun y => Real.tanh y * sech y ^ 4)
      (h + Real.sqrt t * z)) = 5 * gaussianD h t - 4 * gaussianC h t := by
    unfold gaussianExpectation gaussianD gaussianC
    simp_rw [(hasDerivAt_tanh_mul_sech_fourth _).deriv]
    rw [integral_sub ((integrable_gaussian_sech_pow h (Real.sqrt t) 6).const_mul 5)
      ((integrable_gaussian_sech_pow h (Real.sqrt t) 4).const_mul 4),
      integral_const_mul, integral_const_mul]
    rfl
  rw [he]
  exact (eq_div_iff ht.ne').mpr (by nlinarith [hs])

/-- The normalized rational expression displayed for the total C derivative. -/
theorem atCOnCurveSlope_eq_normalized (t : ℝ) (ht : 0 < t) :
    atCOnCurveSlope t =
      -(2 * (gaussianU (atFieldRoot t) t * gaussianT (atFieldRoot t) t +
        gaussianV (atFieldRoot t) t * (2 * t * gaussianB (atFieldRoot t) t -
          atFieldRoot t * gaussianU (atFieldRoot t) t))) /
        (t * (gaussianU (atFieldRoot t) t + 2 * t * gaussianV (atFieldRoot t) t)) := by
  apply at_curve_derivative_identity _ _ _ _ _ _ ht.ne'
  exact (at_slope_denominator_pos t _ _ ht
    (gaussianU_pos _ t (atFieldRoot_pos t ht) ht)
    (gaussianV_pos _ t (atFieldRoot_pos t ht) ht)).ne'

theorem tendsto_atCOnCurve_zero_right :
    Tendsto atCOnCurve (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (1 : ℝ)) := by
  have hp := continuousAt_atFieldRoot_zero.prodMk continuousAt_id
  have hc := continuous_gaussianC_joint.continuousAt.comp hp
  have he : gaussianC (atFieldRoot 0) 0 = 1 := by
    simp [atFieldRoot_zero_variance, gaussianC_zero_time, sech]
  change Tendsto (fun t => gaussianC (atFieldRoot t) t) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1)
  rw [← he]
  exact hc.continuousWithinAt (s := Set.Ioi (0 : ℝ))

end Paper
