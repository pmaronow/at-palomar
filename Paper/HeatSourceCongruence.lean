module

public import Paper.ParisiWeakMild

@[expose] public section

/-! # Gaussian source operators respect space-time null sets -/

open Set MeasureTheory ProbabilityTheory Filter

namespace Paper

theorem heatSemigroup_congr_ae_volume (ell : ℝ) (hell : 0 < ell)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : f =ᵐ[volume] g) (x : ℝ) : heatSemigroup ell f x = heatSemigroup ell g x := by
  unfold heatSemigroup
  rw [gaussianExpectation_shift_eq_integral x ell hell.le f hf,
    gaussianExpectation_shift_eq_integral x ell hell.le g hg]
  exact integral_congr_ae ((gaussianReal_absolutelyContinuous x
    ((Real.toNNReal_pos.mpr hell).ne')).ae_eq he)

/-- Every actual bounded Volterra potential on the physical strip
depends only on the source's space-time almost-everywhere class. -/
theorem boundedVolterraPotential_congr_ae (β : ℝ) (hβ : β ≠ 0)
    (F G : ℝ × ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (he : F =ᵐ[parisiSpaceTime] G) (p : ℝ × ℝ) :
    boundedVolterraPotential β F p = boundedVolterraPotential β G p := by
  have heprod : F =ᵐ[parisiTimeMeasure.prod volume] G := by
    simpa only [← parisiSpaceTime_eq_timeProd] using he
  have hesection := Measure.ae_ae_eq_curry_of_prod heprod
  unfold boundedVolterraPotential
  apply integral_congr_ae
  filter_upwards [hesection] with s hs
  by_cases hps : p.1 < s
  · rw [if_pos hps, if_pos hps]
    exact heatSemigroup_congr_ae_volume _
      (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hps))
      (fun y => F (s, y)) (fun y => G (s, y))
      (hF.comp (by fun_prop)) (hG.comp (by fun_prop)) hs p.2
  · rw [if_neg hps, if_neg hps]

end Paper
