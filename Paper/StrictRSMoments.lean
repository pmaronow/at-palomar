module

public import Paper.RSMoments

@[expose] public section

/-!
# Strict post-interface moment and variational inequalities

Positivity of the actual Doob fourth moment makes the second moment strictly
increasing. In the small-variance regime this turns the comparison derivative
bound into a strict bound. The existing exponential estimate handles the
remaining regime, so strictness holds under the original fixed-point and AT
assumptions without an additional small-field hypothesis.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

private theorem probability_integral_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (hp : ∀ x, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hf).mpr
  have hs : Function.support f = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp x).ne'
  rw [hs]
  simp

/-- The actual Doob fourth-sech moment is strictly positive, including time zero. -/
theorem doobOperator_sech_fourth_pos (lam : ℝ≥0) (x : ℝ) :
    0 < doobOperator lam (fun y => sech y ^ 4) x := by
  have hi := integrable_cosh_mul_gaussianReal x lam (fun y => sech y ^ 4)
    (continuous_sech.pow 4).measurable 1 (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le 4)]
      exact pow_le_one₀ (sech_pos y).le (sech_le_one y))
  unfold doobOperator
  exact mul_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))
    (probability_integral_pos hi (fun y => mul_pos (Real.cosh_pos y) (pow_pos (sech_pos y) 4)))

theorem gaussianDoobFourthMoment_pos (β h q : ℝ) (lam : ℝ≥0) :
    0 < gaussianDoobFourthMoment β h q lam :=
  probability_integral_pos (integrable_gaussianDoobFourthMoment β h q lam)
    (doobOperator_sech_fourth_pos lam)

/-- Strict increase of the actual hard second moment. -/
theorem strictMonoOn_hardSecondMoment {β : ℝ} (hβ : 0 < β) (h q : ℝ) :
    StrictMonoOn (hardSecondMoment β h q) (Icc q (1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc q 1)
    (continuous_hardSecondMoment β h q).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [deriv_hardSecondMoment β h q ht.1]
  exact mul_pos (sq_pos_of_pos hβ) (gaussianDoobFourthMoment_pos β h q _)

/-- Strict comparison in the small-variance regime, including its equality boundary. -/
theorem hardSecondMoment_lt_time_of_small_variance {β h q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hsmall : β ^ 2 * (1 - q) ≤ 1) :
    ∀ t ∈ Ioc q (1 : ℝ), hardSecondMoment β h q t < t := by
  have hfix := hardSecondMoment_initial_fixed hq.1 hfixed
  have hm := strictMonoOn_hardSecondMoment hβ h q
  have hd : DifferentiableOn ℝ (hardSecondMoment β h q) (interior (Icc q (1 : ℝ))) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_hardSecondMoment β h q ht.1).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ interior (Icc q (1 : ℝ)), deriv (hardSecondMoment β h q) t < 1 := by
    intro t ht
    rw [interior_Icc] at ht
    have hqt : q < hardSecondMoment β h q t := by
      have hi := hm ⟨le_rfl, hq.2⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
      simpa only [hfix] using hi
    rw [deriv_hardSecondMoment β h q ht.1]
    have hbound := mul_le_mul_of_nonneg_left
      (gaussianDoobFourthMoment_le_one_sub_second β h q
        (β ^ 2 * (t - q)).toNNReal) (sq_nonneg β)
    change β ^ 2 * hardFourthMoment β h q t ≤
      β ^ 2 * (1 - hardSecondMoment β h q t) at hbound
    exact hbound.trans_lt ((mul_lt_mul_of_pos_left (by linarith) (sq_pos_of_pos hβ)).trans_le hsmall)
  intro t ht
  have he := (convex_Icc q (1 : ℝ)).image_sub_lt_mul_sub_of_deriv_lt
    (continuous_hardSecondMoment β h q).continuousOn hd hb
    q ⟨le_rfl, hq.2⟩ t ⟨ht.1.le, ht.2⟩ ht.1
  rw [hfix] at he
  linarith

/-- Strictness after the interface under the original parameter, fixed-point,
and AT assumptions alone. -/
theorem hardSecondMoment_lt_time {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ t ∈ Ioc q (1 : ℝ), hardSecondMoment β h q t < t := by
  by_cases hsmall : β ^ 2 * (1 - q) ≤ 1
  · exact hardSecondMoment_lt_time_of_small_variance hβ hq hfixed hsmall
  · have hfield := fixedPoint_structural_field_lt hh hq.1 hfixed (lt_of_not_ge hsmall)
    exact hardSecondMoment_lt_time_of_small_field hβ hh hq hfixed hAT hfield.le

theorem rsSecondMoment_right_strict {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Ioc q (1 : ℝ)) : rsSecondMoment β h q t < t := by
  rw [rsSecondMoment_eq_hard ht.1]
  exact hardSecondMoment_lt_time hβ hh hq hfixed hAT t ht

/-- Actual derivative of the assembled variational integral. -/
theorem hasDerivAt_rsParisiG {β h q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) (t : ℝ) :
    HasDerivAt (rsParisiG β h q)
      (-(β ^ 2 / 2 * (rsSecondMoment β h q t - t))) t := by
  have hf : Continuous (fun s => β ^ 2 / 2 * (rsSecondMoment β h q s - s)) :=
    ((continuous_rsSecondMoment β h q hβ hq).sub continuous_id).const_mul _
  exact intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable t 1)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- The RS variational function strictly increases after its interface. -/
theorem rsParisiG_strictMonoOn {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    StrictMonoOn (rsParisiG β h q) (Icc q (1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc q 1)
    (fun t _ => (hasDerivAt_rsParisiG hβ.le hq.1 t).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_rsParisiG hβ.le hq.1 t).deriv]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg (div_pos (sq_pos_of_pos hβ) (by norm_num))
    (sub_neg.mpr (rsSecondMoment_right_strict hβ hh hq hfixed hAT ⟨ht.1, ht.2.le⟩)))

/-- Every point to the right has strictly larger variational value. -/
theorem rsParisiG_interface_lt_right {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Ioc q (1 : ℝ)) : rsParisiG β h q q < rsParisiG β h q t :=
  rsParisiG_strictMonoOn hβ hh hq hfixed hAT ⟨le_rfl, hq.2⟩ ⟨ht.1.le, ht.2⟩ ht.1

end Paper
