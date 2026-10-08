module

public import Paper.MomentIntegral

@[expose] public section

/-! The literal integrated exponential second-moment display. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper

/-- The zero-overlap boundary has a direct heat-semigroup estimate, without
requiring a positive initial Gaussian variance. -/
theorem hardFourthMoment_exponential_decay_zero (β t : ℝ) (ht : 0 ≤ t) :
    β ^ 2 * hardFourthMoment β 0 0 t ≤
      atParameter β 0 0 * Real.exp (-(β ^ 2 * t) / 2) := by
  have htime : 0 ≤ β ^ 2 * t := mul_nonneg (sq_nonneg β) ht
  have hAT : atParameter β 0 0 = β ^ 2 := by
    rw [atParameter_eq_gaussian (le_refl (0 : ℝ))]
    simp
  rw [hAT]
  unfold hardFourthMoment gaussianDoobFourthMoment
  simp only [mul_zero, Real.toNNReal_zero, gaussianReal_zero_var, integral_dirac, sub_zero]
  rw [doobOperator_sech_fourth_eq_heatSemigroup]
  simp only [Real.cosh_zero, div_one, Real.coe_toNNReal _ htime]
  have hb : ∀ y : ℝ, ‖sech y ^ 3‖ ≤ 1 := by
    intro y
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (sech_pos y).le]
    exact pow_le_one₀ (sech_pos y).le (sech_le_one y)
  have hn := norm_heatSemigroup_le (β ^ 2 * t) (fun y => sech y ^ 3) 1 hb 0
  have hs : heatSemigroup (β ^ 2 * t) (fun y => sech y ^ 3) 0 ≤ 1 :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)
  have hp := mul_nonneg (sq_nonneg β) (Real.exp_nonneg (-(β ^ 2 * t) / 2))
  nlinarith

theorem hardFourthMoment_exponential_decay_of_nonneg {β h q t : ℝ}
    (hβ : β ≠ 0) (hq : 0 ≤ q) (hh : 0 ≤ h) (hfield : h ≤ β ^ 2 * q) (ht : q ≤ t) :
    β ^ 2 * hardFourthMoment β h q t ≤
      atParameter β h q * Real.exp (-(β ^ 2 * (t - q)) / 2) := by
  rcases hq.eq_or_lt with he | he
  · subst q
    have hzero : h = 0 := by nlinarith
    subst h
    simpa only [sub_zero] using hardFourthMoment_exponential_decay_zero β t ht
  · exact hardFourthMoment_exponential_decay hβ he hh hfield ht

/-- The paper's explicit integrated exponential bound for the actual hard
second moment, including the zero-overlap boundary. -/
theorem hardSecondMoment_le_exp_bound {β h q : ℝ}
    (hβ : β ≠ 0) (hq : 0 ≤ q) (hh : 0 ≤ h) (hfield : h ≤ β ^ 2 * q)
    (hfixed : q = overlapMap β h q) :
    ∀ t ∈ Icc q (1 : ℝ), hardSecondMoment β h q t ≤ q +
      (2 * atParameter β h q / β ^ 2) *
        (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) := by
  apply secondMoment_le_exp_bound hβ
    (continuous_hardSecondMoment β h q).continuousOn
    ((continuous_hardFourthMoment β h q).const_mul (β ^ 2)).continuousOn
    (fun s hs => hasDerivAt_hardSecondMoment β h q hs.1)
    (hardSecondMoment_initial_fixed hq hfixed)
  intro s hs
  exact hardFourthMoment_exponential_decay_of_nonneg hβ hq hh hfield hs.1.le

theorem physicalHardSecondMoment_le_exp_bound {β h q t : ℝ}
    (hβ : β ≠ 0) (hq : q ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h)
    (hfield : h ≤ β ^ 2 * q) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    physicalHardSecondMoment β h q hq t ≤ q +
      (2 * atParameter β h q / β ^ 2) *
        (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) := by
  rw [physicalHardSecondMoment_eq β h q hq ht]
  exact hardSecondMoment_le_exp_bound hβ hq.1 hh hfield hfixed t ht

theorem canonicalDiracState_secondMoment_le_exp_bound {β h q t : ℝ}
    (hβ : β ≠ 0) (hq : q ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h)
    (hfield : h ≤ β ^ 2 * q) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    (∫ omega, Real.tanh (canonicalDiracStateReal β h q hq omega t) ^ 2
      ∂canonicalBrownianMeasure) ≤ q + (2 * atParameter β h q / β ^ 2) *
        (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) :=
  physicalHardSecondMoment_le_exp_bound hβ hq hh hfield hfixed ht

theorem selectedParisiSecondMoment_dirac_le_exp_bound {β h q t : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h)
    (hfield : h ≤ β ^ 2 * q) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t ≤ q +
      (2 * atParameter β h q / β ^ 2) *
        (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) := by
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩,
    physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1, ht.2⟩,
    rsSecondMoment_eq_hard_of_le hq.1 ht.1]
  exact hardSecondMoment_le_exp_bound hβ.ne' hq.1 hh hfield hfixed t ht

end Paper
