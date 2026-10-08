module

public import Paper.GaussianPoincareStrict
public import Paper.StrictRSMoments

@[expose] public section

/-!
# Strict left-hand moment bound and unique RS variational minimum

Strict Gaussian Poincaré remains strict after Gaussian averaging. Therefore
the soft second moment exceeds time even when the AT parameter equals one.
Together with the strict hard bound, the actual variational integral has its
unique minimum at the fixed-point overlap.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter

namespace Paper

private theorem probability_integral_lt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ x, f x < g x) : (∫ x, f x ∂μ) < ∫ x, g x ∂μ := by
  have hp : 0 < ∫ x, (g - f) x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (sub_pos.mpr (hfg x)).le) (hg.sub hf)).mpr
    have hs : Function.support (fun x => g x - f x) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true, Pi.sub_apply]
      exact (sub_pos.mpr (hfg x)).ne'
    rw [hs]
    simp
  simp only [Pi.sub_apply] at hp
  rw [integral_sub hg hf] at hp
  linarith

theorem softSecondMoment_variance_bound_strict {β h q t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Ico (0 : ℝ) q) :
    overlapMap β h q - softSecondMoment β h q t < atParameter β h q * (q - t) := by
  let a : ℝ := β * Real.sqrt (q - t)
  have ha : 0 < a := mul_pos hβ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))
  have hTanhBound : ∀ x, ‖Real.tanh x ^ 2‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact tanh_sq_le_one x
  have hSechBound : ∀ x, ‖sech x ^ 4‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 4)]
    exact sech_fourth_le_one x
  have hiT := integrable_nested_gaussian_field (fun x => Real.tanh x ^ 2) β h t a 1
    (gaussian_continuous_tanh.pow 2) hTanhBound
  have hiS := integrable_softSecondMoment β h q t
  have hi4 := integrable_nested_gaussian_field (fun x => sech x ^ 4) β h t a 1
    (gaussian_continuous_sech.pow 4) hSechBound
  have hineq := probability_integral_lt (hiT.sub hiS) (hi4.const_mul (a ^ 2)) (fun z => by
    have hp := gaussian_poincare_tanh_strict (gaussianField β h t z) a ha
    simpa only [rsSoftDx, Pi.sub_apply, a] using hp)
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub hiT hiS, integral_const_mul] at hineq
  change gaussianExpectation (fun z => gaussianExpectation
      (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) - softSecondMoment β h q t <
    a ^ 2 * gaussianExpectation (fun z => gaussianExpectation
      (fun w => sech (gaussianField β h t z + a * w) ^ 4)) at hineq
  have hcollapse2 := soft_gaussian_terminal_collapse (fun x => Real.tanh x ^ 2)
    β h q t 1 hβ.le ⟨ht.1, ht.2.le⟩ (gaussian_continuous_tanh.pow 2) hTanhBound
  have hcollapse4 := soft_gaussian_terminal_collapse (fun x => sech x ^ 4)
    β h q t 1 hβ.le ⟨ht.1, ht.2.le⟩ (gaussian_continuous_sech.pow 4) hSechBound
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) = overlapMap β h q at hcollapse2
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => sech (gaussianField β h t z + a * w) ^ 4)) = _ at hcollapse4
  rw [hcollapse2, hcollapse4] at hineq
  have ha2 : a ^ 2 = β ^ 2 * (q - t) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2.le)]
  rw [ha2] at hineq
  unfold atParameter
  nlinarith [hineq]

/-- The literal soft Gaussian second moment strictly exceeds time before `q`,
including the AT equality boundary. -/
theorem softSecondMoment_left_strict {β h q t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Ico (0 : ℝ) q)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    t < softSecondMoment β h q t := by
  have hp := softSecondMoment_variance_bound_strict (h := h) hβ ht
  rw [← hfixed] at hp
  have ha := mul_le_mul_of_nonneg_right hAT (sub_pos.mpr ht.2).le
  linarith

/-- Strictness for the assembled actual RS second moment before `q`. -/
theorem rsSecondMoment_left_strict {β h q t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Ico (0 : ℝ) q)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    t < rsSecondMoment β h q t := by
  rw [rsSecondMoment_eq_soft ht.2.le]
  exact softSecondMoment_left_strict hβ ht hfixed hAT

/-- The concrete RS variational integral strictly decreases up to the interface. -/
theorem rsParisiG_strictAntiOn {β h q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    StrictAntiOn (rsParisiG β h q) (Icc (0 : ℝ) q) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 q)
    (fun t _ => (hasDerivAt_rsParisiG hβ.le hq.1 t).continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_rsParisiG hβ.le hq.1 t).deriv]
  exact neg_neg_of_pos (mul_pos (div_pos (sq_pos_of_pos hβ) (by norm_num))
    (sub_pos.mpr (rsSecondMoment_left_strict hβ ⟨ht.1.le, ht.2⟩ hfixed hAT)))

/-- The interface has strictly smaller variational value than every other point. -/
theorem rsParisiG_interface_lt_of_ne {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hne : t ≠ q) :
    rsParisiG β h q q < rsParisiG β h q t := by
  rcases lt_or_gt_of_ne hne with hleft | hright
  · exact rsParisiG_strictAntiOn hβ hq hfixed hAT ⟨ht.1, hleft.le⟩ ⟨hq.1, le_rfl⟩ hleft
  · exact rsParisiG_interface_lt_right hβ hh hq hfixed hAT ⟨hright, ht.2⟩

/-- The actual deterministic/Gaussian variational minimum is unique. -/
theorem rsParisiG_eq_minimum_iff {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    rsParisiG β h q t = rsParisiG β h q q ↔ t = q := by
  constructor
  · intro he
    by_contra hne
    exact (rsParisiG_interface_lt_of_ne hβ hh hq hfixed hAT ht hne).ne' he
  · rintro rfl
    rfl

end Paper
