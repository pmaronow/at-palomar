module

public import Paper.RSSoft
public import Paper.GaussianPoincare
public import Paper.Variational

@[expose] public section

/-!
# Actual soft Gaussian moment and the left-hand bound

The second moment is the literal squared Gaussian conditional `tanh`
expectation, evaluated at the Gaussian field at time `t`. Gaussian Poincaré
and the independent-sum law are proved in the imported modules. This file
assumes neither a Poincaré estimate nor the desired moment sign.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

/-- The actual Gaussian conditional second moment before the RS interface. -/
def softSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianExpectation (fun z => rsSoftDx β q t (gaussianField β h t z) ^ 2)

lemma soft_dx_square_norm_le_one (β q t x : ℝ) : ‖rsSoftDx β q t x ^ 2‖ ≤ 1 := by
  simpa only [norm_pow, one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_rsSoftDx_le_one β q t x) 2

/-- The soft Gaussian second moment is a genuine integrable expectation. -/
theorem integrable_softSecondMoment (β h q t : ℝ) :
    Integrable (fun z => rsSoftDx β q t (gaussianField β h t z) ^ 2) (gaussianReal 0 1) := by
  have hc : Continuous (fun z => rsSoftDx β q t (gaussianField β h t z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((hasDerivAt_rsSoftDx_spatial β q t _).continuousAt).comp
      (by unfold gaussianField; fun_prop)
  exact (integrable_const (1 : ℝ)).mono' (hc.pow 2).aestronglyMeasurable
    (.of_forall fun z => soft_dx_square_norm_le_one β q t _)

/-- Continuity extends across both time endpoints, including `t=q`. -/
theorem continuous_softSecondMoment (β h q : ℝ) (hβ : 0 ≤ β) :
    Continuous (softSecondMoment β h q) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    exact (integrable_softSecondMoment β h q t).aestronglyMeasurable
  · intro t
    exact .of_forall fun z => soft_dx_square_norm_le_one β q t _
  · exact integrable_const 1
  · filter_upwards [] with z
    have hc : Continuous (fun t : ℝ => (t, gaussianField β h t z)) := by
      unfold gaussianField
      fun_prop
    exact ((continuous_rsSoftDx_joint β q hβ).comp hc).pow 2

/-- At the interface the conditional expectation has zero remaining variance. -/
@[simp] theorem softSecondMoment_interface (β h q : ℝ) :
    softSecondMoment β h q q = overlapMap β h q := by
  simp only [softSecondMoment, rsSoftDx_interface, overlapMap]

theorem softSecondMoment_interface_fixed {β h q : ℝ}
    (hfixed : q = overlapMap β h q) : softSecondMoment β h q q = q := by
  rw [softSecondMoment_interface, ← hfixed]

/-- Gaussian averaging with a fixed scale is continuous in its mean. -/
lemma continuous_gaussian_average_fixed_scale (f : ℝ → ℝ) (a C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun x => gaussianExpectation (fun z => f (x + a * z))) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact .of_forall fun z => hb _
  · exact integrable_const C
  · filter_upwards [] with z
    exact hf.comp (by fun_prop)

lemma norm_gaussian_average_fixed_scale (f : ℝ → ℝ) (a x C : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ C) : ‖gaussianExpectation (fun z => f (x + a * z))‖ ≤ C := by
  simpa [gaussianExpectation] using norm_integral_le_of_norm_le_const
    (μ := gaussianReal 0 1) (f := fun z : ℝ => f (x + a * z)) (.of_forall fun z => hb _)

lemma integrable_nested_gaussian_field (f : ℝ → ℝ) (β h t a C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun z => gaussianExpectation (fun w => f (gaussianField β h t z + a * w)))
      (gaussianReal 0 1) := by
  have hc := (continuous_gaussian_average_fixed_scale f a C hf hb).comp
    (show Continuous (gaussianField β h t) by unfold gaussianField; fun_prop)
  exact (integrable_const C).mono' hc.aestronglyMeasurable
    (.of_forall fun z => norm_gaussian_average_fixed_scale f a _ C hb)

/-- The actual conditional Gaussian field composes to the terminal field. -/
theorem soft_gaussian_terminal_collapse (f : ℝ → ℝ) (β h q t C : ℝ)
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    gaussianExpectation (fun z => gaussianExpectation
      (fun w => f (gaussianField β h t z + β * Real.sqrt (q - t) * w))) =
      gaussianExpectation (fun z => f (gaussianField β h q z)) := by
  have heq : (fun z => gaussianExpectation
      (fun w => f (gaussianField β h t z + β * Real.sqrt (q - t) * w))) =
      (fun z => gaussianExpectation
        (fun w => f (h + β * Real.sqrt t * z + β * Real.sqrt (q - t) * w))) := by
    funext z
    congr 1
    funext w
    congr 1
    unfold gaussianField
    ring
  rw [heq, gaussianExpectation_double_affine_collapse h (β * Real.sqrt t)
    (β * Real.sqrt (q - t)) f hf.measurable C hb]
  have hvar : (β * Real.sqrt t) ^ 2 + (β * Real.sqrt (q - t)) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht.1, Real.sq_sqrt (sub_nonneg.mpr ht.2)]
    ring
  rw [hvar, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]
  congr 1
  funext z
  congr 1
  unfold gaussianField
  ring

/-- The full Gaussian variance estimate, before substituting the fixed point. -/
theorem softSecondMoment_variance_bound {β h q t : ℝ}
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q) :
    overlapMap β h q - softSecondMoment β h q t ≤ atParameter β h q * (q - t) := by
  let a : ℝ := β * Real.sqrt (q - t)
  have ha : 0 ≤ a := mul_nonneg hβ (Real.sqrt_nonneg _)
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
  have hineq := integral_mono (hiT.sub hiS) (hi4.const_mul (a ^ 2)) (fun z => by
    have hp := gaussian_poincare_tanh (gaussianField β h t z) a ha
    simpa only [rsSoftDx, Pi.sub_apply, a] using hp)
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub hiT hiS, integral_const_mul] at hineq
  change gaussianExpectation (fun z => gaussianExpectation
      (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) - softSecondMoment β h q t ≤
    a ^ 2 * gaussianExpectation (fun z => gaussianExpectation
      (fun w => sech (gaussianField β h t z + a * w) ^ 4)) at hineq
  have hcollapse2 := soft_gaussian_terminal_collapse (fun x => Real.tanh x ^ 2)
    β h q t 1 hβ ht (gaussian_continuous_tanh.pow 2) hTanhBound
  have hcollapse4 := soft_gaussian_terminal_collapse (fun x => sech x ^ 4)
    β h q t 1 hβ ht (gaussian_continuous_sech.pow 4) hSechBound
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) = overlapMap β h q at hcollapse2
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => sech (gaussianField β h t z + a * w) ^ 4)) = _ at hcollapse4
  rw [hcollapse2, hcollapse4] at hineq
  have ha2 : a ^ 2 = β ^ 2 * (q - t) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2)]
  rw [ha2] at hineq
  unfold atParameter
  nlinarith [hineq]

/-- The paper's actual conditional Gaussian Poincaré bound from the fixed point. -/
theorem softSecondMoment_poincare_bound {β h q t : ℝ}
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q) (hfixed : q = overlapMap β h q) :
    q - softSecondMoment β h q t ≤ atParameter β h q * (q - t) := by
  have hh := softSecondMoment_variance_bound (h := h) hβ ht
  rwa [← hfixed] at hh

/-- Proposition 4.1's quantitative left bound for the actual explicit moment. -/
theorem softSecondMoment_left_quantitative {β h q t : ℝ}
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q) (hfixed : q = overlapMap β h q)
    (hAT : atParameter β h q ≤ 1) :
    0 ≤ (1 - atParameter β h q) * (q - t) ∧
      (1 - atParameter β h q) * (q - t) ≤ softSecondMoment β h q t - t :=
  left_quantitative_of_poincare_bound hAT ht.2 (softSecondMoment_poincare_bound hβ ht hfixed)

/-- The actual soft moment has the sign required for the variational argument. -/
theorem softSecondMoment_left_sign {β h q t : ℝ}
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q) (hfixed : q = overlapMap β h q)
    (hAT : atParameter β h q ≤ 1) : t ≤ softSecondMoment β h q t :=
  left_sign_of_poincare_bound hAT ht.2 (softSecondMoment_poincare_bound hβ ht hfixed)

end Paper
