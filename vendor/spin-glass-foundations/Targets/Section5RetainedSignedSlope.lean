module

public import Targets.Section4SignedSlopeBound
public import Targets.Section5RetainedSignedInitialLambda
public import Targets.Section5SignedInitialEndpoint

@[expose] public section

/-!
# The signed slope with the original positive shared field retained

Condition on the frozen positive Gaussian field and use the generic signed
factor estimate. Gaussian Fubini and the scalar semigroup recover the original
initial Hessian square. No covariance-law identification or change of the
external field is needed. These scalar gains still require signed pressure
transport before they prove Proposition 5.4.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Conditioning on the frozen field bounds the genuine retained-family
lambda derivative by the original initial Hessian square times the negative
shared variance. -/
theorem section5RetainedSignedInitialV_deriv_lower_bound {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {v b c : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hvar : v + b + c = β ^ 2 * s.q 1) :
    -section4THessianSquare s β h 1 0 * c ≤
      deriv (section5RetainedSignedInitialV s β h v b c) 0 := by
  let A := parisiF s β (k + 1)
  let A' := parisiFDeriv s β (k + 1)
  let A'' := parisiFSecond s β (k + 1)
  let S := stepD1 A A' 0 v
  let G := fun x => A'' x ^ 2
  let f := fun z z' => S (h + Real.sqrt c * z + Real.sqrt b * z') *
    S (h - Real.sqrt c * z + Real.sqrt b * z')
  have hA := parisiF_hasLinearGrowth s β (k + 1)
  have hC2 := (parisiF_C2_props s β (k + 1)).1
  have hAm := parisiF_measurable s β (k + 1)
  have hA'm := (parisiF_C2_props s β (k + 1)).2.1
  have hA''m := (parisiF_C2_props s β (k + 1)).2.2
  have hS := hasParisiC2_parisiStep_nonneg (v := v) (m := 0) le_rfl zero_le_one
    hC2 hA hAm hA'm hA''m
  have hSm : Measurable S := measurable_stepD1 hAm hA'm 0 v
  have hfi : Integrable (Function.uncurry f) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine (integrable_const (1 : ℝ)).mono' (by
      dsimp [Function.uncurry, f]
      exact ((hSm.comp (by fun_prop)).mul (hSm.comp (by fun_prop))).aestronglyMeasurable) ?_
    filter_upwards with z
    dsimp [Function.uncurry, f]
    rw [abs_mul]
    exact (mul_le_mul (hS.abs_first_le_one _) (hS.abs_first_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he (z' : ℝ) : (∫ z, f z z' ∂gaussianReal 0 1) =
      signedSplitSlope A A' (v + c) (h + Real.sqrt b * z') v := by
    unfold signedSplitSlope
    simp only [add_sub_cancel_left]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [f, S]
    congr 2 <;> ring
  have hGb : ∀ x, |G x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := hC2.abs_second_le_one x
    change A'' x ^ 2 ≤ 1
    nlinarith [sq_abs (A'' x), abs_nonneg (A'' x)]
  have hGm : Measurable G := hA''m.pow_const 2
  have hG : HasLinearGrowth G := ⟨1, 0, zero_le_one, le_rfl, by simpa using hGb⟩
  have hi := (integrable_gaussian_bounded_shift (measurable_parisiStep hGm 0 (v+c))
    (abs_parisiStep_zero_le_one hGb (v+c)) b h).neg.mul_const c
  have H := integral_mono hi hfi.integral_prod_right
    (fun z' => show -parisiStep 0 (v+c) G (h + Real.sqrt b * z') * c ≤
      ∫ z, f z z' ∂gaussianReal 0 1 by
      rw [he]
      simpa only [add_sub_cancel_left] using
        signedSplitSlope_lower_bound hA hC2 (continuous_parisiFSecond s β (k+1))
          (a := v+c) (v := v) ⟨hv, le_add_of_nonneg_right hc⟩ (h + Real.sqrt b * z'))
  simp only [Function.uncurry_def, Pi.neg_apply] at H
  rw [← integral_integral_swap hfi] at H
  rw [(hasDerivAt_section5RetainedSignedInitialV_zero s β h v b c).deriv]
  change _ ≤ ∫ z, ∫ z', f z z' ∂gaussianReal 0 1 ∂gaussianReal 0 1
  have hmean : (∫ z', parisiStep 0 (v+c) G (h + Real.sqrt b * z') ∂gaussianReal 0 1) =
      section4THessianSquare s β h 1 0 := by
    have Hsem := congrFun (parisiStep_add 0 b (v+c) hb (add_nonneg hv hc) hG hGm) h
    rw [show b+(v+c) = β ^ 2 * s.q 1 by linarith] at Hsem
    have Hinit : section4THessianSquare s β h 1 0 = parisiStep 0 (β ^ 2 * s.q 1) G h := by
      simp only [section4THessianSquare, Nat.sub_self, s.m_zero,
        section4VarianceR_initial_eq_scalar_integral, s.q_zero, sub_zero]
      simp [stepD2_zero_mass_eq_parisiStep, tiltWeight, parisiStep, G, A'']
    rw [Hinit, Hsem]
    simp only [parisiStep, ↓reduceIte]
  simpa only [integral_mul_const, integral_neg, hmean] using H

/-- The actual retained-field lambda slope is uniformly positive at negative
overlap under the already studied initial endpoint curvature bound. -/
theorem section5RetainedSignedInitialV_slope_lower_bound {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {t t₀ u e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (-s.q 1) 0) (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    (1 - t₀) / 2 * (-u) ≤
      deriv (section5RetainedSignedInitialV s β h (t * (β ^ 2 * (s.q 1 + u)))
        ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * (-u)))) 0 - u := by
  have H := section5RetainedSignedInitialV_deriv_lower_bound s β h
    (v := t * (β ^ 2 * (s.q 1 + u)))
    (b := (1 - t) * (β ^ 2 * s.q 1)) (c := t * (β ^ 2 * (-u)))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (by linarith [hu.1])))
    (mul_nonneg (sub_nonneg.mpr (ht.2.trans ht₀.le))
      (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (neg_nonneg.mpr hu.2))) (by ring)
  have hcurv := mul_le_mul_of_nonneg_left hR ht.1
  have hte : t * e ≤ e := mul_le_of_le_one_left he (ht.2.trans ht₀.le)
  have hcoef : (1 - t₀) / 2 ≤ 1 - t * β ^ 2 * section4THessianSquare s β h 1 0 := by
    nlinarith only [hcurv, hte, ht.2, he_small]
  have Hcoef := mul_le_mul_of_nonneg_right hcoef (neg_nonneg.mpr hu.2)
  nlinarith only [H, Hcoef]

/-- The retained scalar endpoint has a quantitative lambda improvement.
This does not assume or assert its still-unproved transport to positive
interpolation times. -/
theorem section5RetainedSignedInitialV_quantitative_gain {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {t t₀ u e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (-s.q 1) 0) (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    ∃ ℓ : ℝ, section5RetainedSignedInitialV s β h (t * (β ^ 2 * (s.q 1 + u)))
        ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * (-u))) ℓ - ℓ * u ≤
      2 * parisiF s β (k + 2) h - (1 - t₀) ^ 2 / 8 * u ^ 2 := by
  have Hs := section5RetainedSignedInitialV_slope_lower_bound s β h ht ht₀ hu he he_small hR
  obtain ⟨ℓ, Hℓ⟩ := section5RetainedSignedInitialV_lambda_gain s β h
    (t * (β ^ 2 * (s.q 1 + u))) ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * (-u))) u
  have Hz := section5RetainedSignedInitialV_zero s β h
    (v := t * (β ^ 2 * (s.q 1 + u)))
    (b := (1 - t) * (β ^ 2 * s.q 1)) (c := t * (β ^ 2 * (-u)))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (by linarith [hu.1])))
    (mul_nonneg (sub_nonneg.mpr (ht.2.trans ht₀.le))
      (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (neg_nonneg.mpr hu.2))) (by ring)
  rw [Hz] at Hℓ
  have Hsq := mul_self_le_mul_self
    (mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num))
      (neg_nonneg.mpr hu.2)) Hs
  refine ⟨ℓ, ?_⟩
  nlinarith only [Hℓ, Hsq]

/-- The genuine field-only endpoint satisfies the quantitative signed gain.
Only the transport along the signed interpolation remains to turn this into
the corresponding bound on the original constrained free energy. -/
theorem section5SignedInitialFieldEndpoint_quantitative_gain {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) {t t₀ u e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u)
    (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    section5SignedInitialFieldEndpoint n s β h t u ≤
      2 * Real.log 2 + 2 * parisiF s β (k + 2) h - (1 - t₀) ^ 2 / 8 * u ^ 2 := by
  obtain ⟨ℓ, Hℓ⟩ := section5RetainedSignedInitialV_quantitative_gain s β h
    ht ht₀ hu he he_small hR
  have H := section5SignedInitialFieldEndpoint_le hn s β h
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu hu' ℓ
  linarith only [H, Hℓ]

end SpinGlass.Targets
