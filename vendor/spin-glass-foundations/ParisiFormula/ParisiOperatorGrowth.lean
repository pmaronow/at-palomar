module

/-
# The Parisi semigroup law under linear growth

New work for the ParisiFormula project (not vendored).

`SpinGlass.Parisi.T_add` (vendored, in `ParisiFormula/ParisiOperator.lean`) proves the
semigroup law `T_{m,v₁+v₂} = T_{m,v₁} ∘ T_{m,v₂}` under

  `HasUniformBound A := ∃ C, ∀ x, |A x| ≤ C`.

**That hypothesis is never satisfied by the Parisi recursion.**  Its base `log cosh y` grows
like `|y|`, and every level inherits *linear* growth (`Targets.hasLinearGrowth_parisiStep`),
never boundedness.  So the vendored `T_add` applies to no level of `parisiF`, and the natural
route for Target 2b's `q`-perturbation — factoring a change of `q_p` as an extra smoothing
step, `T_{m,v'} = T_{m,v} ∘ T_{m,v'-v}` — is closed.

This file re-proves the same law under `HasLinearGrowth`, which *is* the invariant the
recursion satisfies.  The Gaussian-convolution + Fubini structure of the original proof
carries unchanged; only the two integrability side conditions differ, and they are supplied
here by dominating `exp (m A (t + z))` by `exp b · exp (a|z|)` (and, on the product, by
`exp b · exp (a|p₁|) · exp (a|p₂|)`, using `Integrable.mul_prod`).
-/
public import ParisiFormula.ParisiOperator
public import ParisiFormula.GaussianCosh

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace SpinGlass

namespace Parisi

/-! ## 1. Exponential moments of `|z|` under a general real Gaussian -/

/-- `exp (a |z|)` is integrable under any real Gaussian, since `a|z|` is one of `az`, `-az`. -/
theorem integrable_exp_abs_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (a : ℝ) :
    Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal μ v) := by
  have hdom : Integrable (fun z : ℝ => Real.exp (a * z) + Real.exp (-a * z))
      (gaussianReal μ v) :=
    (integrable_exp_mul_gaussianReal a).add (integrable_exp_mul_gaussianReal (-a))
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal μ v) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have : 0 < Real.exp (-a * z) := Real.exp_pos _
    linarith
  · rw [abs_of_neg hz, show a * -z = -a * z by ring]
    have : 0 < Real.exp (a * z) := Real.exp_pos _
    linarith

/-! ## 2. The two integrability side conditions -/

/-- Pointwise domination of `exp (m A (t + z))` for `A` of linear growth. -/
theorem exp_mul_shift_le {A : ℝ → ℝ} {C D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ y, |A y| ≤ C + D * |y|) (m t z : ℝ) :
    Real.exp (m * A (t + z))
      ≤ Real.exp (|m| * (C + D * |t|)) * Real.exp ((|m| * D) * |z|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : m * A (t + z) ≤ |m| * |A (t + z)| := by
    calc m * A (t + z) ≤ |m * A (t + z)| := le_abs_self _
      _ = |m| * |A (t + z)| := abs_mul _ _
  have h2 : |A (t + z)| ≤ C + D * (|t| + |z|) := by
    refine (hb (t + z)).trans ?_
    have htri : |t + z| ≤ |t| + |z| := abs_add_le _ _
    nlinarith
  have h3 : |m| * |A (t + z)| ≤ |m| * (C + D * (|t| + |z|)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg m)
  have h4 : |m| * (C + D * (|t| + |z|))
      = |m| * (C + D * |t|) + (|m| * D) * |z| := by ring
  linarith

/-- `z ↦ exp (m A (t + z))` is `γ_{0,v}`-integrable for `A` of linear growth. -/
theorem integrable_exp_mul_shift_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m t : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (m * A (t + z))) (gaussianReal 0 v) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  have hmF : AEStronglyMeasurable (fun z : ℝ => Real.exp (m * A (t + z)))
      (gaussianReal 0 v) :=
    ((Real.continuous_exp.measurable).comp
      ((hmeas.comp (measurable_const_add t)).const_mul m)).aestronglyMeasurable
  have hdom : Integrable
      (fun z : ℝ => Real.exp (|m| * (C + D * |t|)) * Real.exp ((|m| * D) * |z|))
      (gaussianReal 0 v) :=
    (integrable_exp_abs_mul_gaussianReal 0 v (|m| * D)).const_mul _
  refine hdom.mono' hmF (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_mul_shift_le hD hb m t z

/-- The same, on the product measure, which is what the Fubini step of `T_add` needs. -/
theorem integrable_exp_mul_prod_of_hasLinearGrowth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m x : ℝ) (v₁ v₂ : ℝ≥0) :
    Integrable (fun p : ℝ × ℝ => Real.exp (m * A (x + (p.1 + p.2))))
      ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  have hmF : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (m * A (x + (p.1 + p.2))))
      ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)) := by
    have hmeas' : Measurable (fun p : ℝ × ℝ => Real.exp (m * A (x + (p.1 + p.2)))) := by
      have h1 : Measurable (fun p : ℝ × ℝ => x + (p.1 + p.2)) := by fun_prop
      exact (Real.continuous_exp.measurable).comp ((hmeas.comp h1).const_mul m)
    exact hmeas'.aestronglyMeasurable
  have hdom : Integrable
      (fun p : ℝ × ℝ =>
        (Real.exp (|m| * (C + D * |x|)) * Real.exp ((|m| * D) * |p.1|))
          * Real.exp ((|m| * D) * |p.2|))
      ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)) :=
    Integrable.mul_prod
      ((integrable_exp_abs_mul_gaussianReal 0 v₁ (|m| * D)).const_mul _)
      (integrable_exp_abs_mul_gaussianReal 0 v₂ (|m| * D))
  refine hdom.mono' hmF (Filter.Eventually.of_forall (fun p => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : m * A (x + (p.1 + p.2)) ≤ |m| * |A (x + (p.1 + p.2))| := by
    calc m * A (x + (p.1 + p.2)) ≤ |m * A (x + (p.1 + p.2))| := le_abs_self _
      _ = |m| * |A (x + (p.1 + p.2))| := abs_mul _ _
  have h2 : |A (x + (p.1 + p.2))| ≤ C + D * (|x| + (|p.1| + |p.2|)) := by
    refine (hb (x + (p.1 + p.2))).trans ?_
    have ht1 : |x + (p.1 + p.2)| ≤ |x| + |p.1 + p.2| := abs_add_le _ _
    have ht2 : |p.1 + p.2| ≤ |p.1| + |p.2| := abs_add_le _ _
    nlinarith
  have h3 : |m| * |A (x + (p.1 + p.2))| ≤ |m| * (C + D * (|x| + (|p.1| + |p.2|))) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg m)
  have h4 : |m| * (C + D * (|x| + (|p.1| + |p.2|)))
      = |m| * (C + D * |x|) + ((|m| * D) * |p.1| + (|m| * D) * |p.2|) := by ring
  linarith

/-! ## 3. The semigroup law under linear growth -/

/--
**`T_{m,v₁+v₂} = T_{m,v₁} ∘ T_{m,v₂}` for `A` of linear growth.**

Same statement as the vendored `Parisi.T_add`, but with `HasUniformBound` weakened to
`HasLinearGrowth` — which is the hypothesis every level of the Parisi recursion actually
satisfies (`Targets.parisiF_hasLinearGrowth`).
-/
theorem T_add_of_hasLinearGrowth (m : ℝ) (hm : m ≠ 0) (v₁ v₂ : ℝ≥0) {A : ℝ → ℝ}
    (hA_meas : Measurable A) (hA : HasLinearGrowth A) :
    T m (v₁ + v₂) A = fun x => T m v₁ (fun y => T m v₂ A y) x := by
  funext x
  let μ₁ : Measure ℝ := ProbabilityTheory.gaussianReal (0 : ℝ) v₁
  let μ₂ : Measure ℝ := ProbabilityTheory.gaussianReal (0 : ℝ) v₂
  let I : ℝ → ℝ := fun t => ∫ z : ℝ, Real.exp (m * A (t + z)) ∂μ₂
  have hI_pos : ∀ t, 0 < I t := by
    intro t
    have hint : Integrable (fun z : ℝ => Real.exp (m * A (t + z))) μ₂ :=
      integrable_exp_mul_shift_of_hasLinearGrowth hA hA_meas m t v₂
    haveI : NeZero μ₂ := by
      have hu : μ₂ Set.univ = 1 := by simp [μ₂]
      refine ⟨?_⟩
      intro h0
      have h0univ : (μ₂ Set.univ) = 0 := by simp [h0]
      have : (1 : ℝ≥0∞) = 0 := by simp [hu] at h0univ
      exact one_ne_zero this
    simpa [I, μ₂] using
      (MeasureTheory.integral_exp_pos (μ := μ₂) (f := fun z => m * A (t + z)) hint)
  have hstep :
      (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁)
        = ∫ z : ℝ, I (x + z) ∂μ₁ := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    have hpos : 0 < I (x + z) := hI_pos (x + z)
    simp [T, I, μ₂, hm, div_eq_mul_inv, Real.exp_log hpos]
  have hFubini :
      (∫ z₁ : ℝ, I (x + z₁) ∂μ₁)
        = ∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂) := by
    let F : ℝ × ℝ → ℝ := fun p => Real.exp (m * A (x + (p.1 + p.2)))
    have hF_meas : Measurable F := by
      have h1 : Measurable fun p : ℝ × ℝ => x + (p.1 + p.2) := by fun_prop
      exact (Real.continuous_exp.measurable).comp ((hA_meas.comp h1).const_mul m)
    have hF_int : Integrable F (μ₁.prod μ₂) :=
      integrable_exp_mul_prod_of_hasLinearGrowth hA hA_meas m x v₁ v₂
    have hleft :
        (∫ z₁ : ℝ, I (x + z₁) ∂μ₁) = ∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂) := by
      have hleft1 :
          (∫ z₁ : ℝ, I (x + z₁) ∂μ₁)
            = ∫ z₁ : ℝ, ∫ z₂ : ℝ, Real.exp (m * A (x + z₁ + z₂)) ∂μ₂ ∂μ₁ := by
        simp [I, add_left_comm, add_comm]
      have hleft2 :
          (∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂))
            = ∫ z₁ : ℝ, ∫ z₂ : ℝ, Real.exp (m * A (x + z₁ + z₂)) ∂μ₂ ∂μ₁ := by
        simpa [F, add_assoc, add_left_comm, add_comm] using
          (MeasureTheory.integral_prod F hF_int)
      exact hleft1.trans (by simpa using hleft2.symm)
    have hright :
        (∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂))
          = ∫ p : ℝ × ℝ, F p ∂(μ₁.prod μ₂) := by
      have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
      have hfm :
          AEStronglyMeasurable (fun z : ℝ => Real.exp (m * A (x + z)))
            (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ₁.prod μ₂)) := by
        have : Measurable (fun z : ℝ => Real.exp (m * A (x + z))) :=
          (Real.continuous_exp.measurable).comp
            ((hA_meas.comp (measurable_const_add x)).const_mul m)
        exact this.aestronglyMeasurable
      simpa [MeasureTheory.Measure.conv, F, add_assoc, add_left_comm, add_comm] using
        (MeasureTheory.integral_map (μ := (μ₁.prod μ₂))
          (φ := fun p : ℝ × ℝ => p.1 + p.2) hadd.aemeasurable
          (f := fun z : ℝ => Real.exp (m * A (x + z))) hfm)
    exact by simpa [hleft] using hright.symm
  have hGauss :
      (ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂) : Measure ℝ) = μ₁ ∗ μ₂ := by
    simpa [μ₁, μ₂, add_assoc, add_left_comm, add_comm] using
      (ProbabilityTheory.gaussianReal_conv_gaussianReal (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ))
        (v₁ := v₁) (v₂ := v₂)).symm
  have hInside :
      (∫ z : ℝ, Real.exp (m * A (x + z))
        ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂)))
        = (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁) := by
    calc
      (∫ z : ℝ, Real.exp (m * A (x + z))
        ∂(ProbabilityTheory.gaussianReal (0 : ℝ) (v₁ + v₂)))
          = ∫ z : ℝ, Real.exp (m * A (x + z)) ∂(μ₁ ∗ μ₂) := by simp [hGauss]
      _ = ∫ z₁ : ℝ, I (x + z₁) ∂μ₁ := by simp [hFubini]
      _ = (∫ z : ℝ, Real.exp (m * (T m v₂ A (x + z))) ∂μ₁) := by simp [hstep]
  simp [T, hInside, μ₁, hm, div_eq_mul_inv, mul_comm]

end Parisi

end SpinGlass
