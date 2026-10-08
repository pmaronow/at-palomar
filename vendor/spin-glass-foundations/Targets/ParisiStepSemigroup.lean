module

public import Targets.Milestones
public import ParisiFormula.ParisiOperatorGrowth
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-!
# The scalar Parisi semigroup, including zero mass

The nonzero-mass statement is an adapter to `Parisi.T_add_of_hasLinearGrowth`.
At zero mass the actual `parisiStep` is a Gaussian expectation rather than the
totalized expression `Parisi.T 0`; Mathlib's convolution integral proves that
branch directly. No boundedness or nondegenerate-variance assumption is imposed.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace SpinGlass.Targets

theorem measurable_parisiStep {A : ℝ → ℝ} (hmeas : Measurable A) (m v : ℝ) :
    Measurable (parisiStep m v A) := by
  change Measurable (fun x => parisiStep m v A x)
  have hj : Measurable (fun p : ℝ × ℝ => A (p.1 + Real.sqrt v * p.2)) :=
    hmeas.comp (by fun_prop)
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm]
    exact hj.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [parisiStep, if_neg hm]
    exact (((hj.const_mul m).exp.stronglyMeasurable.integral_prod_right').measurable.log).const_mul
      (1 / m)

private theorem integrable_gaussian_shift_linear {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => A (x + z)) (gaussianReal 0 v) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  have hid : Integrable (fun z : ℝ => |z|) (gaussianReal 0 v) := by
    simpa only [Real.norm_eq_abs, id_eq] using (IsGaussian.integrable_id (μ := gaussianReal 0 v)).norm
  refine ((integrable_const (C + D * |x|)).add (hid.const_mul D)).mono'
    (hmeas.comp (measurable_const_add x)).aestronglyMeasurable ?_
  filter_upwards with z
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  exact (hb (x + z)).trans (by nlinarith [abs_add_le x z])

/-- The actual Gaussian smoothing semigroup, including zero masses and variances. -/
theorem parisiStep_add (m v₁ v₂ : ℝ) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {A : ℝ → ℝ} (hA : HasLinearGrowth A) (hmeas : Measurable A) :
    parisiStep m (v₁ + v₂) A = fun x => parisiStep m v₁ (parisiStep m v₂ A) x := by
  let w₁ : ℝ≥0 := ⟨v₁, hv₁⟩
  let w₂ : ℝ≥0 := ⟨v₂, hv₂⟩
  by_cases hm : m = 0
  · subst m
    funext x
    have hinner : ∀ y, parisiStep 0 v₂ A y =
        ∫ z, A (y + z) ∂(gaussianReal 0 w₂) := by
      intro y
      simpa [parisiStep, w₂] using! integral_comp_sqrt_mul_gaussianReal w₂ hmeas y
    have hconv : Integrable (fun z => A (x + z))
        ((gaussianReal 0 w₁) ∗ (gaussianReal 0 w₂)) := by
      simpa only [gaussianReal_conv_gaussianReal, zero_add] using
        integrable_gaussian_shift_linear hA hmeas (w₁ + w₂) x
    calc
      parisiStep 0 (v₁ + v₂) A x =
          ∫ z, A (x + z) ∂(gaussianReal 0 (w₁ + w₂)) := by
        simpa [parisiStep, w₁, w₂] using!
          integral_comp_sqrt_mul_gaussianReal (w₁ + w₂) hmeas x
      _ = ∫ z, ∫ y, A ((x + z) + y) ∂(gaussianReal 0 w₂) ∂(gaussianReal 0 w₁) := by
        simpa only [gaussianReal_conv_gaussianReal, zero_add, add_assoc] using integral_conv hconv
      _ = ∫ z, parisiStep 0 v₂ A (x + z) ∂(gaussianReal 0 w₁) := by
        simp_rw [hinner]
      _ = parisiStep 0 v₁ (parisiStep 0 v₂ A) x := by
        simpa [parisiStep, w₁] using!
          (integral_comp_sqrt_mul_gaussianReal w₁ (measurable_parisiStep hmeas 0 v₂) x).symm
  · funext x
    have hinner : parisiStep m v₂ A = Parisi.T m w₂ A := by
      funext y
      exact parisiStep_eq_T hm w₂ hmeas y
    calc
      parisiStep m (v₁ + v₂) A x = Parisi.T m (w₁ + w₂) A x := by
        simpa [w₁, w₂] using! parisiStep_eq_T hm (w₁ + w₂) hmeas x
      _ = Parisi.T m w₁ (Parisi.T m w₂ A) x :=
        congrFun (Parisi.T_add_of_hasLinearGrowth m hm w₁ w₂ hmeas hA) x
      _ = parisiStep m v₁ (parisiStep m v₂ A) x := by
        rw [← hinner]
        exact (parisiStep_eq_T hm w₁ (measurable_parisiStep hmeas m v₂) x).symm

end SpinGlass.Targets
