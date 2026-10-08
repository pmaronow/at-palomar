module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

@[expose] public section

/-!
# The Gaussian cosh transform in Proposition 5.4

The analytic Gaussian operator below is a positive operator preserving the
constant one. This file does not identify it with an SDE transition law;
that identification requires the separate backward-equation and Markov
arguments in the paper.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- Hyperbolic cosine is integrable under every real Gaussian measure,
including the zero-variance Dirac case. -/
theorem integrable_cosh_gaussianReal (x : ℝ) (v : ℝ≥0) :
    Integrable Real.cosh (gaussianReal x v) := by
  have hp : Integrable (fun y : ℝ => Real.exp y) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) 1)
  have hn : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) (-1))
  convert (hp.add hn).div_const 2 using 1
  ext y
  simp [Real.cosh_eq]

/-- The exact cosh eigenfunction identity used to normalize the Doob transform. -/
theorem integral_cosh_gaussianReal (x : ℝ) (v : ℝ≥0) :
    (∫ y, Real.cosh y ∂gaussianReal x v) = Real.exp ((v : ℝ) / 2) * Real.cosh x := by
  have hp : Integrable (fun y : ℝ => Real.exp y) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) 1)
  have hn : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) (-1))
  have hIp : (∫ y, Real.exp y ∂gaussianReal x v) = Real.exp (x + (v : ℝ) / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := x) (v := v)) 1
    simpa [mgf] using h
  have hIn : (∫ y, Real.exp (-y) ∂gaussianReal x v) = Real.exp (-x + (v : ℝ) / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := x) (v := v)) (-1)
    simpa [mgf] using h
  simp_rw [Real.cosh_eq]
  rw [integral_div, integral_add hp hn, hIp, hIn, Real.exp_add, Real.exp_add]
  ring

/-- The Gaussian form of the paper's cosh Doob transform. -/
def doobOperator (v : ℝ≥0) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(v : ℝ) / 2) / Real.cosh x *
    ∫ y, Real.cosh y * ψ y ∂gaussianReal x v

/-- Multiplying cosh by a bounded measurable function is Gaussian-integrable. -/
theorem integrable_cosh_mul_gaussianReal (x : ℝ) (v : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (C : ℝ) (hbound : ∀ y, ‖ψ y‖ ≤ C) :
    Integrable (fun y => Real.cosh y * ψ y) (gaussianReal x v) :=
  (integrable_cosh_gaussianReal x v).mul_bdd hψ.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The Doob transform preserves positivity. -/
theorem doobOperator_nonneg (v : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : ∀ y, 0 ≤ ψ y) (x : ℝ) : 0 ≤ doobOperator v ψ x := by
  unfold doobOperator
  apply mul_nonneg
  · exact div_nonneg (Real.exp_pos _).le (Real.cosh_pos x).le
  · apply integral_nonneg
    intro y
    change 0 ≤ Real.cosh y * ψ y
    exact mul_nonneg (Real.cosh_pos y).le (hψ y)

/-- The Doob transform preserves the constant one, at every variance. -/
theorem doobOperator_one (v : ℝ≥0) (x : ℝ) :
    doobOperator v (fun _ => 1) x = 1 := by
  unfold doobOperator
  simp only [mul_one]
  rw [integral_cosh_gaussianReal]
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp
  rw [← Real.exp_add]
  simp

/-- Every real constant is preserved by the Doob transform. -/
theorem doobOperator_const (v : ℝ≥0) (x c : ℝ) :
    doobOperator v (fun _ => c) x = c := by
  unfold doobOperator
  rw [integral_mul_const, ← mul_assoc]
  have hone := doobOperator_one v x
  simp only [doobOperator, mul_one] at hone
  rw [hone, one_mul]

/-- Monotonicity of the transform, with the exact integral hypotheses needed
for comparison of Bochner integrals. -/
theorem doobOperator_mono_of_integrable
    (v : ℝ≥0) (x : ℝ) (ψ χ : ℝ → ℝ)
    (hψ : Integrable (fun y => Real.cosh y * ψ y) (gaussianReal x v))
    (hχ : Integrable (fun y => Real.cosh y * χ y) (gaussianReal x v))
    (hle : ∀ y, ψ y ≤ χ y) :
    doobOperator v ψ x ≤ doobOperator v χ x := by
  unfold doobOperator
  apply mul_le_mul_of_nonneg_left
  · exact integral_mono hψ hχ (fun y =>
      mul_le_mul_of_nonneg_left (hle y) (Real.cosh_pos y).le)
  · exact div_nonneg (Real.exp_pos _).le (Real.cosh_pos x).le

/-- The Doob transform does not increase a uniform bound. This is the bound
used for the paper's compactly supported test functions. -/
theorem norm_doobOperator_le (v : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (C : ℝ) (hbound : ∀ y, ‖ψ y‖ ≤ C) (x : ℝ) :
    ‖doobOperator v ψ x‖ ≤ C := by
  have hint := integrable_cosh_mul_gaussianReal x v ψ hψ C hbound
  have hlow : ∀ y, -C ≤ ψ y := fun y => (abs_le.mp (by simpa using hbound y)).1
  have hupp : ∀ y, ψ y ≤ C := fun y => (abs_le.mp (by simpa using hbound y)).2
  have hleft := doobOperator_mono_of_integrable v x (fun _ => -C) ψ
    ((integrable_cosh_gaussianReal x v).mul_const (-C)) hint hlow
  have hright := doobOperator_mono_of_integrable v x ψ (fun _ => C)
    hint ((integrable_cosh_gaussianReal x v).mul_const C) hupp
  rw [doobOperator_const] at hleft hright
  simpa only [Real.norm_eq_abs] using abs_le.mpr ⟨hleft, hright⟩

/-- The transform is linear whenever the weighted integrands are integrable. -/
theorem doobOperator_add_of_integrable
    (v : ℝ≥0) (x : ℝ) (ψ χ : ℝ → ℝ)
    (hψ : Integrable (fun y => Real.cosh y * ψ y) (gaussianReal x v))
    (hχ : Integrable (fun y => Real.cosh y * χ y) (gaussianReal x v)) :
    doobOperator v (fun y => ψ y + χ y) x = doobOperator v ψ x + doobOperator v χ x := by
  unfold doobOperator
  simp_rw [mul_add]
  rw [integral_add hψ hχ, mul_add]

/-- Scalar linearity does not require an integrability hypothesis because
Bochner integration commutes with multiplication by a real constant. -/
theorem doobOperator_mul_const (v : ℝ≥0) (x c : ℝ) (ψ : ℝ → ℝ) :
    doobOperator v (fun y => ψ y * c) x = doobOperator v ψ x * c := by
  unfold doobOperator
  simp_rw [← mul_assoc]
  rw [integral_mul_const, mul_assoc]

/-- At variance zero the Gaussian measure is a Dirac mass, so the transform
is the identity operator, as required by the initial condition in the paper. -/
@[simp] theorem doobOperator_zero (ψ : ℝ → ℝ) (x : ℝ) :
    doobOperator 0 ψ x = ψ x := by
  simp only [doobOperator, NNReal.coe_zero, neg_zero, zero_div, Real.exp_zero,
    gaussianReal_zero_var, integral_dirac]
  have h : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp

end Paper
