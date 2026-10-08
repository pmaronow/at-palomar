module

public import Lemmas.GuerraTalagrand.Bound.Basic
public import Lemmas.SmartPath.IndependentEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

open SpinGlass.GeneralizedLatala

/-- One scalar Gaussian recursion step with arbitrary coefficients. -/
noncomputable def gtScalarStep
    (m a b : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x₁ x₂ =>
  if m = 0 then
    standardGaussianExpectation fun z => F (x₁ + a * z) (x₂ + b * z)
  else
    (1 / m) * Real.log (standardGaussianExpectation fun z =>
      Real.exp (m * F (x₁ + a * z) (x₂ + b * z)))

/-- The same recursion step, with one independent Gaussian coordinate per site. -/
noncomputable def gtVectorStep
    (N : ℕ) (m a b : ℝ)
    (F : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) :
    (Fin N → ℝ) → (Fin N → ℝ) → ℝ := fun x₁ x₂ =>
  if m = 0 then
    ∫ z, F (fun i => x₁ i + a * z i) (fun i => x₂ i + b * z i)
      ∂gaussianProduct N
  else
    (1 / m) * Real.log (∫ z,
      Real.exp (m * F (fun i => x₁ i + a * z i)
        (fun i => x₂ i + b * z i)) ∂gaussianProduct N)

lemma gtScalarStep_eq_rankOne
    (m scale sign : ℝ) (F : GTTwoField) :
    gtScalarStep m scale (sign * scale) F =
      gtRankOneStep m scale sign F := by
  funext x₁ x₂
  simp [gtScalarStep, gtRankOneStep]

/-- Tensorization of one Gaussian recursion step over independent sites. -/
lemma gtVectorStep_sum
    {N : ℕ} (m a b : ℝ) (f : Fin N → GTTwoField)
    (x₁ x₂ : Fin N → ℝ)
    (hInt : ∀ i, Integrable
      (fun z => f i (x₁ i + a * z) (x₂ i + b * z)) (gaussianReal 0 1))
    (hPos : m ≠ 0 → ∀ i, 0 < ∫ z,
      Real.exp (m * f i (x₁ i + a * z) (x₂ i + b * z))
        ∂gaussianReal 0 1) :
    gtVectorStep N m a b
        (fun y₁ y₂ => ∑ i, f i (y₁ i) (y₂ i)) x₁ x₂ =
      ∑ i, gtScalarStep m a b (f i) (x₁ i) (x₂ i) := by
  classical
  by_cases hm : m = 0
  · simp only [gtVectorStep, gtScalarStep, if_pos hm]
    have hcoord (i : Fin N) : Integrable
        (fun z : Fin N → ℝ => f i (x₁ i + a * z i) (x₂ i + b * z i))
        (gaussianProduct N) := by
      exact ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
        (hInt i).aestronglyMeasurable).2 (hInt i)
    rw [integral_finset_sum Finset.univ (fun i _ => hcoord i)]
    apply Finset.sum_congr rfl
    intro i _
    unfold standardGaussianExpectation gaussianProduct
    exact integral_comp_eval
      (i := i) (μ := fun _ : Fin N => gaussianReal 0 1)
      (f := fun z => f i (x₁ i + a * z) (x₂ i + b * z))
      (hInt i).aestronglyMeasurable
  · simp only [gtVectorStep, gtScalarStep, if_neg hm]
    have hexp (z : Fin N → ℝ) :
        Real.exp (m * ∑ i, f i (x₁ i + a * z i) (x₂ i + b * z i)) =
          ∏ i, Real.exp (m * f i (x₁ i + a * z i) (x₂ i + b * z i)) := by
      rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [hexp]
    unfold gaussianProduct standardGaussianExpectation
    rw [show (∫ z : Fin N → ℝ,
        ∏ i, Real.exp (m * f i (x₁ i + a * z i) (x₂ i + b * z i))
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
        ∏ i, ∫ z : ℝ,
          Real.exp (m * f i (x₁ i + a * z) (x₂ i + b * z))
            ∂gaussianReal 0 1 by
      exact integral_fintype_prod_eq_prod
        (fun i z => Real.exp (m * f i (x₁ i + a * z) (x₂ i + b * z)))]
    rw [Real.log_prod (fun i _ => (hPos hm i).ne')]
    rw [Finset.mul_sum]

/-- A vector rank-one step tensorizes into the existing scalar rank-one step. -/
lemma gtVectorRankStep_sum
    {N : ℕ} (m scale sign : ℝ) (f : Fin N → GTTwoField)
    (x₁ x₂ : Fin N → ℝ)
    (hInt : ∀ i, Integrable
      (fun z => f i (x₁ i + scale * z)
        (x₂ i + sign * scale * z)) (gaussianReal 0 1))
    (hPos : m ≠ 0 → ∀ i, 0 < ∫ z,
      Real.exp (m * f i (x₁ i + scale * z)
        (x₂ i + sign * scale * z)) ∂gaussianReal 0 1) :
    gtVectorStep N m scale (sign * scale)
        (fun y₁ y₂ => ∑ i, f i (y₁ i) (y₂ i)) x₁ x₂ =
      ∑ i, gtRankOneStep m scale sign (f i) (x₁ i) (x₂ i) := by
  rw [gtVectorStep_sum m scale (sign * scale) f x₁ x₂ hInt hPos]
  simp_rw [gtScalarStep_eq_rankOne]

end SpinGlass.AT
