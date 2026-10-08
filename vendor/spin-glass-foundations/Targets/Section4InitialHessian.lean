module

public import Targets.Section4HessianLipschitz

@[expose] public section

/-!
# The initial Hessian-square comparison

On the initial interval the baseline mass is zero. Cauchy--Schwarz for the
inner Gaussian expectation and the existing scalar Gaussian semigroup imply
`R(v) ≤ R(0)` on the entire physical interval. This is the Jensen argument in
Talagrand's proof of Proposition 5.3; no higher-derivative bound is needed.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Gaussian Jensen for a bounded scalar observable, reusing the existing
weighted Cauchy--Schwarz inequality at zero mass. -/
theorem parisiStep_zero_sq_le {G : ℝ → ℝ} (hG : Measurable G)
    (hbound : ∀ x, |G x| ≤ 1) (v x : ℝ) :
    (parisiStep 0 v G x) ^ 2 ≤ parisiStep 0 v (fun y => (G y) ^ 2) x := by
  have hA : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) :=
    ⟨0, 0, le_rfl, le_rfl, by simp⟩
  simpa [parisiStep] using
    (sq_integral_mul_le (A := fun _ => (0 : ℝ)) (m := 0) (v := v)
      hbound hA measurable_const hG x)

theorem integrable_gaussian_bounded_shift {G : ℝ → ℝ}
    (hG : Measurable G) (hbound : ∀ x, |G x| ≤ 1) (v x : ℝ) :
    Integrable (fun z => G (x + Real.sqrt v * z)) (gaussianReal 0 1) := by
  refine (integrable_const (1 : ℝ)).mono'
    (hG.comp (by fun_prop)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound _)

theorem abs_parisiStep_zero_le_one {G : ℝ → ℝ}
    (hbound : ∀ x, |G x| ≤ 1) (v x : ℝ) : |parisiStep 0 v G x| ≤ 1 := by
  simp only [parisiStep, ↓reduceIte]
  apply (abs_integral_le_integral_abs).trans
  have H := integral_mono_of_nonneg
    (μ := gaussianReal 0 1)
    (Filter.Eventually.of_forall (fun z : ℝ => abs_nonneg (G (x + Real.sqrt v * z))))
    (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall (fun z => hbound _))
  simpa using H

/-- Jensen and the Gaussian semigroup compare the squared inner conditional
mean with the unsplit square, with both zero-variance endpoints included. -/
theorem parisiStep_zero_split_square_le {G : ℝ → ℝ} (hG : Measurable G)
    (hbound : ∀ x, |G x| ≤ 1) {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (x : ℝ) :
    parisiStep 0 (a - v) (fun y => (parisiStep 0 v G y) ^ 2) x ≤
      parisiStep 0 a (fun y => (G y) ^ 2) x := by
  have hsq : ∀ y, |(G y) ^ 2| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := hbound y
    nlinarith [sq_abs (G y), abs_nonneg (G y)]
  have hinner : ∀ y, |(parisiStep 0 v G y) ^ 2| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := abs_parisiStep_zero_le_one hbound v y
    nlinarith [sq_abs (parisiStep 0 v G y), abs_nonneg (parisiStep 0 v G y)]
  have hA : HasLinearGrowth (fun y => (G y) ^ 2) :=
    ⟨1, 0, zero_le_one, le_rfl, by simpa using hsq⟩
  have hsemigroup := congrFun
    (parisiStep_add 0 (a - v) v (sub_nonneg.mpr hv.2) hv.1 hA (hG.pow_const 2)) x
  rw [sub_add_cancel] at hsemigroup
  rw [hsemigroup]
  have H := integral_mono
    (integrable_gaussian_bounded_shift ((measurable_parisiStep hG 0 v).pow_const 2)
      hinner (a - v) x)
    (integrable_gaussian_bounded_shift (measurable_parisiStep (hG.pow_const 2) 0 v)
      (abs_parisiStep_zero_le_one hsq v) (a - v) x)
    (fun z => parisiStep_zero_sq_le hG hbound v (x + Real.sqrt (a - v) * z))
  simpa [parisiStep] using H

/-- At mass zero the actual smoothed Hessian is a Gaussian mean of the input
Hessian. This identity is valid even at zero variance. -/
theorem stepD2_zero_mass_eq_parisiStep (A A' A'' : ℝ → ℝ) (v x : ℝ) :
    stepD2 A A' A'' 0 v x = parisiStep 0 v A'' x := by
  simp [stepD2, tiltQ, tiltE, parisiStep]

/-- Talagrand's initial-interval Jensen comparison for the actual nested
Hessian-square factor, uniformly on its closed physical variance interval. -/
theorem section4THessianSquare_initial_le_zero {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1)) :
    section4THessianSquare s β h 1 v ≤ section4THessianSquare s β h 1 0 := by
  have heq : ∀ w : ℝ, section4THessianSquare s β h 1 w =
      parisiStep 0 (β ^ 2 * s.q 1 - w)
        (fun y => (parisiStep 0 w (parisiFSecond s β (k + 1)) y) ^ 2) h := by
    intro w
    simp only [section4THessianSquare, Nat.sub_self, s.m_zero,
      section4VarianceR_initial_eq_scalar_integral, s.q_zero, sub_zero]
    simp [stepD2_zero_mass_eq_parisiStep, tiltWeight, parisiStep]
  rw [heq v, heq 0]
  simp only [sub_zero, parisiStep_zero_var]
  exact parisiStep_zero_split_square_le (parisiF_C2_props s β _).2.2
    (parisiF_C2_props s β _).1.abs_second_le_one hv h

end SpinGlass.Targets
