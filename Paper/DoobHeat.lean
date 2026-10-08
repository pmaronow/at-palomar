module

public import Paper.Semigroup
public import Paper.DoobKernel
public import Paper.Hyperbolic

@[expose] public section

/-!
# Connecting the Gaussian Doob transform to the heat kernel

The equations below connect actual Gaussian expectations and actual heat
convolution. They establish the analytic identities in the proof of
Proposition 5.5, without asserting an SDE transition-law identification.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- Simultaneous reflection leaves the heat kernel unchanged. -/
theorem heatKernel_neg_neg (v : ℝ≥0) (x y : ℝ) :
    heatKernel v (-x) (-y) = heatKernel v x y := by
  unfold heatKernel gaussianPDFReal
  simp only [sub_zero]
  rw [show (-x - -y) ^ 2 = (x - y) ^ 2 by ring]

/-- Heat convolution preserves evenness, with no integrability assumption
needed for the measure-preserving reflection of the Bochner integral. -/
theorem kernelAverage_heatKernel_even (v : ℝ≥0) (k : ℝ → ℝ)
    (heven : ∀ y, k (-y) = k y) (x : ℝ) :
    kernelAverage (μ := volume) (heatKernel v) k (-x) =
      kernelAverage (μ := volume) (heatKernel v) k x := by
  unfold kernelAverage
  calc
    _ = ∫ y, heatKernel v (-x) (-y) * k (-y) :=
      (integral_neg_eq_self (fun y => heatKernel v (-x) y * k y) volume).symm
    _ = _ := by simp_rw [heatKernel_neg_neg, heven]

/-- Heat convolution is exactly Gaussian expectation at mean `x`. -/
theorem kernelAverage_heatKernel_eq_gaussian_integral
    (v : ℝ≥0) (hv : v ≠ 0) (k : ℝ → ℝ) (x : ℝ) :
    kernelAverage (μ := volume) (heatKernel v) k x = ∫ y, k y ∂gaussianReal x v := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [kernelAverage, heatKernel_eq_gaussianPDFReal, smul_eq_mul]

/-- Joint kernel measurability makes heat convolution measurable. -/
theorem measurable_kernelAverage_heatKernel (v : ℝ≥0) (k : ℝ → ℝ)
    (hk : Measurable k) :
    Measurable (kernelAverage (μ := volume) (heatKernel v) k) := by
  have hm := ((measurable_heatKernel v).mul (hk.comp measurable_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- A normalized Gaussian heat convolution preserves uniform bounds. -/
theorem norm_kernelAverage_heatKernel_le
    (v : ℝ≥0) (hv : v ≠ 0) (k : ℝ → ℝ)
    (C : ℝ) (hbound : ∀ y, ‖k y‖ ≤ C) (x : ℝ) :
    ‖kernelAverage (μ := volume) (heatKernel v) k x‖ ≤ C := by
  rw [kernelAverage_heatKernel_eq_gaussian_integral v hv k x]
  simpa using (norm_integral_le_of_norm_le_const
    (μ := gaussianReal x v) (Filter.Eventually.of_forall hbound))

/-- The Gaussian operator and its heat-kernel formula agree for every test
function at positive variance. -/
theorem doobOperator_eq_heat (v : ℝ≥0) (hv : v ≠ 0) (ψ : ℝ → ℝ) (x : ℝ) :
    doobOperator v ψ x = Real.exp (-(v : ℝ) / 2) / Real.cosh x *
      kernelAverage (μ := volume) (heatKernel v) (fun y => Real.cosh y * ψ y) x := by
  rw [kernelAverage_heatKernel_eq_gaussian_integral v hv]
  rfl

/-- The Doob transform sends measurable test functions to measurable
functions of the starting point, including at time zero. -/
theorem measurable_doobOperator (v : ℝ≥0) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    Measurable (doobOperator v ψ) := by
  by_cases hv : v = 0
  · subst v
    have heq : doobOperator 0 ψ = ψ := funext (doobOperator_zero ψ)
    rw [heq]
    exact hψ
  · have heq : doobOperator v ψ = fun x => Real.exp (-(v : ℝ) / 2) / Real.cosh x *
        kernelAverage (μ := volume) (heatKernel v) (fun y => Real.cosh y * ψ y) x := by
      funext x
      exact doobOperator_eq_heat v hv ψ x
    rw [heq]
    exact (measurable_const.div Real.continuous_cosh.measurable).mul
      (measurable_kernelAverage_heatKernel v _ (Real.continuous_cosh.measurable.mul hψ))

/-- The reciprocal-cosh cancellation used when applying the Doob transform
to `sech⁴`. -/
theorem cosh_mul_sech_fourth (y : ℝ) : Real.cosh y * sech y ^ 4 = sech y ^ 3 := by
  unfold sech
  have h : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp

/-- The Doob transform of `sech⁴` is the scaled heat convolution of `sech³`. -/
theorem doobOperator_sech_fourth_eq_heat
    (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    doobOperator v (fun y => sech y ^ 4) x =
      Real.exp (-(v : ℝ) / 2) / Real.cosh x *
        kernelAverage (μ := volume) (heatKernel v) (fun y => sech y ^ 3) x := by
  unfold doobOperator kernelAverage
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, cosh_mul_sech_fourth, heatKernel_eq_gaussianPDFReal]

/-- The heat convolution of `sech³` is even. -/
theorem heatAverage_sech_cube_even (v : ℝ≥0) (x : ℝ) :
    kernelAverage (μ := volume) (heatKernel v) (fun y => sech y ^ 3) (-x) =
      kernelAverage (μ := volume) (heatKernel v) (fun y => sech y ^ 3) x :=
  kernelAverage_heatKernel_even v (fun y => sech y ^ 3) (by intro y; simp) x

/-- The heat convolution of `sech³` is measurable. -/
theorem heatAverage_sech_cube_measurable (v : ℝ≥0) :
    Measurable (kernelAverage (μ := volume) (heatKernel v) (fun y => sech y ^ 3)) := by
  apply measurable_kernelAverage_heatKernel
  unfold sech
  fun_prop

/-- The heat convolution of `sech³` has absolute value at most one. -/
theorem heatAverage_sech_cube_bound (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    ‖kernelAverage (μ := volume) (heatKernel v) (fun y => sech y ^ 3) x‖ ≤ 1 := by
  apply norm_kernelAverage_heatKernel_le v hv (fun y => sech y ^ 3) 1
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le 3)]
  exact pow_le_one₀ (sech_pos y).le (sech_le_one y)

end Paper
