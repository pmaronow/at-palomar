module

public import Paper.Hyperbolic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The symmetrized Gaussian weight in Proposition 5.5

The formula in the paper is proved for the actual Gaussian density, and
relates its symmetrized weight to the radial function analyzed in
`Paper.Hyperbolic`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The exact weight obtained by symmetrizing the Gaussian density. -/
def symmetrizedWeight (h : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianPDFReal h v x + gaussianPDFReal h v (-x)) / (2 * Real.cosh x)

/-- Factoring the Gaussian density gives the radial formula in the paper. -/
theorem symmetrizedWeight_eq_radialWeight (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    symmetrizedWeight h v x =
      gaussianPDFReal h v 0 * radialWeight (v : ℝ) (h / (v : ℝ)) x := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hp : -(x - h) ^ 2 / (2 * (v : ℝ)) =
      -h ^ 2 / (2 * (v : ℝ)) + (-x ^ 2 / (2 * (v : ℝ)) + h / (v : ℝ) * x) := by
    field_simp
    ring
  have hn : -(-x - h) ^ 2 / (2 * (v : ℝ)) =
      -h ^ 2 / (2 * (v : ℝ)) + (-x ^ 2 / (2 * (v : ℝ)) - h / (v : ℝ) * x) := by
    field_simp
    ring
  unfold symmetrizedWeight radialWeight gaussianPDFReal
  simp only [zero_sub, neg_sq]
  rw [hp, hn, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_sub, Real.cosh_eq (h / (v : ℝ) * x)]
  rw [Real.exp_neg]
  field_simp

/-- The symmetrized density weight is even. -/
@[simp] theorem symmetrizedWeight_neg (h : ℝ) (v : ℝ≥0) (x : ℝ) :
    symmetrizedWeight h v (-x) = symmetrizedWeight h v x := by
  simp [symmetrizedWeight, add_comm]

/-- Nonnegativity of the actual symmetrized Gaussian weight. -/
theorem symmetrizedWeight_nonneg (h : ℝ) (v : ℝ≥0) (x : ℝ) :
    0 ≤ symmetrizedWeight h v x := by
  unfold symmetrizedWeight
  exact div_nonneg
    (add_nonneg (gaussianPDFReal_nonneg h v x) (gaussianPDFReal_nonneg h v (-x)))
    (mul_nonneg (by norm_num) (Real.cosh_pos x).le)

/-- For `0 ≤ h ≤ v`, the actual symmetrized Gaussian weight decreases
strictly on the nonnegative half-line. -/
theorem symmetrizedWeight_strictAntiOn (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ)) :
    StrictAntiOn (symmetrizedWeight h v) (Set.Ici 0) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hc0 : 0 ≤ h / (v : ℝ) := div_nonneg hh0 hvpos.le
  have hc1 : h / (v : ℝ) ≤ 1 := (div_le_one hvpos).mpr hhv
  intro x hx y hy hxy
  rw [symmetrizedWeight_eq_radialWeight h v hv y,
    symmetrizedWeight_eq_radialWeight h v hv x]
  exact mul_lt_mul_of_pos_left
    (radialWeight_strictAntiOn hvpos hc0 hc1 hx hy hxy)
    (gaussianPDFReal_pos h v 0 hv)

/-- Co-monotonicity for the exact two functions appearing in Proposition 5.5. -/
theorem symmetrizedWeight_sech_cube_comonotone
    (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ))
    (x y : ℝ) :
    0 ≤ (symmetrizedWeight h v x - symmetrizedWeight h v y) *
      (sech x ^ 3 - sech y ^ 3) := by
  exact sech_cube_comonotone (symmetrizedWeight_neg h v)
    (symmetrizedWeight_strictAntiOn h v hv hh0 hhv).antitoneOn x y

end Paper
