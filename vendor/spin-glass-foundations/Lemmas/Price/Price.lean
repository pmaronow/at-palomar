module

public import Lemmas.Price.Cosh

@[expose] public section

/-!
# Price's formula for a product of hyperbolic tangents

For fixed `A q s h`, let

  ρ(B) = (1 - s) q + s B

and let `(Y₁(B), Y₂(B))` be Gaussian with common mean `h`,
common variance `A`, and covariance `A * ρ(B)`.

Then

  d/dB E[tanh(Y₁(B)) tanh(Y₂(B))]
    = A * s * E[sech²(Y₁(B)) sech²(Y₂(B))].
-/

open Matrix MeasureTheory Set
open scoped RealInnerProductSpace

namespace ProbabilityTheory.PriceTanh

abbrev Pair := Fin 2

/-- `sech² x = 1 - tanh² x`. -/
noncomputable def sechSq (x : ℝ) : ℝ :=
  1 - Real.tanh x ^ 2

lemma tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (sechSq x) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  apply ((Real.hasDerivAt_sinh x).div
    (Real.hasDerivAt_cosh x) hc).congr_deriv
  rw [sechSq, Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]

/-- The correlation parameter along the interpolation. -/
noncomputable def rho (q s B : ℝ) : ℝ :=
  (1 - s) * q + s * B

/-- Covariance matrix of the centered pair `(Y₁-h, Y₂-h)`. -/
noncomputable def tanhCov
    (A q s B : ℝ) : Matrix Pair Pair ℝ :=
  fun i j =>
    if i = j then A else A * rho q s B

/-- Observable after centering the Gaussian pair. -/
noncomputable def tanhPair
    (h : ℝ) (z : EuclideanSpace ℝ Pair) : ℝ :=
  Real.tanh (h + z 0) * Real.tanh (h + z 1)

