module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section

/-!
# A square root for positive semidefinite real matrices

Mathlib (at the version pinned by this project) provides the continuous functional calculus for
Hermitian matrices, but no packaged square root of a positive semidefinite matrix.  This file
supplies the small amount of API we need: a total function `psdSqrt` which, on positive
semidefinite matrices, is a symmetric square root.
-/

open Matrix

namespace PriceFourier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square root of a real matrix, defined through the continuous functional calculus for
Hermitian matrices (and junk-valued at non-Hermitian matrices). -/
noncomputable def psdSqrt (S : Matrix n n ℝ) : Matrix n n ℝ :=
  if h : S.IsHermitian then h.cfc Real.sqrt else 0

theorem psdSqrt_isHermitian (S : Matrix n n ℝ) : (psdSqrt S).IsHermitian := by
  rw [psdSqrt]
  split
  · rename_i hH
    rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have : IsSelfAdjoint (diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hH.eigenvalues) : Matrix n n ℝ) := by
      rw [isSelfAdjoint_iff, star_eq_conjTranspose, diagonal_conjTranspose]
      congr 1
    exact (this.conjugate' _ : _)
  · exact isHermitian_zero

theorem psdSqrt_transpose (S : Matrix n n ℝ) : (psdSqrt S)ᵀ = psdSqrt S := by
  have := psdSqrt_isHermitian S
  rw [Matrix.IsHermitian] at this
  ext i j
  simpa [Matrix.conjTranspose_apply] using congrFun (congrFun this i) j

theorem psdSqrt_mul_self {S : Matrix n n ℝ} (h : S.PosSemidef) :
    psdSqrt S * psdSqrt S = S := by
  have hH : S.IsHermitian := h.isHermitian
  rw [psdSqrt, dif_pos hH, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix n n ℝ := (hH.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  set D : Matrix n n ℝ := diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hH.eigenvalues) with hDdef
  have hs : star U * U = 1 := by
    exact_mod_cast Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hDD : D * D = diagonal hH.eigenvalues := by
    rw [hDdef, diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (h.eigenvalues_nonneg i)
  have hassoc : star U * (U * D) = (star U * U) * D := by rw [Matrix.mul_assoc]
  have key : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
    rw [Matrix.mul_assoc (U * D), ← Matrix.mul_assoc (star U) (U * D) (star U), hassoc, hs, one_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [key, hDD]
  conv_rhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  simp [hUdef]

theorem psdSqrt_mul_transpose {S : Matrix n n ℝ} (h : S.PosSemidef) :
    psdSqrt S * (psdSqrt S)ᵀ = S := by
  rw [psdSqrt_transpose, psdSqrt_mul_self h]

omit [DecidableEq n] in
/-- The trace of `M * Mᵀ` is the squared Frobenius norm of `M`. -/
theorem trace_mul_transpose {m : Type*} [Fintype m] (M : Matrix n m ℝ) :
    (M * Mᵀ).trace = ∑ i, ∑ j, (M i j) ^ 2 := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diag, sq]

end PriceFourier
