module

/- Compatibility adaptation: use current probability-map instance. -/
public import Lemmas.Price.Sqrt
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# Centered Gaussian measures on `EuclideanSpace ℝ n` with a prescribed covariance matrix

Mathlib provides the predicate `ProbabilityTheory.IsGaussian` and the one-dimensional
`gaussianReal`, but no constructor for a multivariate Gaussian with a prescribed covariance
matrix.  This file builds one.

* `stdGaussian n` is the standard Gaussian on `EuclideanSpace ℝ n`.
* `multivariateGaussian m S` is the Gaussian with mean `m` and covariance matrix `S`
  (for `S` positive semidefinite).
* `charFun_multivariateGaussian` computes its characteristic function.
* `map_matCLM_stdGaussian` says that the image of a standard Gaussian under any linear map `M`
  is the centered Gaussian with covariance `M * Mᵀ`; this is the source of all the
  "reparametrisation" identities used later.
-/

open Matrix MeasureTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal

namespace ProbabilityTheory
namespace PriceGaussian

variable {n m k : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k]

/-! ### Linear maps attached to matrices -/

/-- The continuous linear map on Euclidean spaces attached to a matrix. -/
noncomputable def matCLM (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

omit [DecidableEq m] in
@[simp] theorem matCLM_apply (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) (i : m) :
    matCLM M x i = ∑ j, M i j * x j := by
  simp [matCLM, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

theorem inner_matCLM (M : Matrix m n ℝ) (t : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    ⟪matCLM M x, t⟫ = ⟪x, matCLM Mᵀ t⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matCLM_apply,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem inner_matCLM' (M : Matrix m n ℝ) (t : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    ⟪t, matCLM M x⟫ = ⟪matCLM Mᵀ t, x⟫ := by
  rw [real_inner_comm, inner_matCLM, real_inner_comm]

omit [DecidableEq m] in
theorem matCLM_mul (M : Matrix m n ℝ) (N : Matrix n k ℝ) (x : EuclideanSpace ℝ k) :
    matCLM (M * N) x = matCLM M (matCLM N x) := by
  ext i
  simp only [matCLM_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem norm_sq_matCLM_transpose (M : Matrix m n ℝ) (t : EuclideanSpace ℝ m) :
    ‖matCLM Mᵀ t‖ ^ 2 = ⟪t, matCLM (M * Mᵀ) t⟫ := by
  rw [matCLM_mul, inner_matCLM', real_inner_self_eq_norm_sq]

omit [DecidableEq m] in
theorem matCLM_add (M N : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    matCLM (M + N) x = matCLM M x + matCLM N x := by
  ext i
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-! ### The standard Gaussian -/

/-- The standard Gaussian measure on `EuclideanSpace ℝ n`. -/
noncomputable def stdGaussian (n : Type*) [Fintype n] : Measure (EuclideanSpace ℝ n) :=
  (Measure.pi fun _ : n => gaussianReal 0 1).map (WithLp.toLp 2)

instance instIsProbabilityMeasureStdGaussian (n : Type*) [Fintype n] :
    IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian
  infer_instance

theorem euclid_norm_sq {n : Type*} [Fintype n] (t : EuclideanSpace ℝ n) :
    ‖t‖ ^ 2 = ∑ i, (t i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

theorem charFun_stdGaussian (n : Type*) [Fintype n] (t : EuclideanSpace ℝ n) :
    charFun (stdGaussian n) t = Complex.exp (-((‖t‖ : ℂ) ^ 2) / 2) := by
  have hnc : (-((‖t‖ : ℂ)) ^ 2) / 2 = ∑ i, (-((t i : ℂ)) ^ 2 / 2) := by
    rw [show ((‖t‖ : ℂ)) ^ 2 = (((‖t‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring, euclid_norm_sq]
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [stdGaussian, MeasureTheory.charFun_pi]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum, hnc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The inner product, viewed as a positive semidefinite bilinear form. -/
theorem isPosSemidef_innerSL (n : Type*) [Fintype n] :
    ((innerSL ℝ : EuclideanSpace ℝ n →L[ℝ] _)).toBilinForm.IsPosSemidef :=
  ⟨⟨fun x y => real_inner_comm y x⟩, ⟨fun x => (real_inner_self_nonneg : (0 : ℝ) ≤ ⟪x, x⟫)⟩⟩

theorem charFun_stdGaussian' (n : Type*) [Fintype n] (t : EuclideanSpace ℝ n) :
    charFun (stdGaussian n) t
      = Complex.exp ((⟪t, (0 : EuclideanSpace ℝ n)⟫ : ℝ) * Complex.I
        - ((innerSL ℝ t t : ℝ)) / 2) := by
  rw [charFun_stdGaussian]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, coe_innerSL_apply]
  congr 1
  rw [real_inner_self_eq_norm_sq]
  push_cast
  ring

instance instIsGaussianStdGaussian (n : Type*) [Fintype n] : IsGaussian (stdGaussian n) := by
  rw [isGaussian_iff_gaussian_charFun]
  exact ⟨0, innerSL ℝ, isPosSemidef_innerSL n, charFun_stdGaussian' n⟩

theorem integral_stdGaussian_id (n : Type*) [Fintype n] :
    ∫ w, w ∂(stdGaussian n) = 0 :=
  (gaussian_charFun_congr (μ := stdGaussian n) 0 (innerSL ℝ) (isPosSemidef_innerSL n)
    (charFun_stdGaussian' n)).1.symm

theorem covarianceBilin_stdGaussian (n : Type*) [Fintype n] (x y : EuclideanSpace ℝ n) :
    covarianceBilin (stdGaussian n) x y = ⟪x, y⟫ := by
  have h := (gaussian_charFun_congr (μ := stdGaussian n) 0
    (innerSL ℝ : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ)
    (isPosSemidef_innerSL n) (charFun_stdGaussian' n)).2
  conv_lhs => rw [← h]
  rfl

/-- Second moments of the standard Gaussian. -/
theorem integral_inner_mul_inner_stdGaussian (n : Type*) [Fintype n]
    (x y : EuclideanSpace ℝ n) :
    ∫ w, ⟪x, w⟫ * ⟪y, w⟫ ∂(stdGaussian n) = ⟪x, y⟫ := by
  have hmem : MemLp id 2 (stdGaussian n) := IsGaussian.memLp_two_id
  have h := covarianceBilin_apply (μ := stdGaussian n) hmem x y
  rw [covarianceBilin_stdGaussian] at h
  rw [h]
  simp [integral_stdGaussian_id]

/-! ### The multivariate Gaussian -/

/-- The Gaussian measure on `EuclideanSpace ℝ n` with mean `mean` and covariance matrix `S`
(the definition is only meaningful for positive semidefinite `S`). -/
noncomputable def multivariateGaussian (mean : EuclideanSpace ℝ n) (S : Matrix n n ℝ) :
    Measure (EuclideanSpace ℝ n) :=
  (stdGaussian n).map (fun w => mean + matCLM (PriceFourier.psdSqrt S) w)

instance (mean : EuclideanSpace ℝ n) (S : Matrix n n ℝ) :
    IsProbabilityMeasure (multivariateGaussian mean S) := by
  unfold multivariateGaussian
  infer_instance

theorem multivariateGaussian_zero_eq (S : Matrix n n ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ n) S
      = (stdGaussian n).map (matCLM (PriceFourier.psdSqrt S)) := by
  unfold multivariateGaussian
  congr 1
  funext w
  simp

theorem charFun_map_fun {E F : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (μ : Measure E) (L : E → F) (hL : Measurable L) (t : F) :
    charFun (μ.map L) t = ∫ x, Complex.exp ((⟪L x, t⟫ : ℝ) * Complex.I) ∂μ := by
  rw [charFun_apply, integral_map hL.aemeasurable (by fun_prop)]

theorem charFun_map_matCLM (M : Matrix m n ℝ) (t : EuclideanSpace ℝ m) :
    charFun ((stdGaussian n).map (matCLM M)) t
      = Complex.exp (-((‖matCLM Mᵀ t‖ : ℂ) ^ 2) / 2) := by
  rw [charFun_map_fun _ _ (by fun_prop)]
  have h : ∀ x : EuclideanSpace ℝ n, ⟪matCLM M x, t⟫ = ⟪x, matCLM Mᵀ t⟫ := fun x =>
    inner_matCLM M t x
  simp_rw [h]
  rw [← charFun_apply (μ := stdGaussian n) (t := matCLM Mᵀ t)]
  exact charFun_stdGaussian n _

theorem charFun_multivariateGaussian {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (t : EuclideanSpace ℝ n) :
    charFun (multivariateGaussian 0 S) t = Complex.exp (-((⟪t, matCLM S t⟫ : ℝ) : ℂ) / 2) := by
  rw [multivariateGaussian_zero_eq, charFun_map_matCLM]
  congr 1
  rw [show ((‖matCLM (PriceFourier.psdSqrt S)ᵀ t‖ : ℂ)) ^ 2
      = ((‖matCLM (PriceFourier.psdSqrt S)ᵀ t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    norm_sq_matCLM_transpose, PriceFourier.psdSqrt_mul_transpose hS]

/-- The image of a standard Gaussian under a linear map is the centered Gaussian with
covariance `M * Mᵀ`. -/
theorem map_matCLM_stdGaussian (M : Matrix n m ℝ) :
    (stdGaussian m).map (matCLM M) = multivariateGaussian 0 (M * Mᵀ) := by
  have hpsd : (M * Mᵀ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose (A := M)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_matCLM, charFun_multivariateGaussian hpsd]
  congr 1
  rw [show ((‖matCLM Mᵀ t‖ : ℂ)) ^ 2 = ((‖matCLM Mᵀ t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    norm_sq_matCLM_transpose]

/-! ### Sums of independent Gaussians -/

theorem map_add_prod_stdGaussian (M : Matrix n m ℝ) (N : Matrix n k ℝ) :
    (((stdGaussian m).prod (stdGaussian k)).map
        (fun p => matCLM M p.1 + matCLM N p.2))
      = multivariateGaussian 0 (M * Mᵀ + N * Nᵀ) := by
  have hpsd : (M * Mᵀ + N * Nᵀ).PosSemidef :=
    (Matrix.posSemidef_self_mul_conjTranspose (A := M)).add
      (Matrix.posSemidef_self_mul_conjTranspose (A := N))
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_fun _ _ (by fun_prop), charFun_multivariateGaussian hpsd]
  have hsplit : ∀ p : EuclideanSpace ℝ m × EuclideanSpace ℝ k,
      Complex.exp ((⟪matCLM M p.1 + matCLM N p.2, t⟫ : ℝ) * Complex.I)
        = Complex.exp ((⟪p.1, matCLM Mᵀ t⟫ : ℝ) * Complex.I)
          * Complex.exp ((⟪p.2, matCLM Nᵀ t⟫ : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add, inner_add_left, inner_matCLM, inner_matCLM]
    congr 1
    push_cast
    ring
  simp_rw [hsplit]
  rw [MeasureTheory.integral_prod_mul
    (f := fun x : EuclideanSpace ℝ m => Complex.exp ((⟪x, matCLM Mᵀ t⟫ : ℝ) * Complex.I))
    (g := fun y : EuclideanSpace ℝ k => Complex.exp ((⟪y, matCLM Nᵀ t⟫ : ℝ) * Complex.I))]
  rw [← charFun_apply (μ := stdGaussian m) (t := matCLM Mᵀ t),
    ← charFun_apply (μ := stdGaussian k) (t := matCLM Nᵀ t)]
  rw [charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  rw [show ((‖matCLM Mᵀ t‖ : ℂ)) ^ 2 = ((‖matCLM Mᵀ t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show ((‖matCLM Nᵀ t‖ : ℂ)) ^ 2 = ((‖matCLM Nᵀ t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    norm_sq_matCLM_transpose, norm_sq_matCLM_transpose, matCLM_add, inner_add_right]
  push_cast
  ring

end PriceGaussian
end ProbabilityTheory
