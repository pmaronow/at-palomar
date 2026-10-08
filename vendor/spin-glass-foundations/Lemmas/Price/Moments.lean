module

public import Lemmas.Price.Gaussian
public import Lemmas.Price.Taylor

@[expose] public section

/-!
# Moments, tails and change-of-variables for multivariate Gaussians

This file collects the quantitative facts about `stdGaussian` and `multivariateGaussian` used in
the proof of Price's theorem:

* change of variables `∫ f d(multivariateGaussian 0 S) = ∫ f (√S w) dγ(w)`;
* the convolution identity `N(0, S + T) = N(0,S) * N(0,T)`;
* first and second moments of a linear image of the standard Gaussian;
* an operator bound `‖M w‖ ≤ ‖M‖_F ‖w‖` with `‖√S‖_F = √(tr S)`;
* smallness of Gaussian tails.
-/

open Matrix MeasureTheory Filter PriceFourier
open scoped RealInnerProductSpace ENNReal NNReal

namespace ProbabilityTheory

open PriceGaussian

local notation "stdGaussian" => PriceGaussian.stdGaussian
local notation "multivariateGaussian" => PriceGaussian.multivariateGaussian
local notation "integral_stdGaussian_id" => PriceGaussian.integral_stdGaussian_id

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The Frobenius norm -/

/-- The Frobenius norm of a matrix. -/
noncomputable def frob {m : Type*} [Fintype m] (M : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

omit [DecidableEq n] in
theorem frob_nonneg {m : Type*} [Fintype m] (M : Matrix m n ℝ) : 0 ≤ frob M := Real.sqrt_nonneg _

theorem norm_matCLM_le {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m n ℝ)
    (w : EuclideanSpace ℝ n) : ‖matCLM M w‖ ≤ frob M * ‖w‖ := by
  have hsq : ‖matCLM M w‖ ^ 2 ≤ (∑ i, ∑ j, M i j ^ 2) * ‖w‖ ^ 2 := by
    rw [euclid_norm_sq, euclid_norm_sq w, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [matCLM_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h1 : ‖matCLM M w‖ ≤ Real.sqrt ((∑ i, ∑ j, M i j ^ 2) * ‖w‖ ^ 2) := by
    rw [show ‖matCLM M w‖ = Real.sqrt (‖matCLM M w‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq
  refine h1.trans_eq ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem frob_psdSqrt {S : Matrix n n ℝ} (hS : S.PosSemidef) :
    frob (psdSqrt S) = Real.sqrt S.trace := by
  rw [frob, ← trace_mul_transpose, psdSqrt_mul_transpose hS]

/-! ### Change of variables -/

theorem integral_multivariateGaussian_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Matrix n n ℝ) (f : EuclideanSpace ℝ n → F) (hf : Continuous f) :
    ∫ z, f z ∂(multivariateGaussian 0 S)
      = ∫ w, f (matCLM (psdSqrt S) w) ∂(stdGaussian n) := by
  rw [multivariateGaussian_zero_eq, integral_map (by fun_prop) hf.aestronglyMeasurable]

theorem integral_multivariateGaussian_add {S T : Matrix n n ℝ} (hS : S.PosSemidef)
    (hT : T.PosSemidef) (f : EuclideanSpace ℝ n → ℝ) (hf : Continuous f) :
    ∫ z, f z ∂(multivariateGaussian 0 (S + T))
      = ∫ p, f (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
          ∂(((stdGaussian n).prod (stdGaussian n))) := by
  have hmap := map_add_prod_stdGaussian (psdSqrt S) (psdSqrt T)
  rw [psdSqrt_mul_transpose hS, psdSqrt_mul_transpose hT] at hmap
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]

/-! ### Coordinates -/

/-- The `i`-th coordinate vector of `EuclideanSpace ℝ n`. -/
noncomputable def euclidBasis (i : n) : EuclideanSpace ℝ n := EuclideanSpace.single i (1 : ℝ)

theorem inner_euclidBasis (i : n) (x : EuclideanSpace ℝ n) : ⟪euclidBasis i, x⟫ = x i := by
  simp [euclidBasis, PiLp.inner_apply, EuclideanSpace.single_apply, Finset.sum_ite_eq']

theorem inner_euclidBasis_matCLM (A : Matrix n n ℝ) (i j : n) :
    ⟪euclidBasis i, matCLM A (euclidBasis j)⟫ = A i j := by
  rw [inner_euclidBasis, matCLM_apply]
  simp [euclidBasis, EuclideanSpace.single_apply, Finset.sum_ite_eq']

theorem sum_smul_euclidBasis (x : EuclideanSpace ℝ n) : ∑ i, (x i) • euclidBasis i = x := by
  ext j
  simp [euclidBasis, Pi.single_apply, Finset.sum_ite_eq]

theorem clm_expand (L : EuclideanSpace ℝ n →L[ℝ] ℝ) (v : EuclideanSpace ℝ n) :
    L v = ∑ j, v j * L (euclidBasis j) := by
  conv_lhs => rw [← sum_smul_euclidBasis v]
  rw [map_sum]
  simp

/-- Expansion of a continuous bilinear form in coordinates. -/
theorem bilin_expand (B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ)
    (u v : EuclideanSpace ℝ n) :
    B u v = ∑ i, ∑ j, u i * v j * (B (euclidBasis i)) (euclidBasis j) := by
  have h1 : B u v = ∑ i, u i * (B (euclidBasis i)) v :=
    clm_expand ((ContinuousLinearMap.apply ℝ ℝ v).comp B) u
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [clm_expand (B (euclidBasis i)) v, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### First and second moments of a linear image -/

theorem coord_matCLM_eq_inner (N : Matrix n n ℝ) (l : n) (w : EuclideanSpace ℝ n) :
    (matCLM N w) l = ⟪matCLM Nᵀ (euclidBasis l), w⟫ := by
  rw [← inner_matCLM', inner_euclidBasis]

theorem integral_coord_mul_coord (N : Matrix n n ℝ) (i j : n) :
    ∫ w, (matCLM N w) i * (matCLM N w) j ∂(stdGaussian n) = (N * Nᵀ) i j := by
  simp_rw [coord_matCLM_eq_inner N]
  rw [integral_inner_mul_inner_stdGaussian, inner_matCLM, Matrix.transpose_transpose,
    ← matCLM_mul, inner_euclidBasis_matCLM]

theorem memLp_coord_matCLM (N : Matrix n n ℝ) (i : n) :
    MemLp (fun w : EuclideanSpace ℝ n => (matCLM N w) i) 2 (stdGaussian n) := by
  have hmem : MemLp id 2 (stdGaussian n) := IsGaussian.memLp_two_id
  have h2 := ((innerSL ℝ (matCLM Nᵀ (euclidBasis i)))).comp_memLp' hmem
  have he : (fun w : EuclideanSpace ℝ n => (matCLM N w) i)
      = (⇑(innerSL ℝ (matCLM Nᵀ (euclidBasis i))) ∘ id) := by
    funext w
    simp only [Function.comp_apply, id_eq, coe_innerSL_apply]
    exact coord_matCLM_eq_inner N i w
  rw [he]
  exact h2

theorem integrable_coord_mul_coord (N : Matrix n n ℝ) (i j : n) :
    Integrable (fun w => (matCLM N w) i * (matCLM N w) j) (stdGaussian n) :=
  (memLp_coord_matCLM N i).integrable_mul (memLp_coord_matCLM N j)

/-- The second moment of a bilinear form evaluated at a linear image of the standard Gaussian. -/
theorem integral_bilin_matCLM (B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ)
    (N : Matrix n n ℝ) :
    ∫ w, (B (matCLM N w)) (matCLM N w) ∂(stdGaussian n)
      = ∑ i, ∑ j, (N * Nᵀ) i j * (B (euclidBasis i)) (euclidBasis j) := by
  have hexp : ∀ w : EuclideanSpace ℝ n, (B (matCLM N w)) (matCLM N w)
      = ∑ i, ∑ j, ((matCLM N w) i * (matCLM N w) j) * (B (euclidBasis i)) (euclidBasis j) :=
    fun w => bilin_expand B _ _
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    ((integrable_coord_mul_coord N i j).mul_const _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => (integrable_coord_mul_coord N i j).mul_const _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_coord_mul_coord]

/-- A linear functional of a centered Gaussian has zero mean. -/
theorem integral_clm_matCLM (L : EuclideanSpace ℝ n →L[ℝ] ℝ) (N : Matrix n n ℝ) :
    ∫ w, L (matCLM N w) ∂(stdGaussian n) = 0 := by
  show ∫ w, (L.comp (matCLM N)) (id w) ∂(stdGaussian n) = 0
  rw [(L.comp (matCLM N)).integral_comp_comm IsGaussian.integrable_id]
  rw [show (∫ x : EuclideanSpace ℝ n, id x ∂stdGaussian n) = 0 from integral_stdGaussian_id n]
  simp

/-! ### Integrability and tails -/

omit [DecidableEq n] in
theorem integrable_norm_sq_stdGaussian :
    Integrable (fun w : EuclideanSpace ℝ n => ‖w‖ ^ 2) (stdGaussian n) :=
  MemLp.integrable_norm_pow' (IsGaussian.memLp_two_id (μ := stdGaussian n))

omit [DecidableEq n] in
theorem integrable_norm_stdGaussian :
    Integrable (fun w : EuclideanSpace ℝ n => ‖w‖) (stdGaussian n) :=
  (IsGaussian.integrable_id (μ := stdGaussian n)).norm

omit [DecidableEq n] in
theorem measurableSet_norm_gt (A : ℝ) :
    MeasurableSet {w : EuclideanSpace ℝ n | A < ‖w‖} :=
  measurableSet_lt measurable_const continuous_norm.measurable

omit [DecidableEq n] in
/-- Gaussian tails are small: for any nonnegative integrable `f`, the integral of `f` over the
region `‖w‖ > A` can be made arbitrarily small. -/
theorem exists_tail_bound (f : EuclideanSpace ℝ n → ℝ) (hf : Integrable f (stdGaussian n))
    (hf0 : ∀ w, 0 ≤ f w) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∫ w, Set.indicator {w : EuclideanSpace ℝ n | A < ‖w‖} f w ∂(stdGaussian n) ≤ ε := by
  set F : ℕ → EuclideanSpace ℝ n → ℝ :=
    fun k => Set.indicator {w : EuclideanSpace ℝ n | (k : ℝ) < ‖w‖} f with hF
  have hintF : ∀ k, Integrable (F k) (stdGaussian n) := fun k =>
    hf.indicator (measurableSet_norm_gt _)
  have hbound : ∀ k, ∀ᵐ w ∂(stdGaussian n), ‖F k w‖ ≤ f w := by
    intro k
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun z _ => hf0 z) w)]
    exact Set.indicator_le_self' (fun z _ => hf0 z) w
  have hlim : ∀ᵐ w ∂(stdGaussian n), Tendsto (fun k => F k w) atTop (nhds 0) := by
    filter_upwards with w
    have hev : ∀ᶠ k : ℕ in atTop, F k w = 0 := by
      filter_upwards [eventually_gt_atTop ⌈‖w‖⌉₊] with k hk
      have hnot : w ∉ {z : EuclideanSpace ℝ n | (k : ℝ) < ‖z‖} := by
        simp only [Set.mem_setOf_eq, not_lt]
        exact (Nat.le_ceil ‖w‖).trans (by exact_mod_cast hk.le)
      simp [hF, Set.indicator_of_notMem hnot]
    exact Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
  have hconv := tendsto_integral_of_dominated_convergence f (fun k => (hintF k).1) hf hbound hlim
  rw [integral_zero, Metric.tendsto_atTop] at hconv
  obtain ⟨K, hK⟩ := hconv ε hε
  refine ⟨max (K : ℝ) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  have hle : ∫ w, Set.indicator {w : EuclideanSpace ℝ n | max (K : ℝ) 1 < ‖w‖} f w
        ∂(stdGaussian n) ≤ ∫ w, F K w ∂(stdGaussian n) := by
    refine integral_mono (hf.indicator (measurableSet_norm_gt _)) (hintF K) fun w => ?_
    by_cases hw : max (K : ℝ) 1 < ‖w‖
    · have hw' : (K : ℝ) < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
      simp only [hF, Set.indicator_of_mem, Set.mem_setOf_eq, hw, hw', le_refl]
    · rw [Set.indicator_of_notMem (by simpa using hw)]
      exact Set.indicator_nonneg (fun z _ => hf0 z) w
  refine hle.trans ?_
  have hd := hK K le_rfl
  rw [Real.dist_eq, sub_zero] at hd
  exact (le_abs_self _).trans hd.le

end ProbabilityTheory
