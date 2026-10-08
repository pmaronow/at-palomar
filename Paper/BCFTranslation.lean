module

public import Paper.GaussianSmooth
public import Paper.QuadraticImplicit
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib

@[expose] public section

/-! # Smooth spatial translation curves in bounded continuous functions

Uniform Taylor remainders prove BCF-valued translation differentiability.
An actual bounded derivative hierarchy then yields C∞ translation curves;
the Gaussian smoothing of polynomial observables of tanh supplies such a
hierarchy at every time, including zero smoothing variance.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff

namespace Paper

private theorem contDiff_spanSingleton {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (n : ℕ∞ω) :
    ContDiff ℝ n (fun x : X => ContinuousLinearMap.toSpanSingleton ℝ x) :=
  (ContinuousLinearMap.toSpanSingletonCLE : X ≃L[ℝ] (ℝ →L[ℝ] X)).contDiff

noncomputable def bcfTranslate {P : Type*} [TopologicalSpace P]
    (ξ : ℝ) (f : (P × ℝ) →ᵇ ℝ) : (P × ℝ) →ᵇ ℝ :=
  f.compContinuous ⟨fun p => (p.1, p.2 + ξ), by fun_prop⟩

@[simp] theorem bcfTranslate_apply {P : Type*} [TopologicalSpace P]
    (ξ : ℝ) (f : (P × ℝ) →ᵇ ℝ) (p : P × ℝ) :
    bcfTranslate ξ f p = f (p.1, p.2 + ξ) := rfl

@[simp] theorem bcfTranslate_zero {P : Type*} [TopologicalSpace P]
    (f : (P × ℝ) →ᵇ ℝ) : bcfTranslate 0 f = f := by ext p; simp

theorem bcfTranslate_add {P : Type*} [TopologicalSpace P]
    (ξ η : ℝ) (f : (P × ℝ) →ᵇ ℝ) :
    bcfTranslate ξ (bcfTranslate η f) = bcfTranslate (ξ + η) f := by
  ext p
  simp only [bcfTranslate_apply, add_assoc]

theorem norm_bcfTranslate {P : Type*} [TopologicalSpace P]
    (ξ : ℝ) (f : (P × ℝ) →ᵇ ℝ) : ‖bcfTranslate ξ f‖ = ‖f‖ := by
  apply le_antisymm (BoundedContinuousFunction.norm_compContinuous_le _ _)
  have h := BoundedContinuousFunction.norm_compContinuous_le (bcfTranslate ξ f)
    (⟨fun p : P × ℝ => (p.1, p.2 - ξ), by fun_prop⟩ : C(P × ℝ, P × ℝ))
  have heq : (bcfTranslate ξ f).compContinuous
      (⟨fun p : P × ℝ => (p.1, p.2 - ξ), by fun_prop⟩ : C(P × ℝ, P × ℝ)) = f := by
    ext p
    simp [bcfTranslate, BoundedContinuousFunction.compContinuous_apply]
  rwa [heq] at h

theorem lipschitzWith_bcfTranslate {P : Type*} [TopologicalSpace P]
    (f : (P × ℝ) →ᵇ ℝ) {K : ℝ≥0}
    (hL : ∀ p, LipschitzWith K (fun x => f (p, x))) :
    LipschitzWith K (fun ξ => bcfTranslate ξ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro ξ η
  rw [dist_eq_norm, Real.dist_eq]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro p
  have h := (hL p.1).dist_le_mul (p.2 + ξ) (p.2 + η)
  simpa only [Real.dist_eq, BoundedContinuousFunction.sub_apply, bcfTranslate_apply,
    Real.norm_eq_abs, add_sub_add_left_eq_sub] using h

theorem abs_sub_linear_le_of_lipschitz_derivative {f d : ℝ → ℝ} {K : ℝ≥0}
    (hd : ∀ y, HasDerivAt f (d y) y) (hL : LipschitzWith K d) (x h : ℝ) :
    |f (x + h) - f x - h * d x| ≤ (K : ℝ) * |h| ^ 2 := by
  let R : ℝ → ℝ := fun y => f y - (y - x) * d x
  have hR (y : ℝ) : HasDerivAt R (d y - d x) y := by
    convert! (hd y).sub (((hasDerivAt_id y).sub_const x).mul_const (d x)) using 1
    simp only [one_mul]
  have hb (y : ℝ) (hy : y ∈ Metric.closedBall x |h|) :
      ‖d y - d x‖ ≤ (K : ℝ) * |h| := by
    have hdist := hL.dist_le_mul y x
    rw [dist_eq_norm] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) K.property)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hR y).hasDerivWithinAt) hb (convex_closedBall x |h|)
    (Metric.mem_closedBall.mpr (by simp : dist x x ≤ |h|))
    (Metric.mem_closedBall.mpr (by simp : dist (x + h) x ≤ |h|))
  convert H using 1
  · rw [Real.norm_eq_abs]
    congr 1
    dsimp only [R]
    ring
  · simp only [Real.norm_eq_abs, add_sub_cancel_left]
    ring

theorem norm_bcfTranslate_remainder_le {P : Type*} [TopologicalSpace P]
    (f d : (P × ℝ) →ᵇ ℝ) {K : ℝ≥0}
    (hd : ∀ p x, HasDerivAt (fun y => f (p, y)) (d (p, x)) x)
    (hL : ∀ p, LipschitzWith K (fun x => d (p, x))) (a b : ℝ) :
    ‖bcfTranslate b f - bcfTranslate a f - (b - a) • bcfTranslate a d‖ ≤
      (K : ℝ) * |b - a| ^ 2 := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro p
  have h := abs_sub_linear_le_of_lipschitz_derivative (hd p.1) (hL p.1)
    (p.2 + a) (b - a)
  simpa only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    bcfTranslate_apply, smul_eq_mul, Real.norm_eq_abs,
    show p.2 + a + (b - a) = p.2 + b by ring] using h

theorem hasDerivAt_bcfTranslate {P : Type*} [TopologicalSpace P]
    (f d : (P × ℝ) →ᵇ ℝ) {K : ℝ≥0}
    (hd : ∀ p x, HasDerivAt (fun y => f (p, y)) (d (p, x)) x)
    (hL : ∀ p, LipschitzWith K (fun x => d (p, x))) (a : ℝ) :
    HasDerivAt (fun ξ => bcfTranslate ξ f) (bcfTranslate a d) a := by
  apply hasDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun b => by positivity)
    (g := fun b => (K : ℝ) * |b - a|)
  · intro b
    rw [Real.norm_eq_abs]
    calc
      |b - a|⁻¹ * ‖bcfTranslate b f - bcfTranslate a f - (b - a) • bcfTranslate a d‖ ≤
          |b - a|⁻¹ * ((K : ℝ) * |b - a| ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_bcfTranslate_remainder_le f d hd hL a b) (by positivity)
      _ = (K : ℝ) * |b - a| := by
        by_cases h : b - a = 0
        · simp [h]
        · field_simp [abs_ne_zero.mpr h]
  · have hc : Continuous (fun b : ℝ => (K : ℝ) * |b - a|) := by fun_prop
    simpa only [sub_self, abs_zero, mul_zero] using hc.tendsto a

theorem contDiff_bcfTranslate_of_hierarchy {P : Type*} [TopologicalSpace P]
    (D : ℕ → (P × ℝ) →ᵇ ℝ)
    (hD : ∀ n p x, HasDerivAt (fun y => D n (p, y)) (D (n + 1) (p, x)) x) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (D 0)) := by
  have hL (n : ℕ) (p : P) : LipschitzWith ‖D (n + 2)‖₊ (fun x => D (n + 1) (p, x)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hD (n + 1) p x).differentiableAt)
    intro x
    change ‖deriv (fun y => D (n + 1) (p, y)) x‖ ≤ ‖D (n + 2)‖
    rw [(hD (n + 1) p x).deriv]
    exact (D (n + 2)).norm_coe_le_norm (p, x)
  have hd (n : ℕ) (ξ : ℝ) :
      HasDerivAt (fun ξ => bcfTranslate ξ (D n)) (bcfTranslate ξ (D (n + 1))) ξ :=
    hasDerivAt_bcfTranslate (D n) (D (n + 1)) (hD n) (hL n) ξ
  have hfin (r : ℕ) : ∀ n, ContDiff ℝ r (fun ξ => bcfTranslate ξ (D n)) := by
    induction r with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun ξ => (hd n ξ).continuousAt)
    | succ r ih =>
      intro n
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun ξ => ContinuousLinearMap.toSpanSingleton ℝ (bcfTranslate ξ (D (n + 1))), ?_,
        fun ξ => (hd n ξ).hasFDerivAt⟩
      convert! (contDiff_spanSingleton (X := (P × ℝ) →ᵇ ℝ) r).comp (ih (n + 1))
  exact contDiff_infty.mpr fun r => hfin r 0

theorem norm_gaussianPolynomialMoment_zero_le (P : Polynomial ℝ) {M : ℝ}
    (hM : ∀ y, ‖P.eval (Real.tanh y)‖ ≤ M) (x a : ℝ) :
    ‖gaussianPolynomialMoment P 0 (x, a)‖ ≤ M := by
  unfold gaussianPolynomialMoment gaussianExpectation
  simpa using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (Eventually.of_forall fun z : ℝ => hM (x + a * z))

noncomputable def tanhGaussianBCF {P : Type*} [TopologicalSpace P]
    (Q : Polynomial ℝ) (a : P → ℝ) (ha : Continuous a) : (P × ℝ) →ᵇ ℝ := by
  let M := Classical.choose (tanhPolynomial_bounded Q)
  have hb := (Classical.choose_spec (tanhPolynomial_bounded Q)).2
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : P × ℝ => gaussianPolynomialMoment Q 0 (p.2, a p.1))
    ((continuous_gaussianPolynomialMoment Q 0).comp
      (continuous_snd.prodMk (ha.comp continuous_fst))) M
    (fun p => norm_gaussianPolynomialMoment_zero_le Q hb p.2 (a p.1))

@[simp] theorem tanhGaussianBCF_apply {P : Type*} [TopologicalSpace P]
    (Q : Polynomial ℝ) (a : P → ℝ) (ha : Continuous a) (p : P × ℝ) :
    tanhGaussianBCF Q a ha p = gaussianPolynomialMoment Q 0 (p.2, a p.1) := rfl

noncomputable def tanhDerivativePolynomial (Q : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => Q
  | n + 1 => tanhPolynomialDeriv (tanhDerivativePolynomial Q n)

/-- Gaussian smoothing of every polynomial observable of tanh has a
genuine C∞ spatial translation curve into the joint BCF space. The Gaussian
scale may depend continuously on any additional parameters and may vanish. -/
theorem contDiff_bcfTranslate_tanhGaussian {P : Type*} [TopologicalSpace P]
    (Q : Polynomial ℝ) (a : P → ℝ) (ha : Continuous a) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (tanhGaussianBCF Q a ha)) := by
  apply contDiff_bcfTranslate_of_hierarchy
    (D := fun n => tanhGaussianBCF (tanhDerivativePolynomial Q n) a ha)
  intro n p x
  simpa only [tanhGaussianBCF_apply, tanhDerivativePolynomial] using
    hasDerivAt_gaussianPolynomialMoment_mean (tanhDerivativePolynomial Q n) 0 x (a p)

@[simp] theorem bcfTranslate_add_values {P : Type*} [TopologicalSpace P]
    (ξ : ℝ) (f g : (P × ℝ) →ᵇ ℝ) :
    bcfTranslate ξ (f + g) = bcfTranslate ξ f + bcfTranslate ξ g := by ext p; rfl

/-- Smoothness of a quadratic BCF fixed point follows from smooth terminal
translations and actual translation covariance of the bilinear correction. -/
theorem contDiff_bcfTranslate_quadratic_fixedPoint {P : Type*} [TopologicalSpace P]
    (B : ((P × ℝ) →ᵇ ℝ) →L[ℝ] ((P × ℝ) →ᵇ ℝ) →L[ℝ] ((P × ℝ) →ᵇ ℝ))
    (g v : (P × ℝ) →ᵇ ℝ) {K : ℝ≥0}
    (hg : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ g))
    (hv : ∀ p, LipschitzWith K (fun x => v (p, x)))
    (hfix : v = g + B v v)
    (hcov : ∀ ξ, bcfTranslate ξ (B v v) = B (bcfTranslate ξ v) (bcfTranslate ξ v))
    (hsmall : 2 * bilinearOperatorNorm B * ‖v‖ < 1) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  apply contDiffAt_quadratic_fixedPoint_of_norm (fun _ : ℝ => B)
    (fun η => bcfTranslate η g) (fun η => bcfTranslate η v) ξ
    contDiffAt_const (hg.contDiffAt) ((lipschitzWith_bcfTranslate v hv).continuous.continuousAt)
  · intro η
    have heq := congrArg (bcfTranslate η) hfix
    rwa [bcfTranslate_add_values, hcov η] at heq
  · change 2 * bilinearOperatorNorm B * ‖bcfTranslate ξ v‖ < 1
    simpa only [norm_bcfTranslate] using hsmall

theorem contDiff_bcfTranslate_quadratic_fixedPoint_of_invertible
    {P : Type*} [TopologicalSpace P]
    (B : ((P × ℝ) →ᵇ ℝ) →L[ℝ] ((P × ℝ) →ᵇ ℝ) →L[ℝ] ((P × ℝ) →ᵇ ℝ))
    (g v : (P × ℝ) →ᵇ ℝ) {K : ℝ≥0}
    (hg : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ g))
    (hv : ∀ p, LipschitzWith K (fun x => v (p, x)))
    (hfix : v = g + B v v)
    (hcov : ∀ ξ, bcfTranslate ξ (B v v) = B (bcfTranslate ξ v) (bcfTranslate ξ v))
    (hinv : ∀ ξ, quadraticLinearizationIsInvertible B (bcfTranslate ξ v)) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  apply contDiffAt_quadratic_fixedPoint_of_invertible (fun _ : ℝ => B)
    (fun η => bcfTranslate η g) (fun η => bcfTranslate η v) ξ
    contDiffAt_const (hg.contDiffAt) ((lipschitzWith_bcfTranslate v hv).continuous.continuousAt)
  · intro η
    have heq := congrArg (bcfTranslate η) hfix
    rwa [bcfTranslate_add_values, hcov η] at heq
  · exact hinv ξ

private theorem iteratedDeriv_clm_comp {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {f : ℝ → X} (hf : ContDiff ℝ ∞ f) (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun ξ => L (f ξ)) a = L (iteratedDeriv n f a) := by
  change iteratedDeriv n (L ∘ f) a = _
  rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  rfl

noncomputable def bcfSpatialDerivative {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ) (n : ℕ) : (P × ℝ) →ᵇ ℝ :=
  iteratedDeriv n (fun ξ => bcfTranslate ξ v) 0

/-- Every spatial derivative is represented by an actual BCF value of a
derivative of the translation curve. This gives joint continuity and global
boundedness at every order once the curve has been proved smooth. -/
theorem bcfSpatialDerivative_apply {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ)
    (hv : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v)) (n : ℕ) (p : P × ℝ) :
    bcfSpatialDerivative v n p = iteratedDeriv n (fun y => v (p.1, y)) p.2 := by
  have he := iteratedDeriv_clm_comp (BoundedContinuousFunction.evalCLM ℝ p) hv n 0
  have hs := congrFun (iteratedDeriv_comp_const_add n (fun y => v (p.1, y)) p.2) 0
  calc
    bcfSpatialDerivative v n p = iteratedDeriv n (fun ξ => v (p.1, p.2 + ξ)) 0 := by
      simpa only [bcfSpatialDerivative, Function.comp_def, bcfTranslate_apply,
        BoundedContinuousFunction.evalCLM_apply] using he.symm
    _ = iteratedDeriv n (fun y => v (p.1, y)) p.2 := by simpa only [add_zero] using hs

theorem continuous_iteratedSpatialDeriv_of_translate_smooth {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ)
    (hv : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v)) (n : ℕ) :
    Continuous (fun p : P × ℝ => iteratedDeriv n (fun y => v (p.1, y)) p.2) := by
  have heq : (bcfSpatialDerivative v n : P × ℝ → ℝ) =
      fun p => iteratedDeriv n (fun y => v (p.1, y)) p.2 :=
    funext (bcfSpatialDerivative_apply v hv n)
  rw [← heq]
  exact (bcfSpatialDerivative v n).continuous

theorem bounded_iteratedSpatialDeriv_of_translate_smooth {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ)
    (hv : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v)) (n : ℕ) :
    ∃ M : ℝ, ∀ p : P × ℝ, ‖iteratedDeriv n (fun y => v (p.1, y)) p.2‖ ≤ M := by
  refine ⟨‖bcfSpatialDerivative v n‖, fun p => ?_⟩
  rw [← bcfSpatialDerivative_apply v hv n p]
  exact (bcfSpatialDerivative v n).norm_coe_le_norm p

end Paper
