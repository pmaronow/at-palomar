module

public import Paper.GaussianHeat
public import Paper.TanhPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-!
# Smoothness of the concrete Gaussian moments

Polynomial observables of tanh are closed under differentiation. Gaussian
weighted affine expectations of these observables are therefore smooth by
induction, with every derivative exchange justified by finite Gaussian moments.
The positive-variance moments are obtained by composing with the square root.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace Paper

/-- Gaussian polynomial moments used as dominating functions. -/
theorem integrable_standardGaussian_pow (m : ℕ) :
    Integrable (fun z : ℝ => z ^ m) (gaussianReal 0 1) := by
  apply integrable_pow_of_mem_interior_integrableExpSet
  simp [integrableExpSet_fun_id_gaussianReal]

theorem integrable_standardGaussian_norm_pow (m : ℕ) :
    Integrable (fun z : ℝ => ‖z‖ ^ m) (gaussianReal 0 1) := by
  simpa only [norm_pow] using (integrable_standardGaussian_pow m).norm

/-- Weighted affine Gaussian expectations of polynomial observables of tanh. -/
def gaussianPolynomialMoment (P : Polynomial ℝ) (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  gaussianExpectation (fun z => z ^ m * P.eval (Real.tanh (p.1 + p.2 * z)))

theorem integrable_gaussianPolynomialMoment (P : Polynomial ℝ) (m : ℕ) (p : ℝ × ℝ) :
    Integrable (fun z => z ^ m * P.eval (Real.tanh (p.1 + p.2 * z))) (gaussianReal 0 1) := by
  obtain ⟨M, hM, hb⟩ := tanhPolynomial_bounded P
  have hc : Continuous (fun z : ℝ => p.1 + p.2 * z) := by fun_prop
  exact (integrable_standardGaussian_pow m).mul_bdd
    ((continuous_tanhPolynomial P).comp hc).aestronglyMeasurable
    (Eventually.of_forall fun z => hb _)

theorem continuous_gaussianPolynomialMoment (P : Polynomial ℝ) (m : ℕ) :
    Continuous (gaussianPolynomialMoment P m) := by
  obtain ⟨M, hM, hb⟩ := tanhPolynomial_bounded P
  apply continuous_of_dominated (bound := fun z : ℝ => ‖z‖ ^ m * M)
  · intro p
    have hc : Continuous (fun z : ℝ => p.1 + p.2 * z) := by fun_prop
    exact ((continuous_id.pow m).mul
      ((continuous_tanhPolynomial P).comp hc)).aestronglyMeasurable
  · intro p
    filter_upwards with z
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (norm_nonneg z) m)
  · exact (integrable_standardGaussian_norm_pow m).mul_const M
  · filter_upwards with z
    have hc : Continuous (fun p : ℝ × ℝ => p.1 + p.2 * z) := by fun_prop
    exact continuous_const.mul ((continuous_tanhPolynomial P).comp hc)

theorem hasDerivAt_gaussianPolynomialMoment_mean
    (P : Polynomial ℝ) (m : ℕ) (h a : ℝ) :
    HasDerivAt (fun b => gaussianPolynomialMoment P m (b, a))
      (gaussianPolynomialMoment (tanhPolynomialDeriv P) m (h, a)) h := by
  let Q := tanhPolynomialDeriv P
  obtain ⟨M, hM, hb⟩ := tanhPolynomial_bounded Q
  have hc (b : ℝ) : Continuous (fun z : ℝ => b + a * z) := by fun_prop
  have hm : ∀ᶠ b in 𝓝 h, AEStronglyMeasurable
      (fun z => z ^ m * P.eval (Real.tanh (b + a * z))) (gaussianReal 0 1) :=
    .of_forall fun b => ((continuous_id.pow m).mul
      ((continuous_tanhPolynomial P).comp (hc b))).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z => z ^ m * Q.eval (Real.tanh (h + a * z))) (gaussianReal 0 1) :=
    ((continuous_id.pow m).mul ((continuous_tanhPolynomial Q).comp (hc h))).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      ‖z ^ m * Q.eval (Real.tanh (b + a * z))‖ ≤ ‖z‖ ^ m * M := by
    filter_upwards with z b _
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (norm_nonneg z) m)
  have hd : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun b => z ^ m * P.eval (Real.tanh (b + a * z)))
        (z ^ m * Q.eval (Real.tanh (b + a * z))) b := by
    filter_upwards with z b _
    exact ((hasDerivAt_tanhPolynomial P (b + a * z)).comp_add_const b (a * z)).const_mul (z ^ m)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := fun z : ℝ => ‖z‖ ^ m * M) (by simp) hm
    (integrable_gaussianPolynomialMoment P m (h, a)) hm' hb'
    ((integrable_standardGaussian_norm_pow m).mul_const M) hd).2

theorem hasDerivAt_gaussianPolynomialMoment_scale
    (P : Polynomial ℝ) (m : ℕ) (h a : ℝ) :
    HasDerivAt (fun b => gaussianPolynomialMoment P m (h, b))
      (gaussianPolynomialMoment (tanhPolynomialDeriv P) (m + 1) (h, a)) a := by
  let Q := tanhPolynomialDeriv P
  obtain ⟨M, hM, hb⟩ := tanhPolynomial_bounded Q
  have hc (b : ℝ) : Continuous (fun z : ℝ => h + b * z) := by fun_prop
  have hm : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable
      (fun z => z ^ m * P.eval (Real.tanh (h + b * z))) (gaussianReal 0 1) :=
    .of_forall fun b => ((continuous_id.pow m).mul
      ((continuous_tanhPolynomial P).comp (hc b))).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z => z ^ (m + 1) * Q.eval (Real.tanh (h + a * z))) (gaussianReal 0 1) :=
    ((continuous_id.pow (m + 1)).mul ((continuous_tanhPolynomial Q).comp (hc a))).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      ‖z ^ (m + 1) * Q.eval (Real.tanh (h + b * z))‖ ≤ ‖z‖ ^ (m + 1) * M := by
    filter_upwards with z b _
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (norm_nonneg z) _)
  have hd : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun b => z ^ m * P.eval (Real.tanh (h + b * z)))
        (z ^ (m + 1) * Q.eval (Real.tanh (h + b * z))) b := by
    filter_upwards with z b _
    have hinner : HasDerivAt (fun y : ℝ => h + y * z) z b := by
      simpa using ((hasDerivAt_id b).mul_const z).const_add h
    convert ((hasDerivAt_tanhPolynomial P (h + b * z)).comp b hinner).const_mul (z ^ m) using 1
    · rfl
    · rw [pow_succ]
      ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := fun z : ℝ => ‖z‖ ^ (m + 1) * M) (by simp) hm
    (integrable_gaussianPolynomialMoment P m (h, a)) hm' hb'
    ((integrable_standardGaussian_norm_pow (m + 1)).mul_const M) hd).2

/-- Explicit joint derivative in the mean and affine scale coordinates. -/
def gaussianPolynomialDerivative (P : Polynomial ℝ) (m : ℕ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  gaussianPolynomialMoment (tanhPolynomialDeriv P) m p • fst ℝ ℝ ℝ +
    gaussianPolynomialMoment (tanhPolynomialDeriv P) (m + 1) p • snd ℝ ℝ ℝ

theorem hasFDerivAt_gaussianPolynomialMoment (P : Polynomial ℝ) (m : ℕ) (p : ℝ × ℝ) :
    HasFDerivAt (gaussianPolynomialMoment P m) (gaussianPolynomialDerivative P m p) p := by
  let Q := tanhPolynomialDeriv P
  have hc1 : Continuous (fun p : ℝ × ℝ => toSpanSingleton ℝ
      (gaussianPolynomialMoment Q m p)) :=
    toSpanSingletonCLE.continuous.comp (continuous_gaussianPolynomialMoment Q m)
  have hc2 : Continuous (fun p : ℝ × ℝ => toSpanSingleton ℝ
      (gaussianPolynomialMoment Q (m + 1) p)) :=
    toSpanSingletonCLE.continuous.comp (continuous_gaussianPolynomialMoment Q (m + 1))
  have hd := hasStrictFDerivAt_uncurry_coprod
    (f := fun h a => gaussianPolynomialMoment P m (h, a))
    (f₁ := fun h a => toSpanSingleton ℝ (gaussianPolynomialMoment Q m (h, a)))
    (f₂ := fun h a => toSpanSingleton ℝ (gaussianPolynomialMoment Q (m + 1) (h, a)))
    (u := p)
    (Eventually.of_forall fun v => (hasDerivAt_gaussianPolynomialMoment_mean P m v.1 v.2).hasFDerivAt)
    (Eventually.of_forall fun v => (hasDerivAt_gaussianPolynomialMoment_scale P m v.1 v.2).hasFDerivAt)
    hc1.continuousAt hc2.continuousAt
  convert! hd.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro q
  change gaussianPolynomialMoment Q m p * q.1 +
    gaussianPolynomialMoment Q (m + 1) p * q.2 =
    q.1 * gaussianPolynomialMoment Q m p + q.2 * gaussianPolynomialMoment Q (m + 1) p
  ring

/-- Arbitrary finite regularity, proved simultaneously for every polynomial
and every Gaussian moment weight. -/
theorem gaussianPolynomialMoment_contDiff_nat (n : ℕ) :
    ∀ (P : Polynomial ℝ) (m : ℕ), ContDiff ℝ n (gaussianPolynomialMoment P m) := by
  induction n with
  | zero =>
      intro P m
      exact contDiff_zero.mpr (continuous_gaussianPolynomialMoment P m)
  | succ n ih =>
      intro P m
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨gaussianPolynomialDerivative P m, ?_, hasFDerivAt_gaussianPolynomialMoment P m⟩
      exact ((ih (tanhPolynomialDeriv P) m).smul contDiff_const).add
        ((ih (tanhPolynomialDeriv P) (m + 1)).smul contDiff_const)

/-- The affine Gaussian polynomial moments are genuinely `C∞`. -/
theorem gaussianPolynomialMoment_contDiff (P : Polynomial ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (gaussianPolynomialMoment P m) :=
  contDiff_infty.mpr (fun n => gaussianPolynomialMoment_contDiff_nat n P m)

/-- Even sech moments in affine mean/scale coordinates are polynomial tanh
moments and hence smooth at every parameter value. -/
theorem gaussian_sech_even_affine_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => gaussianExpectation
      (fun z => sech (p.1 + p.2 * z) ^ (2 * n))) := by
  convert gaussianPolynomialMoment_contDiff ((1 - Polynomial.X ^ 2) ^ n) 0 using 1
  ext p
  unfold gaussianPolynomialMoment
  congr 1
  ext z
  simp only [pow_zero, one_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X]
  rw [show 1 - Real.tanh (p.1 + p.2 * z) ^ 2 = sech (p.1 + p.2 * z) ^ 2 by
    linarith [tanh_sq_add_sech_sq (p.1 + p.2 * z)]]
  rw [pow_mul]

/-- The positive-variance parameter domain in mean/variance coordinates. -/
def positiveVariance : Set (ℝ × ℝ) := {p | 0 < p.2}

theorem gaussian_sech_even_contDiffAt (n : ℕ) (h t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gaussianExpectation
      (fun z => sech (p.1 + Real.sqrt p.2 * z) ^ (2 * n))) (h, t) := by
  have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.1) (h, t) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.2) (h, t) := contDiffAt_snd
  have hsingle : ContDiffAt ℝ ∞ Real.sqrt t := Real.contDiffAt_sqrt (ne_of_gt ht)
  have hsqrt0 := hsingle.comp (h, t) hsnd
  have hsqrt : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Real.sqrt p.2) (h, t) := by
    simpa only [Function.comp_def] using hsqrt0
  have hmap : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1, Real.sqrt p.2)) (h, t) :=
    hfst.prodMk hsqrt
  have hout := (gaussian_sech_even_affine_contDiff n).comp_contDiffAt (h, t) hmap
  simpa only [Function.comp_def] using hout

theorem gaussianA_contDiffAt (h t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gaussianA p.1 p.2) (h, t) := by
  change ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gaussianExpectation
    (fun z => sech (p.1 + Real.sqrt p.2 * z) ^ 2)) (h, t)
  simpa only [mul_one] using gaussian_sech_even_contDiffAt 1 h t ht

theorem gaussianC_contDiffAt (h t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gaussianC p.1 p.2) (h, t) := by
  change ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => gaussianExpectation
    (fun z => sech (p.1 + Real.sqrt p.2 * z) ^ 4)) (h, t)
  simpa only [show (2 : ℕ) * 2 = 4 by norm_num] using gaussian_sech_even_contDiffAt 2 h t ht

theorem atZeroFunction_contDiffAt (h t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => atZeroFunction p.1 p.2) (h, t) :=
  ((contDiffAt_snd.mul (gaussianC_contDiffAt h t ht)).add
    (gaussianA_contDiffAt h t ht)).sub contDiffAt_const

theorem gaussianA_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gaussianA p.1 p.2) positiveVariance :=
  fun p hp => (gaussianA_contDiffAt p.1 p.2 hp).contDiffWithinAt

theorem gaussianC_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => gaussianC p.1 p.2) positiveVariance :=
  fun p hp => (gaussianC_contDiffAt p.1 p.2 hp).contDiffWithinAt

theorem atZeroFunction_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => atZeroFunction p.1 p.2) positiveVariance :=
  fun p hp => (atZeroFunction_contDiffAt p.1 p.2 hp).contDiffWithinAt

end Paper
