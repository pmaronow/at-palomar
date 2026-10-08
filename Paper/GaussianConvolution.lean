module

public import Paper.GaussianPositivity
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Independent Gaussian sums and heat convolution

The independent pair uses the genuine product Gaussian probability measure.
The affine sum law is proved by Gaussian convolution, including zero
coefficients. Boundedness supplies the product integrability needed for Fubini.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

noncomputable def standardGaussianPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardGaussianPair := by
  unfold standardGaussianPair
  infer_instance

theorem gaussian_affine_pair_hasLaw (h a b : ℝ) :
    HasLaw (fun p : ℝ × ℝ => h + a * p.1 + b * p.2)
      (gaussianReal h (a ^ 2 + b ^ 2).toNNReal) standardGaussianPair := by
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) (gaussianReal 0 1) standardGaussianPair :=
    measurePreserving_fst.hasLaw
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) (gaussianReal 0 1) standardGaussianPair :=
    measurePreserving_snd.hasLaw
  have hXa := gaussianReal_const_mul hX a
  have hYb := gaussianReal_const_mul hY b
  have hi : IndepFun (fun p : ℝ × ℝ => a * p.1)
      (fun p : ℝ × ℝ => b * p.2) standardGaussianPair :=
    indepFun_prod (by fun_prop) (by fun_prop)
  have hsum : HasLaw (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      (gaussianReal 0 (a ^ 2 + b ^ 2).toNNReal) standardGaussianPair := by
    refine ⟨by fun_prop, ?_⟩
    have he := gaussianReal_add_gaussianReal_of_indepFun hi hXa hYb
    have hv : (NNReal.mk (a ^ 2) (sq_nonneg a)) * 1 +
        (NNReal.mk (b ^ 2) (sq_nonneg b)) * 1 = (a ^ 2 + b ^ 2).toNNReal := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_add, mul_one]
      rw [Real.coe_toNNReal _ (add_nonneg (sq_nonneg a) (sq_nonneg b))]
      rfl
    rw [hv] at he
    simpa only [Pi.add_def, mul_zero, zero_add] using he
  convert gaussianReal_const_add hsum h using 1
  · ext p
    ring
  · simp

theorem integrable_standardGaussianPair_bounded (f : ℝ × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ p, ‖f p‖ ≤ M) :
    Integrable f standardGaussianPair := by
  exact (integrable_const M).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- The convolution identity with its precise product integrability input. -/
theorem gaussianExpectation_double_affine_collapse_of_integrable
    (h a b : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun p : ℝ × ℝ => f (h + a * p.1 + b * p.2))
      standardGaussianPair) :
    gaussianExpectation (fun z => gaussianExpectation (fun w => f (h + a * z + b * w))) =
      gaussianExpectation (fun z => f (h + Real.sqrt (a ^ 2 + b ^ 2) * z)) := by
  have he : (∫ p : ℝ × ℝ, f (h + a * p.1 + b * p.2) ∂standardGaussianPair) =
      ∫ y, f y ∂gaussianReal h (a ^ 2 + b ^ 2).toNNReal := by
    rw [← (gaussian_affine_pair_hasLaw h a b).map_eq]
    exact (integral_map (gaussian_affine_pair_hasLaw h a b).aemeasurable
      hf.aestronglyMeasurable).symm
  rw [gaussianExpectation_shift_eq_integral h (a ^ 2 + b ^ 2)
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) f hf]
  unfold gaussianExpectation
  rw [← integral_prod _ hi]
  exact he

/-- Independent Gaussian sums collapse to their actual combined variance. -/
theorem gaussianExpectation_double_affine_collapse (h a b : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    gaussianExpectation (fun z => gaussianExpectation (fun w => f (h + a * z + b * w))) =
      gaussianExpectation (fun z => f (h + Real.sqrt (a ^ 2 + b ^ 2) * z)) := by
  have hi : Integrable (fun p : ℝ × ℝ => f (h + a * p.1 + b * p.2))
      standardGaussianPair :=
    integrable_standardGaussianPair_bounded _ (hf.comp (by fun_prop)) M (fun p => hb _)
  have he : (∫ p : ℝ × ℝ, f (h + a * p.1 + b * p.2) ∂standardGaussianPair) =
      ∫ y, f y ∂gaussianReal h (a ^ 2 + b ^ 2).toNNReal := by
    rw [← (gaussian_affine_pair_hasLaw h a b).map_eq]
    exact (integral_map (gaussian_affine_pair_hasLaw h a b).aemeasurable
      hf.aestronglyMeasurable).symm
  have hs := gaussianExpectation_shift_eq_integral h (a ^ 2 + b ^ 2)
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) f hf
  rw [hs]
  unfold gaussianExpectation
  rw [← integral_prod _ hi]
  exact he

/-- Rotation leaves the standard normal law invariant in either coordinate. -/
theorem gaussian_rotation_expectation (h a θ : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    gaussianExpectation (fun z => gaussianExpectation
      (fun w => f (h + a * Real.cos θ * z + a * Real.sin θ * w))) =
      gaussianExpectation (fun z => f (h + |a| * z)) := by
  rw [gaussianExpectation_double_affine_collapse h (a * Real.cos θ)
    (a * Real.sin θ) f hf M hb]
  have hv : (a * Real.cos θ) ^ 2 + (a * Real.sin θ) ^ 2 = a ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hv, Real.sqrt_sq_eq_abs]

/-- A coefficient and its absolute value give the same affine Gaussian law. -/
theorem gaussianExpectation_affine_abs (h a : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    gaussianExpectation (fun z => f (h + a * z)) =
      gaussianExpectation (fun z => f (h + |a| * z)) := by
  have he := gaussianExpectation_double_affine_collapse h a 0 f hf M hb
  simpa [Real.sqrt_sq_eq_abs] using he

/-- The signed coefficient form of Gaussian rotation invariance. -/
theorem gaussian_rotation_expectation_signed (h a θ : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    gaussianExpectation (fun z => gaussianExpectation
      (fun w => f (h + a * Real.cos θ * z + a * Real.sin θ * w))) =
      gaussianExpectation (fun z => f (h + a * z)) := by
  rw [gaussian_rotation_expectation h a θ f hf M hb]
  exact (gaussianExpectation_affine_abs h a f hf M hb).symm

/-- The real heat operators form a semigroup at nonnegative times. -/
theorem heatSemigroup_add (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) (x : ℝ) :
    heatSemigroup u (heatSemigroup v f) x = heatSemigroup (u + v) f x := by
  unfold heatSemigroup
  rw [gaussianExpectation_double_affine_collapse x (Real.sqrt u) (Real.sqrt v) f hf M hb]
  rw [Real.sq_sqrt hu, Real.sq_sqrt hv]

end Paper
