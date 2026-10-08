module

public import Targets.Section4SignedGaussianFactor
public import Targets.Section4InitialHessian

@[expose] public section

/-!
# Jensen bound for the signed initial Hessian product

Gaussian reflection identifies the two squared marginals. The pointwise
inequality `2*x*y ≤ x²+y²` and the already checked Gaussian semigroup then
bound the signed product by the original, unsplit Hessian square.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The signed product of two Gaussian means is bounded by the unsplit square.
Both zero-variance endpoints are included. -/
theorem parisiStep_zero_signed_product_le {G : ℝ → ℝ} (hG : Measurable G)
    (hbound : ∀ x, |G x| ≤ 1) {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (h : ℝ) :
    (∫ z, parisiStep 0 v G (h + Real.sqrt (a - v) * z) *
      parisiStep 0 v G (h - Real.sqrt (a - v) * z) ∂gaussianReal 0 1) ≤
      parisiStep 0 a (fun y => (G y) ^ 2) h := by
  let B := parisiStep 0 v G
  let f := fun z => B (h + Real.sqrt (a - v) * z)
  let g := fun z => B (h - Real.sqrt (a - v) * z)
  have hBm : Measurable B := measurable_parisiStep hG 0 v
  have hBb : ∀ x, |B x| ≤ 1 := abs_parisiStep_zero_le_one hbound v
  have hf : Measurable f := hBm.comp (by fun_prop)
  have hg : Measurable g := hBm.comp (by fun_prop)
  have hb (x : ℝ) : |B x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have H := hBb x
    nlinarith [sq_abs (B x), abs_nonneg (B x)]
  have hip : Integrable (fun z => f z ^ 2) (gaussianReal 0 1) :=
    integrable_gaussian_bounded_shift (hBm.pow_const 2) hb (a - v) h
  have hneg : MeasurePreserving (fun z : ℝ => -z)
      (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have hin : Integrable (fun z => g z ^ 2) (gaussianReal 0 1) := by
    simpa only [Function.comp_def, f, g, mul_neg, ← sub_eq_add_neg] using
      hneg.integrable_comp_of_integrable hip
  have he : (∫ z, g z ^ 2 ∂gaussianReal 0 1) =
      ∫ z, f z ^ 2 ∂gaussianReal 0 1 := by
    calc
      _ = ∫ z, (f (-z)) ^ 2 ∂gaussianReal 0 1 := by
        simp only [f, g, mul_neg, ← sub_eq_add_neg]
      _ = ∫ z, f z ^ 2 ∂Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) := by
        rw [integral_map measurable_neg.aemeasurable (hf.pow_const 2).aestronglyMeasurable]
      _ = _ := by rw [hneg.map_eq]
  have hi : Integrable (fun z => f z * g z) (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (hf.mul hg).aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hBb _) (hBb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have H := integral_mono hi ((hip.add hin).div_const 2)
    (fun z => show f z * g z ≤ (f z ^ 2 + g z ^ 2) / 2 by
      nlinarith [sq_nonneg (f z - g z)])
  simp only [Pi.add_apply] at H
  rw [integral_div, integral_add hip hin, he] at H
  have H' : (∫ z, f z * g z ∂gaussianReal 0 1) ≤
      parisiStep 0 (a - v) (fun x => B x ^ 2) h := by
    simp only [parisiStep, ↓reduceIte]
    change (∫ z, f z * g z ∂gaussianReal 0 1) ≤ ∫ z, f z ^ 2 ∂gaussianReal 0 1
    linarith
  exact H'.trans (parisiStep_zero_split_square_le hG hbound hv h)

/-- The actual smoothed Hessians satisfy the signed Jensen estimate. -/
theorem signedSplitHessian_le_unsplit {A A' A'' : ℝ → ℝ}
    (hA'' : Measurable A'') (hbound : ∀ x, |A'' x| ≤ 1)
    {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (h : ℝ) :
    signedSplitHessian A A' A'' a h v ≤
      parisiStep 0 a (fun x => A'' x ^ 2) h := by
  simp only [signedSplitHessian, stepD2_zero_mass_eq_parisiStep]
  exact parisiStep_zero_signed_product_le hA'' hbound hv h

/-- Specialization to the original initial-interval scalar cascade. -/
theorem signedSplitHessian_parisiF_le_initial {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1)) :
    signedSplitHessian (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1))
      (parisiFSecond s β (k + 1)) (β ^ 2 * s.q 1) h v ≤
      section4THessianSquare s β h 1 0 := by
  have H := signedSplitHessian_le_unsplit (A := parisiF s β (k + 1))
    (A' := parisiFDeriv s β (k + 1)) (parisiF_C2_props s β (k + 1)).2.2
    (parisiF_C2_props s β (k + 1)).1.abs_second_le_one hv h
  convert H using 1
  simp only [section4THessianSquare, Nat.sub_self, s.m_zero,
    section4VarianceR_initial_eq_scalar_integral, s.q_zero, sub_zero]
  simp [stepD2_zero_mass_eq_parisiStep, tiltWeight, parisiStep]

end SpinGlass.Targets
