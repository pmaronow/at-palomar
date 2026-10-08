module

public import Paper.Hyperbolic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Concrete Gaussian quantities

The expectations in the paper are Bochner integrals against mathlib's standard
Gaussian probability measure. We keep `q` explicit; existence and uniqueness of
the fixed point are proved separately in `FixedPointUnique.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1

noncomputable def gaussianField (β h q z : ℝ) : ℝ := β * Real.sqrt q * z + h

noncomputable def overlapMap (β h q : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (gaussianField β h q z) ^ 2)

noncomputable def atParameter (β h q : ℝ) : ℝ :=
  β ^ 2 * gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 4)

noncomputable def rsFreeEnergy (β h q : ℝ) : ℝ :=
  Real.log 2 + gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z)))
    + β ^ 2 / 4 * (1 - q) ^ 2

noncomputable def heatSemigroup (ell : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  gaussianExpectation (fun z => φ (x + Real.sqrt ell * z))

noncomputable def gaussianA (h t : ℝ) : ℝ :=
  gaussianExpectation (fun z => sech (h + Real.sqrt t * z) ^ 2)

noncomputable def gaussianC (h t : ℝ) : ℝ :=
  gaussianExpectation (fun z => sech (h + Real.sqrt t * z) ^ 4)

noncomputable def atZeroFunction (h t : ℝ) : ℝ :=
  t * gaussianC h t + gaussianA h t - 1

@[simp] theorem gaussianExpectation_const (c : ℝ) :
    gaussianExpectation (fun _ => c) = c := by
  simp [gaussianExpectation]

 theorem integrable_gaussian_tanh_sq (β h q : ℝ) :
    Integrable (fun z => Real.tanh (gaussianField β h q z) ^ 2) (gaussianReal 0 1) := by
  have hc : Continuous (fun z => gaussianField β h q z) := by unfold gaussianField; fun_prop
  have hm : AEStronglyMeasurable (fun z => Real.tanh (gaussianField β h q z) ^ 2) (gaussianReal 0 1) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact (((Real.continuous_sinh.comp hc).div (Real.continuous_cosh.comp hc)
      (fun z => ne_of_gt (Real.cosh_pos _))).pow 2).aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono' hm
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (tanh_sq_lt_one _).le

 theorem integrable_gaussian_sech_pow (h a : ℝ) (n : ℕ) :
    Integrable (fun z => sech (h + a * z) ^ n) (gaussianReal 0 1) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · have hc : Continuous (fun z => h + a * z) := by fun_prop
    exact ((continuous_const.div (Real.continuous_cosh.comp hc)
      (fun z => ne_of_gt (Real.cosh_pos _))).pow n).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos _).le n)]
    exact pow_le_one₀ (sech_pos _).le (sech_le_one _)

 theorem overlapMap_nonneg (β h q : ℝ) : 0 ≤ overlapMap β h q := by
  exact integral_nonneg (fun _ => sq_nonneg _)

 theorem overlapMap_le_one (β h q : ℝ) : overlapMap β h q ≤ 1 := by
  have hi := integral_mono (integrable_gaussian_tanh_sq β h q)
    (integrable_const (1 : ℝ)) (fun z => (tanh_sq_lt_one (gaussianField β h q z)).le)
  simpa [overlapMap, gaussianExpectation] using hi

 theorem gaussian_sech_pow_pos (h a : ℝ) (n : ℕ) :
    0 < gaussianExpectation (fun z => sech (h + a * z) ^ n) := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => (pow_pos (sech_pos _) n).le)
    (integrable_gaussian_sech_pow h a n)).mpr
  have hs : Function.support (fun z => sech (h + a * z) ^ n) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (pow_pos (sech_pos _) n)
  rw [hs]
  simp

 theorem overlapMap_add_sech_sq (β h q : ℝ) :
    overlapMap β h q + gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 2) = 1 := by
  rw [overlapMap, gaussianExpectation, gaussianExpectation,
    ← integral_add (integrable_gaussian_tanh_sq β h q) ?_]
  · simp_rw [tanh_sq_add_sech_sq]
    simp
  · simpa [gaussianField, add_comm] using integrable_gaussian_sech_pow h (β * Real.sqrt q) 2

 theorem overlapMap_lt_one (β h q : ℝ) : overlapMap β h q < 1 := by
  have he := overlapMap_add_sech_sq β h q
  have hp := gaussian_sech_pow_pos h (β * Real.sqrt q) 2
  have heq : gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 2) =
      gaussianExpectation (fun z => sech (h + β * Real.sqrt q * z) ^ 2) := by
    congr 1
    ext z
    simp [gaussianField, add_comm]
  rw [heq] at he
  linarith

@[simp] theorem overlapMap_zero (β h : ℝ) : overlapMap β h 0 = Real.tanh h ^ 2 := by
  simp [overlapMap, gaussianField]

 theorem fixedPoint_pos {β h q : ℝ} (hh : 0 < h) (hq : 0 ≤ q)
    (hfixed : q = overlapMap β h q) : 0 < q := by
  by_contra hn
  have hq0 : q = 0 := le_antisymm (le_of_not_gt hn) hq
  rw [hq0, overlapMap_zero] at hfixed
  have hp := sq_pos_of_pos (tanh_pos hh)
  linarith

 theorem fixedPoint_lt_one {β h q : ℝ} (hfixed : q = overlapMap β h q) : q < 1 := by
  rw [hfixed]
  exact overlapMap_lt_one β h q

 theorem atParameter_pos {β h q : ℝ} (hβ : β ≠ 0) : 0 < atParameter β h q := by
  unfold atParameter
  apply mul_pos (sq_pos_of_ne_zero hβ)
  simpa [gaussianField, add_comm] using gaussian_sech_pow_pos h (β * Real.sqrt q) 4

 theorem atParameter_le_beta_sq (β h q : ℝ) : atParameter β h q ≤ β ^ 2 := by
  have hi := integral_mono (integrable_gaussian_sech_pow h (β * Real.sqrt q) 4)
    (integrable_const (1 : ℝ)) (fun z => pow_le_one₀ (sech_pos _).le (sech_le_one _) (n := 4))
  have hb : gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 4) ≤ 1 := by
    simpa [gaussianExpectation, gaussianField, add_comm] using hi
  unfold atParameter
  nlinarith [sq_nonneg β]

 theorem heatSemigroup_zero (φ : ℝ → ℝ) (x : ℝ) : heatSemigroup 0 φ x = φ x := by
  simp [heatSemigroup]

 theorem gaussianA_zero_time (h : ℝ) : gaussianA h 0 = sech h ^ 2 := by simp [gaussianA]
 theorem gaussianC_zero_time (h : ℝ) : gaussianC h 0 = sech h ^ 4 := by simp [gaussianC]

/-- Gaussian exponential moments make the unbounded RS terminal datum integrable. -/
theorem integrable_gaussian_cosh_affine (h a : ℝ) :
    Integrable (fun z => Real.cosh (h + a * z)) (gaussianReal 0 1) := by
  have hp := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).const_mul (Real.exp h)
  have hn := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a)).const_mul (Real.exp (-h))
  convert (hp.add hn).div_const 2 using 1
  ext z
  rw [Real.cosh_eq, Real.exp_add]
  congr 1
  rw [show -(h + a * z) = -h + -a * z by ring, Real.exp_add]
  rfl

 theorem integrable_gaussian_logcosh_affine (h a : ℝ) :
    Integrable (fun z => Real.log (Real.cosh (h + a * z))) (gaussianReal 0 1) := by
  have hc : Continuous (fun z => Real.cosh (h + a * z)) := by fun_prop
  refine (integrable_gaussian_cosh_affine h a).mono'
    (hc.log (fun z => ne_of_gt (Real.cosh_pos _))).aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh _))]
  exact (Real.log_le_sub_one_of_pos (Real.cosh_pos _)).trans (by linarith)

 theorem integrable_rs_logcosh (β h q : ℝ) :
    Integrable (fun z => Real.log (Real.cosh (gaussianField β h q z))) (gaussianReal 0 1) := by
  simpa [gaussianField, add_comm] using integrable_gaussian_logcosh_affine h (β * Real.sqrt q)

end Paper
