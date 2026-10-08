module

public import Paper.GaussianDifferentiation
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Strict positivity of odd-function Gaussian expectations

For a positive Gaussian mean, reflection makes an odd function's expectation
positive when it is strictly positive on the positive half-line. The proof
uses genuine Gaussian densities and Lebesgue integrals. The full-line
symmetrization avoids auxiliary set-integral boundary arguments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- A positive-mean Gaussian has strictly larger density at `y` than at `-y`
when `y` is positive and the variance is nonzero. -/
theorem gaussianPDFReal_reflection_lt {h : ℝ} (hh : 0 < h)
    (v : ℝ≥0) (hv : v ≠ 0) {y : ℝ} (hy : 0 < y) :
    gaussianPDFReal h v (-y) < gaussianPDFReal h v y := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hsq : (y - h) ^ 2 < (-y - h) ^ 2 := by nlinarith [mul_pos hh hy]
  unfold gaussianPDFReal
  apply mul_lt_mul_of_pos_left
  · apply Real.exp_lt_exp.mpr
    exact div_lt_div_of_pos_right (neg_lt_neg hsq) (by positivity)
  · apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    positivity

/-- Continuity of a Gaussian density as a function of its real argument. -/
theorem continuous_gaussianPDFReal_argument (h : ℝ) (v : ℝ≥0) :
    Continuous (gaussianPDFReal h v) := by
  unfold gaussianPDFReal
  fun_prop

/-- The Gaussian expectation of a continuous odd function that is positive
on the positive half-line is strictly positive at every positive mean.

The weighted density is explicitly assumed integrable. Bounded measurable
functions satisfy this hypothesis, as shown in the next theorem. -/
theorem gaussian_integral_odd_pos
    (h : ℝ) (hh : 0 < h) (v : ℝ≥0) (hv : v ≠ 0) (g : ℝ → ℝ)
    (hgcont : Continuous g) (hgodd : ∀ y, g (-y) = -g y)
    (hgpos : ∀ y, 0 < y → 0 < g y)
    (hint : Integrable (fun y => gaussianPDFReal h v y * g y)) :
    0 < ∫ y, g y ∂gaussianReal h v := by
  let p : ℝ → ℝ := gaussianPDFReal h v
  let F : ℝ → ℝ := fun y => (p y - p (-y)) * g y
  have hR : Integrable (fun y => p (-y) * g y) := by
    convert hint.comp_neg.neg using 1
    ext y
    dsimp [p]
    rw [hgodd]
    ring
  have hF : Integrable F := by
    convert hint.sub hR using 1
    ext y
    dsimp [F, p]
    ring
  have hFcont : Continuous F :=
    ((continuous_gaussianPDFReal_argument h v).sub
      ((continuous_gaussianPDFReal_argument h v).comp continuous_neg)).mul hgcont
  have hFnonneg : 0 ≤ F := by
    intro y
    change 0 ≤ (p y - p (-y)) * g y
    rcases lt_trichotomy y 0 with hy | hy | hy
    · have hpd : p y < p (-y) := by
        simpa only [neg_neg] using gaussianPDFReal_reflection_lt hh v hv (neg_pos.mpr hy)
      have hgd : g y < 0 := by
        have hhg := hgpos (-y) (neg_pos.mpr hy)
        rw [hgodd] at hhg
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpd.le) hgd.le
    · subst y
      simp
    · exact mul_nonneg (sub_nonneg.mpr (gaussianPDFReal_reflection_lt hh v hv hy).le)
        (hgpos y hy).le
  have hFone : F 1 ≠ 0 := by
    apply ne_of_gt
    change 0 < (p 1 - p (-1)) * g 1
    exact mul_pos (sub_pos.mpr (gaussianPDFReal_reflection_lt hh v hv (by norm_num)))
      (hgpos 1 (by norm_num))
  have hpositive := integral_pos_of_integrable_nonneg_nonzero hFcont hF hFnonneg hFone
  have hreflection : (∫ y, p (-y) * g y) = -(∫ y, p y * g y) := by
    calc
      _ = ∫ y, -(p (-y) * g (-y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hgodd]
        ring
      _ = -(∫ y, p (-y) * g (-y)) := integral_neg _
      _ = -(∫ y, p y * g y) := by
        rw [integral_neg_eq_self (fun y => p y * g y) volume]
  have hidentity : (∫ y, F y) = (∫ y, p y * g y) - ∫ y, p (-y) * g y := by
    calc
      _ = ∫ y, p y * g y - p (-y) * g y := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F]
        ring
      _ = _ := integral_sub hint hR
  rw [hidentity, hreflection] at hpositive
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  change 0 < ∫ y, p y * g y
  linarith

/-- Boundedness supplies the integrability hypothesis of the strict
odd-function Gaussian positivity theorem. -/
theorem gaussian_integral_odd_pos_of_bounded
    (h : ℝ) (hh : 0 < h) (v : ℝ≥0) (hv : v ≠ 0) (g : ℝ → ℝ)
    (hgcont : Continuous g) (hgodd : ∀ y, g (-y) = -g y)
    (hgpos : ∀ y, 0 < y → 0 < g y)
    (C : ℝ) (hbound : ∀ y, ‖g y‖ ≤ C) :
    0 < ∫ y, g y ∂gaussianReal h v := by
  apply gaussian_integral_odd_pos h hh v hv g hgcont hgodd hgpos
  exact (integrable_gaussianPDFReal h v).mul_bdd hgcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The affine standard-Gaussian field has mean `h` and variance `t`. -/
theorem gaussian_shift_law (h t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).map (fun z => h + Real.sqrt t * z) = gaussianReal h t.toNNReal := by
  have he : (fun z : ℝ => h + Real.sqrt t * z) =
      (fun y : ℝ => h + y) ∘ (fun z : ℝ => Real.sqrt t * z) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp only [mul_zero, zero_add, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, Real.coe_toNNReal t ht]
  exact Real.sq_sqrt ht

/-- Rewriting a concrete affine Gaussian expectation as an integral against
its Gaussian image measure. -/
theorem gaussianExpectation_shift_eq_integral
    (h t : ℝ) (ht : 0 ≤ t) (g : ℝ → ℝ) (hg : Measurable g) :
    gaussianExpectation (fun z => g (h + Real.sqrt t * z)) =
      ∫ y, g y ∂gaussianReal h t.toNNReal := by
  unfold gaussianExpectation
  rw [← gaussian_shift_law h t ht]
  exact (integral_map (by fun_prop) hg.aestronglyMeasurable).symm

/-- Uniform bound for the odd functions used in the appendix. -/
theorem norm_tanh_mul_sech_pow_le_one (y : ℝ) (n : ℕ) :
    ‖Real.tanh y * sech y ^ n‖ ≤ 1 := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (sech_pos y).le]
  simpa using mul_le_mul (Real.abs_tanh_lt_one y).le
    (pow_le_one₀ (sech_pos y).le (sech_le_one y) : sech y ^ n ≤ 1)
    (pow_nonneg (sech_pos y).le n) (by norm_num : (0 : ℝ) ≤ 1)

/-- Strict positivity for all the odd tanh-sech moments at positive mean. -/
theorem integral_tanh_mul_sech_pow_gaussian_pos
    (h : ℝ) (hh : 0 < h) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ) :
    0 < ∫ y, Real.tanh y * sech y ^ n ∂gaussianReal h v := by
  apply gaussian_integral_odd_pos_of_bounded h hh v hv (fun y => Real.tanh y * sech y ^ n)
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow n))
    (by intro y; simp)
    (fun y hy => mul_pos (tanh_pos hy) (pow_pos (sech_pos y) n))
    1 (fun y => norm_tanh_mul_sech_pow_le_one y n)

/-- The appendix's actual moment `u` is positive for `h > 0` and `t > 0`. -/
theorem gaussianU_pos (h t : ℝ) (hh : 0 < h) (ht : 0 < t) : 0 < gaussianU h t := by
  unfold gaussianU
  rw [gaussianExpectation_shift_eq_integral h t ht.le (fun y => Real.tanh y * sech y ^ 2)
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 2)).measurable]
  exact integral_tanh_mul_sech_pow_gaussian_pos h hh t.toNNReal
    (by exact_mod_cast (Real.toNNReal_pos.mpr ht).ne') 2

/-- The appendix's actual moment `v` is positive for `h > 0` and `t > 0`. -/
theorem gaussianV_pos (h t : ℝ) (hh : 0 < h) (ht : 0 < t) : 0 < gaussianV h t := by
  unfold gaussianV
  rw [gaussianExpectation_shift_eq_integral h t ht.le (fun y => Real.tanh y * sech y ^ 4)
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4)).measurable]
  exact integral_tanh_mul_sech_pow_gaussian_pos h hh t.toNNReal
    (by exact_mod_cast (Real.toNNReal_pos.mpr ht).ne') 4

/-- The appendix's mixed moment, with the Gaussian random field written out. -/
def gaussianT (h t : ℝ) : ℝ :=
  gaussianExpectation (fun z => (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) *
    sech (h + Real.sqrt t * z) ^ 4)

/-- The appendix's difference of the second and fourth sech moments. -/
def gaussianB (h t : ℝ) : ℝ := gaussianA h t - gaussianC h t

/-- Integrability of the appendix's actual `v` integrand. -/
theorem integrable_gaussianV_integrand (h t : ℝ) :
    Integrable (fun z => Real.tanh (h + Real.sqrt t * z) *
      sech (h + Real.sqrt t * z) ^ 4) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4)).comp
      (by fun_prop : Continuous (fun z : ℝ => h + Real.sqrt t * z))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => norm_tanh_mul_sech_pow_le_one _ 4)

/-- Integrability of the appendix's actual mixed `T` integrand follows from
the first Gaussian moment and a bounded multiplier. -/
theorem integrable_gaussianT_integrand (h t : ℝ) :
    Integrable (fun z => (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) *
      sech (h + Real.sqrt t * z) ^ 4) (gaussianReal 0 1) := by
  have hid : Integrable id (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hY : Integrable (fun z : ℝ => h + Real.sqrt t * z) (gaussianReal 0 1) := by
    convert (integrable_const h).add (hid.const_mul (Real.sqrt t)) using 1
    ext z
    simp only [Pi.add_apply, id_eq]
  have hg : AEStronglyMeasurable (fun z : ℝ => Real.tanh (h + Real.sqrt t * z) *
      sech (h + Real.sqrt t * z) ^ 4) (gaussianReal 0 1) :=
    ((gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4)).comp
      (by fun_prop : Continuous (fun z : ℝ => h + Real.sqrt t * z))).aestronglyMeasurable
  convert hY.mul_bdd hg (Filter.Eventually.of_forall
    (fun z => norm_tanh_mul_sech_pow_le_one (h + Real.sqrt t * z) 4)) using 1
  ext z
  ring

/-- The same mixed moment is integrable directly under the shifted Gaussian. -/
theorem integrable_tanh_sech_mixed_gaussianReal (h : ℝ) (v : ℝ≥0) :
    Integrable (fun y => y * Real.tanh y * sech y ^ 4) (gaussianReal h v) := by
  have hid : Integrable id (gaussianReal h v) :=
    (memLp_id_gaussianReal (μ := h) (v := v) 1).integrable (by norm_num)
  have hg := (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4)).aestronglyMeasurable
    (μ := gaussianReal h v)
  convert hid.mul_bdd hg (Filter.Eventually.of_forall
      (fun y => norm_tanh_mul_sech_pow_le_one y 4)) using 1
  ext y
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
  ring

/-- Gaussian integrability is equivalent to integrability after multiplying
by the real density when the variance is nonzero. -/
theorem integrable_gaussian_density_mul
    (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (g : ℝ → ℝ)
    (hg : Integrable g (gaussianReal h v)) :
    Integrable (fun y => gaussianPDFReal h v y * g y) := by
  rw [gaussianReal_of_var_ne_zero h hv] at hg
  have hi := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF h v) (Filter.Eventually.of_forall
      (fun y => gaussianPDF_lt_top (μ := h) (v := v) (x := y)))).mp hg
  simpa only [toReal_gaussianPDF, smul_eq_mul] using hi

/-- A continuous nonnegative function positive somewhere has strictly
positive expectation under a nondegenerate Gaussian. -/
theorem gaussian_integral_pos_of_continuous_nonneg
    (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (g : ℝ → ℝ)
    (hgcont : Continuous g) (hgint : Integrable g (gaussianReal h v))
    (hgnonneg : ∀ y, 0 ≤ g y) (x : ℝ) (hgpos : 0 < g x) :
    0 < ∫ y, g y ∂gaussianReal h v := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((continuous_gaussianPDFReal_argument h v).mul hgcont)
    (integrable_gaussian_density_mul h v hv g hgint)
  · intro y
    change 0 ≤ gaussianPDFReal h v y * g y
    exact mul_nonneg (gaussianPDFReal_nonneg h v y) (hgnonneg y)
  · exact (mul_pos (gaussianPDFReal_pos h v x hv) hgpos).ne'

/-- Integrability of every sech power against any Gaussian measure. -/
theorem integrable_sech_pow_gaussianReal (h : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun y => sech y ^ n) (gaussianReal h v) := by
  apply (integrable_const (1 : ℝ)).mono' (gaussian_continuous_sech.pow n).aestronglyMeasurable
  filter_upwards with y
  change ‖sech y ^ n‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le n)]
  exact pow_le_one₀ (sech_pos y).le (sech_le_one y)

/-- The pointwise gap whose expectation is `B-T`. -/
def sechMixedGap (y : ℝ) : ℝ :=
  sech y ^ 2 - sech y ^ 4 - y * Real.tanh y * sech y ^ 4

/-- Factoring the mixed gap exposes its strict sign. -/
theorem sechMixedGap_eq (y : ℝ) :
    sechMixedGap y = sech y ^ 2 *
      (Real.tanh y * (Real.tanh y - y * sech y ^ 2)) := by
  have ht : Real.tanh y ^ 2 = 1 - sech y ^ 2 := by
    have hi := tanh_sq_add_sech_sq y
    linarith
  calc
    _ = sech y ^ 2 * Real.tanh y ^ 2 - y * Real.tanh y * sech y ^ 4 := by
      rw [ht]
      unfold sechMixedGap
      ring
    _ = _ := by ring

/-- The mixed gap is strictly positive away from zero. -/
theorem sechMixedGap_pos (y : ℝ) (hy : y ≠ 0) : 0 < sechMixedGap y := by
  rw [sechMixedGap_eq]
  exact mul_pos (sech_sq_pos y) (tanh_mul_tanh_sub_mul_sech_sq_pos hy)

/-- The mixed gap is nonnegative on the entire real line. -/
theorem sechMixedGap_nonneg (y : ℝ) : 0 ≤ sechMixedGap y := by
  by_cases hy : y = 0
  · simp [hy, sechMixedGap]
  · exact (sechMixedGap_pos y hy).le

/-- The exact expectation identity relating the appendix's `B` and `T`. -/
theorem gaussianB_sub_gaussianT_eq_integral (h t : ℝ) (ht : 0 ≤ t) :
    gaussianB h t - gaussianT h t = ∫ y, sechMixedGap y ∂gaussianReal h t.toNNReal := by
  unfold gaussianB gaussianA gaussianC gaussianT
  rw [gaussianExpectation_shift_eq_integral h t ht (fun y => sech y ^ 2)
      (gaussian_continuous_sech.pow 2).measurable,
    gaussianExpectation_shift_eq_integral h t ht (fun y => sech y ^ 4)
      (gaussian_continuous_sech.pow 4).measurable,
    gaussianExpectation_shift_eq_integral h t ht (fun y => y * Real.tanh y * sech y ^ 4)
      ((continuous_id.mul gaussian_continuous_tanh).mul
        (gaussian_continuous_sech.pow 4)).measurable]
  rw [← integral_sub (integrable_sech_pow_gaussianReal h t.toNNReal 2)
      (integrable_sech_pow_gaussianReal h t.toNNReal 4)]
  have hs : Integrable (fun y => sech y ^ 2 - sech y ^ 4)
      (gaussianReal h t.toNNReal) :=
    (integrable_sech_pow_gaussianReal h t.toNNReal 2).sub
      (integrable_sech_pow_gaussianReal h t.toNNReal 4)
  rw [← integral_sub hs (integrable_tanh_sech_mixed_gaussianReal h t.toNNReal)]
  rfl

/-- The strict appendix inequality `B-T>0`, proved for the actual Gaussian
moments whenever the variance is positive. -/
theorem gaussianB_sub_gaussianT_pos (h t : ℝ) (ht : 0 < t) :
    0 < gaussianB h t - gaussianT h t := by
  rw [gaussianB_sub_gaussianT_eq_integral h t ht.le]
  have hv : t.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  apply gaussian_integral_pos_of_continuous_nonneg h t.toNNReal hv sechMixedGap (x := 1)
  · exact ((gaussian_continuous_sech.pow 2).sub (gaussian_continuous_sech.pow 4)).sub
      ((continuous_id.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 4))
  · exact ((integrable_sech_pow_gaussianReal h t.toNNReal 2).sub
      (integrable_sech_pow_gaussianReal h t.toNNReal 4)).sub
      (integrable_tanh_sech_mixed_gaussianReal h t.toNNReal)
  · exact sechMixedGap_nonneg
  · exact sechMixedGap_pos 1 (by norm_num)

/-- The mixed integrand is uniformly bounded by one. The pointwise `B-T`
gap gives a shorter proof than direct exponential estimates. -/
theorem norm_y_tanh_sech_fourth_le_one (y : ℝ) :
    ‖y * Real.tanh y * sech y ^ 4‖ ≤ 1 := by
  have hytanh : 0 ≤ y * Real.tanh y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (mul_tanh_pos hy).le
  have hnonneg : 0 ≤ y * Real.tanh y * sech y ^ 4 :=
    mul_nonneg hytanh (pow_nonneg (sech_pos y).le 4)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hgap := sechMixedGap_nonneg y
  unfold sechMixedGap at hgap
  have hs2 := sech_sq_le_one y
  have hs4 := pow_nonneg (sech_pos y).le 4
  linarith

/-- Version of strict odd-function positivity expressed using integrability
under the Gaussian measure itself. -/
theorem gaussian_integral_odd_pos_of_integrable
    (h : ℝ) (hh : 0 < h) (v : ℝ≥0) (hv : v ≠ 0) (g : ℝ → ℝ)
    (hgcont : Continuous g) (hgodd : ∀ y, g (-y) = -g y)
    (hgpos : ∀ y, 0 < y → 0 < g y)
    (hint : Integrable g (gaussianReal h v)) :
    0 < ∫ y, g y ∂gaussianReal h v :=
  gaussian_integral_odd_pos h hh v hv g hgcont hgodd hgpos
    (integrable_gaussian_density_mul h v hv g hint)

/-- Nonnegativity of the appendix's actual mixed Gaussian moment. -/
theorem gaussianT_nonneg (h t : ℝ) : 0 ≤ gaussianT h t := by
  unfold gaussianT gaussianExpectation
  apply integral_nonneg
  intro z
  change 0 ≤ (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) *
    sech (h + Real.sqrt t * z) ^ 4
  have hy : 0 ≤ (h + Real.sqrt t * z) * Real.tanh (h + Real.sqrt t * z) := by
    by_cases he : h + Real.sqrt t * z = 0
    · simp [he]
    · exact (mul_tanh_pos he).le
  exact mul_nonneg hy (pow_nonneg (sech_pos _).le 4)

/-- Strict positivity of `B=A-C` at every positive variance. -/
theorem gaussianB_pos (h t : ℝ) (ht : 0 < t) : 0 < gaussianB h t := by
  have hgap := gaussianB_sub_gaussianT_pos h t ht
  have hT := gaussianT_nonneg h t
  linarith

/-- The actual mixed moment is strictly positive at every positive variance,
for every real mean. -/
theorem gaussianT_pos (h t : ℝ) (ht : 0 < t) : 0 < gaussianT h t := by
  unfold gaussianT
  rw [gaussianExpectation_shift_eq_integral h t ht.le
    (fun y => y * Real.tanh y * sech y ^ 4)
    ((continuous_id.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 4)).measurable]
  apply gaussian_integral_pos_of_continuous_nonneg h t.toNNReal
    (Real.toNNReal_pos.mpr ht).ne' (fun y => y * Real.tanh y * sech y ^ 4) (x := 1)
  · exact (continuous_id.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 4)
  · exact integrable_tanh_sech_mixed_gaussianReal h t.toNNReal
  · intro y
    have hy : 0 ≤ y * Real.tanh y := by
      by_cases he : y = 0
      · simp [he]
      · exact (mul_tanh_pos he).le
    exact mul_nonneg hy (pow_nonneg (sech_pos y).le 4)
  · exact mul_pos (mul_tanh_pos (by norm_num : (1 : ℝ) ≠ 0)) (sech_fourth_pos 1)

end Paper
