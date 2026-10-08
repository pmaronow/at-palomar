module

public import Paper.GaussianHeat
public import Paper.GaussianConvolution
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# A Gaussian Poincaré proof by rotation

The analytic foundation is derived from dominated differentiation and the
proved one-dimensional Stein identity. No Poincaré inequality is postulated.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

lemma integrable_gaussian_pair_bounded (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hF : Continuous F) (hb : ∀ p, ‖F p‖ ≤ C) : Integrable F standardGaussianPair := by
  exact (integrable_const C).mono' hF.aestronglyMeasurable (.of_forall hb)

lemma integrable_gaussian_pair_coordinate_mul (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hF : Continuous F) (hb : ∀ p, ‖F p‖ ≤ C) :
    Integrable (fun p => p.1 * F p) standardGaussianPair ∧
      Integrable (fun p => p.2 * F p) standardGaussianPair := by
  exact ⟨(integrable_standardGaussian_id.comp_fst (gaussianReal 0 1)).mul_bdd
    hF.aestronglyMeasurable (.of_forall hb),
    (integrable_standardGaussian_id.comp_snd (gaussianReal 0 1)).mul_bdd
    hF.aestronglyMeasurable (.of_forall hb)⟩

/-- Stein's identity in the first coordinate of two independent normals. -/
theorem gaussian_pair_stein_fst (F dF : ℝ × ℝ → ℝ) (M K : ℝ)
    (hF : Continuous F) (hdF : Continuous dF)
    (hd : ∀ p, HasDerivAt (fun z => F (z, p.2)) (dF p) p.1)
    (hb : ∀ p, ‖F p‖ ≤ M) (hdb : ∀ p, ‖dF p‖ ≤ K) :
    (∫ p, p.1 * F p ∂standardGaussianPair) = ∫ p, dF p ∂standardGaussianPair := by
  simp only [standardGaussianPair]
  rw [integral_prod_symm _ (integrable_gaussian_pair_coordinate_mul F M hF hb).1,
    integral_prod_symm _ (integrable_gaussian_pair_bounded dF K hdF hdb)]
  apply integral_congr_ae
  filter_upwards [] with w
  exact gaussian_stein_of_bounded (fun z => F (z, w)) (fun z => dF (z, w)) M K
    (hF.comp (continuous_id.prodMk continuous_const))
    (hdF.comp (continuous_id.prodMk continuous_const))
    (fun z => hd (z, w)) (fun z => hb (z, w)) (fun z => hdb (z, w))

/-- Stein's identity in the second coordinate. -/
theorem gaussian_pair_stein_snd (F dF : ℝ × ℝ → ℝ) (M K : ℝ)
    (hF : Continuous F) (hdF : Continuous dF)
    (hd : ∀ p, HasDerivAt (fun z => F (p.1, z)) (dF p) p.2)
    (hb : ∀ p, ‖F p‖ ≤ M) (hdb : ∀ p, ‖dF p‖ ≤ K) :
    (∫ p, p.2 * F p ∂standardGaussianPair) = ∫ p, dF p ∂standardGaussianPair := by
  simp only [standardGaussianPair]
  rw [integral_prod _ (integrable_gaussian_pair_coordinate_mul F M hF hb).2,
    integral_prod _ (integrable_gaussian_pair_bounded dF K hdF hdb)]
  apply integral_congr_ae
  filter_upwards [] with z
  exact gaussian_stein_of_bounded (fun w => F (z, w)) (fun w => dF (z, w)) M K
    (hF.comp (continuous_const.prodMk continuous_id))
    (hdF.comp (continuous_const.prodMk continuous_id))
    (fun w => hd (z, w)) (fun w => hb (z, w)) (fun w => hdb (z, w))

/-- Correlation of a function with its Gaussian rotation. -/
def gaussianRotationCovariance (f : ℝ → ℝ) (h a θ : ℝ) : ℝ :=
  ∫ p, f (h + a * p.1) *
    f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair

/-- Differentiation of the actual rotation correlation before applying Stein. -/
theorem hasDerivAt_gaussianRotationCovariance_raw (f df : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) :
    HasDerivAt (gaussianRotationCovariance f h a)
      (∫ p, f (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) *
        a * (-Real.sin θ * p.1 + Real.cos θ * p.2) ∂standardGaussianPair) θ := by
  let F : ℝ → ℝ × ℝ → ℝ := fun b p => f (h + a * p.1) *
    f (h + a * (Real.cos b * p.1 + Real.sin b * p.2))
  let D : ℝ → ℝ × ℝ → ℝ := fun b p => f (h + a * p.1) *
    df (h + a * (Real.cos b * p.1 + Real.sin b * p.2)) *
      a * (-Real.sin b * p.1 + Real.cos b * p.2)
  have hFc (b : ℝ) : Continuous (F b) := by dsimp [F]; fun_prop
  have hDc (b : ℝ) : Continuous (D b) := by dsimp [D]; fun_prop
  have hFb : ∀ b p, ‖F b p‖ ≤ C ^ 2 := by
    intro b p
    change ‖f (h + a * p.1) *
      f (h + a * (Real.cos b * p.1 + Real.sin b * p.2))‖ ≤ C ^ 2
    rw [norm_mul]
    nlinarith [mul_le_mul (hb (h + a * p.1))
      (hb (h + a * (Real.cos b * p.1 + Real.sin b * p.2)))
      (norm_nonneg _) hC]
  have hDb : ∀ b p, ‖D b p‖ ≤ C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖) := by
    intro b p
    have htrig : ‖-Real.sin b * p.1 + Real.cos b * p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
      calc
        _ ≤ ‖-Real.sin b * p.1‖ + ‖Real.cos b * p.2‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ + ‖p.2‖ := by
          simp only [norm_mul, norm_neg, Real.norm_eq_abs]
          nlinarith [Real.abs_sin_le_one b, Real.abs_cos_le_one b,
            mul_le_mul_of_nonneg_right (Real.abs_sin_le_one b) (abs_nonneg p.1),
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one b) (abs_nonneg p.2)]
    change ‖f (h + a * p.1) * df (h + a * (Real.cos b * p.1 + Real.sin b * p.2)) *
      a * (-Real.sin b * p.1 + Real.cos b * p.2)‖ ≤ C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖)
    simp only [norm_mul]
    have hprod : ‖f (h + a * p.1)‖ *
        ‖df (h + a * (Real.cos b * p.1 + Real.sin b * p.2))‖ ≤ C ^ 2 := by
      nlinarith [mul_le_mul (hb (h + a * p.1))
        (hdb (h + a * (Real.cos b * p.1 + Real.sin b * p.2))) (norm_nonneg _) hC]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprod (norm_nonneg a)) htrig
      (norm_nonneg _) (mul_nonneg (sq_nonneg C) (norm_nonneg a))
  have hD : ∀ b p, HasDerivAt (fun x => F x p) (D b p) b := by
    intro b p
    have hi := (((Real.hasDerivAt_cos b).mul_const p.1).add
      ((Real.hasDerivAt_sin b).mul_const p.2)).const_mul a |>.const_add h
    convert ((hd _).comp b hi).const_mul (f (h + a * p.1)) using 1
    · rfl
    · dsimp [D]
      ring
  have hIntBound : Integrable (fun p : ℝ × ℝ => C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖))
      standardGaussianPair := by
    exact ((integrable_standardGaussian_id.norm.comp_fst (gaussianReal 0 1)).add
      (integrable_standardGaussian_id.norm.comp_snd (gaussianReal 0 1))).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun p => C ^ 2 * ‖a‖ * (‖p.1‖ + ‖p.2‖))
    (s := Set.univ) (by simp) (.of_forall fun b => (hFc b).aestronglyMeasurable)
    (integrable_gaussian_pair_bounded (F θ) _ (hFc θ) (hFb θ))
    (hDc θ).aestronglyMeasurable (.of_forall fun p b _ => hDb b p)
    hIntBound (.of_forall fun p b _ => hD b p)).2

private lemma poincare_mul_bound {C x y : ℝ} (hC : 0 ≤ C)
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x * y‖ ≤ C ^ 2 := by
  rw [norm_mul]
  nlinarith [mul_le_mul hx hy (norm_nonneg y) hC]

/-- The second-derivative terms cancel exactly after two Gaussian Stein
identities. This is the key identity behind Gaussian Poincaré. -/
theorem hasDerivAt_gaussianRotationCovariance (f df ddf : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hddf : Continuous ddf) (hC : 0 ≤ C)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) (hddb : ∀ x, ‖ddf x‖ ≤ C) :
    HasDerivAt (gaussianRotationCovariance f h a)
      (-a ^ 2 * Real.sin θ * ∫ p, df (h + a * p.1) *
        df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair) θ := by
  let F : ℝ × ℝ → ℝ := fun p => f (h + a * p.1) *
    df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  let P : ℝ × ℝ → ℝ := fun p => df (h + a * p.1) *
    df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  let Q : ℝ × ℝ → ℝ := fun p => f (h + a * p.1) *
    ddf (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hFb : ∀ p, ‖F p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hb _) (hdb _)
  have hPb : ∀ p, ‖P p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hdb _) (hdb _)
  have hQb : ∀ p, ‖Q p‖ ≤ C ^ 2 := fun p => poincare_mul_bound hC (hb _) (hddb _)
  have hIP := integrable_gaussian_pair_bounded P _ hPc hPb
  have hIQ := integrable_gaussian_pair_bounded Q _ hQc hQb
  have hcoord := integrable_gaussian_pair_coordinate_mul F _ hFc hFb
  have hcos : ‖Real.cos θ‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one θ
  have hsin : ‖Real.sin θ‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one θ
  have hD1c : Continuous (fun p => a * P p + a * Real.cos θ * Q p) := by fun_prop
  have hD1b : ∀ p, ‖a * P p + a * Real.cos θ * Q p‖ ≤ 2 * ‖a‖ * C ^ 2 := by
    intro p
    calc
      _ ≤ ‖a‖ * ‖P p‖ + ‖a‖ * ‖Real.cos θ‖ * ‖Q p‖ := by
        simpa only [norm_mul] using norm_add_le (a * P p) (a * Real.cos θ * Q p)
      _ ≤ ‖a‖ * C ^ 2 + ‖a‖ * 1 * C ^ 2 := by gcongr <;> first | exact hPb p | exact hcos | exact hQb p
      _ = _ := by ring
  have hD2c : Continuous (fun p => a * Real.sin θ * Q p) := by fun_prop
  have hD2b : ∀ p, ‖a * Real.sin θ * Q p‖ ≤ ‖a‖ * C ^ 2 := by
    intro p
    calc
      _ = ‖a‖ * ‖Real.sin θ‖ * ‖Q p‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a‖ * 1 * C ^ 2 := by gcongr; first | exact hsin | exact hQb p
      _ = _ := by ring
  have hD1 : ∀ p, HasDerivAt (fun z => F (z, p.2)) (a * P p + a * Real.cos θ * Q p) p.1 := by
    intro p
    have hfirst := (hd (h + a * p.1)).comp p.1
      (((hasDerivAt_id p.1).const_mul a).const_add h)
    have hsecond := (hdd (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))).comp p.1
      (((((hasDerivAt_id p.1).const_mul (Real.cos θ)).add_const (Real.sin θ * p.2)).const_mul a).const_add h)
    convert hfirst.mul hsecond using 1
    · rfl
    · dsimp [P, Q]
      ring
  have hD2 : ∀ p, HasDerivAt (fun w => F (p.1, w)) (a * Real.sin θ * Q p) p.2 := by
    intro p
    have hinner := (((((hasDerivAt_id p.2).const_mul (Real.sin θ)).const_add
      (Real.cos θ * p.1)).const_mul a).const_add h)
    have hsecond := (hdd (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))).comp p.2 hinner
    convert hsecond.const_mul (f (h + a * p.1)) using 1
    · rfl
    · dsimp [Q]
      ring
  have hS1 := gaussian_pair_stein_fst F (fun p => a * P p + a * Real.cos θ * Q p)
    (C ^ 2) (2 * ‖a‖ * C ^ 2) hFc hD1c hD1 hFb hD1b
  have hS2 := gaussian_pair_stein_snd F (fun p => a * Real.sin θ * Q p)
    (C ^ 2) (‖a‖ * C ^ 2) hFc hD2c hD2 hFb hD2b
  rw [integral_add (hIP.const_mul a) (hIQ.const_mul (a * Real.cos θ)),
    integral_const_mul, integral_const_mul] at hS1
  rw [integral_const_mul] at hS2
  have hraw := hasDerivAt_gaussianRotationCovariance_raw f df h a θ C hf hdf hC hd hb hdb
  have heq : (∫ p, f (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) *
      a * (-Real.sin θ * p.1 + Real.cos θ * p.2) ∂standardGaussianPair) =
      -a ^ 2 * Real.sin θ * ∫ p, P p ∂standardGaussianPair := by
    calc
      _ = ∫ p, (-a * Real.sin θ) * (p.1 * F p) +
          (a * Real.cos θ) * (p.2 * F p) ∂standardGaussianPair := by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp [F]
        ring
      _ = (-a * Real.sin θ) * (∫ p, p.1 * F p ∂standardGaussianPair) +
          (a * Real.cos θ) * (∫ p, p.2 * F p ∂standardGaussianPair) := by
        rw [integral_add (hcoord.1.const_mul _) (hcoord.2.const_mul _),
          integral_const_mul, integral_const_mul]
      _ = _ := by rw [hS1, hS2]; ring
  rw [heq] at hraw
  exact hraw

lemma gaussian_pair_rotated_integral (f : ℝ → ℝ) (h a θ C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) :
    (∫ p, f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair) =
      gaussianExpectation (fun z => f (h + a * z)) := by
  have heq : (fun p : ℝ × ℝ => f (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))) =
      (fun p => f (h + a * Real.cos θ * p.1 + a * Real.sin θ * p.2)) := by
    funext p
    congr 1
    ring
  have hi := integrable_gaussian_pair_bounded
    (fun p : ℝ × ℝ => f (h + a * Real.cos θ * p.1 + a * Real.sin θ * p.2))
    C (by fun_prop) (fun p => hb _)
  rw [heq]
  simp only [standardGaussianPair]
  rw [integral_prod _ hi]
  have hr := gaussian_rotation_expectation h a θ f hf.measurable C hb
  rw [abs_of_nonneg ha] at hr
  exact hr

/-- Young's inequality plus Gaussian rotation bounds the derivative correlation. -/
lemma gaussian_rotation_derivative_product_le (df : ℝ → ℝ) (h a θ C : ℝ)
    (hdf : Continuous df) (hC : 0 ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) (ha : 0 ≤ a) :
    (∫ p, df (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
      ∂standardGaussianPair) ≤ gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
  have hb2 : ∀ x, ‖df x ^ 2‖ ≤ C ^ 2 := by
    intro x
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg (df x)) (hdb x) 2
  have hi1 := integrable_gaussian_pair_bounded
    (fun p : ℝ × ℝ => df (h + a * p.1) ^ 2) (C ^ 2) (by fun_prop) (fun p => hb2 _)
  have hi2 := integrable_gaussian_pair_bounded
    (fun p : ℝ × ℝ => df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ^ 2)
    (C ^ 2) (by fun_prop) (fun p => hb2 _)
  have hiP := integrable_gaussian_pair_bounded
    (fun p : ℝ × ℝ => df (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)))
    (C ^ 2) (by fun_prop) (fun p => poincare_mul_bound hC (hdb _) (hdb _))
  have hle := integral_mono hiP ((hi1.add hi2).div_const 2) (fun p => by
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (df (h + a * p.1) -
      df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)))])
  simp only [Pi.add_apply] at hle
  rw [integral_div, integral_add hi1 hi2] at hle
  have hfirst : (∫ p, df (h + a * p.1) ^ 2 ∂standardGaussianPair) =
      gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
    simp only [standardGaussianPair]
    rw [integral_prod _ hi1]
    simp [gaussianExpectation]
  have hrot := gaussian_pair_rotated_integral (fun x => df x ^ 2) h a θ (C ^ 2)
    (hdf.pow 2) hb2 ha
  rw [hfirst, hrot] at hle
  linarith

/-- Gaussian Poincaré for bounded `C²` observables. The inequality is proved
by rotation interpolation, with all differentiation and Gaussian laws proved. -/
theorem gaussian_poincare_bounded_C2 (f df ddf : ℝ → ℝ) (h a C : ℝ)
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : Continuous f) (hdf : Continuous df) (hddf : Continuous ddf)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) (hddb : ∀ x, ‖ddf x‖ ≤ C) :
    gaussianExpectation (fun z => f (h + a * z) ^ 2) -
      gaussianExpectation (fun z => f (h + a * z)) ^ 2 ≤
        a ^ 2 * gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
  let B := gaussianExpectation (fun z => df (h + a * z) ^ 2)
  let g : ℝ → ℝ := fun θ => gaussianRotationCovariance f h a θ - a ^ 2 * Real.cos θ * B
  have hgD (θ : ℝ) : HasDerivAt g
      (a ^ 2 * Real.sin θ * (B - ∫ p, df (h + a * p.1) *
        df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair)) θ := by
    have hCov := hasDerivAt_gaussianRotationCovariance f df ddf h a θ C
      hf hdf hddf hC hd hdd hb hdb hddb
    convert hCov.sub (((Real.hasDerivAt_cos θ).const_mul (a ^ 2)).mul_const B) using 1
    ring
  have hgC : Continuous g := continuous_iff_continuousAt.mpr (fun θ => (hgD θ).continuousAt)
  have hmono : MonotoneOn g (Icc (0 : ℝ) (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hgC.continuousOn
    · exact fun θ _ => (hgD θ).differentiableAt.differentiableWithinAt
    · intro θ hθ
      rw [interior_Icc] at hθ
      rw [(hgD θ).deriv]
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
      exact mul_nonneg (mul_nonneg (sq_nonneg a) hsin)
        (sub_nonneg.mpr (gaussian_rotation_derivative_product_le df h a θ C hdf hC hdb ha))
  have hm := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  have hcov0 : gaussianRotationCovariance f h a 0 =
      gaussianExpectation (fun z => f (h + a * z) ^ 2) := by
    have hi := integrable_gaussian_pair_bounded (fun p : ℝ × ℝ => f (h + a * p.1) ^ 2)
      (C ^ 2) (by fun_prop) (fun p => by
        simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb (h + a * p.1)) 2)
    simp only [gaussianRotationCovariance, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    simp_rw [← pow_two]
    simp only [standardGaussianPair]
    rw [integral_prod _ hi]
    simp [gaussianExpectation]
  have hcovPi : gaussianRotationCovariance f h a (Real.pi / 2) =
      gaussianExpectation (fun z => f (h + a * z)) ^ 2 := by
    simp only [gaussianRotationCovariance, Real.cos_pi_div_two, Real.sin_pi_div_two,
      one_mul, zero_mul, zero_add]
    simp only [standardGaussianPair]
    rw [integral_prod_mul (fun z : ℝ => f (h + a * z)) (fun z : ℝ => f (h + a * z))]
    simp only [gaussianExpectation]
    ring
  dsimp [g] at hm
  rw [hcov0, hcovPi, Real.cos_zero, Real.cos_pi_div_two] at hm
  dsimp [B] at hm
  linarith

/-- The concrete Gaussian Poincaré inequality needed for the paper's `tanh`. -/
theorem gaussian_poincare_tanh (x a : ℝ) (ha : 0 ≤ a) :
    gaussianExpectation (fun z => Real.tanh (x + a * z) ^ 2) -
      gaussianExpectation (fun z => Real.tanh (x + a * z)) ^ 2 ≤
        a ^ 2 * gaussianExpectation (fun z => sech (x + a * z) ^ 4) := by
  have hp := gaussian_poincare_bounded_C2 Real.tanh (fun y => sech y ^ 2)
    (fun y => -2 * Real.tanh y * sech y ^ 2) x a 2 ha (by norm_num)
    gaussian_continuous_tanh (gaussian_continuous_sech.pow 2)
    ((continuous_const.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 2))
    hasDerivAt_tanh hasDerivAt_sech_sq
    (fun y => by rw [Real.norm_eq_abs]; exact (Real.abs_tanh_lt_one y).le.trans (by norm_num))
    (fun y => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact (sech_sq_le_one y).trans (by norm_num))
    sech_sq_derivative_bound
  simpa only [← pow_mul, Nat.reduceMul] using hp

end Paper

