module

public import Paper.ParisiMild
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Spatial derivatives of Gaussian smoothing for bounded measurable data

Differentiation acts on the density, so the observable need not possess a
derivative.  A shifted Gaussian with doubled variance dominates the density
derivative uniformly over a neighborhood of its mean.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Paper

theorem hasDerivAt_gaussianPDFReal_mean (v : ℝ≥0) (hv : 0 < (v : ℝ)) (y x : ℝ) :
    HasDerivAt (fun a : ℝ => gaussianPDFReal a v y)
      ((y - x) / (v : ℝ) * gaussianPDFReal x v y) x := by
  have hi := ((((hasDerivAt_const x y).sub (hasDerivAt_id x)).pow 2).neg.div_const
    (2 * (v : ℝ))).exp
  unfold gaussianPDFReal
  convert hi.const_mul ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) using 1
  · rfl
  · dsimp
    field_simp
    ring

private theorem gaussianPDFReal_mean_neighborhood_bound (v : ℝ≥0)
    (hv : 0 < (v : ℝ)) (x₀ x y : ℝ) (hx : |x - x₀| ≤ 1) :
    gaussianPDFReal x v y ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (1 / (2 * (v : ℝ))) *
        Real.exp (-(1 / (4 * (v : ℝ))) * (y - x₀) ^ 2) := by
  have hs : (x - x₀) ^ 2 ≤ 1 := by
    have ha := abs_nonneg (x - x₀)
    nlinarith [sq_abs (x - x₀)]
  have hq : (y - x) ^ 2 ≥ (y - x₀) ^ 2 / 2 - 1 := by
    nlinarith [sq_nonneg ((y - x₀) - 2 * (x - x₀))]
  have he : -(y - x) ^ 2 / (2 * (v : ℝ)) ≤
      1 / (2 * (v : ℝ)) - (1 / (4 * (v : ℝ))) * (y - x₀) ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))).mpr
    field_simp
    nlinarith
  unfold gaussianPDFReal
  calc
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - x) ^ 2 / (2 * (v : ℝ))) ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (1 / (2 * (v : ℝ)) - (1 / (4 * (v : ℝ))) * (y - x₀) ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [show 1 / (2 * (v : ℝ)) - (1 / (4 * (v : ℝ))) * (y - x₀) ^ 2 =
        1 / (2 * (v : ℝ)) + (-(1 / (4 * (v : ℝ)))) * (y - x₀) ^ 2 by ring,
        Real.exp_add]
      ring

noncomputable def gaussianSpatialDerivativeEnvelope (v : ℝ≥0) (x₀ M y : ℝ) : ℝ :=
  M * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (1 / (2 * (v : ℝ))) /
    (v : ℝ) * ((|y - x₀| + 1) * Real.exp (-(1 / (4 * (v : ℝ))) * (y - x₀) ^ 2))

theorem integrable_gaussianSpatialDerivativeEnvelope (v : ℝ≥0)
    (hv : 0 < (v : ℝ)) (x₀ M : ℝ) :
    Integrable (gaussianSpatialDerivativeEnvelope v x₀ M) := by
  have hpos : (0 : ℝ) < 1 / (4 * (v : ℝ)) := by positivity
  have hi : Integrable (fun z : ℝ => |z| * Real.exp (-(1 / (4 * (v : ℝ))) * z ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hpos).norm
  have hg := integrable_exp_neg_mul_sq hpos
  have hs : Integrable (fun z : ℝ => (|z| + 1) *
      Real.exp (-(1 / (4 * (v : ℝ))) * z ^ 2)) := by
    convert hi.add hg using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  exact (hs.comp_sub_right x₀).const_mul _

theorem norm_gaussianSpatialDerivative_le_envelope (v : ℝ≥0)
    (hv : 0 < (v : ℝ)) (f : ℝ → ℝ) (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M)
    (x₀ x y : ℝ) (hx : |x - x₀| ≤ 1) :
    ‖((y - x) / (v : ℝ) * gaussianPDFReal x v y) * f y‖ ≤
      gaussianSpatialDerivativeEnvelope v x₀ M y := by
  have hM : 0 ≤ M := (norm_nonneg (f y)).trans (hb y)
  have hab : |y - x| ≤ |y - x₀| + 1 := by
    calc
      |y - x| = |(y - x₀) - (x - x₀)| := by congr 1; ring
      _ ≤ |y - x₀| + |x - x₀| := abs_sub _ _
      _ ≤ |y - x₀| + 1 := by linarith
  have hpdf := gaussianPDFReal_mean_neighborhood_bound v hv x₀ x y hx
  simp only [norm_mul, Real.norm_eq_abs, abs_div,
    abs_of_pos hv, abs_of_nonneg (gaussianPDFReal_nonneg x v y)]
  calc
    (|y - x| / (v : ℝ) * gaussianPDFReal x v y) * |f y| ≤
      ((|y - x₀| + 1) / (v : ℝ) *
        ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (1 / (2 * (v : ℝ))) *
          Real.exp (-(1 / (4 * (v : ℝ))) * (y - x₀) ^ 2))) * M :=
            mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right hab hv.le) hpdf
              (gaussianPDFReal_nonneg x v y) (by positivity)) (hb y)
              (abs_nonneg _) (by positivity)
    _ = gaussianSpatialDerivativeEnvelope v x₀ M y := by
      unfold gaussianSpatialDerivativeEnvelope
      ring

/-- Differentiation of the actual Gaussian integral in its mean, for bounded
measurable observables with no spatial derivative assumption. -/
theorem hasDerivAt_gaussian_mean_of_bounded (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    HasDerivAt (fun a : ℝ => ∫ y, f y ∂gaussianReal a v)
      (∫ y, ((y - x) / (v : ℝ) * gaussianPDFReal x v y) * f y) x := by
  have hmeas : ∀ᶠ a in 𝓝 x,
      AEStronglyMeasurable (fun y => gaussianPDFReal a v y * f y) volume :=
    .of_forall fun a => ((measurable_gaussianPDFReal a v).mul hf).aestronglyMeasurable
  have hi : Integrable (fun y => gaussianPDFReal x v y * f y) :=
    (integrable_gaussianPDFReal x v).mul_bdd hf.aestronglyMeasurable (.of_forall hb)
  have hdm : AEStronglyMeasurable
      (fun y => ((y - x) / (v : ℝ) * gaussianPDFReal x v y) * f y) volume := by
    exact (((measurable_id.sub measurable_const).div_const (v : ℝ)).mul
      (measurable_gaussianPDFReal x v)).mul hf |>.aestronglyMeasurable
  have hbound : ∀ᵐ y : ℝ, ∀ a ∈ Metric.ball x 1,
      ‖((y - a) / (v : ℝ) * gaussianPDFReal a v y) * f y‖ ≤
        gaussianSpatialDerivativeEnvelope v x M y := by
    filter_upwards with y a ha
    apply norm_gaussianSpatialDerivative_le_envelope v hv f M hb x a y
    exact (show |a - x| < 1 by simpa only [Metric.mem_ball, Real.dist_eq] using ha).le
  have hd : ∀ᵐ y : ℝ, ∀ a ∈ Metric.ball x 1,
      HasDerivAt (fun a => gaussianPDFReal a v y * f y)
        (((y - a) / (v : ℝ) * gaussianPDFReal a v y) * f y) a :=
    .of_forall fun y a _ => (hasDerivAt_gaussianPDFReal_mean v hv y a).mul_const (f y)
  have hout := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (α := ℝ) (μ := volume) (x₀ := x)
    (F := fun a y => gaussianPDFReal a v y * f y)
    (F' := fun a y => ((y - a) / (v : ℝ) * gaussianPDFReal a v y) * f y)
    (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)) hmeas hi hdm hbound
    (integrable_gaussianSpatialDerivativeEnvelope v hv x M) hd).2
  have hvn : v ≠ 0 := by exact_mod_cast hv.ne'
  have he : (fun a : ℝ => ∫ y, f y ∂gaussianReal a v) =
      (fun a : ℝ => ∫ y, gaussianPDFReal a v y * f y) := by
    funext a
    simpa only [smul_eq_mul] using integral_gaussianReal_eq_integral_smul (f := f) hvn
  rw [he]
  exact hout

theorem gaussian_spatial_derivative_eq_heatGradient (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    (∫ y, ((y - x) / (v : ℝ) * gaussianPDFReal x v y) * f y) =
      heatGradient (v : ℝ) f x := by
  let g : ℝ → ℝ := fun y => (y - x) / (v : ℝ) * f y
  have hg : Measurable g := ((measurable_id.sub measurable_const).div_const (v : ℝ)).mul hf
  have he : gaussianExpectation (fun z => g (x + Real.sqrt (v : ℝ) * z)) =
      ∫ y, g y ∂gaussianReal x v := by
    simpa using gaussianExpectation_shift_eq_integral x
      (v : ℝ) hv.le g hg
  have hvn : v ≠ 0 := by exact_mod_cast hv.ne'
  have hs : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hratio : Real.sqrt (v : ℝ) / (v : ℝ) = (Real.sqrt (v : ℝ))⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt hv.le]
  calc
    (∫ y, ((y - x) / (v : ℝ) * gaussianPDFReal x v y) * f y) =
        ∫ y, g y ∂gaussianReal x v := by
      rw [integral_gaussianReal_eq_integral_smul (f := g) hvn]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [g]
      ring
    _ = gaussianExpectation (fun z => g (x + Real.sqrt (v : ℝ) * z)) := he.symm
    _ = heatGradient (v : ℝ) f x := by
      have hfun : (fun z => g (x + Real.sqrt (v : ℝ) * z)) =
          (fun z => (Real.sqrt (v : ℝ))⁻¹ * (z * f (x + Real.sqrt (v : ℝ) * z))) := by
        funext z
        dsimp [g]
        calc
          (x + Real.sqrt (v : ℝ) * z - x) / (v : ℝ) * f (x + Real.sqrt (v : ℝ) * z) =
            (Real.sqrt (v : ℝ) / (v : ℝ)) * (z * f (x + Real.sqrt (v : ℝ) * z)) := by ring
          _ = _ := by rw [hratio]
      rw [hfun]
      exact integral_const_mul _ _

/-- Gaussian smoothing differentiates bounded measurable data.  The input
function need not be differentiable or continuous. -/
theorem hasDerivAt_heatSemigroup_spatial (ell : ℝ) (hell : 0 < ell)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    HasDerivAt (heatSemigroup ell f) (heatGradient ell f x) x := by
  have hv : 0 < (ell.toNNReal : ℝ) := by simpa [Real.coe_toNNReal ell hell.le] using hell
  have hd := hasDerivAt_gaussian_mean_of_bounded ell.toNNReal hv f hf M hb x
  rw [gaussian_spatial_derivative_eq_heatGradient ell.toNNReal hv f hf x,
    Real.coe_toNNReal ell hell.le] at hd
  have he : heatSemigroup ell f = (fun a : ℝ => ∫ y, f y ∂gaussianReal a ell.toNNReal) := by
    funext a
    exact gaussianExpectation_shift_eq_integral a ell hell.le f hf
  rw [he]
  exact hd

end Paper
