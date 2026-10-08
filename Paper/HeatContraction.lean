module

public import Paper.Hyperbolic
public import Paper.Semigroup
public import Paper.SymmetrizedWeight
public import Paper.DoobHeat
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# The actual radial weight in the heat-contraction estimate

This file checks every analytic hypothesis of the Gaussian-kernel contraction
for the paper's `sech³` and its symmetrized Gaussian/cosh weight, with the
positive scalar normalization removed. In particular integrability is proved,
not supplied as an assumption.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Paper

theorem continuous_sech : Continuous sech := by
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sech x).continuousAt

theorem measurable_sech_cube : Measurable (fun x : ℝ => sech x ^ 3) :=
  (continuous_sech.pow 3).measurable

theorem sech_cube_bound (x : ℝ) : ‖sech x ^ 3‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 3)]
  simpa using pow_le_pow_left₀ (sech_pos x).le (sech_le_one x) 3

/-- The tilt/cosh ratio is at most one in the parameter region used in the paper. -/
theorem radialWeight_le_gaussian {v c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : ℝ) :
    radialWeight v c x ≤ Real.exp (-x ^ 2 / (2 * v)) := by
  have hc : Real.cosh (c * x) ≤ Real.cosh x := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  unfold radialWeight
  rw [div_le_iff₀ (Real.cosh_pos x)]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le

/-- Gaussian domination supplies absolute convergence of the paper's even weight. -/
theorem integrable_radialWeight {v c : ℝ} (hv : 0 < v) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Integrable (radialWeight v c) := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * v))) := by
    convert integrable_exp_neg_mul_sq (one_div_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hv)) using 1
    ext x
    congr 1
    ring
  apply hgauss.mono' (continuous_iff_continuousAt.mpr (fun x =>
    (hasDerivAt_radialWeight hv c x).continuousAt)).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (radialWeight_pos v c x).le]
  exact radialWeight_le_gaussian hc0 hc1 x

/-- Proposition 5.5's Gaussian heat contraction for the explicit functions,
without unproved integrability or pointwise sign hypotheses. -/
theorem radialWeight_heat_contraction {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    (∫ x, radialWeight v c x * kernelAverage (μ := volume) (heatKernel lam)
      (fun y => sech y ^ 3) x) ≤ ∫ x, radialWeight v c x * sech x ^ 3 := by
  exact gaussian_heat_contraction lam hlam (radialWeight v c) (fun y => sech y ^ 3)
    (integrable_radialWeight hv hc0 hc1) measurable_sech_cube 1 sech_cube_bound
    (radialWeight_sech_cube_comonotone hv hc0 hc1)

/-- The paper's exponential heat-convolution estimate for its actual weight. -/
theorem radialWeight_heat_exponential_decay {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    Real.exp (-(lam : ℝ) / 2) *
      (∫ x, radialWeight v c x * kernelAverage (μ := volume) (heatKernel lam)
        (fun y => sech y ^ 3) x) ≤
      Real.exp (-(lam : ℝ) / 2) * (∫ x, radialWeight v c x * sech x ^ 3) := by
  exact mul_le_mul_of_nonneg_left (radialWeight_heat_contraction hv hc0 hc1 lam hlam)
    (Real.exp_pos _).le

/-- Strict contraction follows from a continuous nonnegative double-integrand
that is positive already at `(0,1)`. -/
theorem radialWeight_heat_strict_contraction {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    (∫ x, radialWeight v c x * kernelAverage (μ := volume) (heatKernel lam)
      (fun y => sech y ^ 3) x) < ∫ x, radialWeight v c x * sech x ^ 3 := by
  let w := radialWeight v c
  let k := fun x : ℝ => sech x ^ 3
  let F := fun z : ℝ × ℝ => heatKernel lam z.1 z.2 *
    (w z.1 - w z.2) * (k z.1 - k z.2)
  have hw : Integrable w := integrable_radialWeight hv hc0 hc1
  have hwcont : Continuous w := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_radialWeight hv c x).continuousAt)
  have hkcont : Continuous k := continuous_sech.pow 3
  have hkernel : Continuous (fun z : ℝ × ℝ => heatKernel lam z.1 z.2) := by
    unfold heatKernel ProbabilityTheory.gaussianPDFReal
    fun_prop
  have hFcont : Continuous F :=
    (hkernel.mul ((hwcont.comp continuous_fst).sub (hwcont.comp continuous_snd))).mul
      ((hkcont.comp continuous_fst).sub (hkcont.comp continuous_snd))
  obtain ⟨hdiag, hcross⟩ := kernel_pair_integrable (μ := volume) (heatKernel lam) w k
    (heatKernel_nonneg lam) (measurable_heatKernel lam) (integral_heatKernel_eq_one lam hlam)
    hw measurable_sech_cube 1 sech_cube_bound
  have hFint : Integrable F (volume.prod volume) :=
    symmetric_kernel_difference_integrable (μ := volume) (heatKernel lam) w k
      (heatKernel_symm lam) hdiag hcross
  have hFnonneg : 0 ≤ F := by
    intro z
    dsimp [F]
    rw [mul_assoc]
    exact mul_nonneg (heatKernel_nonneg lam z.1 z.2)
      (radialWeight_sech_cube_comonotone hv hc0 hc1 z.1 z.2)
  have hwdiff : 0 < w 0 - w 1 := sub_pos.mpr
    ((radialWeight_strictAntiOn hv hc0 hc1) (by norm_num) (by norm_num) (by norm_num))
  have hsech : sech 1 < sech 0 := by
    simp only [sech_zero]
    rw [sech, div_lt_one (Real.cosh_pos 1)]
    exact Real.one_lt_cosh.mpr (by norm_num)
  have hkdiff : 0 < k 0 - k 1 := by
    apply sub_pos.mpr
    exact pow_lt_pow_left₀ hsech (sech_pos 1).le (by norm_num)
  have hFpoint : F (0, 1) ≠ 0 := ne_of_gt (mul_pos
    (mul_pos (ProbabilityTheory.gaussianPDFReal_pos 0 lam (0 - 1) hlam) hwdiff) hkdiff)
  have hFpos : 0 < ∫ z : ℝ × ℝ, F z ∂volume.prod volume :=
    integral_pos_of_integrable_nonneg_nonzero hFcont hFint hFnonneg hFpoint
  have hid := symmetric_kernel_difference_identity (μ := volume) (heatKernel lam) w k
    (heatKernel_symm lam) (integral_heatKernel_eq_one lam hlam) hdiag hcross
  change (∫ x, w x * kernelAverage (μ := volume) (heatKernel lam) k x) < ∫ x, w x * k x
  change (∫ x, w x * k x) - (∫ x, w x * kernelAverage (μ := volume) (heatKernel lam) k x) =
    (1 / 2 : ℝ) * (∫ z : ℝ × ℝ, F z ∂volume.prod volume) at hid
  linarith

theorem radialWeight_heat_strict_exponential_decay {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    Real.exp (-(lam : ℝ) / 2) *
      (∫ x, radialWeight v c x * kernelAverage (μ := volume) (heatKernel lam)
        (fun y => sech y ^ 3) x) <
      Real.exp (-(lam : ℝ) / 2) * (∫ x, radialWeight v c x * sech x ^ 3) :=
  mul_lt_mul_of_pos_left (radialWeight_heat_strict_contraction hv hc0 hc1 lam hlam)
    (Real.exp_pos _)

/-- The exact Gaussian symmetrization in the paper is integrable. -/
theorem integrable_symmetrizedWeight (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ)) :
    Integrable (symmetrizedWeight h v) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hc0 : 0 ≤ h / (v : ℝ) := div_nonneg hh0 hvpos.le
  have hc1 : h / (v : ℝ) ≤ 1 := (div_le_one hvpos).mpr hhv
  convert (integrable_radialWeight hvpos hc0 hc1).const_mul
    (ProbabilityTheory.gaussianPDFReal h v 0) using 1
  ext x
  exact symmetrizedWeight_eq_radialWeight h v hv x

/-- The Gaussian heat contraction for the exact weight, with all analytic
hypotheses derived from `0 ≤ h ≤ v`. -/
theorem symmetrizedWeight_heat_contraction (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ)) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    (∫ x, symmetrizedWeight h v x * kernelAverage (μ := volume) (heatKernel lam)
      (fun y => sech y ^ 3) x) ≤ ∫ x, symmetrizedWeight h v x * sech x ^ 3 :=
  gaussian_heat_contraction lam hlam (symmetrizedWeight h v) (fun y => sech y ^ 3)
    (integrable_symmetrizedWeight h v hv hh0 hhv) measurable_sech_cube 1 sech_cube_bound
    (symmetrizedWeight_sech_cube_comonotone h v hv hh0 hhv)

theorem symmetrizedWeight_heat_exponential_decay (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ)) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    Real.exp (-(lam : ℝ) / 2) *
      (∫ x, symmetrizedWeight h v x * kernelAverage (μ := volume) (heatKernel lam)
        (fun y => sech y ^ 3) x) ≤
      Real.exp (-(lam : ℝ) / 2) * (∫ x, symmetrizedWeight h v x * sech x ^ 3) :=
  mul_le_mul_of_nonneg_left (symmetrizedWeight_heat_contraction h v hv hh0 hhv lam hlam)
    (Real.exp_pos _).le

/-- Symmetrization against an even test function preserves the Gaussian/cosh
pairing. Its only analytic hypothesis is integrability of that pairing. -/
theorem integral_gaussian_cosh_even_symmetrization (h : ℝ) (v : ℝ≥0)
    (f : ℝ → ℝ) (hf_even : ∀ x, f (-x) = f x)
    (hf : Integrable (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x)) :
    (∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x) =
      ∫ x, symmetrizedWeight h v x * f x := by
  have href : Integrable
      (fun x => ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) := by
    simpa only [Real.cosh_neg, hf_even] using hf.comp_neg
  have hreflect :
      (∫ x, ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) =
        ∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x := by
    simpa only [Real.cosh_neg, hf_even] using
      integral_neg_eq_self (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x) volume
  have heq : (fun x => symmetrizedWeight h v x * f x) =
      (fun x => (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * f x +
        ProbabilityTheory.gaussianPDFReal h v (-x) / Real.cosh x * f x) / 2) := by
    ext x
    unfold symmetrizedWeight
    ring
  rw [heq, integral_div, integral_add hf href, hreflect]
  ring

theorem integrable_gaussian_div_cosh (h : ℝ) (v : ℝ≥0) :
    Integrable (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x) := by
  convert (ProbabilityTheory.integrable_gaussianPDFReal h v).mul_bdd
    continuous_sech.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => show ‖sech x‖ ≤ (1 : ℝ) by
      rw [Real.norm_of_nonneg (sech_pos x).le]
      exact sech_le_one x) using 1
  ext x
  dsimp [sech]
  ring

/-- Fubini supplies integrability of the outer Gaussian/cosh heat pairing. -/
theorem integrable_gaussian_cosh_heat_pairing (h : ℝ) (v : ℝ≥0)
    (lam : ℝ≥0) (hlam : lam ≠ 0) :
    Integrable (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x *
      kernelAverage (μ := volume) (heatKernel lam) (fun y => sech y ^ 3) x) := by
  obtain ⟨_, hcross⟩ := kernel_pair_integrable (μ := volume) (heatKernel lam)
    (fun x => ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x) (fun y => sech y ^ 3)
    (heatKernel_nonneg lam) (measurable_heatKernel lam) (integral_heatKernel_eq_one lam hlam)
    (integrable_gaussian_div_cosh h v) measurable_sech_cube 1 sech_cube_bound
  convert hcross.integral_prod_left using 1
  ext x
  change _ = ∫ y, heatKernel lam x y *
    (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x) * sech y ^ 3
  rw [show (fun y => heatKernel lam x y *
      (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x) * sech y ^ 3) =
      (fun y => (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x) *
        (heatKernel lam x y * sech y ^ 3)) by ext y; ring]
  rw [integral_const_mul]
  rfl

/-- The pairing at heat time zero is exactly the paper's fourth-sech Gaussian
moment, including its normalizing constant. -/
theorem symmetrizedWeight_sech_cube_integral (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x, symmetrizedWeight h v x * sech x ^ 3) =
      ∫ x, sech x ^ 4 ∂ProbabilityTheory.gaussianReal h v := by
  have hi : Integrable (fun x => ProbabilityTheory.gaussianPDFReal h v x /
      Real.cosh x * sech x ^ 3) :=
    (integrable_gaussian_div_cosh h v).mul_bdd measurable_sech_cube.aestronglyMeasurable
      (Filter.Eventually.of_forall sech_cube_bound)
  calc
    _ = ∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x * sech x ^ 3 :=
      (integral_gaussian_cosh_even_symmetrization h v (fun x => sech x ^ 3)
        (by intro x; simp) hi).symm
    _ = ∫ x, ProbabilityTheory.gaussianPDFReal h v x * sech x ^ 4 := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [sech]
      ring
    _ = _ := by
      rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
      simp only [smul_eq_mul]

/-- The Gaussian average of the Doob-transformed fourth-sech function is the
paper's exact symmetrized heat pairing. -/
theorem integral_doobOperator_sech_fourth_eq_symmetrized
    (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (lam : ℝ≥0) (hlam : lam ≠ 0) :
    (∫ x, doobOperator lam (fun y => sech y ^ 4) x ∂ProbabilityTheory.gaussianReal h v) =
      Real.exp (-(lam : ℝ) / 2) *
        (∫ x, symmetrizedWeight h v x * kernelAverage (μ := volume) (heatKernel lam)
          (fun y => sech y ^ 3) x) := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, doobOperator_sech_fourth_eq_heat lam hlam]
  calc
    _ = ∫ x, Real.exp (-(lam : ℝ) / 2) *
        (ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x *
          kernelAverage (μ := volume) (heatKernel lam) (fun y => sech y ^ 3) x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = Real.exp (-(lam : ℝ) / 2) *
        (∫ x, ProbabilityTheory.gaussianPDFReal h v x / Real.cosh x *
          kernelAverage (μ := volume) (heatKernel lam) (fun y => sech y ^ 3) x) :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_gaussian_cosh_even_symmetrization h v
        (kernelAverage (μ := volume) (heatKernel lam) (fun y => sech y ^ 3))
        (heatAverage_sech_cube_even lam) (integrable_gaussian_cosh_heat_pairing h v lam hlam)]

/-- The full analytic decay estimate for the actual Gaussian Doob transform.
The remaining diffusion-law identification in Proposition 5.4 is separate. -/
theorem gaussian_doob_sech_fourth_exponential_decay
    (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (hh0 : 0 ≤ h) (hhv : h ≤ (v : ℝ))
    (lam : ℝ≥0) (hlam : lam ≠ 0) :
    (∫ x, doobOperator lam (fun y => sech y ^ 4) x ∂ProbabilityTheory.gaussianReal h v) ≤
      Real.exp (-(lam : ℝ) / 2) *
        (∫ x, sech x ^ 4 ∂ProbabilityTheory.gaussianReal h v) := by
  rw [integral_doobOperator_sech_fourth_eq_symmetrized h v hv lam hlam,
    ← symmetrizedWeight_sech_cube_integral h v hv]
  exact symmetrizedWeight_heat_exponential_decay h v hv hh0 hhv lam hlam

end Paper
