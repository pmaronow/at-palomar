module

public import Paper.RSFunctional
public import Paper.GaussianHeat
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # Actual continuity of the Gaussian replica-symmetric free energy -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Paper

theorem logCosh_lipschitz : LipschitzWith 1 (fun x : ℝ => Real.log (Real.cosh x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_log_cosh x).differentiableAt)
  intro x
  rw [(hasDerivAt_log_cosh x).deriv]
  exact_mod_cast (Real.abs_tanh_lt_one x).le

noncomputable def gaussianLogCoshAffine (h a : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.log (Real.cosh (h + a * z)))

noncomputable def standardGaussianAbsMoment : ℝ := gaussianExpectation (fun z : ℝ => |z|)

theorem standardGaussianAbsMoment_nonneg : 0 ≤ standardGaussianAbsMoment :=
  integral_nonneg (fun z => abs_nonneg z)

theorem integrable_standardGaussian_abs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs] using integrable_standardGaussian_id.norm

theorem gaussianLogCoshAffine_bound (h a h' a' : ℝ) :
    |gaussianLogCoshAffine h a - gaussianLogCoshAffine h' a'| ≤
      |h - h'| + |a - a'| * standardGaussianAbsMoment := by
  have hi := integrable_gaussian_logcosh_affine h a
  have hi' := integrable_gaussian_logcosh_affine h' a'
  have hboundint : Integrable (fun z : ℝ => |h - h'| + |a - a'| * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_standardGaussian_abs.const_mul _)
  have hbound : ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.log (Real.cosh (h + a * z)) - Real.log (Real.cosh (h' + a' * z))‖ ≤
        |h - h'| + |a - a'| * |z| := by
    filter_upwards with z
    have hlip := logCosh_lipschitz.dist_le_mul (h + a * z) (h' + a' * z)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hlip
    rw [Real.norm_eq_abs]
    refine hlip.trans ?_
    rw [show h + a * z - (h' + a' * z) = (h - h') + (a - a') * z by ring]
    simpa only [abs_mul] using abs_add_le (h - h') ((a - a') * z)
  have hnorm := norm_integral_le_of_norm_le hboundint hbound
  rw [integral_sub hi hi', Real.norm_eq_abs] at hnorm
  rw [integral_add (integrable_const _) (integrable_standardGaussian_abs.const_mul _),
    integral_const_mul] at hnorm
  simpa only [gaussianLogCoshAffine, standardGaussianAbsMoment, gaussianExpectation,
    integral_const, probReal_univ, one_smul] using hnorm

theorem gaussianLogCoshAffine_lipschitz :
    LipschitzWith (Real.toNNReal (1 + standardGaussianAbsMoment))
      (fun p : ℝ × ℝ => gaussianLogCoshAffine p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p p'
  rw [Real.coe_toNNReal _ (by linarith [standardGaussianAbsMoment_nonneg]), Real.dist_eq]
  have hb := gaussianLogCoshAffine_bound p.1 p.2 p'.1 p'.2
  have hh : |p.1 - p'.1| ≤ dist p p' := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have ha : |p.2 - p'.2| ≤ dist p p' := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_right ha standardGaussianAbsMoment_nonneg
  nlinarith

theorem continuous_gaussianLogCoshAffine :
    Continuous (fun p : ℝ × ℝ => gaussianLogCoshAffine p.1 p.2) :=
  gaussianLogCoshAffine_lipschitz.continuous

theorem rsFreeEnergy_eq_affine (β h q : ℝ) :
    rsFreeEnergy β h q = Real.log 2 + gaussianLogCoshAffine h (β * Real.sqrt q) +
      β ^ 2 / 4 * (1 - q) ^ 2 := by
  unfold rsFreeEnergy gaussianLogCoshAffine
  congr 2
  congr 1
  ext z
  simp only [gaussianField, add_comm]

/-- Joint continuity of the actual Gaussian RS expression, with no
bounded-observable assumption on `log cosh`. -/
theorem continuous_rsFreeEnergy_joint :
    Continuous (fun p : ℝ × ℝ × ℝ => rsFreeEnergy p.1 p.2.1 p.2.2) := by
  have hpair : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1 * Real.sqrt p.2.2)) :=
    continuous_snd.fst.prodMk (continuous_fst.mul continuous_snd.snd.sqrt)
  have hlog := continuous_gaussianLogCoshAffine.comp hpair
  have hcorr : Continuous (fun p : ℝ × ℝ × ℝ => p.1 ^ 2 / 4 * (1 - p.2.2) ^ 2) := by
    fun_prop
  rw [show (fun p : ℝ × ℝ × ℝ => rsFreeEnergy p.1 p.2.1 p.2.2) =
      (fun p => Real.log 2 + gaussianLogCoshAffine p.2.1 (p.1 * Real.sqrt p.2.2) +
        p.1 ^ 2 / 4 * (1 - p.2.2) ^ 2) by
    funext p
    exact rsFreeEnergy_eq_affine _ _ _]
  exact (continuous_const.add hlog).add hcorr

end Paper
