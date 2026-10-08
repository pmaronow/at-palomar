module

public import Paper.DiracBrownianState
public import Paper.SoftMoment
public import Paper.ATCoordinates

@[expose] public section

/-! # The actual Brownian state second moment before the Dirac interface

The concrete Gaussian marginal law of the constructed strong state identifies
its expected squared soft PDE derivative with the proved Gaussian formula.
This yields the paper's quantitative left bound for an actual Brownian-driven
state, rather than an assumed random variable with a supplied law.
-/

open Set MeasureTheory ProbabilityTheory

namespace Paper

theorem continuous_rsSoftDx (β q t : ℝ) : Continuous (rsSoftDx β q t) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_rsSoftDx_spatial β q t x).continuousAt

set_option maxHeartbeats 1000000 in
theorem integrable_diracSoftMoment (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    Integrable (fun ω => rsSoftDx β q t (canonicalDiracStateReal β h q hq ω t) ^ 2)
      canonicalBrownianMeasure := by
  have hi : Integrable (fun x => rsSoftDx β q t x ^ 2)
      (gaussianReal h (β ^ 2 * t).toNNReal) := by
    apply (integrable_const (1 : ℝ) (μ := gaussianReal h (β ^ 2 * t).toNNReal)).mono'
      ((continuous_rsSoftDx β q t).pow 2).aestronglyMeasurable
    exact .of_forall (soft_dx_square_norm_le_one β q t)
  have hl := hasLaw_canonicalDiracState_before β h q hq ht
  exact hl.integrable_fun_comp (f := fun x => rsSoftDx β q t x ^ 2) hi

theorem diracSoftMoment_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hβ : 0 ≤ β)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    (∫ ω, rsSoftDx β q t (canonicalDiracStateReal β h q hq ω t) ^ 2
      ∂canonicalBrownianMeasure) = softSecondMoment β h q t := by
  have hf : Measurable (fun x => rsSoftDx β q t x ^ 2) :=
    ((continuous_rsSoftDx β q t).pow 2).measurable
  have he := (hasLaw_canonicalDiracState_before β h q hq ht).integral_comp
    hf.aestronglyMeasurable
  change (∫ ω, rsSoftDx β q t (canonicalDiracStateReal β h q hq ω t) ^ 2
    ∂canonicalBrownianMeasure) = ∫ x, rsSoftDx β q t x ^ 2
      ∂gaussianReal h (β ^ 2 * t).toNNReal at he
  rw [he, ← gaussianExpectation_shift_eq_integral h (β ^ 2 * t)
    (mul_nonneg (sq_nonneg β) ht.1) (fun x => rsSoftDx β q t x ^ 2) hf]
  unfold softSecondMoment
  congr 1
  ext z
  rw [gaussianField_eq_time β h t z hβ]

/-- **Proposition 4.1.** The quantitative left-hand bound for the genuine
constructed state and the spatial derivative of the explicit RS potential. -/
theorem diracSoftState_left_quantitative {β h q t : ℝ} (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) q)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    0 ≤ (1 - atParameter β h q) * (q - t) ∧
      (1 - atParameter β h q) * (q - t) ≤
        (∫ ω, (deriv (rsSoftPotential β q t)
          (canonicalDiracStateReal β h q hq ω t)) ^ 2 ∂canonicalBrownianMeasure) - t := by
  simp_rw [deriv_rsSoftPotential_spatial]
  rw [diracSoftMoment_eq β h q hq hβ.le ht]
  exact softSecondMoment_left_quantitative hβ.le ht hfixed hAT

end Paper
