module

public import Paper.ParisiHJBFeedback
public import Paper.ParisiControlStability
public import Paper.ParisiMixGlobalDifferentiation

@[expose] public section

/-! # The actual one-sided optimal-control envelope

The proved optimal feedback and the actual control derivative admit a
uniform quadratic error. The resulting envelope has no supplied optimality,
control-convergence, or differentiability assumption.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

noncomputable def parisiOptimalControlMixDerivative (β h : ℝ) (μ ν : ParisiMeasure) : ℝ :=
  ∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
    (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure

noncomputable def parisiControlEnvelopeConstant (β : ℝ) : ℝ :=
  4 * β ^ 4 + (2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β

lemma parisiControlEnvelopeConstant_nonneg (β : ℝ) :
    0 ≤ parisiControlEnvelopeConstant β := by
  unfold parisiControlEnvelopeConstant
  have hc := parisiFeedbackMixConstant_nonneg β
  positivity

set_option maxHeartbeats 1000000 in
/-- A genuine quadratic remainder for the actual optimized PDE value. -/
theorem parisiPotential_mix_control_remainder (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) (epsilon : ℝ) (hepsilon : epsilon ∈ Icc (0 : ℝ) 1) :
    ‖parisiPotential β (parisiMix μ ν epsilon) (0, h) - parisiPotential β μ (0, h) -
      epsilon * parisiOptimalControlMixDerivative β h μ ν‖ ≤
      parisiControlEnvelopeConstant β * epsilon ^ 2 := by
  let A := selectedParisiFeedbackControl β h μ
  let C := selectedParisiFeedbackControl β h (parisiMix μ ν epsilon)
  have hA : IsParisiAdmissibleControl A := isParisiAdmissibleControl_selectedParisiFeedbackControl β h μ
  have hC : IsParisiAdmissibleControl C := isParisiAdmissibleControl_selectedParisiFeedbackControl β h (parisiMix μ ν epsilon)
  let J := fun control eta => parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) control eta
  let D := ∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1) C μ ν 0 sample ∂canonicalBrownianMeasure
  let Q := 4 * β ^ 4
  let L := (2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β
  have hoptA : J A μ = parisiPotential β μ (0, h) :=
    parisiControlObjective_feedback_eq_potential β h μ
  have hoptC : J C (parisiMix μ ν epsilon) = parisiPotential β (parisiMix μ ν epsilon) (0, h) :=
    parisiControlObjective_feedback_eq_potential β h (parisiMix μ ν epsilon)
  have hupperA : J A (parisiMix μ ν epsilon) ≤ parisiPotential β (parisiMix μ ν epsilon) (0, h) :=
    parisiControlObjective_le_potential β h hβ _ A hA
  have hupperC : J C μ ≤ parisiPotential β μ (0, h) :=
    parisiControlObjective_le_potential β h hβ _ C hC
  have hremA := parisiControlObjective_mix_remainder_le canonicalBrownianMeasure β h
    (canonicalBrownian 1) (measurable_canonicalBrownian 1) integrable_hjb_canonicalBrownian_one
    A hA.measurable hA.bounded μ ν epsilon hepsilon
  have hremC := parisiControlObjective_mix_remainder_le canonicalBrownianMeasure β h
    (canonicalBrownian 1) (measurable_canonicalBrownian 1) integrable_hjb_canonicalBrownian_one
    C hC.measurable hC.bounded μ ν epsilon hepsilon
  have hD := integral_parisiAffineControlDerivative_selected_mix_sub_le β h (canonicalBrownian 1)
    (measurable_canonicalBrownian 1) μ ν epsilon hepsilon 0 (by norm_num)
  have hboundA : -(Q * epsilon ^ 2) ≤ J A (parisiMix μ ν epsilon) - J A μ -
      epsilon * parisiOptimalControlMixDerivative β h μ ν := by
    exact (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs, J, Q, parisiOptimalControlMixDerivative, A] using hremA))
  have hboundC : J C (parisiMix μ ν epsilon) - J C μ - epsilon * D ≤ Q * epsilon ^ 2 := by
    exact le_of_abs_le (by simpa only [Real.norm_eq_abs, J, Q, D] using hremC)
  have hdiff : D - parisiOptimalControlMixDerivative β h μ ν ≤ L * epsilon := by
    rw [norm_sub_rev] at hD
    have hh := le_of_abs_le (by
      simpa only [Real.norm_eq_abs, D, L, parisiOptimalControlMixDerivative, C] using hD)
    exact hh
  have hL : 0 ≤ L := by
    dsimp only [L]
    have hc := parisiFeedbackMixConstant_nonneg β
    positivity
  have hlow : -(parisiControlEnvelopeConstant β * epsilon ^ 2) ≤
      parisiPotential β (parisiMix μ ν epsilon) (0, h) - parisiPotential β μ (0, h) -
        epsilon * parisiOptimalControlMixDerivative β h μ ν := by
    rw [hoptA] at hboundA
    have hnon : 0 ≤ L * epsilon ^ 2 := mul_nonneg hL (sq_nonneg epsilon)
    dsimp only [parisiControlEnvelopeConstant] at *
    dsimp only [Q, L] at hboundA hnon
    linarith
  have hhigh : parisiPotential β (parisiMix μ ν epsilon) (0, h) - parisiPotential β μ (0, h) -
      epsilon * parisiOptimalControlMixDerivative β h μ ν ≤ parisiControlEnvelopeConstant β * epsilon ^ 2 := by
    rw [hoptC] at hboundC
    have hmul := mul_le_mul_of_nonneg_left hdiff hepsilon.1
    dsimp only [parisiControlEnvelopeConstant, Q, L] at *
    nlinarith
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- A quadratic error at zero gives the genuine one-sided derivative,
including zero itself in the differentiability set. -/
lemma hasDerivWithinAt_Icc_zero_of_quadratic_remainder {f : ℝ → ℝ} {d K : ℝ}
    (hrem : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - f 0 - t * d‖ ≤ K * t ^ 2) :
    HasDerivWithinAt f d (Icc (0 : ℝ) 1) 0 := by
  rw [hasDerivWithinAt_iff_tendsto]
  simp only [sub_zero, smul_eq_mul]
  apply squeeze_zero' (g := fun t : ℝ => K * t)
    (.of_forall fun t => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hh := mul_le_mul_of_nonneg_left (hrem t ht) (inv_nonneg.mpr (norm_nonneg t))
    by_cases ht0 : t = 0
    · simp only [ht0, norm_zero, inv_zero, zero_mul, mul_zero]
      exact le_rfl
    · have he : ‖t‖⁻¹ * (K * t ^ 2) = K * t := by
        rw [Real.norm_of_nonneg ht.1]
        field_simp [ht0]
        <;> ring
      exact hh.trans_eq he
  · have hi : Tendsto (fun t : ℝ => t) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [mul_zero] using (tendsto_const_nhds (x := K)).mul hi

/-- The actual PDE value's derivative is the expected affine derivative of
its actual optimal feedback, without an envelope hypothesis. -/
theorem hasDerivWithinAt_parisiPotential_mix_control (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun epsilon => parisiPotential β (parisiMix μ ν epsilon) (0, h))
      (∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
        (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure)
      (Icc (0 : ℝ) 1) 0 := by
  apply hasDerivWithinAt_Icc_zero_of_quadratic_remainder
    (K := parisiControlEnvelopeConstant β)
  intro epsilon hepsilon
  simpa only [parisiMix_zero, parisiOptimalControlMixDerivative] using
    parisiPotential_mix_control_remainder β h hβ μ ν epsilon hepsilon

/-- The physical one-sided version on positive mixing parameters. -/
theorem hasDerivWithinAt_parisiPotential_mix_control_right (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun epsilon => parisiPotential β (parisiMix μ ν epsilon) (0, h))
      (∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
        (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure)
      (Ioi (0 : ℝ)) 0 :=
  hasDerivWithinAt_right_of_Icc (hasDerivWithinAt_parisiPotential_mix_control β h hβ μ ν)

/-- The independently proved Gaussian mild derivative equals the closed
expected optimal-control derivative. -/
theorem parisiPotential_mix_mildDerivative_eq_control (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) :
    parisiDuhamelCorrection β ν (parisiGradient β μ) 1 0 h -
      parisiDuhamelCorrection β μ (parisiGradient β μ) 1 0 h +
      2 * parisiSlabPotentialLinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1) 0 h (by norm_num)
        (parisiGradientBCF β μ * parisiGradientMixDerivative β μ ν) =
    ∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
      (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure := by
  exact UniqueDiffWithinAt.eq_deriv (Icc (0 : ℝ) 1)
    (uniqueDiffOn_Icc_zero_one 0 (by norm_num))
    (hasDerivWithinAt_parisiPotential_mix β μ ν 0 h (by norm_num))
    (hasDerivWithinAt_parisiPotential_mix_control β h hβ μ ν)

/-- The zero-parameter case is also identified directly. -/
theorem hasDerivWithinAt_parisiPotential_mix_control_all (β h : ℝ)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun epsilon => parisiPotential β (parisiMix μ ν epsilon) (0, h))
      (∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
        (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure)
      (Icc (0 : ℝ) 1) 0 := by
  by_cases hβ : β = 0
  · subst β
    have he : (∫ sample, parisiAffineControlDerivative 0 h (canonicalBrownian 1)
        (selectedParisiFeedbackControl 0 h μ) μ ν 0 sample ∂canonicalBrownianMeasure) = 0 := by
      simp [parisiAffineControlDerivative, parisiControlDrift, parisiControlCost]
    rw [he]
    have hf : (fun epsilon => parisiPotential 0 (parisiMix μ ν epsilon) (0, h)) =
        (fun _ : ℝ => Real.log (Real.cosh h)) := by
      funext epsilon
      exact parisiPotential_zero _ _
    rw [hf]
    exact (hasDerivAt_const 0 _).hasDerivWithinAt
  · exact hasDerivWithinAt_parisiPotential_mix_control β h hβ μ ν

theorem parisiPotential_mix_mildDerivative_eq_control_all (β h : ℝ)
    (μ ν : ParisiMeasure) :
    parisiDuhamelCorrection β ν (parisiGradient β μ) 1 0 h -
      parisiDuhamelCorrection β μ (parisiGradient β μ) 1 0 h +
      2 * parisiSlabPotentialLinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1) 0 h (by norm_num)
        (parisiGradientBCF β μ * parisiGradientMixDerivative β μ ν) =
    ∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
      (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure := by
  exact UniqueDiffWithinAt.eq_deriv (Icc (0 : ℝ) 1)
    (uniqueDiffOn_Icc_zero_one 0 (by norm_num))
    (hasDerivWithinAt_parisiPotential_mix β μ ν 0 h (by norm_num))
    (hasDerivWithinAt_parisiPotential_mix_control_all β h μ ν)

/-- The literal constructed PDE functional has the closed optimal-control
first derivative, before its expectation is rewritten using the gradient martingale. -/
theorem hasDerivWithinAt_parisiPDEFunctional_mix_control (β h : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun epsilon => parisiPDEFunctional β h (parisiMix μ ν epsilon))
      ((∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
          (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure) -
        β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
          ∫ s in (0 : ℝ)..1, s * parisiCDF μ s))
      (Icc (0 : ℝ) 1) 0 := by
  have hm := hasDerivWithinAt_parisiPDEFunctional_mix β h μ ν
  rw [parisiPotential_mix_mildDerivative_eq_control_all β h μ ν] at hm
  exact hm

theorem hasDerivWithinAt_parisiPDEFunctional_mix_control_right (β h : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun epsilon => parisiPDEFunctional β h (parisiMix μ ν epsilon))
      ((∫ sample, parisiAffineControlDerivative β h (canonicalBrownian 1)
          (selectedParisiFeedbackControl β h μ) μ ν 0 sample ∂canonicalBrownianMeasure) -
        β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
          ∫ s in (0 : ℝ)..1, s * parisiCDF μ s))
      (Ioi (0 : ℝ)) 0 :=
  hasDerivWithinAt_right_of_Icc (hasDerivWithinAt_parisiPDEFunctional_mix_control β h μ ν)

end Paper
