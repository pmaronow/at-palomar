module

public import Paper.ParisiTranslation
public import Paper.ParisiCurvature
public import Paper.ParisiWeightedVolterra

@[expose] public section

/-! # Spatial derivative representation for the actual Parisi solution

The only input to the auxiliary implicit-function statement below is
invertibility of the actual Gaussian Volterra linearization. Its forcing,
solution, continuity and translation covariance are all the actual objects.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff

namespace Paper

theorem parisiGradientBCF_apply (β : ℝ) (μ : ParisiMeasure)
    (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiGradientBCF β μ p = parisiGradient β μ (p.1, p.2) := by
  simp only [parisiGradient, parisiSlabExtend, projIcc_of_mem _ p.1.property]

theorem lipschitzWith_parisiGradientBCF_spatial (β : ℝ) (μ : ParisiMeasure)
    (t : Icc (0 : ℝ) 1) :
    LipschitzWith 1 (fun x => parisiGradientBCF β μ (t, x)) := by
  simpa only [parisiGradientBCF_apply] using lipschitzWith_parisiGradient_all β μ t

theorem parisiGradientBCF_quadratic_fixedPoint (β : ℝ) (μ : ParisiMeasure) :
    parisiGradientBCF β μ =
      parisiSlabTerminalHeatOperator β (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF +
      parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
        (parisiGradientBCF β μ) (parisiGradientBCF β μ) := by
  have h := parisiGradientBCF_fixedPoint β μ
  have heq : parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
      Real.tanh gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      (parisiGradientBCF β μ) =
      parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
        parisiLineTanhBCF parisiLineTanhBCF.continuous
        (fun x => by simpa only [parisiLineTanhBCF_apply, Real.norm_eq_abs]
          using (Real.abs_tanh_lt_one x).le) (parisiGradientBCF β μ) := by
    ext p
    rfl
  rw [heq, parisiSlabGradientOperator_eq_terminalHeat_add_quadratic,
    parisiSlabQuadraticOperator_eq_bilinear] at h
  exact h.symm

theorem contDiff_bcfTranslate_parisiGradient_of_invertible (β : ℝ) (μ : ParisiMeasure)
    (hinv : ∀ ξ, quadraticLinearizationIsInvertible
      (parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1))
      (bcfTranslate ξ (parisiGradientBCF β μ))) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (parisiGradientBCF β μ)) :=
  contDiff_bcfTranslate_quadratic_fixedPoint_of_invertible
    (parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1))
    (parisiSlabTerminalHeatOperator β (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF)
    (parisiGradientBCF β μ) (contDiff_bcfTranslate_parisiSlabTerminalTanh β _)
    (lipschitzWith_parisiGradientBCF_spatial β μ)
    (parisiGradientBCF_quadratic_fixedPoint β μ)
    (parisiSlabBilinearOperator_translate_diagonal β μ _ _) hinv

/-- C∞ spatial smoothness of the actual arbitrary-measure solution, in the
joint bounded-continuous-function norm on the full closed time strip. -/
theorem contDiff_bcfTranslate_parisiGradient (β : ℝ) (μ : ParisiMeasure) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (parisiGradientBCF β μ)) := by
  apply contDiff_bcfTranslate_parisiGradient_of_invertible β μ
  intro ξ
  apply parisiSlabBilinearOperator_global_residual_isInvertible
  simpa only [norm_bcfTranslate] using norm_parisiGradientBCF_le_one β μ

theorem contDiff_parisiGradient_spatial (β : ℝ) (μ : ParisiMeasure) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => parisiGradient β μ (t, x)) := by
  let p : Icc (0 : ℝ) 1 × ℝ := (projIcc (0 : ℝ) 1 (by norm_num) t, 0)
  have h := (BoundedContinuousFunction.evalCLM ℝ p).contDiff.comp
    (contDiff_bcfTranslate_parisiGradient β μ)
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    bcfTranslate_apply, p, zero_add, parisiGradient, parisiSlabExtend] using h

theorem parisiPotential_zero (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiPotential 0 μ p = Real.log (Real.cosh p.2) := by
  simp [parisiPotential, parisiContinuousPotential, parisiNormalizedDuhamelCorrection,
    heatSemigroup, gaussianExpectation]

theorem hasDerivAt_parisiPotential_spatial_all (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => parisiPotential β μ (t, y)) (parisiGradient β μ (t, x)) x := by
  by_cases hβ : β = 0
  · subst β
    simp_rw [parisiPotential_zero, parisiGradient_zero]
    exact hasDerivAt_log_cosh x
  · exact hasDerivAt_parisiPotential_spatial β hβ μ t x ht

theorem contDiff_parisiPotential_spatial (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x => parisiPotential β μ (t, x)) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_parisiPotential_spatial_all β μ t x ht).differentiableAt, ?_⟩
  rw [show deriv (fun x => parisiPotential β μ (t, x)) =
    (fun x => parisiGradient β μ (t, x)) from
      funext (fun x => (hasDerivAt_parisiPotential_spatial_all β μ t x ht).deriv)]
  exact contDiff_parisiGradient_spatial β μ t

theorem iteratedDeriv_parisiPotential_eq_gradient (β : ℝ) (μ : ParisiMeasure)
    (n : ℕ) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDeriv (n + 1) (fun y => parisiPotential β μ (t, y)) x =
      iteratedDeriv n (fun y => parisiGradient β μ (t, y)) x := by
  rw [iteratedDeriv_succ']
  congr 2
  funext y
  exact (hasDerivAt_parisiPotential_spatial_all β μ t y ht).deriv

theorem parisiSpatialDerivative_representation (β : ℝ) (μ : ParisiMeasure)
    (hsmooth : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (parisiGradientBCF β μ)))
    (n : ℕ) (p : Icc (0 : ℝ) 1 × ℝ) :
    bcfSpatialDerivative (parisiGradientBCF β μ) n p =
      iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2 := by
  rw [iteratedDeriv_parisiPotential_eq_gradient β μ n p.1 p.2 p.1.property,
    bcfSpatialDerivative_apply _ hsmooth]
  congr 2
  funext y
  exact parisiGradientBCF_apply β μ _

theorem parisiSpatialDerivatives_continuous_bounded_of_translate_smooth
    (β : ℝ) (μ : ParisiMeasure)
    (hsmooth : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (parisiGradientBCF β μ)))
    (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) 1 × ℝ =>
      iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2) ∧
    ∃ M : ℝ, ∀ p : Icc (0 : ℝ) 1 × ℝ,
      ‖iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2‖ ≤ M := by
  have heq : (bcfSpatialDerivative (parisiGradientBCF β μ) n :
      Icc (0 : ℝ) 1 × ℝ → ℝ) = fun p =>
      iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2 :=
    funext (parisiSpatialDerivative_representation β μ hsmooth n)
  constructor
  · rw [← heq]
    exact (bcfSpatialDerivative (parisiGradientBCF β μ) n).continuous
  · refine ⟨‖bcfSpatialDerivative (parisiGradientBCF β μ) n‖, fun p => ?_⟩
    rw [← parisiSpatialDerivative_representation β μ hsmooth n p]
    exact (bcfSpatialDerivative (parisiGradientBCF β μ) n).norm_coe_le_norm p

/-- Every positive-order spatial derivative of the genuine Parisi potential
is jointly continuous and globally bounded, including the two time endpoints. -/
theorem parisiSpatialDerivatives_continuous_bounded (β : ℝ) (μ : ParisiMeasure)
    (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) 1 × ℝ =>
      iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2) ∧
    ∃ M : ℝ, ∀ p : Icc (0 : ℝ) 1 × ℝ,
      ‖iteratedDeriv (n + 1) (fun y => parisiPotential β μ (p.1, y)) p.2‖ ≤ M :=
  parisiSpatialDerivatives_continuous_bounded_of_translate_smooth β μ
    (contDiff_bcfTranslate_parisiGradient β μ) n

end Paper
