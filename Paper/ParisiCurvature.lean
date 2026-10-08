module

public import Paper.ParisiSolution
public import Paper.ParisiFiniteSpatial

@[expose] public section

/-! # Actual curvature of the general-measure Parisi potential

The limiting Hessian is constructed from the genuine finite Gaussian
recursion. It is the classical spatial derivative of the actual gradient,
is jointly continuous and bounded, retains the coupled unit invariant, and
has a strictly positive quantitative lower bound on the entire time strip.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

noncomputable def parisiHessian (β : ℝ) (μ : ParisiMeasure) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => parisiGradient β μ (p.1, y)) p.2

theorem exists_parisiHessianBCF (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ∃ H : (ℝ × ℝ) →ᵇ ℝ,
      Tendsto (fun n => parisiFiniteHessianBCF (parisiGridRSBScheme μ n) β) atTop (𝓝 H) ∧
      ‖H‖ ≤ 1 ∧ (∀ t, LipschitzWith 14 (fun x => H (t, x))) ∧
      (∀ t x, HasDerivAt (fun y => parisiGradient β μ (t, y)) (H (t, x)) x) ∧
      (∀ p, H p + parisiGradient β μ p ^ 2 ≤ 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, Real.exp (-2 * parisiPotential β μ (t, x)) ≤ H (t, x) ∧
        0 < H (t, x) := by
  obtain ⟨H, hH, hb, hL, hd, hc⟩ := finiteParisiGradient_limit_derivative
    (fun n => n + 1) (parisiGridRSBScheme μ) β (tendsto_actual_finiteParisiGradient β hβ μ)
  refine ⟨H, hH, hb, hL, hd, hc, ?_⟩
  intro t ht x
  exact finiteParisiHessian_limit_pos (fun n => n + 1) (parisiGridRSBScheme μ) β hH (t, x)
    (tendsto_actual_finiteParisiPotential β hβ μ t x ht)

noncomputable def parisiHessianBCF (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    (ℝ × ℝ) →ᵇ ℝ := Classical.choose (exists_parisiHessianBCF β hβ μ)

theorem hasDerivAt_parisiGradient_spatial (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) : HasDerivAt (fun y => parisiGradient β μ (t, y))
      (parisiHessianBCF β hβ μ (t, x)) x :=
  (Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).2.2.2.1 t x

@[simp] theorem parisiHessianBCF_apply (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (p : ℝ × ℝ) : parisiHessianBCF β hβ μ p = parisiHessian β μ p :=
  (hasDerivAt_parisiGradient_spatial β hβ μ p.1 p.2).deriv.symm

theorem continuous_parisiHessian (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Continuous (parisiHessian β μ) := by
  have heq : (parisiHessianBCF β hβ μ : ℝ × ℝ → ℝ) = parisiHessian β μ :=
    funext (parisiHessianBCF_apply β hβ μ)
  rw [← heq]
  exact (parisiHessianBCF β hβ μ).continuous

theorem tendsto_actual_finiteParisiHessian (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Tendsto (fun n => parisiFiniteHessianBCF (parisiGridRSBScheme μ n) β) atTop
      (𝓝 (parisiHessianBCF β hβ μ)) :=
  (Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).1

theorem norm_parisiHessianBCF_le_one (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ‖parisiHessianBCF β hβ μ‖ ≤ 1 :=
  (Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).2.1

theorem lipschitzWith_parisiHessian (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (t : ℝ) :
    LipschitzWith 14 (fun x => parisiHessian β μ (t, x)) := by
  have h : LipschitzWith 14 (fun x => parisiHessianBCF β hβ μ (t, x)) :=
    (Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).2.2.1 t
  simpa only [parisiHessianBCF_apply] using h

theorem parisiHessian_add_gradient_sq_le_one (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiHessian β μ p + parisiGradient β μ p ^ 2 ≤ 1 := by
  have h : parisiHessianBCF β hβ μ p + parisiGradient β μ p ^ 2 ≤ 1 :=
    (Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).2.2.2.2.1 p
  simpa only [parisiHessianBCF_apply] using h

theorem parisiHessian_ge_exp_neg_two (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.exp (-2 * parisiPotential β μ (t, x)) ≤ parisiHessian β μ (t, x) := by
  have h : Real.exp (-2 * parisiPotential β μ (t, x)) ≤ parisiHessianBCF β hβ μ (t, x) :=
    ((Classical.choose_spec (exists_parisiHessianBCF β hβ μ)).2.2.2.2.2 t ht x).1
  simpa only [parisiHessianBCF_apply] using h

theorem parisiHessian_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < parisiHessian β μ (t, x) :=
  (Real.exp_pos _).trans_le (parisiHessian_ge_exp_neg_two β hβ μ t x ht)

theorem parisiHessian_le_one (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiHessian β μ p ≤ 1 := by
  have h := parisiHessian_add_gradient_sq_le_one β hβ μ p
  nlinarith [sq_nonneg (parisiGradient β μ p)]

theorem parisiGradientBCF_zero (μ : ParisiMeasure) (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiGradientBCF 0 μ p = Real.tanh p.2 := by
  have h := congrArg (fun v : ParisiSlabGradient 0 1 => v p) (parisiGradientBCF_fixedPoint 0 μ)
  change parisiSlabGradientValue 0 μ (by norm_num : (0 : ℝ) ≤ 1)
    Real.tanh (parisiGradientBCF 0 μ) p = _ at h
  simpa [parisiSlabGradientValue, parisiNormalizedGradientCorrection,
    heatSemigroup, gaussianExpectation] using h.symm

theorem parisiGradient_zero (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiGradient 0 μ p = Real.tanh p.2 :=
  parisiGradientBCF_zero μ _

theorem parisiHessian_zero (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiHessian 0 μ p = sech p.2 ^ 2 := by
  unfold parisiHessian
  simp_rw [parisiGradient_zero]
  exact (hasDerivAt_tanh p.2).deriv

theorem hasDerivAt_parisiGradient_spatial_all (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) : HasDerivAt (fun y => parisiGradient β μ (t, y))
      (parisiHessian β μ (t, x)) x := by
  by_cases hβ : β = 0
  · subst β
    simp_rw [parisiGradient_zero, parisiHessian_zero]
    exact hasDerivAt_tanh x
  · simpa only [parisiHessianBCF_apply] using hasDerivAt_parisiGradient_spatial β hβ μ t x

theorem continuous_parisiHessian_all (β : ℝ) (μ : ParisiMeasure) :
    Continuous (parisiHessian β μ) := by
  by_cases hβ : β = 0
  · subst β
    have heq : parisiHessian 0 μ = fun p : ℝ × ℝ => 1 - Real.tanh p.2 ^ 2 := by
      funext p
      rw [parisiHessian_zero]
      linarith [tanh_sq_add_sech_sq p.2]
    rw [heq]
    exact continuous_const.sub ((gaussian_continuous_tanh.comp continuous_snd).pow 2)
  · exact continuous_parisiHessian β hβ μ

theorem parisiHessian_pos_all (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < parisiHessian β μ (t, x) := by
  by_cases hβ : β = 0
  · subst β
    rw [parisiHessian_zero]
    exact pow_pos (sech_pos x) 2
  · exact parisiHessian_pos β hβ μ t x ht

theorem parisiHessian_add_gradient_sq_le_one_all (β : ℝ)
    (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiHessian β μ p + parisiGradient β μ p ^ 2 ≤ 1 := by
  by_cases hβ : β = 0
  · subst β
    rw [parisiGradient_zero, parisiHessian_zero]
    linarith [tanh_sq_add_sech_sq p.2]
  · exact parisiHessian_add_gradient_sq_le_one β hβ μ p

theorem parisiHessian_le_one_all (β : ℝ) (μ : ParisiMeasure) (p : ℝ × ℝ) :
    parisiHessian β μ p ≤ 1 := by
  have h := parisiHessian_add_gradient_sq_le_one_all β μ p
  nlinarith [sq_nonneg (parisiGradient β μ p)]

theorem norm_parisiHessian_le_one_all (β : ℝ) (μ : ParisiMeasure) (p : ℝ × ℝ) :
    ‖parisiHessian β μ p‖ ≤ 1 := by
  by_cases hβ : β = 0
  · subst β
    rw [parisiHessian_zero, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (sech p.2))]
    exact sech_sq_le_one p.2
  · rw [← parisiHessianBCF_apply β hβ μ p]
    exact ((parisiHessianBCF β hβ μ).norm_coe_le_norm p).trans
      (norm_parisiHessianBCF_le_one β hβ μ)

theorem lipschitzWith_parisiGradient_all (β : ℝ) (μ : ParisiMeasure) (t : ℝ) :
    LipschitzWith 1 (fun x => parisiGradient β μ (t, x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiGradient_spatial_all β μ t x).differentiableAt)
  intro x
  change ‖deriv (fun y => parisiGradient β μ (t, y)) x‖ ≤ (1 : ℝ)
  rw [(hasDerivAt_parisiGradient_spatial_all β μ t x).deriv]
  exact norm_parisiHessian_le_one_all β μ (t, x)

end Paper
