module

public import Paper.ATCurve
public import Paper.GaussianCurveSigns
public import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! # Differentiability of the concrete AT zero curve -/

open Filter
open scoped Topology ContDiff

namespace Paper

noncomputable def atTimePartial (h t : ℝ) : ℝ :=
  2 * (gaussianB h t - gaussianT h t + h * gaussianV h t)

noncomputable def atFieldPartial (h t : ℝ) : ℝ :=
  -2 * gaussianU h t - 4 * t * gaussianV h t

theorem continuous_atTimePartial_joint :
    Continuous (fun p : ℝ × ℝ => atTimePartial p.1 p.2) := by
  unfold atTimePartial gaussianB
  exact continuous_const.mul (((continuous_gaussianA_joint.sub continuous_gaussianC_joint).sub
    continuous_gaussianT_joint).add (continuous_fst.mul continuous_gaussianV_joint))

theorem continuous_atFieldPartial_joint :
    Continuous (fun p : ℝ × ℝ => atFieldPartial p.1 p.2) := by
  unfold atFieldPartial
  exact (continuous_const.mul continuous_gaussianU_joint).sub
    ((continuous_const.mul continuous_snd).mul continuous_gaussianV_joint)

theorem scalarCLM_isInvertible (c : ℝ) (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  ext
  simp

theorem hasStrictFDerivAt_atZero_swap (t h : ℝ) (ht : 0 < t) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => atZeroFunction p.2 p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (atTimePartial h t)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (atFieldPartial h t))) (t, h) := by
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, h), 0 < p.1 :=
    (continuous_fst.continuousAt.tendsto).eventually (eventually_gt_nhds ht)
  apply hasStrictFDerivAt_uncurry_coprod
    (u := (t, h))
    (f := fun t h : ℝ => atZeroFunction h t)
    (f₁ := fun t h => ContinuousLinearMap.toSpanSingleton ℝ (atTimePartial h t))
    (f₂ := fun t h => ContinuousLinearMap.toSpanSingleton ℝ (atFieldPartial h t))
  · filter_upwards [hpos] with p hp
    exact (hasDerivAt_atZeroFunction_variance p.2 hp).hasFDerivAt
  · exact .of_forall fun p => (hasDerivAt_atZeroFunction_field p.2 p.1).hasFDerivAt
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
        ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp
      (continuous_atTimePartial_joint.comp (continuous_snd.prodMk continuous_fst))).continuousAt
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
        ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp
      (continuous_atFieldPartial_joint.comp (continuous_snd.prodMk continuous_fst))).continuousAt

theorem atFieldPartial_neg (h t : ℝ) (hh : 0 < h) (ht : 0 < t) :
    atFieldPartial h t < 0 :=
  at_field_derivative_neg t (gaussianU h t) (gaussianV h t) ht
    (gaussianU_pos h t hh ht) (gaussianV_pos h t hh ht)

/-- The local implicit function coincides near the base point with the
globally chosen root. Continuity of the root and its exact zero equation
are enough to identify the local functions. -/
theorem differentiableAt_atFieldRoot (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ atFieldRoot t := by
  have hstrict := hasStrictFDerivAt_atZero_swap t (atFieldRoot t) ht
  have hinv : (((ContinuousLinearMap.toSpanSingleton ℝ
        (atTimePartial (atFieldRoot t) t)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (atFieldPartial (atFieldRoot t) t))) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    simpa using scalarCLM_isInvertible (atFieldPartial (atFieldRoot t) t)
      (ne_of_lt (atFieldPartial_neg (atFieldRoot t) t (atFieldRoot_pos t ht) ht))
  let ψ := hstrict.implicitFunctionOfProdDomain hinv
  have hpair : Tendsto (fun s : ℝ => (s, atFieldRoot s)) (𝓝 t)
      (𝓝 (t, atFieldRoot t)) :=
    tendsto_id.prodMk_nhds (continuousAt_atFieldRoot t ht).tendsto
  have hevent := hpair.eventually (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv)
  have heq : atFieldRoot =ᶠ[𝓝 t] ψ := by
    filter_upwards [hevent, eventually_gt_nhds ht] with s hs hspos
    have hz : atZeroFunction (atFieldRoot s) s =
        atZeroFunction (atFieldRoot t) t := by rw [atFieldRoot_zero s hspos, atFieldRoot_zero t ht]
    exact (hs.mp hz).symm
  exact (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
    |>.congr_of_eventuallyEq heq

/-- The explicit derivative of the actual selected root. -/
theorem hasDerivAt_atFieldRoot (t : ℝ) (ht : 0 < t) :
    HasDerivAt atFieldRoot
      ((gaussianB (atFieldRoot t) t - gaussianT (atFieldRoot t) t +
        atFieldRoot t * gaussianV (atFieldRoot t) t) /
        (gaussianU (atFieldRoot t) t + 2 * t * gaussianV (atFieldRoot t) t)) t := by
  have hroot := (differentiableAt_atFieldRoot t ht).hasDerivAt
  have hpair := (hasDerivAt_id t).prodMk hroot
  have htotal := (hasStrictFDerivAt_atZero_swap t (atFieldRoot t) ht).hasFDerivAt
    |>.comp_hasDerivAt t hpair
  have heq : (fun s => atZeroFunction (atFieldRoot s) s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact atFieldRoot_zero s hs
  have hzero := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  have hid := htotal.unique hzero
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul] at hid
  have hden := at_slope_denominator_pos t (gaussianU (atFieldRoot t) t)
    (gaussianV (atFieldRoot t) t) ht
    (gaussianU_pos (atFieldRoot t) t (atFieldRoot_pos t ht) ht)
    (gaussianV_pos (atFieldRoot t) t (atFieldRoot_pos t ht) ht)
  have hd : deriv atFieldRoot t =
      (gaussianB (atFieldRoot t) t - gaussianT (atFieldRoot t) t +
        atFieldRoot t * gaussianV (atFieldRoot t) t) /
        (gaussianU (atFieldRoot t) t + 2 * t * gaussianV (atFieldRoot t) t) := by
    apply (eq_div_iff (ne_of_gt hden)).mpr
    unfold atTimePartial atFieldPartial at hid
    nlinarith
  rwa [hd] at hroot

theorem atFieldRoot_derivative_pos (t : ℝ) (ht : 0 < t) : 0 < deriv atFieldRoot t := by
  rw [(hasDerivAt_atFieldRoot t ht).deriv]
  exact at_curve_slope_pos (atFieldRoot t) t (gaussianB (atFieldRoot t) t)
    (gaussianT (atFieldRoot t) t) (gaussianU (atFieldRoot t) t) (gaussianV (atFieldRoot t) t)
    (atFieldRoot_pos t ht).le ht (by linarith [gaussianB_sub_gaussianT_pos (atFieldRoot t) t ht])
    (gaussianU_pos (atFieldRoot t) t (atFieldRoot_pos t ht) ht)
    (gaussianV_pos (atFieldRoot t) t (atFieldRoot_pos t ht) ht)

/-- Smoothness transfers from a proved smooth Gaussian zero function to the
already constructed unique root. This reusable lemma has a local regularity
hypothesis; the final graph theorem will discharge it with GaussianSmooth. -/
theorem contDiffAt_atFieldRoot_of_zeroFunction (t : ℝ) (ht : 0 < t)
    (hF : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => atZeroFunction p.2 p.1)
      (t, atFieldRoot t)) : ContDiffAt ℝ ∞ atFieldRoot t := by
  have hstrict := hasStrictFDerivAt_atZero_swap t (atFieldRoot t) ht
  have hinv : (fderiv ℝ (fun p : ℝ × ℝ => atZeroFunction p.2 p.1) (t, atFieldRoot t) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hstrict.hasFDerivAt.fderiv]
    simpa using scalarCLM_isInvertible (atFieldPartial (atFieldRoot t) t)
      (ne_of_lt (atFieldPartial_neg (atFieldRoot t) t (atFieldRoot_pos t ht) ht))
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ := hF.implicitFunction hn hinv
  have hpair : Tendsto (fun s : ℝ => (s, atFieldRoot s)) (𝓝 t)
      (𝓝 (t, atFieldRoot t)) :=
    tendsto_id.prodMk_nhds (continuousAt_atFieldRoot t ht).tendsto
  have hevent := hpair.eventually (hF.eventually_apply_eq_iff_implicitFunction hn hinv)
  have heq : atFieldRoot =ᶠ[𝓝 t] ψ := by
    filter_upwards [hevent, eventually_gt_nhds ht] with s hs hspos
    have hz : atZeroFunction (atFieldRoot s) s = atZeroFunction (atFieldRoot t) t := by
      rw [atFieldRoot_zero s hspos, atFieldRoot_zero t ht]
    exact (hs.mp hz).symm
  exact (hF.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq heq

theorem hasStrictFDerivAt_gaussianC_swap (t h : ℝ) (ht : 0 < t) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => gaussianC p.2 p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (2 * (h * gaussianV h t - gaussianT h t) / t)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (-4 * gaussianV h t))) (t, h) := by
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, h), 0 < p.1 :=
    (continuous_fst.continuousAt.tendsto).eventually (eventually_gt_nhds ht)
  apply hasStrictFDerivAt_uncurry_coprod
    (u := (t, h))
    (f := fun t h : ℝ => gaussianC h t)
    (f₁ := fun t h => ContinuousLinearMap.toSpanSingleton ℝ
      (2 * (h * gaussianV h t - gaussianT h t) / t))
    (f₂ := fun t h => ContinuousLinearMap.toSpanSingleton ℝ (-4 * gaussianV h t))
  · filter_upwards [hpos] with p hp
    exact (hasDerivAt_gaussianC_variance_stein p.2 hp).hasFDerivAt
  · exact .of_forall fun p => (hasDerivAt_gaussianC_field p.2 p.1).hasFDerivAt
  · have hV := continuous_gaussianV_joint.comp (continuous_snd.prodMk continuous_fst)
    have hT := continuous_gaussianT_joint.comp (continuous_snd.prodMk continuous_fst)
    have hc : ContinuousAt (fun p : ℝ × ℝ =>
        2 * (p.2 * gaussianV p.2 p.1 - gaussianT p.2 p.1) / p.1) (t, h) :=
      (continuous_const.mul ((continuous_snd.mul hV).sub hT)).continuousAt.div
        continuous_fst.continuousAt (ne_of_gt ht)
    exact ((ContinuousLinearMap.toSpanSingletonCLE :
      ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuousAt).comp
      (f := fun p : ℝ × ℝ => 2 * (p.2 * gaussianV p.2 p.1 - gaussianT p.2 p.1) / p.1) hc
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
        ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp
      (continuous_const.mul (continuous_gaussianV_joint.comp
        (continuous_snd.prodMk continuous_fst)))).continuousAt

noncomputable def atCOnCurve (t : ℝ) : ℝ := gaussianC (atFieldRoot t) t

theorem atCOnCurve_pos (t : ℝ) : 0 < atCOnCurve t := gaussianC_pos (atFieldRoot t) t

noncomputable def atCOnCurveSlope (t : ℝ) : ℝ :=
  2 * (atFieldRoot t * gaussianV (atFieldRoot t) t - gaussianT (atFieldRoot t) t) / t -
    4 * gaussianV (atFieldRoot t) t *
      (gaussianB (atFieldRoot t) t - gaussianT (atFieldRoot t) t +
        atFieldRoot t * gaussianV (atFieldRoot t) t) /
      (gaussianU (atFieldRoot t) t + 2 * t * gaussianV (atFieldRoot t) t)

theorem hasDerivAt_atCOnCurve (t : ℝ) (ht : 0 < t) :
    HasDerivAt atCOnCurve (atCOnCurveSlope t) t := by
  have hp := (hasDerivAt_id t).prodMk (hasDerivAt_atFieldRoot t ht)
  have hd := (hasStrictFDerivAt_gaussianC_swap t (atFieldRoot t) ht).hasFDerivAt
    |>.comp_hasDerivAt t hp
  convert hd using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, one_mul]
    unfold atCOnCurveSlope
    ring

theorem atCOnCurveSlope_neg (t : ℝ) (ht : 0 < t) : atCOnCurveSlope t < 0 :=
  gaussian_zero_curve_C_slope_neg (atFieldRoot t) t (atFieldRoot_pos t ht) ht
    (atFieldRoot_zero t ht)

theorem hasDerivAt_atBetaCurve (t : ℝ) (ht : 0 < t) :
    HasDerivAt atBetaCurve
      ((-atCOnCurveSlope t / atCOnCurve t ^ 2) / (2 * atBetaCurve t)) t := by
  have hC := atCOnCurve_pos t
  have hi := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_atCOnCurve t ht) (ne_of_gt hC)
  simp only [zero_mul, one_mul, zero_sub] at hi
  exact hi.sqrt (ne_of_gt (one_div_pos.mpr hC))

theorem atBetaCurve_derivative_pos (t : ℝ) (ht : 0 < t) : 0 < deriv atBetaCurve t := by
  rw [(hasDerivAt_atBetaCurve t ht).deriv]
  exact div_pos (div_pos (neg_pos.mpr (atCOnCurveSlope_neg t ht))
    (sq_pos_of_pos (atCOnCurve_pos t))) (mul_pos (by norm_num) (atBetaCurve_pos t))

theorem atBetaCurve_strictMonoOn : StrictMonoOn atBetaCurve (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro t ht
    rcases lt_or_eq_of_le (show 0 ≤ t from ht) with htpos | htzero
    · exact (hasDerivAt_atBetaCurve t htpos).continuousAt.continuousWithinAt
    · rw [← htzero]
      exact continuousAt_atBetaCurve_zero.continuousWithinAt
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact atBetaCurve_derivative_pos t ht

theorem atBetaCurve_bijOn : Set.BijOn atBetaCurve (Set.Ioi 0) (Set.Ioi 1) := by
  apply at_beta_bijOn atBetaCurve atBetaCurve_zero
  · intro t ht
    rcases lt_or_eq_of_le (show 0 ≤ t from ht) with htpos | htzero
    · exact (hasDerivAt_atBetaCurve t htpos).continuousAt.continuousWithinAt
    · rw [← htzero]
      exact continuousAt_atBetaCurve_zero.continuousWithinAt
  · exact atBetaCurve_strictMonoOn
  · exact fun t _ => (atBetaCurve_pos t).le
  · exact atBetaCurve_sq_gt_time

end Paper
