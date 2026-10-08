module

public import Targets.ParisiVarianceDerivative
public import Lemmas.GuerraTalagrand.Gaussian
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-!
# Section 4 variance calculus on actual Parisi inputs

The zero-mass spatial derivative adapter completes propagation of the existing
second-order Parisi invariant. Therefore the scalar heat equation applies to
every genuine input level, without an unproved smoothness hypothesis.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

theorem hasDerivAt_integral_gaussian_shift_bounded {A A' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hd : ∀ y, HasDerivAt A (A' y) y) (hb : ∀ y, |A' y| ≤ 1) (v x : ℝ) :
    HasDerivAt (fun y => ∫ z, A (y + Real.sqrt v * z) ∂(gaussianReal 0 1))
      (∫ z, A' (x + Real.sqrt v * z) ∂(gaussianReal 0 1)) x := by
  have hshift : HasLinearGrowth (fun y => A (x + y)) := by
    obtain ⟨C, D, hC, hD, hg⟩ := hA
    refine ⟨C + D * |x|, D, by positivity, hD, fun y => ?_⟩
    exact (hg (x + y)).trans (by nlinarith [abs_add_le x y])
  have H := hasDerivAt_integral_param
    (A := fun u y => A (u + y)) (A' := fun u y => A' (u + y))
    (v := v) (C' := 1) (D' := 0) 0 x (le_refl 0)
    (fun u y => by simpa only [Function.comp_def, mul_one, id_eq] using!
      (hd (u + y)).comp u ((hasDerivAt_id u).add_const y))
    (fun u => hmeas.comp (measurable_const_add u))
    (fun u => hmeas'.comp (measurable_const_add u))
    (fun u y => by simpa using hb (u + y)) hshift
  simpa only [zero_add] using! H

theorem hasDerivAt_parisiStep_spatial {A A' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hd : ∀ y, HasDerivAt A (A' y) y) (hb : ∀ y, |A' y| ≤ 1) (m v x : ℝ) :
    HasDerivAt (parisiStep m v A) (stepD1 A A' m v x) x := by
  change HasDerivAt (fun y => parisiStep m v A y) (stepD1 A A' m v x) x
  by_cases hm : m = 0
  · subst m
    simpa [parisiStep, stepD1, tiltP, tiltE] using!
      hasDerivAt_integral_gaussian_shift_bounded hA hmeas hmeas' hd hb v x
  · simpa only [parisiStep, if_neg hm] using!
      hasDerivAt_stepD1 (v := v) hm hd hb hA hmeas hmeas' x

theorem hasDerivAt_parisiStep_spatial_second {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') (hC2 : HasParisiC2 A A' A'') (m v x : ℝ) :
    HasDerivAt (stepD1 A A' m v) (stepD2 A A' A'' m v x) x := by
  change HasDerivAt (fun y => stepD1 A A' m v y) (stepD2 A A' A'' m v x) x
  by_cases hm : m = 0
  · subst m
    have hA' : HasLinearGrowth A' := ⟨1, 0, zero_le_one, le_refl 0,
      fun y => by simpa using hC2.abs_first_le_one y⟩
    simpa [stepD1, stepD2, tiltP, tiltQ, tiltE] using!
      hasDerivAt_integral_gaussian_shift_bounded hA' hmeas' hmeas'' hC2.2.1
        hC2.abs_second_le_one v x
  · exact hasDerivAt_stepD2 hm hC2.1 hC2.2.1 hC2.abs_first_le_one hC2.abs_second_le_one
      hA hmeas hmeas' hmeas'' x

theorem hasParisiC2_parisiStep_nonneg {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hC2 : HasParisiC2 A A' A'')
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') :
    HasParisiC2 (parisiStep m v A) (stepD1 A A' m v) (stepD2 A A' A'' m v) := by
  refine ⟨hasDerivAt_parisiStep_spatial hA hmeas hmeas' hC2.1 hC2.abs_first_le_one m v,
    hasDerivAt_parisiStep_spatial_second hA hmeas hmeas' hmeas'' hC2 m v, ?_, ?_⟩
  · exact smoothing_second_deriv_nonneg hm0 hC2.abs_first_le_one hC2.abs_second_le_one
      hC2.2.2.1 hA hmeas hmeas' hmeas''
  · exact smoothing_second_deriv_le hm0 hm1 hC2.abs_first_le_one hC2.abs_second_le_one
      hC2.2.2.2 hA hmeas hmeas' hmeas''

/-- The actual first spatial derivative, recursively exposed. -/
noncomputable def parisiFDeriv {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.sinh x / Real.cosh x
  | j + 1 => stepD1 (parisiF s β j) (parisiFDeriv s β j)
      (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))

/-- The actual second spatial derivative, recursively exposed. -/
noncomputable def parisiFSecond {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => 1 - (Real.sinh x / Real.cosh x) ^ 2
  | j + 1 => stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
      (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))

theorem parisiF_C2_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    HasParisiC2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) ∧
      Measurable (parisiFDeriv s β j) ∧ Measurable (parisiFSecond s β j) := by
  induction j with
  | zero =>
    refine ⟨hasParisiC2_log_cosh, ?_, ?_⟩
    · exact Real.measurable_sinh.div Real.measurable_cosh
    · exact measurable_const.sub ((Real.measurable_sinh.div Real.measurable_cosh).pow_const 2)
  | succ j ih =>
    refine ⟨hasParisiC2_parisiStep_nonneg (s.m_nonneg (by omega)) (s.m_le_one (by omega))
      ih.1 (parisiF_hasLinearGrowth s β j) (parisiF_measurable s β j) ih.2.1 ih.2.2,
      measurable_stepD1 (parisiF_measurable s β j) ih.2.1 _ _,
      measurable_stepD2 (parisiF_measurable s β j) ih.2.1 ih.2.2 _ _⟩

/-- Talagrand's (4.4) for a genuine scalar smoothing, in terms of actual derivatives. -/
theorem hasDerivAt_parisiStep_variance_pde {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hmeas : Measurable A) (hmeas' : Measurable A') (hmeas'' : Measurable A'')
    (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => parisiStep m w A x)
      ((deriv (deriv (parisiStep m v A)) x + m * (deriv (parisiStep m v A) x) ^ 2) / 2) v := by
  have hfirst : deriv (parisiStep m v A) = stepD1 A A' m v := by
    funext y
    exact (hasDerivAt_parisiStep_spatial hA hmeas hmeas' hC2.1 hC2.abs_first_le_one m v y).deriv
  rw [hfirst, (hasDerivAt_parisiStep_spatial_second hA hmeas hmeas' hmeas'' hC2 m v x).deriv]
  exact hasDerivAt_parisiStep_variance hA hC2 hmeas hmeas' hmeas'' m x hv

/-- No smoothness assumptions remain for the actual Parisi input at any depth. -/
theorem hasDerivAt_parisiStep_parisiF_variance {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => parisiStep m w (parisiF s β j) x)
      ((deriv (deriv (parisiStep m v (parisiF s β j))) x +
        m * (deriv (parisiStep m v (parisiF s β j)) x) ^ 2) / 2) v :=
  hasDerivAt_parisiStep_variance_pde (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_measurable s β j)
    (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2 m x hv

private theorem scalar_translation_goodTriple {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'') :
    GTFrame.GoodTriple (fun (_ : ℝ) l x => A (l + x.1))
      (fun (_ : ℝ) l x => A' (l + x.1)) (fun (_ : ℝ) l x => A'' (l + x.1)) 1 := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hC2.1 x).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun x => (hC2.2.1 x).continuousAt
  refine ⟨⟨hc.comp (by fun_prop), hc'.comp (by fun_prop), ?_, ?_,
    fun p l x => hC2.abs_first_le_one _⟩, hc''.comp (by fun_prop), ?_,
    fun p l x => hC2.2.2.1 _, fun p l x => (le_abs_self _).trans (hC2.abs_second_le_one _)⟩
  · intro p l x
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hC2.1 (l + x.1)).comp l ((hasDerivAt_id l).add_const x.1)
  · intro p l x y
    have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := A') (s := Set.univ) (C := 1)
      (fun t _ => (hC2.1 t).hasDerivWithinAt)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one t)
      convex_univ (Set.mem_univ (l + y.1)) (Set.mem_univ (l + x.1))
    have hh : |A (l + x.1) - A (l + y.1)| ≤ |x.1 - y.1| := by
      simpa only [Real.norm_eq_abs, one_mul, add_sub_add_left_eq_sub] using H
    exact hh.trans (le_add_of_nonneg_right (abs_nonneg _))
  · intro p l x
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hC2.2.1 (l + x.1)).comp l ((hasDerivAt_id l).add_const x.1)

/-- RSAT supplies joint continuity of the scalar step and its two spatial derivatives. -/
theorem continuous_parisiStep_variance_spatial {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'') {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun p : ℝ × ℝ => parisiStep m p.1 A p.2) ∧
      Continuous (fun p : ℝ × ℝ => stepD1 A A' m p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => stepD2 A A' A'' m p.1 p.2) := by
  have H := GTFrame.goodTriple_finiteStep (α := Real.sqrt) (β := fun _ : ℝ => 0)
    (GTFrame.expMoments_gaussianReal 0 1) (scalar_translation_goodTriple hC2 hc'') hm
    Real.continuous_sqrt continuous_const
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1, p.2, ((0 : ℝ), (0 : ℝ)))) := by fun_prop
  have h0 := H.good.contF.comp hmap
  have h1 := H.good.contD.comp hmap
  have h2 := H.contE.comp hmap
  by_cases hm0 : m = 0
  · subst m
    simpa [GTFrame.finiteStep, GTFrame.finiteStepD, GTFrame.finiteStepDD, GTFrame.step0,
      parisiStep, stepD1, stepD2, tiltE, tiltP, tiltQ, Function.comp_def] using! And.intro h0 (And.intro h1 h2)
  · simpa [GTFrame.finiteStep, GTFrame.finiteStepD, GTFrame.finiteStepDD, GTFrame.stepM,
      GTFrame.stepMD, GTFrame.stepMVar, parisiStep, stepD1, stepD2, tiltE, tiltP, tiltQ, tiltR,
      hm0, Function.comp_def] using! And.intro h0 (And.intro h1 h2)

/-- The actual second derivative at every Parisi level is continuous. -/
theorem continuous_parisiFSecond {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Continuous (parisiFSecond s β j) := by
  induction j with
  | zero =>
    exact continuous_const.sub (((Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')).pow 2))
  | succ j ih =>
    have H := (continuous_parisiStep_variance_spatial (parisiF_C2_props s β j).1 ih
      (s.m_nonneg (p := k + 1 - j) (by omega))).2.2
    exact H.comp (continuous_const.prodMk continuous_id)

/-- Joint differentiation in variance and spatial location. This is the chain-rule
input when the inner step is evaluated at the moving outer Gaussian field. -/
theorem hasFDerivAt_parisiStep_variance_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => parisiStep m p.1 A p.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight
        ((stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2) / 2)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD1 A A' m v x))) (v, x) := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hj := continuous_parisiStep_variance_spatial hC2 hc'' hm
  have hvn : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).eventually_mem hv
  have hdv : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x), HasFDerivAt (fun w => parisiStep m w A p.2)
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        ((stepD2 A A' A'' m p.1 p.2 + m * (stepD1 A A' m p.1 p.2) ^ 2) / 2)) p.1 := by
    filter_upwards [hvn] with p hp
    exact (hasDerivAt_parisiStep_variance hA hC2 hc.measurable hc'.measurable hc''.measurable
      m p.2 hp).hasFDerivAt
  have hdx : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x), HasFDerivAt (parisiStep m p.1 A)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD1 A A' m p.1 p.2)) p.2 := by
    filter_upwards with p
    exact (hasDerivAt_parisiStep_spatial hA hc.measurable hc'.measurable hC2.1
      hC2.abs_first_le_one m p.1 p.2).hasFDerivAt
  apply (hasStrictFDerivAt_uncurry_coprod (u := (v, x)) (f := fun v x => parisiStep m v A x)
    (f₁ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight
      ((stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2) / 2))
    (f₂ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight (stepD1 A A' m v x))
    hdv hdx ?_ ?_).hasFDerivAt
  · exact (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous).comp
      ((hj.2.2.add ((hj.2.1.pow 2).const_mul m)).div_const 2)).continuousAt
  · exact (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous).comp
      hj.2.1).continuousAt

theorem hasDerivAt_parisiStep_variance_curve {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) {V X : ℝ → ℝ} {v' x' t : ℝ}
    (hV : HasDerivAt V v' t) (hX : HasDerivAt X x' t) (hv : 0 < V t) :
    HasDerivAt (fun s => parisiStep m (V s) A (X s))
      (v' * ((stepD2 A A' A'' m (V t) (X t) +
        m * (stepD1 A A' m (V t) (X t)) ^ 2) / 2) +
        x' * stepD1 A A' m (V t) (X t)) t := by
  have H := (hasFDerivAt_parisiStep_variance_spatial hA hC2 hc'' hm hv (X t)).comp_hasDerivAt t
    (hV.prodMk hX)
  simpa only [Function.comp_def, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] using! H

/-- The moving-inner-field derivative needed before the outer averaging in (4.11). -/
theorem hasDerivAt_parisiStep_split_field {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) (a x z : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => parisiStep m w A (x + Real.sqrt (a - w) * z))
      (((stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z) +
          m * (stepD1 A A' m v (x + Real.sqrt (a - v) * z)) ^ 2) / 2) -
        z / (2 * Real.sqrt (a - v)) * stepD1 A A' m v (x + Real.sqrt (a - v) * z)) v := by
  have hd := (((Real.hasDerivAt_sqrt (sub_pos.mpr hv.2).ne').comp v
    ((hasDerivAt_id v).const_sub a)).mul_const z).const_add x
  have H := hasDerivAt_parisiStep_variance_curve hA hC2 hc'' hm (hasDerivAt_id v) hd hv.1
  apply H.congr_deriv
  dsimp only [id_eq, Function.comp_apply]
  ring

/-- The heat derivative is bounded uniformly in the input and its recursion depth. -/
theorem deriv_parisiStep_variance_mem_Icc {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hmeas : Measurable A) (hmeas' : Measurable A') (hmeas'' : Measurable A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    deriv (fun w => parisiStep m w A x) v ∈ Set.Icc 0 (1 / 2) := by
  rw [(hasDerivAt_parisiStep_variance hA hC2 hmeas hmeas' hmeas'' m x hv).deriv]
  have H := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hmeas hmeas' hmeas''
  have hp := H.2.2.1 x
  have hu := H.2.2.2 x
  constructor
  · nlinarith [mul_nonneg hm.1 (sq_nonneg (stepD1 A A' m v x))]
  · have hmul := mul_le_mul_of_nonneg_right hm.2 (sq_nonneg (stepD1 A A' m v x))
    nlinarith

theorem deriv_parisiStep_parisiF_variance_mem_Icc {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    deriv (fun w => parisiStep m w (parisiF s β j) x) v ∈ Set.Icc 0 (1 / 2) :=
  deriv_parisiStep_variance_mem_Icc (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2 hm x hv

end SpinGlass.Targets
