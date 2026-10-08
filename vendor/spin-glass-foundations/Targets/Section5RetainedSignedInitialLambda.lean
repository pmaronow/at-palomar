module

public import Targets.Section5SignedInitialLambda

@[expose] public section

/-!
# Signed initial lambda family retaining the frozen positive field

The negative shared Gaussian mean encloses the positive frozen Gaussian mean,
which encloses the independent prefix. The independent variance `v`, positive
shared variance `b`, and negative shared variance `c` are kept separate. Their
sum controls each marginal; their difference controls the cross-covariance.
No covariance-recombination or pressure-comparison identity is assumed here.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

noncomputable def section5RetainedInitialPrefix {k : ℕ} (s : RSBScheme k) (β b : ℝ) :=
  GTFrame.finiteStep (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt b)
    (fun _ => Real.sqrt b) (section5SignedInitialPrefix s β)

noncomputable def section5RetainedInitialPrefixD {k : ℕ} (s : RSBScheme k) (β b : ℝ) :=
  GTFrame.finiteStepD (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt b)
    (fun _ => Real.sqrt b) (section5SignedInitialPrefix s β) (section5SignedInitialPrefixD s β)

noncomputable def section5RetainedInitialPrefixDD {k : ℕ} (s : RSBScheme k) (β b : ℝ) :=
  GTFrame.finiteStepDD (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt b)
    (fun _ => Real.sqrt b) (section5SignedInitialPrefix s β)
    (section5SignedInitialPrefixD s β) (section5SignedInitialPrefixDD s β)

noncomputable def section5RetainedSignedInitialCascade {k : ℕ} (s : RSBScheme k) (β b c : ℝ) :=
  GTFrame.finiteStep (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt c)
    (fun _ => -Real.sqrt c) (section5RetainedInitialPrefix s β b)

noncomputable def section5RetainedSignedInitialCascadeD {k : ℕ} (s : RSBScheme k) (β b c : ℝ) :=
  GTFrame.finiteStepD (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt c)
    (fun _ => -Real.sqrt c) (section5RetainedInitialPrefix s β b) (section5RetainedInitialPrefixD s β b)

noncomputable def section5RetainedSignedInitialCascadeDD {k : ℕ} (s : RSBScheme k) (β b c : ℝ) :=
  GTFrame.finiteStepDD (gaussianReal 0 1) 0 (fun _ : ℝ => Real.sqrt c)
    (fun _ => -Real.sqrt c) (section5RetainedInitialPrefix s β b)
    (section5RetainedInitialPrefixD s β b) (section5RetainedInitialPrefixDD s β b)

/-- The actual scalar endpoint with both retained positive and new negative
shared fields. The negative field is averaged last (the outermost mean). -/
noncomputable def section5RetainedSignedInitialV {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (v b c ℓ : ℝ) : ℝ := section5RetainedSignedInitialCascade s β b c v ℓ (h,h)

/-- Both extra mass-zero Gaussian means preserve the unit lambda curvature. -/
theorem section5RetainedSignedInitial_unitCurvature {k : ℕ} (s : RSBScheme k) (β b c : ℝ) :
    UnitLambdaCurvature (section5RetainedSignedInitialCascade s β b c)
      (section5RetainedSignedInitialCascadeD s β b c)
      (section5RetainedSignedInitialCascadeDD s β b c) := by
  have H := splitScalarCascade_unitCurvature
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5Variance s β 1 (k + 2 - j))
    (fun j => ⟨section5Mass_nonneg s (by omega) le_rfl (by omega),
      section5Mass_le_one s (by norm_num) 1 (by omega) (by omega)⟩)
    (fun j => section5Variance_continuous s β 1 (k + 2 - j)) (k + 2) (k + 2)
  exact (H.finiteStep (GTFrame.expMoments_gaussianReal 0 1)
    (m := 0) (a := fun _ => Real.sqrt b) (b := fun _ => Real.sqrt b)
    ⟨le_rfl, by norm_num⟩ continuous_const continuous_const).finiteStep
    (GTFrame.expMoments_gaussianReal 0 1) (m := 0) ⟨le_rfl, by norm_num⟩
    continuous_const continuous_const

/-- Genuine differentiation in lambda before any covariance recombination. -/
theorem hasDerivAt_section5RetainedSignedInitialV {k : ℕ} (s : RSBScheme k)
    (β h v b c ℓ : ℝ) :
    HasDerivAt (section5RetainedSignedInitialV s β h v b c)
      (section5RetainedSignedInitialCascadeD s β b c v ℓ (h,h)) ℓ :=
  (section5RetainedSignedInitial_unitCurvature s β b c).triple.good.hasDeriv v ℓ (h,h)

/-- The zero-lambda derivative is the actual two-Gaussian signed product:
the negative field is outer and the positive frozen field is inner. -/
theorem hasDerivAt_section5RetainedSignedInitialV_zero {k : ℕ} (s : RSBScheme k)
    (β h v b c : ℝ) :
    HasDerivAt (section5RetainedSignedInitialV s β h v b c)
      (∫ z, ∫ z',
        stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v
          (h + Real.sqrt c * z + Real.sqrt b * z') *
        stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v
          (h - Real.sqrt c * z + Real.sqrt b * z')
        ∂gaussianReal 0 1 ∂gaussianReal 0 1) 0 := by
  simpa only [section5RetainedSignedInitialCascadeD, section5RetainedInitialPrefixD,
    GTFrame.finiteStepD, ↓reduceIte, GTFrame.step0, section5SignedInitialPrefixD_zero,
    neg_mul, ← sub_eq_add_neg] using
    hasDerivAt_section5RetainedSignedInitialV s β h v b c 0

private theorem positive_zero_mean_marginals {F : ℝ → ℝ → ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v b x y : ℝ)
    (hF : ∀ x y, F v 0 (x,y) = A x + A y) :
    GTFrame.finiteStep (gaussianReal 0 1) 0 (fun _ => Real.sqrt b) (fun _ => Real.sqrt b)
      F v 0 (x,y) = parisiStep 0 b A x + parisiStep 0 b A y := by
  simp only [GTFrame.finiteStep, ↓reduceIte, GTFrame.step0, hF]
  rw [integral_add (integrable_of_hasLinearGrowth hA hAm x b)
    (integrable_of_hasLinearGrowth hA hAm y b)]
  simp only [parisiStep, ↓reduceIte]

private theorem negative_zero_mean_marginals {F : ℝ → ℝ → ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (hcA : Continuous A) (v c x y : ℝ)
    (hF : ∀ x y, F v 0 (x,y) = A x + A y) :
    GTFrame.finiteStep (gaussianReal 0 1) 0 (fun _ => Real.sqrt c) (fun _ => -Real.sqrt c)
      F v 0 (x,y) = parisiStep 0 c A x + parisiStep 0 c A y := by
  have hneg : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have hi : Integrable (fun z => A (y + -Real.sqrt c * z)) (gaussianReal 0 1) := by
    simpa only [Function.comp_def, mul_neg, neg_mul] using
      hneg.integrable_comp_of_integrable (integrable_of_hasLinearGrowth hA hAm y c)
  simp only [GTFrame.finiteStep, ↓reduceIte, GTFrame.step0, hF]
  rw [integral_add (integrable_of_hasLinearGrowth hA hAm x c) hi,
    ← integral_reflect_stdGaussian hcA (Real.sqrt c) y]
  simp only [parisiStep, ↓reduceIte]

/-- At zero lambda the full retained-field family has the original scalar
value whenever its three nonnegative marginal variances sum to `β²q₁`. -/
theorem section5RetainedSignedInitialV_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {v b c : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hvar : v + b + c = β ^ 2 * s.q 1) :
    section5RetainedSignedInitialV s β h v b c 0 = 2 * parisiF s β (k + 2) h := by
  let A := parisiF s β (k + 1)
  let B := parisiStep 0 v A
  let C := parisiStep 0 b B
  have hA := parisiF_hasLinearGrowth s β (k + 1)
  have hAm := parisiF_measurable s β (k + 1)
  have hB := hasLinearGrowth_parisiStep hA hAm 0 v
  have hBm := measurable_parisiStep hAm 0 v
  have hC := hasLinearGrowth_parisiStep hB hBm 0 b
  have hCm := measurable_parisiStep hBm 0 b
  have heC : C = parisiStep 0 (b+v) A :=
    (parisiStep_add 0 b v hb hv hA hAm).symm
  have hcC : Continuous C := by
    rw [heC]
    exact ((continuous_parisiStep_variance_spatial (parisiF_C2_props s β (k + 1)).1
      (continuous_parisiFSecond s β (k + 1)) (m := 0) le_rfl).1).comp
      (show Continuous (fun x : ℝ => (b+v,x)) by fun_prop)
  have hF (x y : ℝ) : section5RetainedInitialPrefix s β b v 0 (x,y) = C x + C y :=
    positive_zero_mean_marginals hB hBm v b x y (section5SignedInitialPrefix_zero s β v)
  have H := negative_zero_mean_marginals hC hCm hcC v c h h hF
  change section5RetainedSignedInitialV s β h v b c 0 = _ at H
  rw [H]
  have he : parisiStep 0 c C h = parisiF s β (k + 2) h := by
    rw [heC, ← congrFun (parisiStep_add 0 c (b+v) hc (add_nonneg hb hv) hA hAm) h,
      show c+(b+v) = β ^ 2 * s.q 1 by linarith]
    simp only [show k + 2 = (k + 1) + 1 by omega, parisiF, Nat.sub_self,
      s.m_zero, s.q_zero, sub_zero, show k + 2 - (k + 1) = 1 by omega]
  rw [he]
  ring

/-- Actual second lambda derivatives remain between zero and one. -/
theorem section5RetainedSignedInitialV_second_derivative {k : ℕ} (s : RSBScheme k)
    (β h v b c ℓ : ℝ) :
    ∃ e : ℝ, HasDerivAt (deriv (section5RetainedSignedInitialV s β h v b c)) e ℓ ∧
      0 ≤ e ∧ e ≤ 1 := by
  have H := section5RetainedSignedInitial_unitCurvature s β b c
  have hd : deriv (section5RetainedSignedInitialV s β h v b c) =
      fun l => section5RetainedSignedInitialCascadeD s β b c v l (h,h) :=
    funext fun l => (hasDerivAt_section5RetainedSignedInitialV s β h v b c l).deriv
  rw [hd]
  exact ⟨_, H.triple.derivD v ℓ (h,h), H.triple.nonnegE v ℓ (h,h),
    (le_abs_self _).trans (H.triple.absE v ℓ (h,h))⟩

/-- The unchanged unit-curvature lambda square gain for the actual retained
positive/negative scalar family. -/
theorem section5RetainedSignedInitialV_lambda_gain {k : ℕ} (s : RSBScheme k)
    (β h v b c u : ℝ) :
    ∃ ℓ : ℝ, section5RetainedSignedInitialV s β h v b c ℓ - ℓ*u ≤
      section5RetainedSignedInitialV s β h v b c 0 -
        (deriv (section5RetainedSignedInitialV s β h v b c) 0 - u)^2/2 := by
  let f := section5RetainedSignedInitialV s β h v b c
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hasDerivAt_section5RetainedSignedInitialV s β h v b c x).differentiableAt.hasDerivAt
  have he (x : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    obtain ⟨e, he, _⟩ := section5RetainedSignedInitialV_second_derivative s β h v b c x
    exact he.differentiableAt.hasDerivAt
  have H := quadratic_upper_of_second_le_one hd he (fun x => by
    obtain ⟨e, he, _, hb⟩ := section5RetainedSignedInitialV_second_derivative s β h v b c x
    rwa [he.deriv]) (u - deriv f 0)
  refine ⟨u - deriv f 0, ?_⟩
  change f (u - deriv f 0) - (u - deriv f 0)*u ≤ f 0 - (deriv f 0-u)^2/2
  nlinarith

end SpinGlass.Targets
