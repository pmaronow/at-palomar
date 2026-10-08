module

public import Targets.Section5LambdaUPrime

@[expose] public section

/-!
# A signed initial Gaussian lambda family

The independent initial prefix is followed by one mass-zero Gaussian mean
with opposite field shifts. Its two marginals are unchanged; its lambda
derivative at zero is the signed product of the two smoothed scalar slopes.
The existing unit-curvature invariant gives the lambda square gain. These
scalar identities do not by themselves identify a signed pressure endpoint.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The initial independent prefix, including the inserted mass-zero step. -/
noncomputable def section5SignedInitialPrefix {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  splitScalarCascade (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5Variance s β 1 (k + 2 - j)) (k + 2) (k + 2)

noncomputable def section5SignedInitialPrefixD {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  splitScalarCascadeD (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5Variance s β 1 (k + 2 - j)) (k + 2) (k + 2)

noncomputable def section5SignedInitialPrefixDD {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  splitScalarCascadeDD (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5Variance s β 1 (k + 2 - j)) (k + 2) (k + 2)

/-- The full signed scalar family before evaluating its external fields. -/
noncomputable def section5SignedInitialCascade {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  GTFrame.finiteStep (gaussianReal 0 1) 0
    (fun v => Real.sqrt (β ^ 2 * s.q 1 - v))
    (fun v => -Real.sqrt (β ^ 2 * s.q 1 - v))
    (section5SignedInitialPrefix s β)

noncomputable def section5SignedInitialCascadeD {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  GTFrame.finiteStepD (gaussianReal 0 1) 0
    (fun v => Real.sqrt (β ^ 2 * s.q 1 - v))
    (fun v => -Real.sqrt (β ^ 2 * s.q 1 - v))
    (section5SignedInitialPrefix s β) (section5SignedInitialPrefixD s β)

noncomputable def section5SignedInitialCascadeDD {k : ℕ} (s : RSBScheme k) (β : ℝ) :=
  GTFrame.finiteStepDD (gaussianReal 0 1) 0
    (fun v => Real.sqrt (β ^ 2 * s.q 1 - v))
    (fun v => -Real.sqrt (β ^ 2 * s.q 1 - v))
    (section5SignedInitialPrefix s β) (section5SignedInitialPrefixD s β)
    (section5SignedInitialPrefixDD s β)

/-- The signed initial zero-time scalar lambda family. -/
noncomputable def section5SignedInitialV {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (v ℓ : ℝ) : ℝ := section5SignedInitialCascade s β v ℓ (h,h)

/-- Opposite field shifts preserve the same sharp lambda curvature invariant
as every other finite Gaussian step; there is no loss in depth. -/
theorem section5SignedInitial_unitCurvature {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    UnitLambdaCurvature (section5SignedInitialCascade s β)
      (section5SignedInitialCascadeD s β) (section5SignedInitialCascadeDD s β) := by
  have H := splitScalarCascade_unitCurvature
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5Variance s β 1 (k + 2 - j))
    (fun j => ⟨section5Mass_nonneg s (by omega) le_rfl (by omega),
      section5Mass_le_one s (by norm_num) 1 (by omega) (by omega)⟩)
    (fun j => section5Variance_continuous s β 1 (k + 2 - j)) (k + 2) (k + 2)
  exact H.finiteStep (GTFrame.expMoments_gaussianReal 0 1)
    (m := 0) ⟨le_rfl, by norm_num⟩ (by fun_prop) (by fun_prop)

/-- Genuine lambda differentiation of the signed family at every lambda. -/
theorem hasDerivAt_section5SignedInitialV {k : ℕ} (s : RSBScheme k) (β h v ℓ : ℝ) :
    HasDerivAt (section5SignedInitialV s β h v)
      (section5SignedInitialCascadeD s β v ℓ (h,h)) ℓ :=
  (section5SignedInitial_unitCurvature s β).triple.good.hasDeriv v ℓ (h,h)

/-- The independent prefix has the exact product of smoothed scalar slopes. -/
theorem section5SignedInitialPrefixD_zero {k : ℕ} (s : RSBScheme k)
    (β v x y : ℝ) : section5SignedInitialPrefixD s β v 0 (x,y) =
      stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v x *
        stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v y := by
  simpa only [section5SignedInitialPrefixD, show k + 3 - 1 = k + 2 by omega,
    show k + 2 - 1 = k + 1 by omega, show k + 1 + 1 = k + 2 by omega] using
    splitScalarCascadeD_inserted_zero s β (r := 1) (by omega) 0 v x y

/-- The zero-lambda signed factor is the actual opposite-field product. -/
theorem hasDerivAt_section5SignedInitialV_zero {k : ℕ} (s : RSBScheme k)
    (β h v : ℝ) :
    HasDerivAt (section5SignedInitialV s β h v)
      (∫ z, stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v
          (h + Real.sqrt (β ^ 2 * s.q 1 - v) * z) *
        stepD1 (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1)) 0 v
          (h - Real.sqrt (β ^ 2 * s.q 1 - v) * z) ∂gaussianReal 0 1) 0 := by
  have H := hasDerivAt_section5SignedInitialV s β h v 0
  simpa only [section5SignedInitialCascadeD, GTFrame.finiteStepD, ↓reduceIte,
    GTFrame.step0, section5SignedInitialPrefixD_zero, neg_mul, ← sub_eq_add_neg] using H

/-- The independent prefix at zero lambda is the sum of its scalar marginals. -/
theorem section5SignedInitialPrefix_zero {k : ℕ} (s : RSBScheme k) (β v x y : ℝ) :
    section5SignedInitialPrefix s β v 0 (x,y) =
      parisiStep 0 v (parisiF s β (k + 1)) x +
        parisiStep 0 v (parisiF s β (k + 1)) y := by
  rw [section5SignedInitialPrefix, (splitScalarCascade_independent_zero _ _ (k + 2) le_rfl v x y).1]
  have H := (section5_scalar_prefix s β 1 0 v (j := k + 1) (by omega)).1
  have he : k + 2 - (k + 1) = 1 := by omega
  have H' : scalarFieldCascade (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5Variance s β 1 (k + 2 - j) v) (k + 2) =
      parisiStep 0 v (parisiF s β (k + 1)) := by
    change parisiStep (section5Mass s 1 0 (k + 2 - (k + 1)))
      (section5Variance s β 1 (k + 2 - (k + 1)) v)
      (scalarFieldCascade _ _ (k + 1)) = _
    rw [H, he]
    simp only [section5Mass, section5Variance, lt_self_iff_false, if_false, if_true]
  rw [H']

/-- At zero lambda both scalar marginals remain the original Parisi scalar
value. The Gaussian sign changes correlation, not either marginal law. -/
theorem section5SignedInitialV_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1)) :
    section5SignedInitialV s β h v 0 = 2 * parisiF s β (k + 2) h := by
  let A := parisiF s β (k + 1)
  let B := parisiStep 0 v A
  let w := β ^ 2 * s.q 1 - v
  have hA := parisiF_hasLinearGrowth s β (k + 1)
  have hAm := parisiF_measurable s β (k + 1)
  have hB := hasLinearGrowth_parisiStep hA hAm 0 v
  have hBm := measurable_parisiStep hAm 0 v
  have hip := integrable_of_hasLinearGrowth hB hBm h w
  have hneg : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have hin : Integrable (fun z => B (h + -Real.sqrt w * z)) (gaussianReal 0 1) := by
    simpa only [Function.comp_def, mul_neg, neg_mul] using hneg.integrable_comp_of_integrable hip
  have hcB : Continuous B := by
    exact (((hasParisiC2_parisiStep_nonneg (m := 0) (v := v) le_rfl (by norm_num)
      (parisiF_C2_props s β (k + 1)).1 hA hAm
      (parisiF_C2_props s β (k + 1)).2.1 (parisiF_C2_props s β (k + 1)).2.2).1)
      |> fun H => continuous_iff_continuousAt.mpr (fun x => (H x).continuousAt))
  have he : (∫ z, B (h + -Real.sqrt w * z) ∂gaussianReal 0 1) =
      ∫ z, B (h + Real.sqrt w * z) ∂gaussianReal 0 1 :=
    (integral_reflect_stdGaussian hcB (Real.sqrt w) h).symm
  have hsemigroup := congrFun (parisiStep_add 0 w v (sub_nonneg.mpr hv.2) hv.1 hA hAm) h
  have hfull : parisiStep 0 (β ^ 2 * s.q 1) A h = parisiF s β (k + 2) h := by
    simp only [show k + 2 = (k + 1) + 1 by omega, parisiF, Nat.sub_self,
      s.m_zero, s.q_zero, sub_zero, show k + 2 - (k + 1) = 1 by omega]
    rfl
  unfold section5SignedInitialV section5SignedInitialCascade
  simp only [GTFrame.finiteStep, ↓reduceIte, GTFrame.step0, section5SignedInitialPrefix_zero]
  change (∫ z, B (h + Real.sqrt w * z) + B (h + -Real.sqrt w * z) ∂gaussianReal 0 1) = _
  rw [integral_add hip hin, he]
  have hp : (∫ z, B (h + Real.sqrt w * z) ∂gaussianReal 0 1) = parisiStep 0 w B h := by
    simp only [parisiStep, ↓reduceIte]
  rw [hp]
  have hs : parisiStep 0 w B h = parisiStep 0 (β ^ 2 * s.q 1) A h := by
    simpa only [w, sub_add_cancel] using hsemigroup.symm
  rw [hs, hfull]
  ring

/-- The actual signed family has second lambda derivative in `[0,1]`. -/
theorem section5SignedInitialV_second_derivative {k : ℕ} (s : RSBScheme k)
    (β h v ℓ : ℝ) :
    ∃ e : ℝ, HasDerivAt (deriv (section5SignedInitialV s β h v)) e ℓ ∧
      0 ≤ e ∧ e ≤ 1 := by
  have H := section5SignedInitial_unitCurvature s β
  have hd : deriv (section5SignedInitialV s β h v) =
      fun l => section5SignedInitialCascadeD s β v l (h,h) :=
    funext fun l => (hasDerivAt_section5SignedInitialV s β h v l).deriv
  rw [hd]
  exact ⟨_, H.triple.derivD v ℓ (h,h), H.triple.nonnegE v ℓ (h,h),
    (le_abs_self _).trans (H.triple.absE v ℓ (h,h))⟩

/-- The signed scalar family has the same explicit lambda square gain as
the unsigned families, with curvature constant one. -/
theorem section5SignedInitialV_lambda_gain {k : ℕ} (s : RSBScheme k)
    (β h v u : ℝ) :
    ∃ ℓ : ℝ, section5SignedInitialV s β h v ℓ - ℓ * u ≤
      section5SignedInitialV s β h v 0 -
        (deriv (section5SignedInitialV s β h v) 0 - u) ^ 2 / 2 := by
  let f := section5SignedInitialV s β h v
  have hfirst (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hasDerivAt_section5SignedInitialV s β h v x).differentiableAt.hasDerivAt
  have hsecond (x : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    obtain ⟨e, he, _⟩ := section5SignedInitialV_second_derivative s β h v x
    exact he.differentiableAt.hasDerivAt
  have H := quadratic_upper_of_second_le_one hfirst hsecond
    (fun x => by
      obtain ⟨e, he, _, hb⟩ := section5SignedInitialV_second_derivative s β h v x
      rwa [he.deriv]) (u - deriv f 0)
  refine ⟨u - deriv f 0, ?_⟩
  change f (u - deriv f 0) - (u - deriv f 0) * u ≤ f 0 - (deriv f 0 - u) ^ 2 / 2
  nlinarith

end SpinGlass.Targets
