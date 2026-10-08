module

public import Targets.ParisiJointMassContinuity

@[expose] public section

/-!
# Positive-variance differentiation of the actual scalar slope

The next input to Talagrand's (4.16) is the variance derivative of B'.
Differentiation of its normalized exponential moment needs only the already
proved C2 invariant, not an assumed third derivative. The formula below is
before the further Stein cancellation in (4.16). Mass zero is retained.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem slope_exponential_bounds {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (m : ℝ) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 ≤ c ∧
      (∀ y, |Real.exp (m * A y)| ≤ K * Real.exp (c * |y|)) ∧
      (∀ y, |m * A' y * Real.exp (m * A y)| ≤ K * Real.exp (c * |y|)) ∧
      (∀ y, |A' y * Real.exp (m * A y)| ≤ K * Real.exp (c * |y|)) ∧
      (∀ y, |(A'' y + m * (A' y) ^ 2) * Real.exp (m * A y)| ≤
        K * Real.exp (c * |y|)) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  let K := (1 + |m|) * Real.exp (|m| * C)
  let c := |m| * D
  have he (y : ℝ) : Real.exp (m * A y) ≤
      Real.exp (|m| * C) * Real.exp (c * |y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := le_abs_self (m * A y)
    rw [abs_mul] at hh
    dsimp only [c]
    nlinarith [mul_le_mul_of_nonneg_left (hb y) (abs_nonneg m)]
  have hcoef (y b : ℝ) (hb : |b| ≤ 1 + |m|) :
      |b * Real.exp (m * A y)| ≤ K * Real.exp (c * |y|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (1 + |m|) * (Real.exp (|m| * C) * Real.exp (c * |y|)) :=
        mul_le_mul hb (he y) (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [K]; ring
  refine ⟨K, c, by dsimp [K]; positivity, by dsimp [c]; positivity, ?_, ?_, ?_, ?_⟩
  · intro y
    simpa only [one_mul] using hcoef y 1 (by simp)
  · intro y
    apply hcoef
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hC2.abs_first_le_one y) (abs_nonneg m)]
  · intro y
    exact hcoef y (A' y) ((hC2.abs_first_le_one y).trans (by linarith [abs_nonneg m]))
  · intro y
    apply hcoef
    have hs : (A' y) ^ 2 ≤ 1 := by
      nlinarith [hC2.abs_first_le_one y, sq_abs (A' y), abs_nonneg (A' y)]
    have hh := abs_add_le (A'' y) (m * (A' y) ^ 2)
    simp only [abs_mul, abs_pow, sq_abs] at hh
    nlinarith [hC2.abs_second_le_one y,
      mul_le_mul_of_nonneg_left hs (abs_nonneg m)]

/-- The explicit variance velocity of the actual spatial slope. This quotient
has no singularity in mass. Only its variance-zero value is totalized. -/
noncomputable def stepD1Variance (A A' A'' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  (((∫ z, (A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) *
        Real.exp (m * A (x + Real.sqrt v * z)) * z ∂(gaussianReal 0 1)) * tiltE A m v x -
      tiltP A A' m v x *
        (∫ z, m * A' (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)) * z
          ∂(gaussianReal 0 1))) / (tiltE A m v x) ^ 2) * (1 / (2 * Real.sqrt v))

/-- Genuine positive-variance derivative of B', for arbitrary real mass,
including zero. Gaussian amplitude differentiation supplies all domination. -/
theorem hasDerivAt_stepD1_variance {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'') (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => stepD1 A A' m w x) (stepD1Variance A A' A'' m v x) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  obtain ⟨K, c, hK, hc, he, he', hp, hp'⟩ := slope_exponential_bounds hA hC2 m
  have hdE (y : ℝ) : HasDerivAt (fun y => Real.exp (m * A y))
      (m * A' y * Real.exp (m * A y)) y := by
    convert! ((hC2.1 y).const_mul m).exp using 1
    ring
  have hdP (y : ℝ) : HasDerivAt (fun y => A' y * Real.exp (m * A y))
      ((A'' y + m * (A' y) ^ 2) * Real.exp (m * A y)) y := by
    convert! (hC2.2.1 y).mul (hdE y) using 1
    ring
  have hE := hasDerivAt_integral_gaussian_amplitude hK hc hdE
    ((hcA'.measurable.const_mul m).mul ((hcA.measurable.const_mul m).exp)) he he' x (Real.sqrt v)
  have hP := hasDerivAt_integral_gaussian_amplitude hK hc hdP
    ((hA''m.add ((hcA'.measurable.pow_const 2).const_mul m)).mul
      ((hcA.measurable.const_mul m).exp)) hp hp' x (Real.sqrt v)
  have hEpos : (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) ≠ 0 :=
    (tiltE_pos hA hcA.measurable x).ne'
  simpa only [stepD1, tiltP, tiltE, stepD1Variance, Function.comp_def, Pi.div_apply] using!
    (hP.div hE hEpos).comp v (Real.hasDerivAt_sqrt hv.ne')

/-- A first Gaussian moment of an exponentially bounded continuous function
is jointly continuous in variance and field, including variance zero. -/
theorem continuous_gaussian_firstMoment_variance_spatial {f : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hfc : Continuous f)
    (hb : ∀ y, |f y| ≤ C * Real.exp (c * |y|)) :
    Continuous (fun p : ℝ × ℝ => ∫ z,
      f (p.2 + Real.sqrt p.1 * z) * z ∂(gaussianReal 0 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let X := |p.2| + 1
  let V := |p.1| + 1
  have hev : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.2| ≤ X ∧ q.1 ≤ V := by
    have hx : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.2| < X :=
      continuous_snd.abs.continuousAt.eventually (Iio_mem_nhds (by dsimp [X]; linarith))
    have hv : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.1 < V :=
      continuous_fst.continuousAt.eventually
        (Iio_mem_nhds (by dsimp [V]; linarith [le_abs_self p.1]))
    filter_upwards [hx, hv] with q hqx hqv
    exact ⟨hqx.le, hqv.le⟩
  apply continuousAt_of_dominated
    (bound := fun z : ℝ => (C * Real.exp (c * X)) *
      (|z| * Real.exp ((c * Real.sqrt V) * |z|)))
  · filter_upwards with q
    exact ((hfc.measurable.comp (measurable_tilt_shift _ _)).mul measurable_id).aestronglyMeasurable
  · filter_upwards [hev] with q hq
    filter_upwards with z
    have hy : |q.2 + Real.sqrt q.1 * z| ≤ X + Real.sqrt V * |z| := by
      have hh := abs_add_le q.2 (Real.sqrt q.1 * z)
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
      nlinarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq.2) (abs_nonneg z), hq.1]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (C * Real.exp (c * (X + Real.sqrt V * |z|))) * |z| := by
        apply mul_le_mul_of_nonneg_right ((hb _).trans ?_) (abs_nonneg z)
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hc)) hC
      _ = _ := by simp only [mul_add, Real.exp_add, mul_assoc]; ring
  · exact (integrable_abs_mul_exp_abs_stdGaussian (c * Real.sqrt V)).const_mul _
  · filter_upwards with z
    exact ((hfc.comp (by fun_prop : Continuous (fun q : ℝ × ℝ =>
      q.2 + Real.sqrt q.1 * z))).mul continuous_const).continuousAt

/-- Joint continuity of the explicit slope velocity on the positive-variance
domain. This justifies a genuine joint chain rule, not merely separate partials. -/
theorem continuousOn_stepD1Variance {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'') (m : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => stepD1Variance A A' A'' m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  obtain ⟨K, c, hK, hc, _, he', _, hp'⟩ := slope_exponential_bounds hA hC2 m
  have hE' := continuous_gaussian_firstMoment_variance_spatial hK hc
    ((hcA'.const_mul m).mul (Real.continuous_exp.comp (hcA.const_mul m))) he'
  have hP' := continuous_gaussian_firstMoment_variance_spatial hK hc
    ((hcA''.add ((hcA'.pow 2).const_mul m)).mul (Real.continuous_exp.comp (hcA.const_mul m))) hp'
  have hmap : Continuous (fun p : ℝ × ℝ => (m, p)) := by fun_prop
  have hE := (continuous_tiltE_mass_variance_spatial hA hcA).comp hmap
  have hP := (continuous_gaussian_weighted_exp_joint hA hcA hcA' hC2.abs_first_le_one).comp hmap
  have hnum := ((hP'.mul hE).sub (hP.mul hE')).continuousOn (s := Set.Ioi 0 ×ˢ Set.univ)
  have hquot := hnum.div (hE.pow 2).continuousOn (fun p _ =>
    pow_ne_zero 2 (tiltE_pos hA hcA.measurable p.2).ne')
  exact hquot.mul (continuousOn_const.div
    ((Real.continuous_sqrt.comp continuous_fst).const_mul 2).continuousOn
    (fun p hp => mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hp.1).ne'))

/-- Genuine joint variance/field differentiation of the scalar spatial slope.
The mass restriction only supplies continuity of the existing spatial Hessian. -/
theorem hasFDerivAt_stepD1_variance_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => stepD1 A A' m p.1 p.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (stepD1Variance A A' A'' m v x)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD2 A A' A'' m v x))) (v, x) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hn : Set.Ioi 0 ×ˢ Set.univ ∈ 𝓝 (v, x) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hv, Set.mem_univ x⟩
  have hdv : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x),
      HasFDerivAt (fun w => stepD1 A A' m w p.2)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD1Variance A A' A'' m p.1 p.2)) p.1 := by
    filter_upwards [hn] with p hp
    exact (hasDerivAt_stepD1_variance hA hC2 hcA''.measurable m p.2 hp.1).hasFDerivAt
  have hdx : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x),
      HasFDerivAt (stepD1 A A' m p.1)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD2 A A' A'' m p.1 p.2)) p.2 := by
    filter_upwards with p
    exact (hasDerivAt_parisiStep_spatial_second hA hcA.measurable hcA'.measurable
      hcA''.measurable hC2 m p.1 p.2).hasFDerivAt
  apply (hasStrictFDerivAt_uncurry_coprod (u := (v, x))
    (f := fun v x => stepD1 A A' m v x)
    (f₁ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight (stepD1Variance A A' A'' m v x))
    (f₂ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight (stepD2 A A' A'' m v x))
    hdv hdx ?_ ?_).hasFDerivAt
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp
      ((continuousOn_stepD1Variance hA hC2 hcA'' m (v, x) ⟨hv, Set.mem_univ x⟩).continuousAt hn)
  · exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp
      (continuous_parisiStep_variance_spatial hC2 hcA'' hm).2.2).continuousAt

/-- Chain rule for B' along the genuine moving inner field and variance. -/
theorem hasDerivAt_stepD1_variance_curve {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) {V X : ℝ → ℝ} {v' x' t : ℝ}
    (hV : HasDerivAt V v' t) (hX : HasDerivAt X x' t) (hv : 0 < V t) :
    HasDerivAt (fun a => stepD1 A A' m (V a) (X a))
      (v' * stepD1Variance A A' A'' m (V t) (X t) +
        x' * stepD2 A A' A'' m (V t) (X t)) t := by
  have H := (hasFDerivAt_stepD1_variance_spatial hA hC2 hcA'' hm hv (X t)).comp_hasDerivAt t
    (hV.prodMk hX)
  simpa only [Function.comp_def, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] using! H

/-- Actual Parisi-recursion inputs discharge every regularity hypothesis. -/
theorem hasDerivAt_stepD1_parisiF_variance {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => stepD1 (parisiF s β j) (parisiFDeriv s β j) m w x)
      (stepD1Variance (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v x) v :=
  hasDerivAt_stepD1_variance (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (parisiF_C2_props s β j).2.2 m x hv

private theorem tiltWeight_eq_exp_div (A : ℝ → ℝ) (m v x z : ℝ) :
    tiltWeight m v A x z = Real.exp (m * A (x + Real.sqrt v * z)) / tiltE A m v x := by
  by_cases hm : m = 0
  · simp [hm, tiltWeight, tiltE]
  · simp only [tiltWeight, if_neg hm, tiltE]

/-- The slope velocity as normalized Gaussian moments. This form is suitable
for the outer weighted differentiation in (4.16). -/
theorem stepD1Variance_eq_tilt {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m v x : ℝ) :
    stepD1Variance A A' A'' m v x =
      ((∫ z, ((A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) * z) *
          tiltWeight m v A x z ∂(gaussianReal 0 1)) -
        stepD1 A A' m v x *
          (∫ z, (m * A' (x + Real.sqrt v * z) * z) * tiltWeight m v A x z
            ∂(gaussianReal 0 1))) / (2 * Real.sqrt v) := by
  simp only [tiltWeight_eq_exp_div, ← mul_div_assoc, integral_div]
  rw [show (fun z => (A'' (x + Real.sqrt v * z) + m * A' (x + Real.sqrt v * z) ^ 2) * z *
      Real.exp (m * A (x + Real.sqrt v * z))) =
      (fun z => (A'' (x + Real.sqrt v * z) + m * A' (x + Real.sqrt v * z) ^ 2) *
        Real.exp (m * A (x + Real.sqrt v * z)) * z) by funext z; ring]
  rw [show (fun z => m * A' (x + Real.sqrt v * z) * z * Real.exp (m * A (x + Real.sqrt v * z))) =
      (fun z => m * A' (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)) * z) by
        funext z; ring]
  dsimp only [stepD1Variance, stepD1]
  field_simp [(tiltE_pos hA hAm x).ne']

private theorem scalar_C2_lipschitz {A A' A'' : ℝ → ℝ} (hC2 : HasParisiC2 A A' A'')
    (x y : ℝ) : |A x - A y| ≤ 1 * |x - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := A') (s := Set.univ) (C := 1)
    (fun z _ => (hC2.1 z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

private theorem abs_tilted_gaussian_linear_le {A f : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ 1 * |x - y|)
    {B : ℝ} (hB : 0 ≤ B) (hfm : Measurable f) (hfb : ∀ z, |f z| ≤ B * |z|)
    (m v x : ℝ) :
    |∫ z, f z * tiltWeight m v A x z ∂(gaussianReal 0 1)| ≤
      B * (Real.exp ((|m| * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (|m| * Real.sqrt v)) := by
  have hfi := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one
    hLip hA hAm x hfm hB (a := 0) (by simpa using hfb)
  have hzi := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one
    hLip hA hAm x measurable_id.abs zero_le_one (a := 0) (by simp)
  have hb (z : ℝ) : |f z * tiltWeight m v A x z| ≤ B * (|z| * tiltWeight m v A x z) := by
    rw [abs_mul, abs_of_nonneg (tiltWeight_nonneg hA hAm x z)]
    nlinarith [mul_le_mul_of_nonneg_right (hfb z) (tiltWeight_nonneg (m := m) (v := v) hA hAm x z)]
  calc
    _ ≤ ∫ z, |f z * tiltWeight m v A x z| ∂(gaussianReal 0 1) := abs_integral_le_integral_abs
    _ ≤ ∫ z, B * (|z| * tiltWeight m v A x z) ∂(gaussianReal 0 1) :=
      integral_mono hfi.abs (hzi.const_mul B) hb
    _ = B * ∫ z, |z| * tiltWeight m v A x z ∂(gaussianReal 0 1) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [mul_one] using
        (integral_abs_mul_tiltWeight_le (m := m) (v := v) zero_le_one hLip hA hAm x)) hB

/-- A field-independent bound for the genuine slope variance derivative.
It is finite on positive variance, and has no singularity at mass zero.
No variance-zero derivative or bound uniform as variance tends to zero is claimed. -/
theorem abs_stepD1Variance_le {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hA''m : Measurable A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    |stepD1Variance A A' A'' m v x| ≤
      (1 + 2 * m) * (Real.exp ((m * Real.sqrt v) * gAbsMoment) *
        gAbsExpMoment (m * Real.sqrt v)) / (2 * Real.sqrt v) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hLip := scalar_C2_lipschitz hC2
  let M := Real.exp ((m * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (m * Real.sqrt v)
  have hfirst : |∫ z, ((A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) * z) *
      tiltWeight m v A x z ∂(gaussianReal 0 1)| ≤ (1 + m) * M := by
    apply (abs_tilted_gaussian_linear_le hA hcA.measurable hLip (B := 1 + m) (by linarith [hm.1])
      (((hA''m.comp (measurable_tilt_shift v x)).add
        (((hcA'.measurable.comp (measurable_tilt_shift v x)).pow_const 2).const_mul m)).mul measurable_id)
      (fun z => ?_) m v x).trans_eq
        (by simp only [abs_of_nonneg hm.1, M])
    change |(A'' (x + Real.sqrt v * z) + m * A' (x + Real.sqrt v * z) ^ 2) * z| ≤ (1 + m) * |z|
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg z)
    have hh := abs_add_le (A'' (x + Real.sqrt v * z)) (m * (A' (x + Real.sqrt v * z)) ^ 2)
    simp only [abs_mul, abs_of_nonneg hm.1, abs_pow, sq_abs] at hh
    have hs : (A' (x + Real.sqrt v * z)) ^ 2 ≤ 1 := by
      nlinarith [hC2.abs_first_le_one (x + Real.sqrt v * z),
        sq_abs (A' (x + Real.sqrt v * z)), abs_nonneg (A' (x + Real.sqrt v * z))]
    nlinarith [hC2.abs_second_le_one (x + Real.sqrt v * z), mul_le_mul_of_nonneg_left hs hm.1]
  have hsecond : |∫ z, (m * A' (x + Real.sqrt v * z) * z) * tiltWeight m v A x z
      ∂(gaussianReal 0 1)| ≤ m * M := by
    apply (abs_tilted_gaussian_linear_le hA hcA.measurable hLip hm.1
      (((hcA'.measurable.comp (measurable_tilt_shift v x)).const_mul m).mul measurable_id)
      (fun z => ?_) m v x).trans_eq (by simp only [abs_of_nonneg hm.1, M])
    change |m * A' (x + Real.sqrt v * z) * z| ≤ m * |z|
    rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
    exact mul_le_mul_of_nonneg_right (by
      nlinarith [mul_le_mul_of_nonneg_left (hC2.abs_first_le_one (x + Real.sqrt v * z)) hm.1]) (abs_nonneg z)
  have hB := (hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hA''m).abs_first_le_one x
  rw [stepD1Variance_eq_tilt hA hcA.measurable m v x, abs_div,
    abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hv))]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  have hh := abs_sub
    (∫ z, ((A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) * z) *
      tiltWeight m v A x z ∂(gaussianReal 0 1))
    (stepD1 A A' m v x * (∫ z, (m * A' (x + Real.sqrt v * z) * z) *
      tiltWeight m v A x z ∂(gaussianReal 0 1)))
  rw [abs_mul] at hh
  have hp := mul_le_mul_of_nonneg_right hB (abs_nonneg
    (∫ z, (m * A' (x + Real.sqrt v * z) * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)))
  dsimp only [M] at hfirst hsecond
  nlinarith

/-- The quantitative bound supplies integrability at every outer Gaussian
field, with no restriction on that outer variance (including zero). -/
theorem integrable_stepD1Variance_gaussian {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x a : ℝ) :
    Integrable (fun z => stepD1Variance A A' A'' m v (x + Real.sqrt a * z)) (gaussianReal 0 1) := by
  have hc := (continuousOn_stepD1Variance hA hC2 hcA'' m).comp_continuous
    (by fun_prop : Continuous (fun z : ℝ => (v, x + Real.sqrt a * z)))
    (fun _ => ⟨hv, Set.mem_univ _⟩)
  apply (integrable_const ((1 + 2 * m) *
    (Real.exp ((m * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (m * Real.sqrt v)) /
      (2 * Real.sqrt v))).mono' hc.measurable.aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_eq_abs, Function.comp_def] using abs_stepD1Variance_le hA hC2 hcA''.measurable hm hv _

/-- B' along the actual moving outer field in the split recursion. -/
theorem hasDerivAt_stepD1_split_field {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) (a x z : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => stepD1 A A' m w (x + Real.sqrt (a - w) * z))
      (stepD1Variance A A' A'' m v (x + Real.sqrt (a - v) * z) -
        z / (2 * Real.sqrt (a - v)) * stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z)) v := by
  have hd := (((Real.hasDerivAt_sqrt (sub_pos.mpr hv.2).ne').comp v
    ((hasDerivAt_id v).const_sub a)).mul_const z).const_add x
  have H := hasDerivAt_stepD1_variance_curve hA hC2 hcA'' hm (hasDerivAt_id v) hd hv.1
  apply H.congr_deriv
  dsimp only [id_eq, Function.comp_apply]
  ring

/-- The actual squared-slope observable has a checked derivative before the
outer normalized averaging and Stein cancellation required for Q'. -/
theorem hasDerivAt_stepD1_parisiF_split_sq {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : 0 ≤ m) (a x z : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => (stepD1 (parisiF s β j) (parisiFDeriv s β j)
      m w (x + Real.sqrt (a - w) * z)) ^ 2)
      (2 * stepD1 (parisiF s β j) (parisiFDeriv s β j) m v (x + Real.sqrt (a - v) * z) *
        (stepD1Variance (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
            m v (x + Real.sqrt (a - v) * z) - z / (2 * Real.sqrt (a - v)) *
          stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
            m v (x + Real.sqrt (a - v) * z))) v := by
  have H := (hasDerivAt_stepD1_split_field (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (continuous_parisiFSecond s β j) hm a x z hv).pow 2
  simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_apply] using! H

/-- Actual joint slope chain rule; all regularity assumptions are discharged
by the existing recursive Parisi invariant and continuity theorem. -/
theorem hasDerivAt_stepD1_parisiF_variance_curve {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : 0 ≤ m) {V X : ℝ → ℝ} {v' x' t : ℝ}
    (hV : HasDerivAt V v' t) (hX : HasDerivAt X x' t) (hv : 0 < V t) :
    HasDerivAt (fun a => stepD1 (parisiF s β j) (parisiFDeriv s β j) m (V a) (X a))
      (v' * stepD1Variance (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m (V t) (X t) +
        x' * stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m (V t) (X t)) t :=
  hasDerivAt_stepD1_variance_curve (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm hV hX hv

/-- A common bound throughout an interior variance interval, uniform over all
admissible masses and every spatial field. For actual Parisi inputs it is also
independent of the number of recursion levels. -/
theorem abs_stepD1Variance_le_on_Icc {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hA''m : Measurable A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {lo hi v : ℝ} (hlo : 0 < lo)
    (hv : v ∈ Set.Icc lo hi) (x : ℝ) :
    |stepD1Variance A A' A'' m v x| ≤
      3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) /
        (2 * Real.sqrt lo) := by
  have hv0 : 0 < v := hlo.trans_le hv.1
  have hab : m * Real.sqrt v ≤ Real.sqrt hi := by
    have h1 := mul_le_mul_of_nonneg_right hm.2 (Real.sqrt_nonneg v)
    simpa only [one_mul] using h1.trans (by simpa only [one_mul] using Real.sqrt_le_sqrt hv.2)
  have hgnn (a : ℝ) : 0 ≤ gAbsExpMoment a :=
    integral_nonneg (fun z => mul_nonneg (abs_nonneg z) (Real.exp_pos _).le)
  have hg : gAbsExpMoment (m * Real.sqrt v) ≤ gAbsExpMoment (Real.sqrt hi) := by
    apply integral_mono (integrable_abs_mul_exp_abs_stdGaussian _) (integrable_abs_mul_exp_abs_stdGaussian _)
    intro z
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hab (abs_nonneg z))) (abs_nonneg z)
  have he : Real.exp ((m * Real.sqrt v) * gAbsMoment) ≤ Real.exp (Real.sqrt hi * gAbsMoment) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab gAbsMoment_nonneg)
  have hM : Real.exp ((m * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (m * Real.sqrt v) ≤
      Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi) :=
    mul_le_mul he hg (hgnn _) (Real.exp_pos _).le
  have hn := mul_le_mul (show 1 + 2 * m ≤ 3 by linarith [hm.2]) hM
    (mul_nonneg (Real.exp_pos _).le (hgnn _)) (by norm_num : (0 : ℝ) ≤ 3)
  calc
    _ ≤ (1 + 2 * m) * (Real.exp ((m * Real.sqrt v) * gAbsMoment) *
        gAbsExpMoment (m * Real.sqrt v)) / (2 * Real.sqrt v) :=
      abs_stepD1Variance_le hA hC2 hA''m hm hv0 x
    _ ≤ 3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) /
        (2 * Real.sqrt v) := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity [hgnn (Real.sqrt hi)])
      (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.1) (by norm_num))

end SpinGlass.Targets
