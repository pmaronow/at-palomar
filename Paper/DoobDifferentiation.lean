module

public import Paper.MomentBridge
public import Paper.GaussianHeat
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Derivatives of the concrete analytic hard moments

The post-`q` moment identity is proved from Gaussian heat differentiation and
cosh normalization, without an Itô formula or a diffusion-law hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ContDiff


namespace Paper

private theorem doobDiff_sech_pow_bound (n : ℕ) (y : ℝ) : ‖sech y ^ n‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le n)]
  exact pow_le_one₀ (sech_pos y).le (sech_le_one y)

private theorem doobDiff_tanh_sq_bound (y : ℝ) : ‖Real.tanh y ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact tanh_sq_le_one y

/-- The Gaussian representation of heat convolution, valid also at time zero. -/
theorem heatSemigroup_eq_gaussian_integral (ell : ℝ) (hell : 0 ≤ ell)
    (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    heatSemigroup ell f x = ∫ y, f y ∂gaussianReal x ell.toNNReal :=
  gaussianExpectation_shift_eq_integral x ell hell f hf

/-- The Gaussian Doob transform of `sech²` uses only heat convolution of `sech`.
The statement includes zero variance. -/
theorem doobOperator_sech_sq_eq_heatSemigroup (lam : ℝ≥0) (x : ℝ) :
    doobOperator lam (fun y => sech y ^ 2) x =
      Real.exp (-(lam : ℝ) / 2) / Real.cosh x * heatSemigroup (lam : ℝ) sech x := by
  have hpdf := heatSemigroup_eq_gaussian_integral (lam : ℝ) lam.coe_nonneg
    sech continuous_sech.measurable x
  have hnn : (lam : ℝ).toNNReal = lam := by simp
  rw [hnn] at hpdf
  rw [hpdf]
  unfold doobOperator
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  unfold sech
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp

/-- The heat representation of the fourth sech moment includes zero variance. -/
theorem doobOperator_sech_fourth_eq_heatSemigroup (lam : ℝ≥0) (x : ℝ) :
    doobOperator lam (fun y => sech y ^ 4) x =
      Real.exp (-(lam : ℝ) / 2) / Real.cosh x *
        heatSemigroup (lam : ℝ) (fun y => sech y ^ 3) x := by
  have hpdf := heatSemigroup_eq_gaussian_integral (lam : ℝ) lam.coe_nonneg
    (fun y => sech y ^ 3) (continuous_sech.pow 3).measurable x
  have hnn : (lam : ℝ).toNNReal = lam := by simp
  rw [hnn] at hpdf
  rw [hpdf]
  unfold doobOperator
  simp only [cosh_mul_sech_fourth]

/-- Normalization and the hyperbolic identity reduce the transformed second
moment to a bounded heat observable. -/
theorem doobOperator_tanh_sq_eq_heatSemigroup (lam : ℝ≥0) (x : ℝ) :
    doobOperator lam (fun y => Real.tanh y ^ 2) x =
      1 - Real.exp (-(lam : ℝ) / 2) / Real.cosh x * heatSemigroup (lam : ℝ) sech x := by
  have htanh := integrable_cosh_mul_gaussianReal x lam (fun y => Real.tanh y ^ 2)
    (gaussian_continuous_tanh.pow 2).measurable 1 doobDiff_tanh_sq_bound
  have hsech := integrable_cosh_mul_gaussianReal x lam (fun y => sech y ^ 2)
    (continuous_sech.pow 2).measurable 1 (doobDiff_sech_pow_bound 2)
  have hsum := doobOperator_add_of_integrable lam x (fun y => Real.tanh y ^ 2)
    (fun y => sech y ^ 2) htanh hsech
  have heq : (fun y : ℝ => Real.tanh y ^ 2 + sech y ^ 2) = (fun _ => 1) :=
    funext tanh_sq_add_sech_sq
  rw [heq, doobOperator_one, doobOperator_sech_sq_eq_heatSemigroup] at hsum
  linarith

/-- The actual second spatial derivative of `sech` is `sech-2sech³`. -/
theorem hasDerivAt_sech_derivative (x : ℝ) :
    HasDerivAt (fun y => -(Real.tanh y * sech y)) (sech x - 2 * sech x ^ 3) x := by
  convert ((hasDerivAt_tanh x).mul (hasDerivAt_sech x)).neg using 1
  have hi := congrArg (fun z : ℝ => z * sech x) (tanh_sq_add_sech_sq x)
  nlinarith

private theorem doobDiff_sech_second_bound (x : ℝ) :
    ‖sech x - 2 * sech x ^ 3‖ ≤ 3 := by
  calc
    _ ≤ ‖sech x‖ + ‖2 * sech x ^ 3‖ := norm_sub_le _ _
    _ ≤ 3 := by
      rw [norm_mul, Real.norm_of_nonneg (sech_pos x).le,
        Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 3)]
      norm_num
      nlinarith [sech_le_one x, pow_le_one₀ (sech_pos x).le (sech_le_one x) (n := 3)]

/-- The heat derivative of `sech`, including the precise cancellation term. -/
theorem hasDerivAt_heatSemigroup_sech (x : ℝ) {ell : ℝ} (hell : 0 < ell) :
    HasDerivAt (fun b => heatSemigroup b sech x)
      ((1 / 2 : ℝ) * (heatSemigroup ell sech x -
        2 * heatSemigroup ell (fun y => sech y ^ 3) x)) ell := by
  have hi : Integrable (fun z => sech (x + Real.sqrt ell * z)) (gaussianReal 0 1) := by
    simpa only [pow_one] using integrable_gaussian_sech_pow x (Real.sqrt ell) 1
  have hd := hasDerivAt_gaussian_variance sech (fun y => -(Real.tanh y * sech y))
    (fun y => sech y - 2 * sech y ^ 3) x ell 1 3 hell continuous_sech
    (gaussian_continuous_tanh.mul continuous_sech).neg
    (continuous_sech.sub (continuous_const.mul (continuous_sech.pow 3))) hi
    hasDerivAt_sech hasDerivAt_sech_derivative
    (fun y => by simpa only [norm_neg, pow_one] using norm_tanh_mul_sech_pow_le_one y 1)
    doobDiff_sech_second_bound
  have he : gaussianExpectation (fun z => sech (x + Real.sqrt ell * z) -
      2 * sech (x + Real.sqrt ell * z) ^ 3) =
      heatSemigroup ell sech x - 2 * heatSemigroup ell (fun y => sech y ^ 3) x := by
    unfold heatSemigroup gaussianExpectation
    rw [integral_sub hi ((integrable_gaussian_sech_pow x (Real.sqrt ell) 3).const_mul 2),
      integral_const_mul]
  rw [he] at hd
  exact hd

/-- The exact analytic moment identity for a single starting point. -/
theorem hasDerivAt_doobOperator_tanh_sq (x : ℝ) {ell : ℝ} (hell : 0 < ell) :
    HasDerivAt (fun b => doobOperator b.toNNReal (fun y => Real.tanh y ^ 2) x)
      (doobOperator ell.toNNReal (fun y => sech y ^ 4) x) ell := by
  have he : HasDerivAt (fun b : ℝ => Real.exp (-b / 2) / Real.cosh x)
      ((-1 / 2 : ℝ) * Real.exp (-ell / 2) / Real.cosh x) ell := by
    convert (((hasDerivAt_id ell).neg.div_const 2).exp).div_const (Real.cosh x) using 1
    · ext b
      simp only [Pi.neg_apply, id_eq]
    · simp only [Pi.neg_apply, id_eq]
      ring
  have hh := hasDerivAt_heatSemigroup_sech x hell
  have hprod := (he.mul hh).const_sub 1
  have heq : (fun b => doobOperator b.toNNReal (fun y => Real.tanh y ^ 2) x) =ᶠ[𝓝 ell]
      (fun b => 1 - Real.exp (-b / 2) / Real.cosh x * heatSemigroup b sech x) := by
    filter_upwards [eventually_gt_nhds hell] with b hb
    rw [doobOperator_tanh_sq_eq_heatSemigroup, Real.coe_toNNReal b hb.le]
  have hfourth := doobOperator_sech_fourth_eq_heatSemigroup ell.toNNReal x
  rw [Real.coe_toNNReal ell hell.le] at hfourth
  convert hprod.congr_of_eventuallyEq heq using 1
  rw [hfourth]
  ring

/-- Joint continuity of the bounded heat observables used by the Doob formulas. -/
theorem continuous_heatSemigroup_sech_pow_joint (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => heatSemigroup p.2 (fun y => sech y ^ n) p.1) :=
  continuous_gaussian_sech_pow_joint n

/-- The transformed fourth-sech moment is jointly continuous in starting point
and real time, including across zero after nonnegative truncation. -/
theorem continuous_doobOperator_sech_fourth_joint :
    Continuous (fun p : ℝ × ℝ => doobOperator p.2.toNNReal (fun y => sech y ^ 4) p.1) := by
  have ht : Continuous (fun p : ℝ × ℝ => (p.2.toNNReal : ℝ)) := by
    simpa only [Real.coe_toNNReal'] using continuous_snd.max continuous_const
  have he : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-(p.2.toNNReal : ℝ) / 2) / Real.cosh p.1) :=
    (Real.continuous_exp.comp (ht.neg.div_const 2)).div (Real.continuous_cosh.comp continuous_fst)
      (fun p => (Real.cosh_pos p.1).ne')
  have hh := (continuous_heatSemigroup_sech_pow_joint 3).comp
    (continuous_fst.prodMk ht)
  have heq : (fun p : ℝ × ℝ => doobOperator p.2.toNNReal (fun y => sech y ^ 4) p.1) =
      (fun p => Real.exp (-(p.2.toNNReal : ℝ) / 2) / Real.cosh p.1 *
        heatSemigroup (p.2.toNNReal : ℝ) (fun y => sech y ^ 3) p.1) :=
    funext (fun p => doobOperator_sech_fourth_eq_heatSemigroup p.2.toNNReal p.1)
  rw [heq]
  exact he.mul hh

/-- The transformed squared-tanh observable is jointly continuous in starting
point and real time, including zero. -/
theorem continuous_doobOperator_tanh_sq_joint :
    Continuous (fun p : ℝ × ℝ => doobOperator p.2.toNNReal (fun y => Real.tanh y ^ 2) p.1) := by
  have ht : Continuous (fun p : ℝ × ℝ => (p.2.toNNReal : ℝ)) := by
    simpa only [Real.coe_toNNReal'] using continuous_snd.max continuous_const
  have he : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-(p.2.toNNReal : ℝ) / 2) / Real.cosh p.1) :=
    (Real.continuous_exp.comp (ht.neg.div_const 2)).div (Real.continuous_cosh.comp continuous_fst)
      (fun p => (Real.cosh_pos p.1).ne')
  have hbase : Continuous (fun p : ℝ × ℝ => heatSemigroup p.2 sech p.1) := by
    simpa only [pow_one] using continuous_heatSemigroup_sech_pow_joint 1
  have hh := hbase.comp (continuous_fst.prodMk ht)
  have heq : (fun p : ℝ × ℝ => doobOperator p.2.toNNReal (fun y => Real.tanh y ^ 2) p.1) =
      (fun p => 1 - Real.exp (-(p.2.toNNReal : ℝ) / 2) / Real.cosh p.1 *
        heatSemigroup (p.2.toNNReal : ℝ) sech p.1) :=
    funext (fun p => doobOperator_tanh_sq_eq_heatSemigroup p.2.toNNReal p.1)
  rw [heq]
  exact continuous_const.sub (he.mul hh)

/-- Continuous Gaussian averaging of the actual second Doob moment. -/
theorem continuous_gaussianDoobSecondMoment_real (β h q : ℝ) :
    Continuous (fun ell : ℝ => gaussianDoobSecondMoment β h q ell.toNNReal) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro ell
    exact (measurable_doobOperator ell.toNNReal (fun y => Real.tanh y ^ 2)
      (gaussian_continuous_tanh.pow 2).measurable).aestronglyMeasurable
  · intro ell
    filter_upwards with x
    exact norm_doobOperator_le ell.toNNReal (fun y => Real.tanh y ^ 2)
      (gaussian_continuous_tanh.pow 2).measurable 1 doobDiff_tanh_sq_bound x
  · exact integrable_const 1
  · filter_upwards with x
    exact continuous_doobOperator_tanh_sq_joint.comp (continuous_const.prodMk continuous_id)

/-- Continuous Gaussian averaging of the actual fourth Doob moment. -/
theorem continuous_gaussianDoobFourthMoment_real (β h q : ℝ) :
    Continuous (fun ell : ℝ => gaussianDoobFourthMoment β h q ell.toNNReal) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro ell
    exact (measurable_doobOperator ell.toNNReal (fun y => sech y ^ 4)
      (continuous_sech.pow 4).measurable).aestronglyMeasurable
  · intro ell
    filter_upwards with x
    exact norm_doobOperator_le ell.toNNReal (fun y => sech y ^ 4)
      (continuous_sech.pow 4).measurable 1 (doobDiff_sech_pow_bound 4) x
  · exact integrable_const 1
  · filter_upwards with x
    exact continuous_doobOperator_sech_fourth_joint.comp (continuous_const.prodMk continuous_id)

/-- Dominated differentiation proves the actual Gaussian-averaged moment
identity, with its derivative bounded by one uniformly in the initial point. -/
theorem hasDerivAt_gaussianDoobSecondMoment (β h q : ℝ) {ell : ℝ} (hell : 0 < ell) :
    HasDerivAt (fun b : ℝ => gaussianDoobSecondMoment β h q b.toNNReal)
      (gaussianDoobFourthMoment β h q ell.toNNReal) ell := by
  let mu := gaussianReal h (β ^ 2 * q).toNNReal
  have : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  change HasDerivAt (fun b => ∫ x, doobOperator b.toNNReal (fun y => Real.tanh y ^ 2) x ∂mu)
    (∫ x, doobOperator ell.toNNReal (fun y => sech y ^ 4) x ∂mu) ell
  have hm : ∀ᶠ b in 𝓝 ell, AEStronglyMeasurable
      (fun x => doobOperator b.toNNReal (fun y => Real.tanh y ^ 2) x) mu :=
    .of_forall (fun b => (measurable_doobOperator b.toNNReal (fun y => Real.tanh y ^ 2)
      (gaussian_continuous_tanh.pow 2).measurable).aestronglyMeasurable)
  have hm' : AEStronglyMeasurable
      (fun x => doobOperator ell.toNNReal (fun y => sech y ^ 4) x) mu :=
    (measurable_doobOperator ell.toNNReal (fun y => sech y ^ 4)
      (continuous_sech.pow 4).measurable).aestronglyMeasurable
  have hb : ∀ᵐ x ∂mu, ∀ b ∈ (Ioi (0 : ℝ)),
      ‖doobOperator b.toNNReal (fun y => sech y ^ 4) x‖ ≤ 1 := by
    filter_upwards with x b _
    exact norm_doobOperator_le b.toNNReal (fun y => sech y ^ 4)
      (continuous_sech.pow 4).measurable 1 (doobDiff_sech_pow_bound 4) x
  have hd : ∀ᵐ x ∂mu, ∀ b ∈ (Ioi (0 : ℝ)),
      HasDerivAt (fun a => doobOperator a.toNNReal (fun y => Real.tanh y ^ 2) x)
        (doobOperator b.toNNReal (fun y => sech y ^ 4) x) b :=
    .of_forall (fun x b hb => hasDerivAt_doobOperator_tanh_sq x hb)
  have hi : Integrable
      (fun x => doobOperator ell.toNNReal (fun y => Real.tanh y ^ 2) x) mu :=
    integrable_gaussianDoobSecondMoment β h q ell.toNNReal
  have hbint : Integrable (fun _ : ℝ => (1 : ℝ)) mu := integrable_const 1
  have hout := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ) (α := ℝ) (x₀ := ell) (μ := mu) (F := fun b x => doobOperator b.toNNReal (fun y => Real.tanh y ^ 2) x)
    (F' := fun b x => doobOperator b.toNNReal (fun y => sech y ^ 4) x)
    (bound := fun _ => (1 : ℝ)) (s := Ioi (0 : ℝ)) (isOpen_Ioi.mem_nhds hell)
    hm hi hm' hb hbint hd
  simpa only [Function.comp_def] using hout.2

/-- The concrete analytic second moment is continuous at every real time. -/
theorem continuous_hardSecondMoment (β h q : ℝ) : Continuous (hardSecondMoment β h q) :=
  (continuous_gaussianDoobSecondMoment_real β h q).comp
    (continuous_const.mul (continuous_id.sub continuous_const))

/-- The concrete analytic fourth moment is continuous at every real time. -/
theorem continuous_hardFourthMoment (β h q : ℝ) : Continuous (hardFourthMoment β h q) :=
  (continuous_gaussianDoobFourthMoment_real β h q).comp
    (continuous_const.mul (continuous_id.sub continuous_const))

/-- The complete derivative identity for the actual post-`q` analytic hard
moment, with no Itô or regularity hypothesis. -/
theorem hasDerivAt_hardSecondMoment (β h q : ℝ) {t : ℝ} (ht : q < t) :
    HasDerivAt (hardSecondMoment β h q) (β ^ 2 * hardFourthMoment β h q t) t := by
  change HasDerivAt (fun s => gaussianDoobSecondMoment β h q (β ^ 2 * (s - q)).toNNReal)
    (β ^ 2 * gaussianDoobFourthMoment β h q (β ^ 2 * (t - q)).toNNReal) t
  by_cases hβ : β = 0
  · subst β
    simpa only [hardSecondMoment, hardFourthMoment, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul, Real.toNNReal_zero] using
      hasDerivAt_const t (gaussianDoobSecondMoment 0 h q 0)
  · have hell : 0 < β ^ 2 * (t - q) := mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr ht)
    have hinner : HasDerivAt (fun s : ℝ => β ^ 2 * (s - q)) (β ^ 2) t := by
      simpa using ((hasDerivAt_id t).sub_const q).const_mul (β ^ 2)
    simpa only [Function.comp_def, mul_comm] using
      (hasDerivAt_gaussianDoobSecondMoment β h q hell).comp t hinner

/-- The familiar derivative notation follows from the genuine derivative proof. -/
theorem deriv_hardSecondMoment (β h q : ℝ) {t : ℝ} (ht : q < t) :
    deriv (hardSecondMoment β h q) t = β ^ 2 * hardFourthMoment β h q t :=
  (hasDerivAt_hardSecondMoment β h q ht).deriv

/-- The concrete second moment has a continuous derivative throughout the
post-`q` interval. -/
theorem continuousOn_deriv_hardSecondMoment (β h q : ℝ) :
    ContinuousOn (deriv (hardSecondMoment β h q)) (Ioi q) := by
  apply ((continuous_hardFourthMoment β h q).const_mul (β ^ 2)).continuousOn.congr
  intro t ht
  exact deriv_hardSecondMoment β h q ht

/-- The concrete analytic hard second moment is `C¹` after `q`. -/
theorem contDiffOn_hardSecondMoment (β h q : ℝ) :
    ContDiffOn ℝ 1 (hardSecondMoment β h q) (Ioi q) := by
  change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) (hardSecondMoment β h q) (Ioi q)
  apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mpr
  refine ⟨?_, by simp, ?_⟩
  · intro t ht
    exact (hasDerivAt_hardSecondMoment β h q ht).differentiableAt.differentiableWithinAt
  · simpa only [contDiffOn_zero] using continuousOn_deriv_hardSecondMoment β h q

/-- The concrete post-`q` comparison is proved with no analytic regularity
or derivative-equation hypotheses. -/
theorem hardSecondMoment_le_time {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ t ∈ Icc q (1 : ℝ), hardSecondMoment β h q t ≤ t := by
  apply right_bound_of_doob_moment_inputs hβ hh hq hfixed hAT
    (continuous_hardSecondMoment β h q).continuousOn
  · intro t ht
    exact (hasDerivAt_hardSecondMoment β h q ht.1).differentiableAt.differentiableWithinAt
  · exact fun _ _ => rfl
  · intro t ht
    exact deriv_hardSecondMoment β h q ht.1

/-- The strict comparison in the small-mean regime holds for the actual
analytic moments, without Itô or regularity assumptions. -/
theorem hardSecondMoment_lt_time_of_small_field {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hfield : h ≤ β ^ 2 * q) :
    ∀ t ∈ Ioc q (1 : ℝ), hardSecondMoment β h q t < t := by
  apply right_strict_bound_of_doob_moment_inputs hβ hh hq hfixed hAT hfield
    (continuous_hardSecondMoment β h q).continuousOn
  · intro t ht
    exact (hasDerivAt_hardSecondMoment β h q ht.1).differentiableAt.differentiableWithinAt
  · exact fun _ _ => rfl
  · intro t ht
    exact deriv_hardSecondMoment β h q ht.1

end Paper
