module

public import Paper.Structural
public import Paper.HeatContraction
public import Paper.Variational

@[expose] public section

/-!
# Analytic Doob moments and the conditional right-hand bound

The moments in this file are literal Gaussian integrals of the proven positive,
normalized Gaussian Doob operator. Their initial values, moment comparison,
and exponential decay are proved. Transition-law identification with the
paper's diffusion and the Itô derivative identity remain explicit hypotheses.
This file does not assert Proposition 5.1 or identify an SDE solution.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- The Gaussian average of the actual Doob transform of squared `tanh`. -/
def gaussianDoobSecondMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => Real.tanh y ^ 2) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal

/-- The Gaussian average of the actual Doob transform of fourth-power `sech`. -/
def gaussianDoobFourthMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => sech y ^ 4) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal

/-- The actual analytic second moment at time `t`, with time rescaling by `β²`.
The nonnegative-real truncation is inactive whenever `t ≥ q`. -/
def hardSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobSecondMoment β h q (β ^ 2 * (t - q)).toNNReal

/-- The actual analytic fourth-sech moment at time `t`. -/
def hardFourthMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobFourthMoment β h q (β ^ 2 * (t - q)).toNNReal

private lemma bridge_tanh_continuous : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)

private lemma bridge_tanh_sq_bound (y : ℝ) : ‖Real.tanh y ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact tanh_sq_le_one y

private lemma bridge_sech_pow_bound (n : ℕ) (y : ℝ) : ‖sech y ^ n‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le n)]
  exact pow_le_one₀ (sech_pos y).le (sech_le_one y)

/-- Bounded measurable Doob tests remain integrable under every Gaussian
initial law, so none of the analytic moment integrals is a junk integral. -/
lemma integrable_gaussian_doob_bounded (h : ℝ) (v lam : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (hbound : ∀ y, ‖ψ y‖ ≤ 1) :
    Integrable (doobOperator lam ψ) (gaussianReal h v) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (measurable_doobOperator lam ψ hψ).aestronglyMeasurable
  · filter_upwards [] with x
    exact norm_doobOperator_le lam ψ hψ 1 hbound x

theorem integrable_gaussianDoobSecondMoment (β h q : ℝ) (lam : ℝ≥0) :
    Integrable (doobOperator lam (fun y => Real.tanh y ^ 2))
      (gaussianReal h (β ^ 2 * q).toNNReal) :=
  integrable_gaussian_doob_bounded h _ lam _ (bridge_tanh_continuous.pow 2).measurable
    bridge_tanh_sq_bound

theorem integrable_gaussianDoobFourthMoment (β h q : ℝ) (lam : ℝ≥0) :
    Integrable (doobOperator lam (fun y => sech y ^ 4))
      (gaussianReal h (β ^ 2 * q).toNNReal) :=
  integrable_gaussian_doob_bounded h _ lam _ (continuous_sech.pow 4).measurable
    (bridge_sech_pow_bound 4)

/-- The initial second moment is the paper's literal fixed-point map. -/
theorem gaussianDoobSecondMoment_initial {β h q : ℝ} (hq : 0 ≤ q) :
    gaussianDoobSecondMoment β h q 0 = overlapMap β h q := by
  simp only [gaussianDoobSecondMoment, doobOperator_zero]
  exact (overlapMap_eq_gaussian hq).symm

@[simp] theorem hardSecondMoment_initial {β h q : ℝ} (hq : 0 ≤ q) :
    hardSecondMoment β h q q = overlapMap β h q := by
  simp only [hardSecondMoment, sub_self, mul_zero, Real.toNNReal_zero]
  exact gaussianDoobSecondMoment_initial hq

/-- The actual initial Doob second moment equals the chosen fixed point. -/
theorem hardSecondMoment_initial_fixed {β h q : ℝ} (hq : 0 ≤ q)
    (hfixed : q = overlapMap β h q) : hardSecondMoment β h q q = q := by
  rw [hardSecondMoment_initial hq, ← hfixed]

/-- The AT parameter is the actual Gaussian fourth-sech integral, scaled by `β²`. -/
theorem atParameter_eq_gaussian {β h q : ℝ} (hq : 0 ≤ q) :
    atParameter β h q = β ^ 2 *
      (∫ x, sech x ^ 4 ∂gaussianReal h (β ^ 2 * q).toNNReal) := by
  unfold atParameter gaussianExpectation
  congr 1
  rw [← gaussianField_law hq]
  exact (integral_map (by unfold gaussianField; fun_prop)
    (continuous_sech.pow 4).aestronglyMeasurable).symm

/-- Initial fourth moment, with no unnecessary division by `β²`. -/
theorem gaussianDoobFourthMoment_initial {β h q : ℝ} (hq : 0 ≤ q) :
    β ^ 2 * gaussianDoobFourthMoment β h q 0 = atParameter β h q := by
  simp only [gaussianDoobFourthMoment, doobOperator_zero]
  exact (atParameter_eq_gaussian hq).symm

@[simp] theorem hardFourthMoment_initial {β h q : ℝ} (hq : 0 ≤ q) :
    β ^ 2 * hardFourthMoment β h q q = atParameter β h q := by
  simp only [hardFourthMoment, sub_self, mul_zero, Real.toNNReal_zero]
  exact gaussianDoobFourthMoment_initial hq

/-- The division form appearing in the paper is valid when `β ≠ 0`. -/
theorem gaussian_fourth_moment_eq_atParameter_div {β h q : ℝ}
    (hβ : β ≠ 0) (hq : 0 ≤ q) :
    (∫ x, sech x ^ 4 ∂gaussianReal h (β ^ 2 * q).toNNReal) = atParameter β h q / β ^ 2 := by
  rw [atParameter_eq_gaussian hq]
  field_simp

/-- Positivity of the operator yields positivity of the fourth moment. -/
theorem gaussianDoobFourthMoment_nonneg (β h q : ℝ) (lam : ℝ≥0) :
    0 ≤ gaussianDoobFourthMoment β h q lam := by
  exact integral_nonneg (fun x => doobOperator_nonneg lam _
    (fun y => (pow_nonneg (sech_pos y).le 4)) x)

theorem gaussianDoobSecondMoment_nonneg (β h q : ℝ) (lam : ℝ≥0) :
    0 ≤ gaussianDoobSecondMoment β h q lam := by
  exact integral_nonneg (fun x => doobOperator_nonneg lam _ (fun y => sq_nonneg _) x)

/-- The actual second moment retains its probabilistic range `[0,1]`. -/
theorem gaussianDoobSecondMoment_le_one (β h q : ℝ) (lam : ℝ≥0) :
    gaussianDoobSecondMoment β h q lam ≤ 1 := by
  have hh := integral_mono (integrable_gaussianDoobSecondMoment β h q lam)
    (integrable_const (1 : ℝ)) (fun x => by
      have hnorm := norm_doobOperator_le lam (fun y => Real.tanh y ^ 2)
        (bridge_tanh_continuous.pow 2).measurable 1 bridge_tanh_sq_bound x
      rw [Real.norm_eq_abs] at hnorm
      exact (abs_le.mp hnorm).2)
  simpa [gaussianDoobSecondMoment] using hh

/-- The pointwise moment comparison follows from positivity, normalization,
and `sech⁴ ≤ sech² = 1-tanh²`. -/
theorem doob_fourth_le_one_sub_second (lam : ℝ≥0) (x : ℝ) :
    doobOperator lam (fun y => sech y ^ 4) x ≤
      1 - doobOperator lam (fun y => Real.tanh y ^ 2) x := by
  have htanh : Integrable (fun y => Real.cosh y * Real.tanh y ^ 2) (gaussianReal x lam) :=
    integrable_cosh_mul_gaussianReal x lam _
      (bridge_tanh_continuous.pow 2).measurable 1 bridge_tanh_sq_bound
  have hsech2 : Integrable (fun y => Real.cosh y * sech y ^ 2) (gaussianReal x lam) :=
    integrable_cosh_mul_gaussianReal x lam _
      (continuous_sech.pow 2).measurable 1 (bridge_sech_pow_bound 2)
  have hsech4 : Integrable (fun y => Real.cosh y * sech y ^ 4) (gaussianReal x lam) :=
    integrable_cosh_mul_gaussianReal x lam _
      (continuous_sech.pow 4).measurable 1 (bridge_sech_pow_bound 4)
  have hsum : doobOperator lam (fun y => Real.tanh y ^ 2) x +
      doobOperator lam (fun y => sech y ^ 2) x = 1 := by
    rw [← doobOperator_add_of_integrable lam x (fun y => Real.tanh y ^ 2)
      (fun y => sech y ^ 2) htanh hsech2]
    have heq : (fun y : ℝ => Real.tanh y ^ 2 + sech y ^ 2) = (fun _ => 1) :=
      funext tanh_sq_add_sech_sq
    rw [heq, doobOperator_one]
  have hle := doobOperator_mono_of_integrable lam x (fun y => sech y ^ 4)
    (fun y => sech y ^ 2) hsech4 hsech2
    (fun y => by
      have hs : 0 ≤ sech y ^ 2 := sq_nonneg _
      have hs1 : sech y ^ 2 ≤ 1 := pow_le_one₀ (sech_pos y).le (sech_le_one y)
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)])
  linarith

/-- Gaussian averaging preserves the moment comparison needed in the small regime. -/
theorem gaussianDoobFourthMoment_le_one_sub_second (β h q : ℝ) (lam : ℝ≥0) :
    gaussianDoobFourthMoment β h q lam ≤ 1 - gaussianDoobSecondMoment β h q lam := by
  have hi2 := integrable_gaussianDoobSecondMoment β h q lam
  have hi4 := integrable_gaussianDoobFourthMoment β h q lam
  have hh := integral_mono hi4 ((integrable_const (1 : ℝ)).sub hi2)
    (fun x => doob_fourth_le_one_sub_second lam x)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const (1 : ℝ)) hi2] at hh
  simpa [gaussianDoobSecondMoment, gaussianDoobFourthMoment] using hh

/-- The actual Gaussian Doob fourth moment satisfies the analytic exponential
estimate, including time zero. This still makes no diffusion-law assertion. -/
theorem gaussianDoobFourthMoment_exponential_decay {β h q : ℝ}
    (hβ : β ≠ 0) (hq : 0 < q) (hh : 0 ≤ h) (hfield : h ≤ β ^ 2 * q) (lam : ℝ≥0) :
    β ^ 2 * gaussianDoobFourthMoment β h q lam ≤
      atParameter β h q * Real.exp (-(lam : ℝ) / 2) := by
  by_cases hlam : lam = 0
  · subst lam
    simpa only [NNReal.coe_zero, neg_zero, zero_div, Real.exp_zero, mul_one] using
      (gaussianDoobFourthMoment_initial (β := β) (h := h) hq.le).le
  · have hvpos : 0 < β ^ 2 * q := mul_pos (sq_pos_of_ne_zero hβ) hq
    have hv : (β ^ 2 * q).toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr hvpos)
    have hvariance : h ≤ ((β ^ 2 * q).toNNReal : ℝ) := by
      simpa only [Real.coe_toNNReal _ hvpos.le] using hfield
    have hdec := gaussian_doob_sech_fourth_exponential_decay h _ hv hh hvariance lam hlam
    have hscaled := mul_le_mul_of_nonneg_left hdec (sq_nonneg β)
    change β ^ 2 * gaussianDoobFourthMoment β h q lam ≤ _ at hscaled
    calc
      _ ≤ β ^ 2 * (Real.exp (-(lam : ℝ) / 2) *
        (∫ x, sech x ^ 4 ∂gaussianReal h (β ^ 2 * q).toNNReal)) := hscaled
      _ = atParameter β h q * Real.exp (-(lam : ℝ) / 2) := by
        rw [atParameter_eq_gaussian hq.le]
        ring

/-- The real-time rescaling gives precisely the derivative envelope in the paper. -/
theorem hardFourthMoment_exponential_decay {β h q t : ℝ}
    (hβ : β ≠ 0) (hq : 0 < q) (hh : 0 ≤ h) (hfield : h ≤ β ^ 2 * q) (ht : q ≤ t) :
    β ^ 2 * hardFourthMoment β h q t ≤
      atParameter β h q * Real.exp (-(β ^ 2 * (t - q)) / 2) := by
  have htime : 0 ≤ β ^ 2 * (t - q) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht)
  have hdec := gaussianDoobFourthMoment_exponential_decay hβ hq hh hfield
    (β ^ 2 * (t - q)).toNNReal
  rw [Real.coe_toNNReal (β ^ 2 * (t - q)) htime] at hdec
  exact hdec

/-- The complete right-hand comparison with the unproved stochastic inputs
visible. The derivative envelope is derived from the actual analytic Gaussian
estimate; the structural field bound is also proved, rather than assumed. -/
theorem right_bound_of_doob_moment_inputs {β h q : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hf : ContinuousOn f (Icc q 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hLaw : ∀ t ∈ Icc q (1 : ℝ), f t = hardSecondMoment β h q t)
    (hIto : ∀ t ∈ Ioo q (1 : ℝ), deriv f t = β ^ 2 * hardFourthMoment β h q t) :
    ∀ t ∈ Icc q (1 : ℝ), f t ≤ t := by
  have hfix : f q = q := by
    rw [hLaw q ⟨le_rfl, hq.2⟩, hardSecondMoment_initial hq.1, ← hfixed]
  have hqpos := fixedPoint_pos hh hq.1 hfixed
  apply hard_full_of_regime_bounds hβ hAT hq.2 hf hd hfix
  · intro t ht
    rw [hIto t ht]
    exact mul_nonneg (sq_nonneg β) (gaussianDoobFourthMoment_nonneg β h q _)
  · intro t ht
    rw [hIto t ht, hLaw t ⟨ht.1.le, ht.2.le⟩]
    exact mul_le_mul_of_nonneg_left
      (gaussianDoobFourthMoment_le_one_sub_second β h q _) (sq_nonneg β)
  · exact fixedPoint_structural_field_lt hh hq.1 hfixed
  · intro hfield t ht
    rw [hIto t ht]
    exact hardFourthMoment_exponential_decay (ne_of_gt hβ) hqpos hh.le hfield ht.1.le

/-- Under the small-mean condition, the same analytic bridge gives the paper's
strict right-hand comparison, conditional on transition and Itô identities. -/
theorem right_strict_bound_of_doob_moment_inputs {β h q : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hfield : h ≤ β ^ 2 * q)
    (hf : ContinuousOn f (Icc q 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hLaw : ∀ t ∈ Icc q (1 : ℝ), f t = hardSecondMoment β h q t)
    (hIto : ∀ t ∈ Ioo q (1 : ℝ), deriv f t = β ^ 2 * hardFourthMoment β h q t) :
    ∀ t ∈ Ioc q (1 : ℝ), f t < t := by
  have hfix : f q = q := by
    rw [hLaw q ⟨le_rfl, hq.2⟩, hardSecondMoment_initial hq.1, ← hfixed]
  apply right_strict_bound_of_exp_deriv hβ hAT hq.2 hf hd hfix
  intro t ht
  rw [hIto t ht]
  exact hardFourthMoment_exponential_decay (ne_of_gt hβ)
    (fixedPoint_pos hh hq.1 hfixed) hh.le hfield ht.1.le

/-- An analytic specialization to the actual second-moment function. Its
regularity and the Itô-style derivative equation remain explicit inputs. -/
theorem hardSecondMoment_le_time_of_derivative_identity {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hf : ContinuousOn (hardSecondMoment β h q) (Icc q 1))
    (hd : DifferentiableOn ℝ (hardSecondMoment β h q) (Ioo q 1))
    (hIto : ∀ t ∈ Ioo q (1 : ℝ),
      deriv (hardSecondMoment β h q) t = β ^ 2 * hardFourthMoment β h q t) :
    ∀ t ∈ Icc q (1 : ℝ), hardSecondMoment β h q t ≤ t :=
  right_bound_of_doob_moment_inputs hβ hh hq hfixed hAT hf hd (fun _ _ => rfl) hIto

/-- Conditional minimum of the actual variational integral, after deriving
the full right-hand bound through the proved Gaussian analytic bridge. -/
theorem parisiG_minimum_of_doob_moment_inputs {β h q : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hf : ContinuousOn f (Icc 0 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hPoincare : ∀ t ∈ Icc (0 : ℝ) q,
      q - f t ≤ atParameter β h q * (q - t))
    (hLaw : ∀ t ∈ Icc q (1 : ℝ), f t = hardSecondMoment β h q t)
    (hIto : ∀ t ∈ Ioo q (1 : ℝ), deriv f t = β ^ 2 * hardFourthMoment β h q t) :
    ∀ t ∈ Icc (0 : ℝ) 1, parisiG β f q ≤ parisiG β f t := by
  apply parisiG_minimum_of_signs hq hf
  · intro t ht
    exact left_sign_of_poincare_bound hAT ht.2 (hPoincare t ht)
  · have hfRight : ContinuousOn f (Icc q (1 : ℝ)) :=
      hf.mono (fun t ht => ⟨hq.1.trans ht.1, ht.2⟩)
    exact right_bound_of_doob_moment_inputs hβ hh hq hfixed hAT hfRight hd hLaw hIto

end Paper
