module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Deterministic variational and second-moment arguments

This file formalizes the real-analysis part of arXiv:2604.11921v2.
The function `f` represents the stochastic second moment. Its identification
with a diffusion and the derivative identities from Itô calculus are explicit
hypotheses; they are not asserted or postulated here.
-/

open Set MeasureTheory

namespace Paper

/-- The actual interval-integral variational function in equation (Gmu-def). -/
noncomputable def parisiG (β : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in t..1, β ^ 2 / 2 * (f s - s)

/-- Continuity of the stochastic second moment suffices for the integrability
needed in the variational argument. -/
lemma parisiIntegrable {β a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => β ^ 2 / 2 * (f s - s)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) 1 :=
    (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) 1)).uIcc_subset ha hb
  exact continuousOn_const.mul ((hf.mono hsub).sub continuousOn_id)

/-- The sign change in the second-moment difference gives the variational
minimum at the replica-symmetric overlap, using the genuine integral. -/
theorem parisiG_minimum_of_signs {β q : ℝ} {f : ℝ → ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hf : ContinuousOn f (Icc 0 1))
    (hleft : ∀ t ∈ Icc (0 : ℝ) q, t ≤ f t)
    (hright : ∀ t ∈ Icc q (1 : ℝ), f t ≤ t) :
    ∀ t ∈ Icc (0 : ℝ) 1, parisiG β f q ≤ parisiG β f t := by
  intro t ht
  have hq1 := parisiIntegrable (β := β) (b := 1) hf hq (by constructor <;> norm_num)
  have htq := parisiIntegrable (β := β) hf ht hq
  have hadd := intervalIntegral.integral_add_adjacent_intervals htq hq1
  change (∫ s in q..1, β ^ 2 / 2 * (f s - s)) ≤
    ∫ s in t..1, β ^ 2 / 2 * (f s - s)
  rcases le_total t q with htq_le | hqt_le
  · have hpos : 0 ≤ ∫ s in t..q, β ^ 2 / 2 * (f s - s) := by
      apply intervalIntegral.integral_nonneg htq_le
      intro s hs
      apply mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num))
      exact sub_nonneg.mpr (hleft s ⟨ht.1.trans hs.1, hs.2⟩)
    linarith
  · have hneg : (∫ s in t..q, β ^ 2 / 2 * (f s - s)) ≥ 0 := by
      rw [intervalIntegral.integral_symm]
      have hpos : 0 ≤ ∫ s in q..t, -(β ^ 2 / 2 * (f s - s)) := by
        apply intervalIntegral.integral_nonneg hqt_le
        intro s hs
        apply neg_nonneg.mpr
        apply mul_nonpos_of_nonneg_of_nonpos
        · exact div_nonneg (sq_nonneg β) (by norm_num)
        · exact sub_nonpos.mpr (hright s ⟨hs.1, hs.2.trans ht.2⟩)
      simpa only [intervalIntegral.integral_neg] using hpos
    linarith

/-- The variational function decreases on any interval where `f(s) ≥ s`. -/
theorem parisiG_antitoneOn {β a b : ℝ} {f : ℝ → ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hf : ContinuousOn f (Icc 0 1))
    (hsign : ∀ s ∈ Icc a b, s ≤ f s) :
    AntitoneOn (parisiG β f) (Icc a b) := by
  intro x hx y hy hxy
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩
  have hxyint := parisiIntegrable (β := β) hf hx01 hy01
  have hy1int := parisiIntegrable (β := β) (b := 1) hf hy01 (by constructor <;> norm_num)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hxyint hy1int
  have hpos : 0 ≤ ∫ s in x..y, β ^ 2 / 2 * (f s - s) := by
    apply intervalIntegral.integral_nonneg hxy
    intro s hs
    exact mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num))
      (sub_nonneg.mpr (hsign s ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩))
  change (∫ s in y..1, β ^ 2 / 2 * (f s - s)) ≤
    ∫ s in x..1, β ^ 2 / 2 * (f s - s)
  linarith

/-- The variational function increases on any interval where `f(s) ≤ s`. -/
theorem parisiG_monotoneOn {β a b : ℝ} {f : ℝ → ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hf : ContinuousOn f (Icc 0 1))
    (hsign : ∀ s ∈ Icc a b, f s ≤ s) :
    MonotoneOn (parisiG β f) (Icc a b) := by
  intro x hx y hy hxy
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩
  have hxyint := parisiIntegrable (β := β) hf hx01 hy01
  have hy1int := parisiIntegrable (β := β) (b := 1) hf hy01 (by constructor <;> norm_num)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hxyint hy1int
  have hnonneg : 0 ≤ ∫ s in x..y, -(β ^ 2 / 2 * (f s - s)) := by
    apply intervalIntegral.integral_nonneg hxy
    intro s hs
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (sq_nonneg β) (by norm_num))
      (sub_nonpos.mpr (hsign s ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩))
  rw [intervalIntegral.integral_neg] at hnonneg
  change (∫ s in x..1, β ^ 2 / 2 * (f s - s)) ≤
    ∫ s in y..1, β ^ 2 / 2 * (f s - s)
  linarith

/-- Proposition soft-full's quantitative conditional Poincaré consequence:
`f(t)-t ≥ (1-α)(q-t) ≥ 0`. -/
theorem left_quantitative_of_poincare_bound {α q t f_t : ℝ}
    (hα : α ≤ 1) (ht : t ≤ q)
    (hpoincare : q - f_t ≤ α * (q - t)) :
    0 ≤ (1 - α) * (q - t) ∧ (1 - α) * (q - t) ≤ f_t - t := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hα) (sub_nonneg.mpr ht)
  · nlinarith

/-- The elementary left-hand estimate arising from conditional Poincaré. -/
theorem left_sign_of_poincare_bound {α q t f_t : ℝ}
    (hα : α ≤ 1) (ht : t ≤ q)
    (hpoincare : q - f_t ≤ α * (q - t)) : t ≤ f_t := by
  have hquant := left_quantitative_of_poincare_bound hα ht hpoincare
  exact sub_nonneg.mp (hquant.1.trans hquant.2)

/-- A derivative bounded by one and a fixed point give the required
right-hand second-moment bound. Endpoints need only continuity. -/
theorem right_bound_of_deriv_le_one {q : ℝ} {f : ℝ → ℝ}
    (hq : q ≤ 1) (hf : ContinuousOn f (Icc q 1))
    (hd : DifferentiableOn ℝ f (Ioo q 1)) (hfix : f q = q)
    (hderiv : ∀ s ∈ Ioo q (1 : ℝ), deriv f s ≤ 1) :
    ∀ t ∈ Icc q (1 : ℝ), f t ≤ t := by
  intro t ht
  have hdiff : DifferentiableOn ℝ f (interior (Icc q (1 : ℝ))) := by
    simpa only [interior_Icc] using hd
  have hderiv' : ∀ s ∈ interior (Icc q (1 : ℝ)), deriv f s ≤ 1 := by
    simpa only [interior_Icc] using hderiv
  have hbound := (convex_Icc q (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hf hdiff hderiv' q ⟨le_rfl, hq⟩ t ht ht.1
  rw [hfix] at hbound
  linarith

/-- Nonnegative derivative gives monotonicity of the stochastic second moment. -/
theorem secondMoment_monotone {q : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc q 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hderiv : ∀ s ∈ Ioo q (1 : ℝ), 0 ≤ deriv f s) :
    MonotoneOn f (Icc q (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc q (1 : ℝ)) hf
  · simpa only [interior_Icc] using hd
  · simpa only [interior_Icc] using hderiv

/-- Proposition hard-small: the Itô derivative identities and the elementary
moment bound imply `f(t) ≤ t` when `β²(1-q) ≤ 1`.
The probabilistic statements have been isolated as explicit input bounds. -/
theorem hard_small_of_derivative_bounds {β q : ℝ} {f : ℝ → ℝ}
    (hq : q ≤ 1) (hf : ContinuousOn f (Icc q 1))
    (hd : DifferentiableOn ℝ f (Ioo q 1)) (hfix : f q = q)
    (hnonneg : ∀ s ∈ Ioo q (1 : ℝ), 0 ≤ deriv f s)
    (hmoment : ∀ s ∈ Ioo q (1 : ℝ), deriv f s ≤ β ^ 2 * (1 - f s))
    (hsmall : β ^ 2 * (1 - q) ≤ 1) :
    ∀ t ∈ Icc q (1 : ℝ), f t ≤ t := by
  have hmono := secondMoment_monotone hf hd hnonneg
  apply right_bound_of_deriv_le_one hq hf hd hfix
  intro s hs
  have hqf : q ≤ f s := by
    have hh := hmono ⟨le_rfl, hq⟩ ⟨hs.1.le, hs.2.le⟩ hs.1.le
    simpa only [hfix] using hh
  have hbound : β ^ 2 * (1 - f s) ≤ β ^ 2 * (1 - q) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg β)
  exact (hmoment s hs).trans (hbound.trans hsmall)

/-- Strict version of hard-hsmall's final calculus step. For positive `β`,
exponential decay gives a strict derivative bound away from `q`. -/
theorem right_strict_bound_of_exp_deriv {β α q : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hα : α ≤ 1) (hq : q ≤ 1)
    (hf : ContinuousOn f (Icc q 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hfix : f q = q)
    (hderiv : ∀ s ∈ Ioo q (1 : ℝ),
      deriv f s ≤ α * Real.exp (-(β ^ 2 * (s - q)) / 2)) :
    ∀ t ∈ Ioc q (1 : ℝ), f t < t := by
  intro t ht
  have hstrict : ∀ s ∈ interior (Icc q (1 : ℝ)), deriv f s < 1 := by
    intro s hs
    rw [interior_Icc] at hs
    have hexp : Real.exp (-(β ^ 2 * (s - q)) / 2) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hb2 : 0 < β ^ 2 := sq_pos_of_pos hβ
      have hprod := mul_pos hb2 (sub_pos.mpr hs.1)
      linarith
    have halpha : α * Real.exp (-(β ^ 2 * (s - q)) / 2) ≤
        Real.exp (-(β ^ 2 * (s - q)) / 2) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hα (Real.exp_nonneg _)
    exact (hderiv s hs).trans_lt (halpha.trans_lt hexp)
  have hdiff : DifferentiableOn ℝ f (interior (Icc q (1 : ℝ))) := by
    simpa only [interior_Icc] using hd
  have hbound := (convex_Icc q (1 : ℝ)).image_sub_lt_mul_sub_of_deriv_lt
    hf hdiff hstrict q ⟨le_rfl, hq⟩ t ⟨ht.1.le, ht.2⟩ ht.1
  rw [hfix] at hbound
  linarith

/-- The two right-hand regimes cover all parameters. This is the deterministic
content of Proposition hard-full, with the semigroup estimate explicit. -/
theorem hard_full_of_regime_bounds {β α q h : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hα : α ≤ 1) (hq : q ≤ 1)
    (hf : ContinuousOn f (Icc q 1)) (hd : DifferentiableOn ℝ f (Ioo q 1))
    (hfix : f q = q)
    (hnonneg : ∀ s ∈ Ioo q (1 : ℝ), 0 ≤ deriv f s)
    (hmoment : ∀ s ∈ Ioo q (1 : ℝ), deriv f s ≤ β ^ 2 * (1 - f s))
    (hstructure : 1 < β ^ 2 * (1 - q) → h < β ^ 2 * q)
    (hdecay : h ≤ β ^ 2 * q → ∀ s ∈ Ioo q (1 : ℝ),
      deriv f s ≤ α * Real.exp (-(β ^ 2 * (s - q)) / 2)) :
    ∀ t ∈ Icc q (1 : ℝ), f t ≤ t := by
  by_cases hsmall : β ^ 2 * (1 - q) ≤ 1
  · exact hard_small_of_derivative_bounds hq hf hd hfix hnonneg hmoment hsmall
  · have hlarge : 1 < β ^ 2 * (1 - q) := lt_of_not_ge hsmall
    have hstrict := right_strict_bound_of_exp_deriv hβ hα hq hf hd hfix
      (hdecay (hstructure hlarge).le)
    intro t ht
    rcases ht.1.eq_or_lt with heq | hlt
    · rw [← heq, hfix]
    · exact (hstrict t ⟨hlt, ht.2⟩).le

/-- The main deterministic variational conclusion, combining the left-hand
conditional Poincaré estimate and the full right-hand regime argument.
PDE/SDE identification, the structural Gaussian bound, and the semigroup
estimate remain explicit mathematical hypotheses. -/
theorem parisiG_minimum_of_regime_bounds {β α q h : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hα : α ≤ 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hf : ContinuousOn f (Icc 0 1))
    (hd : DifferentiableOn ℝ f (Ioo q 1)) (hfix : f q = q)
    (hpoincare : ∀ s ∈ Icc (0 : ℝ) q, q - f s ≤ α * (q - s))
    (hnonneg : ∀ s ∈ Ioo q (1 : ℝ), 0 ≤ deriv f s)
    (hmoment : ∀ s ∈ Ioo q (1 : ℝ), deriv f s ≤ β ^ 2 * (1 - f s))
    (hstructure : 1 < β ^ 2 * (1 - q) → h < β ^ 2 * q)
    (hdecay : h ≤ β ^ 2 * q → ∀ s ∈ Ioo q (1 : ℝ),
      deriv f s ≤ α * Real.exp (-(β ^ 2 * (s - q)) / 2)) :
    ∀ t ∈ Icc (0 : ℝ) 1, parisiG β f q ≤ parisiG β f t := by
  apply parisiG_minimum_of_signs hq hf
  · intro s hs
    exact left_sign_of_poincare_bound hα hs.2 (hpoincare s hs)
  · have hfRight : ContinuousOn f (Icc q (1 : ℝ)) :=
      hf.mono fun s hs => ⟨hq.1.trans hs.1, hs.2⟩
    exact hard_full_of_regime_bounds hβ hα hq.2 hfRight hd hfix
      hnonneg hmoment hstructure hdecay

/-- FTC version of the integrated exponential estimate. The identity for the
second-moment derivative is given by `HasDerivAt`, while continuity of that
moment derivative supplies genuine interval integrability. -/
theorem secondMoment_le_integrated_exp {β α q : ℝ} {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc q 1)) (hd : ContinuousOn d (Icc q 1))
    (hderiv : ∀ s ∈ Ioo q (1 : ℝ), HasDerivAt f (d s) s) (hfix : f q = q)
    (hbound : ∀ s ∈ Ioo q (1 : ℝ),
      d s ≤ α * Real.exp (-(β ^ 2 * (s - q)) / 2)) :
    ∀ t ∈ Icc q (1 : ℝ),
      f t ≤ q + ∫ s in q..t, α * Real.exp (-(β ^ 2 * (s - q)) / 2) := by
  intro t ht
  have hsub : Icc q t ⊆ Icc q (1 : ℝ) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hIntD : IntervalIntegrable d volume q t :=
    (hd.mono hsub).intervalIntegrable_of_Icc ht.1
  have hexpCont : Continuous (fun s : ℝ => α * Real.exp (-(β ^ 2 * (s - q)) / 2)) := by
    fun_prop
  have hIntExp : IntervalIntegrable
      (fun s : ℝ => α * Real.exp (-(β ^ 2 * (s - q)) / 2)) volume q t :=
    hexpCont.intervalIntegrable q t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hf.mono hsub) (fun s hs => hderiv s ⟨hs.1, hs.2.trans_le ht.2⟩) hIntD
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo ht.1 hIntD hIntExp
    (fun s hs => hbound s ⟨hs.1, hs.2.trans_le ht.2⟩)
  rw [hFTC, hfix] at hmono
  linarith

/-- Exact evaluation of the exponential interval integral in the right-hand bound. -/
lemma exp_decay_integral {β α q t : ℝ} (hβ : β ≠ 0) :
    (∫ s in q..t, α * Real.exp (-(β ^ 2 * (s - q)) / 2)) =
      (2 * α / β ^ 2) * (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) := by
  have hInt : IntervalIntegrable
      (fun s : ℝ => α * Real.exp (-(β ^ 2 * (s - q)) / 2)) volume q t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hDeriv : ∀ s ∈ uIcc q t,
      HasDerivAt (fun x : ℝ => -(2 * α / β ^ 2) *
        Real.exp (-(β ^ 2 * (x - q)) / 2))
        (α * Real.exp (-(β ^ 2 * (s - q)) / 2)) s := by
    intro s hs
    have hh := (((((hasDerivAt_id s).sub_const q).const_mul (β ^ 2)).neg).div_const
      (2 : ℝ)).exp.const_mul (-(2 * α / β ^ 2))
    convert hh using 1 <;> simp only [id_eq, Pi.neg_apply, mul_one]
    field_simp [hβ]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt
  rw [hFTC]
  simp only [sub_self, mul_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- The explicit integrated exponential estimate in the proof of hard-hsmall. -/
theorem secondMoment_le_exp_bound {β α q : ℝ} {f d : ℝ → ℝ}
    (hβ : β ≠ 0) (hf : ContinuousOn f (Icc q 1))
    (hd : ContinuousOn d (Icc q 1))
    (hderiv : ∀ s ∈ Ioo q (1 : ℝ), HasDerivAt f (d s) s) (hfix : f q = q)
    (hbound : ∀ s ∈ Ioo q (1 : ℝ),
      d s ≤ α * Real.exp (-(β ^ 2 * (s - q)) / 2)) :
    ∀ t ∈ Icc q (1 : ℝ), f t ≤ q +
      (2 * α / β ^ 2) * (1 - Real.exp (-(β ^ 2 * (t - q)) / 2)) := by
  intro t ht
  have hle := secondMoment_le_integrated_exp hf hd hderiv hfix hbound t ht
  rwa [exp_decay_integral hβ] at hle

end Paper
