module

/-
# Differentiating a cascade level: the tilted (Gibbs) chain rule

New work for the ParisiFormula project (not vendored).

## What this file is for

Half 2 of Target 3 is the sign of `φ'(t)` for Guerra's interpolating cascade.  The
interpolation is arranged (see `Targets/CascadeEndpoint.lean` §8) so that `t` enters in one
place only, the base

  `base_t(y) = log ∑_σ exp (√t·U(σ) + ∑_i σ_i (√(1-t)·y_i + h))`,

with the level variances held fixed.  Differentiating `φ(t)` then means pushing `d/dt`
through `k+2` nested smoothing levels down to the base.

**This file supplies the rule for one level.**  The point is that the derivative of

  `(1/m) log ∫ exp (m · A_u(x + √v z)) dγ(z)`

with respect to the parameter `u` is the *tilted average* of `∂_u A_u`:

  `∫ (∂_u A_u)(x + √v z) · W(z) dγ(z)`,   `W(z) = exp (m A_u(x + √v z)) / ∫ exp (m A_u …)`,

and that the `m = 0` branch obeys the same formula with `W ≡ 1`.  The two branches therefore
unify, which is what makes the nested derivative computable: chaining the rule over the
levels turns `dφ/dt` into a nested tilted average — the Gibbs average over the cascade tree,
which is exactly the object `⟨·⟩_t` that Guerra's remainder
`-(β²/4) ∑_p (m_{p+1} - m_p) 𝔼⟨(R_{1,2} - q_p)²⟩` is written in.

The hypotheses are uniform-in-`u` linear growth bounds on `A` and on `∂_u A`, which is what
the domination in `hasDerivAt_integral_of_dominated_loc_of_deriv_le` needs; because they are
uniform, the neighbourhood in that lemma can be taken to be all of `ℝ`.
-/
public import Targets.CascadeEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

/-! ## 1. Integrability of the dominating functions -/

/-- `(a + b|z|) e^{c|z|}` is Gaussian-integrable: the two pieces are
`integrable_exp_abs_mul_stdGaussian` and `integrable_abs_mul_exp_abs_stdGaussian`. -/
theorem integrable_poly_mul_exp_abs (a b c : ℝ) :
    Integrable (fun z : ℝ => (a + b * |z|) * Real.exp (c * |z|)) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => a * Real.exp (c * |z|)) (gaussianReal 0 1) :=
    (integrable_exp_abs_mul_stdGaussian c).const_mul a
  have h2 : Integrable (fun z : ℝ => b * (|z| * Real.exp (c * |z|))) (gaussianReal 0 1) :=
    (integrable_abs_mul_exp_abs_stdGaussian c).const_mul b
  refine (h1.add h2).congr ?_
  filter_upwards with z
  show a * Real.exp (c * |z|) + b * (|z| * Real.exp (c * |z|))
      = (a + b * |z|) * Real.exp (c * |z|)
  ring

/-! ## 2. The tilted weight of one level -/

/--
The tilted (Gibbs) weight attached to one smoothing level.  For `m ≠ 0` it is the
exponential tilt normalised to a probability density; for `m = 0` — where the level is a
plain average — it is `1`.  Writing both branches this way is what lets the chain rule below
be stated uniformly.
-/
noncomputable def tiltWeight (m v : ℝ) (A : ℝ → ℝ) (x z : ℝ) : ℝ :=
  if m = 0 then 1
  else Real.exp (m * A (x + Real.sqrt v * z)) /
        ∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1)

/-- The tilted weight is non-negative. -/
theorem tiltWeight_nonneg {m v : ℝ} {A : ℝ → ℝ} (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (x z : ℝ) : 0 ≤ tiltWeight m v A x z := by
  unfold tiltWeight
  split
  · exact zero_le_one
  · exact div_nonneg (Real.exp_pos _).le (smoothing_integral_pos hA hmeas x).le

/-! ## 3. The chain rule for one level -/

section ChainRule

variable {A A' : ℝ → ℝ → ℝ} {m v C D C' D' : ℝ}

/-- Uniform growth transported to the shifted argument. -/
private theorem shift_bound (hD : 0 ≤ D) (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (x v : ℝ) (u z : ℝ) :
    |A u (x + Real.sqrt v * z)| ≤ (C + D * |x|) + (D * Real.sqrt v) * |z| := by
  refine (hb u _).trans ?_
  have h : |x + Real.sqrt v * z| ≤ |x| + Real.sqrt v * |z| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
  nlinarith [abs_nonneg z, Real.sqrt_nonneg v]

/--
**The `m = 0` branch.**  Differentiating under a plain Gaussian average: the derivative is
the plain average of the derivative, i.e. the tilted average with weight `1`.
-/
theorem hasDerivAt_integral_param (x u₀ : ℝ) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => ∫ z, A u (x + Real.sqrt v * z) ∂(gaussianReal 0 1))
      (∫ z, A' u₀ (x + Real.sqrt v * z) ∂(gaussianReal 0 1)) u₀ := by
  classical
  have hbint : Integrable
      (fun z : ℝ => (C' + D' * |x|) + (D' * Real.sqrt v) * |z|) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_abs_stdGaussian.const_mul _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => A u (x + Real.sqrt v * z))
    (F' := fun u z => A' u (x + Real.sqrt v * z))
    (bound := fun z => (C' + D' * |x|) + (D' * Real.sqrt v) * |z|)
    (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ hbint ?_).2
  · filter_upwards with u
    exact ((hmeas u).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).aestronglyMeasurable
  · exact integrable_of_hasLinearGrowth hA0 (hmeas u₀) x v
  · exact ((hmeas' u₀).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs]
    exact shift_bound hD' hb' x v u z
  · filter_upwards with z u _
    exact hderiv u (x + Real.sqrt v * z)


/--
**The `m ≠ 0` branch, inner step.**  Differentiating under the exponential average.
-/
theorem hasDerivAt_integral_exp_param (x u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => ∫ z, Real.exp (m * A u (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
      (∫ z, m * (A' u₀ (x + Real.sqrt v * z)
        * Real.exp (m * A u₀ (x + Real.sqrt v * z))) ∂(gaussianReal 0 1)) u₀ := by
  classical
  set K : ℝ := Real.exp (|m| * (C + D * |x|)) with hK
  set a0 : ℝ := |m| * (C' + D' * |x|) * K with ha0
  set b0 : ℝ := |m| * (D' * Real.sqrt v) * K with hb0
  set c0 : ℝ := |m| * (D * Real.sqrt v) with hc0
  have hbint : Integrable (fun z : ℝ => (a0 + b0 * |z|) * Real.exp (c0 * |z|))
      (gaussianReal 0 1) := integrable_poly_mul_exp_abs _ _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => Real.exp (m * A u (x + Real.sqrt v * z)))
    (F' := fun u z => m * (A' u (x + Real.sqrt v * z)
      * Real.exp (m * A u (x + Real.sqrt v * z))))
    (bound := fun z => (a0 + b0 * |z|) * Real.exp (c0 * |z|))
    (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ hbint ?_).2
  · filter_upwards with u
    exact (Real.continuous_exp.measurable.comp
      (((hmeas u).comp
        ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m)).aestronglyMeasurable
  · exact integrable_exp_mul_of_hasLinearGrowth hA0 (hmeas u₀) m x v
  · exact ((((hmeas' u₀).comp
      ((measurable_id.const_mul (Real.sqrt v)).const_add x)).mul
      (Real.continuous_exp.measurable.comp
        (((hmeas u₀).comp
          ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m))).const_mul
      m).aestronglyMeasurable
  · filter_upwards with z u _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    -- `|m| · |A'| · exp (m A) ≤ (a0 + b0|z|) · exp (c0 |z|)`
    have h1 : |A' u (x + Real.sqrt v * z)|
        ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| := shift_bound hD' hb' x v u z
    have h2 : Real.exp (m * A u (x + Real.sqrt v * z)) ≤ K * Real.exp (c0 * |z|) := by
      have hle : m * A u (x + Real.sqrt v * z)
          ≤ |m| * ((C + D * |x|) + (D * Real.sqrt v) * |z|) := by
        have hmm : m * A u (x + Real.sqrt v * z) ≤ |m * A u (x + Real.sqrt v * z)| :=
          le_abs_self _
        have : |m * A u (x + Real.sqrt v * z)| = |m| * |A u (x + Real.sqrt v * z)| := abs_mul _ _
        nlinarith [shift_bound hD hb x v u z, abs_nonneg m]
      calc Real.exp (m * A u (x + Real.sqrt v * z))
          ≤ Real.exp (|m| * ((C + D * |x|) + (D * Real.sqrt v) * |z|)) := Real.exp_le_exp.2 hle
        _ = K * Real.exp (c0 * |z|) := by
            rw [hK, hc0, ← Real.exp_add]; ring_nf
    have hKpos : 0 < K := Real.exp_pos _
    have hexppos : 0 < Real.exp (c0 * |z|) := Real.exp_pos _
    have hbn : (0 : ℝ) ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| :=
      le_trans (abs_nonneg _) h1
    calc |m| * (|A' u (x + Real.sqrt v * z)| * Real.exp (m * A u (x + Real.sqrt v * z)))
        ≤ |m| * (((C' + D' * |x|) + (D' * Real.sqrt v) * |z|)
            * (K * Real.exp (c0 * |z|))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg m)
          exact mul_le_mul h1 h2 (Real.exp_pos _).le hbn
      _ = (a0 + b0 * |z|) * Real.exp (c0 * |z|) := by rw [ha0, hb0]; ring
  · filter_upwards with z u _
    have hd := ((hderiv u (x + Real.sqrt v * z)).const_mul m).exp
    exact hd.congr_deriv (by ring)

/--
**The tilted (Gibbs) chain rule for one cascade level.**

The derivative of a smoothing level with respect to a parameter of the function being
smoothed is the *tilted average* of the derivative.  Both branches of `parisiStep` obey the
same formula: for `m ≠ 0` the weight is the exponential tilt, for `m = 0` it is `1`.

Chaining this over the `k+2` levels is what turns `dφ/dt` into a nested tilted average — the
Gibbs average over the cascade tree.
-/
theorem hasDerivAt_parisiStep_param (x u₀ : ℝ) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u, Measurable (A u)) (hmeas' : ∀ u, Measurable (A' u))
    (hb : ∀ u y, |A u y| ≤ C + D * |y|)
    (hb' : ∀ u y, |A' u y| ≤ C' + D' * |y|)
    (hA0 : HasLinearGrowth (A u₀)) :
    HasDerivAt (fun u => parisiStep m v (A u) x)
      (∫ z, A' u₀ (x + Real.sqrt v * z)
        * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1)) u₀ := by
  classical
  by_cases hm : m = 0
  · have hfun : (fun u => parisiStep m v (A u) x)
        = fun u => ∫ z, A u (x + Real.sqrt v * z) ∂(gaussianReal 0 1) := by
      funext u; rw [parisiStep, if_pos hm]
    have hval : (∫ z, A' u₀ (x + Real.sqrt v * z)
          * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1))
        = ∫ z, A' u₀ (x + Real.sqrt v * z) ∂(gaussianReal 0 1) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show A' u₀ (x + Real.sqrt v * z) * tiltWeight m v (A u₀) x z
          = A' u₀ (x + Real.sqrt v * z)
      rw [tiltWeight, if_pos hm, mul_one]
    rw [hfun, hval]
    exact hasDerivAt_integral_param x u₀ hD' hderiv hmeas hmeas' hb' hA0
  · have hIpos : 0 < ∫ z, Real.exp (m * A u₀ (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      smoothing_integral_pos hA0 (hmeas u₀) x
    have hfun : (fun u => parisiStep m v (A u) x)
        = fun u => (1 / m) * Real.log
            (∫ z, Real.exp (m * A u (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) := by
      funext u; rw [parisiStep, if_neg hm]
    have hI := hasDerivAt_integral_exp_param (A := A) (A' := A') (m := m) (v := v)
      (C := C) (D := D) (C' := C') (D' := D')
      x u₀ hD hD' hderiv hmeas hmeas' hb hb' hA0
    have hlog := hI.log hIpos.ne'
    have hfin := hlog.const_mul (1 / m)
    rw [hfun]
    refine hfin.congr_deriv ?_
    -- `(1/m) · (∫ m (A' e)) / I  =  ∫ A' · (e / I)`
    rw [integral_const_mul]
    rw [show (∫ z, A' u₀ (x + Real.sqrt v * z)
          * tiltWeight m v (A u₀) x z ∂(gaussianReal 0 1))
        = ∫ z, (A' u₀ (x + Real.sqrt v * z)
            * Real.exp (m * A u₀ (x + Real.sqrt v * z)))
            / (∫ w, Real.exp (m * A u₀ (x + Real.sqrt v * w)) ∂(gaussianReal 0 1))
          ∂(gaussianReal 0 1) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show A' u₀ (x + Real.sqrt v * z) * tiltWeight m v (A u₀) x z
            = A' u₀ (x + Real.sqrt v * z) * Real.exp (m * A u₀ (x + Real.sqrt v * z))
              / (∫ w, Real.exp (m * A u₀ (x + Real.sqrt v * w)) ∂(gaussianReal 0 1))
        rw [tiltWeight, if_neg hm, mul_div_assoc]))]
    rw [integral_div]
    field_simp

end ChainRule


/-! ## 4. The tilted weight is a bounded perturbation of the Gaussian

To chain the rule of §3 over the `k+2` levels one needs the *derivative* to keep linear
growth from level to level.  The derivative at a level is a tilted average
`∫ A'(x + √v z) W(z) dγ`, so with `|A'(y)| ≤ C' + D'|y|` one gets

  `|∫ A' W| ≤ C' + D'|x| + D'√v · ∫ |z| W(z) dγ`,

and linear growth propagates **iff the tilted first moment `∫ |z| W dγ` is bounded
independently of `x`**.  That is false for a general tilt — the tilt can drag mass out to
where `A` is large — but true when `A` is Lipschitz, because then the tilt is a bounded
perturbation of the Gaussian:

  `W(z) ≤ exp (c·∫|w|dγ) · exp (c|z|)`,   `c = |m|·L·√v`,

with the numerator bounded by Lipschitzness and the denominator bounded below by Jensen.
Every level of the Parisi cascade is `1`-Lipschitz (`parisiF_props`), so this applies.
-/

/-- Jensen's inequality in the form `exp (∫ g) ≤ ∫ exp g`. -/
theorem exp_integral_le_integral_exp {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 1))
    (hexp : Integrable (fun z => Real.exp (g z)) (gaussianReal 0 1)) :
    Real.exp (∫ z, g z ∂(gaussianReal 0 1)) ≤ ∫ z, Real.exp (g z) ∂(gaussianReal 0 1) := by
  have hpos : 0 < ∫ z, Real.exp (g z) ∂(gaussianReal 0 1) := integral_exp_pos hexp
  have hlogint : Integrable (fun z => Real.log (Real.exp (g z))) (gaussianReal 0 1) := by
    refine hg.congr ?_
    filter_upwards with z
    show g z = Real.log (Real.exp (g z))
    rw [Real.log_exp]
  have hJ := integral_log_le_log_integral (μ := gaussianReal 0 1)
    (W := fun z => Real.exp (g z)) (fun z => Real.exp_pos _) hexp hlogint
  have hLHS : (∫ z, Real.log (Real.exp (g z)) ∂(gaussianReal 0 1))
      = ∫ z, g z ∂(gaussianReal 0 1) := by
    have hfun : (fun z => Real.log (Real.exp (g z))) = g := by
      funext z; rw [Real.log_exp]
    rw [hfun]
  rw [hLHS] at hJ
  calc Real.exp (∫ z, g z ∂(gaussianReal 0 1))
      ≤ Real.exp (Real.log (∫ z, Real.exp (g z) ∂(gaussianReal 0 1))) := Real.exp_le_exp.2 hJ
    _ = _ := Real.exp_log hpos

section Tilt

variable {m v L : ℝ} {A : ℝ → ℝ}

/-- For an `L`-Lipschitz `A`, the tilted weight is dominated by `e^{c·𝔼|w|}·e^{c|z|}` with
`c = |m|L√v` — a bound **independent of `x`**. -/
theorem tiltWeight_le (hL : 0 ≤ L) (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x z : ℝ) :
    tiltWeight m v A x z
      ≤ Real.exp ((|m| * L * Real.sqrt v) * gAbsMoment)
        * Real.exp ((|m| * L * Real.sqrt v) * |z|) := by
  classical
  set c : ℝ := |m| * L * Real.sqrt v with hc
  have hcnn : 0 ≤ c := by
    rw [hc]; positivity
  have hgm : 0 ≤ gAbsMoment := gAbsMoment_nonneg
  by_cases hm : m = 0
  · rw [tiltWeight, if_pos hm]
    have h1 : (1 : ℝ) ≤ Real.exp (c * gAbsMoment) :=
      Real.one_le_exp (by positivity)
    have h2 : (1 : ℝ) ≤ Real.exp (c * |z|) :=
      Real.one_le_exp (by positivity)
    nlinarith
  · rw [tiltWeight, if_neg hm]
    -- the Lipschitz deviation of the shifted function
    have hdev : ∀ w : ℝ, |A (x + Real.sqrt v * w) - A x| ≤ L * (Real.sqrt v * |w|) := by
      intro w
      have := hLip (x + Real.sqrt v * w) x
      rwa [show (x + Real.sqrt v * w) - x = Real.sqrt v * w by ring, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg v)] at this
    have hnum : Real.exp (m * A (x + Real.sqrt v * z))
        ≤ Real.exp (m * A x) * Real.exp (c * |z|) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h2 : m * A (x + Real.sqrt v * z) - m * A x
          ≤ |m| * |A (x + Real.sqrt v * z) - A x| := by
        rw [← mul_sub, ← abs_mul]
        exact le_abs_self _
      have h3 : |m| * |A (x + Real.sqrt v * z) - A x|
          ≤ |m| * (L * (Real.sqrt v * |z|)) :=
        mul_le_mul_of_nonneg_left (hdev z) (abs_nonneg m)
      have h4 : |m| * (L * (Real.sqrt v * |z|)) = c * |z| := by rw [hc]; ring
      linarith
    -- Jensen lower bound on the normalisation
    have hAint : Integrable (fun w => m * A (x + Real.sqrt v * w)) (gaussianReal 0 1) :=
      (integrable_of_hasLinearGrowth hA hmeas x v).const_mul m
    have hexpint : Integrable (fun w => Real.exp (m * A (x + Real.sqrt v * w)))
        (gaussianReal 0 1) := integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
    have hmean : Real.exp (m * A x) * Real.exp (-(c * gAbsMoment))
        ≤ ∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1) := by
      refine le_trans ?_ (exp_integral_le_integral_exp hAint hexpint)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      -- `m A x - c 𝔼|w| ≤ ∫ m A (x + √v w)`
      have hlow : (∫ w, (m * A x - c * |w|) ∂(gaussianReal 0 1))
          ≤ ∫ w, m * A (x + Real.sqrt v * w) ∂(gaussianReal 0 1) := by
        refine integral_mono
          ((integrable_const _).sub (integrable_abs_stdGaussian.const_mul c)) hAint ?_
        intro w
        have h := (abs_le.1 (hdev w)).1
        have h2 : |m * A (x + Real.sqrt v * w) - m * A x|
            ≤ |m| * (L * (Real.sqrt v * |w|)) := by
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (hdev w) (abs_nonneg m)
        have h3 := (abs_le.1 h2).1
        show m * A x - c * |w| ≤ m * A (x + Real.sqrt v * w)
        rw [hc]; nlinarith
      have hcalc : (∫ w, (m * A x - c * |w|) ∂(gaussianReal 0 1))
          = m * A x - c * gAbsMoment := by
        rw [integral_sub (integrable_const _) (integrable_abs_stdGaussian.const_mul c),
          integral_const, probReal_univ, one_smul, integral_const_mul, gAbsMoment]
      rw [hcalc] at hlow
      linarith
    -- combine
    have hIpos : 0 < ∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1) :=
      smoothing_integral_pos hA hmeas x
    rw [div_le_iff₀ hIpos]
    calc Real.exp (m * A (x + Real.sqrt v * z))
        ≤ Real.exp (m * A x) * Real.exp (c * |z|) := hnum
      _ = (Real.exp (c * gAbsMoment) * Real.exp (c * |z|))
            * (Real.exp (m * A x) * Real.exp (-(c * gAbsMoment))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ ≤ (Real.exp (c * gAbsMoment) * Real.exp (c * |z|))
            * (∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1)) := by
          exact mul_le_mul_of_nonneg_left hmean (by positivity)

/-- Hence the **tilted first absolute moment is bounded independently of `x`** — the fact
that makes linear growth propagate through the cascade. -/
theorem integral_abs_mul_tiltWeight_le (hL : 0 ≤ L)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    (∫ z, |z| * tiltWeight m v A x z ∂(gaussianReal 0 1))
      ≤ Real.exp ((|m| * L * Real.sqrt v) * gAbsMoment)
        * gAbsExpMoment (|m| * L * Real.sqrt v) := by
  classical
  set c : ℝ := |m| * L * Real.sqrt v with hc
  have hmeasW : Measurable (fun z => |z| * tiltWeight m v A x z) := by
    unfold tiltWeight
    split
    · exact measurable_id.abs.mul measurable_const
    · exact measurable_id.abs.mul
        ((Real.continuous_exp.measurable.comp
          ((hmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m)).div
          measurable_const)
  have hbd : ∀ z : ℝ, |z| * tiltWeight m v A x z
      ≤ Real.exp (c * gAbsMoment) * (|z| * Real.exp (c * |z|)) := by
    intro z
    have h := tiltWeight_le (m := m) (v := v) hL hLip hA hmeas x z
    have hz : (0 : ℝ) ≤ |z| := abs_nonneg z
    nlinarith [Real.exp_pos (c * gAbsMoment), Real.exp_pos (c * |z|)]
  have hdom : Integrable
      (fun z : ℝ => Real.exp (c * gAbsMoment) * (|z| * Real.exp (c * |z|)))
      (gaussianReal 0 1) :=
    (integrable_abs_mul_exp_abs_stdGaussian c).const_mul _
  have hint : Integrable (fun z => |z| * tiltWeight m v A x z) (gaussianReal 0 1) := by
    refine Integrable.mono hdom hmeasW.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg z)
        (tiltWeight_nonneg hA hmeas x z)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (c * gAbsMoment) * (|z| * Real.exp (c * |z|)))]
    exact hbd z
  calc (∫ z, |z| * tiltWeight m v A x z ∂(gaussianReal 0 1))
      ≤ ∫ z, Real.exp (c * gAbsMoment) * (|z| * Real.exp (c * |z|)) ∂(gaussianReal 0 1) :=
        integral_mono hint hdom hbd
    _ = Real.exp (c * gAbsMoment) * gAbsExpMoment c := by
        rw [integral_const_mul, gAbsExpMoment]

end Tilt


/-! ## 5. One level preserves linear growth of the derivative

The chain rule of §3 sends a level's derivative `A'` to the tilted average
`x ↦ ∫ A'(x + √v z) W(z) dγ`.  For the induction over levels to run, that tilted average must
again have linear growth in `x`.  It does, and the constant is explicit: since `W` is a
probability density,

  `|∫ A'(x + √v z) W| ≤ (C' + D'|x|) + D'√v · ∫|z| W`,

and §4 bounds `∫|z| W` independently of `x`.  This is the last new ingredient; the remaining
components of the induction (Lipschitzness, measurability, growth of the *function*) are
already available from `Targets/Milestones.lean`.
-/

section TiltGrowth

variable {m v L : ℝ} {A : ℝ → ℝ}

theorem measurable_tiltWeight (hmeas : Measurable A) (x : ℝ) :
    Measurable (fun z => tiltWeight m v A x z) := by
  unfold tiltWeight
  split
  · exact measurable_const
  · exact (Real.continuous_exp.measurable.comp
      ((hmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add x)).const_mul m)).div
      measurable_const

/-- Anything of linear growth is integrable against the tilted weight. -/
theorem integrable_mul_tiltWeight_of_bound (hL : 0 ≤ L)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {a b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ z : ℝ, |f z| ≤ a + b * |z|) :
    Integrable (fun z => f z * tiltWeight m v A x z) (gaussianReal 0 1) := by
  classical
  have ha : 0 ≤ a := by
    have h0 := hf 0
    rw [abs_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  set c : ℝ := |m| * L * Real.sqrt v with hc
  set K : ℝ := Real.exp (c * gAbsMoment) with hK
  have hKpos : 0 < K := Real.exp_pos _
  have hdom : Integrable
      (fun z : ℝ => (a * K + (b * K) * |z|) * Real.exp (c * |z|)) (gaussianReal 0 1) :=
    integrable_poly_mul_exp_abs _ _ _
  refine Integrable.mono hdom
    (hfmeas.mul (measurable_tiltWeight hmeas x)).aestronglyMeasurable ?_
  filter_upwards with z
  have hW := tiltWeight_le (m := m) (v := v) hL hLip hA hmeas x z
  have hWnn : 0 ≤ tiltWeight m v A x z := tiltWeight_nonneg hA hmeas x z
  have hane : 0 ≤ a + b * |z| := le_trans (abs_nonneg _) (hf z)
  have hnn : (0 : ℝ) ≤ (a * K + (b * K) * |z|) * Real.exp (c * |z|) := by
    have h1 : 0 ≤ a * K := mul_nonneg ha hKpos.le
    have h2 : 0 ≤ (b * K) * |z| := mul_nonneg (mul_nonneg hb hKpos.le) (abs_nonneg z)
    have h3 : 0 ≤ Real.exp (c * |z|) := (Real.exp_pos _).le
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  calc |f z| * |tiltWeight m v A x z|
      = |f z| * tiltWeight m v A x z := by rw [abs_of_nonneg hWnn]
    _ ≤ (a + b * |z|) * (K * Real.exp (c * |z|)) := mul_le_mul (hf z) hW hWnn hane
    _ = (a * K + (b * K) * |z|) * Real.exp (c * |z|) := by ring

/-- The tilted weight is a probability density. -/
theorem tiltWeight_integral_one (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    (∫ z, tiltWeight m v A x z ∂(gaussianReal 0 1)) = 1 := by
  classical
  by_cases hm : m = 0
  · have hfun : (fun z : ℝ => tiltWeight m v A x z) = fun _ : ℝ => (1 : ℝ) := by
      funext z; rw [tiltWeight, if_pos hm]
    rw [hfun, integral_const, probReal_univ, one_smul]
  · have hIpos : 0 < ∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1) :=
      smoothing_integral_pos hA hmeas x
    have hfun : (fun z : ℝ => tiltWeight m v A x z)
        = fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))
            / (∫ w, Real.exp (m * A (x + Real.sqrt v * w)) ∂(gaussianReal 0 1)) := by
      funext z; rw [tiltWeight, if_neg hm]
    rw [hfun, integral_div, div_self hIpos.ne']

/--
**One level preserves linear growth of the derivative.**

If `|g y| ≤ C' + D'|y|` then the tilted average `x ↦ ∫ g(x + √v z) W(z) dγ` again has linear
growth, with an explicit constant that does not depend on `x`.
-/
theorem abs_integral_mul_tiltWeight_le (hL : 0 ≤ L)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A)
    {g : ℝ → ℝ} (hgmeas : Measurable g) {C' D' : ℝ} (hD' : 0 ≤ D')
    (hg : ∀ y, |g y| ≤ C' + D' * |y|) (x : ℝ) :
    |∫ z, g (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)|
      ≤ (C' + D' * |x|)
        + (D' * Real.sqrt v)
          * (Real.exp ((|m| * L * Real.sqrt v) * gAbsMoment)
              * gAbsExpMoment (|m| * L * Real.sqrt v)) := by
  classical
  have hDv : 0 ≤ D' * Real.sqrt v := mul_nonneg hD' (Real.sqrt_nonneg v)
  have hC' : 0 ≤ C' := by
    have h0 := hg 0
    rw [abs_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  have hshift : ∀ z : ℝ, |g (x + Real.sqrt v * z)|
      ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| := by
    intro z
    refine (hg _).trans ?_
    have h : |x + Real.sqrt v * z| ≤ |x| + Real.sqrt v * |z| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
    nlinarith [abs_nonneg z, Real.sqrt_nonneg v]
  have hbnn : ∀ z : ℝ, 0 ≤ (C' + D' * |x|) + (D' * Real.sqrt v) * |z| := by
    intro z
    have h1 : 0 ≤ D' * |x| := mul_nonneg hD' (abs_nonneg x)
    have h2 : 0 ≤ (D' * Real.sqrt v) * |z| := mul_nonneg hDv (abs_nonneg z)
    linarith
  have hWnn : ∀ z, 0 ≤ tiltWeight m v A x z := fun z => tiltWeight_nonneg hA hmeas x z
  have hgW : Integrable
      (fun z => g (x + Real.sqrt v * z) * tiltWeight m v A x z) (gaussianReal 0 1) :=
    integrable_mul_tiltWeight_of_bound hL hLip hA hmeas x
      (hgmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add x)) hDv hshift
  have hbW : Integrable
      (fun z => ((C' + D' * |x|) + (D' * Real.sqrt v) * |z|) * tiltWeight m v A x z)
      (gaussianReal 0 1) :=
    integrable_mul_tiltWeight_of_bound hL hLip hA hmeas x
      (measurable_const.add (measurable_id.abs.const_mul _)) hDv
      (fun z => le_of_eq (abs_of_nonneg (hbnn z)))
  have hzW : Integrable
      (fun z => |z| * tiltWeight m v A x z) (gaussianReal 0 1) :=
    integrable_mul_tiltWeight_of_bound (m := m) (v := v) hL hLip hA hmeas x measurable_id.abs
      (a := 0) (b := 1) zero_le_one
      (fun z => by rw [abs_abs]; linarith [abs_nonneg z])
  have hWint : Integrable (fun z => tiltWeight m v A x z) (gaussianReal 0 1) := by
    have h := integrable_mul_tiltWeight_of_bound (m := m) (v := v) hL hLip hA hmeas x
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
      (a := 1) (b := 0) (le_refl (0 : ℝ))
      (fun z => by rw [abs_one]; linarith [abs_nonneg z])
    simpa using h
  calc |∫ z, g (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)|
      ≤ ∫ z, |g (x + Real.sqrt v * z) * tiltWeight m v A x z| ∂(gaussianReal 0 1) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, ((C' + D' * |x|) + (D' * Real.sqrt v) * |z|) * tiltWeight m v A x z
          ∂(gaussianReal 0 1) := by
        refine integral_mono hgW.abs hbW (fun z => ?_)
        rw [abs_mul, abs_of_nonneg (hWnn z)]
        exact mul_le_mul_of_nonneg_right (hshift z) (hWnn z)
    _ = (C' + D' * |x|) * (∫ z, tiltWeight m v A x z ∂(gaussianReal 0 1))
          + (D' * Real.sqrt v) * ∫ z, |z| * tiltWeight m v A x z ∂(gaussianReal 0 1) := by
        rw [show (fun z : ℝ =>
              ((C' + D' * |x|) + (D' * Real.sqrt v) * |z|) * tiltWeight m v A x z)
            = fun z : ℝ => (C' + D' * |x|) * tiltWeight m v A x z
              + (D' * Real.sqrt v) * (|z| * tiltWeight m v A x z) from
          funext (fun z => by ring)]
        rw [integral_add (hWint.const_mul _) (hzW.const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ (C' + D' * |x|)
          + (D' * Real.sqrt v)
            * (Real.exp ((|m| * L * Real.sqrt v) * gAbsMoment)
                * gAbsExpMoment (|m| * L * Real.sqrt v)) := by
        rw [tiltWeight_integral_one hA hmeas, mul_one]
        have hmom := integral_abs_mul_tiltWeight_le (m := m) (v := v) hL hLip hA hmeas x
        have := mul_le_mul_of_nonneg_left hmom hDv
        linarith

end TiltGrowth

end Targets
end SpinGlass
