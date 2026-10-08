module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/-
# The tilted chain rule for an `N`-site cascade level

New work for the ParisiFormula project (not vendored).

`Targets/CascadeDeriv.lean` proves the tilted (Gibbs) chain rule for the one-dimensional
smoothing step.  Talagrand's (3.2) needs it for the `N`-site step `parisiStepPi`, because
for `t > 0` the base `F_{k+1,t}` couples the sites through `√t H(σ)` and does not factorise.
This file is that port.  Growth is measured in `ℓ¹`, `∑ᵢ |yᵢ|`, which is what the spin sum
naturally produces (`|∑ᵢ σᵢ yᵢ| ≤ ∑ᵢ |yᵢ|`), and integrability against `piGauss n` comes from
`Integrable.fintype_prod` applied to `exp (c ∑ᵢ |zᵢ|) = ∏ᵢ exp (c |zᵢ|)`.
-/
public import Targets.CascadeDeriv

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

variable {n : ℕ}

/-! ## 1. Integrability against `piGauss n` in `ℓ¹` -/

/-- `∑ᵢ |zᵢ|` as a function; the `ℓ¹` size of the cascade field. -/
noncomputable abbrev l1 (z : Fin n → ℝ) : ℝ := ∑ i, |z i|

theorem l1_nonneg (z : Fin n → ℝ) : 0 ≤ l1 z :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem measurable_l1 : Measurable (fun z : Fin n → ℝ => l1 z) :=
  Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).abs)

theorem measurable_shift (v : ℝ) (x : Fin n → ℝ) :
    Measurable (fun z : Fin n → ℝ => fun i => x i + Real.sqrt v * z i) :=
  Measurable.of_eval (fun i => measurable_const.add (measurable_const.mul (measurable_pi_apply i)))

theorem integrable_exp_l1 (c : ℝ) :
    Integrable (fun z : Fin n → ℝ => Real.exp (c * l1 z)) (piGauss n) := by
  have hfun : (fun z : Fin n → ℝ => Real.exp (c * l1 z))
      = fun z => ∏ i, Real.exp (c * |z i|) := by
    funext z
    rw [l1, Finset.mul_sum, Real.exp_sum]
  rw [hfun]
  exact Integrable.fintype_prod (fun i => integrable_exp_abs_mul_stdGaussian c)

theorem integrable_l1 : Integrable (fun z : Fin n → ℝ => l1 z) (piGauss n) :=
  integrable_finsetSum _ (fun i _ => integrable_piGauss_eval i integrable_abs_stdGaussian)

/-- `(a + b S) e^{c S} ≤ (a + b) e^{(c+1) S}` for `S ≥ 0`, so the left side is integrable. -/
theorem integrable_poly_mul_exp_l1 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    Integrable (fun z : Fin n → ℝ => (a + b * l1 z) * Real.exp (c * l1 z)) (piGauss n) := by
  refine Integrable.mono ((integrable_exp_l1 (c + 1)).const_mul (a + b)) ?_ ?_
  · exact ((measurable_const.add (measurable_l1.const_mul b)).mul
      (Real.continuous_exp.measurable.comp (measurable_l1.const_mul c))).aestronglyMeasurable
  · filter_upwards with z
    have hS := l1_nonneg z
    have hSe : l1 z ≤ Real.exp (l1 z) := by
      have := Real.add_one_le_exp (l1 z); linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a + b * l1 z) * Real.exp (c * l1 z)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a + b) * Real.exp ((c + 1) * l1 z))]
    have h1 : Real.exp (c * l1 z) ≤ Real.exp ((c + 1) * l1 z) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : l1 z * Real.exp (c * l1 z) ≤ Real.exp ((c + 1) * l1 z) := by
      calc l1 z * Real.exp (c * l1 z) ≤ Real.exp (l1 z) * Real.exp (c * l1 z) :=
            mul_le_mul_of_nonneg_right hSe (Real.exp_pos _).le
        _ = Real.exp ((c + 1) * l1 z) := by rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (c * l1 z)]

/-- The shifted argument in `ℓ¹`. -/
theorem l1_shift_le (v : ℝ) (x z : Fin n → ℝ) :
    l1 (fun i => x i + Real.sqrt v * z i) ≤ l1 x + Real.sqrt v * l1 z := by
  simp only [l1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]

/-! ## 2. The tilted weight of an `N`-site level -/

noncomputable def tiltWeightPi (n : ℕ) (m v : ℝ) (A : (Fin n → ℝ) → ℝ) (x z : Fin n → ℝ) : ℝ :=
  if m = 0 then 1
  else Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) /
        ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)

section ChainRule

/-! The hypotheses are required only on a neighbourhood `s` of `u₀`, because in the
application `u = t ∈ (0,1)` and the base derivative carries factors `1/(2√t)`,
`1/(2√(1-t))` that are bounded only away from the endpoints. -/

variable {A A' : ℝ → (Fin n → ℝ) → ℝ} {m v C D C' D' : ℝ}

private theorem shift_bound_pi (hD : 0 ≤ D) {B : (Fin n → ℝ) → ℝ}
    (hb : ∀ y, |B y| ≤ C + D * l1 y) (x : Fin n → ℝ) (v : ℝ) (z : Fin n → ℝ) :
    |B (fun i => x i + Real.sqrt v * z i)| ≤ (C + D * l1 x) + (D * Real.sqrt v) * l1 z := by
  refine (hb _).trans ?_
  have := l1_shift_le v x z
  nlinarith [l1_nonneg z, Real.sqrt_nonneg v]

/-- Integrability of `exp (m B(x + √v z))` from an `ℓ¹` growth bound. -/
theorem integrable_exp_shift_pi (hD : 0 ≤ D) {B : (Fin n → ℝ) → ℝ}
    (hb : ∀ y, |B y| ≤ C + D * l1 y) (hmeas : Measurable B) (x : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => Real.exp (m * B (fun i => x i + Real.sqrt v * z i)))
      (piGauss n) := by
  have hC : 0 ≤ C := by
    have h0 := hb 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  refine Integrable.mono ((integrable_exp_l1 (|m| * (D * Real.sqrt v))).const_mul
    (Real.exp (|m| * (C + D * l1 x)))) ?_ ?_
  · exact (Real.continuous_exp.measurable.comp
      ((hmeas.comp (measurable_shift v x)).const_mul m)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (|m| * (C + D * l1 x))
        * Real.exp (|m| * (D * Real.sqrt v) * l1 z)), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : m * B (fun i => x i + Real.sqrt v * z i)
        ≤ |m| * |B (fun i => x i + Real.sqrt v * z i)| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 := mul_le_mul_of_nonneg_left (shift_bound_pi hD hb x v z) (abs_nonneg m)
    nlinarith

theorem integral_exp_shift_pi_pos (hD : 0 ≤ D) {B : (Fin n → ℝ) → ℝ}
    (hb : ∀ y, |B y| ≤ C + D * l1 y) (hmeas : Measurable B) (x : Fin n → ℝ) :
    0 < ∫ z, Real.exp (m * B (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n) :=
  integral_exp_pos (integrable_exp_shift_pi hD hb hmeas x)

/-- **The `m = 0` branch.** -/
theorem hasDerivAt_integral_param_pi (x : Fin n → ℝ) {u₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 u₀)
    (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u ∈ s, Measurable (A u)) (hmeas' : ∀ u ∈ s, Measurable (A' u))
    (hb : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u ∈ s, ∀ y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => ∫ z, A u (fun i => x i + Real.sqrt v * z i) ∂(piGauss n))
      (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)) u₀ := by
  classical
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  have hbint : Integrable
      (fun z : Fin n → ℝ => (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) (piGauss n) :=
    (integrable_const _).add (integrable_l1.const_mul _)
  have hA0 : Integrable (fun z : Fin n → ℝ => A u₀ (fun i => x i + Real.sqrt v * z i))
      (piGauss n) := by
    refine Integrable.mono ((integrable_const (C + D * l1 x)).add
        (integrable_l1.const_mul (D * Real.sqrt v)))
      ((hmeas u₀ hu₀).comp (measurable_shift v x)).aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (shift_bound_pi hD (hb u₀ hu₀) x v z).trans (le_abs_self _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => A u (fun i => x i + Real.sqrt v * z i))
    (F' := fun u z => A' u (fun i => x i + Real.sqrt v * z i))
    (bound := fun z => (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z)
    (s := s) hs ?_ hA0 ?_ ?_ hbint ?_).2
  · filter_upwards [hs] with u hu
    exact ((hmeas u hu).comp (measurable_shift v x)).aestronglyMeasurable
  · exact ((hmeas' u₀ hu₀).comp (measurable_shift v x)).aestronglyMeasurable
  · filter_upwards with z u hu
    rw [Real.norm_eq_abs]
    exact shift_bound_pi hD' (hb' u hu) x v z
  · filter_upwards with z u hu
    exact hderiv u hu _

/-- **The `m ≠ 0` branch, inner step.** -/
theorem hasDerivAt_integral_exp_param_pi (x : Fin n → ℝ) {u₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 u₀)
    (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u ∈ s, Measurable (A u)) (hmeas' : ∀ u ∈ s, Measurable (A' u))
    (hb : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u ∈ s, ∀ y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => ∫ z, Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))
      (∫ z, m * (A' u₀ (fun i => x i + Real.sqrt v * z i)
        * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i))) ∂(piGauss n)) u₀ := by
  classical
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  have hC' : 0 ≤ C' := by
    have h0 := hb' u₀ hu₀ 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  set K : ℝ := Real.exp (|m| * (C + D * l1 x)) with hK
  set a0 : ℝ := |m| * (C' + D' * l1 x) * K with ha0
  set b0 : ℝ := |m| * (D' * Real.sqrt v) * K with hb0
  set c0 : ℝ := |m| * (D * Real.sqrt v) with hc0
  have hKpos : 0 < K := Real.exp_pos _
  have ha0n : 0 ≤ a0 := by rw [ha0]; positivity
  have hb0n : 0 ≤ b0 := by rw [hb0]; positivity
  have hc0n : 0 ≤ c0 := by rw [hc0]; positivity
  have hbint : Integrable (fun z : Fin n → ℝ => (a0 + b0 * l1 z) * Real.exp (c0 * l1 z))
      (piGauss n) := integrable_poly_mul_exp_l1 ha0n hb0n hc0n
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
    (F' := fun u z => m * (A' u (fun i => x i + Real.sqrt v * z i)
      * Real.exp (m * A u (fun i => x i + Real.sqrt v * z i))))
    (bound := fun z => (a0 + b0 * l1 z) * Real.exp (c0 * l1 z))
    (s := s) hs ?_ (integrable_exp_shift_pi hD (hb u₀ hu₀) (hmeas u₀ hu₀) x) ?_ ?_
    hbint ?_).2
  · filter_upwards [hs] with u hu
    exact (Real.continuous_exp.measurable.comp
      (((hmeas u hu).comp (measurable_shift v x)).const_mul m)).aestronglyMeasurable
  · exact ((((hmeas' u₀ hu₀).comp (measurable_shift v x)).mul
      (Real.continuous_exp.measurable.comp
        (((hmeas u₀ hu₀).comp (measurable_shift v x)).const_mul m))).const_mul
      m).aestronglyMeasurable
  · filter_upwards with z u hu
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 := shift_bound_pi hD' (hb' u hu) x v z
    have h2 : Real.exp (m * A u (fun i => x i + Real.sqrt v * z i))
        ≤ K * Real.exp (c0 * l1 z) := by
      have hle : m * A u (fun i => x i + Real.sqrt v * z i)
          ≤ |m| * ((C + D * l1 x) + (D * Real.sqrt v) * l1 z) := by
        have hmm : m * A u (fun i => x i + Real.sqrt v * z i)
            ≤ |m| * |A u (fun i => x i + Real.sqrt v * z i)| := by
          rw [← abs_mul]; exact le_abs_self _
        have := mul_le_mul_of_nonneg_left (shift_bound_pi hD (hb u hu) x v z) (abs_nonneg m)
        linarith
      calc Real.exp (m * A u (fun i => x i + Real.sqrt v * z i))
          ≤ Real.exp (|m| * ((C + D * l1 x) + (D * Real.sqrt v) * l1 z)) :=
            Real.exp_le_exp.2 hle
        _ = K * Real.exp (c0 * l1 z) := by rw [hK, hc0, ← Real.exp_add]; ring_nf
    have hbn : (0 : ℝ) ≤ (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z :=
      le_trans (abs_nonneg _) h1
    calc |m| * (|A' u (fun i => x i + Real.sqrt v * z i)|
            * Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
        ≤ |m| * (((C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z)
            * (K * Real.exp (c0 * l1 z))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg m)
          exact mul_le_mul h1 h2 (Real.exp_pos _).le hbn
      _ = (a0 + b0 * l1 z) * Real.exp (c0 * l1 z) := by rw [ha0, hb0]; ring
  · filter_upwards with z u hu
    exact (((hderiv u hu _).const_mul m).exp).congr_deriv (by ring)

/--
**The tilted chain rule for one `N`-site cascade level** — Talagrand's
`∂_t F_{ℓ,t} = 𝔼_ℓ W_ℓ ∂_t F_{ℓ+1,t}`, the step iterated in (3.2).  Hypotheses are needed only
on a neighbourhood `s` of the differentiation point.
-/
theorem hasDerivAt_parisiStepPi_param (x : Fin n → ℝ) {u₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 u₀)
    (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hderiv : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hmeas : ∀ u ∈ s, Measurable (A u)) (hmeas' : ∀ u ∈ s, Measurable (A' u))
    (hb : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hb' : ∀ u ∈ s, ∀ y, |A' u y| ≤ C' + D' * l1 y) :
    HasDerivAt (fun u => parisiStepPi n m v (A u) x)
      (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
        * tiltWeightPi n m v (A u₀) x z ∂(piGauss n)) u₀ := by
  classical
  have hu₀ : u₀ ∈ s := mem_of_mem_nhds hs
  by_cases hm : m = 0
  · have hfun : (fun u => parisiStepPi n m v (A u) x)
        = fun u => ∫ z, A u (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext u; rw [parisiStepPi, if_pos hm]
    have hval : (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (A u₀) x z ∂(piGauss n))
        = ∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show A' u₀ (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v (A u₀) x z
          = A' u₀ (fun i => x i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun, hval]
    exact hasDerivAt_integral_param_pi x hs hD hD' hderiv hmeas hmeas' hb hb'
  · have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD (hb u₀ hu₀) (hmeas u₀ hu₀) x
    have hfun : (fun u => parisiStepPi n m v (A u) x)
        = fun u => (1 / m) * Real.log
            (∫ z, Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n)) := by
      funext u; rw [parisiStepPi, if_neg hm]
    have hI := hasDerivAt_integral_exp_param_pi (A := A) (A' := A') (m := m) (v := v)
      (C := C) (D := D) (C' := C') (D' := D') x hs hD hD' hderiv hmeas hmeas' hb hb'
    have hfin := (hI.log hIpos.ne').const_mul (1 / m)
    rw [hfun]
    refine hfin.congr_deriv ?_
    rw [integral_const_mul]
    rw [show (∫ z, A' u₀ (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (A u₀) x z ∂(piGauss n))
        = ∫ z, (A' u₀ (fun i => x i + Real.sqrt v * z i)
            * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
          ∂(piGauss n) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by
        show A' u₀ (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v (A u₀) x z
            = A' u₀ (fun i => x i + Real.sqrt v * z i)
              * Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * z i))
              / (∫ w, Real.exp (m * A u₀ (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
        rw [tiltWeightPi, if_neg hm, mul_div_assoc]))]
    rw [integral_div]
    field_simp

/-! ## 3. `ℓ¹` bookkeeping -/

theorem l1_add_le (x y : Fin n → ℝ) : l1 (x + y) ≤ l1 x + l1 y := by
  simp only [l1, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)

theorem l1_neg (x : Fin n → ℝ) : l1 (-x) = l1 x := by
  simp only [l1, Pi.neg_apply, abs_neg]

theorem l1_sub_le (x y : Fin n → ℝ) : l1 (x - y) ≤ l1 x + l1 y := by
  rw [sub_eq_add_neg]
  exact (l1_add_le x (-y)).trans (by rw [l1_neg])

theorem l1_const_smul (c : ℝ) (x : Fin n → ℝ) :
    l1 (fun i => c * x i) = |c| * l1 x := by
  simp only [l1, abs_mul, Finset.mul_sum]

/-- Jensen, `exp (∫ g) ≤ ∫ exp g`, against `piGauss n`. -/
theorem exp_integral_le_integral_exp_pi {g : (Fin n → ℝ) → ℝ}
    (hg : Integrable g (piGauss n))
    (hexp : Integrable (fun z => Real.exp (g z)) (piGauss n)) :
    Real.exp (∫ z, g z ∂(piGauss n)) ≤ ∫ z, Real.exp (g z) ∂(piGauss n) := by
  have hpos : 0 < ∫ z, Real.exp (g z) ∂(piGauss n) := integral_exp_pos hexp
  have hlogint : Integrable (fun z => Real.log (Real.exp (g z))) (piGauss n) := by
    refine hg.congr ?_
    filter_upwards with z
    show g z = Real.log (Real.exp (g z))
    rw [Real.log_exp]
  have hJ := integral_log_le_log_integral (μ := piGauss n)
    (W := fun z => Real.exp (g z)) (fun z => Real.exp_pos _) hexp hlogint
  have hLHS : (∫ z, Real.log (Real.exp (g z)) ∂(piGauss n)) = ∫ z, g z ∂(piGauss n) := by
    have hfun : (fun z => Real.log (Real.exp (g z))) = g := by
      funext z; rw [Real.log_exp]
    rw [hfun]
  rw [hLHS] at hJ
  calc Real.exp (∫ z, g z ∂(piGauss n))
      ≤ Real.exp (Real.log (∫ z, Real.exp (g z) ∂(piGauss n))) := Real.exp_le_exp.2 hJ
    _ = _ := Real.exp_log hpos

/-- A function of `ℓ¹` growth, shifted, is integrable. -/
theorem integrable_shift_pi {C D v : ℝ} (hD : 0 ≤ D) {B : (Fin n → ℝ) → ℝ}
    (hb : ∀ y, |B y| ≤ C + D * l1 y) (hmeas : Measurable B) (x : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => B (fun i => x i + Real.sqrt v * z i)) (piGauss n) := by
  refine Integrable.mono ((integrable_const (C + D * l1 x)).add
      (integrable_l1.const_mul (D * Real.sqrt v)))
    (hmeas.comp (measurable_shift v x)).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine (shift_bound_pi hD hb x v z).trans (le_abs_self _)

/-! ## 4. Non-expansiveness and `ℓ¹`-Lipschitzness of an `N`-site level -/

/-- One `N`-site level is non-expansive in the sup norm of the function being smoothed. -/
theorem parisiStepPi_dist_le {m v ε : ℝ} {A A' : (Fin n → ℝ) → ℝ} {C D C₂ D₂ : ℝ}
    (hD : 0 ≤ D) (hD₂ : 0 ≤ D₂)
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hA' : ∀ y, |A' y| ≤ C₂ + D₂ * l1 y)
    (hmA : Measurable A) (hmA' : Measurable A')
    (hε : ∀ y, |A y - A' y| ≤ ε) (x : Fin n → ℝ) :
    |parisiStepPi n m v A x - parisiStepPi n m v A' x| ≤ ε := by
  classical
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hε 0)
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]
    have h1 := integrable_shift_pi (v := v) hD hA hmA x
    have h2 := integrable_shift_pi (v := v) hD₂ hA' hmA' x
    rw [← integral_sub h1 h2]
    calc |∫ z, (A (fun i => x i + Real.sqrt v * z i) - A' (fun i => x i + Real.sqrt v * z i))
            ∂(piGauss n)|
        ≤ ∫ z, |A (fun i => x i + Real.sqrt v * z i) - A' (fun i => x i + Real.sqrt v * z i)|
            ∂(piGauss n) := abs_integral_le_integral_abs
      _ ≤ ∫ _z, ε ∂(piGauss n) :=
          integral_mono (h1.sub h2).abs (integrable_const _) (fun z => hε _)
      _ = ε := by rw [integral_const, probReal_univ, one_smul]
  · simp only [parisiStepPi, if_neg hm]
    have hI := integrable_exp_shift_pi (m := m) (v := v) hD hA hmA x
    have hI' := integrable_exp_shift_pi (m := m) (v := v) hD₂ hA' hmA' x
    have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD hA hmA x
    have hI'pos := integral_exp_shift_pi_pos (m := m) (v := v) hD₂ hA' hmA' x
    -- pointwise: `e^{mA} ≤ e^{|m|ε} e^{mA'}` and symmetrically
    have hpt : ∀ z : Fin n → ℝ, Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
        ≤ Real.exp (|m| * ε) * Real.exp (m * A' (fun i => x i + Real.sqrt v * z i)) := by
      intro z
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h := hε (fun i => x i + Real.sqrt v * z i)
      have h2 : m * A (fun i => x i + Real.sqrt v * z i) - m * A' (fun i => x i + Real.sqrt v * z i)
          ≤ |m| * ε := by
        rw [← mul_sub]
        calc m * (A _ - A' _) ≤ |m * (A _ - A' _)| := le_abs_self _
          _ = |m| * |A _ - A' _| := abs_mul _ _
          _ ≤ |m| * ε := mul_le_mul_of_nonneg_left h (abs_nonneg m)
      linarith
    have hpt' : ∀ z : Fin n → ℝ, Real.exp (m * A' (fun i => x i + Real.sqrt v * z i))
        ≤ Real.exp (|m| * ε) * Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) := by
      intro z
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h := hε (fun i => x i + Real.sqrt v * z i)
      rw [abs_sub_comm] at h
      have h2 : m * A' (fun i => x i + Real.sqrt v * z i) - m * A (fun i => x i + Real.sqrt v * z i)
          ≤ |m| * ε := by
        rw [← mul_sub]
        calc m * (A' _ - A _) ≤ |m * (A' _ - A _)| := le_abs_self _
          _ = |m| * |A' _ - A _| := abs_mul _ _
          _ ≤ |m| * ε := mul_le_mul_of_nonneg_left h (abs_nonneg m)
      linarith
    have hint1 : (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))
        ≤ Real.exp (|m| * ε) * ∫ z, Real.exp (m * A' (fun i => x i + Real.sqrt v * z i))
            ∂(piGauss n) := by
      rw [← integral_const_mul]
      exact integral_mono hI (hI'.const_mul _) hpt
    have hint2 : (∫ z, Real.exp (m * A' (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))
        ≤ Real.exp (|m| * ε) * ∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
            ∂(piGauss n) := by
      rw [← integral_const_mul]
      exact integral_mono hI' (hI.const_mul _) hpt'
    have hlog1 := Real.log_le_log hIpos hint1
    have hlog2 := Real.log_le_log hI'pos hint2
    rw [Real.log_mul (Real.exp_pos _).ne' hI'pos.ne', Real.log_exp] at hlog1
    rw [Real.log_mul (Real.exp_pos _).ne' hIpos.ne', Real.log_exp] at hlog2
    have hmpos : 0 < |m| := abs_pos.2 hm
    rw [← mul_sub, abs_mul, abs_div, abs_one, div_mul_eq_mul_div, one_mul, div_le_iff₀ hmpos]
    rw [abs_le]
    constructor <;> linarith

/-- One `N`-site level preserves `ℓ¹`-Lipschitzness. -/
theorem parisiStepPi_lipschitz {m v L : ℝ} {A : (Fin n → ℝ) → ℝ} {C D : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmA : Measurable A)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y')) (x x' : Fin n → ℝ) :
    |parisiStepPi n m v A x - parisiStepPi n m v A x'| ≤ L * l1 (x - x') := by
  classical
  set c : Fin n → ℝ := x' - x with hc
  have hshift : parisiStepPi n m v A x' = parisiStepPi n m v (fun y => A (y + c)) x := by
    rw [parisiStepPi_shift, hc, add_sub_cancel]
  rw [hshift]
  have hA' : ∀ y, |A (y + c)| ≤ (C + D * l1 c) + D * l1 y := by
    intro y
    refine (hA _).trans ?_
    have := l1_add_le y c
    nlinarith
  have hmA' : Measurable (fun y => A (y + c)) := hmA.comp (measurable_id.add_const c)
  have hε : ∀ y, |A y - A (y + c)| ≤ L * l1 c := by
    intro y
    refine (hLip y (y + c)).trans ?_
    rw [show y - (y + c) = -c by abel, l1_neg]
  have := parisiStepPi_dist_le (m := m) (v := v) hD hD hA hA' hmA hmA' hε x
  rw [hc, ← l1_neg, neg_sub] at this
  exact this

end ChainRule


/-! ## 5. The tilted weight of an `N`-site level is a bounded perturbation of `piGauss`

Port of `CascadeDeriv` §§4–5 to `N` sites, with `ℓ¹`-Lipschitzness in place of Lipschitzness.
-/

/-- `∫ ∑ᵢ |zᵢ| dπ`, the `ℓ¹` first moment of the `N`-site Gaussian. -/
noncomputable def l1Moment (n : ℕ) : ℝ := ∫ z, l1 z ∂(piGauss n)

theorem l1Moment_nonneg (n : ℕ) : 0 ≤ l1Moment n :=
  integral_nonneg (fun z => l1_nonneg z)

section TiltPi

variable {m v L C D : ℝ} {A : (Fin n → ℝ) → ℝ}

theorem measurable_tiltWeightPi (hmeas : Measurable A) (x : Fin n → ℝ) :
    Measurable (fun z => tiltWeightPi n m v A x z) := by
  unfold tiltWeightPi
  split
  · exact measurable_const
  · exact (Real.continuous_exp.measurable.comp
      ((hmeas.comp (measurable_shift v x)).const_mul m)).div measurable_const

theorem tiltWeightPi_nonneg (hD : 0 ≤ D) (hA : ∀ y, |A y| ≤ C + D * l1 y)
    (hmeas : Measurable A) (x z : Fin n → ℝ) : 0 ≤ tiltWeightPi n m v A x z := by
  unfold tiltWeightPi
  split
  · exact zero_le_one
  · exact div_nonneg (Real.exp_pos _).le
      (integral_exp_shift_pi_pos (m := m) (v := v) hD hA hmeas x).le

/-- The Lipschitz deviation of the shifted function. -/
theorem shift_dev_pi (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y')) (x : Fin n → ℝ) (v : ℝ)
    (z : Fin n → ℝ) :
    |A (fun i => x i + Real.sqrt v * z i) - A x| ≤ L * (Real.sqrt v * l1 z) := by
  refine (hLip _ _).trans ?_
  have : (fun i => x i + Real.sqrt v * z i) - x = fun i => Real.sqrt v * z i := by
    funext i; simp only [Pi.sub_apply]; ring
  rw [this, l1_const_smul, abs_of_nonneg (Real.sqrt_nonneg v)]

/-- For an `ℓ¹`-`L`-Lipschitz `A`, the tilted weight is dominated by
`e^{c·l1Moment}·e^{c·l1 z}` with `c = |m|L√v` — independently of `x`. -/
theorem tiltWeightPi_le (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y'))
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmeas : Measurable A) (x z : Fin n → ℝ) :
    tiltWeightPi n m v A x z
      ≤ Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
        * Real.exp ((|m| * L * Real.sqrt v) * l1 z) := by
  classical
  set c : ℝ := |m| * L * Real.sqrt v with hc
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  have hM := l1Moment_nonneg n
  by_cases hm : m = 0
  · rw [tiltWeightPi, if_pos hm]
    have h1 : (1 : ℝ) ≤ Real.exp (c * l1Moment n) := Real.one_le_exp (by positivity)
    have h2 : (1 : ℝ) ≤ Real.exp (c * l1 z) := Real.one_le_exp (mul_nonneg hcnn (l1_nonneg z))
    nlinarith
  · rw [tiltWeightPi, if_neg hm]
    have hnum : Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
        ≤ Real.exp (m * A x) * Real.exp (c * l1 z) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h2 : m * A (fun i => x i + Real.sqrt v * z i) - m * A x
          ≤ |m| * |A (fun i => x i + Real.sqrt v * z i) - A x| := by
        rw [← mul_sub, ← abs_mul]; exact le_abs_self _
      have h3 := mul_le_mul_of_nonneg_left (shift_dev_pi hLip x v z) (abs_nonneg m)
      have h4 : |m| * (L * (Real.sqrt v * l1 z)) = c * l1 z := by rw [hc]; ring
      linarith
    have hAint : Integrable (fun w => m * A (fun i => x i + Real.sqrt v * w i)) (piGauss n) :=
      (integrable_shift_pi (v := v) hD hA hmeas x).const_mul m
    have hexpint : Integrable (fun w => Real.exp (m * A (fun i => x i + Real.sqrt v * w i)))
        (piGauss n) := integrable_exp_shift_pi hD hA hmeas x
    have hmean : Real.exp (m * A x) * Real.exp (-(c * l1Moment n))
        ≤ ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n) := by
      refine le_trans ?_ (exp_integral_le_integral_exp_pi hAint hexpint)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hlow : (∫ w, (m * A x - c * l1 w) ∂(piGauss n))
          ≤ ∫ w, m * A (fun i => x i + Real.sqrt v * w i) ∂(piGauss n) := by
        refine integral_mono ((integrable_const _).sub (integrable_l1.const_mul c)) hAint ?_
        intro w
        have h2 : |m * A (fun i => x i + Real.sqrt v * w i) - m * A x|
            ≤ |m| * (L * (Real.sqrt v * l1 w)) := by
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_left (shift_dev_pi hLip x v w) (abs_nonneg m)
        have h3 := (abs_le.1 h2).1
        have h4 : |m| * (L * (Real.sqrt v * l1 w)) = c * l1 w := by rw [hc]; ring
        show m * A x - c * l1 w ≤ m * A (fun i => x i + Real.sqrt v * w i)
        linarith
      have hcalc : (∫ w, (m * A x - c * l1 w) ∂(piGauss n)) = m * A x - c * l1Moment n := by
        rw [integral_sub (integrable_const _) (integrable_l1.const_mul c), integral_const,
          probReal_univ, one_smul, integral_const_mul, l1Moment]
      rw [hcalc] at hlow
      linarith
    have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD hA hmeas x
    rw [div_le_iff₀ hIpos]
    calc Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
        ≤ Real.exp (m * A x) * Real.exp (c * l1 z) := hnum
      _ = (Real.exp (c * l1Moment n) * Real.exp (c * l1 z))
            * (Real.exp (m * A x) * Real.exp (-(c * l1Moment n))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ ≤ (Real.exp (c * l1Moment n) * Real.exp (c * l1 z))
            * (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)) :=
          mul_le_mul_of_nonneg_left hmean (by positivity)

/-- Anything of `ℓ¹` growth is integrable against the tilted weight. -/
theorem integrable_mul_tiltWeightPi_of_bound (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y'))
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmeas : Measurable A) (x : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hfmeas : Measurable f) {a b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ z, |f z| ≤ a + b * l1 z) :
    Integrable (fun z => f z * tiltWeightPi n m v A x z) (piGauss n) := by
  classical
  have ha : 0 ≤ a := by
    have h0 := hf 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  set c : ℝ := |m| * L * Real.sqrt v with hc
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  set K : ℝ := Real.exp (c * l1Moment n) with hK
  have hKpos : 0 < K := Real.exp_pos _
  have hdom : Integrable (fun z : Fin n → ℝ => (a * K + (b * K) * l1 z) * Real.exp (c * l1 z))
      (piGauss n) :=
    integrable_poly_mul_exp_l1 (mul_nonneg ha hKpos.le) (mul_nonneg hb hKpos.le) hcnn
  refine Integrable.mono hdom (hfmeas.mul (measurable_tiltWeightPi hmeas x)).aestronglyMeasurable ?_
  filter_upwards with z
  have hW := tiltWeightPi_le (m := m) (v := v) hL hD hLip hA hmeas x z
  have hWnn := tiltWeightPi_nonneg (m := m) (v := v) hD hA hmeas x z
  have hane : 0 ≤ a + b * l1 z := le_trans (abs_nonneg _) (hf z)
  have hnn : (0 : ℝ) ≤ (a * K + (b * K) * l1 z) * Real.exp (c * l1 z) := by
    have h1 : 0 ≤ a * K := mul_nonneg ha hKpos.le
    have h2 : 0 ≤ (b * K) * l1 z := mul_nonneg (mul_nonneg hb hKpos.le) (l1_nonneg z)
    have h3 : 0 ≤ Real.exp (c * l1 z) := (Real.exp_pos _).le
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  calc |f z| * |tiltWeightPi n m v A x z|
      = |f z| * tiltWeightPi n m v A x z := by rw [abs_of_nonneg hWnn]
    _ ≤ (a + b * l1 z) * (K * Real.exp (c * l1 z)) := mul_le_mul (hf z) hW hWnn hane
    _ = (a * K + (b * K) * l1 z) * Real.exp (c * l1 z) := by ring

/-- The tilted weight is a probability density. -/
theorem tiltWeightPi_integral_one (hD : 0 ≤ D) (hA : ∀ y, |A y| ≤ C + D * l1 y)
    (hmeas : Measurable A) (x : Fin n → ℝ) :
    (∫ z, tiltWeightPi n m v A x z ∂(piGauss n)) = 1 := by
  classical
  by_cases hm : m = 0
  · have hfun : (fun z : Fin n → ℝ => tiltWeightPi n m v A x z) = fun _ => (1 : ℝ) := by
      funext z; rw [tiltWeightPi, if_pos hm]
    rw [hfun, integral_const, probReal_univ, one_smul]
  · have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD hA hmeas x
    have hfun : (fun z : Fin n → ℝ => tiltWeightPi n m v A x z)
        = fun z => Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
            / (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)) := by
      funext z; rw [tiltWeightPi, if_neg hm]
    rw [hfun, integral_div, div_self hIpos.ne']

/-- Hence the tilted `ℓ¹` first moment is bounded independently of `x`. -/
theorem integral_l1_mul_tiltWeightPi_le (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y'))
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmeas : Measurable A) (x : Fin n → ℝ) :
    (∫ z, l1 z * tiltWeightPi n m v A x z ∂(piGauss n))
      ≤ Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
        * ∫ z, l1 z * Real.exp ((|m| * L * Real.sqrt v) * l1 z) ∂(piGauss n) := by
  classical
  set c : ℝ := |m| * L * Real.sqrt v with hc
  have hcnn : 0 ≤ c := by rw [hc]; positivity
  have hint : Integrable (fun z => l1 z * tiltWeightPi n m v A x z) (piGauss n) :=
    integrable_mul_tiltWeightPi_of_bound (m := m) (v := v) hL hD hLip hA hmeas x measurable_l1
      (a := 0) (b := 1) zero_le_one (fun z => by rw [abs_of_nonneg (l1_nonneg z)]; linarith)
  have hdom : Integrable (fun z : Fin n → ℝ =>
      Real.exp (c * l1Moment n) * (l1 z * Real.exp (c * l1 z))) (piGauss n) := by
    have := integrable_poly_mul_exp_l1 (n := n) (a := 0) (b := 1) (c := c) le_rfl zero_le_one hcnn
    refine (this.const_mul (Real.exp (c * l1Moment n))).congr ?_
    filter_upwards with z
    show Real.exp (c * l1Moment n) * ((0 + 1 * l1 z) * Real.exp (c * l1 z))
        = Real.exp (c * l1Moment n) * (l1 z * Real.exp (c * l1 z))
    ring
  calc (∫ z, l1 z * tiltWeightPi n m v A x z ∂(piGauss n))
      ≤ ∫ z, Real.exp (c * l1Moment n) * (l1 z * Real.exp (c * l1 z)) ∂(piGauss n) := by
        refine integral_mono hint hdom (fun z => ?_)
        have hW := tiltWeightPi_le (m := m) (v := v) hL hD hLip hA hmeas x z
        have hz := l1_nonneg z
        nlinarith [Real.exp_pos (c * l1Moment n), Real.exp_pos (c * l1 z)]
    _ = _ := by rw [integral_const_mul]

/-- **One level preserves `ℓ¹` growth of the derivative.** -/
theorem abs_integral_mul_tiltWeightPi_le (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y'))
    (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmeas : Measurable A)
    {g : (Fin n → ℝ) → ℝ} (hgmeas : Measurable g) {C' D' : ℝ} (hD' : 0 ≤ D')
    (hg : ∀ y, |g y| ≤ C' + D' * l1 y) (x : Fin n → ℝ) :
    |∫ z, g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z ∂(piGauss n)|
      ≤ (C' + D' * l1 x)
        + (D' * Real.sqrt v)
          * (Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
              * ∫ z, l1 z * Real.exp ((|m| * L * Real.sqrt v) * l1 z) ∂(piGauss n)) := by
  classical
  have hDv : 0 ≤ D' * Real.sqrt v := mul_nonneg hD' (Real.sqrt_nonneg v)
  have hshift : ∀ z : Fin n → ℝ, |g (fun i => x i + Real.sqrt v * z i)|
      ≤ (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z := fun z => shift_bound_pi hD' hg x v z
  have hbnn : ∀ z : Fin n → ℝ, 0 ≤ (C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z :=
    fun z => le_trans (abs_nonneg _) (hshift z)
  have hWnn : ∀ z, 0 ≤ tiltWeightPi n m v A x z :=
    fun z => tiltWeightPi_nonneg (m := m) (v := v) hD hA hmeas x z
  have hgW : Integrable
      (fun z => g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z) (piGauss n) :=
    integrable_mul_tiltWeightPi_of_bound hL hD hLip hA hmeas x
      (hgmeas.comp (measurable_shift v x)) hDv hshift
  have hbW : Integrable
      (fun z => ((C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) * tiltWeightPi n m v A x z)
      (piGauss n) :=
    integrable_mul_tiltWeightPi_of_bound hL hD hLip hA hmeas x
      (measurable_const.add (measurable_l1.const_mul _)) hDv
      (fun z => le_of_eq (abs_of_nonneg (hbnn z)))
  have hzW : Integrable (fun z => l1 z * tiltWeightPi n m v A x z) (piGauss n) :=
    integrable_mul_tiltWeightPi_of_bound (m := m) (v := v) hL hD hLip hA hmeas x measurable_l1
      (a := 0) (b := 1) zero_le_one (fun z => by rw [abs_of_nonneg (l1_nonneg z)]; linarith)
  have hWint : Integrable (fun z => tiltWeightPi n m v A x z) (piGauss n) := by
    have h := integrable_mul_tiltWeightPi_of_bound (m := m) (v := v) hL hD hLip hA hmeas x
      (measurable_const : Measurable (fun _ : Fin n → ℝ => (1 : ℝ)))
      (a := 1) (b := 0) (le_refl (0 : ℝ))
      (fun z => by rw [abs_one]; linarith [l1_nonneg z])
    simpa using h
  calc |∫ z, g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z ∂(piGauss n)|
      ≤ ∫ z, |g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z| ∂(piGauss n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, ((C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) * tiltWeightPi n m v A x z
          ∂(piGauss n) := by
        refine integral_mono hgW.abs hbW (fun z => ?_)
        rw [abs_mul, abs_of_nonneg (hWnn z)]
        exact mul_le_mul_of_nonneg_right (hshift z) (hWnn z)
    _ = (C' + D' * l1 x) * (∫ z, tiltWeightPi n m v A x z ∂(piGauss n))
          + (D' * Real.sqrt v) * ∫ z, l1 z * tiltWeightPi n m v A x z ∂(piGauss n) := by
        rw [show (fun z : Fin n → ℝ =>
              ((C' + D' * l1 x) + (D' * Real.sqrt v) * l1 z) * tiltWeightPi n m v A x z)
            = fun z => (C' + D' * l1 x) * tiltWeightPi n m v A x z
              + (D' * Real.sqrt v) * (l1 z * tiltWeightPi n m v A x z) from
          funext (fun z => by ring)]
        rw [integral_add (hWint.const_mul _) (hzW.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        rw [tiltWeightPi_integral_one (m := m) (v := v) hD hA hmeas, mul_one]
        have hmom := integral_l1_mul_tiltWeightPi_le (m := m) (v := v) hL hD hLip hA hmeas x
        have := mul_le_mul_of_nonneg_left hmom hDv
        linarith

end TiltPi

/-! ## 6. `ℓ¹` growth of an `N`-site level, for `0 ≤ m` -/

/-- The constant by which one level of the cascade enlarges the `ℓ¹` growth bound.  Depends
only on `m`, `v`, `D` (and `n`); for `m = 0` the first term vanishes since `1/0 = 0`. -/
noncomputable def stepK (n : ℕ) (m v D : ℝ) : ℝ :=
  (1 / m) * Real.log (∫ z, Real.exp (m * (D * Real.sqrt v) * l1 z) ∂(piGauss n))
    + (D * Real.sqrt v) * l1Moment n

/-- A level of the cascade keeps `ℓ¹` growth, with the explicit new constant `stepK`. -/
theorem parisiStepPi_abs_le {m v C D : ℝ} {A : (Fin n → ℝ) → ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (hD : 0 ≤ D) (hA : ∀ y, |A y| ≤ C + D * l1 y) (hmeas : Measurable A) :
    ∀ x, |parisiStepPi n m v A x| ≤ (C + stepK n m v D) + D * l1 x := by
  classical
  have hC : 0 ≤ C := by
    have h0 := hA 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at h0
    exact le_trans (abs_nonneg _) h0
  have hM := l1Moment_nonneg n
  -- the plain average is controlled by the `ℓ¹` moment
  have hmean : ∀ x : Fin n → ℝ,
      |∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)|
        ≤ (C + D * l1 x) + (D * Real.sqrt v) * l1Moment n := by
    intro x
    have hint := integrable_shift_pi (v := v) hD hA hmeas x
    calc |∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)|
        ≤ ∫ z, |A (fun i => x i + Real.sqrt v * z i)| ∂(piGauss n) := abs_integral_le_integral_abs
      _ ≤ ∫ z, ((C + D * l1 x) + (D * Real.sqrt v) * l1 z) ∂(piGauss n) :=
          integral_mono hint.abs ((integrable_const _).add (integrable_l1.const_mul _))
            (fun z => shift_bound_pi hD hA x v z)
      _ = (C + D * l1 x) + (D * Real.sqrt v) * l1Moment n := by
          rw [integral_add (integrable_const _) (integrable_l1.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul, l1Moment]
  by_cases hm0 : m = 0
  · intro x
    have hK : stepK n m v D = (D * Real.sqrt v) * l1Moment n := by
      rw [stepK, hm0, div_zero, zero_mul, zero_add]
    rw [hK]
    simp only [parisiStepPi, if_pos hm0]
    have := hmean x
    linarith
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    set J : ℝ := ∫ z, Real.exp (m * (D * Real.sqrt v) * l1 z) ∂(piGauss n) with hJ
    have hJint : Integrable (fun z : Fin n → ℝ => Real.exp (m * (D * Real.sqrt v) * l1 z))
        (piGauss n) := integrable_exp_l1 _
    have hJge : 1 ≤ J := by
      have h1 : Real.exp (∫ z, m * (D * Real.sqrt v) * l1 z ∂(piGauss n)) ≤ J :=
        exp_integral_le_integral_exp_pi (integrable_l1.const_mul _) hJint
      have h2 : (1 : ℝ) ≤ Real.exp (∫ z, m * (D * Real.sqrt v) * l1 z ∂(piGauss n)) := by
        refine Real.one_le_exp ?_
        rw [integral_const_mul]
        exact mul_nonneg (by positivity) hM
      exact h2.trans h1
    have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJge
    have hK1 : 0 ≤ (1 / m) * Real.log J := mul_nonneg (by positivity) hlogJ
    have hK2 : 0 ≤ (D * Real.sqrt v) * l1Moment n :=
      mul_nonneg (mul_nonneg hD (Real.sqrt_nonneg v)) hM
    intro x
    have hK : stepK n m v D = (1 / m) * Real.log J + (D * Real.sqrt v) * l1Moment n := by
      rw [stepK, hJ]
    rw [hK]
    simp only [parisiStepPi, if_neg hm0]
    have hint := integrable_exp_shift_pi (m := m) (v := v) hD hA hmeas x
    have hIpos := integral_exp_shift_pi_pos (m := m) (v := v) hD hA hmeas x
    -- upper bound
    have hup : (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))
        ≤ Real.exp (m * (C + D * l1 x)) * J := by
      rw [hJ, ← integral_const_mul]
      refine integral_mono hint (hJint.const_mul _) (fun z => ?_)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : m * A (fun i => x i + Real.sqrt v * z i)
          ≤ m * ((C + D * l1 x) + (D * Real.sqrt v) * l1 z) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (shift_bound_pi hD hA x v z)) hm
      linarith
    have hup' : (1 / m) * Real.log (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
          ∂(piGauss n)) ≤ (C + D * l1 x) + (1 / m) * Real.log J := by
      have := Real.log_le_log hIpos hup
      rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at this
      have hm1 : 0 < 1 / m := by positivity
      calc (1 / m) * Real.log (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
              ∂(piGauss n))
          ≤ (1 / m) * (m * (C + D * l1 x) + Real.log J) := mul_le_mul_of_nonneg_left this hm1.le
        _ = (C + D * l1 x) + (1 / m) * Real.log J := by field_simp
    -- lower bound (Jensen)
    have hlow : ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)
        ≤ (1 / m) * Real.log (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i))
          ∂(piGauss n)) := by
      have hAint := integrable_shift_pi (v := v) hD hA hmeas x
      have h := exp_integral_le_integral_exp_pi (hAint.const_mul m) hint
      have h2 := Real.log_le_log (Real.exp_pos _) h
      rw [Real.log_exp, integral_const_mul] at h2
      have hm1 : 0 < 1 / m := by positivity
      calc ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)
          = (1 / m) * (m * ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)) := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hm1.le
    have hmx := hmean x
    rw [abs_le] at hmx ⊢
    constructor
    · linarith [hmx.1, hlow, hK1]
    · linarith [hup', hK2]

end Targets
end SpinGlass
