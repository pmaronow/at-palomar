module

/-
# The `t = 0` endpoint of Guerra's RSB interpolation

New work for the ParisiFormula project (not vendored).

## What this file is for

Target 3 (Guerra's bound) for a `k`-step scheme interpolates between the SK Hamiltonian and
a comparison field organised along a `(k+2)`-level cascade. The general finite-`k` bound
is now proved in `Targets/Talagrand.lean`, using the endpoint evaluation here and the
assembled Theorem 2.1 identity. The earlier `k = 0` result (`Targets.guerra_rs_bound`)
uses RSAT's smart path against a single Gaussian.

**This file does the endpoint.**  The point is that at `t = 0` the comparison Hamiltonian is

  `H(σ) = ∑_i σ_i (∑_p z_p^i) + h ∑_i σ_i`,

a sum over sites of *independent* terms, so the entire `(k+2)`-fold recursion

  `X_{k+1} = log ∑_σ exp (H σ)`,   `X_p = (1/m_p) log 𝔼_p exp (m_p X_{p+1})`

**factorises over sites**, and the one-dimensional recursion that survives is exactly
`Targets.parisiF`.  Concretely `X_0 = N · (log 2 + parisiF s β (k+2) h)`.

Two ingredients, both elementary:

* `spinSum_exp` — summing `exp` over `Config N = Fin N → Bool` factorises into
  `∏ i, 2 cosh (c i)`, so the innermost level contributes `N log 2 + ∑ i, log cosh (c i)`;
* `parisiStepPi_sum` — one smoothing step in `N` independent Gaussian coordinates, applied
  to a function of the form `y ↦ ∑ i, a (y i)`, is `∑ i, parisiStep m v a (x i)`.  For
  `m ≠ 0` this is Fubini for products (`integral_fintype_prod_eq_prod`) plus
  `log (∏ …) = ∑ log …`; for `m = 0` it is linearity of the integral plus the fact that a
  coordinate marginal of `Measure.pi` is the factor.

Iterating the second gives `parisiFPi_eq`, and combining with the first gives the endpoint.

Nothing here is deep; the content is the bookkeeping that turns the `N`-site cascade into
`N` copies of the one-dimensional recursion already built in `Targets/Milestones.lean`.
-/
public import Targets.Milestones

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

/-! ## 1. The `N`-fold standard Gaussian -/

/-- `N` independent standard Gaussians. -/
noncomputable abbrev piGauss (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

instance instIsProbabilityMeasurePiGauss (n : ℕ) : IsProbabilityMeasure (piGauss n) := by
  unfold piGauss; infer_instance

/-- The `i`-th coordinate marginal of `piGauss n` is the standard Gaussian. -/
theorem piGauss_map_eval {n : ℕ} (i : Fin n) :
    (piGauss n).map (Function.eval i) = gaussianReal 0 1 := by
  classical
  rw [piGauss, Measure.pi_map_eval]
  simp

theorem integrable_piGauss_eval {n : ℕ} (i : Fin n) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun z : Fin n → ℝ => f (z i)) (piGauss n) := by
  have hmap : Integrable f ((piGauss n).map (Function.eval i)) := by
    rwa [piGauss_map_eval]
  have := (integrable_map_measure hmap.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 hmap
  exact this

theorem integral_piGauss_eval {n : ℕ} (i : Fin n) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    (∫ z, f (z i) ∂(piGauss n)) = ∫ t, f t ∂(gaussianReal 0 1) := by
  have hf' : AEStronglyMeasurable f ((piGauss n).map (Function.eval i)) := by
    rwa [piGauss_map_eval]
  have h := integral_map (μ := piGauss n)
    (φ := (Function.eval i : (Fin n → ℝ) → ℝ)) (f := f)
    (measurable_pi_apply i).aemeasurable hf'
  rw [piGauss_map_eval] at h
  exact h.symm

/-! ## 2. One smoothing step in `N` independent coordinates -/

/--
The `N`-site smoothing operator: the same `(1/m) log 𝔼 exp (m ·)` (and its `m = 0` limit
`𝔼`) as `Targets.parisiStep`, but averaging over `N` independent Gaussian coordinates at
once.  This is one level of the Guerra cascade at fixed `t = 0`.
-/
noncomputable def parisiStepPi (n : ℕ) (m v : ℝ) (A : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  if m = 0 then
    ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)
  else
    (1 / m) * Real.log
      (∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n))

/--
**Site factorisation of one cascade level.**

Applied to a function that is a sum over sites of a single one-dimensional `a`, the `N`-site
smoothing step is the sum over sites of the one-dimensional step.  This is what collapses
the `N`-site cascade to `N` copies of `parisiF`.
-/
theorem parisiStepPi_sum {n : ℕ} (m v : ℝ) {a : ℝ → ℝ}
    (ha : HasLinearGrowth a) (hmeas : Measurable a) (x : Fin n → ℝ) :
    parisiStepPi n m v (fun y => ∑ i, a (y i)) x = ∑ i, parisiStep m v a (x i) := by
  classical
  by_cases hm : m = 0
  · -- `m = 0`: linearity of the integral, then the coordinate marginal
    simp only [parisiStepPi, parisiStep, if_pos hm]
    have hint : ∀ i : Fin n,
        Integrable (fun z : Fin n → ℝ => a (x i + Real.sqrt v * z i)) (piGauss n) := by
      intro i
      exact integrable_piGauss_eval i
        (integrable_of_hasLinearGrowth ha hmeas (x i) v)
    rw [show (fun z : Fin n → ℝ => ∑ i, a ((fun j => x j + Real.sqrt v * z j) i))
          = fun z : Fin n → ℝ => ∑ i, a (x i + Real.sqrt v * z i) from rfl,
      integral_finsetSum _ (fun i _ => hint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact integral_piGauss_eval i (fun t => a (x i + Real.sqrt v * t))
      (hmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add (x i))).aestronglyMeasurable
  · -- `m ≠ 0`: Fubini for products, then `log (∏ …) = ∑ log …`
    simp only [parisiStepPi, parisiStep, if_neg hm]
    have hprod : (∫ z, Real.exp (m * ∑ i, a (x i + Real.sqrt v * z i)) ∂(piGauss n))
        = ∏ i, ∫ t, Real.exp (m * a (x i + Real.sqrt v * t)) ∂(gaussianReal 0 1) := by
      have hpt : ∀ z : Fin n → ℝ,
          Real.exp (m * ∑ i, a (x i + Real.sqrt v * z i))
            = ∏ i, Real.exp (m * a (x i + Real.sqrt v * z i)) := by
        intro z
        rw [Finset.mul_sum, Real.exp_sum]
      rw [show (fun z : Fin n → ℝ => Real.exp (m * ∑ i, a (x i + Real.sqrt v * z i)))
            = fun z : Fin n → ℝ => ∏ i, Real.exp (m * a (x i + Real.sqrt v * z i)) from
          funext hpt]
      exact integral_fintype_prod_eq_prod
        (fun i (t : ℝ) => Real.exp (m * a (x i + Real.sqrt v * t)))
    have hpos : ∀ i : Fin n,
        0 < ∫ t, Real.exp (m * a (x i + Real.sqrt v * t)) ∂(gaussianReal 0 1) :=
      fun i => smoothing_integral_pos ha hmeas (x i)
    rw [show (fun z : Fin n → ℝ => Real.exp (m * ∑ i, a ((fun j => x j + Real.sqrt v * z j) i)))
          = fun z : Fin n → ℝ => Real.exp (m * ∑ i, a (x i + Real.sqrt v * z i)) from rfl,
      hprod, Real.log_prod (fun i _ => (hpos i).ne'), Finset.mul_sum]


/-! ## 3. Constants pass through a smoothing step -/

/-- `parisiStep` is equivariant for additive constants: `T (c + A) = c + T A`.  This is what
lets the `log 2` from the spin sum sit outside the whole cascade. -/
theorem parisiStep_const_add (c m v : ℝ) {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    parisiStep m v (fun t => c + A t) x = c + parisiStep m v A x := by
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm]
    rw [integral_add (integrable_const c) (integrable_of_hasLinearGrowth hA hmeas x v),
      integral_const, probReal_univ, one_smul]
  · simp only [parisiStep, if_neg hm]
    have hsplit : ∀ z : ℝ,
        Real.exp (m * (c + A (x + Real.sqrt v * z)))
          = Real.exp (m * c) * Real.exp (m * A (x + Real.sqrt v * z)) := by
      intro z; rw [← Real.exp_add]; ring_nf
    have hpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      smoothing_integral_pos hA hmeas x
    rw [show (fun z : ℝ => Real.exp (m * (c + A (x + Real.sqrt v * z))))
          = fun z : ℝ => Real.exp (m * c) * Real.exp (m * A (x + Real.sqrt v * z)) from
        funext hsplit,
      integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
    field_simp

/-- `c + A` still has linear growth. -/
theorem hasLinearGrowth_const_add (c : ℝ) {A : ℝ → ℝ} (hA : HasLinearGrowth A) :
    HasLinearGrowth (fun t => c + A t) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  refine ⟨|c| + C, D, by positivity, hD, fun y => ?_⟩
  calc |c + A y| ≤ |c| + |A y| := abs_add_le _ _
    _ ≤ |c| + (C + D * |y|) := by linarith [hb y]
    _ = |c| + C + D * |y| := by ring

/-! ## 4. Summing `exp` over spin configurations -/

/-- Summing `exp (∑ᵢ σᵢ cᵢ)` over all `2^n` configurations factorises into `∏ᵢ 2 cosh cᵢ`. -/
theorem spinSum_exp {n : ℕ} (c : Fin n → ℝ) :
    ∑ σ : Config n, Real.exp (∑ i, spin n σ i * c i) = ∏ i, (2 * Real.cosh (c i)) := by
  classical
  have hexp : ∀ σ : Config n,
      Real.exp (∑ i, spin n σ i * c i) = ∏ i, Real.exp (spin n σ i * c i) := by
    intro σ; rw [Real.exp_sum]
  rw [Finset.sum_congr rfl (fun σ _ => hexp σ)]
  have hpi : (∏ i, ∑ b : Bool, Real.exp ((if b then (1 : ℝ) else -1) * c i))
      = ∑ σ : Config n, ∏ i, Real.exp (spin n σ i * c i) := by
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    rfl
  rw [← hpi]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hT : (if (true : Bool) = true then (1 : ℝ) else -1) = 1 := by simp
  have hF : (if (false : Bool) = true then (1 : ℝ) else -1) = -1 := by simp
  rw [Fintype.sum_bool, hT, hF, Real.cosh_eq, one_mul, neg_one_mul]
  ring

/-- The spin sum, in logarithmic form: the innermost level of the cascade. -/
theorem log_spinSum_exp {n : ℕ} (c : Fin n → ℝ) :
    Real.log (∑ σ : Config n, Real.exp (∑ i, spin n σ i * c i))
      = ∑ i, Real.log (2 * Real.cosh (c i)) := by
  rw [spinSum_exp]
  exact Real.log_prod (fun i _ => by positivity)

/-! ## 5. The `N`-site cascade and its collapse -/

/--
The `N`-site Guerra cascade at `t = 0`.  Level `0` is the spin sum (`log ∑_σ exp …` after
`log_spinSum_exp`); each further level applies one `N`-site smoothing step with the same
parameters as `Targets.parisiF`.
-/
noncomputable def parisiFPi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) :
    ℕ → ((Fin n → ℝ) → ℝ)
  | 0 => fun y => ∑ i, Real.log (2 * Real.cosh (y i))
  | j + 1 =>
      parisiStepPi n (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
        (parisiFPi n s β j)

/--
**The `N`-site cascade collapses to `N` copies of the one-dimensional recursion.**

Every level of the `N`-site cascade is `∑ᵢ (log 2 + parisiF s β j (yᵢ))`.  This is the
endpoint computation Guerra's bound needs at `t = 0`: the comparison Hamiltonian is a sum
over sites of independent terms, so the whole `(k+2)`-fold recursion factorises and the
surviving one-dimensional recursion is exactly `parisiF`.
-/
theorem parisiFPi_eq {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) (y : Fin n → ℝ) :
    parisiFPi n s β j y = ∑ i, (Real.log 2 + parisiF s β j (y i)) := by
  induction j generalizing y with
  | zero =>
      show (∑ i, Real.log (2 * Real.cosh (y i))) = _
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show Real.log (2 * Real.cosh (y i)) = Real.log 2 + Real.log (Real.cosh (y i))
      exact Real.log_mul two_ne_zero (Real.cosh_pos _).ne'
  | succ j ih =>
      obtain ⟨hmeas, hgrow, -⟩ := parisiF_props s β j
      have hstep : parisiFPi n s β (j + 1) y
          = parisiStepPi n (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
              (parisiFPi n s β j) y := rfl
      have hfun : parisiFPi n s β j
          = fun w : Fin n → ℝ => ∑ i, (Real.log 2 + parisiF s β j (w i)) := by
        funext w; exact ih w
      rw [hstep, hfun,
        parisiStepPi_sum _ _ (hasLinearGrowth_const_add (Real.log 2) hgrow)
          (measurable_const.add hmeas) y]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [parisiStep_const_add _ _ _ hgrow hmeas]
      rfl

/--
**The `t = 0` endpoint of Guerra's interpolation.**

Evaluated at the constant configuration `h` (the external field), the top of the `N`-site
cascade is `N · (log 2 + parisiF s β (k+2) h)` — that is, `N` times the Parisi functional
before the `-(β²/4) ∑ …` correction term is subtracted.
-/
theorem parisiFPi_top {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) :
    parisiFPi n s β (k + 2) (fun _ => h)
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
  rw [parisiFPi_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/--
The endpoint in the form Guerra's bound consumes: `(1/N)` times the top of the cascade is
the Parisi functional plus the correction term that the interpolation's derivative supplies.
-/
theorem parisiFPi_top_eq_parisiFunctional {k : ℕ} (n : ℕ) (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) :
    (1 / (n : ℝ)) * parisiFPi n s β (k + 2) (fun _ => h)
      = parisiFunctional s β h
        + (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1),
            s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [parisiFPi_top, parisiFunctional]
  field_simp
  ring


/-! ## 6. Zero variance: the cascade collapses

At the `t = 1` end of Guerra's interpolation every level has variance
`(1-t)·β²(q_{p+1} - q_p) = 0`, so no smoothing happens at all and the whole `(k+2)`-fold
cascade is the identity.  That is the mechanism behind the second endpoint evaluation, and
it holds for either branch of `parisiStep`: for `m = 0` because the measure is a probability
measure, and for `m ≠ 0` because `(1/m) log exp (m c) = c`.
-/

/-- A smoothing step with zero variance does nothing. -/
@[simp] theorem parisiStep_zero_var (m : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    parisiStep m 0 A x = A x := by
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm, Real.sqrt_zero, zero_mul, add_zero]
    rw [integral_const, probReal_univ, one_smul]
  · simp only [parisiStep, if_neg hm, Real.sqrt_zero, zero_mul, add_zero]
    rw [integral_const, probReal_univ, one_smul, Real.log_exp]
    field_simp

/-- An `N`-site smoothing step with zero variance does nothing. -/
@[simp] theorem parisiStepPi_zero_var {n : ℕ} (m : ℝ) (A : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    parisiStepPi n m 0 A x = A x := by
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm, Real.sqrt_zero, zero_mul, add_zero]
    rw [integral_const, probReal_univ, one_smul]
  · simp only [parisiStepPi, if_neg hm, Real.sqrt_zero, zero_mul, add_zero]
    rw [integral_const, probReal_univ, one_smul, Real.log_exp]
    field_simp

/-! ## 7. The interpolating cascade

Guerra's interpolation carries two things that the `t = 0` cascade of §5 does not: an
arbitrary *base* function (at `t > 0` the innermost level is `log ∑_σ exp (√t·U(σ) + …)`,
which no longer factorises over sites once the SK field is present), and a *scale* on the
variances, namely `1 - t`.

`cascadeT` below is that general form.  Both endpoints are instances:

* `scale = 1` with the factorised base recovers `parisiFPi` — the `t = 0` endpoint of §5;
* `scale = 0` collapses to the base — the `t = 1` endpoint, `cascadeT_zero_scale`.

Keeping the base abstract means this definition commits to no Hamiltonian sign convention.
-/

/--
The interpolating cascade: `k+2` smoothing levels with the `parisiF` parameters, variances
scaled by `scale`, over an arbitrary base function.
-/
noncomputable def cascadeT {k : ℕ} (n : ℕ) (s : RSBScheme k) (β scale : ℝ)
    (base : (Fin n → ℝ) → ℝ) : ℕ → ((Fin n → ℝ) → ℝ)
  | 0 => base
  | j + 1 =>
      parisiStepPi n (s.m (k + 1 - j))
        (scale * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
        (cascadeT n s β scale base j)

/-- **The `t = 1` endpoint.**  At zero scale every level has zero variance, so the cascade
is the identity: `φ(1)` is just the base, i.e. the SK free energy. -/
theorem cascadeT_zero_scale {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (base : (Fin n → ℝ) → ℝ) (j : ℕ) (y : Fin n → ℝ) :
    cascadeT n s β 0 base j y = base y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      show parisiStepPi n (s.m (k + 1 - j))
        (0 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
        (cascadeT n s β 0 base j) y = base y
      rw [zero_mul, parisiStepPi_zero_var]
      exact ih y

/-- **The `t = 0` endpoint.**  At unit scale over the factorised base, `cascadeT` is the
cascade of §5, hence collapses to `N` copies of `parisiF`. -/
theorem cascadeT_one_scale {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) (y : Fin n → ℝ) :
    cascadeT n s β 1 (fun w => ∑ i, Real.log (2 * Real.cosh (w i))) j y
      = ∑ i, (Real.log 2 + parisiF s β j (y i)) := by
  rw [← parisiFPi_eq]
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      show parisiStepPi n (s.m (k + 1 - j))
          (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
          (cascadeT n s β 1 (fun w => ∑ i, Real.log (2 * Real.cosh (w i))) j) y
        = parisiStepPi n (s.m (k + 1 - j))
            (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) (parisiFPi n s β j) y
      rw [one_mul]
      congr 1
      funext w
      exact ih w


/-! ## 8. Constant base: the other route to the `t = 1` endpoint

Guerra's interpolation can be set up either by scaling the *variances* by `1 - t` (§7) or by
holding the variances fixed and scaling the Gaussian shift *inside the base*, i.e. taking

  `base_t(y) = log ∑_σ exp (√t·U(σ) + ∑_i σ_i (√(1-t)·y_i + h))`.

The second is more convenient for differentiating, since then `t` occurs in one place only.
In that formulation the `t = 1` endpoint is a *constant* base — `base_1` does not depend on
`y` at all, being `log Z_N` — and the cascade of a constant is that constant.
-/

/-- A smoothing step applied to a constant function returns it. -/
@[simp] theorem parisiStep_const (m v c : ℝ) (x : ℝ) :
    parisiStep m v (fun _ => c) x = c := by
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm]
    rw [integral_const, probReal_univ, one_smul]
  · simp only [parisiStep, if_neg hm]
    rw [integral_const, probReal_univ, one_smul, Real.log_exp]
    field_simp

/-- An `N`-site smoothing step applied to a constant function returns it. -/
@[simp] theorem parisiStepPi_const {n : ℕ} (m v c : ℝ) (x : Fin n → ℝ) :
    parisiStepPi n m v (fun _ => c) x = c := by
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]
    rw [integral_const, probReal_univ, one_smul]
  · simp only [parisiStepPi, if_neg hm]
    rw [integral_const, probReal_univ, one_smul, Real.log_exp]
    field_simp

/-- **The `t = 1` endpoint, fixed-variance formulation.**  The cascade over a base that does
not depend on the Gaussian coordinates is that base. -/
theorem cascadeT_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β scale c : ℝ) (j : ℕ)
    (y : Fin n → ℝ) :
    cascadeT n s β scale (fun _ => c) j y = c := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      show parisiStepPi n (s.m (k + 1 - j))
        (scale * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
        (cascadeT n s β scale (fun _ => c) j) y = c
      have hfun : cascadeT n s β scale (fun _ : Fin n → ℝ => c) j
          = fun _ : Fin n → ℝ => c := by
        funext w; exact ih w
      rw [hfun, parisiStepPi_const]

/-! ## 9. Translation -/

/-- Smoothing commutes with translation of the argument. -/
theorem parisiStepPi_shift {n : ℕ} (m v : ℝ) (A : (Fin n → ℝ) → ℝ) (c x : Fin n → ℝ) :
    parisiStepPi n m v (fun y => A (y + c)) x = parisiStepPi n m v A (x + c) := by
  have hpt : ∀ z : Fin n → ℝ,
      A ((fun i => x i + Real.sqrt v * z i) + c)
        = A (fun i => (x + c) i + Real.sqrt v * z i) := by
    intro z
    congr 1
    funext i
    simp only [Pi.add_apply]
    ring
  simp only [parisiStepPi, hpt]

/-- Hence so does the whole cascade. -/
theorem cascadeT_shift {k : ℕ} (n : ℕ) (s : RSBScheme k) (β scale : ℝ)
    (B : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) (j : ℕ) (x : Fin n → ℝ) :
    cascadeT n s β scale (fun y => B (y + c)) j x = cascadeT n s β scale B j (x + c) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      show parisiStepPi n (s.m (k + 1 - j))
          (scale * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
          (cascadeT n s β scale (fun y => B (y + c)) j) x
        = parisiStepPi n (s.m (k + 1 - j))
          (scale * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
          (cascadeT n s β scale B j) (x + c)
      have hfun : cascadeT n s β scale (fun y => B (y + c)) j
          = fun y => cascadeT n s β scale B j (y + c) := funext (fun y => ih y)
      rw [hfun, parisiStepPi_shift]

end Targets
end SpinGlass
