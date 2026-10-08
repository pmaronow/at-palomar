module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/-
# Core definitions and upper bound from Talagrand's §2, in Lean

New work for the ParisiFormula project (not vendored).

## What this file is

The foundational SK formalisation of Talagrand (Annals 2006) §2. Theorem 2.1,
Guerra's upper bound, and the deduction of the Parisi formula from an explicit
Theorem 2.2 hypothesis are proved here. The downstream Section 3--5 development
supplies that hypothesis; `Targets/TalagrandFinal.lean` exports the completed
canonical Theorem 2.2 and Parisi-formula declarations.

## The objects (Talagrand (2.1)–(2.4), (2.18))

* `guerraBase` — (2.2), `F_{k+1,t} = log ∑_σ exp H_t(σ)`, with the cascade Gaussians `y`
  left as a free argument;
* `guerraPhi` — (2.4), `φ(t) = (1/N) 𝔼 F_{1,t}`, obtained by pushing `guerraBase` through
  the `k+2` levels of `cascadeT` and averaging over the disorder.  As in (2.1), `√(1-t)`
  multiplies the cascade field *inside the base*, so the level variances are fixed and the
  tilted chain rule pushes `d/dt` straight to the base — Talagrand's (3.2);
* `guerraPsi` — (2.18), `ψ(t) = φ(0) - (t/2) ∑_ℓ m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))`.  For the SK
  model `ξ(x) = β²x²/2`, so `θ(q) = β²q²/2` and the sum is exactly the correction term of
  `parisiFunctional`; hence `ψ(1) = 𝒫_k(m,q)` on the nose (`guerraPsi_one`).

## The two cores

* `guerra_identity` — **Theorem 2.1** (Guerra's identity, (2.10)–(2.11)): on `(0,1)`,
  `φ'(t) = ψ'(t) - Rem(t)` with `0 ≤ Rem(t) ≤ β²`.  The remainder is
  `(β²/4) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ((R_{1,2} - q_ℓ)²)`, constructed as `guerraRemainder`.
  The theorem exposes its sign and size for downstream use. No `c(N)` error term appears: our
  covariance kernel is exactly `(Nβ²/2) R²`.
* The downstream Section 3--5 modules prove **Theorem 2.2**: for `t₀ < 1` there is
  `ε > 0` such that every `ε`-optimal fixed-level minimizer satisfies
  `φ_N(t) → ψ(t)` for every `t ≤ t₀`.

## The derivations

* `guerra_rsb_bound` (Target 3) from Theorem 2.1: `Rem ≥ 0` makes `φ - ψ` non-increasing, so
  `φ(1) ≤ ψ(1)`, i.e. `free_entropy ≤ 𝒫_k(m,q)`, via `guerraPhi_one`, `guerraPhi_zero`.
* `parisi_formula_of_theorem_2_2` (Target 4) derives the formula from an explicit
  Theorem 2.2 hypothesis together with Theorem 2.1 and the minimiser of Target 2b-i,
  exactly as Talagrand argues on p. 229–230. The final public module supplies the
  now-checked hypothesis.
-/
public import ParisiFormula.CoordStein
public import Targets.CascadeFieldPi
public import Targets.CascadeContinuityPi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped BigOperators NNReal

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## 1. Talagrand's (2.1)–(2.4): the interpolation

`t` enters **only through the base** — exactly as in (2.1), where `√(1-t)` multiplies the
cascade Gaussians — so that the level variances are fixed and the tilted chain rule of
`Targets/CascadeDeriv.lean` pushes `d/dt` straight down to the base, which is Talagrand's
(3.2).  The cascade is evaluated at `0`; the external field `h` sits inside `H_t`.
-/

/-- (2.1): `H_t(σ) = √t H(σ) + ∑_i σ_i (h + √(1-t) y_i)`, with the cascade field `y` free. -/
noncomputable def guerraH (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ)
    (σ : Config n) : ℝ :=
  Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)

/-- (2.2): `F_{k+1,t}(y) = log ∑_σ exp H_t(σ)`. -/
noncomputable def guerraBase (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, Real.exp (guerraH n U h t y σ))

/-- (2.4): `φ(t) = (1/N) 𝔼 F_{1,t}` — the base pushed through the `k+2` cascade levels (fixed
variances), evaluated at `0`, averaged over the disorder. -/
noncomputable def guerraPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, cascadeT n s β 1 (guerraBase n (U ω) h t) (k + 2) 0 ∂ℙ

/-- The correction term of the Parisi functional, `(1/2) ∑_ℓ m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))` with
`θ(q) = β²q²/2`. -/
noncomputable def parisiCorrection {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℝ :=
  (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)

/-- (2.18): `ψ(t) = φ(0) - t · (correction)`.  Written with the closed form of `φ(0)` so that
it is visibly independent of `N` and of the disorder. -/
noncomputable def guerraPsi {k : ℕ} (s : RSBScheme k) (β h t : ℝ) : ℝ :=
  Real.log 2 + parisiF s β (k + 2) h - t * parisiCorrection s β

/-! ## 2. Endpoints and elementary facts -/

theorem guerraPsi_one {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    guerraPsi s β h 1 = parisiFunctional s β h := by
  rw [guerraPsi, parisiCorrection, parisiFunctional, one_mul]

theorem parisiCorrection_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    0 ≤ parisiCorrection s β := by
  unfold parisiCorrection
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun p hp => ?_)
  rw [Finset.mem_range] at hp
  have hm := s.m_nonneg (p := p + 1) (by omega)
  have hq := s.q_mono (p + 1) (by omega)
  have hq0 := s.q_nonneg (p := p + 1) (by omega)
  exact mul_nonneg hm (by nlinarith)

theorem parisiCorrection_le {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiCorrection s β ≤ β ^ 2 / 4 := by
  unfold parisiCorrection
  have := sum_correction_le_one s
  have hb : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
  nlinarith

/-- At `t = 0` there is no interaction: the base is the spin sum of `CascadeEndpoint` §4,
translated by the external field. -/
theorem guerraBase_zero (n : ℕ) (U : EnergySpace n) (h : ℝ) :
    guerraBase n U h 0
      = fun y => (fun w : Fin n → ℝ => ∑ i, Real.log (2 * Real.cosh (w i)))
          (y + fun _ => h) := by
  funext y
  show guerraBase n U h 0 y = ∑ i, Real.log (2 * Real.cosh ((y + fun _ : Fin n => h) i))
  have hH : ∀ σ : Config n,
      guerraH n U h 0 y σ = ∑ i, spin n σ i * (y + fun _ : Fin n => h) i := by
    intro σ
    simp only [guerraH, Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul,
      Pi.add_apply]
  simp only [guerraBase, hH]
  exact log_spinSum_exp _

/-- At `t = 1` the base is `log Z_N`, independent of the cascade field. -/
theorem guerraBase_one (n : ℕ) (β : ℝ) (U : EnergySpace n) (h : ℝ) :
    guerraBase n U h 1 = fun _ => Real.log (skZ (N := n) (β := β) (h := h) U) := by
  funext y
  have hmag : ∀ σ : Config n, (∑ i, spin n σ i * h) = h * magnetization n σ := by
    intro σ
    rw [magnetization, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hH : ∀ σ : Config n, guerraH n U h 1 y σ = U σ + h * magnetization n σ := by
    intro σ
    simp only [guerraH, Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, zero_add]
    rw [hmag σ]
  simp only [guerraBase, hH, skZ_eq]

/-- **(2.14): `φ(0) = log 2 + X_0`.** -/
theorem guerraPhi_zero {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 0 = Real.log 2 + parisiF s β (k + 2) h := by
  have hfun : ∀ ω, cascadeT n s β 1 (guerraBase n (U ω) h 0) (k + 2) 0
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    intro ω
    rw [guerraBase_zero,
      cascadeT_shift n s β 1 (fun w : Fin n → ℝ => ∑ i, Real.log (2 * Real.cosh (w i)))
        (fun _ => h), zero_add, cascadeT_one_scale]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint : (∫ ω, cascadeT n s β 1 (guerraBase n (U ω) h 0) (k + 2) 0 ∂ℙ)
      = (n : ℝ) * (Real.log 2 + parisiF s β (k + 2) h) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun), integral_const, probReal_univ,
      one_smul]
  rw [guerraPhi, hint]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

/-- **The `t = 1` endpoint: `φ(1)` is the free entropy.** -/
theorem guerraPhi_one {k : ℕ} (n : ℕ) (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) :
    guerraPhi n s β h U 1 = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) U := by
  have hfun : ∀ ω, cascadeT n s β 1 (guerraBase n (U ω) h 1) (k + 2) 0
      = Real.log (skZ (N := n) (β := β) (h := h) (U ω)) := by
    intro ω
    rw [guerraBase_one n β, cascadeT_const]
  rw [guerraPhi, free_entropy, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  show (1 / (n : ℝ)) * cascadeT n s β 1 (guerraBase n (U ω) h 1) (k + 2) 0
      = free_energy_density (N := n) (skEnergy (N := n) (β := β) (h := h) (U ω))
  rw [hfun ω, free_energy_density]
  rfl

/-! ## 2b. The derivative of the base: `∂_t F_{k+1,t} = ⟨∂_t H_t⟩_t`

The first line of Talagrand's proof of Theorem 2.1 (§3, between (3.1) and (3.6)).  Since the
base is `log` of a *finite* sum of exponentials, its `t`-derivative is a finite Gibbs
average — no integration by parts is involved yet.  For `0 < t < 1`,

  `∂_t H_t(σ) = H(σ)/(2√t) - (∑_i σ_i y_i)/(2√(1-t))`,

and these two terms are what (3.7) calls `I` and (3.8) calls `∑_p II(p)`.
-/

/-- The finite Gibbs average `⟨f⟩ = ∑_σ f(σ) e^{E(σ)} / ∑_σ e^{E(σ)}` for the energy `E`
(Talagrand's `⟨·⟩_t` with `E = H_t`). -/
noncomputable def gibbsAvg {n : ℕ} (E f : Config n → ℝ) : ℝ :=
  (∑ σ, Real.exp (E σ) * f σ) / ∑ σ, Real.exp (E σ)

/-- `∂_t H_t(σ)` for `0 < t < 1`. -/
noncomputable def guerraHDeriv (n : ℕ) (U : EnergySpace n) (t : ℝ) (y : Fin n → ℝ)
    (σ : Config n) : ℝ :=
  U σ / (2 * Real.sqrt t) - (∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))

theorem hasDerivAt_guerraH (n : ℕ) (U : EnergySpace n) (h : ℝ) (y : Fin n → ℝ) (σ : Config n)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => guerraH n U h t y σ) (guerraHDeriv n U t y σ) t := by
  have ht0 : t ≠ 0 := ht.1.ne'
  have ht1 : 1 - t ≠ 0 := (sub_pos.2 ht.2).ne'
  have h1 : HasDerivAt (fun t => Real.sqrt t * U σ) (1 / (2 * Real.sqrt t) * U σ) t :=
    (Real.hasDerivAt_sqrt ht0).mul_const (U σ)
  have hs : HasDerivAt (fun t => Real.sqrt (1 - t)) (1 / (2 * Real.sqrt (1 - t)) * (-1)) t :=
    (Real.hasDerivAt_sqrt ht1).comp t ((hasDerivAt_id t).const_sub 1)
  have h2 : HasDerivAt (fun t => ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h))
      (∑ i, spin n σ i * (1 / (2 * Real.sqrt (1 - t)) * (-1) * y i)) t := by
    refine HasDerivAt.fun_sum (fun i _ => ?_)
    exact ((hs.mul_const (y i)).add_const h).const_mul _
  refine (h1.add h2).congr_deriv ?_
  unfold guerraHDeriv
  have hsum : (∑ i, spin n σ i * (1 / (2 * Real.sqrt (1 - t)) * (-1) * y i))
      = -((∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  ring

/-- **`∂_t F_{k+1,t} = ⟨∂_t H_t⟩_t`**: the derivative of the base is the Gibbs average of
`∂_t H_t`. -/
theorem hasDerivAt_guerraBase (n : ℕ) (U : EnergySpace n) (h : ℝ) (y : Fin n → ℝ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => guerraBase n U h t y)
      (gibbsAvg (guerraH n U h t y) (guerraHDeriv n U t y)) t := by
  have hsum : HasDerivAt (fun t => ∑ σ : Config n, Real.exp (guerraH n U h t y σ))
      (∑ σ : Config n, Real.exp (guerraH n U h t y σ) * guerraHDeriv n U t y σ) t :=
    HasDerivAt.fun_sum (fun σ _ => (hasDerivAt_guerraH n U h y σ ht).exp)
  have hpos : 0 < ∑ σ : Config n, Real.exp (guerraH n U h t y σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  exact hsum.log hpos.ne'

/-! ## 2b-i. Differentiating the base along the disorder

The disorder part of Gaussian integration by parts varies `U` along one basis direction.
This is the base case for pushing that line derivative through the cascade, just as
`hasDerivAt_guerraBase` is the base case for pushing the `t`-derivative through it.
-/

/-- The derivative of the base along the affine disorder line `U + u • V`.

The direction enters `guerraH` with coefficient `√t`, so the answer is `√t` times the
finite Gibbs average of `V` at the perturbed disorder.  No assumption on `t` is needed.
-/
noncomputable def guerraBaseUDeriv (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  Real.sqrt t * gibbsAvg (guerraH n U h t y) V

theorem hasDerivAt_guerraBase_Uline (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun u => guerraBase n (U + u • V) h t y)
      (guerraBaseUDeriv n (U + r • V) V h t y) r := by
  have hH : ∀ σ : Config n,
      HasDerivAt (fun u => guerraH n (U + u • V) h t y σ) (Real.sqrt t * V σ) r := by
    intro σ
    have heq : (fun u => guerraH n (U + u • V) h t y σ) =
        fun u => Real.sqrt t * U σ
          + u * (Real.sqrt t * V σ)
          + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h) := by
      funext u
      simp only [guerraH, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      congr 1
      ring
    rw [heq]
    simpa using (((hasDerivAt_const r (Real.sqrt t * U σ)).add
      ((hasDerivAt_id r).mul_const (Real.sqrt t * V σ))).add_const
        (∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)))
  have hsum : HasDerivAt
      (fun u => ∑ σ : Config n, Real.exp (guerraH n (U + u • V) h t y σ))
      (∑ σ : Config n,
        Real.exp (guerraH n (U + r • V) h t y σ) * (Real.sqrt t * V σ)) r :=
    HasDerivAt.fun_sum (fun σ _ => (hH σ).exp)
  have hpos : 0 < ∑ σ : Config n, Real.exp (guerraH n (U + r • V) h t y σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  refine (hsum.log hpos.ne').congr_deriv ?_
  unfold guerraBaseUDeriv
  unfold gibbsAvg
  have hnum :
      (∑ σ : Config n,
        Real.exp (guerraH n (U + r • V) h t y σ) * (Real.sqrt t * V σ)) =
        Real.sqrt t *
          ∑ σ : Config n, Real.exp (guerraH n (U + r • V) h t y σ) * V σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring
  rw [hnum]
  ring

/-! ## 2c. Bounds on the base and its derivative

What the level induction needs of `F_{k+1,t}`: measurability in `y`, `ℓ¹` growth with
constants uniform in `t ∈ [0,1]`, `ℓ¹`-Lipschitzness with constant `1`, and `ℓ¹` growth of
`∂_t F_{k+1,t}` with constants uniform for `t` away from the endpoints.  All elementary: the
base is `log` of a finite sum of exponentials.
-/

/-- `∂_t F_{k+1,t}` as a function of the cascade field. -/
noncomputable def guerraBaseDeriv (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) : ℝ :=
  gibbsAvg (guerraH n U h t y) (guerraHDeriv n U t y)

/-- `∑_σ |U σ|`, a crude size for the disorder. -/
noncomputable def uAbs (n : ℕ) (U : EnergySpace n) : ℝ := ∑ σ : Config n, |U σ|

theorem uAbs_nonneg (n : ℕ) (U : EnergySpace n) : 0 ≤ uAbs n U :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_uAbs (n : ℕ) (U : EnergySpace n) (σ : Config n) : |U σ| ≤ uAbs n U :=
  Finset.single_le_sum (fun τ _ => abs_nonneg (U τ)) (Finset.mem_univ σ)

theorem abs_spin (n : ℕ) (σ : Config n) (i : Fin n) : |spin n σ i| = 1 := by
  unfold spin; split <;> simp

/-- `log ∑_σ e^{f σ}` is within `log card + ∑_σ |f σ|` of `0`. -/
theorem abs_log_sum_exp_le {n : ℕ} (f : Config n → ℝ) :
    |Real.log (∑ σ : Config n, Real.exp (f σ))|
      ≤ Real.log (Fintype.card (Config n)) + ∑ σ, |f σ| := by
  have hpos : 0 < ∑ σ : Config n, Real.exp (f σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hcard : (0 : ℝ) < Fintype.card (Config n) := by exact_mod_cast Fintype.card_pos
  have hup : (∑ σ : Config n, Real.exp (f σ))
      ≤ Fintype.card (Config n) * Real.exp (∑ σ, |f σ|) := by
    calc (∑ σ : Config n, Real.exp (f σ)) ≤ ∑ _σ : Config n, Real.exp (∑ τ, |f τ|) := by
          refine Finset.sum_le_sum fun σ _ => Real.exp_le_exp.2 ?_
          exact (le_abs_self _).trans
            (Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ))
      _ = Fintype.card (Config n) * Real.exp (∑ τ, |f τ|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlow : Real.exp (-(∑ σ, |f σ|)) ≤ ∑ σ : Config n, Real.exp (f σ) := by
    obtain ⟨σ₀⟩ := (inferInstance : Nonempty (Config n))
    calc Real.exp (-(∑ σ, |f σ|)) ≤ Real.exp (f σ₀) := by
          refine Real.exp_le_exp.2 ?_
          have := Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ₀)
          linarith [neg_abs_le (f σ₀)]
      _ ≤ ∑ σ : Config n, Real.exp (f σ) :=
          Finset.single_le_sum (fun τ _ => (Real.exp_pos (f τ)).le) (Finset.mem_univ σ₀)
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    have hc : 0 ≤ Real.log (Fintype.card (Config n)) :=
      Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    linarith
  · have := Real.log_le_log hpos hup
    rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    exact this

/-- `log ∑ e^{f}` is `1`-Lipschitz in the sup norm of `f`. -/
theorem abs_log_sum_exp_sub_le {n : ℕ} {f g : Config n → ℝ} {ε : ℝ}
    (hε : ∀ σ, |f σ - g σ| ≤ ε) :
    |Real.log (∑ σ : Config n, Real.exp (f σ))
      - Real.log (∑ σ : Config n, Real.exp (g σ))| ≤ ε := by
  have hf : 0 < ∑ σ : Config n, Real.exp (f σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have hg : 0 < ∑ σ : Config n, Real.exp (g σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  have h1 : (∑ σ : Config n, Real.exp (f σ)) ≤ Real.exp ε * ∑ σ, Real.exp (g σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hε σ)).2])
  have h2 : (∑ σ : Config n, Real.exp (g σ)) ≤ Real.exp ε * ∑ σ, Real.exp (f σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hε σ)).1])
  have hl1 := Real.log_le_log hf h1
  have hl2 := Real.log_le_log hg h2
  rw [Real.log_mul (Real.exp_pos _).ne' hg.ne', Real.log_exp] at hl1
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hl2
  rw [abs_le]
  constructor <;> linarith

/-- A Gibbs average is bounded by the `ℓ¹` size of the observable. -/
theorem abs_gibbsAvg_le {n : ℕ} (E f : Config n → ℝ) : |gibbsAvg E f| ≤ ∑ σ, |f σ| := by
  unfold gibbsAvg
  have hpos : 0 < ∑ σ : Config n, Real.exp (E σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∑ σ, Real.exp (E σ) * f σ| ≤ ∑ σ, |Real.exp (E σ) * f σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ, Real.exp (E σ) * |f σ| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∑ σ, Real.exp (E σ) * ∑ τ, |f τ| := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ))
          (Real.exp_pos _).le
    _ = (∑ τ, |f τ|) * ∑ σ, Real.exp (E σ) := by rw [← Finset.sum_mul, mul_comm]

/-- The disorder-direction derivative has a bound independent of the cascade field. -/
theorem abs_guerraBaseUDeriv_le (n : ℕ) (U V : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) :
    |guerraBaseUDeriv n U V h t y| ≤ Real.sqrt t * uAbs n V := by
  unfold guerraBaseUDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    (by simpa [uAbs] using abs_gibbsAvg_le (guerraH n U h t y) V)
    (Real.sqrt_nonneg t)

/-- `|H_t(σ)| ≤ |U σ| + ∑ᵢ|yᵢ| + n|h|` for `0 ≤ t ≤ 1`. -/
theorem abs_guerraH_le (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : Fin n → ℝ) (σ : Config n) :
    |guerraH n U h t y σ| ≤ |U σ| + (l1 y + n * |h|) := by
  have hst : Real.sqrt t ≤ 1 := by
    have := Real.sqrt_le_sqrt ht1; rwa [Real.sqrt_one] at this
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith); rwa [Real.sqrt_one] at this
  unfold guerraH
  refine (abs_add_le _ _).trans ?_
  have h1 : |Real.sqrt t * U σ| ≤ |U σ| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
    nlinarith [abs_nonneg (U σ)]
  have h2 : |∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)| ≤ l1 y + n * |h| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i, |spin n σ i * (Real.sqrt (1 - t) * y i + h)| ≤ |y i| + |h| := by
      intro i
      rw [abs_mul, abs_spin, one_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [abs_nonneg (y i)]
    calc (∑ i, |spin n σ i * (Real.sqrt (1 - t) * y i + h)|) ≤ ∑ i, (|y i| + |h|) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = l1 y + n * |h| := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  linarith

theorem guerraH_sub (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y y' : Fin n → ℝ) (σ : Config n) :
    guerraH n U h t y σ - guerraH n U h t y' σ
      = Real.sqrt (1 - t) * ∑ i, spin n σ i * (y i - y' i) := by
  unfold guerraH
  rw [Finset.mul_sum]
  have hsplit : ∀ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)
      - spin n σ i * (Real.sqrt (1 - t) * y' i + h)
      = Real.sqrt (1 - t) * (spin n σ i * (y i - y' i)) := fun i => by ring
  calc Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)
        - (Real.sqrt t * U σ + ∑ i, spin n σ i * (Real.sqrt (1 - t) * y' i + h))
      = ∑ i, (spin n σ i * (Real.sqrt (1 - t) * y i + h)
          - spin n σ i * (Real.sqrt (1 - t) * y' i + h)) := by
        rw [Finset.sum_sub_distrib]; ring
    _ = ∑ i, Real.sqrt (1 - t) * (spin n σ i * (y i - y' i)) :=
        Finset.sum_congr rfl fun i _ => hsplit i

theorem abs_guerraHDeriv_le (n : ℕ) (U : EnergySpace n) (t : ℝ) (y : Fin n → ℝ) (σ : Config n) :
    |guerraHDeriv n U t y σ|
      ≤ |U σ| / (2 * Real.sqrt t) + l1 y / (2 * Real.sqrt (1 - t)) := by
  unfold guerraHDeriv
  refine (abs_sub _ _).trans ?_
  have hd1 : (0 : ℝ) ≤ 2 * Real.sqrt t := by positivity
  have hd2 : (0 : ℝ) ≤ 2 * Real.sqrt (1 - t) := by positivity
  have h1 : |U σ / (2 * Real.sqrt t)| = |U σ| / (2 * Real.sqrt t) := by
    rw [abs_div, abs_of_nonneg hd1]
  have h2 : |(∑ i, spin n σ i * y i) / (2 * Real.sqrt (1 - t))|
      ≤ l1 y / (2 * Real.sqrt (1 - t)) := by
    rw [abs_div, abs_of_nonneg hd2]
    refine div_le_div_of_nonneg_right ?_ hd2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [abs_mul, abs_spin, one_mul]
  linarith

/-! Measurability in the cascade field. -/

theorem measurable_guerraH (n : ℕ) (U : EnergySpace n) (h t : ℝ) (σ : Config n) :
    Measurable (fun y : Fin n → ℝ => guerraH n U h t y σ) := by
  unfold guerraH
  refine measurable_const.add (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul ((measurable_const.mul (measurable_pi_apply i)).add measurable_const)

theorem measurable_guerraHDeriv (n : ℕ) (U : EnergySpace n) (t : ℝ) (σ : Config n) :
    Measurable (fun y : Fin n → ℝ => guerraHDeriv n U t y σ) := by
  unfold guerraHDeriv
  refine measurable_const.sub ?_
  exact (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)).div_const _

theorem measurable_guerraBase (n : ℕ) (U : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBase n U h t) := by
  unfold guerraBase
  exact Real.measurable_log.comp
    (Finset.measurable_sum _ fun σ _ => Real.measurable_exp.comp (measurable_guerraH n U h t σ))

theorem measurable_guerraBaseDeriv (n : ℕ) (U : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBaseDeriv n U h t) := by
  unfold guerraBaseDeriv gibbsAvg
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH n U h t σ)).mul (measurable_guerraHDeriv n U t σ)
  · exact Finset.measurable_sum _ fun σ _ => Real.measurable_exp.comp (measurable_guerraH n U h t σ)

/-- The disorder-direction derivative is measurable in the cascade field. -/
theorem measurable_guerraBaseUDeriv (n : ℕ) (U V : EnergySpace n) (h t : ℝ) :
    Measurable (guerraBaseUDeriv n U V h t) := by
  unfold guerraBaseUDeriv gibbsAvg
  refine measurable_const.mul (Measurable.div ?_ ?_)
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH n U h t σ)).mul measurable_const
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH n U h t σ)

/-! The three bounds the induction consumes. -/

/-- `ℓ¹` growth of the base, uniform in `t ∈ [0,1]`. -/
theorem abs_guerraBase_le (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : Fin n → ℝ) :
    |guerraBase n U h t y|
      ≤ (Real.log (Fintype.card (Config n)) + uAbs n U + Fintype.card (Config n) * (n * |h|))
        + Fintype.card (Config n) * l1 y := by
  refine (abs_log_sum_exp_le _).trans ?_
  have : (∑ σ : Config n, |guerraH n U h t y σ|)
      ≤ uAbs n U + Fintype.card (Config n) * (l1 y + n * |h|) := by
    calc (∑ σ : Config n, |guerraH n U h t y σ|)
        ≤ ∑ σ : Config n, (|U σ| + (l1 y + n * |h|)) :=
          Finset.sum_le_sum fun σ _ => abs_guerraH_le n U h ht0 ht1 y σ
      _ = uAbs n U + Fintype.card (Config n) * (l1 y + n * |h|) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uAbs]
  linarith

/-- The base is `1`-Lipschitz in `ℓ¹`, for `t ≤ 1`. -/
theorem guerraBase_lipschitz (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (y y' : Fin n → ℝ) :
    |guerraBase n U h t y - guerraBase n U h t y'| ≤ 1 * l1 (y - y') := by
  unfold guerraBase
  refine abs_log_sum_exp_sub_le fun σ => ?_
  rw [guerraH_sub, one_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith); rwa [Real.sqrt_one] at this
  have hsum : |∑ i, spin n σ i * (y i - y' i)| ≤ l1 (y - y') := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [abs_mul, abs_spin, one_mul, Pi.sub_apply]
  nlinarith [abs_nonneg (∑ i, spin n σ i * (y i - y' i)), Real.sqrt_nonneg (1 - t)]

/-- `ℓ¹` growth of `∂_t F_{k+1,t}`, with constants controlled by `1/(2√t)`, `1/(2√(1-t))`. -/
theorem abs_guerraBaseDeriv_le (n : ℕ) (U : EnergySpace n) (h t : ℝ) (y : Fin n → ℝ) :
    |guerraBaseDeriv n U h t y|
      ≤ uAbs n U / (2 * Real.sqrt t)
        + (Fintype.card (Config n) / (2 * Real.sqrt (1 - t))) * l1 y := by
  refine (abs_gibbsAvg_le _ _).trans ?_
  calc (∑ σ : Config n, |guerraHDeriv n U t y σ|)
      ≤ ∑ σ : Config n, (|U σ| / (2 * Real.sqrt t) + l1 y / (2 * Real.sqrt (1 - t))) :=
        Finset.sum_le_sum fun σ _ => abs_guerraHDeriv_le n U t y σ
    _ = uAbs n U / (2 * Real.sqrt t)
          + (Fintype.card (Config n) / (2 * Real.sqrt (1 - t))) * l1 y := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_div, uAbs]
        ring

/-! ## 2d. Talagrand's (3.2): the derivative through the cascade

`∂_t F_{ℓ,t} = 𝔼_ℓ W_ℓ ∂_t F_{ℓ+1,t}`, iterated: the derivative of the cascade at level `j` is
the nested tilted average `guerraD j` of the base derivative.  The induction carries, on a
neighbourhood `talNbhd t₀` of the differentiation point, measurability in the cascade
field, `ℓ¹` growth and `ℓ¹`-Lipschitzness of the level, and `ℓ¹` growth of its derivative —
exactly the hypotheses of `hasDerivAt_parisiStepPi_param`.
-/

/-- Joint measurability of the shift `(x, z) ↦ x + √v z`. -/
theorem measurable_shift_prod (n : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + Real.sqrt v * p.2 i) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

/-- `x ↦ parisiStepPi n m v A x` is measurable. -/
theorem measurable_parisiStepPi {n : ℕ} {A : (Fin n → ℝ) → ℝ} (hA : Measurable A) (m v : ℝ) :
    Measurable (fun x => parisiStepPi n m v A x) := by
  classical
  have hj : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A (fun i => p.1 i + Real.sqrt v * p.2 i)) := hA.comp (measurable_shift_prod n v)
  have hint0 : Measurable (fun x : Fin n → ℝ =>
      ∫ z, A (fun i => x i + Real.sqrt v * z i) ∂(piGauss n)) :=
    (hj.stronglyMeasurable.integral_prod_right').measurable
  have hint1 : Measurable (fun x : Fin n → ℝ =>
      ∫ z, Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hj.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]; exact hint0
  · simp only [parisiStepPi, if_neg hm]
    exact (Real.measurable_log.comp hint1).const_mul _

/-- The tilted average `x ↦ ∫ g(x + √v z) W(z)` is measurable. -/
theorem measurable_tiltAvg {n : ℕ} {A g : (Fin n → ℝ) → ℝ} (hA : Measurable A) (hg : Measurable g)
    (m v : ℝ) :
    Measurable (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
      * tiltWeightPi n m v A x z ∂(piGauss n)) := by
  classical
  have hjg : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (fun i => p.1 i + Real.sqrt v * p.2 i)) := hg.comp (measurable_shift_prod n v)
  have hjA : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A (fun i => p.1 i + Real.sqrt v * p.2 i)) := hA.comp (measurable_shift_prod n v)
  have hI : Measurable (fun x : Fin n → ℝ =>
      ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hjA.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · have hfun : (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v A x z ∂(piGauss n))
        = fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z
          = g (fun i => x i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun]
    exact (hjg.stronglyMeasurable.integral_prod_right').measurable
  · have hfun : (fun x => ∫ z, g (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v A x z ∂(piGauss n))
        = fun x => ∫ z, (g (fun i => x i + Real.sqrt v * z i)
            * Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
            ∂(piGauss n) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show g (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z
          = (g (fun i => x i + Real.sqrt v * z i)
              * Real.exp (m * A (fun i => x i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂(piGauss n))
      rw [tiltWeightPi, if_neg hm, mul_div_assoc]
    rw [hfun]
    have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (g (fun i => p.1 i + Real.sqrt v * p.2 i)
          * Real.exp (m * A (fun i => p.1 i + Real.sqrt v * p.2 i)))
          / (∫ w, Real.exp (m * A (fun i => p.1 i + Real.sqrt v * w i)) ∂(piGauss n))) :=
      (hjg.mul (Real.measurable_exp.comp (hjA.const_mul m))).div (hI.comp measurable_fst)
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The neighbourhood of `t₀ ∈ (0,1)` on which the induction runs. -/
def talNbhd (t₀ : ℝ) : Set ℝ := Set.Ioo (t₀ / 2) ((1 + t₀) / 2)

theorem talNbhd_mem_nhds {t₀ t : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ talNbhd t₀) :
    talNbhd t₀ ∈ 𝓝 t :=
  isOpen_Ioo.mem_nhds ht

theorem self_mem_talNbhd {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) : t₀ ∈ talNbhd t₀ :=
  ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩

theorem talNbhd_subset_Ioo {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    talNbhd t₀ ⊆ Set.Ioo (0 : ℝ) 1 := fun t ht =>
  ⟨by linarith [ht.1, ht₀.1], by linarith [ht.2, ht₀.2]⟩

/-- Talagrand's `∂_t F_{ℓ,t}`, defined top-down from the base derivative by tilted
averaging at each level — the right-hand side of (3.2) written level by level. -/
noncomputable def guerraD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (U : EnergySpace n) (h : ℝ) :
    ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun t => guerraBaseDeriv n U h t
  | j + 1 => fun t x => ∫ z,
      guerraD n s β U h j t
          (fun i => x i + Real.sqrt (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
        * tiltWeightPi n (s.m (k + 1 - j)) (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
            (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)

/-- The level variance is non-negative. -/
theorem levelVar_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    0 ≤ 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) := by
  rw [one_mul]
  refine mul_nonneg (sq_nonneg β) ?_
  rcases le_or_gt j (k + 1) with hj | hj
  · have hidx : k + 2 - j = (k + 1 - j) + 1 := by omega
    rw [hidx]
    linarith [s.q_mono (k + 1 - j) (by omega)]
  · have h1 : k + 2 - j = 0 := by omega
    have h2 : k + 1 - j = 0 := by omega
    rw [h1, h2]; simp

/--
**Talagrand's (3.2), level by level.**  On `talNbhd t₀`, level `j` of the cascade is
measurable, of `ℓ¹` growth, `ℓ¹`-Lipschitz, differentiable in `t` with derivative
`guerraD j`, and `guerraD j` is measurable and of `ℓ¹` growth.  The constants are uniform on
the neighbourhood **and affine in the size `uAbs n U` of the disorder, uniformly in `U`** —
which is what differentiating under the expectation over the disorder needs.
-/
theorem guerra_cascade_hasDerivAt {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (h : ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    ∃ a b D L a' b' D' : ℝ, 0 ≤ b ∧ 0 ≤ D ∧ 0 ≤ L ∧ 0 ≤ b' ∧ 0 ≤ D' ∧
    ∀ U : EnergySpace n,
    (∀ t ∈ talNbhd t₀, Measurable (cascadeT n s β 1 (guerraBase n U h t) j)) ∧
    (∀ t ∈ talNbhd t₀, Measurable (guerraD n s β U h j t)) ∧
    (∀ t ∈ talNbhd t₀, ∀ y,
        |cascadeT n s β 1 (guerraBase n U h t) j y| ≤ (a + b * uAbs n U) + D * l1 y) ∧
    (∀ t ∈ talNbhd t₀, ∀ y y',
        |cascadeT n s β 1 (guerraBase n U h t) j y - cascadeT n s β 1 (guerraBase n U h t) j y'|
          ≤ L * l1 (y - y')) ∧
    (∀ t ∈ talNbhd t₀, ∀ y, |guerraD n s β U h j t y| ≤ (a' + b' * uAbs n U) + D' * l1 y) ∧
    (∀ t ∈ talNbhd t₀, ∀ x, HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) j x)
        (guerraD n s β U h j t x) t) := by
  classical
  have hsub := talNbhd_subset_Ioo ht₀
  induction j with
  | zero =>
      have ht₀2 : 0 < t₀ / 2 := by linarith [ht₀.1]
      have h1t₀2 : 0 < (1 - t₀) / 2 := by linarith [ht₀.2]
      refine ⟨Real.log (Fintype.card (Config n)) + Fintype.card (Config n) * (n * |h|), 1,
        Fintype.card (Config n), 1, 0, 1 / (2 * Real.sqrt (t₀ / 2)),
        Fintype.card (Config n) / (2 * Real.sqrt ((1 - t₀) / 2)),
        zero_le_one, by positivity, zero_le_one, by positivity, by positivity, fun U => ?_⟩
      refine ⟨fun t _ => measurable_guerraBase n U h t, fun t _ => measurable_guerraBaseDeriv n U h t,
        fun t ht y => ?_, fun t ht y y' => ?_, fun t ht y => ?_, fun t ht x => ?_⟩
      · have := abs_guerraBase_le n U h (hsub ht).1.le (hsub ht).2.le y
        show |guerraBase n U h t y| ≤ _
        linarith
      · exact guerraBase_lipschitz n U h (hsub ht).1.le (hsub ht).2.le y y'
      · -- the derivative bound, with `1/(2√t)` monotone on the neighbourhood
        have hb := abs_guerraBaseDeriv_le n U h t y
        have hs1 : 2 * Real.sqrt (t₀ / 2) ≤ 2 * Real.sqrt t :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.1.le) (by norm_num)
        have hs2 : 2 * Real.sqrt ((1 - t₀) / 2) ≤ 2 * Real.sqrt (1 - t) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [ht.2])) (by norm_num)
        have hp1 : 0 < 2 * Real.sqrt (t₀ / 2) := by positivity
        have hp2 : 0 < 2 * Real.sqrt ((1 - t₀) / 2) := by positivity
        have hA : uAbs n U / (2 * Real.sqrt t) ≤ uAbs n U / (2 * Real.sqrt (t₀ / 2)) :=
          div_le_div_of_nonneg_left (uAbs_nonneg n U) hp1 hs1
        have hB : (Fintype.card (Config n) : ℝ) / (2 * Real.sqrt (1 - t))
            ≤ Fintype.card (Config n) / (2 * Real.sqrt ((1 - t₀) / 2)) :=
          div_le_div_of_nonneg_left (by positivity) hp2 hs2
        have hB' := mul_le_mul_of_nonneg_right hB (l1_nonneg y)
        have hA' : uAbs n U / (2 * Real.sqrt (t₀ / 2))
            = (1 / (2 * Real.sqrt (t₀ / 2))) * uAbs n U := by ring
        show |guerraBaseDeriv n U h t y| ≤ _
        linarith
      · exact hasDerivAt_guerraBase n U h x (hsub ht)
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', ihU⟩ := ih
      set m : ℝ := s.m (k + 1 - j) with hm_def
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv_def
      have hm : 0 ≤ m := s.m_nonneg (by omega)
      have hv : 0 ≤ v := levelVar_nonneg s β j
      refine ⟨a + stepK n m v D, b, D, L,
        a' + (D' * Real.sqrt v)
          * (Real.exp ((|m| * L * Real.sqrt v) * l1Moment n)
              * ∫ z, l1 z * Real.exp ((|m| * L * Real.sqrt v) * l1 z) ∂(piGauss n)),
        b', D', hb, hD, hL, hb', hD', fun U => ?_⟩
      obtain ⟨hFm, hDm, hF, hLip, hD'b, hderiv⟩ := ihU U
      -- level `j+1` is one `N`-site step applied to level `j`
      have hstep : ∀ t, cascadeT n s β 1 (guerraBase n U h t) (j + 1)
          = fun x => parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x := by
        intro t; rfl
      have hDstep : ∀ t, guerraD n s β U h (j + 1) t
          = fun x => ∫ z, guerraD n s β U h j t (fun i => x i + Real.sqrt v * z i)
              * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n) := by
        intro t; rfl
      refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht y => ?_, fun t ht y y' => ?_,
        fun t ht y => ?_, fun t ht x => ?_⟩
      · rw [hstep]; exact measurable_parisiStepPi (hFm t ht) m v
      · rw [hDstep]; exact measurable_tiltAvg (hFm t ht) (hDm t ht) m v
      · rw [hstep]
        have := parisiStepPi_abs_le hm hv hD (hF t ht) (hFm t ht) y
        linarith
      · rw [hstep]
        exact parisiStepPi_lipschitz hD hL (hF t ht) (hFm t ht) (hLip t ht) y y'
      · rw [hDstep]
        have := abs_integral_mul_tiltWeightPi_le (m := m) (v := v) hL hD (hLip t ht) (hF t ht)
          (hFm t ht) (hDm t ht) hD' (hD'b t ht) y
        linarith
      · have hN := talNbhd_mem_nhds ht₀ ht
        show HasDerivAt (fun t => parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x)
          (∫ z, guerraD n s β U h j t (fun i => x i + Real.sqrt v * z i)
            * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)) t
        exact hasDerivAt_parisiStepPi_param (A := fun t => cascadeT n s β 1 (guerraBase n U h t) j)
          (A' := fun t => guerraD n s β U h j t) (m := m) (v := v)
          (C := a + b * uAbs n U) (D := D) (C' := a' + b' * uAbs n U) (D' := D') x hN hD hD'
          (fun u hu y => hderiv u hu y) hFm hDm hF hD'b

/-- **(3.2) at the top of the cascade**: `d/dt F_{1,t}(0) = guerraD (k+2) t 0`. -/
theorem hasDerivAt_cascade_top {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => cascadeT n s β 1 (guerraBase n U h t) (k + 2) 0)
      (guerraD n s β U h (k + 2) t 0) t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hU⟩ := guerra_cascade_hasDerivAt n s β h ht (k + 2)
  exact (hU U).2.2.2.2.2 t (self_mem_talNbhd ht) 0

/-- The size `uAbs` is controlled by the Hilbert norm: `|U σ| ≤ ‖U‖` coordinatewise. -/
theorem uAbs_le_card_mul_norm (n : ℕ) (U : EnergySpace n) :
    uAbs n U ≤ Fintype.card (Config n) * ‖U‖ := by
  unfold uAbs
  calc (∑ σ : Config n, |U σ|) ≤ ∑ _σ : Config n, ‖U‖ :=
        Finset.sum_le_sum fun σ _ => by
          have := PiLp.norm_apply_le U σ
          simpa [Real.norm_eq_abs] using this
    _ = Fintype.card (Config n) * ‖U‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The domination needed to differentiate under the expectation over the disorder**: on
`talNbhd t₀`, `|∂_t F_{1,t}(0)|` is bounded by an affine function of `‖U‖`, uniformly in `t`. -/
theorem abs_guerraD_top_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ) (h : ℝ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ U : EnergySpace n, ∀ t ∈ talNbhd t₀,
      |guerraD n s β U h (k + 2) t 0| ≤ a + b * ‖U‖ := by
  obtain ⟨_, _, _, _, a', b', _, _, _, _, hb', _, hU⟩ :=
    guerra_cascade_hasDerivAt n s β h ht₀ (k + 2)
  refine ⟨a', b' * Fintype.card (Config n), by positivity, fun U t ht => ?_⟩
  have h1 := (hU U).2.2.2.2.1 t ht 0
  have h2 : l1 (0 : Fin n → ℝ) = 0 := by simp [l1]
  rw [h2, mul_zero, add_zero] at h1
  have h3 := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm n U) hb'
  nlinarith

/-! ## 2e. Differentiating `φ` under the expectation over the disorder

`φ(t) = (1/N) 𝔼_ω F_{1,t}(0)` with `F_{1,t}` depending on `ω` through `U ω`.  Two inputs:
measurability of `U ↦ F_{1,t}(0)` and of `U ↦ ∂_t F_{1,t}(0)` (an induction jointly in
`(U, x)`, the same parametric-integral argument as §2d), and the domination
`|∂_t F_{1,t}(0)| ≤ a + b‖U‖` of §2d with `‖U ω‖` integrable
(`integrable_norm_of_gaussian`).  Then `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
over `ℙ` gives `φ'(t) = (1/N) 𝔼_ω ∂_t F_{1,t}(0)`, i.e. Talagrand's (3.2) with the outer
expectation in place.
-/

/-- Coordinates of the energy space are measurable. -/
theorem measurable_coord (n : ℕ) (σ : Config n) : Measurable (fun U : EnergySpace n => U σ) := by
  have hc : Continuous (fun U : EnergySpace n =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Config n => ℝ) U) σ) :=
    (continuous_apply σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Config n => ℝ)).continuous
  exact hc.measurable

section Joint

variable {n : ℕ}

/-- The shift `((U, x), z) ↦ x + √v z`, jointly measurable. -/
theorem measurable_shift_joint (v : ℝ) :
    Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      fun i => q.1.2 i + Real.sqrt v * q.2 i) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst.snd).add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

/-- One `N`-site level of a family `F U`, measurable jointly in `(U, x)`. -/
theorem measurable_parisiStepPi_joint {F : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => F p.1 p.2)) (m v : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => parisiStepPi n m v (F p.1) p.2) := by
  classical
  have hj : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hint0 : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, F p.1 (fun i => p.2 i + Real.sqrt v * z i) ∂(piGauss n)) :=
    (hj.stronglyMeasurable.integral_prod_right').measurable
  have hint1 : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hj.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]; exact hint0
  · simp only [parisiStepPi, if_neg hm]
    exact (Real.measurable_log.comp hint1).const_mul _

/-- The tilted average of a family `G U` against a family `F U`, jointly measurable. -/
theorem measurable_tiltAvg_joint {F G : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => F p.1 p.2))
    (hG : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => G p.1 p.2)) (m v : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
        * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n)) := by
  classical
  have hjG : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      G q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hjF : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
      F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_shift_joint v))
  have hI : Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      ∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n)) :=
    ((Real.measurable_exp.comp (hjF.const_mul m)).stronglyMeasurable.integral_prod_right').measurable
  by_cases hm : m = 0
  · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n))
        = fun p => ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i) ∂(piGauss n) := by
      funext p
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show G p.1 (fun i => p.2 i + Real.sqrt v * z i) * tiltWeightPi n m v (F p.1) p.2 z
          = G p.1 (fun i => p.2 i + Real.sqrt v * z i)
      rw [tiltWeightPi, if_pos hm, mul_one]
    rw [hfun]
    exact (hjG.stronglyMeasurable.integral_prod_right').measurable
  · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          ∫ z, G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * tiltWeightPi n m v (F p.1) p.2 z ∂(piGauss n))
        = fun p => ∫ z, (G p.1 (fun i => p.2 i + Real.sqrt v * z i)
            * Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n))
            ∂(piGauss n) := by
      funext p
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show G p.1 (fun i => p.2 i + Real.sqrt v * z i) * tiltWeightPi n m v (F p.1) p.2 z
          = (G p.1 (fun i => p.2 i + Real.sqrt v * z i)
              * Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * z i)))
            / (∫ w, Real.exp (m * F p.1 (fun i => p.2 i + Real.sqrt v * w i)) ∂(piGauss n))
      rw [tiltWeightPi, if_neg hm, mul_div_assoc]
    rw [hfun]
    have hjoint : Measurable (fun q : (EnergySpace n × (Fin n → ℝ)) × (Fin n → ℝ) =>
        (G q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)
          * Real.exp (m * F q.1.1 (fun i => q.1.2 i + Real.sqrt v * q.2 i)))
          / (∫ w, Real.exp (m * F q.1.1 (fun i => q.1.2 i + Real.sqrt v * w i)) ∂(piGauss n))) :=
      (hjG.mul (Real.measurable_exp.comp (hjF.const_mul m))).div (hI.comp measurable_fst)
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_guerraH_joint (h t : ℝ) (σ : Config n) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraH n p.1 h t p.2 σ) := by
  unfold guerraH
  refine (measurable_const.mul ((measurable_coord n σ).comp measurable_fst)).add
    (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul
    ((measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).add measurable_const)

theorem measurable_guerraHDeriv_joint (t : ℝ) (σ : Config n) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraHDeriv n p.1 t p.2 σ) := by
  unfold guerraHDeriv
  refine (((measurable_coord n σ).comp measurable_fst).div_const _).sub ?_
  exact (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).div_const _

theorem measurable_guerraBase_joint (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraBase n p.1 h t p.2) := by
  unfold guerraBase
  exact Real.measurable_log.comp (Finset.measurable_sum _ fun σ _ =>
    Real.measurable_exp.comp (measurable_guerraH_joint h t σ))

theorem measurable_guerraBaseDeriv_joint (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraBaseDeriv n p.1 h t p.2) := by
  unfold guerraBaseDeriv gibbsAvg
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH_joint h t σ)).mul
        (measurable_guerraHDeriv_joint t σ)
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH_joint h t σ)

/-- Every level, and its derivative, is measurable jointly in `(U, x)`. -/
theorem measurable_cascade_joint {k : ℕ} (s : RSBScheme k) (β h t : ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
        cascadeT n s β 1 (guerraBase n p.1 h t) j p.2) ∧
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraD n s β p.1 h j t p.2) := by
  induction j with
  | zero => exact ⟨measurable_guerraBase_joint h t, measurable_guerraBaseDeriv_joint h t⟩
  | succ j ih =>
      obtain ⟨hF, hD⟩ := ih
      constructor
      · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
              cascadeT n s β 1 (guerraBase n p.1 h t) (j + 1) p.2)
            = fun p => parisiStepPi n (s.m (k + 1 - j))
                (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 := by
          funext p; rfl
        rw [hfun]
        exact measurable_parisiStepPi_joint
          (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j) hF _ _
      · have hfun : (fun p : EnergySpace n × (Fin n → ℝ) => guerraD n s β p.1 h (j + 1) t p.2)
            = fun p => ∫ z, guerraD n s β p.1 h j t
                (fun i => p.2 i + Real.sqrt (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
                * tiltWeightPi n (s.m (k + 1 - j)) (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                    (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 z ∂(piGauss n) := by
          funext p; rfl
        rw [hfun]
        exact measurable_tiltAvg_joint
          (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
          (G := fun U => guerraD n s β U h j t) hF hD _ _

theorem measurable_cascade_top_U {k : ℕ} (s : RSBScheme k) (β h t : ℝ) :
    Measurable (fun U : EnergySpace n => cascadeT n s β 1 (guerraBase n U h t) (k + 2) 0) := by
  have hm := (measurable_cascade_joint (n := n) s β h t (k + 2)).1.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))
  exact hm

theorem measurable_guerraD_top_U {k : ℕ} (s : RSBScheme k) (β h t : ℝ) :
    Measurable (fun U : EnergySpace n => guerraD n s β U h (k + 2) t 0) := by
  have hm := (measurable_cascade_joint (n := n) s β h t (k + 2)).2.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))
  exact hm

end Joint

/--
**(3.2) with the expectation over the disorder**: for `0 < t < 1`,

  `φ'(t) = (1/N) 𝔼_ω [∂_t F_{1,t}(0)]`,

the outer expectation of the nested tilted average `guerraD (k+2)`.
-/
theorem hasDerivAt_guerraPhi {N : ℕ} (β h : ℝ) (sk : SKDisorder (Ω := Ω) N β h)
    {k : ℕ} (s : RSBScheme k) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi N s β h sk.U)
      ((1 / (N : ℝ)) * ∫ ω, guerraD N s β (sk.U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
  classical
  obtain ⟨a, b, hb, hbound⟩ := abs_guerraD_top_le N s β h ht₀ (k := k)
  obtain ⟨a₀, b₀, D, L, a', b', D', hb₀, -, -, -, -, hU⟩ :=
    guerra_cascade_hasDerivAt N s β h ht₀ (k + 2)
  have hUmeas : Measurable sk.U := sk.hU.repr_measurable
  have hnormint : Integrable (fun ω => ‖sk.U ω‖) (ℙ : Measure Ω) :=
    PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian sk.hU
  have hbint : Integrable (fun ω => a + b * ‖sk.U ω‖) (ℙ : Measure Ω) :=
    (integrable_const _).add (hnormint.const_mul _)
  have hs : talNbhd t₀ ∈ 𝓝 t₀ := talNbhd_mem_nhds ht₀ (self_mem_talNbhd ht₀)
  have hb2 : Integrable (fun ω => a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖))
      (ℙ : Measure Ω) :=
    (integrable_const _).add ((hnormint.const_mul _).const_mul _)
  have hF0 : Integrable
      (fun ω => cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0) (ℙ : Measure Ω) := by
    refine Integrable.mono hb2
      ((measurable_cascade_top_U s β h t₀).comp hUmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 := (hU (sk.U ω)).2.2.1 t₀ (self_mem_talNbhd ht₀) 0
    have h2 : l1 (0 : Fin N → ℝ) = 0 := by simp [l1]
    rw [h2, mul_zero, add_zero] at h1
    have h3 := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N (sk.U ω)) hb₀
    have hnn : 0 ≤ a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖) := by
      linarith [abs_nonneg (cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0)]
    show ‖cascadeT N s β 1 (guerraBase N (sk.U ω) h t₀) (k + 2) 0‖
        ≤ ‖a₀ + b₀ * (Fintype.card (Config N) * ‖sk.U ω‖)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  have hmain : HasDerivAt
      (fun t => ∫ ω, cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ)
      (∫ ω, guerraD N s β (sk.U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
      (F := fun t ω => cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0)
      (F' := fun t ω => guerraD N s β (sk.U ω) h (k + 2) t 0)
      (bound := fun ω => a + b * ‖sk.U ω‖) (s := talNbhd t₀) hs ?_ hF0 ?_ ?_ hbint ?_).2
    · filter_upwards [hs] with t ht
      exact ((measurable_cascade_top_U s β h t).comp hUmeas).aestronglyMeasurable
    · exact ((measurable_guerraD_top_U s β h t₀).comp hUmeas).aestronglyMeasurable
    · filter_upwards with ω t ht
      rw [Real.norm_eq_abs]
      exact hbound (sk.U ω) t ht
    · filter_upwards with ω t ht
      exact hasDerivAt_cascade_top N s β (sk.U ω) h (talNbhd_subset_Ioo ht₀ ht)
  show HasDerivAt (fun t => (1 / (N : ℝ))
      * ∫ ω, cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ) _ t₀
  exact hmain.const_mul (1 / (N : ℝ))

/-! ## 2f. Differentiating the cascade along the disorder

The coordinate Stein identity needs derivatives along the affine lines `U + u • V` in the
disorder space.  The base derivative is `guerraBaseUDeriv`; `guerraUD` pushes it through the
same normalized tilted averages as `guerraD`.  Since the base derivative is bounded
independently of the cascade field and every tilted weight integrates to one, this bound is
preserved exactly at every level.
-/

/-- The disorder-direction derivative propagated through `j` cascade levels. -/
noncomputable def guerraUD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h t : ℝ) : ℕ → (Fin n → ℝ) → ℝ
  | 0 => guerraBaseUDeriv n U V h t
  | j + 1 => fun x => ∫ z,
      guerraUD n s β U V h t j
          (fun i => x i + Real.sqrt
            (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
        * tiltWeightPi n (s.m (k + 1 - j))
            (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
            (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂(piGauss n)

/-- The crude disorder size is subadditive along affine lines. -/
theorem uAbs_add_smul_le (n : ℕ) (U V : EnergySpace n) (u : ℝ) :
    uAbs n (U + u • V) ≤ uAbs n U + |u| * uAbs n V := by
  unfold uAbs
  calc
    (∑ σ : Config n, |(U + u • V) σ|)
        ≤ ∑ σ : Config n, (|U σ| + |u| * |V σ|) := by
          refine Finset.sum_le_sum (fun σ _ => ?_)
          simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_mul]
            using abs_add_le (U σ) (u * V σ)
    _ = (∑ σ : Config n, |U σ|) + |u| * ∑ σ : Config n, |V σ| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A fixed open neighborhood of a point on a disorder-coordinate line. -/
def guerraLineNbhd (r : ℝ) : Set ℝ := Set.Ioo (r - 1) (r + 1)

theorem guerraLineNbhd_mem_nhds (r : ℝ) : guerraLineNbhd r ∈ 𝓝 r :=
  isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩

theorem abs_le_abs_add_one_of_mem_guerraLineNbhd {r u : ℝ} (hu : u ∈ guerraLineNbhd r) :
    |u| ≤ |r| + 1 := by
  rw [abs_le]
  constructor
  · have hr := neg_abs_le r
    exact le_of_lt (by dsimp [guerraLineNbhd] at hu; linarith [hu.1])
  · have hr := le_abs_self r
    exact le_of_lt (by dsimp [guerraLineNbhd] at hu; linarith [hu.2])

/-- `guerraUD` is measurable in the cascade field, and its base bound is preserved at every
level because the tilted weights are normalized probability densities. -/
theorem guerraUD_measurable_and_bound {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ j : ℕ, Measurable (guerraUD n s β U V h t j) ∧
      ∀ x, |guerraUD n s β U V h t j x| ≤ Real.sqrt t * uAbs n V := by
  intro j
  induction j with
  | zero =>
      exact ⟨measurable_guerraBaseUDeriv n U V h t,
        abs_guerraBaseUDeriv_le n U V h t⟩
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      obtain ⟨hAmeas, -, hAbound, hAlip, -, -⟩ := hprops U
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      set m : ℝ := s.m (k + 1 - j) with hm
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv
      have hmeas : Measurable (guerraUD n s β U V h t (j + 1)) := by
        change Measurable (fun x => ∫ z,
          guerraUD n s β U V h t j (fun i => x i + Real.sqrt v * z i)
            * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z
          ∂(piGauss n))
        exact measurable_tiltAvg (hAmeas t htt) ih.1 m v
      refine ⟨hmeas, fun x => ?_⟩
      change |∫ z, guerraUD n s β U V h t j (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z
        ∂(piGauss n)| ≤ Real.sqrt t * uAbs n V
      have hbound := abs_integral_mul_tiltWeightPi_le
        (m := m) (v := v) (C := a + b * uAbs n U) (D := D) (L := L)
        hL hD (hAlip t htt) (hAbound t htt) (hAmeas t htt) ih.1
        (C' := Real.sqrt t * uAbs n V) (D' := 0) le_rfl
        (fun y => by simpa using ih.2 y) x
      simpa using hbound

/-- The full cascade has derivative `guerraUD` along every affine disorder line. -/
theorem hasDerivAt_cascade_Uline {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (x : Fin n → ℝ) (r : ℝ) :
    HasDerivAt
      (fun u => cascadeT n s β 1 (guerraBase n (U + u • V) h t) j x)
      (guerraUD n s β (U + r • V) V h t j x) r := by
  induction j generalizing U x r with
  | zero => exact hasDerivAt_guerraBase_Uline n U V h t x r
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      set m : ℝ := s.m (k + 1 - j) with hm
      set v : ℝ := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) with hv
      have hs : guerraLineNbhd r ∈ 𝓝 r := guerraLineNbhd_mem_nhds r
      have hlinebound : ∀ u ∈ guerraLineNbhd r,
          uAbs n (U + u • V) ≤ uAbs n U + (|r| + 1) * uAbs n V := by
        intro u hu
        refine (uAbs_add_smul_le n U V u).trans ?_
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (abs_le_abs_add_one_of_mem_guerraLineNbhd hu) (uAbs_nonneg n V))
      change HasDerivAt
        (fun u => parisiStepPi n m v
          (cascadeT n s β 1 (guerraBase n (U + u • V) h t) j) x)
        (∫ z, guerraUD n s β (U + r • V) V h t j
            (fun i => x i + Real.sqrt v * z i)
          * tiltWeightPi n m v
              (cascadeT n s β 1 (guerraBase n (U + r • V) h t) j) x z
          ∂(piGauss n)) r
      exact hasDerivAt_parisiStepPi_param
        (A := fun u => cascadeT n s β 1 (guerraBase n (U + u • V) h t) j)
        (A' := fun u => guerraUD n s β (U + u • V) V h t j)
        (m := m) (v := v)
        (C := (a + b * (uAbs n U + (|r| + 1) * uAbs n V))) (D := D)
        (C' := Real.sqrt t * uAbs n V) (D' := 0) x hs hD le_rfl
        (fun u _ y => ih (U := U) (x := y) (r := u))
        (fun u _ => (hprops (U + u • V)).1 t htt)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • V) V h ht j).1)
        (fun u hu y => by
          have hbu := (hprops (U + u • V)).2.2.1 t htt y
          have hmul := mul_le_mul_of_nonneg_left (hlinebound u hu) hb
          linarith)
        (fun u _ y => by
          have hbu := (guerraUD_measurable_and_bound n s β (U + u • V) V h ht j).2 y
          simpa using hbu)

/-- For a fixed disorder direction `V`, the base directional derivative is jointly
measurable in the current disorder and the cascade field. -/
theorem measurable_guerraBaseUDeriv_joint {n : ℕ} (V : EnergySpace n) (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraBaseUDeriv n p.1 V h t p.2) := by
  unfold guerraBaseUDeriv gibbsAvg
  refine measurable_const.mul (Measurable.div ?_ ?_)
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH_joint h t σ)).mul measurable_const
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH_joint h t σ)

/-- For fixed direction `V`, every propagated disorder derivative is jointly measurable
in the current disorder `U` and the cascade field `x`. -/
theorem measurable_guerraUD_joint {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (V : EnergySpace n) (h t : ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraUD n s β p.1 V h t j p.2) := by
  induction j with
  | zero => exact measurable_guerraBaseUDeriv_joint V h t
  | succ j ih =>
      have hF := (measurable_cascade_joint (n := n) s β h t j).1
      have hfun : (fun p : EnergySpace n × (Fin n → ℝ) =>
          guerraUD n s β p.1 V h t (j + 1) p.2) =
          fun p => ∫ z,
            guerraUD n s β p.1 V h t j
                (fun i => p.2 i + Real.sqrt
                  (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)
              * tiltWeightPi n (s.m (k + 1 - j))
                  (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
                  (cascadeT n s β 1 (guerraBase n p.1 h t) j) p.2 z ∂(piGauss n) := by
        funext p
        rfl
      rw [hfun]
      exact measurable_tiltAvg_joint
        (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
        (G := fun U => guerraUD n s β U V h t j) hF ih _ _

/-- The top-level disorder-direction derivative is measurable as a function of the current
disorder. -/
theorem measurable_guerraUD_top_U {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (V : EnergySpace n) (h t : ℝ) :
    Measurable (fun U : EnergySpace n => guerraUD n s β U V h t (k + 2) 0) := by
  exact (measurable_guerraUD_joint s β V h t (k + 2)).comp
    (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : EnergySpace n => (0 : Fin n → ℝ))))

/-- Gaussian integration by parts for the top cascade in a fixed disorder direction. -/
theorem guerra_cascade_stein {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (a : EnergySpace N) :
    (∫ ω, inner ℝ (sk.U ω) a
        * cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ) =
      ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * inner ℝ a (sk.hU.w i)
        * ∫ ω, guerraUD N s β (sk.U ω) (sk.hU.w i) h t (k + 2) 0 ∂ℙ := by
  classical
  let Φ : EnergySpace N → ℝ := fun U =>
    cascadeT N s β 1 (guerraBase N U h t) (k + 2) 0
  let D : sk.hU.ι → EnergySpace N → ℝ := fun i U =>
    guerraUD N s β U (sk.hU.w i) h t (k + 2) 0
  have hΦm : Measurable Φ := measurable_cascade_top_U s β h t
  have hDm : ∀ i : sk.hU.ι, Measurable (D i) := fun i =>
    measurable_guerraUD_top_U s β (sk.hU.w i) h t
  obtain ⟨A, B, E, L, A', B', E', hB, hE, hL, hB', hE', hprops⟩ :=
    guerra_cascade_hasDerivAt N s β h ht (k + 2)
  have hΦbound : ∀ U : EnergySpace N,
      |Φ U| ≤ A + (B * Fintype.card (Config N)) * ‖U‖ := by
    intro U
    have hbase := (hprops U).2.2.1 t (self_mem_talNbhd ht) 0
    have hu := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N U) hB
    simp [l1] at hbase
    dsimp only [Φ]
    calc
      |cascadeT N s β 1 (guerraBase N U h t) (k + 2) 0|
          ≤ A + B * uAbs N U := hbase
      _ ≤ A + B * (Fintype.card (Config N) * ‖U‖) := by linarith
      _ = A + (B * Fintype.card (Config N)) * ‖U‖ := by ring
  have hA : 0 ≤ A := by
    have hz := hΦbound (0 : EnergySpace N)
    exact le_trans (abs_nonneg (Φ 0)) (by simpa using hz)
  have hnormSlope : 0 ≤ B * Fintype.card (Config N) := by positivity
  have hintCoord : ∀ i : sk.hU.ι,
      Integrable (fun ω => sk.hU.c i ω * Φ (sk.U ω)) (ℙ : Measure Ω) := fun i =>
    integrable_coord_mul_comp_of_affine_norm_bound sk.hU i hΦm hA hnormSlope hΦbound
  have hintΦ : Integrable (fun ω => Φ (sk.U ω)) (ℙ : Measure Ω) :=
    integrable_comp_of_affine_norm_bound sk.hU hΦm hA hnormSlope hΦbound
  have hintD : ∀ i : sk.hU.ι,
      Integrable (fun ω => D i (sk.U ω)) (ℙ : Measure Ω) := by
    intro i
    have hC : 0 ≤ Real.sqrt t * uAbs N (sk.hU.w i) :=
      mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg N _)
    refine integrable_comp_of_affine_norm_bound sk.hU (hDm i)
      (C := Real.sqrt t * uAbs N (sk.hU.w i)) (D := 0) hC le_rfl ?_
    intro U
    have hb := (guerraUD_measurable_and_bound N s β U (sk.hU.w i) h ht (k + 2)).2 0
    simpa only [D, zero_mul, add_zero] using hb
  have hline : ∀ i : sk.hU.ι, ∀ z : EnergySpace N, ∀ x : ℝ,
      HasDerivAt (fun r => Φ (z + r • sk.hU.w i))
        (D i (z + x • sk.hU.w i)) x := by
    intro i z x
    exact hasDerivAt_cascade_Uline N s β z (sk.hU.w i) h ht (k + 2) 0 x
  simpa only [Φ, D] using
    (stein_inner_of_hasDerivAt (g := sk.U) sk.hU a (Φ := Φ) (D := D)
      hline hΦm hDm hintCoord hintΦ hintD)

/-! ## 2g. Mixed disorder derivatives and integration by parts for the gradient

The disorder term in `φ'` contains a first disorder derivative.  Applying Stein to
that term needs a second derivative, including the covariance contribution from
each normalized cascade weight.
-/

/-- Differentiating a finite Gibbs average gives a Gibbs covariance. -/
theorem hasDerivAt_gibbsAvg {n : ℕ} {E : ℝ → Config n → ℝ}
    {E' : Config n → ℝ} (f : Config n → ℝ) (r : ℝ)
    (hE : ∀ σ, HasDerivAt (fun u => E u σ) (E' σ) r) :
    HasDerivAt (fun u => gibbsAvg (E u) f)
      (gibbsAvg (E r) (fun σ => f σ * E' σ) - gibbsAvg (E r) f * gibbsAvg (E r) E') r := by
  have hnum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ _ => ((hE σ).exp).mul_const (f σ))
  have hden := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => (hE σ).exp)
  have hpos : 0 < ∑ σ, Real.exp (E r σ) :=
    Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty
  refine (hnum.div hden hpos.ne').congr_deriv ?_
  have hsum : (∑ σ, Real.exp (E r σ) * E' σ * f σ) =
      ∑ σ, Real.exp (E r σ) * (f σ * E' σ) :=
    Finset.sum_congr rfl (fun σ _ => by ring)
  rw [hsum]
  unfold gibbsAvg
  field_simp

/-- Scalar multiplication of the observable commutes with a Gibbs average. -/
theorem gibbsAvg_const_mul {n : ℕ} (E f : Config n → ℝ) (c : ℝ) :
    gibbsAvg E (fun σ => c * f σ) = c * gibbsAvg E f := by
  unfold gibbsAvg
  have hsum : (∑ σ, Real.exp (E σ) * (c * f σ)) =
      c * ∑ σ, Real.exp (E σ) * f σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  rw [hsum]
  ring

/-- The mixed disorder Hessian of the terminal log partition function. -/
noncomputable def guerraBaseUUDeriv (n : ℕ) (U V W : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) : ℝ :=
  (Real.sqrt t) ^ 2 * (gibbsAvg (guerraH n U h t y) (fun σ => V σ * W σ) -
    gibbsAvg (guerraH n U h t y) V * gibbsAvg (guerraH n U h t y) W)

theorem hasDerivAt_guerraBaseUDeriv_Uline (n : ℕ) (U V W : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun u => guerraBaseUDeriv n (U + u • W) V h t y)
      (guerraBaseUUDeriv n (U + r • W) V W h t y) r := by
  have hE : ∀ σ : Config n,
      HasDerivAt (fun u => guerraH n (U + u • W) h t y σ) (Real.sqrt t * W σ) r := by
    intro σ
    have heq : (fun u => guerraH n (U + u • W) h t y σ) =
        fun u => Real.sqrt t * U σ + u * (Real.sqrt t * W σ) +
          ∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h) := by
      funext u
      simp only [guerraH, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      congr 1
      ring
    rw [heq]
    simpa using (((hasDerivAt_const r (Real.sqrt t * U σ)).add
      ((hasDerivAt_id r).mul_const (Real.sqrt t * W σ))).add_const
        (∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)))
  have hg := (hasDerivAt_gibbsAvg V r hE).const_mul (Real.sqrt t)
  refine hg.congr_deriv ?_
  have hprod : (fun σ : Config n => V σ * (Real.sqrt t * W σ)) =
      fun σ => Real.sqrt t * (V σ * W σ) := by funext σ; ring
  rw [hprod, gibbsAvg_const_mul, gibbsAvg_const_mul]
  unfold guerraBaseUUDeriv
  ring

/-- A uniform bound on the base mixed derivative, independent of the disorder and field. -/
theorem abs_guerraBaseUUDeriv_le (n : ℕ) (U V W : EnergySpace n) (h t : ℝ)
    (y : Fin n → ℝ) :
    |guerraBaseUUDeriv n U V W h t y| ≤
      2 * (Real.sqrt t * uAbs n V) * (Real.sqrt t * uAbs n W) := by
  have hprod : (∑ σ : Config n, |V σ * W σ|) ≤ uAbs n V * uAbs n W := by
    calc
      (∑ σ : Config n, |V σ * W σ|) ≤ ∑ σ, |V σ| * uAbs n W := by
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le_uAbs n W σ) (abs_nonneg _)
      _ = uAbs n V * uAbs n W := by rw [← Finset.sum_mul]; rfl
  have hVW := (abs_gibbsAvg_le (guerraH n U h t y) (fun σ => V σ * W σ)).trans hprod
  have hV := abs_gibbsAvg_le (guerraH n U h t y) V
  have hW := abs_gibbsAvg_le (guerraH n U h t y) W
  have hp : |gibbsAvg (guerraH n U h t y) V * gibbsAvg (guerraH n U h t y) W| ≤
      uAbs n V * uAbs n W := by
    rw [abs_mul]
    exact mul_le_mul hV hW (abs_nonneg _) (uAbs_nonneg n V)
  unfold guerraBaseUUDeriv
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (Real.sqrt t) ^ 2 * (2 * (uAbs n V * uAbs n W)) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (sq_nonneg _)
    _ = _ := by ring

/-- A fixed Gibbs observable is jointly measurable in the disorder and cascade field. -/
theorem measurable_gibbsAvg_guerraH_joint {n : ℕ} (f : Config n → ℝ) (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => gibbsAvg (guerraH n p.1 h t p.2) f) := by
  unfold gibbsAvg
  refine Measurable.div ?_ ?_
  · exact Finset.measurable_sum _ fun σ _ =>
      (Real.measurable_exp.comp (measurable_guerraH_joint h t σ)).mul measurable_const
  · exact Finset.measurable_sum _ fun σ _ =>
      Real.measurable_exp.comp (measurable_guerraH_joint h t σ)

theorem measurable_guerraBaseUUDeriv_joint {n : ℕ} (V W : EnergySpace n) (h t : ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraBaseUUDeriv n p.1 V W h t p.2) :=
  measurable_const.mul ((measurable_gibbsAvg_guerraH_joint (fun σ => V σ * W σ) h t).sub
    ((measurable_gibbsAvg_guerraH_joint V h t).mul (measurable_gibbsAvg_guerraH_joint W h t)))

/-- Mixed disorder derivatives through the cascade.  The two terms at a successor
level are the derivative of the numerator and the normalization correction. -/
noncomputable def guerraUUD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h t : ℝ) : ℕ → (Fin n → ℝ) → ℝ
  | 0 => guerraBaseUUDeriv n U V W h t
  | j + 1 => fun x =>
      (∫ z, (guerraUUD n s β U V W h t j
            (fun i => x i + Real.sqrt
              (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i) +
          s.m (k + 1 - j) * guerraUD n s β U V h t j
            (fun i => x i + Real.sqrt
              (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i) *
          guerraUD n s β U W h t j
            (fun i => x i + Real.sqrt
              (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i)) *
          tiltWeightPi n (s.m (k + 1 - j))
            (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
            (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n) -
        s.m (k + 1 - j) * guerraUD n s β U V h t (j + 1) x *
          guerraUD n s β U W h t (j + 1) x

theorem measurable_guerraUUD_joint {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (V W : EnergySpace n) (h t : ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraUUD n s β p.1 V W h t j p.2) := by
  induction j with
  | zero => exact measurable_guerraBaseUUDeriv_joint V W h t
  | succ j ih =>
      set m := s.m (k + 1 - j)
      set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
      have hF := (measurable_cascade_joint (n := n) s β h t j).1
      have hV := measurable_guerraUD_joint s β V h t j
      have hW := measurable_guerraUD_joint s β W h t j
      have hnum := measurable_tiltAvg_joint
        (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
        (G := fun U x => guerraUUD n s β U V W h t j x +
          m * guerraUD n s β U V h t j x * guerraUD n s β U W h t j x)
        hF (ih.add ((hV.const_mul m).mul hW)) m v
      exact hnum.sub (((measurable_guerraUD_joint s β V h t (j + 1)).const_mul m).mul
        (measurable_guerraUD_joint s β W h t (j + 1)))

theorem measurable_guerraUUD {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h t : ℝ) (j : ℕ) :
    Measurable (guerraUUD n s β U V W h t j) :=
  (measurable_guerraUUD_joint s β V W h t j).comp (measurable_const.prodMk measurable_id)

/-- A finite bound for mixed derivatives, uniform in `U` and the cascade field.
Only integrability needs this coarse bound; the overlap calculation uses the exact recursion. -/
noncomputable def guerraUUBound (n : ℕ) (V W : EnergySpace n) (t : ℝ) (j : ℕ) : ℝ :=
  2 * ((j : ℝ) + 1) * (Real.sqrt t * uAbs n V) * (Real.sqrt t * uAbs n W)

theorem guerraUUBound_nonneg (n : ℕ) (V W : EnergySpace n) (t : ℝ) (j : ℕ) :
    0 ≤ guerraUUBound n V W t j := by
  unfold guerraUUBound
  have := uAbs_nonneg n V
  have := uAbs_nonneg n W
  positivity

theorem abs_guerraUUD_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (x : Fin n → ℝ) :
    |guerraUUD n s β U V W h t j x| ≤ guerraUUBound n V W t j := by
  induction j generalizing x with
  | zero => simpa [guerraUUD, guerraUUBound] using abs_guerraBaseUUDeriv_le n U V W h t x
  | succ j ih =>
      set m := s.m (k + 1 - j)
      set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
      set BV := Real.sqrt t * uAbs n V
      set BW := Real.sqrt t * uAbs n W
      have hBV : 0 ≤ BV := mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg n V)
      have hBW : 0 ≤ BW := mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg n W)
      have hm0 : 0 ≤ m := s.m_nonneg (by omega)
      have hm1 : m ≤ 1 := s.m_le_one (by omega)
      have hmabs : |m| ≤ 1 := by rwa [abs_of_nonneg hm0]
      have hVB := guerraUD_measurable_and_bound n s β U V h ht j
      have hWB := guerraUD_measurable_and_bound n s β U W h ht j
      have hG : ∀ y, |guerraUUD n s β U V W h t j y +
          m * guerraUD n s β U V h t j y * guerraUD n s β U W h t j y| ≤
          guerraUUBound n V W t j + BV * BW := by
        intro y
        refine (abs_add_le _ _).trans (add_le_add (ih y) ?_)
        rw [abs_mul, abs_mul]
        calc
          _ ≤ (1 * BV) * BW := mul_le_mul
            (mul_le_mul hmabs (hVB.2 y) (abs_nonneg _) (by positivity))
            (hWB.2 y) (abs_nonneg _) (by positivity)
          _ = _ := by ring
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      have hI := abs_integral_mul_tiltWeightPi_le
        (m := m) (v := v) (C := a + b * uAbs n U) (D := D) (L := L)
        hL hD (hAlip t htt) (hAb t htt) (hAm t htt)
        ((measurable_guerraUUD s β U V W h t j).add ((hVB.1.const_mul m).mul hWB.1))
        (C' := guerraUUBound n V W t j + BV * BW) (D' := 0) le_rfl
        (by simpa using hG) x
      simp only [zero_mul, add_zero] at hI
      have hP : |m * guerraUD n s β U V h t (j + 1) x *
          guerraUD n s β U W h t (j + 1) x| ≤ BV * BW := by
        rw [abs_mul, abs_mul]
        calc
          _ ≤ (1 * BV) * BW := mul_le_mul
            (mul_le_mul hmabs
              ((guerraUD_measurable_and_bound n s β U V h ht (j + 1)).2 x)
              (abs_nonneg _) (by positivity))
            ((guerraUD_measurable_and_bound n s β U W h ht (j + 1)).2 x)
            (abs_nonneg _) (by positivity)
          _ = _ := by ring
      change |(∫ z, (guerraUUD n s β U V W h t j (fun i => x i + Real.sqrt v * z i) +
          m * guerraUD n s β U V h t j (fun i => x i + Real.sqrt v * z i) *
            guerraUD n s β U W h t j (fun i => x i + Real.sqrt v * z i)) *
          tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n) -
          m * guerraUD n s β U V h t (j + 1) x * guerraUD n s β U W h t (j + 1) x| ≤ _
      refine (abs_sub _ _).trans ((add_le_add hI hP).trans ?_)
      dsimp [guerraUUBound, BV, BW]
      push_cast
      ring_nf
      rfl

/-- Every first disorder derivative is differentiable along any other disorder line. -/
theorem hasDerivAt_guerraUD_Uline {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (x : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun u => guerraUD n s β (U + u • W) V h t j x)
      (guerraUUD n s β (U + r • W) V W h t j x) r := by
  induction j generalizing x r with
  | zero => exact hasDerivAt_guerraBaseUDeriv_Uline n U V W h t x r
  | succ j ih =>
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      set m := s.m (k + 1 - j)
      set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
      have hlinebound : ∀ u ∈ guerraLineNbhd r,
          uAbs n (U + u • W) ≤ uAbs n U + (|r| + 1) * uAbs n W := by
        intro u hu
        refine (uAbs_add_smul_le n U W u).trans ?_
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (abs_le_abs_add_one_of_mem_guerraLineNbhd hu) (uAbs_nonneg n W))
      exact hasDerivAt_tiltAvg_param_pi
        (A := fun u => cascadeT n s β 1 (guerraBase n (U + u • W) h t) j)
        (A' := fun u => guerraUD n s β (U + u • W) W h t j)
        (G := fun u => guerraUD n s β (U + u • W) V h t j)
        (G' := fun u => guerraUUD n s β (U + u • W) V W h t j)
        (m := m) (v := v) (C := a + b * (uAbs n U + (|r| + 1) * uAbs n W)) (D := D)
        (BA := Real.sqrt t * uAbs n W) (BG := Real.sqrt t * uAbs n V)
        (BG' := guerraUUBound n V W t j) x (guerraLineNbhd_mem_nhds r) hD
        (fun u _ y => hasDerivAt_cascade_Uline n s β U W h ht j y u)
        (fun u _ y => ih y u)
        (fun u _ => (hprops (U + u • W)).1 t htt)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • W) W h ht j).1)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • W) V h ht j).1)
        (fun u _ => measurable_guerraUUD s β (U + u • W) V W h t j)
        (fun u hu y => by
          have hbu := (hprops (U + u • W)).2.2.1 t htt y
          have hmul := mul_le_mul_of_nonneg_left (hlinebound u hu) hb
          linarith)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • W) W h ht j).2)
        (fun u _ => (guerraUD_measurable_and_bound n s β (U + u • W) V h ht j).2)
        (fun u _ y => abs_guerraUUD_le n s β (U + u • W) V W h ht j y)

/-- Gaussian integration by parts applied to a first disorder derivative, at any
cascade depth.  All derivative and integrability hypotheses are discharged. -/
theorem guerra_gradient_stein {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (V a : EnergySpace N)
    (j : ℕ) (x : Fin N → ℝ) :
    (∫ ω, inner ℝ (sk.U ω) a * guerraUD N s β (sk.U ω) V h t j x ∂ℙ) =
      ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * inner ℝ a (sk.hU.w i) *
        ∫ ω, guerraUUD N s β (sk.U ω) V (sk.hU.w i) h t j x ∂ℙ := by
  let Φ := fun U => guerraUD N s β U V h t j x
  let D := fun (i : sk.hU.ι) U => guerraUUD N s β U V (sk.hU.w i) h t j x
  have hΦm : Measurable Φ := (measurable_guerraUD_joint s β V h t j).comp
    (measurable_id.prodMk measurable_const)
  have hDm : ∀ i : sk.hU.ι, Measurable (D i) := fun i =>
    (measurable_guerraUUD_joint s β V (sk.hU.w i) h t j).comp
      (measurable_id.prodMk measurable_const)
  have hC : 0 ≤ Real.sqrt t * uAbs N V := mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg N V)
  have hΦb : ∀ U, |Φ U| ≤ Real.sqrt t * uAbs N V + 0 * ‖U‖ := by
    intro U
    simpa only [zero_mul, add_zero] using (guerraUD_measurable_and_bound N s β U V h ht j).2 x
  have hintCoord : ∀ i : sk.hU.ι, Integrable (fun ω => sk.hU.c i ω * Φ (sk.U ω)) ℙ :=
    fun i => integrable_coord_mul_comp_of_affine_norm_bound sk.hU i hΦm hC le_rfl hΦb
  have hintΦ : Integrable (fun ω => Φ (sk.U ω)) ℙ :=
    integrable_comp_of_affine_norm_bound sk.hU hΦm hC le_rfl hΦb
  have hintD : ∀ i : sk.hU.ι, Integrable (fun ω => D i (sk.U ω)) ℙ := by
    intro i
    refine integrable_comp_of_affine_norm_bound sk.hU (hDm i)
      (guerraUUBound_nonneg N V (sk.hU.w i) t j) (D := 0) le_rfl ?_
    intro U
    simpa only [zero_mul, add_zero] using abs_guerraUUD_le N s β U V (sk.hU.w i) h ht j x
  exact stein_inner_of_hasDerivAt sk.hU a
    (fun i U r => hasDerivAt_guerraUD_Uline N s β U V (sk.hU.w i) h ht j x r)
    hΦm hDm hintCoord hintΦ hintD

/-- Finite linear combinations commute with a Gibbs average. -/
theorem gibbsAvg_sum_mul {n : ℕ} {ι : Type*} [Fintype ι] (E : Config n → ℝ)
    (c : ι → ℝ) (f : ι → Config n → ℝ) :
    gibbsAvg E (fun σ => ∑ i, c i * f i σ) = ∑ i, c i * gibbsAvg E (f i) := by
  classical
  unfold gibbsAvg
  have hsum : (∑ σ, Real.exp (E σ) * ∑ i, c i * f i σ) =
      ∑ i, c i * ∑ σ, Real.exp (E σ) * f i σ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun σ _ => by ring))
  rw [hsum, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The propagated first derivative is linear in its direction.  The finite
interchange of sum and integral includes the tilted-integrability proof. -/
theorem guerraUD_sum_smul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (V : ι → EnergySpace n)
    (j : ℕ) (x : Fin n → ℝ) :
    guerraUD n s β U (∑ i, c i • V i) h t j x =
      ∑ i, c i * guerraUD n s β U (V i) h t j x := by
  classical
  induction j generalizing x with
  | zero =>
      have hdir : (fun σ : Config n => (∑ i, c i • V i) σ) =
          fun σ => ∑ i, c i * V i σ := by
        funext σ
        change (WithLp.ofLp (∑ i, c i • V i)) σ = _
        simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      change Real.sqrt t * gibbsAvg (guerraH n U h t x) (fun σ => (∑ i, c i • V i) σ) =
        ∑ i, c i * (Real.sqrt t * gibbsAvg (guerraH n U h t x) (V i))
      rw [hdir, gibbsAvg_sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  | succ j ih =>
      set m := s.m (k + 1 - j)
      set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
      obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
        guerra_cascade_hasDerivAt n s β h ht j
      obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
      have htt : t ∈ talNbhd t := self_mem_talNbhd ht
      have hint : ∀ i : ι, Integrable (fun z => c i *
          (guerraUD n s β U (V i) h t j (fun l => x l + Real.sqrt v * z l) *
            tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z)) (piGauss n) := by
        intro i
        have hVB := guerraUD_measurable_and_bound n s β U (V i) h ht j
        exact (integrable_mul_tiltWeightPi_of_bound (m := m) (v := v) hL hD
          (hAlip t htt) (hAb t htt) (hAm t htt) x (hVB.1.comp (measurable_shift v x))
          (a := Real.sqrt t * uAbs n (V i)) (b := 0) le_rfl
          (fun z => by simpa using hVB.2 (fun l => x l + Real.sqrt v * z l))).const_mul (c i)
      change (∫ z, guerraUD n s β U (∑ i, c i • V i) h t j
          (fun l => x l + Real.sqrt v * z l) *
          tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n) = _
      simp_rw [ih, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ (fun i _ => hint i)]
      simp only [integral_const_mul]
      rfl

/-- The disorder integration-by-parts identity for the cascade: the expected
radial derivative is the covariance-weighted trace of the disorder Hessian.
At the top level this is the disorder contribution to Talagrand's interpolation
derivative up to the factor `1 / (2 * N * t)`, before rewriting it in terms of
two-replica overlaps. -/
theorem guerra_disorder_stein {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (x : Fin N → ℝ) :
    (∫ ω, guerraUD N s β (sk.U ω) (sk.U ω) h t j x ∂ℙ) =
      ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        ∫ ω, guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t j x ∂ℙ := by
  classical
  let Φ := fun (i : sk.hU.ι) U => guerraUD N s β U (sk.hU.w i) h t j x
  let D := fun (i : sk.hU.ι) U => guerraUUD N s β U (sk.hU.w i) (sk.hU.w i) h t j x
  have hΦm : ∀ i, Measurable (Φ i) := fun i =>
    (measurable_guerraUD_joint s β (sk.hU.w i) h t j).comp
      (measurable_id.prodMk measurable_const)
  have hDm : ∀ i, Measurable (D i) := fun i =>
    (measurable_guerraUUD_joint s β (sk.hU.w i) (sk.hU.w i) h t j).comp
      (measurable_id.prodMk measurable_const)
  have hC : ∀ i, 0 ≤ Real.sqrt t * uAbs N (sk.hU.w i) := fun i =>
    mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg N _)
  have hΦb : ∀ i U, |Φ i U| ≤ Real.sqrt t * uAbs N (sk.hU.w i) + 0 * ‖U‖ := by
    intro i U
    simpa only [zero_mul, add_zero] using
      (guerraUD_measurable_and_bound N s β U (sk.hU.w i) h ht j).2 x
  have hintCoord : ∀ i, Integrable (fun ω => sk.hU.c i ω * Φ i (sk.U ω)) ℙ := fun i =>
    integrable_coord_mul_comp_of_affine_norm_bound sk.hU i (hΦm i) (hC i) le_rfl (hΦb i)
  have hintΦ : ∀ i, Integrable (fun ω => Φ i (sk.U ω)) ℙ := fun i =>
    integrable_comp_of_affine_norm_bound sk.hU (hΦm i) (hC i) le_rfl (hΦb i)
  have hintD : ∀ i, Integrable (fun ω => D i (sk.U ω)) ℙ := by
    intro i
    refine integrable_comp_of_affine_norm_bound sk.hU (hDm i)
      (guerraUUBound_nonneg N (sk.hU.w i) (sk.hU.w i) t j) (D := 0) le_rfl ?_
    intro U
    simpa only [zero_mul, add_zero] using
      abs_guerraUUD_le N s β U (sk.hU.w i) (sk.hU.w i) h ht j x
  have hexpand : ∀ ω, guerraUD N s β (sk.U ω) (sk.U ω) h t j x =
      ∑ i, sk.hU.c i ω * Φ i (sk.U ω) := by
    intro ω
    have hrepr : sk.U ω = ∑ i, sk.hU.c i ω • sk.hU.w i := congrFun sk.hU.repr ω
    calc
      guerraUD N s β (sk.U ω) (sk.U ω) h t j x =
          guerraUD N s β (sk.U ω) (∑ i, sk.hU.c i ω • sk.hU.w i) h t j x :=
        congrArg (fun V => guerraUD N s β (sk.U ω) V h t j x) hrepr
      _ = _ := guerraUD_sum_smul N s β (sk.U ω) h ht (fun i => sk.hU.c i ω) sk.hU.w j x
  calc
    (∫ ω, guerraUD N s β (sk.U ω) (sk.U ω) h t j x ∂ℙ) =
        ∫ ω, ∑ i, sk.hU.c i ω * Φ i (sk.U ω) ∂ℙ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = _ := stein_sum_of_hasDerivAt sk.hU
      (fun i U r => hasDerivAt_guerraUD_Uline N s β U (sk.hU.w i) (sk.hU.w i) h ht j x r)
      hΦm hDm hintCoord hintΦ hintD

/-! ## 2h. Cascade-field derivatives

For `t > 0`, translating the field is exactly a disorder translation in the
direction represented by the spin-field pairing.  This identifies the field
derivatives with the already proved disorder derivatives at every depth.
-/

/-- A field direction embedded in the disorder space with the interpolation scaling. -/
noncomputable def guerraFieldDirection (n : ℕ) (t : ℝ) (a : Fin n → ℝ) : EnergySpace n :=
  WithLp.toLp 2 (fun σ => (Real.sqrt (1 - t) / Real.sqrt t) * ∑ i, spin n σ i * a i)

theorem guerraH_field_shift (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : 0 < t)
    (a y : Fin n → ℝ) (r : ℝ) (σ : Config n) :
    guerraH n U h t (y + r • a) σ =
      guerraH n (U + r • guerraFieldDirection n t a) h t y σ := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hdir : Real.sqrt t * guerraFieldDirection n t a σ =
      Real.sqrt (1 - t) * ∑ i, spin n σ i * a i := by
    dsimp [guerraFieldDirection]
    field_simp
  have hsum : (∑ i, spin n σ i * (Real.sqrt (1 - t) * (y + r • a) i + h)) =
      (∑ i, spin n σ i * (Real.sqrt (1 - t) * y i + h)) +
        r * (Real.sqrt t * guerraFieldDirection n t a σ) := by
    rw [hdir, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [guerraH, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hsum]
  ring

theorem guerraBase_field_shift (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : 0 < t)
    (a y : Fin n → ℝ) (r : ℝ) :
    guerraBase n U h t (y + r • a) =
      guerraBase n (U + r • guerraFieldDirection n t a) h t y := by
  simp only [guerraBase, guerraH_field_shift n U h ht a y r]

/-- Translating the free field commutes with all cascade integrations. -/
theorem guerraCascade_field_shift {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : 0 < t)
    (a x : Fin n → ℝ) (r : ℝ) (j : ℕ) :
    cascadeT n s β 1 (guerraBase n U h t) j (x + r • a) =
      cascadeT n s β 1 (guerraBase n (U + r • guerraFieldDirection n t a) h t) j x := by
  rw [← cascadeT_shift n s β 1 (guerraBase n U h t) (r • a) j x]
  have hbase : (fun y => guerraBase n U h t (y + r • a)) =
      guerraBase n (U + r • guerraFieldDirection n t a) h t :=
    funext (fun y => guerraBase_field_shift n U h ht a y r)
  rw [hbase]

theorem guerraUD_field_shift {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a x : Fin n → ℝ) (r : ℝ) (j : ℕ) :
    guerraUD n s β U V h t j (x + r • a) =
      guerraUD n s β (U + r • guerraFieldDirection n t a) V h t j x := by
  have hleft := hasDerivAt_cascade_Uline n s β U V h ht j (x + r • a) 0
  have hright := hasDerivAt_cascade_Uline n s β (U + r • guerraFieldDirection n t a) V h ht j x 0
  have hfun : (fun u : ℝ => cascadeT n s β 1 (guerraBase n (U + u • V) h t) j (x + r • a)) =
      fun u : ℝ => cascadeT n s β 1 (guerraBase n (U + r • guerraFieldDirection n t a + u • V) h t) j x := by
    funext u
    rw [guerraCascade_field_shift n s β (U + u • V) h ht.1 a x r j]
    rw [show U + u • V + r • guerraFieldDirection n t a =
      U + r • guerraFieldDirection n t a + u • V by abel]
  rw [hfun] at hleft
  simpa only [zero_smul, add_zero] using hleft.unique hright

theorem guerraUUD_field_shift {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a x : Fin n → ℝ) (r : ℝ) (j : ℕ) :
    guerraUUD n s β U V W h t j (x + r • a) =
      guerraUUD n s β (U + r • guerraFieldDirection n t a) V W h t j x := by
  have hleft := hasDerivAt_guerraUD_Uline n s β U V W h ht j (x + r • a) 0
  have hright := hasDerivAt_guerraUD_Uline n s β (U + r • guerraFieldDirection n t a) V W h ht j x 0
  have hfun : (fun u : ℝ => guerraUD n s β (U + u • W) V h t j (x + r • a)) =
      fun u : ℝ => guerraUD n s β (U + r • guerraFieldDirection n t a + u • W) V h t j x := by
    funext u
    rw [guerraUD_field_shift n s β (U + u • W) V h ht a x r j]
    rw [show U + u • W + r • guerraFieldDirection n t a =
      U + r • guerraFieldDirection n t a + u • W by abel]
  rw [hfun] at hleft
  simpa only [zero_smul, add_zero] using hleft.unique hright

/-- First field derivative in direction `a`. -/
noncomputable def guerraYD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (a : Fin n → ℝ) (h t : ℝ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  guerraUD n s β U (guerraFieldDirection n t a) h t j x

/-- Mixed field derivative in directions `a,b`. -/
noncomputable def guerraYYD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (a b : Fin n → ℝ) (h t : ℝ) (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  guerraUUD n s β U (guerraFieldDirection n t a) (guerraFieldDirection n t b) h t j x

theorem hasDerivAt_guerraCascade_Yline {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a x : Fin n → ℝ) (r : ℝ) (j : ℕ) :
    HasDerivAt (fun u => cascadeT n s β 1 (guerraBase n U h t) j (x + u • a))
      (guerraYD n s β U a h t j (x + r • a)) r := by
  simp only [guerraYD, guerraCascade_field_shift n s β U h ht.1 a x,
    guerraUD_field_shift n s β U (guerraFieldDirection n t a) h ht a x r j]
  exact hasDerivAt_cascade_Uline n s β U (guerraFieldDirection n t a) h ht j x r

theorem hasDerivAt_guerraYD_Yline {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a b x : Fin n → ℝ) (r : ℝ) (j : ℕ) :
    HasDerivAt (fun u => guerraYD n s β U a h t j (x + u • b))
      (guerraYYD n s β U a b h t j (x + r • b)) r := by
  simp only [guerraYD, guerraYYD,
    guerraUD_field_shift n s β U (guerraFieldDirection n t a) h ht b x,
    guerraUUD_field_shift n s β U (guerraFieldDirection n t a) (guerraFieldDirection n t b) h ht b x r j]
  exact hasDerivAt_guerraUD_Uline n s β U (guerraFieldDirection n t a)
    (guerraFieldDirection n t b) h ht j x r

/-- A single-site field direction is the corresponding spin observable. -/
theorem guerraFieldDirection_single (n : ℕ) (t : ℝ) (i : Fin n) (σ : Config n) :
    guerraFieldDirection n t (Pi.single i 1) σ =
      (Real.sqrt (1 - t) / Real.sqrt t) * spin n σ i := by
  simp [guerraFieldDirection, Pi.single_apply]

theorem guerraFieldDirection_eq_sum (n : ℕ) (t : ℝ) (a : Fin n → ℝ) :
    guerraFieldDirection n t a = ∑ i, a i • guerraFieldDirection n t (Pi.single i 1) := by
  ext σ
  change (Real.sqrt (1 - t) / Real.sqrt t) * (∑ i, spin n σ i * a i) =
    (WithLp.ofLp (∑ i, a i • guerraFieldDirection n t (Pi.single i 1))) σ
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  change (Real.sqrt (1 - t) / Real.sqrt t) * (∑ i, spin n σ i * a i) =
    ∑ i, a i * guerraFieldDirection n t (Pi.single i 1) σ
  simp_rw [guerraFieldDirection_single]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Expand a directional field derivative into its site-coordinate derivatives. -/
theorem guerraYD_eq_sum {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a x : Fin n → ℝ) (j : ℕ) :
    guerraYD n s β U a h t j x = ∑ i, a i * guerraYD n s β U (Pi.single i 1) h t j x := by
  unfold guerraYD
  rw [guerraFieldDirection_eq_sum, guerraUD_sum_smul n s β U h ht]

theorem measurable_guerraYD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (a : Fin n → ℝ) (j : ℕ) : Measurable (guerraYD n s β U a h t j) :=
  (guerraUD_measurable_and_bound n s β U (guerraFieldDirection n t a) h ht j).1

theorem measurable_guerraYYD {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (a b : Fin n → ℝ) (j : ℕ) :
    Measurable (guerraYYD n s β U a b h t j) :=
  measurable_guerraUUD s β U (guerraFieldDirection n t a) (guerraFieldDirection n t b) h t j

/-- The conditional field integration-by-parts identity at every cascade level.
Both the Hessian term and the derivative of the tilted weight are retained. -/
theorem guerra_field_stein {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    let m := s.m (k + 1 - j)
    let v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
    (∫ z, z i * (guerraYD n s β U (Pi.single i 1) h t j
        (fun l => x l + Real.sqrt v * z l) *
      tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z) ∂piGauss n) =
      Real.sqrt v * ∫ z, (guerraYYD n s β U (Pi.single i 1) (Pi.single i 1) h t j
          (fun l => x l + Real.sqrt v * z l) +
        m * (guerraYD n s β U (Pi.single i 1) h t j (fun l => x l + Real.sqrt v * z l)) ^ 2) *
        tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n := by
  dsimp only
  set m := s.m (k + 1 - j)
  set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
  obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
    guerra_cascade_hasDerivAt n s β h ht j
  obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
  have htt : t ∈ talNbhd t := self_mem_talNbhd ht
  have hGm := measurable_guerraYD n s β U h ht (Pi.single i 1) j
  have hG'm := measurable_guerraYYD n s β U h t (Pi.single i 1) (Pi.single i 1) j
  have hG := (guerraUD_measurable_and_bound n s β U
    (guerraFieldDirection n t (Pi.single i 1)) h ht j).2
  have hG' := abs_guerraUUD_le n s β U (guerraFieldDirection n t (Pi.single i 1))
    (guerraFieldDirection n t (Pi.single i 1)) h ht j
  have hs := stein_tiltWeightPi (m := m) (v := v) i x hD hL
    (hAm t htt) hGm hGm hG'm (hAb t htt) (hAlip t htt) hG hG hG'
    (fun y r => hasDerivAt_guerraCascade_Yline n s β U h ht (Pi.single i 1) y r j)
    (fun y r => hasDerivAt_guerraYD_Yline n s β U h ht (Pi.single i 1) (Pi.single i 1) y r j)
  simpa only [pow_two, mul_assoc] using hs

/-- Multiplying by the increment scale turns the two square roots into its
variance.  This also covers a zero-variance cascade level. -/
theorem guerra_field_increment_stein {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    let m := s.m (k + 1 - j)
    let v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
    Real.sqrt v * (∫ z, z i * (guerraYD n s β U (Pi.single i 1) h t j
        (fun l => x l + Real.sqrt v * z l) *
      tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z) ∂piGauss n) =
      v * ∫ z, (guerraYYD n s β U (Pi.single i 1) (Pi.single i 1) h t j
          (fun l => x l + Real.sqrt v * z l) +
        m * (guerraYD n s β U (Pi.single i 1) h t j (fun l => x l + Real.sqrt v * z l)) ^ 2) *
        tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n := by
  dsimp only
  rw [guerra_field_stein n s β U h ht j i x, ← mul_assoc,
    Real.mul_self_sqrt (levelVar_nonneg s β j)]

/-- The radial field derivative after one tilted integration equals the radial
derivative at the next level plus the full Gaussian-increment correction.
This sums the coordinate IBP identities with all integral interchanges justified. -/
theorem guerra_field_radial_step {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (x : Fin n → ℝ) :
    let m := s.m (k + 1 - j)
    let v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
    let S := fun z : Fin n → ℝ => fun l => x l + Real.sqrt v * z l
    (∫ z, guerraYD n s β U (S z) h t j (S z) *
      tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n) =
      guerraYD n s β U x h t (j + 1) x +
        v * ∑ i, ∫ z, (guerraYYD n s β U (Pi.single i 1) (Pi.single i 1) h t j (S z) +
          m * (guerraYD n s β U (Pi.single i 1) h t j (S z)) ^ 2) *
          tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n := by
  dsimp only
  set m := s.m (k + 1 - j)
  set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
  let S := fun z : Fin n → ℝ => fun l => x l + Real.sqrt v * z l
  let K := fun z => tiltWeightPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) x z
  let B := fun (i : Fin n) z => guerraYD n s β U (Pi.single i 1) h t j (S z) * K z
  let J := fun i : Fin n => ∫ z,
    (guerraYYD n s β U (Pi.single i 1) (Pi.single i 1) h t j (S z) +
      m * (guerraYD n s β U (Pi.single i 1) h t j (S z)) ^ 2) * K z ∂piGauss n
  obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
    guerra_cascade_hasDerivAt n s β h ht j
  obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
  have htt : t ∈ talNbhd t := self_mem_talNbhd ht
  have hint : ∀ i, Integrable (B i) (piGauss n) := by
    intro i
    have hGi := guerraUD_measurable_and_bound n s β U
      (guerraFieldDirection n t (Pi.single i 1)) h ht j
    exact integrable_mul_tiltWeightPi_of_bound hL hD (hAlip t htt) (hAb t htt) (hAm t htt) x
      (hGi.1.comp (measurable_shift v x)) (b := 0) le_rfl
      (fun z => by simpa only [guerraYD, zero_mul, add_zero] using hGi.2 (S z))
  have hzint : ∀ i, Integrable (fun z => z i * B i z) (piGauss n) := by
    intro i
    have hGi := guerraUD_measurable_and_bound n s β U
      (guerraFieldDirection n t (Pi.single i 1)) h ht j
    exact integrable_coord_mul_tiltWeightPi i x hD hL (hAm t htt) hGi.1
      (hAb t htt) (hAlip t htt) hGi.2
  have hexpand : ∀ z, guerraYD n s β U (S z) h t j (S z) * K z =
      ∑ i, (x i * B i z + Real.sqrt v * (z i * B i z)) := by
    intro z
    rw [guerraYD_eq_sum n s β U h ht (S z) (S z) j, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp [B, S]
    ring
  have hterm : ∀ i, x i * (∫ z, B i z ∂piGauss n) +
      Real.sqrt v * (∫ z, z i * B i z ∂piGauss n) =
      x i * guerraYD n s β U (Pi.single i 1) h t (j + 1) x + v * J i := by
    intro i
    have hi := guerra_field_increment_stein n s β U h ht j i x
    change Real.sqrt v * (∫ z, z i * B i z ∂piGauss n) = v * J i at hi
    rw [hi]
    rfl
  change (∫ z, guerraYD n s β U (S z) h t j (S z) * K z ∂piGauss n) =
    guerraYD n s β U x h t (j + 1) x + v * ∑ i, J i
  have hxi : ∀ i, Integrable (fun z => x i * B i z) (piGauss n) :=
    fun i => (hint i).const_mul (x i)
  have hzi : ∀ i, Integrable (fun z => Real.sqrt v * (z i * B i z)) (piGauss n) :=
    fun i => (hzint i).const_mul (Real.sqrt v)
  have hsumint : ∀ i, Integrable (fun z => x i * B i z + Real.sqrt v * (z i * B i z)) (piGauss n) :=
    fun i => (hxi i).add (hzi i)
  calc
    _ = ∫ z, ∑ i, (x i * B i z + Real.sqrt v * (z i * B i z)) ∂piGauss n :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i, (x i * (∫ z, B i z ∂piGauss n) +
        Real.sqrt v * (∫ z, z i * B i z ∂piGauss n)) := by
      rw [integral_finsetSum _ (fun i _ => hsumint i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_add (hxi i) (hzi i),
        integral_const_mul, integral_const_mul]
    _ = ∑ i, (x i * guerraYD n s β U (Pi.single i 1) h t (j + 1) x + v * J i) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← guerraYD_eq_sum n s β U h ht x x (j + 1)]

/-! ## 2i. Continuity on the closed interpolation interval -/

/-- Uniform affine growth and continuity of every cascade level on `[0,1]`.
No bound on the square-root derivatives at the endpoints is required. -/
theorem guerra_cascade_continuous_Icc {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) (j : ℕ) :
    ∃ a D : ℝ, 0 ≤ D ∧ ∀ U : EnergySpace n,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Measurable (cascadeT n s β 1 (guerraBase n U h t) j)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y,
        |cascadeT n s β 1 (guerraBase n U h t) j y| ≤ a + uAbs n U + D * l1 y) ∧
      (∀ y, ContinuousOn (fun t => cascadeT n s β 1 (guerraBase n U h t) j y) (Set.Icc (0 : ℝ) 1)) := by
  induction j with
  | zero =>
      refine ⟨Real.log (Fintype.card (Config n)) + Fintype.card (Config n) * (n * |h|),
        Fintype.card (Config n), by positivity, fun U => ?_⟩
      refine ⟨fun t _ => measurable_guerraBase n U h t, fun t ht y => ?_, fun y => ?_⟩
      · have hb := abs_guerraBase_le n U h ht.1 ht.2 y
        change |guerraBase n U h t y| ≤ _
        linarith
      · have hZ : Continuous (fun t : ℝ => ∑ σ : Config n, Real.exp (guerraH n U h t y σ)) := by
          refine continuous_finsetSum _ (fun σ _ => Real.continuous_exp.comp ?_)
          unfold guerraH
          fun_prop
        exact (hZ.log (fun t => (Finset.sum_pos (fun σ _ => Real.exp_pos _)
          Finset.univ_nonempty).ne')).continuousOn
  | succ j ih =>
      obtain ⟨a, D, hD, hprops⟩ := ih
      set m := s.m (k + 1 - j)
      set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
      refine ⟨a + stepK n m v D, D, hD, fun U => ?_⟩
      obtain ⟨hAm, hAb, hAc⟩ := hprops U
      refine ⟨fun t ht => measurable_parisiStepPi (hAm t ht) m v, fun t ht y => ?_, fun y => ?_⟩
      · have hb := parisiStepPi_abs_le (m := m) (v := v)
          (s.m_nonneg (by omega)) (levelVar_nonneg s β j) hD (hAb t ht) (hAm t ht) y
        change |parisiStepPi n m v (cascadeT n s β 1 (guerraBase n U h t) j) y| ≤ _
        linarith
      · exact continuousOn_parisiStepPi_param hD hAm hAb hAc y

/-- Continuity of the interpolation pressure, including both endpoints. -/
theorem continuousOn_guerraPhi {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (guerraPhi N s β h sk.U) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc N s β h (k + 2)
  have hc : ContinuousOn (fun t => ∫ ω,
      cascadeT N s β 1 (guerraBase N (sk.U ω) h t) (k + 2) 0 ∂ℙ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (bound := fun ω => a + Fintype.card (Config N) * ‖sk.U ω‖)
    · intro t _
      exact ((measurable_cascade_top_U s β h t).comp sk.hU.repr_measurable).aestronglyMeasurable
    · intro t ht
      filter_upwards with ω
      have hb := (hprops (sk.U ω)).2.1 t ht 0
      simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hb
      rw [Real.norm_eq_abs]
      exact hb.trans (add_le_add_right (uAbs_le_card_mul_norm N (sk.U ω)) a)
    · exact (integrable_const a).add
        ((PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian sk.hU).const_mul _)
    · exact Filter.Eventually.of_forall (fun ω => (hprops (sk.U ω)).2.2 0)
  exact hc.const_mul (1 / (N : ℝ))

/-! ## 2j. Normalized cascade averages and two replicas -/

/-- The normalized conditional average at one cascade level. -/
noncomputable def guerraStepAvg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ z, f (fun i => x i + Real.sqrt
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i) *
    tiltWeightPi n (s.m (k + 1 - j))
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
      (cascadeT n s β 1 (guerraBase n U h t) j) x z ∂piGauss n

theorem integrable_guerraStepAvg_integrand {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {a b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ y, |f y| ≤ a + b * l1 y) (x : Fin n → ℝ) :
    Integrable (fun z => f (fun i => x i + Real.sqrt
        (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) * z i) *
      tiltWeightPi n (s.m (k + 1 - j))
        (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))))
        (cascadeT n s β 1 (guerraBase n U h t) j) x z) (piGauss n) := by
  obtain ⟨c, d, D, L, a', b', D', hd, hD, hL, hb', hD', hprops⟩ :=
    guerra_cascade_hasDerivAt n s β h ht j
  obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
  have htt := self_mem_talNbhd ht
  set v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
  apply integrable_mul_tiltWeightPi_of_bound hL hD (hAlip t htt) (hAb t htt) (hAm t htt) x
    (hf.comp (measurable_shift v x)) (b := b * Real.sqrt v) (mul_nonneg hb (Real.sqrt_nonneg _))
  intro z
  calc
    _ ≤ a + b * l1 (fun i => x i + Real.sqrt v * z i) := hbound _
    _ ≤ a + b * (l1 x + Real.sqrt v * l1 z) := by gcongr; exact l1_shift_le v x z
    _ = (a + b * l1 x) + (b * Real.sqrt v) * l1 z := by ring

theorem guerraStepAvg_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun _ => c) x = c := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc n s β h j
  unfold guerraStepAvg
  rw [integral_const_mul, tiltWeightPi_integral_one hD ((hprops U).2.1 t ht)
    ((hprops U).1 t ht), mul_one]

theorem guerraStepAvg_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : ∀ y, 0 ≤ f y) (x : Fin n → ℝ) :
    0 ≤ guerraStepAvg n s β U h t j f x := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc n s β h j
  exact integral_nonneg (fun z => mul_nonneg (hf _)
    (tiltWeightPi_nonneg hD ((hprops U).2.1 t ht) ((hprops U).1 t ht) x z))

theorem guerraStepAvg_abs_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ y, |f y| ≤ C) (x : Fin n → ℝ) :
    |guerraStepAvg n s β U h t j f x| ≤ C := by
  obtain ⟨a, b, D, L, a', b', D', hb, hD, hL, hb', hD', hprops⟩ :=
    guerra_cascade_hasDerivAt n s β h ht j
  obtain ⟨hAm, -, hAb, hAlip, -, -⟩ := hprops U
  have htt := self_mem_talNbhd ht
  have hh := abs_integral_mul_tiltWeightPi_le (m := s.m (k + 1 - j))
    (v := 1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) hL hD (hAlip t htt) (hAb t htt)
    (hAm t htt) hf (D' := 0) le_rfl (by simpa using hbound) x
  simpa only [guerraStepAvg, zero_mul, add_zero] using hh

theorem measurable_guerraStepAvg_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ) (j : ℕ)
    {f : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hf : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => f p.1 p.2)) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraStepAvg n s β p.1 h t j (f p.1) p.2) :=
  measurable_tiltAvg_joint (F := fun U => cascadeT n s β 1 (guerraBase n U h t) j)
    (G := f) (measurable_cascade_joint (n := n) s β h t j).1 hf _ _

theorem guerraStepAvg_sum {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (f : ι → (Fin n → ℝ) → ℝ) (hf : ∀ i, Measurable (f i))
    (C : ι → ℝ) (hbound : ∀ i y, |f i y| ≤ C i) (x : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun y => ∑ i, f i y) x =
      ∑ i, guerraStepAvg n s β U h t j (f i) x := by
  unfold guerraStepAvg
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => integrable_guerraStepAvg_integrand n s β U h ht j
    (hf i) (b := 0) le_rfl (by simpa using hbound i) x)

/-- Single-replica probabilities propagated through the normalized cascade. -/
noncomputable def guerraProb {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) : ℕ → Config n → (Fin n → ℝ) → ℝ
  | 0 => fun σ y => Real.exp (guerraH n U h t y σ) /
      ∑ τ : Config n, Real.exp (guerraH n U h t y τ)
  | j + 1 => fun σ => guerraStepAvg n s β U h t j (guerraProb n s β U h t j σ)

theorem measurable_guerraProb_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (j : ℕ) (σ : Config n) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraProb n s β p.1 h t j σ p.2) := by
  induction j with
  | zero =>
      change Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
        Real.exp (guerraH n p.1 h t p.2 σ) / ∑ τ : Config n, Real.exp (guerraH n p.1 h t p.2 τ))
      have hH : ∀ τ : Config n, Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
          guerraH n p.1 h t p.2 τ) := by
        intro τ
        unfold guerraH
        fun_prop
      exact (hH σ).exp.div (Finset.measurable_sum _ (fun τ _ => (hH τ).exp))
  | succ j ih =>
      exact measurable_guerraStepAvg_joint s β h t j
        (f := fun U => guerraProb n s β U h t j σ) ih

theorem guerraProb_nonneg_sum_one {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    (∀ σ y, 0 ≤ guerraProb n s β U h t j σ y) ∧
      ∀ y, (∑ σ : Config n, guerraProb n s β U h t j σ y) = 1 := by
  induction j with
  | zero =>
      refine ⟨fun σ y => div_nonneg (Real.exp_pos _).le
        (Finset.sum_nonneg (fun τ _ => (Real.exp_pos _).le)), fun y => ?_⟩
      change (∑ σ : Config n, Real.exp (guerraH n U h t y σ) /
        ∑ τ : Config n, Real.exp (guerraH n U h t y τ)) = 1
      rw [← Finset.sum_div, div_self (Finset.sum_pos (fun τ _ => Real.exp_pos _)
        Finset.univ_nonempty).ne']
  | succ j ih =>
      refine ⟨fun σ y => guerraStepAvg_nonneg n s β U h ⟨ht.1.le, ht.2.le⟩ j (ih.1 σ) y,
        fun y => ?_⟩
      have hb : ∀ σ y, |guerraProb n s β U h t j σ y| ≤ 1 := by
        intro σ y
        rw [abs_of_nonneg (ih.1 σ y), ← ih.2 y]
        exact Finset.single_le_sum (fun τ _ => ih.1 τ y) (Finset.mem_univ σ)
      have hm : ∀ σ, Measurable (guerraProb n s β U h t j σ) :=
        fun σ => (measurable_guerraProb_joint s β h t j σ).comp
        (measurable_const.prodMk measurable_id)
      change (∑ σ : Config n, guerraStepAvg n s β U h t j (guerraProb n s β U h t j σ) y) = 1
      rw [← guerraStepAvg_sum n s β U h ht j _ hm (fun _ => 1) hb, show
        (fun x => ∑ σ : Config n, guerraProb n s β U h t j σ x) = (fun _ => 1) from funext ih.2]
      exact guerraStepAvg_const n s β U h ⟨ht.1.le, ht.2.le⟩ j 1 y

/-- Two conditionally independent replicas at a given cascade level. -/
noncomputable def guerraReplicaAvg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (K : Config n → Config n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ σ : Config n, ∑ τ : Config n,
    guerraProb n s β U h t j σ y * guerraProb n s β U h t j τ y * K σ τ

theorem measurable_guerraReplicaAvg_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (j : ℕ) (K : Config n → Config n → ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraReplicaAvg n s β p.1 h t j K p.2) := by
  exact Finset.measurable_sum _ (fun σ _ => Finset.measurable_sum _ (fun τ _ =>
    ((measurable_guerraProb_joint s β h t j σ).mul
      (measurable_guerraProb_joint s β h t j τ)).mul_const (K σ τ)))

theorem guerraReplicaAvg_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) {K : Config n → Config n → ℝ} (hK : ∀ σ τ, 0 ≤ K σ τ) (y : Fin n → ℝ) :
    0 ≤ guerraReplicaAvg n s β U h t j K y := by
  have hp := (guerraProb_nonneg_sum_one n s β U h ht j).1
  exact Finset.sum_nonneg (fun σ _ => Finset.sum_nonneg (fun τ _ =>
    mul_nonneg (mul_nonneg (hp σ y) (hp τ y)) (hK σ τ)))

theorem guerraReplicaAvg_abs_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) {K : Config n → Config n → ℝ} {C : ℝ} (hK : ∀ σ τ, |K σ τ| ≤ C)
    (y : Fin n → ℝ) : |guerraReplicaAvg n s β U h t j K y| ≤ C := by
  obtain ⟨hp, hsum⟩ := guerraProb_nonneg_sum_one n s β U h ht j
  calc
    _ ≤ ∑ σ : Config n, ∑ τ : Config n,
        guerraProb n s β U h t j σ y * guerraProb n s β U h t j τ y * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun τ _ => ?_))
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hp σ y) (hp τ y))]
      exact mul_le_mul_of_nonneg_left (hK σ τ) (mul_nonneg (hp σ y) (hp τ y))
    _ = C := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, one_mul]

/-- The remaining cascade mass, indexed from the Gibbs base downwards. -/
noncomputable def guerraMass {k : ℕ} (s : RSBScheme k) : ℕ → ℝ
  | 0 => 1
  | j + 1 => s.m (k + 1 - j)

theorem guerraMass_mem_Icc {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    guerraMass s j ∈ Set.Icc (0 : ℝ) 1 := by
  cases j with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ j => exact ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩

theorem guerraMass_drop_nonneg {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    0 ≤ guerraMass s j - guerraMass s (j + 1) := by
  cases j with
  | zero => simp [guerraMass, s.m_top]
  | succ j =>
      exact sub_nonneg.mpr (s.m_mono' (k + 1 - j) (by omega) (k + 1 - (j + 1)) (by omega))

@[simp] theorem guerraMass_top {k : ℕ} (s : RSBScheme k) : guerraMass s (k + 2) = 0 := by
  change s.m (k + 1 - (k + 1)) = 0
  simp only [Nat.sub_self, s.m_zero]

/-- Accumulated two-replica averages with weights `m_ℓ - m_{ℓ-1}`.
The kernel may depend on the level (in particular through `q_ℓ`). -/
noncomputable def guerraReplicaAccum {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (K : ℕ → Config n → Config n → ℝ) :
    ℕ → (Fin n → ℝ) → ℝ
  | 0 => fun _ => 0
  | j + 1 => guerraStepAvg n s β U h t j (fun y =>
      guerraReplicaAccum n s β U h t K j y +
        (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) y)

theorem measurable_guerraReplicaAccum_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (K : ℕ → Config n → Config n → ℝ) (j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraReplicaAccum n s β p.1 h t K j p.2) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
      exact measurable_guerraStepAvg_joint s β h t j
        (f := fun U y => guerraReplicaAccum n s β U h t K j y +
          (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) y)
        (ih.add ((measurable_guerraReplicaAvg_joint s β h t j (K j)).const_mul _))

theorem guerraReplicaAccum_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} (hK : ∀ j σ τ, 0 ≤ K j σ τ) (j : ℕ) (y : Fin n → ℝ) :
    0 ≤ guerraReplicaAccum n s β U h t K j y := by
  induction j generalizing y with
  | zero => exact le_rfl
  | succ j ih =>
      exact guerraStepAvg_nonneg n s β U h ⟨ht.1.le, ht.2.le⟩ j (fun y =>
        add_nonneg (ih y) (mul_nonneg (guerraMass_drop_nonneg s j)
          (guerraReplicaAvg_nonneg n s β U h ht j (hK j) y))) y

theorem guerraReplicaAccum_abs_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hK : ∀ j σ τ, |K j σ τ| ≤ C) (j : ℕ) (y : Fin n → ℝ) :
    |guerraReplicaAccum n s β U h t K j y| ≤ C * (1 - guerraMass s j) := by
  induction j generalizing y with
  | zero => simp [guerraReplicaAccum, guerraMass]
  | succ j ih =>
      have hm : Measurable (fun y => guerraReplicaAccum n s β U h t K j y +
          (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) y) :=
        ((measurable_guerraReplicaAccum_joint s β h t K j).comp
          (measurable_const.prodMk measurable_id)).add
        (((measurable_guerraReplicaAvg_joint s β h t j (K j)).comp
          (measurable_const.prodMk measurable_id)).const_mul _)
      apply guerraStepAvg_abs_le n s β U h ht j hm _ y
      intro x
      calc
        _ ≤ |guerraReplicaAccum n s β U h t K j x| +
            |(guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) x| :=
          abs_add_le _ _
        _ ≤ C * (1 - guerraMass s j) + (guerraMass s j - guerraMass s (j + 1)) * C := by
          refine add_le_add (ih x) ?_
          rw [abs_mul, abs_of_nonneg (guerraMass_drop_nonneg s j)]
          exact mul_le_mul_of_nonneg_left (guerraReplicaAvg_abs_le n s β U h ht j (hK j) x)
            (guerraMass_drop_nonneg s j)
        _ = C * (1 - guerraMass s (j + 1)) := by ring

theorem abs_overlap_le_one {n : ℕ} (hn : 0 < n) (σ τ : Config n) :
    |overlap n σ τ| ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold overlap
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ i, |spin n σ i * spin n τ i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = 1 := by simp [abs_mul, abs_spin, ne_of_gt hnR]

theorem guerra_overlap_sq_le_four {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (j : ℕ) (σ τ : Config n) : |(overlap n σ τ - s.q (k + 2 - j)) ^ 2| ≤ 4 := by
  have hR := abs_overlap_le_one hn σ τ
  have hq0 := s.q_nonneg (p := k + 2 - j) (by omega)
  have hq1 := s.q_le_one (p := k + 2 - j) (by omega)
  have hd : |overlap n σ τ - s.q (k + 2 - j)| ≤ 2 := by
    calc
      _ ≤ |overlap n σ τ| + |s.q (k + 2 - j)| := abs_sub _ _
      _ ≤ 2 := by rw [abs_of_nonneg hq0]; linarith
  rw [abs_of_nonneg (sq_nonneg _)]
  have hs := mul_self_le_mul_self (abs_nonneg _) hd
  nlinarith [sq_abs (overlap n σ τ - s.q (k + 2 - j))]

/-- The explicit squared-overlap remainder, extended by zero outside `(0,1)`.
Its identification with the pressure derivative is a separate assertion. -/
noncomputable def guerraRemainder {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  if t ∈ Set.Ioo (0 : ℝ) 1 then
    (β ^ 2 / 4) * ∫ ω, guerraReplicaAccum n s β (U ω) h t
      (fun j σ τ => (overlap n σ τ - s.q (k + 2 - j)) ^ 2) (k + 2) 0 ∂ℙ
  else 0

theorem guerraRemainder_nonneg_le {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (t : ℝ) :
    0 ≤ guerraRemainder n s β h U t ∧ guerraRemainder n s β h U t ≤ β ^ 2 := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · rw [guerraRemainder, if_pos ht]
    have hnn := integral_nonneg (μ := (ℙ : Measure Ω))
      (f := fun ω => guerraReplicaAccum n s β (U ω) h t
        (fun j σ τ => (overlap n σ τ - s.q (k + 2 - j)) ^ 2) (k + 2) 0)
      (fun ω => guerraReplicaAccum_nonneg n s β (U ω) h ht
        (fun j σ τ => sq_nonneg (overlap n σ τ - s.q (k + 2 - j))) (k + 2) 0)
    have hb := norm_integral_le_of_norm_le_const (μ := (ℙ : Measure Ω)) (C := 4)
      (f := fun ω => guerraReplicaAccum n s β (U ω) h t
        (fun j σ τ => (overlap n σ τ - s.q (k + 2 - j)) ^ 2) (k + 2) 0)
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, guerraMass_top, sub_zero, mul_one] using
          guerraReplicaAccum_abs_le n s β (U ω) h ht (by norm_num : (0 : ℝ) ≤ 4)
            (guerra_overlap_sq_le_four hn s) (k + 2) 0))
    simp only [probReal_univ, mul_one, Real.norm_eq_abs, abs_of_nonneg hnn] at hb
    exact ⟨mul_nonneg (by positivity) hnn, by nlinarith [sq_nonneg β]⟩
  · simp only [guerraRemainder, if_neg ht]
    exact ⟨le_rfl, sq_nonneg β⟩

theorem guerraStepAvg_const_mul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (c : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun y => c * f y) x = c * guerraStepAvg n s β U h t j f x := by
  unfold guerraStepAvg
  simp only [mul_assoc, integral_const_mul]

/-- A one-replica expectation at a cascade level. -/
noncomputable def guerraMean {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (f : Config n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ σ : Config n, guerraProb n s β U h t j σ y * f σ

theorem measurable_guerraMean_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (j : ℕ) (f : Config n → ℝ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => guerraMean n s β p.1 h t j f p.2) := by
  exact Finset.measurable_sum _ (fun σ _ => (measurable_guerraProb_joint s β h t j σ).mul_const _)

theorem guerraMean_abs_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (f : Config n → ℝ) (y : Fin n → ℝ) :
    |guerraMean n s β U h t j f y| ≤ ∑ σ, |f σ| := by
  obtain ⟨hp, hsum⟩ := guerraProb_nonneg_sum_one n s β U h ht j
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
  rw [abs_mul, abs_of_nonneg (hp σ y)]
  have hle : guerraProb n s β U h t j σ y ≤ 1 := by
    rw [← hsum y]
    exact Finset.single_le_sum (fun τ _ => hp τ y) (Finset.mem_univ σ)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (abs_nonneg (f σ))

theorem guerraMean_zero {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (f : Config n → ℝ) (y : Fin n → ℝ) :
    guerraMean n s β U h t 0 f y = gibbsAvg (guerraH n U h t y) f := by
  simp only [guerraMean, guerraProb, gibbsAvg, div_mul_eq_mul_div, Finset.sum_div]

theorem guerraMean_succ {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (f : Config n → ℝ) (y : Fin n → ℝ) :
    guerraMean n s β U h t (j + 1) f y =
      guerraStepAvg n s β U h t j (guerraMean n s β U h t j f) y := by
  have hp := guerraProb_nonneg_sum_one n s β U h ht j
  have hm : ∀ σ, Measurable (fun y => f σ * guerraProb n s β U h t j σ y) :=
    fun σ => ((measurable_guerraProb_joint s β h t j σ).comp
      (measurable_const.prodMk measurable_id)).const_mul _
  have hb : ∀ σ y, |f σ * guerraProb n s β U h t j σ y| ≤ |f σ| := by
    intro σ y
    rw [abs_mul, abs_of_nonneg (hp.1 σ y)]
    have hle : guerraProb n s β U h t j σ y ≤ 1 := by
      rw [← hp.2 y]
      exact Finset.single_le_sum (fun τ _ => hp.1 τ y) (Finset.mem_univ σ)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (abs_nonneg (f σ))
  change (∑ σ, guerraStepAvg n s β U h t j (guerraProb n s β U h t j σ) y * f σ) = _
  have he : guerraMean n s β U h t j f = fun y => ∑ σ, f σ * guerraProb n s β U h t j σ y := by
    funext y
    exact Finset.sum_congr rfl (fun σ _ => mul_comm _ _)
  rw [he, guerraStepAvg_sum n s β U h ht j _ hm (fun σ => |f σ|) hb]
  simp only [guerraStepAvg_const_mul, mul_comm]

theorem guerraReplicaAvg_mul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (f g : Config n → ℝ) (y : Fin n → ℝ) :
    guerraReplicaAvg n s β U h t j (fun σ τ => f σ * g τ) y =
      guerraMean n s β U h t j f y * guerraMean n s β U h t j g y := by
  unfold guerraReplicaAvg guerraMean
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun τ _ => by ring)

/-- The first disorder derivative is the one-replica average of its direction. -/
theorem guerraUD_eq_mean {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin n → ℝ) :
    guerraUD n s β U V h t j y = Real.sqrt t * guerraMean n s β U h t j V y := by
  induction j generalizing y with
  | zero => rw [guerraMean_zero]; rfl
  | succ j ih =>
      change guerraStepAvg n s β U h t j (guerraUD n s β U V h t j) y = _
      rw [show guerraUD n s β U V h t j = fun x => Real.sqrt t * guerraMean n s β U h t j V x
        from funext ih, guerraStepAvg_const_mul, ← guerraMean_succ n s β U h ht]

theorem guerraStepAvg_sub {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ)
    {f g : (Fin n → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) {C D : ℝ}
    (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ D) (y : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun x => f x - g x) y =
      guerraStepAvg n s β U h t j f y - guerraStepAvg n s β U h t j g y := by
  unfold guerraStepAvg
  simp_rw [sub_mul]
  exact integral_sub
    (integrable_guerraStepAvg_integrand n s β U h ht j hf (b := 0) le_rfl (by simpa using hfb) y)
    (integrable_guerraStepAvg_integrand n s β U h ht j hg (b := 0) le_rfl (by simpa using hgb) y)

/-- The mixed Hessian is a one-replica diagonal term minus the current pair term
and the accumulated pair terms.  This is the exact replica representation, not
an estimate of the Hessian. -/
theorem guerraUUD_eq_replicas {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V W : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin n → ℝ) :
    guerraUUD n s β U V W h t j y = t *
      (guerraMean n s β U h t j (fun σ => V σ * W σ) y -
        guerraMass s j * guerraMean n s β U h t j V y * guerraMean n s β U h t j W y -
        guerraReplicaAccum n s β U h t (fun _ σ τ => V σ * W τ) j y) := by
  induction j generalizing y with
  | zero =>
      simp only [guerraUUD, guerraBaseUUDeriv, guerraMean_zero, guerraMass,
        guerraReplicaAccum, one_mul, sub_zero, Real.sq_sqrt ht.1.le]
  | succ j ih =>
      let K : ℕ → Config n → Config n → ℝ := fun _ σ τ => V σ * W τ
      let f := guerraMean n s β U h t j (fun σ => V σ * W σ)
      let g := fun x => guerraReplicaAccum n s β U h t K j x +
        (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) x
      have hf : Measurable f := (measurable_guerraMean_joint s β h t j _).comp
        (measurable_const.prodMk measurable_id)
      have hg : Measurable g :=
        ((measurable_guerraReplicaAccum_joint s β h t K j).comp
          (measurable_const.prodMk measurable_id)).add
        (((measurable_guerraReplicaAvg_joint s β h t j (K j)).comp
          (measurable_const.prodMk measurable_id)).const_mul _)
      have hK : ∀ l σ τ, |K l σ τ| ≤ uAbs n V * uAbs n W := by
        intro l σ τ
        exact (abs_mul (V σ) (W τ)).le.trans (mul_le_mul (abs_le_uAbs n V σ)
          (abs_le_uAbs n W τ) (abs_nonneg _) (uAbs_nonneg n V))
      have hgb : ∀ x, |g x| ≤ (uAbs n V * uAbs n W) * (1 - guerraMass s j) +
          (guerraMass s j - guerraMass s (j + 1)) * (uAbs n V * uAbs n W) := by
        intro x
        refine (abs_add_le _ _).trans (add_le_add
          (guerraReplicaAccum_abs_le n s β U h ht
            (mul_nonneg (uAbs_nonneg n V) (uAbs_nonneg n W)) hK j x) ?_)
        rw [abs_mul, abs_of_nonneg (guerraMass_drop_nonneg s j)]
        exact mul_le_mul_of_nonneg_left (guerraReplicaAvg_abs_le n s β U h ht j (hK j) x)
          (guerraMass_drop_nonneg s j)
      have he : (fun x => guerraUUD n s β U V W h t j x +
          s.m (k + 1 - j) * guerraUD n s β U V h t j x * guerraUD n s β U W h t j x) =
          fun x => t * (f x - g x) := by
        funext x
        rw [ih, guerraUD_eq_mean n s β U V h ht, guerraUD_eq_mean n s β U W h ht]
        dsimp only [f, g, K]
        rw [guerraReplicaAvg_mul]
        change t * (_ - _ - _) + guerraMass s (j + 1) * (Real.sqrt t * _) *
          (Real.sqrt t * _) = _
        ring_nf
        rw [Real.sq_sqrt ht.1.le]
        ring
      change guerraStepAvg n s β U h t j
        (fun x => guerraUUD n s β U V W h t j x +
          s.m (k + 1 - j) * guerraUD n s β U V h t j x * guerraUD n s β U W h t j x) y -
        s.m (k + 1 - j) * guerraUD n s β U V h t (j + 1) y *
          guerraUD n s β U W h t (j + 1) y = _
      rw [he, guerraStepAvg_const_mul, guerraStepAvg_sub n s β U h ht j hf hg
        (guerraMean_abs_le n s β U h ht j _) hgb]
      change t * (guerraStepAvg n s β U h t j f y -
        guerraReplicaAccum n s β U h t K (j + 1) y) - _ = _
      dsimp only [f, K]
      rw [← guerraMean_succ n s β U h ht,
        guerraUD_eq_mean n s β U V h ht, guerraUD_eq_mean n s β U W h ht]
      change t * (_ - _) - guerraMass s (j + 1) * (Real.sqrt t * _) * (Real.sqrt t * _) = _
      ring_nf
      rw [Real.sq_sqrt ht.1.le]
      ring

theorem guerraReplicaAvg_const_mul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (c : ℝ) (K : Config n → Config n → ℝ) (y : Fin n → ℝ) :
    guerraReplicaAvg n s β U h t j (fun σ τ => c * K σ τ) y =
      c * guerraReplicaAvg n s β U h t j K y := by
  unfold guerraReplicaAvg
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => by ring))

theorem guerraReplicaAvg_sum_mul {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h t : ℝ) (j : ℕ) (c : ι → ℝ)
    (K : ι → Config n → Config n → ℝ) (y : Fin n → ℝ) :
    guerraReplicaAvg n s β U h t j (fun σ τ => ∑ i, c i * K i σ τ) y =
      ∑ i, c i * guerraReplicaAvg n s β U h t j (K i) y := by
  let p := fun σ => guerraProb n s β U h t j σ y
  change (∑ σ, ∑ τ, p σ * p τ * ∑ i, c i * K i σ τ) = _
  simp only [Finset.mul_sum]
  calc
    _ = ∑ σ, ∑ i, ∑ τ, p σ * p τ * (c i * K i σ τ) :=
      Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)
    _ = ∑ i, ∑ σ, ∑ τ, p σ * p τ * (c i * K i σ τ) := Finset.sum_comm
    _ = _ := by
      simp only [guerraReplicaAvg, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun σ _ =>
        Finset.sum_congr rfl (fun τ _ => by dsimp [p]; ring)))

/-- Contracting two first derivatives is precisely a two-replica kernel average. -/
theorem guerraUD_square_sum {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (c : ι → ℝ) (V : ι → EnergySpace n) (y : Fin n → ℝ) :
    (∑ i, c i * (guerraUD n s β U (V i) h t j y) ^ 2) =
      t * guerraReplicaAvg n s β U h t j (fun σ τ => ∑ i, c i * (V i σ * V i τ)) y := by
  rw [guerraReplicaAvg_sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [guerraUD_eq_mean n s β U (V i) h ht, guerraReplicaAvg_mul, mul_pow, Real.sq_sqrt ht.1.le]
  ring

theorem sk_covariance_spectral_sum {N : ℕ} (β h : ℝ) (sk : SKDisorder (Ω := Ω) N β h)
    (σ τ : Config N) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * (sk.hU.w i σ * sk.hU.w i τ)) = sk_cov_kernel N β σ τ := by
  have hc := sk.cov_eq σ τ
  rw [PhysLean.Probability.GaussianIBP.covOp_apply] at hc
  simp only [sum_inner, real_inner_smul_left, inner_std_basis_apply] at hc
  have hi : ∀ i : sk.hU.ι, inner ℝ (sk.hU.w i) (std_basis N τ) = sk.hU.w i τ := by
    intro i
    rw [real_inner_comm, inner_std_basis_apply]
  simp only [hi] at hc
  simpa only [mul_assoc] using hc

/-- The disorder-gradient contraction uses the square of the overlap. -/
theorem guerra_disorder_gradient_overlap {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) (U : EnergySpace N)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * (guerraUD N s β U (sk.hU.w i) h t j y) ^ 2) =
      (t * (N * β ^ 2 / 2)) * guerraReplicaAvg N s β U h t j (fun σ τ => (overlap N σ τ) ^ 2) y := by
  rw [guerraUD_square_sum N s β U h ht]
  simp_rw [sk_covariance_spectral_sum β h sk, sk_cov_kernel]
  rw [guerraReplicaAvg_const_mul]
  ring

/-- The field-gradient contraction uses the overlap itself. -/
theorem guerra_field_gradient_overlap {N : ℕ} (hN : 0 < N) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace N) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin N → ℝ) :
    (∑ i : Fin N, (guerraYD N s β U (Pi.single i 1) h t j y) ^ 2) =
      ((1 - t) * N) * guerraReplicaAvg N s β U h t j (overlap N) y := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hK : (fun σ τ : Config N => ∑ i : Fin N,
      guerraFieldDirection N t (Pi.single i 1) σ * guerraFieldDirection N t (Pi.single i 1) τ) =
      fun σ τ => ((1 - t) / t * N) * overlap N σ τ := by
    funext σ τ
    simp_rw [guerraFieldDirection_single]
    calc
      _ = (Real.sqrt (1 - t) / Real.sqrt t) ^ 2 * ∑ i, spin N σ i * spin N τ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
        rw [div_pow, Real.sq_sqrt (sub_pos.mpr ht.2).le, Real.sq_sqrt ht.1.le, overlap]
        field_simp
  have hg := guerraUD_square_sum N s β U h ht j (fun _ : Fin N => (1 : ℝ))
    (fun i => guerraFieldDirection N t (Pi.single i 1)) y
  simp only [one_mul] at hg
  change (∑ i : Fin N, (guerraUD N s β U (guerraFieldDirection N t (Pi.single i 1)) h t j y) ^ 2) = _
  rw [hg, hK, guerraReplicaAvg_const_mul]
  field_simp [ht.1.ne']

/-- Discrete integration by parts for the masses and overlap parameters. -/
theorem guerra_mass_q_telescope {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    (∑ l ∈ Finset.range j, (guerraMass s l - guerraMass s (l + 1)) * s.q (k + 2 - l) ^ 2) +
      (∑ l ∈ Finset.range j, s.m (k + 1 - l) *
        (s.q (k + 2 - l) ^ 2 - s.q (k + 1 - l) ^ 2)) =
      1 - guerraMass s j * s.q (k + 2 - j) ^ 2 := by
  induction j with
  | zero => simp [guerraMass, s.q_top]
  | succ j ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hq : k + 2 - (j + 1) = k + 1 - j := by omega
      rw [hq]
      change _ = 1 - s.m (k + 1 - j) * _
      change _ + _ = _ at ih
      change (∑ l ∈ Finset.range j, _) +
        (guerraMass s j - s.m (k + 1 - j)) * s.q (k + 2 - j) ^ 2 +
        ((∑ l ∈ Finset.range j, _) + s.m (k + 1 - j) *
          (s.q (k + 2 - j) ^ 2 - s.q (k + 1 - j) ^ 2)) = _
      nlinarith only [ih]

/-- The reversed cascade indexing gives exactly the correction in the paper. -/
theorem parisiCorrection_eq_mass_q {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiCorrection s β = (β ^ 2 / 4) *
      (1 - ∑ j ∈ Finset.range (k + 2),
        (guerraMass s j - guerraMass s (j + 1)) * s.q (k + 2 - j) ^ 2) := by
  have hr : (∑ j ∈ Finset.range (k + 2), s.m (k + 1 - j) *
      (s.q (k + 2 - j) ^ 2 - s.q (k + 1 - j) ^ 2)) =
      ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, s.m_zero, zero_mul, add_zero]
    rw [← Finset.sum_range_reflect
      (fun p => s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) (k + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have h1 : k + 1 - 1 - j + 1 = k + 1 - j := by omega
    have h2 : k + 1 - 1 - j + 2 = k + 2 - j := by omega
    rw [h1, h2]
  have hh := guerra_mass_q_telescope s (k + 2)
  rw [guerraMass_top, zero_mul, sub_zero, hr] at hh
  unfold parisiCorrection
  congr 1
  linarith

theorem guerraReplicaAccum_const_mul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (c : ℝ) (K : ℕ → Config n → Config n → ℝ)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun l σ τ => c * K l σ τ) j y =
      c * guerraReplicaAccum n s β U h t K j y := by
  induction j generalizing y with
  | zero => simp [guerraReplicaAccum]
  | succ j ih =>
      simp only [guerraReplicaAccum, ih, guerraReplicaAvg_const_mul]
      rw [show (fun x => c * guerraReplicaAccum n s β U h t K j x +
          (guerraMass s j - guerraMass s (j + 1)) * (c * guerraReplicaAvg n s β U h t j (K j) x)) =
          (fun x => c * (guerraReplicaAccum n s β U h t K j x +
            (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K j) x)) by
        funext x; ring, guerraStepAvg_const_mul]

theorem guerraReplicaAccum_sum_mul {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (c : ι → ℝ) (K : ι → ℕ → Config n → Config n → ℝ) (C : ι → ℝ)
    (hK : ∀ i l σ τ, |K i l σ τ| ≤ C i) (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun l σ τ => ∑ i, c i * K i l σ τ) j y =
      ∑ i, c i * guerraReplicaAccum n s β U h t (K i) j y := by
  have hC : ∀ i, 0 ≤ C i := fun i => (abs_nonneg (K i 0 default default)).trans (hK i 0 _ _)
  induction j generalizing y with
  | zero => simp [guerraReplicaAccum]
  | succ j ih =>
      let f := fun i x => guerraReplicaAccum n s β U h t (K i) j x +
        (guerraMass s j - guerraMass s (j + 1)) * guerraReplicaAvg n s β U h t j (K i j) x
      let B := fun i => C i * (1 - guerraMass s j) + (guerraMass s j - guerraMass s (j + 1)) * C i
      have hfm : ∀ i, Measurable (f i) := fun i =>
        ((measurable_guerraReplicaAccum_joint s β h t (K i) j).comp
          (measurable_const.prodMk measurable_id)).add
        (((measurable_guerraReplicaAvg_joint s β h t j (K i j)).comp
          (measurable_const.prodMk measurable_id)).const_mul _)
      have hfb : ∀ i x, |f i x| ≤ B i := by
        intro i x
        refine (abs_add_le _ _).trans (add_le_add
          (guerraReplicaAccum_abs_le n s β U h ht (hC i) (hK i) j x) ?_)
        rw [abs_mul, abs_of_nonneg (guerraMass_drop_nonneg s j)]
        exact mul_le_mul_of_nonneg_left (guerraReplicaAvg_abs_le n s β U h ht j (hK i j) x)
          (guerraMass_drop_nonneg s j)
      have he : (fun x =>
          guerraReplicaAccum n s β U h t (fun l σ τ => ∑ i, c i * K i l σ τ) j x +
            (guerraMass s j - guerraMass s (j + 1)) *
              guerraReplicaAvg n s β U h t j (fun σ τ => ∑ i, c i * K i j σ τ) x) =
          fun x => ∑ i, c i * f i x := by
        funext x
        rw [ih, guerraReplicaAvg_sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by dsimp [f]; ring)
      change guerraStepAvg n s β U h t j _ y = _
      rw [he, guerraStepAvg_sum n s β U h ht j (fun i x => c i * f i x)
        (fun i => (hfm i).const_mul _) (fun i => |c i| * B i)
        (fun i x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfb i x) (abs_nonneg _))]
      simp only [guerraStepAvg_const_mul]
      rfl

theorem guerraMean_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (c : ℝ) (y : Fin n → ℝ) : guerraMean n s β U h t j (fun _ => c) y = c := by
  rw [guerraMean, ← Finset.sum_mul, (guerraProb_nonneg_sum_one n s β U h ht j).2, one_mul]

theorem guerraMean_const_mul {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (c : ℝ) (f : Config n → ℝ) (y : Fin n → ℝ) :
    guerraMean n s β U h t j (fun σ => c * f σ) y = c * guerraMean n s β U h t j f y := by
  unfold guerraMean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

theorem guerraMean_sum_mul {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h t : ℝ) (j : ℕ) (c : ι → ℝ)
    (f : ι → Config n → ℝ) (y : Fin n → ℝ) :
    guerraMean n s β U h t j (fun σ => ∑ i, c i * f i σ) y =
      ∑ i, c i * guerraMean n s β U h t j (f i) y := by
  unfold guerraMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun σ _ => by ring))

/-- The complete Hessian trace for any finite family of directions, expressed
using its covariance kernel. -/
theorem guerraUUD_trace_replicas {ι : Type*} [Fintype ι] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (c : ι → ℝ) (V : ι → EnergySpace n) (y : Fin n → ℝ) :
    (∑ i, c i * guerraUUD n s β U (V i) (V i) h t j y) = t *
      (guerraMean n s β U h t j (fun σ => ∑ i, c i * (V i σ * V i σ)) y -
        guerraMass s j * guerraReplicaAvg n s β U h t j (fun σ τ => ∑ i, c i * (V i σ * V i τ)) y -
        guerraReplicaAccum n s β U h t (fun _ σ τ => ∑ i, c i * (V i σ * V i τ)) j y) := by
  have hK : ∀ i (l : ℕ) σ τ, |V i σ * V i τ| ≤ uAbs n (V i) * uAbs n (V i) := by
    intro i l σ τ
    rw [abs_mul]
    exact mul_le_mul (abs_le_uAbs n (V i) σ) (abs_le_uAbs n (V i) τ)
      (abs_nonneg _) (uAbs_nonneg n (V i))
  rw [guerraMean_sum_mul, guerraReplicaAvg_sum_mul,
    guerraReplicaAccum_sum_mul n s β U h ht c (fun i _ σ τ => V i σ * V i τ)
      (fun i => uAbs n (V i) * uAbs n (V i)) hK,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [guerraUUD_eq_replicas n s β U (V i) (V i) h ht, guerraReplicaAvg_mul]
  ring

/-- The disorder Hessian trace in the precise form needed by Gaussian IBP. -/
theorem guerra_disorder_hessian_overlap {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) (U : EnergySpace N)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * guerraUUD N s β U (sk.hU.w i) (sk.hU.w i) h t j y) =
      (t * (N * β ^ 2 / 2)) * (1 -
        guerraMass s j * guerraReplicaAvg N s β U h t j (fun σ τ => (overlap N σ τ) ^ 2) y -
        guerraReplicaAccum N s β U h t (fun _ σ τ => (overlap N σ τ) ^ 2) j y) := by
  have hd : ∀ σ : Config N, overlap N σ σ = 1 := by
    intro σ
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hs : ∀ i, spin N σ i * spin N σ i = 1 := by
      intro i
      have hh := abs_spin N σ i
      nlinarith [sq_abs (spin N σ i)]
    simp [overlap, hs, hNR]
  rw [guerraUUD_trace_replicas N s β U h ht]
  simp_rw [sk_covariance_spectral_sum β h sk, sk_cov_kernel, hd, one_pow, mul_one]
  rw [guerraMean_const N s β U h ht, guerraReplicaAvg_const_mul, guerraReplicaAccum_const_mul]
  ring

theorem guerra_field_hessian_overlap {N : ℕ} (hN : 0 < N) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace N) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin N → ℝ) :
    (∑ i : Fin N, guerraYYD N s β U (Pi.single i 1) (Pi.single i 1) h t j y) =
      ((1 - t) * N) * (1 - guerraMass s j * guerraReplicaAvg N s β U h t j (overlap N) y -
        guerraReplicaAccum N s β U h t (fun _ => overlap N) j y) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd : ∀ σ : Config N, overlap N σ σ = 1 := by
    intro σ
    have hs : ∀ i, spin N σ i * spin N σ i = 1 := by
      intro i
      have hh := abs_spin N σ i
      nlinarith [sq_abs (spin N σ i)]
    simp [overlap, hs, hNR]
  have hK : ∀ σ τ : Config N, (∑ i : Fin N,
      guerraFieldDirection N t (Pi.single i 1) σ * guerraFieldDirection N t (Pi.single i 1) τ) =
      ((1 - t) / t * N) * overlap N σ τ := by
    intro σ τ
    simp_rw [guerraFieldDirection_single]
    calc
      _ = (Real.sqrt (1 - t) / Real.sqrt t) ^ 2 * ∑ i, spin N σ i * spin N τ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
        rw [div_pow, Real.sq_sqrt (sub_pos.mpr ht.2).le, Real.sq_sqrt ht.1.le, overlap]
        field_simp
  have hh := guerraUUD_trace_replicas N s β U h ht j (fun _ : Fin N => (1 : ℝ))
    (fun i => guerraFieldDirection N t (Pi.single i 1)) y
  simp only [one_mul] at hh
  simp_rw [hK, hd, mul_one] at hh
  change (∑ i : Fin N, guerraUUD N s β U (guerraFieldDirection N t (Pi.single i 1))
    (guerraFieldDirection N t (Pi.single i 1)) h t j y) = _
  rw [hh, guerraMean_const N s β U h ht, guerraReplicaAvg_const_mul, guerraReplicaAccum_const_mul]
  field_simp [ht.1.ne']

/-- One field-IBP step, now expressed entirely in terms of the overlap. -/
theorem guerra_field_radial_overlap_step {N : ℕ} (hN : 0 < N) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace N) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin N → ℝ) :
    guerraStepAvg N s β U h t j (fun x => guerraYD N s β U x h t j x) y =
      guerraYD N s β U y h t (j + 1) y +
        (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) * ((1 - t) * N) *
          (1 - guerraReplicaAccum N s β U h t (fun _ => overlap N) (j + 1) y) := by
  have hs := guerra_field_radial_step N s β U h ht j y
  dsimp only at hs
  change guerraStepAvg N s β U h t j (fun x => guerraYD N s β U x h t j x) y = _ at hs
  have hi : ∀ i : Fin N,
      guerraStepAvg N s β U h t j (fun x =>
        guerraYYD N s β U (Pi.single i 1) (Pi.single i 1) h t j x +
          s.m (k + 1 - j) * (guerraYD N s β U (Pi.single i 1) h t j x) ^ 2) y =
        guerraYYD N s β U (Pi.single i 1) (Pi.single i 1) h t (j + 1) y +
          s.m (k + 1 - j) * (guerraYD N s β U (Pi.single i 1) h t (j + 1) y) ^ 2 := by
    intro i
    simp only [guerraYYD, guerraYD, guerraUUD, guerraStepAvg, pow_two, mul_assoc]
    ring
  change guerraStepAvg N s β U h t j (fun x => guerraYD N s β U x h t j x) y =
    guerraYD N s β U y h t (j + 1) y +
      (1 * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) *
        ∑ i : Fin N, guerraStepAvg N s β U h t j (fun x =>
          guerraYYD N s β U (Pi.single i 1) (Pi.single i 1) h t j x +
            s.m (k + 1 - j) * (guerraYD N s β U (Pi.single i 1) h t j x) ^ 2) y at hs
  rw [hs]
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    guerra_field_hessian_overlap hN s β h U ht,
    guerra_field_gradient_overlap hN s β h U ht]
  change _ = _
  change _ + _ * (((1 - t) * N) * (1 - s.m (k + 1 - j) * _ - _) + _ * _) = _
  ring

/-- Measurability and affine field growth, bundled for linear integral operations. -/
structure GuerraGrowth {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop where
  measurable : Measurable f
  bound : ∃ a b : ℝ, 0 ≤ b ∧ ∀ y, |f y| ≤ a + b * l1 y

theorem GuerraGrowth.of_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) : GuerraGrowth f :=
  ⟨hf, C, 0, le_rfl, by simpa using hb⟩

theorem GuerraGrowth.const {n : ℕ} (c : ℝ) : GuerraGrowth (fun _ : Fin n → ℝ => c) :=
  GuerraGrowth.of_bound measurable_const (fun _ => le_rfl)

theorem GuerraGrowth.const_mul {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : GuerraGrowth f) (c : ℝ) : GuerraGrowth (fun y => c * f y) := by
  obtain ⟨a, b, hb, hbound⟩ := hf.bound
  refine ⟨hf.measurable.const_mul c, |c| * a, |c| * b, mul_nonneg (abs_nonneg _) hb, fun y => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ |c| * (a + b * l1 y) := mul_le_mul_of_nonneg_left (hbound y) (abs_nonneg _)
    _ = _ := by ring

theorem GuerraGrowth.sub {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : GuerraGrowth f) (hg : GuerraGrowth g) : GuerraGrowth (fun y => f y - g y) := by
  obtain ⟨a, b, hb, hfb⟩ := hf.bound
  obtain ⟨c, d, hd, hgb⟩ := hg.bound
  refine ⟨hf.measurable.sub hg.measurable, a + c, b + d, add_nonneg hb hd, fun y => ?_⟩
  calc
    _ ≤ |f y| + |g y| := abs_sub _ _
    _ ≤ (a + b * l1 y) + (c + d * l1 y) := add_le_add (hfb y) (hgb y)
    _ = _ := by ring

theorem GuerraGrowth.add {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : GuerraGrowth f) (hg : GuerraGrowth g) : GuerraGrowth (fun y => f y + g y) := by
  have hh := hf.sub (hg.const_mul (-1))
  simpa only [neg_one_mul, sub_neg_eq_add] using hh

theorem guerraStepAvg_sub_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ)
    {f g : (Fin n → ℝ) → ℝ} (hf : GuerraGrowth f) (hg : GuerraGrowth g) (y : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun x => f x - g x) y =
      guerraStepAvg n s β U h t j f y - guerraStepAvg n s β U h t j g y := by
  obtain ⟨a, b, hb, hfb⟩ := hf.bound
  obtain ⟨c, d, hd, hgb⟩ := hg.bound
  unfold guerraStepAvg
  simp_rw [sub_mul]
  exact integral_sub (integrable_guerraStepAvg_integrand n s β U h ht j hf.measurable hb hfb y)
    (integrable_guerraStepAvg_integrand n s β U h ht j hg.measurable hd hgb y)

theorem guerraStepAvg_add_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ)
    {f g : (Fin n → ℝ) → ℝ} (hf : GuerraGrowth f) (hg : GuerraGrowth g) (y : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun x => f x + g x) y =
      guerraStepAvg n s β U h t j f y + guerraStepAvg n s β U h t j g y := by
  have hh := guerraStepAvg_sub_growth n s β U h ht j hf (hg.const_mul (-1)) y
  rw [guerraStepAvg_const_mul] at hh
  simpa only [neg_one_mul, sub_neg_eq_add] using hh

theorem guerraReplicaAvg_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : Config n → Config n → ℝ} {C : ℝ} (hK : ∀ σ τ, |K σ τ| ≤ C) (j : ℕ) :
    GuerraGrowth (guerraReplicaAvg n s β U h t j K) := by
  apply GuerraGrowth.of_bound (C := C)
  · exact (measurable_guerraReplicaAvg_joint (n := n) s β h t j K).comp
      (f := fun y : Fin n → ℝ => (U, y)) (measurable_const.prodMk measurable_id)
  · exact guerraReplicaAvg_abs_le n s β U h ht j hK

theorem guerraReplicaAccum_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} {C : ℝ} (hK : ∀ l σ τ, |K l σ τ| ≤ C) (j : ℕ) :
    GuerraGrowth (guerraReplicaAccum n s β U h t K j) := by
  have hC : 0 ≤ C := (abs_nonneg (K 0 default default)).trans (hK 0 _ _)
  apply GuerraGrowth.of_bound ((measurable_guerraReplicaAccum_joint s β h t K j).comp
    (measurable_const.prodMk measurable_id))
  intro y
  exact (guerraReplicaAccum_abs_le n s β U h ht hC hK j y).trans
    (mul_le_of_le_one_right hC (by linarith [(guerraMass_mem_Icc s j).1]))

theorem guerraUD_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U V : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    GuerraGrowth (guerraUD n s β U V h t j) := by
  obtain ⟨hm, hb⟩ := guerraUD_measurable_and_bound n s β U V h ht j
  exact GuerraGrowth.of_bound hm hb

theorem guerraYD_radial_growth {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    GuerraGrowth (fun y => guerraYD n s β U y h t j y) := by
  let B := fun i : Fin n => Real.sqrt t * uAbs n (guerraFieldDirection n t (Pi.single i 1))
  have hB : ∀ i, 0 ≤ B i := fun i => mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg _ _)
  have hb : ∀ i y, |guerraYD n s β U (Pi.single i 1) h t j y| ≤ B i := fun i =>
    (guerraUD_measurable_and_bound n s β U (guerraFieldDirection n t (Pi.single i 1)) h ht j).2
  have he : (fun y => guerraYD n s β U y h t j y) =
      fun y => ∑ i, y i * guerraYD n s β U (Pi.single i 1) h t j y :=
    funext (fun y => guerraYD_eq_sum n s β U h ht y y j)
  rw [he]
  refine ⟨Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).mul
    (measurable_guerraYD n s β U h ht (Pi.single i 1) j)), 0, ∑ i, B i,
    Finset.sum_nonneg (fun i _ => hB i), fun y => ?_⟩
  simp only [zero_add]
  calc
    _ ≤ ∑ i, |y i * guerraYD n s β U (Pi.single i 1) h t j y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |y i| * (∑ l, B l) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hb i y).trans
        (Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ i))) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem guerraReplicaAccum_succ_split {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} {C : ℝ} (hK : ∀ l σ τ, |K l σ τ| ≤ C)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t K (j + 1) y =
      guerraStepAvg n s β U h t j (guerraReplicaAccum n s β U h t K j) y +
        (guerraMass s j - guerraMass s (j + 1)) *
          guerraStepAvg n s β U h t j (guerraReplicaAvg n s β U h t j (K j)) y := by
  rw [guerraReplicaAccum, guerraStepAvg_add_growth n s β U h ht j
    (guerraReplicaAccum_growth n s β U h ht hK j)
    ((guerraReplicaAvg_growth n s β U h ht (hK j) j).const_mul _), guerraStepAvg_const_mul]

theorem abs_q_mul_overlap_le_one {N k : ℕ} (hN : 0 < N) (s : RSBScheme k)
    (j : ℕ) (σ τ : Config N) : |s.q (k + 2 - j) * overlap N σ τ| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (s.q_nonneg (by omega))]
  simpa only [one_mul] using mul_le_mul (s.q_le_one (by omega)) (abs_overlap_le_one hN σ τ)
    (abs_nonneg _) zero_le_one

/-- The field correction after `j` integrations, divided by `N β² / 2`. -/
noncomputable def guerraFieldTerm {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (j : ℕ) (y : Fin n → ℝ) : ℝ :=
  1 - s.q (k + 2 - j) -
    guerraReplicaAccum n s β U h t (fun l σ τ => s.q (k + 2 - l) * overlap n σ τ) j y +
    s.q (k + 2 - j) * guerraReplicaAccum n s β U h t (fun _ => overlap n) j y

theorem guerraFieldTerm_growth {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    GuerraGrowth (guerraFieldTerm n s β U h t j) := by
  exact ((GuerraGrowth.const (1 - s.q (k + 2 - j))).sub
    (guerraReplicaAccum_growth n s β U h ht (abs_q_mul_overlap_le_one hn s) j)).add
    ((guerraReplicaAccum_growth n s β U h ht (fun _ => abs_overlap_le_one hn) j).const_mul _)

/-- The overlap representation telescopes the field corrections through a level. -/
theorem guerraFieldTerm_step {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (guerraFieldTerm n s β U h t j) y +
      (s.q (k + 2 - j) - s.q (k + 2 - (j + 1))) *
        (1 - guerraReplicaAccum n s β U h t (fun _ => overlap n) (j + 1) y) =
      guerraFieldTerm n s β U h t (j + 1) y := by
  have hR := guerraReplicaAccum_growth n s β U h ht (fun _ => abs_overlap_le_one hn) j
  have hQ := guerraReplicaAccum_growth n s β U h ht (abs_q_mul_overlap_le_one hn s) j
  unfold guerraFieldTerm
  rw [guerraStepAvg_add_growth n s β U h ht j
    ((GuerraGrowth.const (1 - s.q (k + 2 - j))).sub hQ) (hR.const_mul _),
    guerraStepAvg_sub_growth n s β U h ht j (GuerraGrowth.const _) hQ,
    guerraStepAvg_const n s β U h ⟨ht.1.le, ht.2.le⟩, guerraStepAvg_const_mul]
  rw [guerraReplicaAccum_succ_split n s β U h ht (fun _ => abs_overlap_le_one hn),
    guerraReplicaAccum_succ_split n s β U h ht (abs_q_mul_overlap_le_one hn s)]
  have he : guerraReplicaAvg n s β U h t j (fun σ τ => s.q (k + 2 - j) * overlap n σ τ) =
      fun x => s.q (k + 2 - j) * guerraReplicaAvg n s β U h t j (overlap n) x :=
    funext (fun x => guerraReplicaAvg_const_mul n s β U h t j _ _ x)
  rw [he, guerraStepAvg_const_mul]
  ring

theorem gibbsAvg_sub {n : ℕ} (E f g : Config n → ℝ) :
    gibbsAvg E (fun σ => f σ - g σ) = gibbsAvg E f - gibbsAvg E g := by
  simp only [gibbsAvg, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem guerraBaseDeriv_eq_radials {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (y : Fin n → ℝ) :
    guerraD n s β U h 0 t y = (1 / (2 * t)) * guerraUD n s β U U h t 0 y -
      (1 / (2 * (1 - t))) * guerraYD n s β U y h t 0 y := by
  have hrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
  have hr1 : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr ht.2)).ne'
  have h1t : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  have ha : 1 / (2 * Real.sqrt t) = (1 / (2 * t)) * Real.sqrt t := by
    field_simp [hrt, ht.1.ne']
    nlinarith [Real.sq_sqrt ht.1.le]
  have hb : 1 / (2 * Real.sqrt (1 - t)) = (1 / (2 * (1 - t))) * Real.sqrt (1 - t) := by
    field_simp [hr1, h1t]
    nlinarith [Real.sq_sqrt (sub_pos.mpr ht.2).le]
  have he : guerraHDeriv n U t y = fun σ =>
      ((1 / (2 * t)) * Real.sqrt t) * U σ -
        ((1 / (2 * (1 - t))) * Real.sqrt t) * guerraFieldDirection n t y σ := by
    funext σ
    have hd : Real.sqrt t * guerraFieldDirection n t y σ =
        Real.sqrt (1 - t) * ∑ i, spin n σ i * y i := by
      change Real.sqrt t * ((Real.sqrt (1 - t) / Real.sqrt t) * _) = _
      field_simp
    calc
      _ = (1 / (2 * Real.sqrt t)) * U σ -
          (1 / (2 * Real.sqrt (1 - t))) * (∑ i, spin n σ i * y i) := by
        unfold guerraHDeriv
        ring
      _ = _ := by rw [ha, hb]; simp only [mul_assoc, hd]
  change gibbsAvg (guerraH n U h t y) (guerraHDeriv n U t y) = _
  rw [he, gibbsAvg_sub, gibbsAvg_const_mul, gibbsAvg_const_mul]
  change _ = (1 / (2 * t)) * (Real.sqrt t * gibbsAvg _ _) -
    (1 / (2 * (1 - t))) * (Real.sqrt t * gibbsAvg _ _)
  ring

/-- All conditional field-IBP terms assembled through the entire cascade. -/
theorem guerraD_eq_radials_overlap {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraD n s β U h j t y =
      (1 / (2 * t)) * guerraUD n s β U U h t j y -
        (1 / (2 * (1 - t))) * guerraYD n s β U y h t j y -
        (n * β ^ 2 / 2) * guerraFieldTerm n s β U h t j y := by
  induction j generalizing y with
  | zero =>
      simpa only [guerraFieldTerm, guerraReplicaAccum, Nat.sub_zero, s.q_top,
        sub_self, sub_zero, mul_zero, add_zero] using guerraBaseDeriv_eq_radials n s β U h ht y
  | succ j ih =>
      have hU := (guerraUD_growth n s β U U h ht j).const_mul (1 / (2 * t))
      have hY := (guerraYD_radial_growth n s β U h ht j).const_mul (1 / (2 * (1 - t)))
      have hF := (guerraFieldTerm_growth hn s β h U ht j).const_mul (n * β ^ 2 / 2)
      change guerraStepAvg n s β U h t j (guerraD n s β U h j t) y = _
      rw [show guerraD n s β U h j t = fun x =>
        (1 / (2 * t)) * guerraUD n s β U U h t j x -
          (1 / (2 * (1 - t))) * guerraYD n s β U x h t j x -
          (n * β ^ 2 / 2) * guerraFieldTerm n s β U h t j x from funext ih,
        guerraStepAvg_sub_growth n s β U h ht j (hU.sub hY) hF,
        guerraStepAvg_sub_growth n s β U h ht j hU hY]
      simp only [guerraStepAvg_const_mul]
      rw [guerra_field_radial_overlap_step hn s β h U ht]
      have hh := guerraFieldTerm_step hn s β h U ht j y
      rw [eq_sub_iff_add_eq.mpr hh]
      have hq : k + 2 - (j + 1) = k + 1 - j := by omega
      rw [hq]
      change (1 / (2 * t)) * guerraUD n s β U U h t (j + 1) y - _ - _ = _
      field_simp [(sub_pos.mpr ht.2).ne', ht.1.ne']
      ring

theorem abs_overlap_sq_le_one {n : ℕ} (hn : 0 < n) (σ τ : Config n) :
    |(overlap n σ τ) ^ 2| ≤ 1 := by
  rw [pow_two, abs_mul]
  simpa only [one_mul] using mul_le_mul (abs_overlap_le_one hn σ τ) (abs_overlap_le_one hn σ τ)
    (abs_nonneg _) zero_le_one

theorem guerraReplicaAvg_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (c : ℝ) (y : Fin n → ℝ) :
    guerraReplicaAvg n s β U h t j (fun _ _ => c) y = c := by
  have hs := (guerraProb_nonneg_sum_one n s β U h ht j).2
  simp only [guerraReplicaAvg, ← Finset.sum_mul, ← Finset.mul_sum, hs, one_mul, mul_one]

theorem guerraReplicaAccum_const_level {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (c : ℕ → ℝ) (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun l _ _ => c l) j y =
      ∑ l ∈ Finset.range j, (guerraMass s l - guerraMass s (l + 1)) * c l := by
  induction j generalizing y with
  | zero => simp [guerraReplicaAccum]
  | succ j ih =>
      rw [guerraReplicaAccum]
      simp_rw [ih, guerraReplicaAvg_const n s β U h ht]
      rw [guerraStepAvg_const n s β U h ⟨ht.1.le, ht.2.le⟩, Finset.sum_range_succ]

/-- Completing the square inside the accumulated replica averages. -/
theorem guerraReplicaAccum_overlap_sq {n : ℕ} (hn : 0 < n) {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (U : EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (y : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t (fun l σ τ => (overlap n σ τ - s.q (k + 2 - l)) ^ 2) j y =
      guerraReplicaAccum n s β U h t (fun _ σ τ => (overlap n σ τ) ^ 2) j y -
        2 * guerraReplicaAccum n s β U h t (fun l σ τ => s.q (k + 2 - l) * overlap n σ τ) j y +
        ∑ l ∈ Finset.range j, (guerraMass s l - guerraMass s (l + 1)) * s.q (k + 2 - l) ^ 2 := by
  let c : Fin 3 → ℝ := ![1, -2, 1]
  let K : Fin 3 → ℕ → Config n → Config n → ℝ :=
    ![fun _ σ τ => (overlap n σ τ) ^ 2,
      fun l σ τ => s.q (k + 2 - l) * overlap n σ τ,
      fun l _ _ => s.q (k + 2 - l) ^ 2]
  have hK : ∀ i l σ τ, |K i l σ τ| ≤ 1 := by
    intro i l σ τ
    fin_cases i
    · exact abs_overlap_sq_le_one hn σ τ
    · exact abs_q_mul_overlap_le_one hn s l σ τ
    · change |s.q (k + 2 - l) ^ 2| ≤ 1
      rw [pow_two, abs_mul, abs_of_nonneg (s.q_nonneg (by omega))]
      simpa only [one_mul] using mul_le_mul (s.q_le_one (p := k + 2 - l) (by omega))
        (s.q_le_one (p := k + 2 - l) (by omega)) (s.q_nonneg (by omega)) zero_le_one
  have he : (fun l σ τ => ∑ i, c i * K i l σ τ) =
      fun l σ τ => (overlap n σ τ - s.q (k + 2 - l)) ^ 2 := by
    funext l σ τ
    simp [c, K, Fin.sum_univ_succ]
    ring
  have hh := guerraReplicaAccum_sum_mul n s β U h ht c K (fun _ => 1) hK j y
  rw [he] at hh
  simpa [c, K, Fin.sum_univ_succ, guerraReplicaAccum_const_level n s β U h ht, sub_eq_add_neg, add_assoc]
    using hh

theorem integrable_guerraReplicaAccum {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {K : ℕ → Config N → Config N → ℝ}
    {C : ℝ} (hK : ∀ l σ τ, |K l σ τ| ≤ C) (j : ℕ) (y : Fin N → ℝ) :
    Integrable (fun ω => guerraReplicaAccum N s β (sk.U ω) h t K j y) (ℙ : Measure Ω) := by
  have hC : 0 ≤ C := (abs_nonneg (K 0 default default)).trans (hK 0 _ _)
  apply integrable_comp_of_affine_norm_bound sk.hU
    ((measurable_guerraReplicaAccum_joint s β h t K j).comp
      (f := fun U : EnergySpace N => (U, y)) (measurable_id.prodMk measurable_const))
    (C := C * (1 - guerraMass s j)) (D := 0)
    (mul_nonneg hC (sub_nonneg.mpr (guerraMass_mem_Icc s j).2)) le_rfl
  intro U
  simpa only [Function.comp_apply, zero_mul, add_zero] using guerraReplicaAccum_abs_le N s β U h ht hC hK j y

theorem integrable_guerraUD_radial {N : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    Integrable (fun ω => guerraUD N s β (sk.U ω) (sk.U ω) h t j y) (ℙ : Measure Ω) := by
  have hm : Measurable (fun U : EnergySpace N => guerraUD N s β U U h t j y) := by
    have he : (fun U : EnergySpace N => guerraUD N s β U U h t j y) =
        fun U => Real.sqrt t * ∑ σ : Config N, guerraProb N s β U h t j σ y * U σ := by
      funext U
      exact guerraUD_eq_mean N s β U U h ht j y
    rw [he]
    exact (Finset.measurable_sum _ (fun σ _ =>
      ((measurable_guerraProb_joint s β h t j σ).comp
        (f := fun U : EnergySpace N => (U, y)) (measurable_id.prodMk measurable_const)).mul
      (measurable_coord N σ))).const_mul _
  apply integrable_comp_of_affine_norm_bound sk.hU hm (C := 0)
    (D := Real.sqrt t * Fintype.card (Config N)) le_rfl (by positivity)
  intro U
  calc
    _ ≤ Real.sqrt t * uAbs N U := (guerraUD_measurable_and_bound N s β U U h ht j).2 y
    _ ≤ Real.sqrt t * (Fintype.card (Config N) * ‖U‖) :=
      mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N U) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem guerra_disorder_expectation_overlap {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω, guerraUD N s β (sk.U ω) (sk.U ω) h t (k + 2) 0 ∂ℙ) =
      (t * (N * β ^ 2 / 2)) * (1 - ∫ ω,
        guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => (overlap N σ τ) ^ 2) (k + 2) 0 ∂ℙ) := by
  have hA := integrable_guerraReplicaAccum β h sk s ht (fun _ => abs_overlap_sq_le_one hN) (k + 2) 0
  have hI : ∀ i : sk.hU.ι, Integrable (fun ω => (sk.hU.τ i : ℝ) *
      guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0) ℙ := by
    intro i
    apply Integrable.const_mul
    apply integrable_comp_of_affine_norm_bound sk.hU
      ((measurable_guerraUUD_joint s β (sk.hU.w i) (sk.hU.w i) h t (k + 2)).comp
        (f := fun U : EnergySpace N => (U, (0 : Fin N → ℝ))) (measurable_id.prodMk measurable_const))
      (C := guerraUUBound N (sk.hU.w i) (sk.hU.w i) t (k + 2)) (D := 0)
      (guerraUUBound_nonneg _ _ _ _ _) le_rfl
    intro U
    simpa only [Function.comp_apply, zero_mul, add_zero] using
      abs_guerraUUD_le N s β U (sk.hU.w i) (sk.hU.w i) h ht (k + 2) 0
  calc
    _ = ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        ∫ ω, guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0 ∂ℙ :=
      guerra_disorder_stein β h sk s ht (k + 2) 0
    _ = ∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        guerraUUD N s β (sk.U ω) (sk.hU.w i) (sk.hU.w i) h t (k + 2) 0 ∂ℙ := by
      rw [integral_finsetSum _ (fun i _ => hI i)]
      simp only [integral_const_mul]
    _ = ∫ ω, (t * (N * β ^ 2 / 2)) * (1 -
        guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => (overlap N σ τ) ^ 2) (k + 2) 0) ∂ℙ := by
      apply integral_congr_ae
      filter_upwards with ω
      simpa only [guerraMass_top, zero_mul, sub_zero] using
        guerra_disorder_hessian_overlap hN β h sk s (sk.U ω) ht (k + 2) 0
    _ = _ := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hA]
      simp only [integral_const, probReal_univ, one_smul]

theorem guerraD_top_expectation {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω, guerraD N s β (sk.U ω) h (k + 2) t 0 ∂ℙ) =
      (N * β ^ 2 / 4) * (-1 -
        (∫ ω, guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => (overlap N σ τ) ^ 2) (k + 2) 0 ∂ℙ) +
        2 * ∫ ω, guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0 ∂ℙ) := by
  have hU := integrable_guerraUD_radial β h sk s ht (k + 2) 0
  have hQ := integrable_guerraReplicaAccum β h sk s ht (abs_q_mul_overlap_le_one hN s) (k + 2) 0
  have h1Q : Integrable (fun ω => 1 - guerraReplicaAccum N s β (sk.U ω) h t
      (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0) ℙ :=
    (integrable_const 1).sub hQ
  have hIQ : Integrable (fun ω => (N * β ^ 2 / 2) * (1 - guerraReplicaAccum N s β (sk.U ω) h t
      (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0)) ℙ := h1Q.const_mul _
  have he : ∀ ω, guerraD N s β (sk.U ω) h (k + 2) t 0 =
      (1 / (2 * t)) * guerraUD N s β (sk.U ω) (sk.U ω) h t (k + 2) 0 -
        (N * β ^ 2 / 2) * (1 - guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0) := by
    intro ω
    rw [guerraD_eq_radials_overlap hN s β h (sk.U ω) ht,
      guerraYD_eq_sum N s β (sk.U ω) h ht]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero,
      guerraFieldTerm, Nat.sub_self, s.q_zero, add_zero]
  simp_rw [he]
  rw [integral_sub (hU.const_mul _) hIQ,
    integral_const_mul, integral_const_mul, integral_sub (integrable_const 1) hQ,
    guerra_disorder_expectation_overlap hN β h sk s ht]
  simp only [integral_const, probReal_univ, one_smul]
  field_simp [ht.1.ne']
  ring

theorem guerraRemainder_eq_expansion {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    guerraRemainder N s β h sk.U t = (β ^ 2 / 4) *
      ((∫ ω, guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => (overlap N σ τ) ^ 2) (k + 2) 0 ∂ℙ) -
        2 * (∫ ω, guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0 ∂ℙ) +
        ∑ l ∈ Finset.range (k + 2), (guerraMass s l - guerraMass s (l + 1)) * s.q (k + 2 - l) ^ 2) := by
  have hR := integrable_guerraReplicaAccum β h sk s ht (fun _ => abs_overlap_sq_le_one hN) (k + 2) 0
  have hQ := integrable_guerraReplicaAccum β h sk s ht (abs_q_mul_overlap_le_one hN s) (k + 2) 0
  have hDiff : Integrable (fun ω =>
      guerraReplicaAccum N s β (sk.U ω) h t (fun _ σ τ => (overlap N σ τ) ^ 2) (k + 2) 0 -
        2 * guerraReplicaAccum N s β (sk.U ω) h t
          (fun l σ τ => s.q (k + 2 - l) * overlap N σ τ) (k + 2) 0) ℙ := hR.sub (hQ.const_mul 2)
  rw [guerraRemainder, if_pos ht]
  simp_rw [guerraReplicaAccum_overlap_sq hN s β h _ ht]
  rw [integral_add hDiff (integrable_const _),
    integral_sub hR (hQ.const_mul 2), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

/-! ## 3. The two analytic cores of the paper -/

/--
**Theorem 2.1 (Guerra's identity).**  On `(0,1)`,

  `φ'(t) = ψ'(t) - Rem(t)`,   `0 ≤ Rem(t) ≤ β²`,

together with continuity of `φ` on `[0,1]`.  Here `ψ'(t) = -parisiCorrection`, and the
remainder is Talagrand's `(1/2) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ(ξ(R) - Rξ'(q_ℓ) + θ(q_ℓ))`, which for
the SK model is `(β²/4) ∑_ℓ (m_ℓ - m_{ℓ-1}) μ_ℓ((R_{1,2} - q_ℓ)²)`: non-negative by (2.11),
and at most `β²` since `|R_{1,2} - q_ℓ| ≤ 2` and `∑_ℓ (m_ℓ - m_{ℓ-1}) = 1`.  No `c(N)`
error term: the covariance kernel is exactly `(Nβ²/2) R²`.

The proof combines closed-interval continuity, the assembled field identity
`guerraD_eq_radials_overlap`, the disorder expectation `guerraD_top_expectation`, and
completion of the square in `guerraRemainder_eq_expansion`. The explicit witness and
its bounds are proved independently; no analytic-core placeholder is used here.
-/
theorem guerra_identity {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (guerraPhi N s β h sk.U) (Set.Icc (0 : ℝ) 1) ∧
    ∃ Rem : ℝ → ℝ, (∀ t, 0 ≤ Rem t ∧ Rem t ≤ β ^ 2) ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (guerraPhi N s β h sk.U) (-(parisiCorrection s β) - Rem t) t := by
  refine ⟨continuousOn_guerraPhi β h sk s, ?_⟩
  refine ⟨guerraRemainder N s β h sk.U, guerraRemainder_nonneg_le hN s β h sk.U, ?_⟩
  intro t ht
  refine (hasDerivAt_guerraPhi β h sk s ht).congr_deriv ?_
  rw [guerraD_top_expectation hN β h sk s ht, guerraRemainder_eq_expansion hN β h sk s ht,
    parisiCorrection_eq_mass_q]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNR]
  ring

/-! ## 4. Target 3 from Theorem 2.1 -/

/-- **Target 3 (Guerra 2003), (2.12)–(2.15).**  `φ - ψ` is non-increasing because
`Rem ≥ 0`, so `φ(1) ≤ ψ(1)`: the free entropy is at most `𝒫_k(m,q)`, with no `O(1/N)`
error term. -/
theorem guerra_rsb_bound {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) {k : ℕ} (s : RSBScheme k) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U ≤ parisiFunctional s β h := by
  obtain ⟨hcont, Rem, hRem, hderiv⟩ := guerra_identity hN β h sk s
  have hdiff : DifferentiableOn ℝ (guerraPhi N s β h sk.U) (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hle : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (guerraPhi N s β h sk.U) t ≤ -(parisiCorrection s β) := by
    rw [interior_Icc]
    intro t ht
    rw [(hderiv t ht).deriv]
    linarith [(hRem t).1]
  have hmvt := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff hle
    0 (by simp) 1 (by simp) zero_le_one
  rw [guerraPhi_one N hN s β h sk.U, guerraPhi_zero N hN s β h sk.U] at hmvt
  rw [parisiFunctional]
  simp only [parisiCorrection, sub_zero, mul_one] at hmvt
  linarith

/-- **Target 3' (upper bound in the limit).**  Immediate from Target 3: the free entropy is a
lower bound for the whole defining set of `parisiValue`, hence at most its infimum. -/
theorem limsup_free_entropy_le_parisiValue (β h : ℝ)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h + ε := by
  intro ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hle : free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U ≤ parisiValue β h := by
    refine le_csInf (parisiSet_nonempty β h) ?_
    rintro x ⟨k, s, rfl⟩
    exact guerra_rsb_bound hN β h (sk N) s
  linarith

/-! ## 5. Target 4 from Theorems 2.1 and 2.2 -/

/--
**Target 4 (the Parisi formula), Talagrand's Theorem 1.1**, deduced from Theorems 2.1 and
2.2 exactly as on p. 229–230 of the paper.

Upper half: Target 3'.  Lower half: fix `a < 𝒫` and pick `t₀ < 1` so close to `1` that
`L(1 - t₀)` is small, where `L` bounds `|φ'|` by Theorem 2.1.  Theorem 2.2 supplies `ε`; by
definition of the infimum some scheme is `ε`-optimal, and Target 2b-i replaces it by a
minimiser at the same level, which is still `ε`-optimal.  Then `φ_N(t₀) → ψ(t₀) ≥ 𝒫`, and
`φ_N(1) ≥ φ_N(t₀) - L(1 - t₀)` by the mean value theorem, so eventually `φ_N(1) > a`.
-/
theorem parisi_formula_of_theorem_2_2 (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h)
    (hthm2_2 : ∀ {t₀ : ℝ}, t₀ < 1 →
      ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
        parisiFunctional s β h ≤ parisiValue β h + ε →
        (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
        ∀ t, 0 ≤ t → t ≤ t₀ →
          Tendsto (fun N => guerraPhi N s β h (sk N).U t) atTop
            (𝓝 (guerraPsi s β h t))) :
    Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 (parisiValue β h)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound
    set η : ℝ := (parisiValue β h - a) / 2 with hη
    have hηpos : 0 < η := by rw [hη]; linarith
    set L : ℝ := β ^ 2 / 4 + β ^ 2 with hL
    have hLpos : 0 < L := by rw [hL]; positivity
    set t₀ : ℝ := max 0 (1 - η / (2 * (L + 1))) with ht₀
    have ht₀0 : 0 ≤ t₀ := le_max_left _ _
    have ht₀1 : t₀ < 1 := by
      rw [ht₀]
      apply max_lt one_pos
      have : 0 < η / (2 * (L + 1)) := by positivity
      linarith
    have hgap : L * (1 - t₀) ≤ η / 2 := by
      have h1 : 1 - η / (2 * (L + 1)) ≤ t₀ := le_max_right _ _
      have h2 : 1 - t₀ ≤ η / (2 * (L + 1)) := by linarith
      have hfrac : L / (L + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      have hrw : L * (η / (2 * (L + 1))) = (η / 2) * (L / (L + 1)) := by
        field_simp
      calc L * (1 - t₀) ≤ L * (η / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h2 hLpos.le
        _ = (η / 2) * (L / (L + 1)) := hrw
        _ ≤ η / 2 := by nlinarith [hηpos.le]
    obtain ⟨ε, hεpos, hthm⟩ := hthm2_2 ht₀1
    -- an `ε`-optimal scheme, then a minimiser at its level (Target 2b-i)
    obtain ⟨x, ⟨k, s₀, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (parisiSet_nonempty β h)
      (show sInf {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}
          < parisiValue β h + ε from lt_add_of_pos_right _ hεpos)
    obtain ⟨s, hsmin⟩ := exists_minimizer_parisiFunctional k β h
    have hs16 : parisiFunctional s β h ≤ parisiValue β h + ε := le_trans (hsmin s₀) hx.le
    have hconv := hthm s hs16 hsmin t₀ ht₀0 le_rfl
    -- `ψ(t₀) ≥ 𝒫`
    have hψ : parisiValue β h ≤ guerraPsi s β h t₀ := by
      have h1 : parisiValue β h ≤ parisiFunctional s β h := parisiValue_le s β h
      rw [← guerraPsi_one] at h1
      rw [guerraPsi] at h1 ⊢
      have hc := parisiCorrection_nonneg s β
      nlinarith [ht₀1.le]
    have hev1 : ∀ᶠ N in atTop,
        guerraPsi s β h t₀ - η / 2 < guerraPhi N s β h (sk N).U t₀ :=
      (tendsto_order.1 hconv).1 _ (by linarith)
    filter_upwards [hev1, eventually_gt_atTop 0] with N hN1 hNpos
    -- mean value theorem on `[t₀, 1]` with `|φ'| ≤ L`
    obtain ⟨hcont, Rem, hRem, hderiv⟩ := guerra_identity hNpos β h (sk N) s
    have hdiff : DifferentiableOn ℝ (guerraPhi N s β h (sk N).U)
        (interior (Set.Icc (0 : ℝ) 1)) := by
      rw [interior_Icc]
      intro t ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    have hge : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        -L ≤ deriv (guerraPhi N s β h (sk N).U) t := by
      rw [interior_Icc]
      intro t ht
      rw [(hderiv t ht).deriv]
      have := parisiCorrection_le s β
      have := (hRem t).2
      rw [hL]
      linarith
    have hmvt := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont hdiff hge
      t₀ ⟨ht₀0, ht₀1.le⟩ 1 (by simp) ht₀1.le
    rw [guerraPhi_one N hNpos s β h (sk N).U] at hmvt
    show a < free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U
    linarith
  · -- upper bound: Target 3'
    have hε : 0 < (b - parisiValue β h) / 2 := by linarith
    filter_upwards [limsup_free_entropy_le_parisiValue β h sk _ hε] with N hN
    show free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U < b
    linarith

#print axioms parisi_formula_of_theorem_2_2

end Targets
end SpinGlass
