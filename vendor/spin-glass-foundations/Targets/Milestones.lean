module

/- Adapted for the paper formalization: removed off-path unfinished declaration Φ_monotoneOn; removed off-path unfinished declaration free_entropy_tendsto; removed off-path unfinished declaration parisiFunctional_lipschitz. Original source and pinned revision are recorded in PROVENANCE.json. -/
public import ParisiFormula.GuerraToninelli
public import ParisiFormula.AnnealedBound
public import ParisiFormula.GaussianCosh
public import ParisiFormula.ParisiOperator
public import ParisiFormula.GaussianConcentration1D
public import ParisiFormula.GaussianExpCompare
public import Lemmas.SmartPath.Interpolation
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# The finite-step Parisi functional and supporting milestones

This file contains the Parisi recursion, its fixed-level parameter continuity and
minimizer, the replica-symmetric case, and the well-definedness of `parisiValue`.
These are proved. Three legacy targets remain open: `Φ_monotoneOn`,
`free_entropy_tendsto`, and `parisiFunctional_lipschitz`; none is used by the completed
final deduction exported from `Targets/Talagrand.lean`.

The completed SK Theorems 2.1, 2.2 and 2.4 and the Parisi formula are exported from
`Targets/Talagrand.lean`. `lake build Targets` builds the full proof and the axiom
guards in `Targets/GuerraAudit.lean`; elaboration errors are not allowed.

## Conventions (inherited from the RSAT dependency's `Lemmas.SpinGlass` modules)

* A configuration on `N` spins is `Config N := Fin N → Bool`, with `spin N σ i ∈ {±1}`.
* An SK disorder `sk : SKDisorder N β h` is a centred Gaussian random vector
  `sk.U : Ω → EnergySpace N` with covariance `E[U σ · U τ] = (N β²/2) · R(σ,τ)²`,
  where `R` is the overlap.  In the language of mixed p-spin models this is
  `N β² ξ(R)` with `ξ(x) = x²/2`.
* The quenched free entropy is `free_entropy β h sk.U = (1/N) E log ∑_σ exp(U σ + h ∑ᵢ σᵢ)`
  (defined in `ParisiFormula/GuerraToninelli.lean`).

## References

* M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263.
* F. Guerra, *Broken replica symmetry bounds in the mean field spin glass model*,
  Comm. Math. Phys. 233 (2003), 1–12.
* F. Guerra, F. L. Toninelli, *The thermodynamic limit in mean field spin glass models*,
  Comm. Math. Phys. 230 (2002), 71–79.
* M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I (Ch. 1) and Vol. II (Ch. 12–14).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal ProbabilityTheory

namespace SpinGlass
namespace Targets

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Milestone 1 — existence of the thermodynamic limit (Guerra–Toninelli)

`ParisiFormula/GuerraToninelli.lean` already contains the whole argument *except* two
hypotheses that were left open upstream: an upper bound on the free entropy, and
monotonicity of the interpolation `Φ`.  Targets 1a and 1b discharge them; 1c assembles.
-/

/-- Mutual independence of the three disorders entering the Guerra–Toninelli interpolation
(sizes `N+M`, `N`, `M`).  Expressed as pairwise independence of `skN.U` and `skM.U`, plus
independence of `skL.U` from the pair. -/
structure IndepTriple {N M : ℕ} {β h : ℝ}
    (skL : SKDisorder (Ω := Ω) (N + M) β h)
    (skN : SKDisorder (Ω := Ω) N β h)
    (skM : SKDisorder (Ω := Ω) M β h) : Prop where
  indep_NM : skN.U ⟂ᵢ[(ℙ : Measure Ω)] skM.U
  indep_L_pair : skL.U ⟂ᵢ[(ℙ : Measure Ω)] (fun ω => (skN.U ω, skM.U ω))

/-- **Target 1a (annealed bound).**  Jensen's inequality `E log Z ≤ log E Z` and the Gaussian
moment generating function give `(1/N) E log Z_N ≤ log 2 + β²/4 + |h|`.

Reference: Talagrand Vol. I, (1.24) and the discussion after it. -/
theorem free_entropy_le_annealed {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U
      ≤ Real.log 2 + β ^ 2 / 4 + |h| :=
  _root_.SpinGlass.free_entropy_le_annealed hN β h sk

/- **Target 1b (Gaussian comparison).**  The Guerra–Toninelli interpolation
`Φ(t) = E log Z_{N+M}(√t · K_{N+M} + √(1-t) · (K_N ⊕ K_M))` is non-decreasing on `[0,1]`.

Proof plan (blueprint, Chapter 1): differentiate under the expectation (dominated
convergence, cf. `SpinGlass.hasDerivAt_nu` in `Lemmas/SpinGlass/Replicas.lean`), rewrite
`Φ'(t)` by Gaussian integration by parts
(`PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov`) as a trace of
the covariance difference `C_L - C_blk` against the Hessian of `log Z`
(`SpinGlass.trace_formula`), then use the two facts already proved in
`ParisiFormula/GuerraToninelli.lean`: the diagonal of `C_L - C_blk` vanishes and its
off-diagonal is `≤ 0` (convexity of `x ↦ x²`), while the off-diagonal Hessian entries of
`log Z` are `≤ 0`.  Hence `Φ' ≥ 0`.

Reference: Guerra–Toninelli (2002); Talagrand Vol. I, Theorem 1.3.7 (in the 2nd edition:
Section 1.3, "the Guerra–Toninelli argument"). -/
/- Legacy unfinished declaration removed from this trusted dependency slice. -/

/- **Target 1c (thermodynamic limit).**  Assembles 1a and 1b with the already-formalised
Fekete argument `free_entropy_tendsto_of_bddAbove`. -/
/- Legacy unfinished declaration removed from this trusted dependency slice. -/

/-! ## Milestone 2 — the finite-step Parisi functional (no PDE)

Following Talagrand (Annals 2006, §1), a `k`-step replica-symmetry-breaking scheme is a pair
of non-decreasing sequences

  `0 = m₀ ≤ m₁ ≤ ⋯ ≤ m_k ≤ m_{k+1} = 1`,   `0 = q₀ ≤ q₁ ≤ ⋯ ≤ q_{k+1} ≤ q_{k+2} = 1`.

The functional is defined by a *finite backward recursion* through the Gaussian smoothing
operator `T_{m,v}`, so no Parisi PDE is needed. The compiled port
`ParisiFormula/ParisiOperator.lean` provides the bounded-function semigroup law;
`ParisiFormula/ParisiOperatorGrowth.lean` extends it to linear growth.
-/

/-- A `k`-step RSB scheme.  Sequences are indexed by `ℕ` (values beyond the stated range are
irrelevant) to avoid dependent-index bookkeeping. -/
structure RSBScheme (k : ℕ) where
  /-- `m 0 = 0`, …, `m (k+1) = 1`. -/
  m : ℕ → ℝ
  /-- `q 0 = 0`, …, `q (k+2) = 1`. -/
  q : ℕ → ℝ
  m_zero : m 0 = 0
  m_top : m (k + 1) = 1
  m_mono : ∀ p, p ≤ k → m p ≤ m (p + 1)
  q_zero : q 0 = 0
  q_top : q (k + 2) = 1
  q_mono : ∀ p, p ≤ k + 1 → q p ≤ q (p + 1)

/-- Gaussian smoothing step at "temperature" `m` and variance `v`:

  `T_{m,v} A (x) = (1/m) log ∫ exp(m · A(x + √v · z)) dγ(z)`  for `m ≠ 0`,
  `T_{0,v} A (x) = ∫ A(x + √v · z) dγ(z)`,

with `γ` the standard Gaussian.  The `m = 0` case is the `m → 0` limit of the first. -/
noncomputable def parisiStep (m v : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then
    ∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1)
  else
    (1 / m) * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))

/--
**Reconciliation of `parisiStep` with the ported operator `Parisi.T`** (roadmap Phase 2).

For `m ≠ 0` the two agree, via the Gaussian rescaling
`integral_comp_sqrt_mul_gaussianReal`.

They do **not** agree at `m = 0`, and this matters.  `Parisi.T` has no `m = 0` branch, so
`Parisi.T 0 v A x = (1/0) * log (…) = 0`, whereas `parisiStep 0 v A x` is the `m → 0` limit
`∫ A (x + √v z) dγ`.  So `parisiStep` must **not** be redefined as `Parisi.T`: the `m = 0`
branch is precisely the outermost step `F₀ = T_{0, β²q₁} F₁` of the Parisi recursion, and
collapsing it to `0` would break `parisiFunctional` (and with it Target 2a, which is proved
below and does use that branch).
-/
theorem parisiStep_eq_T {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0) {A : ℝ → ℝ} (hA : Measurable A)
    (x : ℝ) :
    parisiStep m (v : ℝ) A x = Parisi.T m v A x := by
  have hf : Measurable (fun y : ℝ => Real.exp (m * A y)) :=
    Real.continuous_exp.measurable.comp (hA.const_mul m)
  rw [parisiStep, if_neg hm, Parisi.T,
      integral_comp_sqrt_mul_gaussianReal v hf x]

/--
**The smoothing step is non-expansive in the sup-norm of its argument.**

If `|A - A'| ≤ ε` pointwise then `|T_{m,v} A - T_{m,v} A'| ≤ ε`, *uniformly in `m` and `v`*.

This is the inductive engine for **Target 2b**: a perturbation of the scheme parameters
`(m,q)` changes each level of the backward recursion by a controlled amount, and this lemma
carries that change through the remaining levels without amplification.  The uniformity in
`m` is what makes the resulting Lipschitz constant independent of `k`, which is exactly the
property Target 2b needs (see the note there on quantifier order).

For `m ≠ 0` the proof is the standard one: `|m(A - A')| ≤ |m| ε` gives `I ≤ e^{|m|ε} I'` for
the two exponential integrals, hence `|log I - log I'| ≤ |m| ε`, and the prefactor `1/m`
cancels the `|m|`.

The integrability hypotheses are not removable: the `m = 0` branch needs `A`, `A'`
integrable, and the `m ≠ 0` branch needs the exponentials integrable, else Lean's junk value
`∫ = 0` breaks the comparison.  Discharging them for `parisiF` at every level is the
"moderate-growth" item of Phase 2 in `docs/ROADMAP.md`.
-/
theorem parisiStep_dist_le {m v ε x : ℝ} {A A' : ℝ → ℝ}
    (hε : ∀ y, |A y - A' y| ≤ ε)
    (hA : Integrable (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1))
    (hA' : Integrable (fun z => A' (x + Real.sqrt v * z)) (gaussianReal 0 1))
    (hEA : Integrable (fun z => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1))
    (hEA' : Integrable (fun z => Real.exp (m * A' (x + Real.sqrt v * z))) (gaussianReal 0 1)) :
    |parisiStep m v A x - parisiStep m v A' x| ≤ ε := by
  classical
  by_cases hm : m = 0
  · simp only [parisiStep, if_pos hm]
    rw [← integral_sub hA hA']
    calc |∫ z, (A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)|
        ≤ ∫ z, |A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z)| ∂(gaussianReal 0 1) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm
              (μ := (gaussianReal 0 1))
              (f := fun z => A (x + Real.sqrt v * z) - A' (x + Real.sqrt v * z))
      _ ≤ ∫ _z : ℝ, ε ∂(gaussianReal 0 1) :=
          integral_mono (hA.sub hA').abs (integrable_const ε)
            (fun z => hε (x + Real.sqrt v * z))
      _ = ε := by simp
  · have hmabs : (0 : ℝ) < |m| := abs_pos.2 hm
    have hIpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      integral_exp_pos hEA
    have hI'pos : 0 < ∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
      integral_exp_pos hEA'
    have key : ∀ B B' : ℝ → ℝ,
        (∀ y, |B y - B' y| ≤ ε) →
        Integrable (fun z => Real.exp (m * B (x + Real.sqrt v * z))) (gaussianReal 0 1) →
        Integrable (fun z => Real.exp (m * B' (x + Real.sqrt v * z))) (gaussianReal 0 1) →
        (∫ z, Real.exp (m * B (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ Real.exp (|m| * ε)
            * ∫ z, Real.exp (m * B' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) := by
      intro B B' hBB hEB hEB'
      have hpt : ∀ z : ℝ,
          Real.exp (m * B (x + Real.sqrt v * z))
            ≤ Real.exp (|m| * ε) * Real.exp (m * B' (x + Real.sqrt v * z)) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z)) ≤ |m| * ε := by
          calc m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z))
              ≤ |m * (B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z))| := le_abs_self _
            _ = |m| * |B (x + Real.sqrt v * z) - B' (x + Real.sqrt v * z)| := abs_mul _ _
            _ ≤ |m| * ε :=
                mul_le_mul_of_nonneg_left (hBB (x + Real.sqrt v * z)) (abs_nonneg m)
        linarith
      calc (∫ z, Real.exp (m * B (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ ∫ z, Real.exp (|m| * ε) * Real.exp (m * B' (x + Real.sqrt v * z))
              ∂(gaussianReal 0 1) :=
            integral_mono hEB (hEB'.const_mul _) hpt
        _ = Real.exp (|m| * ε)
              * ∫ z, Real.exp (m * B' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) :=
            integral_const_mul _ _
    have hεsymm : ∀ y, |A' y - A y| ≤ ε := by
      intro y
      rw [abs_sub_comm]
      exact hε y
    have h1 := key A A' hε hEA hEA'
    have h2 := key A' A hεsymm hEA' hEA
    have hlog1 :
        Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ |m| * ε := by
      have h := Real.log_le_log hIpos h1
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hI'pos), Real.log_exp] at h
      linarith
    have hlog2 :
        Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          ≤ |m| * ε := by
      have h := Real.log_le_log hI'pos h2
      rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hIpos), Real.log_exp] at h
      linarith
    have habs :
        |Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
          - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))|
          ≤ |m| * ε := abs_le.2 ⟨by linarith, hlog1⟩
    simp only [parisiStep, if_neg hm]
    rw [← mul_sub, abs_mul, abs_one_div]
    calc 1 / |m|
          * |Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))
              - Real.log (∫ z, Real.exp (m * A' (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))|
        ≤ 1 / |m| * (|m| * ε) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ = ε := by field_simp

/--
**The smoothing step preserves linear growth.**

Together with `hasLinearGrowth_log_cosh` this closes the induction that discharges
`parisiStep_dist_le`'s integrability hypotheses at every level of `parisiF`.

For `m ≠ 0` the constant produced here degrades like `1/|m|`.  That is an artefact of the
crude two-sided bound and is harmless: growth preservation is only ever used at a *fixed*
`m`, purely to obtain integrability.  The estimate that must be uniform in `m` is
`parisiStep_dist_le`, and that one is.
-/
theorem hasLinearGrowth_parisiStep {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v : ℝ) :
    HasLinearGrowth (parisiStep m v A) := by
  classical
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  have hshift : ∀ x z : ℝ,
      |A (x + Real.sqrt v * z)| ≤ (C + D * |x|) + (D * |Real.sqrt v|) * |z| := by
    intro x z
    refine (hb _).trans ?_
    have habs : |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v| * |z| := by
      calc |x + Real.sqrt v * z| ≤ |x| + |Real.sqrt v * z| := abs_add_le _ _
        _ = |x| + |Real.sqrt v| * |z| := by rw [abs_mul]
    nlinarith [abs_nonneg z, abs_nonneg (Real.sqrt v)]
  by_cases hm : m = 0
  · -- `m = 0`: the step is the plain Gaussian average.
    set M : ℝ := ∫ z, |z| ∂(gaussianReal 0 1) with hMdef
    have hM0 : 0 ≤ M := integral_nonneg (fun z => abs_nonneg z)
    refine ⟨C + (D * |Real.sqrt v|) * M, D, by positivity, hD, fun x => ?_⟩
    simp only [parisiStep, if_pos hm]
    have hint : Integrable (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) :=
      integrable_of_hasLinearGrowth ⟨C, D, hC, hD, hb⟩ hmeas x v
    have hdom : Integrable
        (fun z : ℝ => (C + D * |x|) + (D * |Real.sqrt v|) * |z|) (gaussianReal 0 1) :=
      (integrable_const _).add ((integrable_id_stdGaussian.abs).const_mul _)
    calc |∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1)|
        ≤ ∫ z, |A (x + Real.sqrt v * z)| ∂(gaussianReal 0 1) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := (gaussianReal 0 1))
              (f := fun z => A (x + Real.sqrt v * z))
      _ ≤ ∫ z, ((C + D * |x|) + (D * |Real.sqrt v|) * |z|) ∂(gaussianReal 0 1) :=
          integral_mono hint.abs hdom (fun z => hshift x z)
      _ = (C + D * |x|) + (D * |Real.sqrt v|) * M := by
          rw [integral_add (integrable_const _)
                ((integrable_id_stdGaussian.abs).const_mul _),
            integral_const_mul]
          simp [hMdef, probReal_univ]
      _ = (C + (D * |Real.sqrt v|) * M) + D * |x| := by ring
  · -- `m ≠ 0`.
    have hmabs : (0 : ℝ) < |m| := abs_pos.2 hm
    set a : ℝ := |m| * (D * |Real.sqrt v|) with hadef
    set K : ℝ := ∫ z, Real.exp (a * |z|) ∂(gaussianReal 0 1) with hKdef
    set K' : ℝ := ∫ z, Real.exp (-a * |z|) ∂(gaussianReal 0 1) with hK'def
    have hKpos : 0 < K := integral_exp_pos (integrable_exp_abs_mul_stdGaussian a)
    have hK'pos : 0 < K' := integral_exp_pos (integrable_exp_abs_mul_stdGaussian (-a))
    set E : ℝ := |Real.log K| + |Real.log K'| with hEdef
    refine ⟨C + E / |m|, D, by positivity, hD, fun x => ?_⟩
    simp only [parisiStep, if_neg hm]
    set I : ℝ := ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) with hIdef
    have hIint : Integrable
        (fun z => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1) :=
      integrable_exp_mul_of_hasLinearGrowth ⟨C, D, hC, hD, hb⟩ hmeas m x v
    have hIpos : 0 < I := integral_exp_pos hIint
    set B : ℝ := |m| * (C + D * |x|) with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hkey : ∀ z : ℝ, |m| * |A (x + Real.sqrt v * z)| ≤ B + a * |z| := by
      intro z
      have h := mul_le_mul_of_nonneg_left (hshift x z) (abs_nonneg m)
      calc |m| * |A (x + Real.sqrt v * z)|
          ≤ |m| * ((C + D * |x|) + (D * |Real.sqrt v|) * |z|) := h
        _ = B + a * |z| := by rw [hBdef, hadef]; ring
    have hup : I ≤ Real.exp B * K := by
      have hpt : ∀ z : ℝ,
          Real.exp (m * A (x + Real.sqrt v * z))
            ≤ Real.exp B * Real.exp (a * |z|) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : m * A (x + Real.sqrt v * z) ≤ |m| * |A (x + Real.sqrt v * z)| := by
          calc m * A (x + Real.sqrt v * z) ≤ |m * A (x + Real.sqrt v * z)| := le_abs_self _
            _ = |m| * |A (x + Real.sqrt v * z)| := abs_mul _ _
        linarith [hkey z]
      calc I ≤ ∫ z, Real.exp B * Real.exp (a * |z|) ∂(gaussianReal 0 1) :=
            integral_mono hIint ((integrable_exp_abs_mul_stdGaussian a).const_mul _) hpt
        _ = Real.exp B * K := integral_const_mul _ _
    have hlow : Real.exp (-B) * K' ≤ I := by
      have hpt : ∀ z : ℝ,
          Real.exp (-B) * Real.exp (-a * |z|)
            ≤ Real.exp (m * A (x + Real.sqrt v * z)) := by
        intro z
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : -(|m| * |A (x + Real.sqrt v * z)|) ≤ m * A (x + Real.sqrt v * z) := by
          calc -(|m| * |A (x + Real.sqrt v * z)|)
              = -|m * A (x + Real.sqrt v * z)| := by rw [abs_mul]
            _ ≤ m * A (x + Real.sqrt v * z) := neg_abs_le _
        linarith [hkey z]
      calc Real.exp (-B) * K'
          = ∫ z, Real.exp (-B) * Real.exp (-a * |z|) ∂(gaussianReal 0 1) :=
            (integral_const_mul _ _).symm
        _ ≤ I :=
            integral_mono ((integrable_exp_abs_mul_stdGaussian (-a)).const_mul _) hIint hpt
    have hlogup : Real.log I ≤ B + Real.log K := by
      have h := Real.log_le_log hIpos hup
      rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hKpos), Real.log_exp] at h
    have hloglow : -B + Real.log K' ≤ Real.log I := by
      have h := Real.log_le_log (by positivity) hlow
      rwa [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hK'pos), Real.log_exp] at h
    have habsI : |Real.log I| ≤ B + E := by
      refine abs_le.2 ⟨?_, ?_⟩
      · have h1 : -Real.log K' ≤ |Real.log K'| := neg_le_abs _
        have h2 : (0 : ℝ) ≤ |Real.log K| := abs_nonneg _
        rw [hEdef]
        linarith
      · have h1 : Real.log K ≤ |Real.log K| := le_abs_self _
        have h2 : (0 : ℝ) ≤ |Real.log K'| := abs_nonneg _
        rw [hEdef]
        linarith
    rw [abs_mul, abs_one_div]
    calc 1 / |m| * |Real.log I|
        ≤ 1 / |m| * (B + E) := mul_le_mul_of_nonneg_left habsI (by positivity)
      _ = (C + E / |m|) + D * |x| := by
          rw [hBdef]
          field_simp
          ring

/--
**The smoothing step does not increase the Lipschitz constant.**

If `A` is `L`-Lipschitz then so is `parisiStep m v A`, *uniformly in `m` and `v`*.

This is a corollary of `parisiStep_dist_le`, by a translation trick: comparing `A` with
`y ↦ A (y + (x' - x))` turns a change of *evaluation point* into a change of *function*, and
the two differ uniformly by at most `L |x - x'|`.

With `log_cosh_dist_le` as the base case this gives: every level `F_p` of the Parisi
recursion is 1-Lipschitz.  That is what makes a perturbation of the variance `v` tractable
in Target 2b — the argument `x + √v z` then moves by `(√v - √v') z`, and Lipschitz control
converts that into something integrable against the Gaussian.
-/
theorem parisiStep_lipschitz {m v L : ℝ} {A : ℝ → ℝ}
    (hL : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x x' : ℝ) :
    |parisiStep m v A x - parisiStep m v A x'| ≤ L * |x - x'| := by
  classical
  set c : ℝ := x' - x with hc
  set A' : ℝ → ℝ := fun y => A (y + c) with hA'def
  -- `A'` inherits measurability and linear growth
  have hmeas' : Measurable A' := hmeas.comp (measurable_id.add_const c)
  have hgrow' : HasLinearGrowth A' := by
    obtain ⟨C, D, hC, hD, hb⟩ := hA
    refine ⟨C + D * |c|, D, by positivity, hD, fun y => ?_⟩
    refine (hb (y + c)).trans ?_
    have htri : |y + c| ≤ |y| + |c| := abs_add_le _ _
    nlinarith [abs_nonneg y, abs_nonneg c]
  -- translating the argument turns the point change into a function change
  have hshift : ∀ z : ℝ, A' (x + Real.sqrt v * z) = A (x' + Real.sqrt v * z) := by
    intro z
    show A (x + Real.sqrt v * z + c) = A (x' + Real.sqrt v * z)
    congr 1
    rw [hc]; ring
  have heq : parisiStep m v A' x = parisiStep m v A x' := by
    simp only [parisiStep]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
      exact integral_congr_ae (Filter.Eventually.of_forall hshift)
    · rw [if_neg hm, if_neg hm]
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.exp (m * A' (x + Real.sqrt v * z))
          = Real.exp (m * A (x' + Real.sqrt v * z))
      rw [hshift z]
  have hunif : ∀ y, |A y - A' y| ≤ L * |x - x'| := by
    intro y
    have h := hL y (y + c)
    have hrw : |y - (y + c)| = |x - x'| := by
      rw [show y - (y + c) = -c by ring, abs_neg, hc, abs_sub_comm]
    rwa [hrw] at h
  rw [← heq]
  exact parisiStep_dist_le hunif
    (integrable_of_hasLinearGrowth hA hmeas x v)
    (integrable_of_hasLinearGrowth hgrow' hmeas' x v)
    (integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v)
    (integrable_exp_mul_of_hasLinearGrowth hgrow' hmeas' m x v)

/--
Pure arithmetic behind the variance-perturbation estimate: if `X` is squeezed between
`mm * c` and `mm * c + B mm² / 2`, then `1/mm * X` is within `|mm| B / 2` of `c`.

Isolated from the measure theory so that the two can fail independently.
-/
theorem abs_inv_mul_sub_le_of_bounds {X c mm B : ℝ} (hmm : mm ≠ 0) (hB : 0 ≤ B)
    (h1 : mm * c ≤ X) (h2 : X ≤ mm * c + B * mm ^ 2 / 2) :
    |1 / mm * X - c| ≤ |mm| * B / 2 := by
  have hmpos : 0 < |mm| := abs_pos.2 hmm
  have hid : mm * (1 / mm * X - c) = X - mm * c := by field_simp
  have habs : |mm| * |1 / mm * X - c| = |X - mm * c| := by
    rw [← abs_mul, hid]
  have hb : |X - mm * c| ≤ B * mm ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hsq : |mm| * |mm| = mm ^ 2 := by
    rw [abs_mul_abs_self]; ring
  refine le_of_mul_le_mul_left ?_ hmpos
  calc |mm| * |1 / mm * X - c| = |X - mm * c| := habs
    _ ≤ B * mm ^ 2 / 2 := hb
    _ = |mm| * (|mm| * B / 2) := by
        rw [show |mm| * (|mm| * B / 2) = |mm| * |mm| * B / 2 by ring, hsq]
        ring

/--
**The variance-perturbation estimate.**

For `A` `L`-Lipschitz, `w > 0` and `m ≠ 0`,

  `|T_{m,w} A (x) - A x| ≤ L √w 𝔼|Z| + |m| L² w / 2`.

This is the analytic core of the `q`-perturbation half of Target 2b: via the semigroup law
`Parisi.T_add`, changing a scheme parameter `q_p` factors as an extra smoothing step of small
variance `w`, and this bounds its effect.

Both bounds on `(1/m) log 𝔼[exp (m g)]`, `g z = A (x + √w z) - A x`, are used:

* **above** by the Herbst sub-Gaussian bound (`gaussianReal_mgf_le_of_lipschitz`);
* **below** by Jensen (`integral_log_le_log_integral`, proved for Target 1a and generalised
  to an arbitrary probability measure for exactly this use).

The estimate stays bounded as `m → 0`, which the naive `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)` would
not; that is what keeps Target 2b's constant uniform in `k`.
-/
theorem abs_parisiStep_sub_self_le {A : ℝ → ℝ} {L m w : ℝ}
    (hL : 0 < L) (hw : 0 < w) (hm : m ≠ 0)
    (hLip : ∀ y y', |A y - A y'| ≤ L * |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    |parisiStep m w A x - A x|
      ≤ L * Real.sqrt w * (∫ z, |z| ∂(gaussianReal 0 1)) + |m| * (L ^ 2 * w) / 2 := by
  classical
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hLw : 0 < L * Real.sqrt w := mul_pos hL hsw
  have hfmeas : Measurable (fun z : ℝ => A (x + Real.sqrt w * z)) :=
    hmeas.comp (by fun_prop)
  have hfint : Integrable (fun z : ℝ => A (x + Real.sqrt w * z)) (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth hA hmeas x w
  have hexpint : Integrable
      (fun z : ℝ => Real.exp (m * A (x + Real.sqrt w * z))) (gaussianReal 0 1) :=
    integrable_exp_mul_of_hasLinearGrowth hA hmeas m x w
  have hIpos : 0 < ∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1) :=
    integral_exp_pos hexpint
  -- `z ↦ A (x + √w z)` is `L √w`-Lipschitz
  have hfLip : LipschitzWith (L * Real.sqrt w).toNNReal
      (fun z : ℝ => A (x + Real.sqrt w * z)) := by
    refine LipschitzWith.of_dist_le_mul (fun z z' => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hLw.le]
    have h := hLip (x + Real.sqrt w * z) (x + Real.sqrt w * z')
    have hrw : |x + Real.sqrt w * z - (x + Real.sqrt w * z')| = Real.sqrt w * |z - z'| := by
      rw [show x + Real.sqrt w * z - (x + Real.sqrt w * z') = Real.sqrt w * (z - z') by ring,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg w)]
    rw [hrw] at h
    calc |A (x + Real.sqrt w * z) - A (x + Real.sqrt w * z')|
        ≤ L * (Real.sqrt w * |z - z'|) := h
      _ = L * Real.sqrt w * |z - z'| := by ring
  -- Herbst, rewritten as a bound on the plain exponential integral
  have hherbst := gaussianReal_mgf_le_of_lipschitz
    (fun z : ℝ => A (x + Real.sqrt w * z)) (L * Real.sqrt w) hLw hfLip hfmeas m
  have hmgf_eq : mgf (fun z : ℝ => A (x + Real.sqrt w * z)
        - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) (gaussianReal 0 1) m
      = Real.exp (-(m * ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
        * ∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1) := by
    simp only [mgf]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show Real.exp (m * (A (x + Real.sqrt w * z)
        - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
      = Real.exp (-(m * ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)))
        * Real.exp (m * A (x + Real.sqrt w * z))
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper : Real.log (∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1))
      ≤ m * (∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1))
        + (L ^ 2 * w) * m ^ 2 / 2 := by
    rw [hmgf_eq] at hherbst
    have h := Real.log_le_log (by positivity) hherbst
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hIpos), Real.log_exp, Real.log_exp] at h
    have hsq : (L * Real.sqrt w) ^ 2 = L ^ 2 * w := by
      rw [mul_pow, Real.sq_sqrt hw.le]
    rw [hsq] at h
    linarith
  -- Jensen
  have hlower : m * (∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1))
      ≤ Real.log (∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1)) := by
    have hlogint : Integrable
        (fun z : ℝ => Real.log (Real.exp (m * A (x + Real.sqrt w * z))))
        (gaussianReal 0 1) := by
      simpa [Real.log_exp] using hfint.const_mul m
    have h := integral_log_le_log_integral (μ := gaussianReal 0 1)
      (W := fun z : ℝ => Real.exp (m * A (x + Real.sqrt w * z)))
      (fun z => Real.exp_pos _) hexpint hlogint
    simpa [Real.log_exp, integral_const_mul] using h
  -- combine the two bounds, then add the mean term
  have hTc : |parisiStep m w A x
      - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)| ≤ |m| * (L ^ 2 * w) / 2 := by
    rw [parisiStep, if_neg hm]
    exact abs_inv_mul_sub_le_of_bounds hm (by positivity) hlower hupper
  have hcA : |(∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) - A x|
      ≤ L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) :=
    abs_integral_shift_sub_le hL.le hLip hA hmeas x w
  calc |parisiStep m w A x - A x|
      ≤ |parisiStep m w A x - ∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)|
          + |(∫ y, A (x + Real.sqrt w * y) ∂(gaussianReal 0 1)) - A x| :=
        abs_sub_le _ _ _
    _ ≤ |m| * (L ^ 2 * w) / 2 + L * Real.sqrt w * ∫ z, |z| ∂(gaussianReal 0 1) := by
        linarith [hTc, hcA]
    _ = L * Real.sqrt w * (∫ z, |z| ∂(gaussianReal 0 1)) + |m| * (L ^ 2 * w) / 2 := by ring

/--
**The smoothing step preserves the second-order invariant.**

If `A` satisfies `0 ≤ A'' ≤ 1 - (A')²` and `0 < m ≤ 1`, then so does `parisiStep m v A`,
with derivatives `stepD1` and `stepD2`.

The hypothesis `m ≤ 1` is essential and is exactly what an RSB scheme provides
(`RSBScheme.m_le_one`): it is what gives the `-(1-m)·Var_tilt(A')` term in
`(T A)'' = ⟨A''⟩ + m Var_tilt(A')` the right sign.  For `m > 1` the invariant is *not*
preserved and the second derivative can grow with the level, which would destroy the
uniformity in `k` that Target 2b needs.
-/
theorem hasParisiC2_parisiStep {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm : m ≠ 0) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hA : HasParisiC2 A A' A'')
    (hgrow : HasLinearGrowth A) (hmeas : Measurable A) (hmeas' : Measurable A')
    (hmeas'' : Measurable A'') :
    HasParisiC2 (parisiStep m v A) (stepD1 A A' m v) (stepD2 A A' A'' m v) := by
  have hA'bd : ∀ y, |A' y| ≤ 1 := fun y => hA.abs_first_le_one y
  have hA''bd : ∀ y, |A'' y| ≤ 1 := fun y => hA.abs_second_le_one y
  obtain ⟨hd1, hd2, hnn, hle⟩ := hA
  have hstep : parisiStep m v A
      = fun t : ℝ => (1 / m)
        * Real.log (∫ z, Real.exp (m * A (t + Real.sqrt v * z))
            ∂(gaussianReal 0 1)) := by
    funext t
    rw [parisiStep, if_neg hm]
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hstep]
    exact hasDerivAt_stepD1 hm hd1 hA'bd hgrow hmeas hmeas' x
  · exact hasDerivAt_stepD2 hm hd1 hd2 hA'bd hA''bd hgrow hmeas hmeas' hmeas'' x
  · exact smoothing_second_deriv_nonneg hm0 hA'bd hA''bd hnn hgrow hmeas hmeas' hmeas'' x
  · exact smoothing_second_deriv_le hm0 hm1 hA'bd hA''bd hle hgrow hmeas hmeas' hmeas'' x

/-- Backward Parisi recursion for the SK model (`ξ(x) = x²/2`, so `ξ'(x) = x`).

`parisiF s β j` is the function `F_{k+2-j}` of Talagrand's recursion:

  `F_{k+2}(x) = log cosh x`,
  `F_p = T_{m_p, β²(q_{p+1} - q_p)} F_{p+1}`   for `p = k+1, k, …, 1`,
  `F_0 = T_{0, β² q₁} F_1 = E F_1(· + β√q₁ z)`.

So `parisiF s β (k+2)` is `F_0` (there are `k+2` smoothing steps: `p = k+1, …, 1`, then `p = 0`). -/
noncomputable def parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun x => Real.log (Real.cosh x)
  | j + 1 =>
      parisiStep (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
        (parisiF s β j)

/--
**Every level of the Parisi recursion is measurable, of linear growth, and 1-Lipschitz.**

These are exactly the three side conditions that `parisiStep_dist_le`,
`hasLinearGrowth_parisiStep`, `parisiStep_lipschitz` and `abs_parisiStep_sub_self_le` all
require of the function being smoothed, so proving them once by simultaneous induction
discharges them at every level of `parisiF` — which is what Target 2b needs in order to sum
the per-level perturbation estimates over `p = 0, …, k+1`.

The three properties have to be carried *together*: the Lipschitz step needs measurability
and linear growth as hypotheses, and measurability at the next level is obtained *from* the
Lipschitz bound (Lipschitz ⟹ continuous ⟹ measurable), so neither can be proved on its own.

Base case: `log cosh` is measurable, satisfies `|log cosh y| ≤ |y|`, and is 1-Lipschitz.
Note the Lipschitz constant is `1` at every level — the smoothing step never increases it.
-/
theorem parisiF_props {k : ℕ} (s : RSBScheme k) (β : ℝ) : ∀ j : ℕ,
    Measurable (parisiF s β j)
      ∧ HasLinearGrowth (parisiF s β j)
      ∧ ∀ x x' : ℝ, |parisiF s β j x - parisiF s β j x'| ≤ |x - x'| := by
  intro j
  induction j with
  | zero =>
      refine ⟨?_, hasLinearGrowth_log_cosh, fun x x' => log_cosh_dist_le x x'⟩
      exact (Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))).measurable
  | succ j ih =>
      obtain ⟨hmeas, hgrow, hlip⟩ := ih
      have hlip' : ∀ y y' : ℝ,
          |parisiF s β j y - parisiF s β j y'| ≤ 1 * |y - y'| := by
        intro y y'
        simpa using hlip y y'
      have hstep : ∀ x x' : ℝ,
          |parisiF s β (j + 1) x - parisiF s β (j + 1) x'| ≤ |x - x'| := by
        intro x x'
        have h := parisiStep_lipschitz (m := s.m (k + 1 - j))
          (v := β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) (L := 1)
          hlip' hgrow hmeas x x'
        rw [one_mul] at h
        -- `parisiF s β (j+1)` is definitionally this `parisiStep`; `exact` uses that,
        -- whereas `simpa` normalises the two sides into different syntactic forms.
        exact h
      have hgrow' : HasLinearGrowth (parisiF s β (j + 1)) :=
        hasLinearGrowth_parisiStep hgrow hmeas _ _
      have hmeas' : Measurable (parisiF s β (j + 1)) := by
        have hL : LipschitzWith 1 (parisiF s β (j + 1)) := by
          refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
          rw [Real.dist_eq, Real.dist_eq]
          simpa using hstep a b
        exact hL.continuous.measurable
      exact ⟨hmeas', hgrow', hstep⟩

/-- Every level of the Parisi recursion is measurable. -/
theorem parisiF_measurable {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Measurable (parisiF s β j) := (parisiF_props s β j).1

/-- Every level of the Parisi recursion has linear growth. -/
theorem parisiF_hasLinearGrowth {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    HasLinearGrowth (parisiF s β j) := (parisiF_props s β j).2.1

/-- Every level of the Parisi recursion is 1-Lipschitz. -/
theorem parisiF_lipschitz {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x x' : ℝ) :
    |parisiF s β j x - parisiF s β j x'| ≤ |x - x'| := (parisiF_props s β j).2.2 x x'

/-- The `k`-step Parisi functional for the SK model with external field `h`:

  `𝒫_k(m,q) = log 2 + F_0(h) - (β²/4) ∑_{p=1}^{k+1} m_p (q_{p+1}² - q_p²)`.

(The prefactor `β²/4` is `β²/2 · (θ(q_{p+1}) - θ(q_p))` with `θ(q) = q ξ'(q) - ξ(q) = q²/2`.) -/
noncomputable def parisiFunctional {k : ℕ} (s : RSBScheme k) (β h : ℝ) : ℝ :=
  Real.log 2 + parisiF s β (k + 2) h
    - (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)

/-! ### Well-definedness of the Parisi value

`parisiValue` (below) is an `sInf`.  In Mathlib, `sInf` of a set that is **not bounded
below** is the junk value `sInf ∅ = 0` (`csInf_of_not_bddBelow`).  So without a lower
bound, Target 4 would be asserting that the free entropy converges to `0` — false.

This section supplies the missing bound: `log 2 - β²/4 ≤ 𝒫_k(m,q)` for *every* scheme,
uniformly in `k`.  Two ingredients:

* `parisiF_nonneg` — the Gaussian smoothing operator preserves non-negativity (note the
  junk values work in our favour: a non-integrable integrand gives `∫ = 0`, and
  `log 0 = 0`), and the base case `log cosh ≥ 0`;
* `sum_correction_le_one` — `∑_p m_p (q²_{p+1} - q²_p) ≤ 1` by telescoping, using
  `m_p ≤ 1` and `q` non-decreasing.
-/

namespace RSBScheme

variable {k : ℕ} (s : RSBScheme k)

/-- `s.m` is non-decreasing on `[0, k+1]`. -/
lemma m_mono' : ∀ b, b ≤ k + 1 → ∀ a, a ≤ b → s.m a ≤ s.m b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      exact le_of_eq (congrArg s.m (Nat.le_zero.mp ha))
  | succ b ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have h1 : s.m a ≤ s.m b := ih (by omega) a (Nat.lt_succ_iff.mp h)
        have h2 : s.m b ≤ s.m (b + 1) := s.m_mono b (by omega)
        linarith
      · exact le_of_eq (congrArg s.m (le_antisymm ha h))

/-- `s.q` is non-decreasing on `[0, k+2]`. -/
lemma q_mono' : ∀ b, b ≤ k + 2 → ∀ a, a ≤ b → s.q a ≤ s.q b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      exact le_of_eq (congrArg s.q (Nat.le_zero.mp ha))
  | succ b ih =>
      intro hb a ha
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have h1 : s.q a ≤ s.q b := ih (by omega) a (Nat.lt_succ_iff.mp h)
        have h2 : s.q b ≤ s.q (b + 1) := s.q_mono b (by omega)
        linarith
      · exact le_of_eq (congrArg s.q (le_antisymm ha h))

lemma m_le_one {p : ℕ} (hp : p ≤ k + 1) : s.m p ≤ 1 := by
  have h := s.m_mono' (k + 1) le_rfl p hp
  rwa [s.m_top] at h

lemma q_nonneg {p : ℕ} (hp : p ≤ k + 2) : 0 ≤ s.q p := by
  have h := s.q_mono' p hp 0 (Nat.zero_le p)
  rwa [s.q_zero] at h

end RSBScheme

/-- The Gaussian smoothing step preserves non-negativity. -/
lemma parisiStep_nonneg {m v : ℝ} {A : ℝ → ℝ} (hA : ∀ y, 0 ≤ A y) (x : ℝ) :
    0 ≤ parisiStep m v A x := by
  rw [parisiStep]
  split_ifs with hm
  · exact integral_nonneg (fun z => hA _)
  · set I : ℝ := ∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1) with hIdef
    have hI0 : 0 ≤ I := integral_nonneg (fun z => (Real.exp_pos _).le)
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · have hIle : I ≤ 1 := by
        by_cases hint : Integrable
            (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1)
        · have hmono : I ≤ ∫ _z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
            refine integral_mono hint (integrable_const 1) (fun z => ?_)
            have hle : m * A (x + Real.sqrt v * z) ≤ 0 := by
              nlinarith [hA (x + Real.sqrt v * z)]
            calc Real.exp (m * A (x + Real.sqrt v * z)) ≤ Real.exp 0 :=
                  Real.exp_le_exp.2 hle
              _ = 1 := Real.exp_zero
          simpa using hmono
        · rw [hIdef, integral_undef hint]; norm_num
      have hlog : Real.log I ≤ 0 := Real.log_nonpos hI0 hIle
      have hminv : 1 / m < 0 := div_neg_of_pos_of_neg one_pos hneg
      nlinarith
    · have hcase : (1 : ℝ) ≤ I ∨ I = 0 := by
        by_cases hint : Integrable
            (fun z : ℝ => Real.exp (m * A (x + Real.sqrt v * z))) (gaussianReal 0 1)
        · left
          have hmono : (∫ _z : ℝ, (1 : ℝ) ∂(gaussianReal 0 1)) ≤ I := by
            refine integral_mono (integrable_const 1) hint (fun z => ?_)
            have hle : (0 : ℝ) ≤ m * A (x + Real.sqrt v * z) :=
              mul_nonneg hpos.le (hA _)
            calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
              _ ≤ Real.exp (m * A (x + Real.sqrt v * z)) := Real.exp_le_exp.2 hle
          simpa using hmono
        · right; rw [hIdef, integral_undef hint]
      have hminv : 0 < 1 / m := div_pos one_pos hpos
      rcases hcase with h1 | h1
      · exact mul_nonneg hminv.le (Real.log_nonneg h1)
      · rw [h1, Real.log_zero, mul_zero]

/-- Every level of the Parisi recursion is non-negative. -/
lemma parisiF_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ∀ (j : ℕ) (x : ℝ), 0 ≤ parisiF s β j x := by
  intro j
  induction j with
  | zero => intro x; exact log_cosh_nonneg x
  | succ j ih => intro x; exact parisiStep_nonneg (fun y => ih y) x

/-- The correction sum telescopes to at most `1`. -/
lemma sum_correction_le_one {k : ℕ} (s : RSBScheme k) :
    (∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) ≤ 1 := by
  have hterm : ∀ p ∈ Finset.range (k + 1),
      s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)
        ≤ s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2 := by
    intro p hp
    have hpk : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    have hm1 : s.m (p + 1) ≤ 1 := s.m_le_one (by omega)
    have hq1 : 0 ≤ s.q (p + 1) := s.q_nonneg (by omega)
    have hqle : s.q (p + 1) ≤ s.q (p + 2) := s.q_mono (p + 1) (by omega)
    have hsq : s.q (p + 1) ^ 2 ≤ s.q (p + 2) ^ 2 := by nlinarith
    nlinarith
  calc
    (∑ p ∈ Finset.range (k + 1), s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2))
        ≤ ∑ p ∈ Finset.range (k + 1), (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2) :=
          Finset.sum_le_sum hterm
    _ = s.q (k + 2) ^ 2 - s.q 1 ^ 2 := by
          simpa using Finset.sum_range_sub (fun i => s.q (i + 1) ^ 2) (k + 1)
    _ ≤ 1 := by
          rw [s.q_top]
          nlinarith [sq_nonneg (s.q 1)]

/-- **Uniform lower bound on the finite-step Parisi functional.** -/
theorem parisiFunctional_ge {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    Real.log 2 - β ^ 2 / 4 ≤ parisiFunctional s β h := by
  have hF : 0 ≤ parisiF s β (k + 2) h := parisiF_nonneg s β (k + 2) h
  have hS := sum_correction_le_one s
  have hb : (0 : ℝ) ≤ β ^ 2 / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hS hb
  rw [parisiFunctional]
  linarith

/-- The replica-symmetric scheme with overlap `q`: `k = 0`, `m = (0, 1)`, `q = (0, q, 1)`. -/
noncomputable def rsScheme (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : RSBScheme 0 where
  m := fun p => if p = 0 then 0 else 1
  q := fun p => if p = 0 then 0 else if p = 1 then q else 1
  m_zero := by simp
  m_top := by simp
  m_mono := by
    intro p hp
    have : p = 0 := Nat.le_zero.mp hp
    subst this
    norm_num
  q_zero := by simp
  q_top := by simp
  q_mono := by
    intro p hp
    have hp' : p ≤ 1 := by simpa using hp
    interval_cases p <;> simp [hq0, hq1]

/-- **Target 2a (sanity check: RS case).**  The `0`-step functional is the classical
replica-symmetric formula `log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`.

This lemma guards against off-by-one or normalisation mistakes in the definitions above:
if it is false, the definitions are wrong, not the theorem.

Hand computation to check against (`k = 0`, `m = (0,1)`, `q = (0,q,1)`):
`F_1 = T_{1, β²(1-q)} (log cosh)`, and `∫ cosh(x + σ z) dγ(z) = cosh x · e^{σ²/2}`, so
`F_1(x) = log cosh x + β²(1-q)/2`; then `F_0(h) = E log cosh(h + β√q z) + β²(1-q)/2` and
`𝒫_0 = log 2 + F_0(h) - (β²/4)(1 - q²) = log 2 + E log cosh(β√q z + h) + (β²/4)(1-q)²`. -/
theorem parisiFunctional_rsScheme (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    parisiFunctional (rsScheme q hq0 hq1) β h
      = Real.log 2
        + (∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1))
        + (β ^ 2 / 4) * (1 - q) ^ 2 := by
  classical
  set s := rsScheme q hq0 hq1 with hs
  have hm0 : s.m 0 = 0 := by simp [hs, rsScheme]
  have hm1 : s.m 1 = 1 := by simp [hs, rsScheme]
  have hqq0 : s.q 0 = 0 := by simp [hs, rsScheme]
  have hqq1 : s.q 1 = q := by simp [hs, rsScheme]
  have hqq2 : s.q 2 = 1 := by simp [hs, rsScheme]
  have hv1 : (0:ℝ) ≤ β ^ 2 * (1 - q) := mul_nonneg (sq_nonneg β) (by linarith)
  have hlogcosh_cont : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))
  -- `F₁ = T_{1, β²(1-q)} (log cosh) = log cosh + β²(1-q)/2`
  have hF1 : parisiF s β 1
      = fun x => Real.log (Real.cosh x) + β ^ 2 * (1 - q) / 2 := by
    funext x
    show parisiStep (s.m 1) (β ^ 2 * (s.q 2 - s.q 1)) (parisiF s β 0) x = _
    rw [hm1, hqq2, hqq1, parisiStep, if_neg (one_ne_zero)]
    have hpt : ∀ z : ℝ,
        Real.exp (1 * parisiF s β 0 (x + Real.sqrt (β ^ 2 * (1 - q)) * z))
          = Real.cosh (x + Real.sqrt (β ^ 2 * (1 - q)) * z) := by
      intro z
      show Real.exp (1 * Real.log (Real.cosh _)) = _
      rw [one_mul, Real.exp_log (Real.cosh_pos _)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_cosh_add_mul_stdGaussian x (Real.sqrt (β ^ 2 * (1 - q))),
        Real.sq_sqrt hv1,
        Real.log_mul (ne_of_gt (Real.cosh_pos x)) (Real.exp_ne_zero _),
        Real.log_exp]
    ring
  -- `F₀(h) = ∫ log cosh (h + |β|√q z) dγ + β²(1-q)/2`
  have hsq : Real.sqrt (β ^ 2 * q) = |β| * Real.sqrt q := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have hF0 : parisiF s β 2 h
      = (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
          + β ^ 2 * (1 - q) / 2 := by
    show parisiStep (s.m 0) (β ^ 2 * (s.q 1 - s.q 0)) (parisiF s β 1) h = _
    rw [hm0, hqq1, hqq0, sub_zero, parisiStep, if_pos rfl, hF1, hsq]
    rw [integral_add (integrable_log_cosh_stdGaussian (|β| * Real.sqrt q) h)
        (integrable_const _)]
    simp
  -- the correction sum is `1 * (1 - q²)`
  have hsum : (∑ p ∈ Finset.range (0 + 1),
      s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) = 1 * (1 - q ^ 2) := by
    simp [hm1, hqq1, hqq2]
  -- `|β|√q` and `β√q` agree under the symmetric Gaussian
  have hrefl :
      (∫ z, Real.log (Real.cosh (h + |β| * Real.sqrt q * z)) ∂(gaussianReal 0 1))
        = ∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
    rcases le_or_gt 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.log (Real.cosh (h + β * Real.sqrt q * z))
          = Real.log (Real.cosh (β * Real.sqrt q * z + h))
      rw [add_comm]
    · rw [abs_of_neg hβ]
      have hre := integral_reflect_stdGaussian
        (f := fun y : ℝ => Real.log (Real.cosh y)) hlogcosh_cont (β * Real.sqrt q) h
      rw [show -β * Real.sqrt q = -(β * Real.sqrt q) by ring, ← hre]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show Real.log (Real.cosh (h + β * Real.sqrt q * z))
          = Real.log (Real.cosh (β * Real.sqrt q * z + h))
      rw [add_comm]
  rw [parisiFunctional, hF0, hsum, hrefl]
  ring

/-! ### The `m = 0` boundary of the smoothing operator

`parisiStep` branches at `m = 0`, and Talagrand's admissible sequences (1.6) *allow*
`m_0 = 0` — indeed he notes that equality in (1.6)–(1.7) is exactly what makes the
compactness argument behind (2.17) work.  So the two branches must be reconciled
quantitatively before anything can be said about `𝒫_k` as a function of its parameters.

`parisiStep_zero_sandwich` does that: the `m`-branch sits above the `0`-branch (Jensen) and
overshoots it by at most `m·v/2` (Herbst).  Two features matter downstream:

* the estimate is **uniform in `x`** — the constant involves only the Lipschitz constant of
  `A` and the variance `v`, never `sup |A|` (which is infinite for `log cosh`); and
* it is **linear in `m`**, not `√m`, so it survives summation over the `k+2` levels of the
  recursion with a constant independent of `k`.

Both are consequences of using the sub-Gaussian form of the Herbst bound rather than the
naive `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)`, whose `(log 2)/m` term blows up as `m → 0`.
-/

/--
**The `m`-branch and the `0`-branch of `parisiStep` differ by at most `m·v/2`.**

For `A` 1-Lipschitz of linear growth, `0 < m` and `0 ≤ v`:

  `parisiStep 0 v A x ≤ parisiStep m v A x ≤ parisiStep 0 v A x + m·v/2`,

uniformly in `x`.  The lower bound is Jensen's inequality, the upper bound is the Herbst
sub-Gaussian estimate for the `√v`-Lipschitz function `z ↦ A (x + √v z)`.
-/
theorem parisiStep_zero_sandwich {A : ℝ → ℝ} {m v : ℝ}
    (hm : 0 < m) (hv : 0 ≤ v)
    (hLip : ∀ y y', |A y - A y'| ≤ |y - y'|)
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (x : ℝ) :
    parisiStep 0 v A x ≤ parisiStep m v A x
      ∧ parisiStep m v A x ≤ parisiStep 0 v A x + m * v / 2 := by
  classical
  -- the smoothed function, and the two branches written out
  set f : ℝ → ℝ := fun z => A (x + Real.sqrt v * z) with hf
  have hfmeas : Measurable f := hmeas.comp ((measurable_id.const_mul (Real.sqrt v)).const_add x)
  have hfint : Integrable f (gaussianReal 0 1) := integrable_of_hasLinearGrowth hA hmeas x v
  have hfexp : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1) :=
    integrable_exp_mul_of_hasLinearGrowth hA hmeas m x v
  have hzero : parisiStep 0 v A x = ∫ z, f z ∂(gaussianReal 0 1) := by
    rw [parisiStep, if_pos rfl]
  have hpos : parisiStep m v A x
      = (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1)) := by
    rw [parisiStep, if_neg hm.ne']
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · -- degenerate variance: both branches equal `A x`
    have hfconst : ∀ z : ℝ, f z = A x := by
      intro z
      rw [hf]
      simp [← hv0]
    have h0 : parisiStep 0 v A x = A x := by
      rw [hzero]
      rw [show (∫ z, f z ∂(gaussianReal 0 1)) = ∫ _z : ℝ, A x ∂(gaussianReal 0 1) from
        integral_congr_ae (Filter.Eventually.of_forall hfconst)]
      simp
    have hm' : parisiStep m v A x = A x := by
      rw [hpos]
      rw [show (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
            = ∫ _z : ℝ, Real.exp (m * A x) ∂(gaussianReal 0 1) from
        integral_congr_ae (Filter.Eventually.of_forall (fun z => by
          show Real.exp (m * f z) = Real.exp (m * A x)
          rw [hfconst z]))]
      rw [integral_const, probReal_univ, one_smul, Real.log_exp]
      field_simp
    rw [h0, hm', ← hv0]
    constructor
    · exact le_rfl
    · simp
  · -- non-degenerate: Jensen below, Herbst above
    have hsq : Real.sqrt v > 0 := Real.sqrt_pos.2 hvpos
    have hLipf : LipschitzWith (Real.sqrt v).toNNReal f := by
      refine LipschitzWith.of_dist_le_mul (fun z z' => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg v)]
      have h := hLip (x + Real.sqrt v * z) (x + Real.sqrt v * z')
      rwa [show (x + Real.sqrt v * z) - (x + Real.sqrt v * z')
            = Real.sqrt v * (z - z') by ring,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)] at h
    have hlow := SpinGlass.integral_le_inv_mul_log_integral_exp (f := f) hm hfint hfexp
    have hhigh := SpinGlass.inv_mul_log_integral_exp_le (f := f) (L := Real.sqrt v)
      hm hsq hLipf hfmeas hfexp
    rw [Real.sq_sqrt hv] at hhigh
    refine ⟨?_, ?_⟩
    · rw [hzero, hpos]; exact hlow
    · rw [hzero, hpos]
      calc (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
          ≤ (∫ z, f z ∂(gaussianReal 0 1)) + m * v / 2 := hhigh

/-! ### Target 2b, split

Reading Talagrand's Annals paper directly (see `docs/ROADMAP.md`) shows that the parameter
regularity his proof consumes is **not** a Lipschitz estimate.  Immediately after (1.13) he
declines that viewpoint:

> "Guerra proves that this definition can be extended by a continuity argument to any
> probability measure µ on [0,1] … *We do not adopt this point of view since an essential
> ingredient of our approach is that we need only consider discrete objects rather than
> continuous ones.*"

What he uses instead is (2.17) — that the infimum defining `𝒫` is *attained* — obtained "by
a compactness argument", and he remarks that allowing equality in (1.6)–(1.7) is precisely
what makes that argument available.  Section 5 then works with partial derivatives of the
functional **at** that minimiser.

So the target splits:

* `exists_minimizer_parisiFunctional` (**2b-i**) — Talagrand's (2.17).  On the critical path
  to Target 4.  Needs only continuity of `𝒫_k` in `(m,q)` for *fixed* `k`: no modulus, no
  uniformity in `k`.
* `parisiFunctional_lipschitz` (**2b-ii**) — Guerra's uniform-in-`k` Lipschitz bound, needed
  to pass from discrete schemes to general Parisi measures.  Kept, but **off** the critical
  path for the Talagrand route.

### The parameter space

`RSBScheme k` bundles `m q : ℕ → ℝ` with the constraints, but the *set* of schemes is not
compact: `m p` for `p ≥ k + 2` is entirely unconstrained.  The functional never reads those
values, so we work instead with raw parameter pairs `(m, q) : (ℕ → ℝ) × (ℕ → ℝ)` and the set
`admissible k` of pairs that satisfy the constraints **and** take values in `[0,1]`
everywhere.  That set is a closed subset of a product of copies of `[0,1]`, hence compact by
Tychonoff, and this is exactly the compactness Talagrand invokes: it is closed because
(1.6)–(1.7) use `≤` rather than `<`.
-/

namespace RSBScheme

variable {k : ℕ} (s : RSBScheme k)

lemma m_nonneg {p : ℕ} (hp : p ≤ k + 1) : 0 ≤ s.m p := by
  have h := s.m_mono' p hp 0 (Nat.zero_le p)
  rwa [s.m_zero] at h

lemma q_le_one {p : ℕ} (hp : p ≤ k + 2) : s.q p ≤ 1 := by
  have h := s.q_mono' (k + 2) le_rfl p hp
  rwa [s.q_top] at h

end RSBScheme

/-- `parisiF` with the scheme's two sequences supplied as bare functions.  Definitionally
the same recursion; only the packaging differs, so that the parameters can be varied
continuously without carrying the `RSBScheme` proof fields around. -/
noncomputable def parisiFRaw (k : ℕ) (m q : ℕ → ℝ) (β : ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun x => Real.log (Real.cosh x)
  | j + 1 =>
      parisiStep (m (k + 1 - j)) (β ^ 2 * (q (k + 2 - j) - q (k + 1 - j)))
        (parisiFRaw k m q β j)

/-- `parisiFunctional` on bare parameter sequences. -/
noncomputable def parisiFunctionalRaw (k : ℕ) (m q : ℕ → ℝ) (β h : ℝ) : ℝ :=
  Real.log 2 + parisiFRaw k m q β (k + 2) h
    - (β ^ 2 / 4) * ∑ p ∈ Finset.range (k + 1), m (p + 1) * (q (p + 2) ^ 2 - q (p + 1) ^ 2)

theorem parisiF_eq_raw {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    parisiF s β j = parisiFRaw k s.m s.q β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show parisiStep (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
            (parisiF s β j)
          = parisiStep (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))
            (parisiFRaw k s.m s.q β j)
      rw [ih]

theorem parisiFunctional_eq_raw {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    parisiFunctional s β h = parisiFunctionalRaw k s.m s.q β h := by
  rw [parisiFunctional, parisiFunctionalRaw, parisiF_eq_raw]

/-- The recursion reads `m` only at indices `≤ k + 1` and `q` only at indices `≤ k + 2`. -/
theorem parisiFRaw_congr {k : ℕ} {m m' q q' : ℕ → ℝ} (β : ℝ)
    (hm : ∀ p, p ≤ k + 1 → m p = m' p) (hq : ∀ p, p ≤ k + 2 → q p = q' p) (j : ℕ) :
    parisiFRaw k m q β j = parisiFRaw k m' q' β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show parisiStep (m (k + 1 - j)) (β ^ 2 * (q (k + 2 - j) - q (k + 1 - j)))
            (parisiFRaw k m q β j)
          = parisiStep (m' (k + 1 - j)) (β ^ 2 * (q' (k + 2 - j) - q' (k + 1 - j)))
            (parisiFRaw k m' q' β j)
      rw [ih, hm _ (by omega), hq _ (by omega), hq _ (by omega)]

theorem parisiFunctionalRaw_congr {k : ℕ} {m m' q q' : ℕ → ℝ} (β h : ℝ)
    (hm : ∀ p, p ≤ k + 1 → m p = m' p) (hq : ∀ p, p ≤ k + 2 → q p = q' p) :
    parisiFunctionalRaw k m q β h = parisiFunctionalRaw k m' q' β h := by
  have hsum : (∑ p ∈ Finset.range (k + 1), m (p + 1) * (q (p + 2) ^ 2 - q (p + 1) ^ 2))
      = ∑ p ∈ Finset.range (k + 1), m' (p + 1) * (q' (p + 2) ^ 2 - q' (p + 1) ^ 2) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_range] at hp
    rw [hm (p + 1) (by omega), hq (p + 2) (by omega), hq (p + 1) (by omega)]
  rw [parisiFunctionalRaw, parisiFunctionalRaw, parisiFRaw_congr β hm hq (k + 2), hsum]

/--
**The admissible parameter set.**  Talagrand's (1.6)–(1.7), together with the (automatic)
containment of all values in `[0,1]`, which is what makes the set bounded.
-/
def admissible (k : ℕ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {p | (∀ n : ℕ, 0 ≤ p.1 n) ∧ (∀ n : ℕ, p.1 n ≤ 1)
     ∧ (∀ n : ℕ, 0 ≤ p.2 n) ∧ (∀ n : ℕ, p.2 n ≤ 1)
     ∧ p.1 0 = 0 ∧ p.1 (k + 1) = 1
     ∧ (∀ j : Fin (k + 1), p.1 (j : ℕ) ≤ p.1 ((j : ℕ) + 1))
     ∧ p.2 0 = 0 ∧ p.2 (k + 2) = 1
     ∧ (∀ j : Fin (k + 2), p.2 (j : ℕ) ≤ p.2 ((j : ℕ) + 1))}

theorem isClosed_admissible (k : ℕ) : IsClosed (admissible k) := by
  have hc1 : ∀ n : ℕ, Continuous fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 n :=
    fun n => (continuous_apply n).comp continuous_fst
  have hc2 : ∀ n : ℕ, Continuous fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 n :=
    fun n => (continuous_apply n).comp continuous_snd
  have key : admissible k =
      ((((((((((⋂ n : ℕ, {p : (ℕ → ℝ) × (ℕ → ℝ) | 0 ≤ p.1 n}) ∩
      (⋂ n : ℕ, {p : (ℕ → ℝ) × (ℕ → ℝ) | p.1 n ≤ 1})) ∩
      (⋂ n : ℕ, {p : (ℕ → ℝ) × (ℕ → ℝ) | 0 ≤ p.2 n})) ∩
      (⋂ n : ℕ, {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 n ≤ 1})) ∩
      {p : (ℕ → ℝ) × (ℕ → ℝ) | p.1 0 = 0}) ∩
      {p : (ℕ → ℝ) × (ℕ → ℝ) | p.1 (k + 1) = 1}) ∩
      (⋂ j : Fin (k + 1), {p : (ℕ → ℝ) × (ℕ → ℝ) | p.1 (j : ℕ) ≤ p.1 ((j : ℕ) + 1)})) ∩
      {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 0 = 0}) ∩
      {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 (k + 2) = 1}) ∩
      (⋂ j : Fin (k + 2), {p : (ℕ → ℝ) × (ℕ → ℝ) | p.2 (j : ℕ) ≤ p.2 ((j : ℕ) + 1)})) := by
    ext p
    simp only [admissible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    tauto
  rw [key]
  repeat' apply IsClosed.inter
  · exact isClosed_iInter fun n => isClosed_le continuous_const (hc1 n)
  · exact isClosed_iInter fun n => isClosed_le (hc1 n) continuous_const
  · exact isClosed_iInter fun n => isClosed_le continuous_const (hc2 n)
  · exact isClosed_iInter fun n => isClosed_le (hc2 n) continuous_const
  · exact isClosed_eq (hc1 0) continuous_const
  · exact isClosed_eq (hc1 (k + 1)) continuous_const
  · exact isClosed_iInter fun j => isClosed_le (hc1 _) (hc1 _)
  · exact isClosed_eq (hc2 0) continuous_const
  · exact isClosed_eq (hc2 (k + 2)) continuous_const
  · exact isClosed_iInter fun j => isClosed_le (hc2 _) (hc2 _)

/-- **Tychonoff.**  The admissible set is compact — this is the compactness Talagrand
invokes for (2.17), and it works precisely because (1.6)–(1.7) allow equality, making the
constraint set closed. -/
theorem isCompact_admissible (k : ℕ) : IsCompact (admissible k) := by
  have hbox : IsCompact
      ((Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) 1)
        ×ˢ (Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset (isClosed_admissible k) ?_
  rintro p ⟨h1, h2, h3, h4, -⟩
  exact ⟨fun n _ => ⟨h1 n, h2 n⟩, fun n _ => ⟨h3 n, h4 n⟩⟩

/-- Every scheme, with its parameters clamped past the range the functional reads. -/
noncomputable def RSBScheme.toPair {k : ℕ} (s : RSBScheme k) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun n => s.m (min n (k + 1)), fun n => s.q (min n (k + 2)))

theorem RSBScheme.toPair_mem {k : ℕ} (s : RSBScheme k) : s.toPair ∈ admissible k := by
  refine ⟨fun n => s.m_nonneg (min_le_right _ _), fun n => s.m_le_one (min_le_right _ _),
    fun n => s.q_nonneg (min_le_right _ _), fun n => s.q_le_one (min_le_right _ _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.m (min 0 (k + 1)) = 0
    rw [Nat.min_eq_left (Nat.zero_le _)]; exact s.m_zero
  · show s.m (min (k + 1) (k + 1)) = 1
    rw [min_self]; exact s.m_top
  · intro j
    show s.m (min (j : ℕ) (k + 1)) ≤ s.m (min ((j : ℕ) + 1) (k + 1))
    rw [Nat.min_eq_left (by omega : (j : ℕ) ≤ k + 1),
      Nat.min_eq_left (by omega : (j : ℕ) + 1 ≤ k + 1)]
    exact s.m_mono _ (by omega)
  · show s.q (min 0 (k + 2)) = 0
    rw [Nat.min_eq_left (Nat.zero_le _)]; exact s.q_zero
  · show s.q (min (k + 2) (k + 2)) = 1
    rw [min_self]; exact s.q_top
  · intro j
    show s.q (min (j : ℕ) (k + 2)) ≤ s.q (min ((j : ℕ) + 1) (k + 2))
    rw [Nat.min_eq_left (by omega : (j : ℕ) ≤ k + 2),
      Nat.min_eq_left (by omega : (j : ℕ) + 1 ≤ k + 2)]
    exact s.q_mono _ (by omega)

theorem parisiFunctional_eq_raw_toPair {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    parisiFunctional s β h = parisiFunctionalRaw k s.toPair.1 s.toPair.2 β h := by
  rw [parisiFunctional_eq_raw]
  refine parisiFunctionalRaw_congr β h (fun p hp => ?_) (fun p hp => ?_)
  · show s.m p = s.m (min p (k + 1))
    rw [Nat.min_eq_left hp]
  · show s.q p = s.q (min p (k + 2))
    rw [Nat.min_eq_left hp]

/-- Conversely, an admissible pair *is* a scheme. -/
noncomputable def schemeOfPair {k : ℕ} (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : p ∈ admissible k) :
    RSBScheme k where
  m := p.1
  q := p.2
  m_zero := hp.2.2.2.2.1
  m_top := hp.2.2.2.2.2.1
  m_mono := fun j hj => hp.2.2.2.2.2.2.1 ⟨j, by omega⟩
  q_zero := hp.2.2.2.2.2.2.2.1
  q_top := hp.2.2.2.2.2.2.2.2.1
  q_mono := fun j hj => hp.2.2.2.2.2.2.2.2.2 ⟨j, by omega⟩

@[simp] theorem schemeOfPair_m {k : ℕ} (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : p ∈ admissible k) :
    (schemeOfPair p hp).m = p.1 := rfl

@[simp] theorem schemeOfPair_q {k : ℕ} (p : (ℕ → ℝ) × (ℕ → ℝ)) (hp : p ∈ admissible k) :
    (schemeOfPair p hp).q = p.2 := rfl

/-- A scheme exists for every `k`, so the admissible set is non-empty. -/
noncomputable def trivialScheme (k : ℕ) : RSBScheme k where
  m := fun p => if p = 0 then 0 else 1
  q := fun p => if p = 0 then 0 else 1
  m_zero := by simp
  m_top := by simp
  m_mono := by
    intro p _
    simp only [Nat.succ_ne_zero, if_false]
    split <;> norm_num
  q_zero := by simp
  q_top := by simp
  q_mono := by
    intro p _
    simp only [Nat.succ_ne_zero, if_false]
    split <;> norm_num

theorem admissible_nonempty (k : ℕ) : (admissible k).Nonempty :=
  ⟨(trivialScheme k).toPair, (trivialScheme k).toPair_mem⟩

/-! ### Uniform bounds over the admissible set

The continuity argument integrates `exp (m_p · F_j(p)(x + √v_p z))` and lets `p` vary, so it
needs a dominating function valid for **every** admissible `p` at once.  Since `k` is fixed
this bound may depend on `k` — 2b-i, unlike 2b-ii, requires no uniformity in `k`.

Every level is `1`-Lipschitz (`parisiF_props`, inherited by `parisiFRaw` through
`schemeOfPair`), so `|F_j(y)| ≤ F_j(0) + |y|` and only `F_j(0)` needs a uniform bound.  One
smoothing step moves the value at `0` by at most `√v · ∫|z| + m v / 2`: the first term is
`1`-Lipschitzness, the second is the `m = 0` sandwich.  With `m ≤ 1` and `v ≤ β²` that is
`|β| ∫|z| + β²/2` per level, so `F_j(0) ≤ j (|β| ∫|z| + β²/2)`.
-/

/-- One smoothing step moves the value at `x` up by at most `√v ∫|z| + m v / 2`. -/
theorem parisiStep_zero_apply_le {A : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hLip : ∀ y y', |A y - A y'| ≤ |y - y'|) (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (x : ℝ) :
    parisiStep 0 v A x ≤ A x + Real.sqrt v * gAbsMoment := by
  rw [parisiStep, if_pos rfl]
  have hint : Integrable (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth hA hmeas x v
  have hbd : Integrable (fun z : ℝ => A x + Real.sqrt v * |z|) (gaussianReal 0 1) :=
    (integrable_const (A x)).add (integrable_abs_stdGaussian.const_mul _)
  have hmono : ∀ z : ℝ, A (x + Real.sqrt v * z) ≤ A x + Real.sqrt v * |z| := by
    intro z
    have h := hLip (x + Real.sqrt v * z) x
    rw [show (x + Real.sqrt v * z) - x = Real.sqrt v * z by ring, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg v)] at h
    have h2 := (abs_le.1 h).2
    linarith
  calc (∫ z, A (x + Real.sqrt v * z) ∂(gaussianReal 0 1))
      ≤ ∫ z, (A x + Real.sqrt v * |z|) ∂(gaussianReal 0 1) := integral_mono hint hbd hmono
    _ = A x + Real.sqrt v * gAbsMoment := by
        rw [integral_add (integrable_const _) (integrable_abs_stdGaussian.const_mul _),
          integral_const, probReal_univ, one_smul, integral_const_mul, gAbsMoment]

theorem parisiStep_apply_le {A : ℝ → ℝ} {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (hLip : ∀ y y', |A y - A y'| ≤ |y - y'|) (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (x : ℝ) :
    parisiStep m v A x ≤ A x + Real.sqrt v * gAbsMoment + m * v / 2 := by
  have h0 := parisiStep_zero_apply_le hv hLip hA hmeas x
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · have hmz : m = 0 := hm0.symm
    subst hmz
    nlinarith
  · have hs := (parisiStep_zero_sandwich hmpos hv hLip hA hmeas x).2
    linarith

/-- The three structural properties of every level, transported to `parisiFRaw` for an
admissible parameter pair. -/
theorem parisiFRaw_props_of_admissible {k : ℕ} (β : ℝ) {p : (ℕ → ℝ) × (ℕ → ℝ)}
    (hp : p ∈ admissible k) (j : ℕ) :
    Measurable (parisiFRaw k p.1 p.2 β j)
      ∧ HasLinearGrowth (parisiFRaw k p.1 p.2 β j)
      ∧ ∀ x x', |parisiFRaw k p.1 p.2 β j x - parisiFRaw k p.1 p.2 β j x'| ≤ |x - x'| := by
  have h := parisiF_props (schemeOfPair p hp) β j
  rwa [parisiF_eq_raw] at h

/-- The `m`-parameter read at level `j` lies in `[0,1]`. -/
theorem admissible_m_mem {k : ℕ} {p : (ℕ → ℝ) × (ℕ → ℝ)} (hp : p ∈ admissible k) (i : ℕ) :
    0 ≤ p.1 i ∧ p.1 i ≤ 1 := ⟨hp.1 i, hp.2.1 i⟩

/-- The variance read at level `j` lies in `[0, β²]`. -/
theorem admissible_var_mem {k : ℕ} {β : ℝ} {p : (ℕ → ℝ) × (ℕ → ℝ)} (hp : p ∈ admissible k)
    {j : ℕ} (hj : j ≤ k + 1) :
    0 ≤ β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))
      ∧ β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)) ≤ β ^ 2 := by
  have hidx : k + 2 - j = (k + 1 - j) + 1 := by omega
  have hmono : p.2 (k + 1 - j) ≤ p.2 ((k + 1 - j) + 1) :=
    hp.2.2.2.2.2.2.2.2.2 ⟨k + 1 - j, by omega⟩
  rw [hidx]
  have hle : p.2 ((k + 1 - j) + 1) ≤ 1 := hp.2.2.2.1 _
  have hge : 0 ≤ p.2 (k + 1 - j) := hp.2.2.1 _
  have hsq : (0 : ℝ) ≤ β ^ 2 := sq_nonneg β
  constructor
  · exact mul_nonneg hsq (by linarith)
  · nlinarith

/-- **Uniform bound on the value at `0`, over the whole admissible set.** -/
theorem parisiFRaw_zero_le {k : ℕ} {β : ℝ} {p : (ℕ → ℝ) × (ℕ → ℝ)} (hp : p ∈ admissible k) :
    ∀ j, j ≤ k + 2 → parisiFRaw k p.1 p.2 β j 0 ≤ j * (|β| * gAbsMoment + β ^ 2 / 2) := by
  intro j
  induction j with
  | zero =>
      intro _
      show Real.log (Real.cosh 0) ≤ _
      rw [Real.cosh_zero, Real.log_one]
      norm_num
  | succ j ih =>
      intro hj
      have hj' : j ≤ k + 1 := by omega
      have hj'' : j ≤ k + 2 := by omega
      obtain ⟨hmeas, hgrow, hlip⟩ := parisiFRaw_props_of_admissible β hp j
      obtain ⟨hm0, hm1⟩ := admissible_m_mem hp (k + 1 - j)
      obtain ⟨hv0, hv1⟩ := admissible_var_mem (β := β) hp hj'
      have hstep := parisiStep_apply_le (A := parisiFRaw k p.1 p.2 β j)
        (m := p.1 (k + 1 - j)) (v := β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
        hm0 hv0 hlip hgrow hmeas 0
      have hsqrt : Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) ≤ |β| := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hv1
      have hgm : 0 ≤ gAbsMoment := gAbsMoment_nonneg
      have hih := ih hj''
      have hmv : p.1 (k + 1 - j) * (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) / 2
          ≤ β ^ 2 / 2 := by nlinarith
      show parisiStep (p.1 (k + 1 - j)) (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
          (parisiFRaw k p.1 p.2 β j) 0 ≤ _
      have hcast : ((j : ℝ) + 1) * (|β| * gAbsMoment + β ^ 2 / 2)
          = (j : ℝ) * (|β| * gAbsMoment + β ^ 2 / 2) + (|β| * gAbsMoment + β ^ 2 / 2) := by
        ring
      push_cast
      rw [hcast]
      nlinarith [mul_le_mul_of_nonneg_right hsqrt hgm]

/-- **Uniform linear growth over the admissible set.** -/
theorem parisiFRaw_abs_le {k : ℕ} {β : ℝ} {p : (ℕ → ℝ) × (ℕ → ℝ)} (hp : p ∈ admissible k)
    {j : ℕ} (hj : j ≤ k + 2) (y : ℝ) :
    |parisiFRaw k p.1 p.2 β j y| ≤ (k + 2) * (|β| * gAbsMoment + β ^ 2 / 2) + |y| := by
  obtain ⟨-, -, hlip⟩ := parisiFRaw_props_of_admissible β hp j
  have hnn : 0 ≤ parisiFRaw k p.1 p.2 β j 0 := by
    have h := parisiF_nonneg (schemeOfPair p hp) β j 0
    rwa [parisiF_eq_raw] at h
  have hle := parisiFRaw_zero_le (β := β) hp j hj
  have hstep := hlip y 0
  rw [sub_zero] at hstep
  have hmono : (j : ℝ) * (|β| * gAbsMoment + β ^ 2 / 2)
      ≤ (k + 2) * (|β| * gAbsMoment + β ^ 2 / 2) := by
    have hc : (0 : ℝ) ≤ |β| * gAbsMoment + β ^ 2 / 2 := by
      have := gAbsMoment_nonneg
      positivity
    have hjr : (j : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast hj
    nlinarith
  have habs : |parisiFRaw k p.1 p.2 β j y|
      ≤ |parisiFRaw k p.1 p.2 β j 0| + |y| := by
    have := abs_sub_abs_le_abs_sub (parisiFRaw k p.1 p.2 β j y) (parisiFRaw k p.1 p.2 β j 0)
    linarith [hstep]
  rw [abs_of_nonneg hnn] at habs
  linarith

/-! ### Continuity of each level in the parameters

The induction propagates, over `j`, the statement

  `∀ y, ContinuousWithinAt (fun p => parisiFRaw k p.1 p.2 β j y) (admissible k) p₀`

— continuity at each *fixed* evaluation point `y`.  The step has to evaluate level `j` at the
*moving* point `y + √(v p) z`, and equi-Lipschitzness bridges the two:

  `|F_j(p)(y + √(v p) z) - F_j(p₀)(y + √(v p₀) z)|`
      `≤ |√(v p) - √(v p₀)|·|z| + |F_j(p)(w₀) - F_j(p₀)(w₀)|`,  `w₀ = y + √(v p₀) z`,

whose first term vanishes because `p ↦ √(v p)` is continuous and whose second vanishes by the
induction hypothesis at the fixed point `w₀`.  Dominated convergence along the filter
`𝓝[admissible k] p₀` (countably generated, the ambient space being second countable) then
moves the limit through the integral, dominated by `parisiFRaw_abs_le`.

The `m = 0` branch point of `parisiStep` is handled by splitting on `m p₀`:

* `m p₀ > 0` — nearby parameters also have `m p > 0`, both sides take the `else` branch, and
  the result is dominated convergence followed by continuity of `log` and of `t ↦ 1/t` away
  from `0`;
* `m p₀ = 0` — nearby `m p` may be either, so we compare against the `0`-branch at the *same*
  `p` using `parisiStep_zero_sandwich`, whose gap `m p · v p / 2` vanishes since `m p → 0`.
-/

/-- **Each level of the recursion is continuous in the parameters.** -/
theorem continuousWithinAt_parisiFRaw {k : ℕ} (β : ℝ) {p₀ : (ℕ → ℝ) × (ℕ → ℝ)}
    (hp₀ : p₀ ∈ admissible k) :
    ∀ j, j ≤ k + 2 → ∀ y : ℝ,
      ContinuousWithinAt (fun p => parisiFRaw k p.1 p.2 β j y) (admissible k) p₀ := by
  classical
  set Bk : ℝ := (k + 2 : ℝ) * (|β| * gAbsMoment + β ^ 2 / 2) with hBk
  have hcoord1 : ∀ i : ℕ,
      ContinuousWithinAt (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i) (admissible k) p₀ :=
    fun i => (((continuous_apply i).comp continuous_fst).continuousAt).continuousWithinAt
  have hcoord2 : ∀ i : ℕ,
      ContinuousWithinAt (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i) (admissible k) p₀ :=
    fun i => (((continuous_apply i).comp continuous_snd).continuousAt).continuousWithinAt
  intro j
  induction j with
  | zero => intro _ y; exact continuousWithinAt_const
  | succ j ih =>
      intro hj y
      have hj' : j ≤ k + 1 := by omega
      have hj'' : j ≤ k + 2 := by omega
      have ihj := ih hj''
      -- the two parameters read at this level
      have hm : ContinuousWithinAt (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 (k + 1 - j))
          (admissible k) p₀ := hcoord1 _
      have hv : ContinuousWithinAt
          (fun p : (ℕ → ℝ) × (ℕ → ℝ) => β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
          (admissible k) p₀ :=
        continuousWithinAt_const.mul ((hcoord2 _).sub (hcoord2 _))
      have hsq : ContinuousWithinAt
          (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
            Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))) (admissible k) p₀ :=
        (Real.continuous_sqrt.continuousAt).comp_continuousWithinAt hv
      -- `√v ≤ |β|` on the admissible set
      have hsqle : ∀ p ∈ admissible k,
          Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) ≤ |β| := by
        intro p hp
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (admissible_var_mem (β := β) hp hj').2
      -- **the moving-point pointwise limit**
      have hptw : ∀ z : ℝ, Filter.Tendsto
          (fun p : (ℕ → ℝ) × (ℕ → ℝ) => parisiFRaw k p.1 p.2 β j
            (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z))
          (𝓝[admissible k] p₀)
          (𝓝 (parisiFRaw k p₀.1 p₀.2 β j
            (y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z))) := by
        intro z
        set w₀ : ℝ := y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z with hw₀
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero' (g := fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
            |Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
              - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))| * |z|
            + |parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀|)
          (Filter.Eventually.of_forall fun p => dist_nonneg) ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with p hp
          obtain ⟨-, -, hlip⟩ := parisiFRaw_props_of_admissible β hp j
          have hstep := hlip
            (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z) w₀
          have harg : (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z) - w₀
              = (Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                  - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))) * z := by
            rw [hw₀]; ring
          rw [harg, abs_mul] at hstep
          rw [Real.dist_eq]
          calc |parisiFRaw k p.1 p.2 β j
                  (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                - parisiFRaw k p₀.1 p₀.2 β j w₀|
              ≤ |parisiFRaw k p.1 p.2 β j
                    (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                  - parisiFRaw k p.1 p.2 β j w₀|
                + |parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀| := by
                have := abs_sub_abs_le_abs_sub
                  (parisiFRaw k p.1 p.2 β j
                    (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                    - parisiFRaw k p.1 p.2 β j w₀)
                  (parisiFRaw k p₀.1 p₀.2 β j w₀ - parisiFRaw k p.1 p.2 β j w₀)
                have h2 := abs_sub (parisiFRaw k p.1 p.2 β j
                    (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                    - parisiFRaw k p.1 p.2 β j w₀)
                  (parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀)
                calc |parisiFRaw k p.1 p.2 β j
                        (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                      - parisiFRaw k p₀.1 p₀.2 β j w₀|
                    = |(parisiFRaw k p.1 p.2 β j
                        (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                        - parisiFRaw k p.1 p.2 β j w₀)
                      + (parisiFRaw k p.1 p.2 β j w₀
                        - parisiFRaw k p₀.1 p₀.2 β j w₀)| := by ring_nf
                  _ ≤ _ := abs_add_le _ _
            _ ≤ |Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                  - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))| * |z|
                + |parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀| := by
                linarith [hstep]
        · have h1 : Filter.Tendsto
              (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
                |Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                  - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))| * |z|)
              (𝓝[admissible k] p₀) (𝓝 0) := by
            have hs : Filter.Tendsto
                (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
                  |Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                    - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))|)
                (𝓝[admissible k] p₀)
                (𝓝 |Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))
                    - Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))|) :=
              ((hsq.sub continuousWithinAt_const).abs).tendsto
            rw [sub_self, abs_zero] at hs
            simpa using hs.mul_const |z|
          have h2 : Filter.Tendsto
              (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
                |parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀|)
              (𝓝[admissible k] p₀) (𝓝 0) := by
            have hs : Filter.Tendsto
                (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
                  |parisiFRaw k p.1 p.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀|)
                (𝓝[admissible k] p₀)
                (𝓝 |parisiFRaw k p₀.1 p₀.2 β j w₀ - parisiFRaw k p₀.1 p₀.2 β j w₀|) :=
              (((ihj w₀).sub continuousWithinAt_const).abs).tendsto
            rwa [sub_self, abs_zero] at hs
          simpa using h1.add h2
      -- **the dominating bound**
      have hbnd : ∀ p ∈ admissible k, ∀ z : ℝ,
          |parisiFRaw k p.1 p.2 β j
            (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)|
            ≤ (Bk + |y|) + |β| * |z| := by
        intro p hp z
        have habs := parisiFRaw_abs_le (β := β) hp hj''
          (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
        have hsplit : |y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z|
            ≤ |y| + |β| * |z| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have := hsqle p hp
          nlinarith [abs_nonneg z]
        calc |parisiFRaw k p.1 p.2 β j
              (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)|
            ≤ Bk + |y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z| := habs
          _ ≤ (Bk + |y|) + |β| * |z| := by linarith
      have hbound_lin : Integrable (fun z : ℝ => (Bk + |y|) + |β| * |z|) (gaussianReal 0 1) :=
        (integrable_const _).add (integrable_abs_stdGaussian.const_mul _)
      have hbound_exp :
          Integrable (fun z : ℝ => Real.exp ((Bk + |y|) + |β| * |z|)) (gaussianReal 0 1) := by
        refine ((integrable_exp_abs_mul_stdGaussian |β|).const_mul
          (Real.exp (Bk + |y|))).congr ?_
        filter_upwards with z
        show Real.exp (Bk + |y|) * Real.exp (|β| * |z|) = Real.exp ((Bk + |y|) + |β| * |z|)
        rw [← Real.exp_add]
      -- **the `m = 0` branch integral converges**
      have h0branch : Filter.Tendsto
          (fun p : (ℕ → ℝ) × (ℕ → ℝ) => ∫ z, parisiFRaw k p.1 p.2 β j
            (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
            ∂(gaussianReal 0 1))
          (𝓝[admissible k] p₀)
          (𝓝 (∫ z, parisiFRaw k p₀.1 p₀.2 β j
            (y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z)
            ∂(gaussianReal 0 1))) := by
        refine tendsto_integral_filter_of_dominated_convergence
          (fun z => (Bk + |y|) + |β| * |z|) ?_ ?_ hbound_lin
          (Filter.Eventually.of_forall hptw)
        · filter_upwards [self_mem_nhdsWithin] with p hp
          obtain ⟨hmeas, -, -⟩ := parisiFRaw_props_of_admissible β hp j
          exact (hmeas.comp ((measurable_id.const_mul _).const_add y)).aestronglyMeasurable
        · filter_upwards [self_mem_nhdsWithin] with p hp
          filter_upwards with z
          rw [Real.norm_eq_abs]
          exact hbnd p hp z
      show ContinuousWithinAt
        (fun p => parisiStep (p.1 (k + 1 - j))
          (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
          (parisiFRaw k p.1 p.2 β j) y) (admissible k) p₀
      by_cases hm0 : p₀.1 (k + 1 - j) = 0
      · -- **Case B: the base parameter sits on the branch point**
        have hzero : parisiStep (p₀.1 (k + 1 - j))
            (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j)))
            (parisiFRaw k p₀.1 p₀.2 β j) y
            = ∫ z, parisiFRaw k p₀.1 p₀.2 β j
              (y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z)
              ∂(gaussianReal 0 1) := by
          rw [parisiStep, if_pos hm0]
        -- the gap between the two branches at the same parameter
        have hgap : ∀ᶠ p in 𝓝[admissible k] p₀,
            |parisiStep (p.1 (k + 1 - j)) (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                (parisiFRaw k p.1 p.2 β j) y
              - ∫ z, parisiFRaw k p.1 p.2 β j
                  (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                  ∂(gaussianReal 0 1)|
              ≤ p.1 (k + 1 - j) * (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) / 2 := by
          filter_upwards [self_mem_nhdsWithin] with p hp
          obtain ⟨hmeas, hgrow, hlip⟩ := parisiFRaw_props_of_admissible β hp j
          obtain ⟨hmA, hmB⟩ := admissible_m_mem hp (k + 1 - j)
          obtain ⟨hvA, -⟩ := admissible_var_mem (β := β) hp hj'
          have hrw : (∫ z, parisiFRaw k p.1 p.2 β j
              (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
              ∂(gaussianReal 0 1))
              = parisiStep 0 (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                (parisiFRaw k p.1 p.2 β j) y := by
            rw [parisiStep, if_pos rfl]
          rw [hrw]
          rcases eq_or_lt_of_le hmA with hz | hpos
          · rw [← hz]
            simp
          · have hs := parisiStep_zero_sandwich hpos hvA hlip hgrow hmeas y
            rw [abs_le]
            constructor
            · nlinarith [hs.1, mul_nonneg hmA hvA]
            · linarith [hs.2]
        have hgapzero : Filter.Tendsto
            (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
              p.1 (k + 1 - j) * (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) / 2)
            (𝓝[admissible k] p₀) (𝓝 0) := by
          have h2 : Filter.Tendsto
              (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
                p.1 (k + 1 - j) * (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) / 2)
              (𝓝[admissible k] p₀)
              (𝓝 (p₀.1 (k + 1 - j) * (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) / 2)) :=
            (hm.tendsto.mul hv.tendsto).div_const 2
          rwa [hm0, zero_mul, zero_div] at h2
        have hdiff : Filter.Tendsto
            (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
              parisiStep (p.1 (k + 1 - j)) (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j)))
                (parisiFRaw k p.1 p.2 β j) y
              - ∫ z, parisiFRaw k p.1 p.2 β j
                  (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)
                  ∂(gaussianReal 0 1))
            (𝓝[admissible k] p₀) (𝓝 0) := by
          rw [tendsto_zero_iff_abs_tendsto_zero]
          exact squeeze_zero' (Filter.Eventually.of_forall fun p => abs_nonneg _) hgap hgapzero
        have := hdiff.add h0branch
        rw [zero_add] at this
        rw [ContinuousWithinAt, hzero]
        simpa using this
      · -- **Case A: the base parameter is off the branch point**
        have hmpos : 0 < p₀.1 (k + 1 - j) := lt_of_le_of_ne (hp₀.1 _) (Ne.symm hm0)
        have hposev : ∀ᶠ p in 𝓝[admissible k] p₀, 0 < p.1 (k + 1 - j) :=
          Filter.Tendsto.eventually_const_lt hmpos hm
        -- both sides take the `else` branch
        have hexpint : Filter.Tendsto
            (fun p : (ℕ → ℝ) × (ℕ → ℝ) => ∫ z, Real.exp (p.1 (k + 1 - j) *
              parisiFRaw k p.1 p.2 β j
                (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z))
              ∂(gaussianReal 0 1))
            (𝓝[admissible k] p₀)
            (𝓝 (∫ z, Real.exp (p₀.1 (k + 1 - j) *
              parisiFRaw k p₀.1 p₀.2 β j
                (y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z))
              ∂(gaussianReal 0 1))) := by
          refine tendsto_integral_filter_of_dominated_convergence
            (fun z => Real.exp ((Bk + |y|) + |β| * |z|)) ?_ ?_ hbound_exp ?_
          · filter_upwards [self_mem_nhdsWithin] with p hp
            obtain ⟨hmeas, -, -⟩ := parisiFRaw_props_of_admissible β hp j
            exact (Real.continuous_exp.measurable.comp
              (((hmeas.comp ((measurable_id.const_mul _).const_add y))).const_mul
                (p.1 (k + 1 - j)))).aestronglyMeasurable
          · filter_upwards [self_mem_nhdsWithin] with p hp
            filter_upwards with z
            obtain ⟨hmA, hmB⟩ := admissible_m_mem hp (k + 1 - j)
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
            refine Real.exp_le_exp.2 ?_
            have hb := hbnd p hp z
            have habs := (abs_le.1 hb).2
            nlinarith [abs_nonneg (parisiFRaw k p.1 p.2 β j
              (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z)),
              le_abs_self (parisiFRaw k p.1 p.2 β j
                (y + Real.sqrt (β ^ 2 * (p.2 (k + 2 - j) - p.2 (k + 1 - j))) * z))]
          · filter_upwards with z
            exact (Real.continuous_exp.tendsto _).comp (hm.tendsto.mul (hptw z))
        have hIpos : 0 < ∫ z, Real.exp (p₀.1 (k + 1 - j) *
            parisiFRaw k p₀.1 p₀.2 β j
              (y + Real.sqrt (β ^ 2 * (p₀.2 (k + 2 - j) - p₀.2 (k + 1 - j))) * z))
            ∂(gaussianReal 0 1) := by
          obtain ⟨hmeas, hgrow, -⟩ := parisiFRaw_props_of_admissible β hp₀ j
          exact integral_exp_pos
            (integrable_exp_mul_of_hasLinearGrowth hgrow hmeas _ y _)
        have hlog := (Real.continuousAt_log hIpos.ne').tendsto.comp hexpint
        have hinv : Filter.Tendsto (fun p : (ℕ → ℝ) × (ℕ → ℝ) => 1 / p.1 (k + 1 - j))
            (𝓝[admissible k] p₀) (𝓝 (1 / p₀.1 (k + 1 - j))) :=
          tendsto_const_nhds.div hm.tendsto hmpos.ne'
        have hfinal := hinv.mul hlog
        rw [ContinuousWithinAt]
        rw [parisiStep, if_neg hm0]
        refine hfinal.congr' ?_
        filter_upwards [hposev] with p hp
        rw [parisiStep, if_neg hp.ne']
        rfl

/--
**Continuity of the Parisi functional in its parameters, at fixed `k`.**

The single analytic input to Target 2b-i.  Proof plan: induct on the level, propagating

* joint continuity of `(m, q, x) ↦ parisiFRaw k m q β j x` on `admissible k ×ˢ univ`,
* together with measurability, 1-Lipschitzness in `x` and a linear-growth bound whose
  constants are uniform over `admissible k` (the set is compact and `k` is fixed, so the
  constants may depend on `k` — 2b-i, unlike 2b-ii, needs no uniformity in `k`).

A single step is continuous in its parameters by dominated convergence, the dominating
function coming from the uniform linear-growth bound.  At a parameter where `m_p = 0` the
two branches of `parisiStep` meet, and continuity there is exactly
`parisiStep_zero_sandwich`, whose gap `m·v/2` is uniform in `x`.
-/
theorem continuousOn_parisiFunctionalRaw (k : ℕ) (β h : ℝ) :
    ContinuousOn (fun p : (ℕ → ℝ) × (ℕ → ℝ) => parisiFunctionalRaw k p.1 p.2 β h)
      (admissible k) := by
  intro p₀ hp₀
  have hF := continuousWithinAt_parisiFRaw β hp₀ (k + 2) le_rfl h
  have hsumc : Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ∑ i ∈ Finset.range (k + 1), p.1 (i + 1) * (p.2 (i + 2) ^ 2 - p.2 (i + 1) ^ 2)) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((continuous_apply (i + 1)).comp continuous_fst).mul
      ((((continuous_apply (i + 2)).comp continuous_snd).pow 2).sub
        (((continuous_apply (i + 1)).comp continuous_snd).pow 2))
  show ContinuousWithinAt (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      Real.log 2 + parisiFRaw k p.1 p.2 β (k + 2) h
        - β ^ 2 / 4 * ∑ i ∈ Finset.range (k + 1),
            p.1 (i + 1) * (p.2 (i + 2) ^ 2 - p.2 (i + 1) ^ 2)) (admissible k) p₀
  exact (continuousWithinAt_const.add hF).sub
    (continuousWithinAt_const.mul hsumc.continuousWithinAt)

/--
**Target 2b-i (Talagrand 2006, (2.17)).**  For each fixed number of levels `k`, the infimum
of `𝒫_k(m,q)` over admissible schemes is **attained**.

This is the form of parameter regularity that Talagrand's proof actually consumes: (2.16)
and (2.17) are the standing hypotheses of Theorem 2.2, and §5 differentiates the functional
at the minimising scheme.  He obtains it "by a compactness argument", noting that it is to
permit that argument that equality is allowed in (1.6) and (1.7).
-/
theorem exists_minimizer_parisiFunctional (k : ℕ) (β h : ℝ) :
    ∃ s : RSBScheme k, ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h := by
  obtain ⟨p₀, hp₀, hmin⟩ := (isCompact_admissible k).exists_isMinOn
    (admissible_nonempty k) (continuousOn_parisiFunctionalRaw k β h)
  refine ⟨schemeOfPair p₀ hp₀, fun s' => ?_⟩
  rw [parisiFunctional_eq_raw (schemeOfPair p₀ hp₀), parisiFunctional_eq_raw_toPair s',
    schemeOfPair_m, schemeOfPair_q]
  exact hmin s'.toPair_mem

/- **Target 2b (Lipschitz continuity in the scheme).**  Guerra's estimate:

  `|𝒫_k(m,q) - 𝒫_k(m',q')| ≤ C(β,h) · ∑_p (|m_p - m'_p| + |q_p - q'_p|)`,

with a constant `C` depending only on `β` and `h` — **uniformly in `k`**.

*Quantifier order matters here, and the previous statement had it wrong.*  It read

  `∀ k, ∃ C, ∀ s s' : RSBScheme k, …`,

which permits `C` to depend on `k`.  That cannot serve the purpose stated for this target:
controlling `parisiValue = inf_k inf_{(m,q)} 𝒫_k` requires an estimate uniform in `k`,
otherwise nothing survives the infimum over all `k`.  So `∃ C` is now hoisted outside
`∀ k`.  (`0 ≤ C` is added for convenience downstream; it costs nothing, since any witness
can be replaced by its absolute value.)

This is a legacy target for uniform control and passage from discrete to general
Parisi measures. It is not a hypothesis of the current `parisi_formula` deduction:
that deduction uses the proved fixed-`k` continuity and minimizer, together with
Theorems 2.1 and 2.2. Do not confuse this open uniform estimate with the completed
`continuousOn_parisiFunctionalRaw`.

This retained target is not a claim that the Annals proof uses this particular `ℓ¹`
estimate. Any future work on it should audit its intended purpose separately from
the current Theorem 2.2 task. -/
/- Legacy unfinished declaration removed from this trusted dependency slice. -/

/-! ## Milestone 3 — Guerra's replica-symmetry-breaking bound -/

/-! ### Guerra's bound, replica-symmetric case (`k = 0`)

The `k = 0` case of Target 3 is **proved**, by combining two things that already exist:

* RSAT's **Guerra sum rule** `SpinGlass.GeneralizedLatala.replica_symmetric_sum_rule`,

    `rsPressure β h q - interpolatedPressure … 1 = (β²/4) ∫₀¹ overlapVariance t dt`,

  whose right-hand side is `≥ 0` because `overlapVariance` is a variance
  (`overlapVariance_nonneg`).  This is exactly Guerra's interpolation: RSAT carries out the
  differentiation of the pressure along the smart path (`pressure_derivative`), the Gaussian
  integration by parts (`pressure_derivative_ibp_trace`), and the endpoint evaluation
  (`endpoint_pressure`).
* our **Target 2a** `parisiFunctional_rsScheme`, which evaluates the `k = 0` Parisi
  functional in closed form.

The two closed forms agree on the nose — RSAT's

    `rsPressure β h q = log 2 + 𝔼 log cosh (h + β√q z) + (β²/4)(1-q)²`

is our `𝒫_0(m,q)` after `add_comm` inside the `cosh`, since RSAT's
`standardGaussianExpectation` *is* `∫ · ∂(gaussianReal 0 1)`.  That is
`rsPressure_eq_parisiFunctional` below.

**What this does and does not settle.**  It settles Target 3 at `k = 0`: the SK free energy
is at most the replica-symmetric Parisi functional, for every `q ∈ [0,1]` — a genuine
finite-`N` theorem with no `O(1/N)` error, and the historically first form of Guerra's bound.
It does *not* settle Target 3 for general `k`: there the comparison field is the
Ruelle-type **cascade** attached to a `k+2`-level tree, and the free energy is computed
through the iterated `(1/m_p) log 𝔼_p exp(m_p ·)` — that is, through `parisiStep`.  RSAT's
smart path compares against a *single* Gaussian field (`SimpleDisorder`, covariance
`Nβ²q·R`), which is the `k = 0` cascade.

**Note on the pressure conventions.**  The statement is in terms of RSAT's
`interpolatedPressure … 1`, i.e. `𝔼[(1/N) log ∑_σ exp (-(U(σ) + h·mag σ))]`, whereas
`free_entropy` in this project is `𝔼[(1/N) log ∑_σ exp (U(σ) + h·mag σ)]`.  The two agree in
value — `-U` has the same law as `U` because `sk_cov_kernel` depends on the overlap only
through `R²`, and `cosh` is even — but that is an equality *in law*, not definitional, so it
is deliberately not asserted here.  Bridging the two conventions is a separate (routine but
non-trivial) lemma; stating the bound in RSAT's own convention keeps this theorem honest.
-/

/-- RSAT's replica-symmetric pressure is our `k = 0` Parisi functional. -/
theorem rsPressure_eq_parisiFunctional (β h q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    SpinGlass.GeneralizedLatala.rsPressure β h q
      = parisiFunctional (rsScheme q hq0 hq1) β h := by
  rw [parisiFunctional_rsScheme β h q hq0 hq1, SpinGlass.GeneralizedLatala.rsPressure]
  have hc : SpinGlass.GeneralizedLatala.standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z)))
      = ∫ z, Real.log (Real.cosh (β * Real.sqrt q * z + h)) ∂(gaussianReal 0 1) := by
    rw [SpinGlass.GeneralizedLatala.standardGaussianExpectation]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show Real.log (Real.cosh (h + β * Real.sqrt q * z))
        = Real.log (Real.cosh (β * Real.sqrt q * z + h))
    rw [add_comm]
  rw [hc]

/--
**Guerra's bound, replica-symmetric case — Target 3 for `k = 0`.**

For every `N`, every `(β, h)` and every `q ∈ [0,1]`, the finite-volume SK pressure is at most
the `k = 0` Parisi functional:

  `𝔼[(1/N) log Z_N] ≤ 𝒫_0(m, q)`.

No `O(1/N)` error term, because the covariance kernel is exactly `(Nβ²/2) R²`.

The proof is the Guerra sum rule together with non-negativity of the overlap variance; the
interpolation itself (differentiation of the pressure, Gaussian integration by parts,
endpoint evaluation) is RSAT's.
-/
theorem guerra_rs_bound {N : ℕ} [NeZero N] (hN : 0 < N) (β h q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (sk : SpinGlass.SKDisorder (Ω := Ω) N β h)
    (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    SpinGlass.GeneralizedLatala.interpolatedPressure N β h q sk sim 1
      ≤ parisiFunctional (rsScheme q hq0 hq1) β h := by
  obtain ⟨-, heq⟩ := SpinGlass.GeneralizedLatala.replica_symmetric_sum_rule
    N β h q sk sim hN hq0 hIndep
  have hnn : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1,
      SpinGlass.GeneralizedLatala.overlapVariance N β h q sk sim t :=
    setIntegral_nonneg measurableSet_Icc
      (fun t _ => SpinGlass.GeneralizedLatala.overlapVariance_nonneg N β h q sk sim t)
  rw [← rsPressure_eq_parisiFunctional β h q hq0 hq1]
  nlinarith [heq, hnn, sq_nonneg β]

/-- The Parisi value: infimum of the finite-step functionals over all `k` and all schemes. -/
noncomputable def parisiValue (β h : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}

/-! ### `parisiValue` is a genuine infimum

Consequences of `parisiFunctional_ge`: the defining set is non-empty and bounded below,
so `sInf` is *not* the junk value and `parisiValue` means what it says.  `parisiValue_le`
is the form Target 3' consumes.
-/

/-- The set of finite-step Parisi functionals is non-empty (take the RS scheme at `q = 0`). -/
theorem parisiSet_nonempty (β h : ℝ) :
    {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h}.Nonempty :=
  ⟨parisiFunctional (rsScheme 0 le_rfl zero_le_one) β h,
    ⟨0, rsScheme 0 le_rfl zero_le_one, rfl⟩⟩

/-- **The set of finite-step Parisi functionals is bounded below**, uniformly in `k`.
Without this, `sInf` would collapse to the junk value `0`. -/
theorem bddBelow_parisiSet (β h : ℝ) :
    BddBelow {x : ℝ | ∃ (k : ℕ) (s : RSBScheme k), x = parisiFunctional s β h} := by
  refine ⟨Real.log 2 - β ^ 2 / 4, ?_⟩
  rintro x ⟨k, s, rfl⟩
  exact parisiFunctional_ge s β h

/-- `parisiValue` really is below every finite-step functional. -/
theorem parisiValue_le {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    parisiValue β h ≤ parisiFunctional s β h :=
  csInf_le (bddBelow_parisiSet β h) ⟨k, s, rfl⟩

/-- `parisiValue` is bounded below by `log 2 - β²/4` (in particular it is not the junk value). -/
theorem parisiValue_ge (β h : ℝ) : Real.log 2 - β ^ 2 / 4 ≤ parisiValue β h := by
  refine le_csInf (parisiSet_nonempty β h) ?_
  rintro x ⟨k, s, rfl⟩
  exact parisiFunctional_ge s β h

end Targets
end SpinGlass
