module

/- Compatibility adaptation: supply measurable Gaussian coordinate laws to the moment-generating theorem. -/
/-
# Target 1a — the annealed bound

New work for the ParisiFormula project (not vendored).

This file discharges **Target 1a** of `Targets/Milestones.lean`:

  `free_entropy β h sk.U ≤ log 2 + β²/4 + |h|`,

which is one of the two hypotheses (`hbdd`) left open by
`ParisiFormula/GuerraToninelli.lean`.

## Proof outline

1. **Jensen for `log`** (`integral_log_le_log_integral`).  Rather than invoking the
   measure-theoretic Jensen inequality, we use the elementary bound
   `log x ≤ x - 1`: applying it to `W ω / m` with `m = 𝔼[W]` and integrating gives
   `𝔼[log W] - log m ≤ 𝔼[W]/m - 1 = 0`.

2. **The moment generating function of a coordinate of a Hilbert-space Gaussian**
   (`mgf_inner_isGaussianHilbert`).  The vendored `IsGaussianHilbert` structure
   presents `g` as a finite sum `∑ i, c i • w i` over an orthonormal basis, with the
   `c i` independent centred real Gaussians.  Hence `⟪g ω, v⟫ = ∑ i, ⟪w i, v⟫ * c i ω`
   is a finite sum of *independent* real random variables, and
   `ProbabilityTheory.iIndepFun.mgf_sum` together with `mgf_gaussianReal` gives

     `𝔼[exp ⟪g ·, v⟫] = exp (⟪Σ v, v⟫ / 2)`.

   This deliberately avoids having to prove the general statement "a continuous linear
   image of a Hilbert-space Gaussian is Gaussian", which the vendored core does not
   provide.

3. **Specialisation to the SK disorder** (`mgf_skDisorder_coord`).  Taking
   `v = std_basis N σ` and using `SKDisorder.cov_eq` together with `overlap_self`
   (`overlap N σ σ = 1`) gives `Var (U · σ) = N β² / 2`, hence
   `𝔼[exp (U · σ)] = exp (N β² / 4)`.  This is where the `β²/4` in the statement
   comes from.

4. **Assembly.**  `𝔼[Z] = ∑_σ exp(h m(σ)) · exp(N β²/4) ≤ 2^N · exp(|h| N) · exp(N β²/4)`,
   and Jensen turns this into the claimed bound on `(1/N) 𝔼[log Z]`.

Reference: Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, (1.24).
-/
public import ParisiFormula.GuerraToninelli
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open scoped BigOperators NNReal InnerProductSpace

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

universe u

variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## 1. Jensen's inequality for `log`, via `log x ≤ x - 1` -/

/--
**Jensen's inequality for `log`** on *any* probability space: `𝔼[log W] ≤ log 𝔼[W]` for a
strictly positive integrable `W` with integrable logarithm.

Stated for a general `μ` rather than the ambient `ℙ`: Target 1a uses it on `ℙ`, but Target
2b needs the same inequality on `gaussianReal 0 1` (for the Jensen half of
`Targets.abs_parisiStep_sub_self_le`).

The proof is the elementary one: `log t ≤ t - 1` applied to `t = W ω / 𝔼[W]`.
-/
theorem integral_log_le_log_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {W : α → ℝ}
    (hpos : ∀ a, 0 < W a)
    (hW : Integrable W μ)
    (hlog : Integrable (fun a => Real.log (W a)) μ) :
    (∫ a, Real.log (W a) ∂μ) ≤ Real.log (∫ a, W a ∂μ) := by
  classical
  set m : ℝ := ∫ a, W a ∂μ with hm
  have hmpos : 0 < m := by
    have hsupp : (Function.support fun a => W a) = Set.univ := by
      ext a
      simp [Function.mem_support, ne_of_gt (hpos a)]
    rw [hm, integral_pos_iff_support_of_nonneg (fun a => (hpos a).le) hW, hsupp]
    simp
  have hmne : m ≠ 0 := ne_of_gt hmpos
  -- Pointwise: `log (W a) - log m = log (W a / m) ≤ W a / m - 1`.
  have key : ∀ a, Real.log (W a) - Real.log m ≤ W a / m - 1 := by
    intro a
    have h1 : Real.log (W a / m) ≤ W a / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hpos a) hmpos)
    rwa [Real.log_div (ne_of_gt (hpos a)) hmne] at h1
  have hintL : Integrable (fun a => Real.log (W a) - Real.log m) μ :=
    hlog.sub (integrable_const _)
  have hintR : Integrable (fun a => W a / m - 1) μ :=
    (hW.div_const m).sub (integrable_const _)
  have hmono := integral_mono hintL hintR key
  rw [integral_sub hlog (integrable_const _),
      integral_sub (hW.div_const m) (integrable_const _),
      integral_div] at hmono
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at hmono
  rw [← hm, div_self hmne] at hmono
  linarith

/-! ## 2. The mgf of a coordinate of a Hilbert-space Gaussian -/

section HilbertGaussian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] {g : Ω → H}

/--
The coordinate `ω ↦ ⟪g ω, v⟫` of an `IsGaussianHilbert` vector is the finite sum
`∑ i, ⟪w i, v⟫ * c i ω` of independent centred real Gaussians.
-/
theorem inner_apply_eq_sum_coord (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H)
    (ω : Ω) :
    ⟪g ω, v⟫_ℝ = ∑ i : hg.ι, ⟪hg.w i, v⟫_ℝ * hg.c i ω := by
  classical
  have hpt : g ω = ∑ i : hg.ι, hg.c i ω • hg.w i := congrFun hg.repr ω
  rw [hpt, sum_inner]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_smul_left]
  ring

/-- The same identity, packaged as an equality of functions (for the mgf computation). -/
theorem inner_eq_sum_coord (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H) :
    (fun ω => ⟪g ω, v⟫_ℝ)
      = ∑ i : hg.ι, (fun ω => ⟪hg.w i, v⟫_ℝ * hg.c i ω) := by
  funext ω
  simp only [Finset.sum_apply]
  exact inner_apply_eq_sum_coord hg v ω

/-- The family `ω ↦ ⟪w i, v⟫ * c i ω` is independent. -/
theorem iIndepFun_coord (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H) :
    iIndepFun (fun i : hg.ι => fun ω => ⟪hg.w i, v⟫_ℝ * hg.c i ω) (ℙ : Measure Ω) :=
  hg.c_indep.comp (fun i : hg.ι => fun x : ℝ => ⟪hg.w i, v⟫_ℝ * x)
    (fun i => measurable_id.const_mul _)

/-- Each scaled coordinate has an integrable exponential. -/
theorem integrable_exp_coord (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H)
    (i : hg.ι) :
    Integrable (fun ω => Real.exp ((1 : ℝ) * (⟪hg.w i, v⟫_ℝ * hg.c i ω)))
      (ℙ : Measure Ω) := by
  have hlaw : Measure.map (hg.c i) (ℙ : Measure Ω) = gaussianReal 0 (hg.τ i) :=
    hg.c_gauss i
  have hgauss : Integrable (fun x : ℝ => Real.exp (⟪hg.w i, v⟫_ℝ * x))
      (Measure.map (hg.c i) (ℙ : Measure Ω)) := by
    rw [hlaw]
    exact integrable_exp_mul_gaussianReal _
  have h2 : Integrable (fun ω => Real.exp (⟪hg.w i, v⟫_ℝ * hg.c i ω)) (ℙ : Measure Ω) :=
    (integrable_map_measure hgauss.aestronglyMeasurable (hg.c_meas i).aemeasurable).mp hgauss
  simpa [one_mul] using h2

/--
**Moment generating function of a Hilbert-space Gaussian coordinate.**

`𝔼[exp ⟪g ·, v⟫] = exp (⟪Σ v, v⟫ / 2)`, where `Σ = covOp hg` is the covariance operator.
-/
theorem mgf_inner_isGaussianHilbert (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H) :
    mgf (fun ω => ⟪g ω, v⟫_ℝ) (ℙ : Measure Ω) 1
      = Real.exp (⟪(covOp (g := g) hg) v, v⟫_ℝ / 2) := by
  classical
  have hmeas : ∀ i : hg.ι, Measurable (fun ω => ⟪hg.w i, v⟫_ℝ * hg.c i ω) :=
    fun i => (hg.c_meas i).const_mul _
  -- Each factor of the product.
  have hfac : ∀ i : hg.ι,
      mgf (fun ω => ⟪hg.w i, v⟫_ℝ * hg.c i ω) (ℙ : Measure Ω) 1
        = Real.exp ((hg.τ i : ℝ) * ⟪hg.w i, v⟫_ℝ ^ 2 / 2) := by
    intro i
    have hlaw : HasLaw (hg.c i) (gaussianReal 0 (hg.τ i)) (ℙ : Measure Ω) :=
      { aemeasurable := (hg.c_meas i).aemeasurable, map_eq := hg.c_gauss i }
    rw [mgf_const_mul, mgf_gaussianReal hlaw]
    congr 1
    ring
  -- The covariance pairing is the corresponding sum of variances.
  have hcov : ⟪(covOp (g := g) hg) v, v⟫_ℝ
      = ∑ i : hg.ι, (hg.τ i : ℝ) * ⟪hg.w i, v⟫_ℝ ^ 2 := by
    rw [covOp_apply (g := g) (hg := hg) v, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left, real_inner_comm v (hg.w i)]
    ring
  rw [inner_eq_sum_coord hg v,
      (iIndepFun_coord hg v).mgf_sum hmeas Finset.univ,
      Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfac i),
      ← Real.exp_sum, hcov, Finset.sum_div]

/-- The exponential of a Hilbert-space Gaussian coordinate is integrable. -/
theorem integrable_exp_inner_isGaussianHilbert
    (hg : IsGaussianHilbert (Ω := Ω) (H := H) g) (v : H) :
    Integrable (fun ω => Real.exp (⟪g ω, v⟫_ℝ)) (ℙ : Measure Ω) := by
  classical
  have hmeas : ∀ i : hg.ι, Measurable (fun ω => ⟪hg.w i, v⟫_ℝ * hg.c i ω) :=
    fun i => (hg.c_meas i).const_mul _
  have h := (iIndepFun_coord hg v).integrable_exp_mul_sum (t := 1) hmeas
    (s := Finset.univ) (fun i _ => integrable_exp_coord hg v i)
  simp only [Finset.sum_apply, one_mul] at h
  simp only [inner_apply_eq_sum_coord hg v]
  exact h

end HilbertGaussian

/-! ## 3. Specialisation to the SK disorder -/

section SK

variable {N : ℕ} {β h : ℝ}

/-- Writing a coordinate of the disorder as an inner product against `std_basis`. -/
theorem skDisorder_coord_apply_eq_inner (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N)
    (ω : Ω) : sk.U ω σ = ⟪sk.U ω, std_basis N σ⟫_ℝ := by
  rw [real_inner_comm]
  exact (inner_std_basis_apply (N := N) σ (sk.U ω)).symm

/-- The same identity, packaged as an equality of functions. -/
theorem skDisorder_coord_eq_inner (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N) :
    (fun ω => sk.U ω σ) = fun ω => ⟪sk.U ω, std_basis N σ⟫_ℝ :=
  funext (fun ω => skDisorder_coord_apply_eq_inner sk σ ω)

/--
The variance of a single coordinate of the SK disorder is `N β² / 2`
(`sk_cov_kernel N β σ σ = (N β²/2) · (overlap N σ σ)² = N β²/2`, since `overlap N σ σ = 1`).
-/
theorem skDisorder_cov_diag (hN : 0 < N) (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N) :
    ⟪(covOp (g := sk.U) sk.hU) (std_basis N σ), std_basis N σ⟫_ℝ = (N : ℝ) * β ^ 2 / 2 := by
  rw [sk.cov_eq σ σ]
  simp [sk_cov_kernel, overlap_self (N := N) hN σ]

/--
**The annealed moment of a single configuration**: `𝔼[exp (U σ)] = exp (N β² / 4)`.
-/
theorem mgf_skDisorder_coord (hN : 0 < N) (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N) :
    mgf (fun ω => sk.U ω σ) (ℙ : Measure Ω) 1 = Real.exp ((N : ℝ) * β ^ 2 / 4) := by
  rw [skDisorder_coord_eq_inner sk σ,
      mgf_inner_isGaussianHilbert sk.hU (std_basis N σ),
      skDisorder_cov_diag hN sk σ]
  congr 1
  ring

/-- `𝔼[exp (U σ)] = exp (N β² / 4)`, stated as an integral. -/
theorem integral_exp_skDisorder_coord (hN : 0 < N) (sk : SKDisorder (Ω := Ω) N β h)
    (σ : Config N) :
    (∫ ω, Real.exp (sk.U ω σ) ∂(ℙ : Measure Ω)) = Real.exp ((N : ℝ) * β ^ 2 / 4) := by
  have h := mgf_skDisorder_coord (Ω := Ω) hN sk σ
  simpa [mgf, one_mul] using h

/-- Integrability of `exp (U σ)`. -/
theorem integrable_exp_skDisorder_coord (sk : SKDisorder (Ω := Ω) N β h) (σ : Config N) :
    Integrable (fun ω => Real.exp (sk.U ω σ)) (ℙ : Measure Ω) := by
  simp only [skDisorder_coord_apply_eq_inner sk σ]
  exact integrable_exp_inner_isGaussianHilbert sk.hU (std_basis N σ)

/-- The partition function is integrable. -/
theorem integrable_skZ (sk : SKDisorder (Ω := Ω) N β h) :
    Integrable (fun ω => skZ (N := N) (β := β) (h := h) (sk.U ω)) (ℙ : Measure Ω) := by
  classical
  have hrw : (fun ω => skZ (N := N) (β := β) (h := h) (sk.U ω))
      = fun ω => ∑ σ : Config N,
          Real.exp (h * magnetization N σ) * Real.exp (sk.U ω σ) := by
    funext ω
    rw [skZ_eq]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Real.exp_add]
    ring_nf
  rw [hrw]
  refine integrable_finsetSum _ (fun σ _ => ?_)
  exact (integrable_exp_skDisorder_coord sk σ).const_mul _

/--
**The annealed partition function.**  `𝔼[Z_N] = exp (N β²/4) · ∑_σ exp (h m(σ))`.
-/
theorem integral_skZ (hN : 0 < N) (sk : SKDisorder (Ω := Ω) N β h) :
    (∫ ω, skZ (N := N) (β := β) (h := h) (sk.U ω) ∂(ℙ : Measure Ω))
      = ∑ σ : Config N, Real.exp (h * magnetization N σ) * Real.exp ((N : ℝ) * β ^ 2 / 4) := by
  classical
  have hrw : (fun ω => skZ (N := N) (β := β) (h := h) (sk.U ω))
      = fun ω => ∑ σ : Config N,
          Real.exp (h * magnetization N σ) * Real.exp (sk.U ω σ) := by
    funext ω
    rw [skZ_eq]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Real.exp_add]
    ring_nf
  rw [hrw, integral_finsetSum _
    (fun σ _ => (integrable_exp_skDisorder_coord sk σ).const_mul _)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [integral_const_mul, integral_exp_skDisorder_coord hN sk σ]

/--
**Target 1a (annealed bound).**

`(1/N) 𝔼[log Z_N] ≤ log 2 + β²/4 + |h|`.

Reference: Talagrand, Vol. I, (1.24).
-/
theorem free_entropy_le_annealed (hN : 0 < N) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) N β h) :
    free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U
      ≤ Real.log 2 + β ^ 2 / 4 + |h| := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  -- Step 1: rewrite the free entropy as `(1/N) * 𝔼[log Z]`.
  have hfe : free_entropy (Ω := Ω) (N := N) (β := β) (h := h) sk.U
      = (1 / (N : ℝ)) * ∫ ω, Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))
          ∂(ℙ : Measure Ω) := by
    rw [free_entropy]
    rw [← integral_const_mul]
    rfl
  -- Step 2: Jensen.
  have hZpos : ∀ ω, 0 < skZ (N := N) (β := β) (h := h) (sk.U ω) := fun ω =>
    Z_pos (N := N) _
  have hjensen := integral_log_le_log_integral (W := fun ω =>
      skZ (N := N) (β := β) (h := h) (sk.U ω)) hZpos (integrable_skZ sk)
      (integrable_log_skZ (Ω := Ω) (N := N) (β := β) (h := h) sk)
  -- Step 3: bound `𝔼[Z]`.
  have hbound : (∫ ω, skZ (N := N) (β := β) (h := h) (sk.U ω) ∂(ℙ : Measure Ω))
      ≤ 2 ^ N * Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4) := by
    rw [integral_skZ hN sk]
    have hterm : ∀ σ : Config N,
        Real.exp (h * magnetization N σ) * Real.exp ((N : ℝ) * β ^ 2 / 4)
          ≤ Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4) := by
      intro σ
      exact mul_le_mul_of_nonneg_right (exp_magnetization_le (N := N) h σ)
        (Real.exp_pos _).le
    calc
      ∑ σ : Config N, Real.exp (h * magnetization N σ) * Real.exp ((N : ℝ) * β ^ 2 / 4)
          ≤ ∑ _σ : Config N, Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4) :=
            Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = (Fintype.card (Config N) : ℝ)
            * (Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ((2 : ℝ) ^ N)
            * (Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4)) := by
            congr 1
            simp [Config]
      _ = 2 ^ N * Real.exp (|h| * (N : ℝ)) * Real.exp ((N : ℝ) * β ^ 2 / 4) := by
            ring
  -- Step 4: take logs and divide by `N`.
  have hEZpos : 0 < ∫ ω, skZ (N := N) (β := β) (h := h) (sk.U ω) ∂(ℙ : Measure Ω) := by
    have hsupp : (Function.support fun ω => skZ (N := N) (β := β) (h := h) (sk.U ω))
        = Set.univ := by
      ext ω
      simp [Function.mem_support, ne_of_gt (hZpos ω)]
    rw [integral_pos_iff_support_of_nonneg (fun ω => (hZpos ω).le) (integrable_skZ sk), hsupp]
    simp
  have hlogle : Real.log (∫ ω, skZ (N := N) (β := β) (h := h) (sk.U ω) ∂(ℙ : Measure Ω))
      ≤ (N : ℝ) * Real.log 2 + |h| * (N : ℝ) + (N : ℝ) * β ^ 2 / 4 := by
    have := Real.log_le_log hEZpos hbound
    refine this.trans_eq ?_
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_pow, Real.log_exp, Real.log_exp]
    try push_cast
    try ring
  have hfinal : (∫ ω, Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω)) ∂(ℙ : Measure Ω))
      ≤ (N : ℝ) * Real.log 2 + |h| * (N : ℝ) + (N : ℝ) * β ^ 2 / 4 := hjensen.trans hlogle
  rw [hfe, one_div, inv_mul_eq_div, div_le_iff₀ hNR]
  calc
    (∫ ω, Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω)) ∂(ℙ : Measure Ω))
        ≤ (N : ℝ) * Real.log 2 + |h| * (N : ℝ) + (N : ℝ) * β ^ 2 / 4 := hfinal
    _ = (Real.log 2 + β ^ 2 / 4 + |h|) * (N : ℝ) := by ring

end SK

end SpinGlass
