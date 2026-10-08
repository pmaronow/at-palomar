module

/- Compatibility adaptation: configuration restriction abbreviations preserve decidable-instance transparency. -/
/- Compatibility adaptation: normalize spin-product conditional multiplication explicitly. -/
/-
PROVENANCE (ParisiFormula project):
  Ported verbatim from njimaMath/research_public, path
  perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean, commit f3b34d2071d9cde5262c6672b6ebab132d4a7b43
  (Apache-2.0).  The only edits are the two `import` lines, which now point at the
  vendored core under `Lemmas.SpinGlass`.

  STATUS: the file contains no placeholders, but the final results are CONDITIONAL:
  `guerra_toninelli_superadditive` assumes monotonicity of the interpolation `Φ` (`hmono`),
  and `free_entropy_tendsto_of_bddAbove` additionally assumes an upper bound (`hbdd`).
  Discharging those two hypotheses is Milestone 1 of this project; see
  `Targets/Milestones.lean` and `blueprint/blueprint.tex`, Chapter 1.
-/
public import Lemmas.SpinGlass.SKModel
public import Lemmas.SpinGlass.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Subadditive
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

open scoped BigOperators

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

open scoped InnerProductSpace

/-!
# Guerra–Toninelli inequality for the SK model (blueprint)

This file is a **blueprint** for the Guerra–Toninelli superadditivity theorem for the SK model:

`𝔼[log Z_{N+M}(β,h)] ≥ 𝔼[log Z_N(β,h)] + 𝔼[log Z_M(β,h)]`.

We follow the usual Aizenman–Sims–Starr / Talagrand interpolation argument:

1. Put the SK Hamiltonian in a convenient centered Gaussian form (here: `SKDisorder`).
2. Prove a Gaussian interpolation lemma for `t ↦ 𝔼[log ∑ ξ_γ exp(X_γ(t))]`
   (Gaussian IBP + Hessian computation).
3. Use the Guerra–Toninelli interpolation between size `L = N+M` and the decoupled
   pair of systems of sizes `N` and `M`.
4. Compare covariances along the interpolation using convexity of `x ↦ x^2`, and use the
   sign of the off-diagonal Hessian entries to deduce monotonicity.

At the end, superadditivity of `Q_N := 𝔼[log Z_N]` implies subadditivity of `(N f_N)` and
existence of the thermodynamic limit via Fekete’s lemma.

This file is intentionally *not* fully finished: the analytic Gaussian-comparison step is
left as a TODO, but all objects and reductions are laid out so the remaining work is local.
-/

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- Expectation notation
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂(ℙ : Measure Ω)

/-! ## 1. Configurations on `N+M` spins: split/join -/

section Blocks

variable (N M : ℕ)

/-- Restrict a configuration on `N+M` spins to the first `N` coordinates. -/
abbrev cfgLeft (γ : Config (N + M)) : Config N :=
  fun i => γ (Fin.castAdd M i)

/-- Restrict a configuration on `N+M` spins to the last `M` coordinates. -/
abbrev cfgRight (γ : Config (N + M)) : Config M :=
  fun j => γ (Fin.natAdd N j)

/-- Concatenate two configurations `(α,σ)` into a configuration on `N+M` spins. -/
def cfgJoin (α : Config N) (σ : Config M) : Config (N + M) :=
  fun i => Fin.addCases α σ i

@[simp] lemma cfgLeft_join (α : Config N) (σ : Config M) :
    cfgLeft (N := N) (M := M) (cfgJoin (N := N) (M := M) α σ) = α := by
  funext i
  simp [cfgLeft, cfgJoin]

@[simp] lemma cfgRight_join (α : Config N) (σ : Config M) :
    cfgRight (N := N) (M := M) (cfgJoin (N := N) (M := M) α σ) = σ := by
  funext j
  simp [cfgRight, cfgJoin]

/-- Equivalence `Config (N+M) ≃ Config N × Config M`. -/
def cfgEquiv : Config (N + M) ≃ (Config N × Config M) where
  toFun γ := (cfgLeft (N := N) (M := M) γ, cfgRight (N := N) (M := M) γ)
  invFun p := cfgJoin (N := N) (M := M) p.1 p.2
  left_inv γ := by
    -- `Fin.addCases_castAdd_natAdd` is exactly the statement that splitting then joining is `id`.
    -- (Mathlib ≥ v4.32.1 states it pointwise, with an explicit point argument.)
    -- `exact` (not `simpa`): `cfgJoin`/`cfgLeft`/`cfgRight` unfold definitionally, whereas
    -- their `simp` equation lemmas are in applied form and cannot fire under `Fin.addCases`.
    funext i
    exact Fin.addCases_castAdd_natAdd (m := N) (n := M) (v := γ) i
  right_inv p := by
    rcases p with ⟨α, σ⟩
    simp [cfgLeft_join, cfgRight_join]

@[simp] lemma cfgJoin_cfgLeft_cfgRight (γ : Config (N + M)) :
    cfgJoin (N := N) (M := M)
        (cfgLeft (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ) = γ := by
  funext i
  exact Fin.addCases_castAdd_natAdd (m := N) (n := M) (v := γ) i

lemma magnetization_join (α : Config N) (σ : Config M) :
    magnetization (N := N + M) (cfgJoin (N := N) (M := M) α σ)
      =
    magnetization (N := N) α + magnetization (N := M) σ := by
  simp [magnetization, cfgJoin, spin, Fin.sum_univ_add]

lemma magnetization_split (γ : Config (N + M)) :
    magnetization (N := N + M) γ
      =
    magnetization (N := N) (cfgLeft (N := N) (M := M) γ)
      +
    magnetization (N := M) (cfgRight (N := N) (M := M) γ) := by
  have h := magnetization_join (N := N) (M := M)
    (cfgLeft (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ)
  rwa [cfgJoin_cfgLeft_cfgRight] at h

end Blocks

/-! ## 2. Partition function with external field (deterministic layer) -/

section Deterministic

variable {N : ℕ} (β h : ℝ)

/--
The SK energy functional, in the “Gaussian + external field” convention compatible with `Z`:

`H(σ) = -(K(σ) + h*magnetization(σ))`, so that `exp(-H(σ)) = exp(K(σ) + h*magnetization(σ))`.
-/
noncomputable def skEnergy (β : ℝ) (K : EnergySpace N) : EnergySpace N :=
  (-1) • K + magnetic_field_vector (N := N) (-h)

/-- The corresponding partition function. -/
noncomputable def skZ (K : EnergySpace N) : ℝ :=
  Z N (skEnergy (N := N) (β := β) (h := h) K)

lemma skZ_eq (K : EnergySpace N) :
    skZ (N := N) (β := β) (h := h) K
      = ∑ σ : Config N, Real.exp (K σ + h * magnetization N σ) := by
  classical
  -- Unfolding shows `-skEnergy = K + h*magnetization`.
  simpa [add_comm] using
    (by
      simp [skZ, skEnergy, Z, magnetic_field_vector])

/-! ### Free entropy -/

/--
Free entropy (quenched) for an abstract SK disorder `K`:

`s_N(β,h) = 𝔼[ F_N(skEnergy(K)) ]` where `F_N` is `free_energy_density`.
-/
noncomputable def free_entropy (K : Ω → EnergySpace N) : ℝ :=
  𝔼[fun ω =>
    free_energy_density (N := N) (skEnergy (N := N) (β := β) (h := h) (K ω))]

lemma integrable_log_skZ (sk : SKDisorder (Ω := Ω) N β h) :
    Integrable (fun ω => Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))) (ℙ : Measure Ω) := by
  classical
  have abs_log_Z_le (n : ℕ) (H : EnergySpace n) :
      |Real.log (Z n H)| ≤ Real.log (Fintype.card (Config n) : ℝ) + ‖H‖ := by
    classical
    have hcard_pos : 0 < Fintype.card (Config n) := by
      have : Nonempty (Config n) := ⟨fun _ => false⟩
      exact Fintype.card_pos
    have hZpos : 0 < Z n H := Z_pos (N := n) (H := H)
    have hZ_le := Z_le_card_mul_exp_norm (N := n) H
    have hZ_ge := Z_ge_exp_neg_norm (N := n) H
    have hlog_nonneg : 0 ≤ Real.log (Fintype.card (Config n) : ℝ) := by
      have h1le : (1 : ℝ) ≤ (Fintype.card (Config n) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
      exact Real.log_nonneg h1le
    have hlog_upper :
        Real.log (Z n H) ≤ Real.log (Fintype.card (Config n) : ℝ) + ‖H‖ := by
      have hlog_le :
          Real.log (Z n H) ≤ Real.log ((Fintype.card (Config n) : ℝ) * Real.exp (‖H‖)) :=
        Real.log_le_log hZpos hZ_le
      have hcard_ne : (Fintype.card (Config n) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcard_pos)
      have h1 :
          Real.log ((Fintype.card (Config n) : ℝ) * Real.exp (‖H‖))
            =
          Real.log (Fintype.card (Config n) : ℝ) + ‖H‖ := by
        have hexp_ne : Real.exp (‖H‖) ≠ 0 := Real.exp_ne_zero _
        calc
          Real.log ((Fintype.card (Config n) : ℝ) * Real.exp (‖H‖))
              = Real.log (Fintype.card (Config n) : ℝ) + Real.log (Real.exp (‖H‖)) := by
                simpa using (Real.log_mul hcard_ne hexp_ne)
          _ = Real.log (Fintype.card (Config n) : ℝ) + ‖H‖ := by
                rw [Real.log_exp]
      exact (le_trans hlog_le (le_of_eq h1))
    have hlog_lower :
        -(Real.log (Fintype.card (Config n) : ℝ) + ‖H‖) ≤ Real.log (Z n H) := by
      have h1 : -‖H‖ ≤ Real.log (Z n H) := by
        have hlog_le : Real.log (Real.exp (-‖H‖)) ≤ Real.log (Z n H) := by
          have hexp_pos : 0 < Real.exp (-‖H‖) := Real.exp_pos _
          exact Real.log_le_log hexp_pos hZ_ge
        simpa using hlog_le
      have h2 : -(Real.log (Fintype.card (Config n) : ℝ) + ‖H‖) ≤ -‖H‖ := by
        nlinarith [hlog_nonneg]
      exact le_trans h2 h1
    exact (abs_le.2 ⟨hlog_lower, hlog_upper⟩)

  have hU_meas : Measurable sk.U := sk.hU.repr_measurable
  have hZ := contDiff_Z (N := N)
  have hlogZ := hZ.log (fun H => (Z_pos (N := N) (H := H)).ne')
  have hEnergy :
      Continuous fun K : EnergySpace N => skEnergy (N := N) (β := β) (h := h) K := by
    -- `simp only [skEnergy]` (not `simpa ... using h1.add h2`): a full `simp` normalises the
    -- goal into `Pi.add` form, which no longer matches the pointwise `Continuous.add`.
    -- `fun_prop` then discharges `fun K => (-1) • K + const` without depending on how the
    -- scalar literal in `skEnergy` elaborates.
    simp only [skEnergy]
    fun_prop
  have hcont :
      Continuous fun K : EnergySpace N => Real.log (skZ (N := N) (β := β) (h := h) K) := by
    exact hlogZ.continuous.comp hEnergy
  have hf_m :
      AEStronglyMeasurable
        (fun ω => Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))) (ℙ : Measure Ω) := by
    exact (hcont.measurable.comp hU_meas).aestronglyMeasurable

  let cN : ℝ :=
    Real.log (Fintype.card (Config N) : ℝ) + ‖magnetic_field_vector (N := N) (-h)‖
  let gN : Ω → ℝ := fun ω => cN + ‖sk.U ω‖
  have hgN : Integrable gN (ℙ : Measure Ω) := by
    have hnorm : Integrable (fun ω => ‖sk.U ω‖) (ℙ : Measure Ω) :=
      integrable_norm_of_gaussian (g := sk.U) sk.hU
    simpa [gN] using
      (integrable_const (μ := (ℙ : Measure Ω)) (c := cN)).add hnorm
  refine Integrable.mono' hgN hf_m ?_
  refine ae_of_all _ (fun ω => ?_)
  have hAbs :
      |Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))|
        ≤ Real.log (Fintype.card (Config N) : ℝ) +
          ‖skEnergy (N := N) (β := β) (h := h) (sk.U ω)‖ := by
    simpa [skZ] using
      (abs_log_Z_le (n := N) (H := skEnergy (N := N) (β := β) (h := h) (sk.U ω)))
  have hEnergy_norm :
      ‖skEnergy (N := N) (β := β) (h := h) (sk.U ω)‖
        ≤ ‖sk.U ω‖ + ‖magnetic_field_vector (N := N) (-h)‖ := by
    simpa [skEnergy, neg_one_smul] using
      (norm_add_le (-(sk.U ω)) (magnetic_field_vector (N := N) (-h)))
  have hAbs' :
      |Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))|
        ≤ Real.log (Fintype.card (Config N) : ℝ) +
          (‖sk.U ω‖ + ‖magnetic_field_vector (N := N) (-h)‖) := by
    have :
        Real.log (Fintype.card (Config N) : ℝ) +
            ‖skEnergy (N := N) (β := β) (h := h) (sk.U ω)‖
          ≤
        Real.log (Fintype.card (Config N) : ℝ) +
            (‖sk.U ω‖ + ‖magnetic_field_vector (N := N) (-h)‖) := by
      linarith [hEnergy_norm]
    exact le_trans hAbs this
  have hAbs'' :
      |Real.log (skZ (N := N) (β := β) (h := h) (sk.U ω))| ≤ cN + ‖sk.U ω‖ := by
    simpa [cN, add_assoc, add_left_comm, add_comm] using hAbs'
  simpa [gN, Real.norm_eq_abs] using hAbs''

end Deterministic

/-! ## 3. Off-diagonal Hessian sign for `log Z` -/

section GaussianInterpolation

variable {N : ℕ}

/--
For the free energy density `H ↦ (1/N) log Z_N(H)`, the mixed second derivatives in distinct
configuration directions are nonpositive.

Concretely, for `σ ≠ τ`, the Hessian entry along the standard basis vectors equals
`-(1/N) * gσ * gτ`, where `gσ` are the Gibbs weights `gibbs_pmf`.
-/
theorem hessian_free_energy_std_basis_offdiag (H : EnergySpace N) {σ τ : Config N} (hστ : σ ≠ τ) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      = -(1 / (N : ℝ)) * gibbs_pmf N H σ * gibbs_pmf N H τ := by
  classical
  have hsum_h :
      (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N σ ρ) = gibbs_pmf N H σ := by
    simp [std_basis]
  have hsum_k :
      (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N τ ρ) = gibbs_pmf N H τ := by
    simp [std_basis]
  have hsum_hk' :
      (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N σ ρ * std_basis N τ ρ)
        = if σ = τ then gibbs_pmf N H σ else 0 := by
    by_cases h : σ = τ
    · subst h
      simp [std_basis]
    · simp [std_basis, h]
  have hsum_hk :
      (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N σ ρ * std_basis N τ ρ) = 0 := by
    simpa [hστ] using hsum_hk'
  -- Unfold the explicit Gibbs-covariance formula for the Hessian.
  calc
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
        =
        (1 / (N : ℝ)) *
          ((∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N σ ρ * std_basis N τ ρ) -
            (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N σ ρ) *
              (∑ ρ : Config N, gibbs_pmf N H ρ * std_basis N τ ρ)) := by
          simp [hessian_free_energy]
    _ = (1 / (N : ℝ)) * (0 - gibbs_pmf N H σ * gibbs_pmf N H τ) := by
          simp [hsum_h, hsum_k, hsum_hk]
    _ = -(1 / (N : ℝ)) * gibbs_pmf N H σ * gibbs_pmf N H τ := by
          ring

/-- Alias (historical name): the off-diagonal Hessian identity used in Gaussian interpolation. -/
theorem gaussian_interpolation_deriv_identity (H : EnergySpace N) {σ τ : Config N} (hστ : σ ≠ τ) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ)
      = -(1 / (N : ℝ)) * gibbs_pmf N H σ * gibbs_pmf N H τ :=
  hessian_free_energy_std_basis_offdiag (N := N) (H := H) (σ := σ) (τ := τ) hστ

theorem hessian_free_energy_std_basis_offdiag_nonpos (H : EnergySpace N) {σ τ : Config N} (hστ : σ ≠ τ) :
    hessian_free_energy N H (std_basis N σ) (std_basis N τ) ≤ 0 := by
  have h :=
    hessian_free_energy_std_basis_offdiag (N := N) (H := H) (σ := σ) (τ := τ) hστ
  -- The RHS is a nonpositive scalar times a nonnegative product of Gibbs weights.
  have hcoeff : -(1 / (N : ℝ)) ≤ 0 := by
    have : 0 ≤ (1 / (N : ℝ)) := by positivity
    exact neg_nonpos.2 this
  have hgσ : 0 ≤ gibbs_pmf N H σ := gibbs_pmf_nonneg (N := N) (H := H) σ
  have hgτ : 0 ≤ gibbs_pmf N H τ := gibbs_pmf_nonneg (N := N) (H := H) τ
  have h1 : (-(1 / (N : ℝ)) * gibbs_pmf N H σ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoeff hgσ
  have h2 : (-(1 / (N : ℝ)) * gibbs_pmf N H σ) * gibbs_pmf N H τ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h1 hgτ
  simpa [h, mul_assoc] using h2

end GaussianInterpolation

/-! ## 4. Guerra–Toninelli interpolation (random layer) -/

section Interpolation

variable {N M : ℕ} (β h : ℝ)
variable (skL : SKDisorder (Ω := Ω) (N + M) β h)
variable (skN : SKDisorder (Ω := Ω) N β h)
variable (skM : SKDisorder (Ω := Ω) M β h)

/--
The “decoupled” SK field on `N+M` spins obtained from independent fields on `N` and `M` spins:
`γ ↦ K_N(α) + K_M(σ)` where `γ = (α,σ)`.
-/
noncomputable def K_block : Ω → EnergySpace (N + M) :=
  fun ω =>
    WithLp.toLp 2 (fun γ : Config (N + M) =>
      (skN.U ω) (cfgLeft (N := N) (M := M) γ) + (skM.U ω) (cfgRight (N := N) (M := M) γ))

/--
Guerra–Toninelli interpolated field:

`K(t) = √t * K_{N+M} + √(1-t) * (K_N ⊕ K_M)` (pointwise on configurations).

This is the standard “smart path” / Gaussian interpolation used to compare free energies.
-/
noncomputable def K_interpol (t : ℝ) : Ω → EnergySpace (N + M) :=
  fun ω =>
    (Real.sqrt t) • skL.U ω + (Real.sqrt (1 - t)) • K_block (N := N) (M := M) (β := β) (h := h)
      (skN := skN) (skM := skM) ω

/-- The interpolated partition function `Z_{N+M}(t)`. -/
noncomputable def Z_interpol (t : ℝ) : Ω → ℝ :=
  fun ω => skZ (N := N + M) (β := β) (h := h) (K_interpol (N := N) (M := M) (β := β) (h := h)
    (skL := skL) (skN := skN) (skM := skM) t ω)

/-- The interpolated quenched free energy `Φ(t) = 𝔼[log Z_{N+M}(t)]`. -/
noncomputable def Φ (t : ℝ) : ℝ :=
  𝔼[fun ω => Real.log (Z_interpol (N := N) (M := M) (β := β) (h := h)
    (skL := skL) (skN := skN) (skM := skM) t ω)]

end Interpolation

/-! ## 5. Endpoint evaluation: `t = 0` factorizes -/

section Endpoints

variable {N M : ℕ} (β h : ℝ)
variable (skL : SKDisorder (Ω := Ω) (N + M) β h)
variable (skN : SKDisorder (Ω := Ω) N β h)
variable (skM : SKDisorder (Ω := Ω) M β h)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma Z_interpol_one (hNM : 0 < N + M) :
    Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 1
      = (N + M : ℝ) * free_entropy (N := N + M) (β := β) (h := h) skL.U := by
  -- At `t=1`, the interpolated field is exactly `skL.U`.
  have hNM0 : (N + M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNM)
  -- Rewrite the RHS as an integral, then cancel `(N+M) * (1/(N+M))`.
  symm
  calc
    (N + M : ℝ) * free_entropy (N := N + M) (β := β) (h := h) skL.U
        = 𝔼[fun ω =>
            (N + M : ℝ) *
              free_energy_density (N := N + M)
                (skEnergy (N := N + M) (β := β) (h := h) (skL.U ω))] := by
          simp [free_entropy, integral_const_mul]
    _ = Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 1 := by
          simp [Φ, Z_interpol, K_interpol, free_energy_density, skZ, div_eq_mul_inv, hNM0]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma Z_interpol_zero_factorizes (ω : Ω) :
    Z_interpol (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0 ω
      =
      skZ (N := N) (β := β) (h := h) (skN.U ω) *
      skZ (N := M) (β := β) (h := h) (skM.U ω) := by
  classical
  -- Expand the definition: at `t=0`, the field is `K_block`, and the sum over `Config (N+M)`
  -- can be rewritten as a sum over `Config N × Config M` using `cfgEquiv`.
  have hsum :
      (∑ γ : Config (N + M),
          Real.exp
            ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) γ +
              h * magnetization (N := N + M) γ))
        =
      ∑ p : Config N × Config M,
        Real.exp
          ((skN.U ω) p.1 + h * magnetization (N := N) p.1) *
            Real.exp ((skM.U ω) p.2 + h * magnetization (N := M) p.2) := by
    -- This is the purely combinatorial factorization step; the core is that
    -- `magnetization (α ⊕ σ) = magnetization α + magnetization σ`.
    have hmag (γ : Config (N + M)) :
        magnetization (N := N + M) γ =
          magnetization (N := N) (cfgLeft (N := N) (M := M) γ) +
            magnetization (N := M) (cfgRight (N := N) (M := M) γ) := by
      simpa using magnetization_split (N := N) (M := M) γ
    have hrew :
        (∑ γ : Config (N + M),
            Real.exp
              ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) γ +
                h * magnetization (N := N + M) γ))
          =
        ∑ p : Config N × Config M,
          Real.exp
            ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
                ((cfgEquiv (N := N) (M := M)).symm p) +
              h *
                magnetization (N := N + M) ((cfgEquiv (N := N) (M := M)).symm p)) := by
      simpa using
        (Fintype.sum_equiv (cfgEquiv (N := N) (M := M))
          (f := fun γ : Config (N + M) =>
            Real.exp
              ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) γ +
                h * magnetization (N := N + M) γ))
          (g := fun p : Config N × Config M =>
            Real.exp
              ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
                  ((cfgEquiv (N := N) (M := M)).symm p) +
                h *
                  magnetization (N := N + M) ((cfgEquiv (N := N) (M := M)).symm p)))
          (h := fun γ => by simp))
    calc
      (∑ γ : Config (N + M),
            Real.exp
              ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) γ +
                h * magnetization (N := N + M) γ))
          =
        ∑ p : Config N × Config M,
          Real.exp
            ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
                ((cfgEquiv (N := N) (M := M)).symm p) +
              h *
                magnetization (N := N + M) ((cfgEquiv (N := N) (M := M)).symm p)) := hrew
      _ =
        ∑ p : Config N × Config M,
          Real.exp
              ((skN.U ω) p.1 + h * magnetization (N := N) p.1) *
            Real.exp ((skM.U ω) p.2 + h * magnetization (N := M) p.2) := by
        refine
          (Fintype.sum_congr
            (fun p : Config N × Config M =>
              Real.exp
                ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω)
                    ((cfgEquiv (N := N) (M := M)).symm p) +
                  h *
                    magnetization (N := N + M) ((cfgEquiv (N := N) (M := M)).symm p)))
            (fun p : Config N × Config M =>
              Real.exp
                  ((skN.U ω) p.1 + h * magnetization (N := N) p.1) *
                Real.exp ((skM.U ω) p.2 + h * magnetization (N := M) p.2))
            ?_)
        intro p
        have hadd :
            ((skN.U ω) p.1 + (skM.U ω) p.2) +
                h *
                  (magnetization (N := N) p.1 + magnetization (N := M) p.2)
              =
            ((skN.U ω) p.1 + h * magnetization (N := N) p.1) +
              ((skM.U ω) p.2 + h * magnetization (N := M) p.2) := by
          simpa [mul_add] using (by ac_rfl)
        simp [cfgEquiv, K_block, hmag, hadd, Real.exp_add]
  -- Once the sum is rewritten as a product of terms depending only on `α` and `σ`,
  -- it factors using `Fintype.sum_mul_sum`.
  calc
    Z_interpol (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0 ω
        =
      (∑ γ : Config (N + M),
          Real.exp
            ((K_block (N := N) (M := M) (β := β) (h := h) (skN := skN) (skM := skM) ω) γ +
              h * magnetization (N := N + M) γ)) := by
      simp [Z_interpol, K_interpol, skZ_eq]
    _ =
      ∑ p : Config N × Config M,
        Real.exp
          ((skN.U ω) p.1 + h * magnetization (N := N) p.1) *
            Real.exp ((skM.U ω) p.2 + h * magnetization (N := M) p.2) := by
      exact hsum
    _ =
      (∑ α : Config N,
          Real.exp ((skN.U ω) α + h * magnetization (N := N) α)) *
        (∑ σ : Config M,
          Real.exp ((skM.U ω) σ + h * magnetization (N := M) σ)) := by
      calc
        (∑ p : Config N × Config M,
            Real.exp
                ((skN.U ω) p.1 + h * magnetization (N := N) p.1) *
              Real.exp ((skM.U ω) p.2 + h * magnetization (N := M) p.2))
            =
          ∑ α : Config N, ∑ σ : Config M,
            Real.exp ((skN.U ω) α + h * magnetization (N := N) α) *
              Real.exp ((skM.U ω) σ + h * magnetization (N := M) σ) := by
          simp [Fintype.sum_prod_type]
        _ =
          (∑ α : Config N,
              Real.exp ((skN.U ω) α + h * magnetization (N := N) α)) *
            (∑ σ : Config M,
              Real.exp ((skM.U ω) σ + h * magnetization (N := M) σ)) := by
          simpa using
            (Fintype.sum_mul_sum
              (fun α : Config N =>
                Real.exp ((skN.U ω) α + h * magnetization (N := N) α))
              (fun σ : Config M =>
                Real.exp ((skM.U ω) σ + h * magnetization (N := M) σ))).symm
    _ =
      skZ (N := N) (β := β) (h := h) (skN.U ω) *
        skZ (N := M) (β := β) (h := h) (skM.U ω) := by
      rw [← skZ_eq (N := N) (β := β) (h := h) (K := skN.U ω)]
      rw [← skZ_eq (N := M) (β := β) (h := h) (K := skM.U ω)]

private lemma Z_interpol_zero (hN : 0 < N) (hM : 0 < M) :
    Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0
      = (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U
        + (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U := by
  -- Take `log` and expectation in the pointwise factorization.
  classical
  let fN : Ω → ℝ := fun ω => Real.log (skZ (N := N) (β := β) (h := h) (skN.U ω))
  let fM : Ω → ℝ := fun ω => Real.log (skZ (N := M) (β := β) (h := h) (skM.U ω))
  have hInt_fN : Integrable fN (ℙ : Measure Ω) := by
    simpa [fN] using integrable_log_skZ (Ω := Ω) (N := N) (β := β) (h := h) skN
  have hInt_fM : Integrable fM (ℙ : Measure Ω) := by
    simpa [fM] using integrable_log_skZ (Ω := Ω) (N := M) (β := β) (h := h) skM

  have hcongr :
      (fun ω => Real.log (Z_interpol (N := N) (M := M) (β := β) (h := h)
          (skL := skL) (skN := skN) (skM := skM) 0 ω))
        =ᵐ[ℙ] fun ω => fN ω + fM ω := by
    refine ae_of_all _ (fun ω => ?_)
    have hNpos :
        0 < skZ (N := N) (β := β) (h := h) (skN.U ω) := by
      simpa [skZ] using
        (Z_pos (N := N) (H := skEnergy (N := N) (β := β) (h := h) (skN.U ω)))
    have hMpos :
        0 < skZ (N := M) (β := β) (h := h) (skM.U ω) := by
      simpa [skZ] using
        (Z_pos (N := M) (H := skEnergy (N := M) (β := β) (h := h) (skM.U ω)))
    have hNne : skZ (N := N) (β := β) (h := h) (skN.U ω) ≠ 0 := (ne_of_gt hNpos)
    have hMne : skZ (N := M) (β := β) (h := h) (skM.U ω) ≠ 0 := (ne_of_gt hMpos)
    calc
      Real.log
          (Z_interpol (N := N) (M := M) (β := β) (h := h)
            (skL := skL) (skN := skN) (skM := skM) 0 ω)
          =
        Real.log
          (skZ (N := N) (β := β) (h := h) (skN.U ω) *
            skZ (N := M) (β := β) (h := h) (skM.U ω)) := by
          simp [Z_interpol_zero_factorizes (N := N) (M := M) (β := β) (h := h)
            (skL := skL) (skN := skN) (skM := skM) ω]
      _ =
        Real.log (skZ (N := N) (β := β) (h := h) (skN.U ω)) +
          Real.log (skZ (N := M) (β := β) (h := h) (skM.U ω)) := by
          simpa using (Real.log_mul hNne hMne)
      _ = fN ω + fM ω := by
          simp [fN, fM]

  calc
    Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0
        =
      𝔼[fun ω =>
        Real.log
          (Z_interpol (N := N) (M := M) (β := β) (h := h)
            (skL := skL) (skN := skN) (skM := skM) 0 ω)] := by
        rfl
    _ = 𝔼[fun ω => fN ω + fM ω] := by
        simpa [Φ] using (integral_congr_ae hcongr)
    _ = 𝔼[fun ω => fN ω] + 𝔼[fun ω => fM ω] := by
        simpa using (integral_add (μ := (ℙ : Measure Ω)) hInt_fN hInt_fM)
    _ =
        (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U
          + (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U := by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
        -- Rewrite each `log` integral as `N * 𝔼[F_N]` using `free_energy_density`.
        have hN' :
            𝔼[fun ω => fN ω] =
              (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U := by
          -- Pull the constant `(N : ℝ)` into the integral, then cancel.
          symm
          calc
            (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U
                = 𝔼[fun ω =>
                    (N : ℝ) *
                      free_energy_density (N := N)
                        (skEnergy (N := N) (β := β) (h := h) (skN.U ω))] := by
                  simp [free_entropy, integral_const_mul]
            _ = 𝔼[fun ω => fN ω] := by
                  refine integral_congr_ae ?_
                  refine ae_of_all _ (fun ω => ?_)
                  simp [free_energy_density, skZ, fN, div_eq_mul_inv, hN0]
        have hM' :
            𝔼[fun ω => fM ω] =
              (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U := by
          -- Pull the constant `(M : ℝ)` into the integral, then cancel.
          symm
          calc
            (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U
                = 𝔼[fun ω =>
                    (M : ℝ) *
                      free_energy_density (N := M)
                        (skEnergy (N := M) (β := β) (h := h) (skM.U ω))] := by
                  simp [free_entropy, integral_const_mul]
            _ = 𝔼[fun ω => fM ω] := by
                  refine integral_congr_ae ?_
                  refine ae_of_all _ (fun ω => ?_)
                  simp [free_energy_density, skZ, fM, div_eq_mul_inv, hM0]
        -- Conclude by replacing both terms.
        simp [hN', hM']

end Endpoints

/-! ## 6. Covariance comparison along the interpolation (SK-specific) -/

section Covariance

variable {N M : ℕ} (β : ℝ)

-- The overlap used in `sk_cov_kernel` is already defined in `Defs.lean` as `SpinGlass.overlap`.

private lemma overlap_split (γ γ' : Config (N + M)) :
    overlap (N := N + M) γ γ'
      =
        ((N : ℝ) / (N + M : ℝ)) * overlap (N := N) (cfgLeft (N := N) (M := M) γ)
          (cfgLeft (N := N) (M := M) γ')
        +
        ((M : ℝ) / (N + M : ℝ)) * overlap (N := M) (cfgRight (N := N) (M := M) γ)
          (cfgRight (N := N) (M := M) γ') := by
  classical
  cases N with
  | zero =>
      cases M with
      | zero =>
          simp [overlap]
      | succ M =>
          have hM0 : (M.succ : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
          dsimp [overlap, cfgLeft, cfgRight, spin]
          simp [Fin.sum_univ_add]
          field_simp [hM0]
  | succ N =>
      cases M with
      | zero =>
          have hN0 : (N.succ : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
          dsimp [overlap, cfgLeft, cfgRight, spin]
          simp [Fin.sum_univ_add]
          field_simp [hN0] <;> simp only [mul_ite, mul_one, mul_neg_one]
      | succ M =>
          have hN0 : (N.succ : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
          have hM0 : (M.succ : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
          have hNMnat : N.succ + M.succ ≠ 0 := by
            simp [Nat.succ_add]
          have hNM0 : ((N.succ + M.succ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNMnat
          -- Expand overlaps and split the `Fin (N+M)` sum into the two blocks.
          -- `simp` also rewrites the spins of the restricted configurations.
          dsimp [overlap, cfgLeft, cfgRight, spin]
          simp [Fin.sum_univ_add]
          field_simp [hN0, hM0, hNM0] <;> simp only [mul_ite, mul_one, mul_neg_one]

private lemma sq_le_weighted_sq (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
  -- Standard two-point Jensen / convexity of `x ↦ x^2`.
  -- One clean proof is `a*b*(x-y)^2 ≥ 0` after using `hab` to rewrite `1-a=b`.
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha_le_one : a ≤ 1 := by linarith
  have hnonneg : 0 ≤ a * (1 - a) := mul_nonneg ha (sub_nonneg.2 ha_le_one)
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  have hprod : 0 ≤ a * (1 - a) * (x - y) ^ 2 := mul_nonneg hnonneg hsq
  have hident :
      a * x ^ 2 + (1 - a) * y ^ 2 - (a * x + (1 - a) * y) ^ 2 = a * (1 - a) * (x - y) ^ 2 := by
    ring
  have : 0 ≤ a * x ^ 2 + (1 - a) * y ^ 2 - (a * x + (1 - a) * y) ^ 2 := by
    simpa [hident] using hprod
  linarith

/--
The key covariance inequality (off-diagonal sign) used in Guerra–Toninelli:
after splitting `γ=(α,σ)`, convexity gives

`(N+M)/2 * overlap(γ,γ')^2 ≤ N/2 * overlap(α,α')^2 + M/2 * overlap(σ,σ')^2`.

Equivalently, the derivative of the interpolated covariance is nonpositive off the diagonal.
-/
lemma cov_deriv_offdiag_nonpos (hN : 0 < N) (hM : 0 < M)
    {γ γ' : Config (N + M)} :
    (sk_cov_kernel (N := N + M) (β := β) γ γ')
      ≤ (sk_cov_kernel (N := N) (β := β) (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ'))
        + (sk_cov_kernel (N := M) (β := β) (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ')) := by
  classical
  -- Set the block overlaps.
  set rN :=
    overlap (N := N) (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ') with hrN
  set rM :=
    overlap (N := M) (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ') with hrM
  have hden_pos : 0 < (N + M : ℝ) := by
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hMnonneg : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
    exact add_pos_of_pos_of_nonneg hNpos hMnonneg
  have hNM0 : (N + M : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hden_nonneg : 0 ≤ (N + M : ℝ) := le_of_lt hden_pos
  have ha : 0 ≤ (N : ℝ) / (N + M : ℝ) := by
    exact div_nonneg (Nat.cast_nonneg N) hden_nonneg
  have hb : 0 ≤ (M : ℝ) / (N + M : ℝ) := by
    exact div_nonneg (Nat.cast_nonneg M) hden_nonneg
  have hab : (N : ℝ) / (N + M : ℝ) + (M : ℝ) / (N + M : ℝ) = 1 := by
    field_simp [hNM0]
  have hsq :=
    sq_le_weighted_sq (a := (N : ℝ) / (N + M : ℝ)) (b := (M : ℝ) / (N + M : ℝ))
      (x := rN) (y := rM) ha hb hab
  have hover :
      overlap (N := N + M) γ γ'
        =
          ((N : ℝ) / (N + M : ℝ)) * rN + ((M : ℝ) / (N + M : ℝ)) * rM := by
    simpa [rN, rM] using
      (overlap_split (N := N) (M := M) γ γ')
  have hsq' :
      (overlap (N := N + M) γ γ') ^ 2
        ≤ ((N : ℝ) / (N + M : ℝ)) * rN ^ 2 + ((M : ℝ) / (N + M : ℝ)) * rM ^ 2 := by
    simpa [hover] using hsq
  have hcoef : 0 ≤ ((N + M : ℝ) * β ^ 2 / 2) := by positivity
  -- Multiply by the nonnegative prefactor and simplify.
  have :=
    (mul_le_mul_of_nonneg_left hsq' hcoef)
  -- `sk_cov_kernel` is `(N*β^2/2) * overlap^2`, so this is exactly the desired inequality.
  -- We simplify the weights by canceling `(N+M)` and distributing the prefactor.
  have hmulN :
      ((N : ℝ) / (N + M : ℝ)) * ((N + M : ℝ) * β ^ 2 / 2) = (N : ℝ) * β ^ 2 / 2 := by
    field_simp [hNM0]
  have hmulM :
      ((M : ℝ) / (N + M : ℝ)) * ((N + M : ℝ) * β ^ 2 / 2) = (M : ℝ) * β ^ 2 / 2 := by
    field_simp [hNM0]
  have h' :
      ((N + M : ℝ) * β ^ 2 / 2) * (overlap (N := N + M) γ γ') ^ 2
        ≤
        ((N : ℝ) * β ^ 2 / 2) * rN ^ 2 + ((M : ℝ) * β ^ 2 / 2) * rM ^ 2 := by
    -- Expand the RHS of `this` and rewrite the prefactor-times-weight products.
    have hNfactor :
        ((N : ℝ) / (N + M : ℝ)) * (((N + M : ℝ) * β ^ 2 / 2) * rN ^ 2)
          = ((N : ℝ) * β ^ 2 / 2) * rN ^ 2 := by
      calc
        ((N : ℝ) / (N + M : ℝ)) * (((N + M : ℝ) * β ^ 2 / 2) * rN ^ 2)
            = (((N : ℝ) / (N + M : ℝ)) * ((N + M : ℝ) * β ^ 2 / 2)) * rN ^ 2 := by
                simp [mul_assoc]
        _ = ((N : ℝ) * β ^ 2 / 2) * rN ^ 2 := by
                simp [hmulN]
    have hMfactor :
        ((M : ℝ) / (N + M : ℝ)) * (((N + M : ℝ) * β ^ 2 / 2) * rM ^ 2)
          = ((M : ℝ) * β ^ 2 / 2) * rM ^ 2 := by
      calc
        ((M : ℝ) / (N + M : ℝ)) * (((N + M : ℝ) * β ^ 2 / 2) * rM ^ 2)
            = (((M : ℝ) / (N + M : ℝ)) * ((N + M : ℝ) * β ^ 2 / 2)) * rM ^ 2 := by
                simp [mul_assoc]
        _ = ((M : ℝ) * β ^ 2 / 2) * rM ^ 2 := by
                simp [hmulM]
    -- Now simplify `this` using the two factorization identities.
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm, hNfactor, hMfactor] using this
  simpa [sk_cov_kernel, rN, rM] using h'

lemma cov_deriv_diag (hN : 0 < N) (hM : 0 < M) (γ : Config (N + M)) :
    (sk_cov_kernel (N := N + M) (β := β) γ γ)
      =
      (sk_cov_kernel (N := N) (β := β) (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ))
        + (sk_cov_kernel (N := M) (β := β) (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ)) := by
  -- Diagonal: all overlaps are 1, so this is just `(N+M)β^2/2 = Nβ^2/2 + Mβ^2/2`.
  classical
  have hNM : 0 < N + M := Nat.add_pos_left hN M
  have hN1 : overlap (N := N) (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ) = 1 := by
    simpa using overlap_self (N := N) (hN := hN) (cfgLeft (N := N) (M := M) γ)
  have hM1 : overlap (N := M) (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ) = 1 := by
    simpa using overlap_self (N := M) (hN := hM) (cfgRight (N := N) (M := M) γ)
  have hNM1 : overlap (N := N + M) γ γ = 1 := by
    simpa using overlap_self (N := N + M) (hN := hNM) γ
  -- Reduce overlaps to `1` and finish by linearity of division.
  simp [sk_cov_kernel, hN1, hM1, hNM1, Nat.cast_add, add_mul, add_div]

end Covariance

/-! ## 7. Guerra–Toninelli superadditivity (final statement, conditional on `hmono`) -/

section MainTheorem

variable {N M : ℕ} {β h : ℝ}
variable (skL : SKDisorder (Ω := Ω) (N + M) β h)
variable (skN : SKDisorder (Ω := Ω) N β h)
variable (skM : SKDisorder (Ω := Ω) M β h)

open scoped BigOperators

/-!
We name the two covariance kernels that enter the Guerra–Toninelli interpolation:

* `C_L` is the SK covariance kernel on `N+M` spins;
* `C_blk` is the block (decoupled) kernel coming from the `N`- and `M`-spin systems.

We also package the relevant Hessian entry of the (unnormalized) log-partition function:
it is `(N+M)` times the Hessian of the free energy density evaluated on standard basis vectors.
-/

private def C_L (γ γ' : Config (N + M)) : ℝ :=
  sk_cov_kernel (N := N + M) (β := β) γ γ'

private def C_blk (γ γ' : Config (N + M)) : ℝ :=
  sk_cov_kernel (N := N) (β := β)
      (cfgLeft (N := N) (M := M) γ) (cfgLeft (N := N) (M := M) γ')
    +
    sk_cov_kernel (N := M) (β := β)
      (cfgRight (N := N) (M := M) γ) (cfgRight (N := N) (M := M) γ')

private noncomputable def hessian_logZ_entry (K : EnergySpace (N + M)) (γ γ' : Config (N + M)) : ℝ :=
  (N + M : ℝ) *
    hessian_free_energy (N := N + M)
      (skEnergy (N := N + M) (β := β) (h := h) K)
      (std_basis (N := N + M) γ)
      (std_basis (N := N + M) γ')

theorem Φ_one_ge_zero (hN : 0 < N) (hM : 0 < M)
    (hmono :
      MonotoneOn
        (Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM))
        (Set.Icc (0 : ℝ) 1)) :
    Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 1
      ≥
    Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0 := by
  have _ : 0 < N := hN
  have _ : 0 < M := hM
  have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by simp
  have h11 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by simp
  exact hmono h01 h11 zero_le_one

/--
**Guerra–Toninelli inequality (SK model, blueprint).**

Assuming the Gaussian interpolation lemma for the interpolation `Φ(t)`,
we obtain superadditivity of the quenched log partition function:

`Q_{N+M}(β,h) ≥ Q_N(β,h) + Q_M(β,h)`.
-/
theorem guerra_toninelli_superadditive (_hβ : 0 < β) (hN : 0 < N) (hM : 0 < M)
    (hmono :
      MonotoneOn
        (Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM))
        (Set.Icc (0 : ℝ) 1)) :
    (N + M : ℝ) * free_entropy (N := N + M) (β := β) (h := h) skL.U
      ≥ (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U
        + (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U := by
  -- Strategy:
  -- 1) Define `Φ(t)` for the Guerra–Toninelli interpolation (`Interpolation.Φ`).
  -- 2) Prove `Φ` is increasing using the Gaussian interpolation lemma and covariance sign
  --    (`Covariance.cov_deriv_diag` + `Covariance.cov_deriv_offdiag_nonpos`).
  -- 3) Evaluate endpoints (`Endpoints.Z_interpol_one` and `Endpoints.Z_interpol_zero`).
  -- 4) Conclude `Φ(1) ≥ Φ(0)`.
  --
  -- The analytic comparison step (monotonicity of `Φ`) is assumed via `hmono`.
  have hΦ :
      Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 1
        ≥ Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0 :=
    Φ_one_ge_zero (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM)
      (hN := hN) (hM := hM) (hmono := hmono)
  have h1 :
      Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 1
        = (N + M : ℝ) * free_entropy (N := N + M) (β := β) (h := h) skL.U :=
    Z_interpol_one (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM)
      (hNM := Nat.add_pos_left hN M)
  have h0 :
      Φ (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM) 0
        =
        (N : ℝ) * free_entropy (N := N) (β := β) (h := h) skN.U
          + (M : ℝ) * free_entropy (N := M) (β := β) (h := h) skM.U :=
    Z_interpol_zero (N := N) (M := M) (β := β) (h := h) (skL := skL) (skN := skN) (skM := skM)
      (hN := hN) (hM := hM)
  simpa [h1, h0] using hΦ

end MainTheorem

/-! ## 8. Linear growth bound and thermodynamic limit (Fekete) -/

section ThermodynamicLimit

open scoped BigOperators
open Filter

/-- Superadditivity: `Q (m+n) ≥ Q m + Q n`. -/
def Superadditive (Q : ℕ → ℝ) : Prop :=
  ∀ m n, Q (m + n) ≥ Q m + Q n

lemma subadditive_neg_of_superadditive {Q : ℕ → ℝ} (hQ : Superadditive Q) :
    Subadditive (fun n : ℕ => -Q n) := by
  intro m n
  simpa [neg_add, add_comm, add_left_comm, add_assoc] using (neg_le_neg (hQ m n))

section AnnealedBound

variable {N : ℕ}

lemma abs_magnetization_le (σ : Config N) :
    |magnetization N σ| ≤ (N : ℝ) := by
  classical
  -- `|∑ spin| ≤ ∑ |spin| = N`.
  have hterm : ∀ i : Fin N, |spin N σ i| = (1 : ℝ) := by
    intro i
    cases hσ : σ i <;> simp [spin, hσ]
  have hsum :
      |∑ i : Fin N, spin N σ i| ≤ ∑ i : Fin N, |spin N σ i| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin N)))
        (f := fun i : Fin N => spin N σ i))
  calc
    |magnetization N σ|
        = |∑ i : Fin N, spin N σ i| := by rfl
    _ ≤ ∑ i : Fin N, |spin N σ i| := hsum
    _ = (N : ℝ) := by
        simp [hterm]

variable (h : ℝ)

lemma exp_magnetization_le (σ : Config N) :
    Real.exp (h * magnetization N σ) ≤ Real.exp (|h| * (N : ℝ)) := by
  have hle :
      h * magnetization N σ ≤ |h| * (N : ℝ) := by
    calc
      h * magnetization N σ
          ≤ |h * magnetization N σ| := le_abs_self _
      _ = |h| * |magnetization N σ| := by
            simp [abs_mul]
      _ ≤ |h| * (N : ℝ) := by
            exact mul_le_mul_of_nonneg_left (abs_magnetization_le (N := N) σ) (abs_nonneg h)
  exact Real.exp_le_exp.2 hle

section FreeEntropyLimit

open Filter

theorem free_entropy_tendsto_of_bddAbove
    (β h : ℝ) (hβ : 0 < β) (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h)
    (hΦmono :
      ∀ (N M : ℕ), 0 < N → 0 < M →
        MonotoneOn
          (Φ (N := N) (M := M) (β := β) (h := h)
            (skL := sk (N + M)) (skN := sk N) (skM := sk M))
          (Set.Icc (0 : ℝ) 1))
    (hbdd : BddAbove (Set.range fun N =>
      free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)) :
    ∃ ℓ : ℝ,
      Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U) atTop (𝓝 ℓ) := by
  classical
  -- Define `Q_N = N * s_N`.
  let Q : ℕ → ℝ :=
    fun N => (N : ℝ) * free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U
  have hQ : Superadditive Q := by
    intro m n
    cases m with
    | zero =>
        simp [Q]
    | succ m =>
        cases n with
        | zero =>
            simp [Q]
        | succ n =>
            -- Directly apply the superadditivity inequality for sizes `m+1` and `n+1`.
            simpa [Q] using
              (guerra_toninelli_superadditive (Ω := Ω) (N := m.succ) (M := n.succ) (β := β) (h := h)
                (skL := sk (m.succ + n.succ)) (skN := sk m.succ) (skM := sk n.succ)
                (_hβ := hβ) (hN := Nat.succ_pos _) (hM := Nat.succ_pos _)
                (hmono := hΦmono _ _ (Nat.succ_pos _) (Nat.succ_pos _)))

  -- Apply Fekete to `-Q`.
  let u : ℕ → ℝ := fun n => -Q n
  have hu : Subadditive u := subadditive_neg_of_superadditive hQ
  -- Boundedness for Fekete: `u n / n = - (Q n / n)` is bounded below.
  rcases hbdd with ⟨B, hB⟩
  have hbdd' : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨min (-B) 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      simp [u, Q]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hsn : free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U ≤ B := by
        exact hB ⟨n, rfl⟩
      have hneg : -B ≤ -free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
        simpa using (neg_le_neg hsn)
      have hmin : min (-B) 0 ≤ -B := min_le_left _ _
      -- `u n / n = - free_entropy n` for `n ≠ 0`
      have hun : u n / n = -free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
        -- cancel the factor `n` in `Q n = n * s n`
        have :
            Q n / n = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
          calc
            Q n / n
                = ((n : ℝ) * free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U) / n := by
                    simp [Q]
            _ = (n : ℝ) * (free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U * (n : ℝ)⁻¹) := by
                    simp [div_eq_mul_inv, mul_assoc]
            _ = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
                    -- `n * (s * n⁻¹) = s`
                    calc
                      (n : ℝ) * (free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U * (n : ℝ)⁻¹)
                          = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U *
                              ((n : ℝ) * (n : ℝ)⁻¹) := by
                                ac_rfl
                      _ = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
                                simp [hn']
        simp [u, neg_div, this]
      -- use the lower bound `min (-B) 0 ≤ -B ≤ u n / n`
      have : -B ≤ u n / n := by simpa [hun] using hneg
      exact hmin.trans this

  refine ⟨-hu.lim, ?_⟩
  have ht : Tendsto (fun n => u n / n) atTop (𝓝 hu.lim) :=
    Subadditive.tendsto_lim (h := hu) hbdd'
  have ht' : Tendsto (fun n => Q n / n) atTop (𝓝 (-hu.lim)) := by
    -- negate the convergence of `u n / n`
    have hneg := Tendsto.neg ht
    -- `-(u n / n) = Q n / n`
    have : (fun n => - (u n / n)) = fun n => Q n / n := by
      funext n
      simp [u, neg_div]
    simpa [this] using hneg
  -- `Q n / n = free_entropy` eventually.
  have hEq : (fun n => Q n / n) =ᶠ[atTop]
      fun n => free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      Q n / n
          = ((n : ℝ) * free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U) / n := by
              simp [Q]
      _ = (n : ℝ) * (free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U * (n : ℝ)⁻¹) := by
              simp [div_eq_mul_inv, mul_assoc]
      _ = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
              -- `n * (s * n⁻¹) = s`
              calc
                (n : ℝ) * (free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U * (n : ℝ)⁻¹)
                    =
                  free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U *
                    ((n : ℝ) * (n : ℝ)⁻¹) := by
                      ac_rfl
                _ = free_entropy (Ω := Ω) (N := n) (β := β) (h := h) (sk n).U := by
                      simp [hn']
  exact ht'.congr' hEq

end FreeEntropyLimit

end AnnealedBound

end ThermodynamicLimit

end

end SpinGlass
