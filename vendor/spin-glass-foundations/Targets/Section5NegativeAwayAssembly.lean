module

public import Targets.Section5LocalCompactCover
public import Targets.Section5NegativeCompact
public import Targets.Section5NegativeInitialCompact
public import Targets.Section5NegativeInitialBeyondCompact
public import Targets.Section5NegativeInitialTerminalCompact
public import Targets.Section5PhysicalAwayCompact

@[expose] public section

/-!
# Negative-overlap compact assembly at one physical level

The negative region is assembled as an open-cover problem.  Away from the
deleted neighborhood of `q r`, each point is supplied with an admissible open
trial regime and a compact regional gap (from the negative, initial, or
terminal modules).  The compact local-gap theorem then extracts one deficit.
The point `u = 0` is intentionally included in the hypotheses: it is a
boundary crossing, and must be supplied by the physical-neighbor/off-diagonal
argument when it is not already covered by an open signed regime.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

def section5NegativeAwayRegion {k : ℕ} (s : RSBScheme k) (r : ℕ)
    (t₀ η : ℝ) : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) t₀ ×ˢ {u : ℝ | u ∈ Icc (-1 : ℝ) 0 ∧ η ≤ |u - s.q r|}

theorem isCompact_section5NegativeAwayRegion
    {k : ℕ} (s : RSBScheme k) (r : ℕ) {t₀ η : ℝ}
    (ht₀ : 0 ≤ t₀) :
    IsCompact (section5NegativeAwayRegion s r t₀ η) := by
  unfold section5NegativeAwayRegion
  apply isCompact_Icc.prod
  have habs : Continuous (fun u : ℝ => |u - s.q r|) := by fun_prop
  exact isCompact_Icc.inter_right (isClosed_le continuous_const habs)

/-- Uniform negative-overlap gap for the physical level `d = k + 2 - r`.
The local hypothesis is the exact obligation discharged by the signed
negative trial modules on ordinary open regimes, with a separate boundary
patch for `u = 0` when needed. -/
theorem exists_uniform_constrainedPhi_negative_away_at_level
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t₀ η : ℝ}
    (ht₀ : 0 ≤ t₀) (hη : 0 < η)
    (hlocal : ∀ z ∈ section5NegativeAwayRegion s r t₀ η,
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧
        ∃ δ > (0 : ℝ), ∀ y ∈ section5NegativeAwayRegion s r t₀ η,
          y ∈ U → ∀ {n : ℕ}, 0 < n →
          ∀ sk : SKDisorder (Ω := Ω) n β h,
          (∃ σ τ : Config n, overlap n σ τ = y.2) →
          constrainedPhi n s β h sk.U (k + 2 - r) y.1 y.2 ≤
            2 * guerraPsi s β h y.1 - δ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 0,
      η ≤ |u - s.q r| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let X := section5NegativeAwayRegion s r t₀ η
  let P : ℝ → (ℝ × ℝ) → Prop := fun δ z =>
    ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ
  have hmono : ∀ {a b : ℝ} {z : ℝ × ℝ}, 0 < b → b ≤ a → P a z → P b z := by
    intro a b z hb hba Ha n hn sk hatt
    have H := Ha hn sk hatt
    linarith
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_gap_of_compact_local_gaps
    (isCompact_section5NegativeAwayRegion s r ht₀) P hmono (by
      intro z hz
      obtain ⟨U, hU, hzU, δ, hδ, H⟩ := hlocal z hz
      exact ⟨U, hU, hzU, δ, hδ, by
        intro y hy hyU
        exact H y hy hyU⟩)
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu haway n hn sk hatt
  exact Hδ (t, u) ⟨ht, ⟨hu, haway⟩⟩ hn sk hatt

end SpinGlass.Targets
