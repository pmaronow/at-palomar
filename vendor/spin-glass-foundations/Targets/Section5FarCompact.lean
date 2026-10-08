module

public import Targets.Section5ScalarComparisonCompact
public import Targets.Section5FarLeft

@[expose] public section

/-!
# Compact far-left and far-right regions

The beta-only Section 5 smallness estimate is pointwise in the overlap gap.
On a compact region whose distance from the physical endpoint is uniformly
large, it supplies exactly the strict scalar hypothesis required by the
compact comparison lemmas.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_compact_far_left
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hmpos : 0 < s.m (r - 1))
    (hgap : s.m (r - 1) < s.m r) (hβ : β ≠ 0)
    {L₁ t₀ : ℝ} (hL : 0 < L₁) (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (r - 1)) (s.q r))
    (hfar : ∀ z ∈ S, 1 - t₀ ≤ L₁ * (s.q r - z.2))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  obtain ⟨δ, hδ, H⟩ := exists_constrainedPhi_compact_left_gap (Ω := Ω) s β h ε hr0 hr hmpos hgap hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) hu hmin hnear
    (fun z hz => section5FarLeft_smallness hβ hL ht₀ (ht z hz).2 (hfar z hz) hsmall)
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n z.2) := ⟨⟨(σ, τ), hστ⟩⟩
  exact H z hz hn sk inferInstance

theorem exists_uniform_constrainedPhi_compact_far_right
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hgap : s.m (r - 1) < s.m r)
    (hβ : β ≠ 0) {L₁ t₀ : ℝ} (hL : 0 < L₁) (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q r) (s.q (r + 1)))
    (hfar : ∀ z ∈ S, 1 - t₀ ≤ L₁ * (z.2 - s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  obtain ⟨δ, hδ, H⟩ := exists_constrainedPhi_compact_right_gap (Ω := Ω) s β h ε hr0 hr hgap hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) hu hmin hnear
    (fun z hz => section5FarLeft_smallness hβ hL ht₀ (ht z hz).2 (hfar z hz) hsmall)
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n z.2) := ⟨⟨(σ, τ), hστ⟩⟩
  exact H z hz hn sk inferInstance

end SpinGlass.Targets
