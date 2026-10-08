module

public import Targets.Section5LeftOffDiagonalTube
public import Targets.Section5PositiveAwayPhysicalCore
public import Targets.Section5PositiveAwayOuterPieces
public import Targets.Section5PositiveAwayTerminalTube

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
This adapter records exactly what the direct physical-left tube contributes to
the positive-away quantifier.  It is deliberately restricted to the tube
around `q_(r-1)`; the complementary central band still requires an independent
scalar gap and is not silently discharged here.
-/
theorem exists_uniform_constrainedPhi_positive_away_on_left_tube
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v t₀ η : ℝ}
    (hv : v ∈ Icc (s.q (r - 1)) (s.q r)) (ht₀ : t₀ < 1)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ,
        0 < section5LeftOffDiagonalDeficit s β h r m ℓ t v v) :
    ∃ ρ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u - v| ≤ ρ → η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨ρ, hρ, c, hc, H⟩ :=
    exists_uniform_constrainedPhi_left_physical_tube (Ω := Ω) s β h hr0 hr hv ht₀ hboundary
  exact ⟨ρ, hρ, c, hc, fun t ht u hu _hu n hn sk hatt =>
    H t ht u hu hn sk hatt⟩

end SpinGlass.Targets
