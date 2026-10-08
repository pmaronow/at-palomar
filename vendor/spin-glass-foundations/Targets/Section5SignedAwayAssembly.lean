module

public import Targets.Section5PositiveAwayAssembly
public import Targets.Section5NegativeAwayAssembly

@[expose] public section

/-!
# Joining the positive and negative away regions

The regional analysis naturally treats nonnegative and nonpositive overlaps
separately.  This file takes the minimum of their two uniform deficits and
produces the single signed estimate used by the final quadratic assembly.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_signed_away_at_level
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t₀ η : ℝ}
    (hpos : ∃ c > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∀ u ∈ Set.Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c)
    (hneg : ∃ c > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∀ u ∈ Set.Icc (-1 : ℝ) 0, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c) :
    ∃ c > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∀ u ∈ Set.Icc (-1 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨cp, hcp, Hp⟩ := hpos
  obtain ⟨cn, hcn, Hn⟩ := hneg
  refine ⟨min cp cn, lt_min hcp hcn, ?_⟩
  intro t ht u hu haway n hn sk hatt
  by_cases hu0 : 0 ≤ u
  · have H := Hp t ht u ⟨hu0, hu.2⟩ haway hn sk hatt
    linarith [min_le_left cp cn]
  · have H := Hn t ht u ⟨hu.1, le_of_not_ge hu0⟩ haway hn sk hatt
    linarith [min_le_right cp cn]

end SpinGlass.Targets
