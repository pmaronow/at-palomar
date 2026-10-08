module

public import Targets.Section5PositiveAwayLeftAssembly
public import Targets.Section5PositiveAwayPhysicalCore

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! The finite assembly adapter for the positive half of the away region.
The only input not reconstructed here is the right-side outer estimate; its
exact quantified form is exposed as `hright`. -/
theorem exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2)
    (hright : ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q (r + 1)) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨cr, hcr, Hright⟩ := hright
  by_cases hr1 : r = 1
  · subst r
    obtain ⟨ci, hci, Hinitial⟩ :=
      exists_uniform_constrainedPhi_positive_away_initial_physical_core
        (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
    refine ⟨min ci cr, lt_min hci hcr, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hu1 : u ≤ s.q 1
    · have H := Hinitial t ht u hu haway (Or.inl ⟨hu.1, hu1⟩) hn sk hatt
      exact H.trans (by linarith [min_le_left ci cr])
    · have huq1 : s.q 1 ≤ u := le_of_not_ge hu1
      have hq2 : s.q 2 ≤ 1 := s.q_le_one (p := 2) (by omega)
      by_cases hu2 : u ≤ s.q 2
      · have H := Hinitial t ht u hu haway (Or.inr ⟨huq1, hu2⟩) hn sk hatt
        exact H.trans (by linarith [min_le_left ci cr])
      · have huq2 : s.q 2 ≤ u := le_of_not_ge hu2
        have H := Hright t ht u ⟨huq2, hu.2⟩ haway hn sk hatt
        exact H.trans (by linarith [min_le_right ci cr])
  · have hr2 : 2 ≤ r := by omega
    obtain ⟨_ρl, _hρl, cl, hcl, Hleft⟩ :=
      exists_uniform_constrainedPhi_positive_away_left_at_level
        (Ω := Ω) s β h ε hr2 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
    obtain ⟨cc, hcc, Hcore⟩ :=
      exists_uniform_constrainedPhi_positive_away_physical_core
        (Ω := Ω) s β h ε hr2 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
    refine ⟨min (min cl cc) cr, lt_min (lt_min hcl hcc) hcr, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hup : u ≤ s.q (r - 1)
    · have H := Hleft t ht u ⟨hu.1, hup⟩ haway hn sk hatt
      exact H.trans (by linarith [min_le_left cl cc, min_le_left (min cl cc) cr])
    · have hlow : s.q (r - 1) ≤ u := le_of_not_ge hup
      by_cases huq : u ≤ s.q r
      · have H := Hcore t ht u hu (Or.inl ⟨hlow, huq⟩) haway hn sk hatt
        have hmc : min cl cc ≤ cc := min_le_right _ _
        have hma : min (min cl cc) cr ≤ min cl cc := min_le_left _ _
        exact H.trans (by linarith)
      · have hqr : s.q r ≤ u := le_of_not_ge huq
        by_cases hunext : u ≤ s.q (r + 1)
        · have H := Hcore t ht u hu (Or.inr ⟨hqr, hunext⟩) haway hn sk hatt
          have hmc : min cl cc ≤ cc := min_le_right _ _
          have hma : min (min cl cc) cr ≤ min cl cc := min_le_left _ _
          exact H.trans (by linarith)
        · have hnext : s.q (r + 1) ≤ u := le_of_not_ge hunext
          have H := Hright t ht u ⟨hnext, hu.2⟩ haway hn sk hatt
          exact H.trans (by linarith [min_le_right (min cl cc) cr])

end SpinGlass.Targets
