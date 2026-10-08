module

public import Targets.Section5PositiveAwayConcreteAdapter
public import Targets.Section5RightPhysicalNeighborTube
public import Targets.Section5PositiveAwayInitialRight

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! Boundary assembly at the last physical level.  The right side is the
terminal point `q_(k+2)=1`, so the physical core itself supplies the explicit
right hypothesis required by the finite signed adapter. -/
theorem exists_uniform_constrainedPhi_positive_away_complete_last
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hβ : β ≠ 0)
    (hk : 1 ≤ k)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q (k + 1)| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - (k + 1)) t u ≤
        2 * guerraPsi s β h t - c := by
  have hqtop : s.q (k + 2) = 1 := s.q_top
  have hr : k + 1 ≤ k + 1 := le_rfl
  have hr0 : 2 ≤ k + 1 := by omega
  obtain ⟨cc, hcc, Hcore⟩ :=
    exists_uniform_constrainedPhi_positive_away_physical_core
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  have hright : ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q ((k + 1) + 1)) 1, η ≤ |u - s.q (k + 1)| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - (k + 1)) t u ≤
        2 * guerraPsi s β h t - c := by
    refine ⟨cc, hcc, ?_⟩
    intro t ht u hu haway n hn sk hatt
    have hu' : u ∈ Icc (s.q (k + 1)) (s.q (k + 2)) := by
      refine ⟨?_, ?_⟩
      · exact (s.q_mono' (k + 2) (by omega) (k + 1) (by omega)).trans hu.1
      · simpa only [hqtop] using hu.2
    have hu01 : u ∈ Icc (0 : ℝ) 1 := by
      exact ⟨(s.q_nonneg (p := k + 1) (by omega)).trans hu'.1,
        (by simpa only [hqtop] using hu'.2)⟩
    have H := Hcore t ht u hu01 (Or.inr hu') haway hn sk hatt
    simpa only [show k + 2 - (k + 1) = 1 by omega] using H
  exact exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
    (Ω := Ω) s β h ε (by omega) hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
    hright

/-! Degenerate one-step scheme (`k=0`).  Here `q₂=1`, so the initial
physical core already covers the whole positive overlap interval. -/
theorem exists_uniform_constrainedPhi_positive_away_complete_zero_scheme
    (s : RSBScheme 0) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ 0 → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ 0 → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme 0,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 1 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨c, hc, H⟩ :=
    exists_uniform_constrainedPhi_positive_away_initial_physical_core
      (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  refine ⟨c, hc, ?_⟩
  intro t ht u hu haway n hn sk hatt
  have hqtop : s.q 2 = 1 := s.q_top
  have hband : u ∈ Icc (0 : ℝ) (s.q 1) ∨
      u ∈ Icc (s.q 1) (s.q 2) := by
    by_cases hu1 : u ≤ s.q 1
    · exact Or.inl ⟨hu.1, hu1⟩
    · right
      exact ⟨le_of_not_ge hu1, by simpa [hqtop] using hu.2⟩
  exact H t ht u hu haway hband hn sk hatt

/-! The first nondegenerate scheme (`k=1`).  The initial core covers through
`q₂`; the checked last-level right/terminal assembly covers the remaining
terminal tail. -/
theorem exists_uniform_constrainedPhi_positive_away_complete_one_scheme
    (s : RSBScheme 1) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ 1 → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ 1 → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme 1,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 2 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨ci, hci, Hi⟩ :=
    exists_uniform_constrainedPhi_positive_away_initial_physical_core
      (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  obtain ⟨cr, hcr, Hr⟩ :=
    exists_uniform_constrainedPhi_positive_away_initial_right_k1
      (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  refine ⟨min ci cr, lt_min hci hcr, ?_⟩
  intro t ht u hu haway n hn sk hatt
  by_cases hu1 : u ≤ s.q 1
  · exact (Hi t ht u hu haway (Or.inl ⟨hu.1, hu1⟩) hn sk hatt).trans
      (by linarith [min_le_left ci cr])
  · have hlow1 : s.q 1 ≤ u := le_of_not_ge hu1
    by_cases hu2 : u ≤ s.q 2
    · exact (Hi t ht u hu haway (Or.inr ⟨hlow1, hu2⟩) hn sk hatt).trans
        (by linarith [min_le_left ci cr])
    · have hlow2 : s.q 2 ≤ u := le_of_not_ge hu2
      exact (Hr t ht u ⟨hlow2, hu.2⟩ haway hn sk hatt).trans
        (by linarith [min_le_right ci cr])

end SpinGlass.Targets
