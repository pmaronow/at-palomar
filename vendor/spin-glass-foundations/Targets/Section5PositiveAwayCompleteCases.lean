module

public import Targets.Section5PositiveAwayComplete
public import Targets.Section5PositiveAwayRightAssembly
public import Targets.Section5PositiveAwayNearLast

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! Small wrappers which turn the checked right-hand assemblies into the
global positive-away estimate through the common finite-level adapter. -/

theorem exists_uniform_constrainedPhi_positive_away_complete_initial_k2
    (s : RSBScheme 2) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ 2 → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ 2 → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme 2,
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
      constrainedPhi n s β h sk.U 3 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨hright, hrightpos⟩ :=
    exists_uniform_constrainedPhi_positive_away_initial_right_k2
      (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  exact exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
    (Ω := Ω) s β h ε (r := 1) (by omega) (by omega) hβ hmass hqstrict
    ht₀ hη hmin hnear hsmall hfar ⟨hright, hrightpos⟩

theorem exists_uniform_constrainedPhi_positive_away_complete_right_outer
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hrk : r + 1 < k) (hβ : β ≠ 0)
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
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨cr, hcr, Hright⟩ :=
    exists_uniform_constrainedPhi_positive_away_right_outer_at_level
      (Ω := Ω) s β h ε hr0 hrk hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  exact exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
    (Ω := Ω) s β h ε (by omega) (by omega) hβ hmass hqstrict ht₀ hη hmin hnear
    hsmall hfar ⟨cr, hcr, Hright⟩

theorem exists_uniform_constrainedPhi_positive_away_complete_right_terminal
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hβ : β ≠ 0)
    (hkr : 2 ≤ k)
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
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q k| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 2 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨_ρ, _hρ, cr, hcr, Hright⟩ :=
    exists_uniform_constrainedPhi_right_outer_and_terminal_at_last
      (Ω := Ω) s β h ε hβ hkr hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  simpa only [show k + 2 - k = 2 by omega] using
    (exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
      (Ω := Ω) s β h ε (r := k) (by omega) (by omega) hβ hmass hqstrict
      ht₀ hη hmin hnear hsmall hfar ⟨cr, hcr, (by
        intro t ht u hu haway n hn sk hatt
        simpa only [show k + 2 - k = 2 by omega] using
        Hright t ht u hu haway hn sk hatt)⟩)

/-! Complete finite-level positive-away assembly.  The only case split is on
the finite breakpoint index; every branch is discharged by one of the
checked compact assemblies above and the common left/core adapter. -/
theorem exists_uniform_constrainedPhi_positive_away_complete
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
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  by_cases hk0 : k = 0
  · subst k
    have hr1 : r = 1 := by omega
    subst r
    simpa only [show 0 + 2 - 1 = 1 by omega] using
      (exists_uniform_constrainedPhi_positive_away_complete_zero_scheme
        (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar)
  · have hk1 : 1 ≤ k := by omega
    by_cases hrone : r = 1
    · subst r
      obtain ⟨cr, hcr, Hright⟩ :=
        exists_uniform_constrainedPhi_positive_away_initial_right
          (Ω := Ω) s β h ε hk1 hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
      simpa only [show k + 2 - 1 = k + 1 by omega] using
        (exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
          (Ω := Ω) s β h ε (r := 1) (by omega) (by omega) hβ hmass hqstrict
          ht₀ hη hmin hnear hsmall hfar ⟨cr, hcr, Hright⟩)
    · have hr2 : 2 ≤ r := by omega
      by_cases hrlast : r = k + 1
      · subst r
        simpa only [show k + 2 - (k + 1) = 1 by omega] using
          (exists_uniform_constrainedPhi_positive_away_complete_last
            (Ω := Ω) s β h ε hβ hk1 hmass hqstrict ht₀ hη hmin hnear hsmall hfar)
      · have hrk : r ≤ k := by omega
        by_cases hrk_eq : r = k
        · subst r
          simpa only [show k + 2 - k = 2 by omega] using
            (exists_uniform_constrainedPhi_positive_away_complete_right_terminal
              (Ω := Ω) s β h ε hβ (by omega) hmass hqstrict ht₀ hη hmin hnear
              hsmall hfar)
        · have hr_lt : r < k := by omega
          by_cases hnear_last : r + 1 = k
          · obtain ⟨cr, hcr, Hright⟩ :=
              exists_uniform_constrainedPhi_positive_away_near_last
                (Ω := Ω) s β h ε hr2 hnear_last hβ hmass hqstrict ht₀ hη
                hmin hnear hsmall hfar
            simpa only [show k + 2 - r = k + 2 - r by rfl] using
              (exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
                (Ω := Ω) s β h ε (by omega) (by omega) hβ hmass hqstrict ht₀ hη hmin
                hnear hsmall hfar ⟨cr, hcr, Hright⟩)
          · obtain ⟨cr, hcr, Hright⟩ :=
              exists_uniform_constrainedPhi_positive_away_right_outer_at_level
                (Ω := Ω) s β h ε hr2 (by omega) hβ hmass hqstrict ht₀ hη hmin
                hnear hsmall hfar
            exact exists_uniform_constrainedPhi_positive_away_concrete_at_level_of_right
              (Ω := Ω) s β h ε (by omega) (by omega) hβ hmass hqstrict ht₀ hη hmin
              hnear hsmall hfar ⟨cr, hcr, Hright⟩

end SpinGlass.Targets
