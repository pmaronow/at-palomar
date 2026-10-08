module

public import Targets.Section5RightPhysicalNeighborTube
public import Targets.Section5PositiveAwayTerminalTube
public import Targets.Section5PositiveAwayOuterPieces

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! The near-last right region.  When `r + 1 = k`, the immediate right band
reaches the terminal breakpoint `q (k+1)`, so no nonterminal finite outer
pieces are needed. -/
theorem exists_uniform_constrainedPhi_positive_away_near_last
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hrlast : r + 1 = k) (hβ : β ≠ 0)
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
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q (r + 1)) 1,
      η ≤ |u - s.q r| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hrk : r + 1 ≤ k := by omega
  have hr : r ≤ k + 1 := by omega
  have hqprev : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hqnext : s.q r < s.q (r + 1) :=
    hqstrict r (by omega) (by omega)
  have hidx : r + 2 = k + 1 := by omega
  have hqterminal : s.q (r + 1) < s.q (r + 2) := by
    simpa only [hidx, hrlast] using hqstrict k (by omega) (by omega)
  have hqterminal_eq : s.q (r + 2) = s.q (k + 1) := by rw [hidx]
  have hmassr : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hmass (r - 1) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := Or.inl hqnext
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) hr hβ hmassr (Or.inl hqprev) hright hmin
  obtain ⟨ρi, hρi, δi, hδi, Hi⟩ :=
    exists_uniform_constrainedPhi_immediate_right_band
      (Ω := Ω) s β h ε hr0 hrk hβ hmass hqstrict ht₀ hη hmin hnear
        hsmall hfar
  obtain ⟨ρt, hρt, δt, hδt, Ht⟩ :=
    exists_uniform_constrainedPhi_terminal_lower_tube
      (Ω := Ω) s β h ε (r := r) (by omega) (by omega) hβ hmass hqstrict
        ht₀ hmin hnear
  let a : ℝ := s.q (k + 1) + ρt
  by_cases htail : a ≤ 1
  · obtain ⟨dt, hdt, Htail⟩ :=
      exists_uniform_constrainedPhi_positive_terminal_outer_piece
        (Ω := Ω) s β h hβ (by omega) (by omega)
        ((hmass r (by omega)).trans_le
          (s.m_mono' (k + 1) (by omega) (r + 1) (by omega)))
        hqnext hQ ht₀ (by dsimp [a]; linarith) htail
    refine ⟨min (min δi δt) dt,
      lt_min (lt_min hδi hδt) hdt, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hmid : u ≤ s.q (r + 2)
    · by_cases hnearI : |u - s.q (r + 1)| ≤ ρi
      · have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
          haway (Or.inl hnearI) hn sk hatt
        exact H.trans (by
          have hm' : min (min δi δt) dt ≤ δi :=
            le_trans (min_le_left _ _) (min_le_left _ _)
          linarith)
      · have hnearI' : s.q (r + 1) + ρi ≤ u := by
          rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnearI
          linarith
        have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
          haway (Or.inr hnearI') hn sk hatt
        exact H.trans (by
          have hm' : min (min δi δt) dt ≤ δi :=
            le_trans (min_le_left _ _) (min_le_left _ _)
          linarith)
    · by_cases hterm : |u - s.q (k + 1)| ≤ ρt
      · have H := Ht t ht u hterm hn sk hatt
        exact H.trans (by
          have hm' : min (min δi δt) dt ≤ δt :=
            le_trans (min_le_left _ _) (min_le_right _ _)
          linarith)
      · have htailu : a ≤ u := by
          dsimp [a]
          have huq : s.q (k + 1) ≤ u := by
            rw [← hqterminal_eq]
            exact le_of_not_ge hmid
          rw [abs_of_nonneg (sub_nonneg.mpr huq)] at hterm
          linarith
        have H := Htail (t, u) ⟨ht, ⟨htailu, hu.2⟩⟩ hn sk hatt
        exact H.trans (by
          have hm' : min (min δi δt) dt ≤ dt := min_le_right _ _
          linarith)
  · refine ⟨min δi δt, lt_min hδi hδt, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hmid : u ≤ s.q (r + 2)
    · by_cases hnearI : |u - s.q (r + 1)| ≤ ρi
      · have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
          haway (Or.inl hnearI) hn sk hatt
        exact H.trans (by
          have hm' : min δi δt ≤ δi := min_le_left _ _
          linarith)
      · have hnearI' : s.q (r + 1) + ρi ≤ u := by
          rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnearI
          linarith
        have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
          haway (Or.inr hnearI') hn sk hatt
        exact H.trans (by
          have hm' : min δi δt ≤ δi := min_le_left _ _
          linarith)
    · have hterm : |u - s.q (k + 1)| ≤ ρt := by
        have huq : s.q (k + 1) ≤ u := by
          rw [← hqterminal_eq]
          exact le_of_not_ge hmid
        rw [abs_of_nonneg (sub_nonneg.mpr huq)]
        dsimp [a] at htail
        by_contra hnterm
        have hlt : ρt < u - s.q (k + 1) := lt_of_not_ge hnterm
        linarith [hu.2, htail]
      exact Ht t ht u hterm hn sk hatt |>.trans (by
        have hm' : min δi δt ≤ δt := min_le_right _ _
        linarith)

end SpinGlass.Targets
