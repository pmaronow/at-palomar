module

public import Targets.Section5RightPhysicalNeighborTube
public import Targets.Section5PositiveAwayOuterPieces
public import Targets.Section5PositiveAwayTerminalTube
public import Targets.Section5FiniteGapCover
public import Targets.Section5OutsideIntervals
public import Targets.Section5AdjacentStationaryCompact

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! Finite right-side assembly away from a physical level.  This is the
nonterminal part (`2 ≤ r < k`); the last level is already handled by the
right-neighbor module. -/
theorem exists_uniform_constrainedPhi_positive_away_right_outer_at_level
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
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (s.q (r + 1)) 1,
      η ≤ |u - s.q r| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hrk' : r + 1 ≤ k := by omega
  have hr : r ≤ k + 1 := by omega
  have hqprev : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hqnext : s.q r < s.q (r + 1) := hqstrict r (by omega) (by omega)
  have hqnext2 : s.q (r + 1) < s.q (r + 2) :=
    hqstrict (r + 1) (by omega) (by omega)
  have hmassr : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hmass (r - 1) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := Or.inl hqnext
  obtain ⟨ρi, hρi, δi, hδi, Hi⟩ :=
    exists_uniform_constrainedPhi_immediate_right_band
      (Ω := Ω) s β h ε hr0 hrk' hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  obtain ⟨ρt, hρt, δt, hδt, Ht⟩ :=
    exists_uniform_constrainedPhi_terminal_lower_tube
      (Ω := Ω) s β h ε (r := r) (by omega) (by omega) hβ hmass hqstrict ht₀ hmin hnear
  let ρ : ℝ := min (min ρi ρt) ((s.q (r + 2) - s.q (r + 1)) / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (lt_min hρi hρt) (div_pos (sub_pos.mpr hqnext2) (by norm_num))
  have hρi' : ρ ≤ ρi := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρt' : ρ ≤ ρt := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρgap : ρ ≤ (s.q (r + 2) - s.q (r + 1)) / 2 := min_le_right _ _
  have hmassFin : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) hr hβ hmassr (Or.inl hqprev) hright hmin
  let X : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q (r + 2)) (s.q (k + 1))
  let S : Fin (k + 2) → Set (ℝ × ℝ) := fun j =>
    if r + 2 ≤ j.val ∧ j.val ≤ k then
      X ∩ ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1)))
    else ∅
  have hS : ∀ j, IsCompact (S j) := by
    intro j
    by_cases hj : r + 2 ≤ j.val ∧ j.val ≤ k
    · rw [show S j = X ∩
          ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1))) by
          dsimp [S]; rw [if_pos hj]]
      exact (isCompact_Icc.prod isCompact_Icc).inter_right
        (isClosed_univ.prod isClosed_Icc)
    · have he : S j = ∅ := by dsimp [S]; rw [if_neg hj]
      rw [he]
      exact isCompact_empty
  have hcover : ∀ z ∈ X, ∃ j, z ∈ S j := by
    intro z hz
    by_cases he : z.2 = s.q (r + 2)
    · let jj : Fin (k + 2) := ⟨r + 2, by omega⟩
      have hjcond : r + 2 ≤ jj.val ∧ jj.val ≤ k := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q jj.val) (s.q (jj.val + 1))) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, Set.mem_univ _, ?_⟩
      dsimp [jj]
      simpa [he] using (s.q_mono' (r + 3) (by omega)
        (r + 2) (by omega))
    · have huq : s.q (r + 2) < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm he)
      obtain ⟨j, hj0, hjr, hjtop, hjL, hjU⟩ :=
        section5OutsideRight_exists_interval (r := r + 1) s (by omega) huq hz.2.2
      let jj : Fin (k + 2) := ⟨j - 1, by omega⟩
      have hjcond : r + 2 ≤ jj.val ∧ jj.val ≤ k := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q jj.val) (s.q (jj.val + 1))) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, Set.mem_univ _, ?_⟩
      have hidx1 : jj.val = j - 1 := by rfl
      rw [hidx1]
      have hidx2 : j - 1 + 1 = j := by omega
      rw [hidx2]
      exact ⟨hjL.le, hjU⟩
  have hgap : ∀ j, ∃ d > (0 : ℝ), ∀ z ∈ S j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - d := by
    intro j
    by_cases hj : r + 2 ≤ j.val ∧ j.val ≤ k
    · have hqj : s.q (j.val - 1) < s.q j.val := by
        simpa only [Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using
          hqstrict (j.val - 1) (by omega) (by omega)
      obtain ⟨d, hd, Hd⟩ :=
        exists_uniform_constrainedPhi_positive_right_outer_piece
          (Ω := Ω) s β h hβ (r := r) (j := j.val)
          (by omega) hr (by omega) (by omega) (by omega)
          hmassFin hqj hqprev hqnext hmin ht₀
      exact ⟨d, hd, by
        intro z hz n hn sk hatt
        rw [show S j = X ∩
          ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1))) by
            dsimp [S]; rw [if_pos hj]] at hz
        exact Hd z ⟨hz.1.1, hz.2.2⟩ hn sk hatt⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro z hz
      have he : S j = ∅ := by dsimp [S]; rw [if_neg hj]
      rw [he] at hz
      exact hz.elim
  obtain ⟨douter, hdouter, Ho⟩ :=
    exists_uniform_constrainedPhi_gap_of_finite_compact_cover_at_level
      (Ω := Ω) s β h (k + 2 - r) X S hS hcover hgap
  let a : ℝ := s.q (k + 1) + ρt
  by_cases htail : a ≤ 1
  · let T : Set (ℝ × ℝ) := Icc (0 : ℝ) t₀ ×ˢ Icc a 1
    have hT : IsCompact T := by
      dsimp [T]
      exact isCompact_Icc.prod isCompact_Icc
    obtain ⟨dt, hdt, Htail⟩ := exists_uniform_constrainedPhi_positive_terminal_outer_piece
      (Ω := Ω) s β h hβ (by omega) (by omega)
      ((hmass r (by omega)).trans_le
        (s.m_mono' (k + 1) (by omega) (r + 1) (by omega))) hqnext hQ ht₀
      (by dsimp [a]; linarith) htail
    refine ⟨min (min δi douter) (min δt dt),
      lt_min (lt_min hδi hdouter) (lt_min hδt hdt), ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear : |u - s.q (r + 1)| ≤ ρ
    · have hu2 : u ≤ s.q (r + 2) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear
        linarith [hρgap]
      have H := Hi t ht u ⟨hqnext.le.trans hu.1, hu2⟩
        haway (Or.inl (hnear.trans hρi')) hn sk hatt
      have hmin : min (min δi douter) (min δt dt) ≤ δi :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      exact H.trans (by linarith)
    · have hnear' : s.q (r + 1) + ρ ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear
        linarith
      by_cases hterm : |u - s.q (k + 1)| ≤ ρt
      · have H := Ht t ht u hterm hn sk hatt
        have hmin : min (min δi douter) (min δt dt) ≤ δt :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        exact H.trans (by linarith)
      · by_cases hmid : u ≤ s.q (r + 2)
        · by_cases hnearI : |u - s.q (r + 1)| ≤ ρi
          · have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
              haway (Or.inl hnearI) hn sk hatt
            have hmin : min (min δi douter) (min δt dt) ≤ δi :=
              le_trans (min_le_left _ _) (min_le_left _ _)
            exact H.trans (by linarith)
          · have hnearI' : s.q (r + 1) + ρi ≤ u := by
              rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnearI
              linarith
            have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
              haway (Or.inr hnearI') hn sk hatt
            have hmin : min (min δi douter) (min δt dt) ≤ δi :=
              le_trans (min_le_left _ _) (min_le_left _ _)
            exact H.trans (by linarith)
        · by_cases htailu : a ≤ u
          · have H := Htail (t, u) ⟨ht, ⟨htailu, hu.2⟩⟩ hn sk hatt
            have hmin : min (min δi douter) (min δt dt) ≤ dt :=
              le_trans (min_le_right _ _) (min_le_right _ _)
            exact H.trans (by linarith)
          · have huo : u ≤ s.q (k + 1) := by
              by_contra hnot
              have hlt : s.q (k + 1) < u := lt_of_not_ge hnot
              rw [abs_of_pos (sub_pos.mpr hlt)] at hterm
              dsimp [a] at htailu
              linarith [hu.2]
            have H := Ho (t, u) ⟨ht, ⟨le_of_not_ge hmid, huo⟩⟩ hn sk hatt
            have hmin : min (min δi douter) (min δt dt) ≤ douter :=
              le_trans (min_le_left _ _) (min_le_right _ _)
            exact H.trans (by linarith)
  · refine ⟨min (min δi douter) δt,
      lt_min (lt_min hδi hdouter) hδt, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear : |u - s.q (r + 1)| ≤ ρ
    · have hu2 : u ≤ s.q (r + 2) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear
        linarith [hρgap]
      have H := Hi t ht u ⟨hqnext.le.trans hu.1, hu2⟩
        haway (Or.inl (hnear.trans hρi')) hn sk hatt
      exact H.trans (by
        have hmin : min (min δi douter) δt ≤ δi :=
          le_trans (min_le_left _ _) (min_le_left _ _)
        linarith)
    · have hnear' : s.q (r + 1) + ρ ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear
        linarith
      by_cases hterm : |u - s.q (k + 1)| ≤ ρt
      · have H := Ht t ht u hterm hn sk hatt
        exact H.trans (by
          have hmin : min (min δi douter) δt ≤ δt :=
            min_le_right _ _
          linarith)
      · by_cases hmid : u ≤ s.q (r + 2)
        · by_cases hnearI : |u - s.q (r + 1)| ≤ ρi
          · have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
              haway (Or.inl hnearI) hn sk hatt
            exact H.trans (by
              have hmin : min (min δi douter) δt ≤ δi :=
                le_trans (min_le_left _ _) (min_le_left _ _)
              linarith)
          · have hnearI' : s.q (r + 1) + ρi ≤ u := by
              rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnearI
              linarith
            have H := Hi t ht u ⟨hqnext.le.trans hu.1, hmid⟩
              haway (Or.inr hnearI') hn sk hatt
            exact H.trans (by
              have hmin : min (min δi douter) δt ≤ δi :=
                le_trans (min_le_left _ _) (min_le_left _ _)
              linarith)
        · have huo : u ≤ s.q (k + 1) := by
            by_contra hnot
            have hlt : s.q (k + 1) < u := lt_of_not_ge hnot
            rw [abs_of_pos (sub_pos.mpr hlt)] at hterm
            dsimp [a] at htail
            linarith [hu.2]
          have H := Ho (t, u) ⟨ht, ⟨le_of_not_ge hmid, huo⟩⟩ hn sk hatt
          exact H.trans (by
            have hmin : min (min δi douter) δt ≤ douter :=
              le_trans (min_le_left _ _) (min_le_right _ _)
            linarith)

end SpinGlass.Targets
