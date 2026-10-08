module

public import Targets.Section5RightPhysicalNeighborTube
public import Targets.Section5PositiveAwayOuterPieces
public import Targets.Section5PositiveAwayTerminalTube
public import Targets.Section5FiniteGapCover
public import Targets.Section5OutsideIntervals
public import Targets.Section5AdjacentStationaryCompact

@[expose] public section

/-! Positive right-hand assembly at the initial physical level. -/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Uniform tube around the first right neighbor `q₂`, including the
degenerate `q₁=0` case. -/
theorem exists_uniform_constrainedPhi_initial_q2_tube
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hk : 1 ≤ k)
    (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      |u - s.q 2| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hm01 := hmass 0 (by omega)
  have hq12 := hqstrict 1 (by omega) hk
  rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hqzero | hqpos
  · exact exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_initial_zero_unconditional
      (Ω := Ω) s β h ε hk hβ hqzero.symm hm01 hq12 ht₀ hmin hnear hsmall hfar
  · have hleft : s.q (1 - 1) < s.q 1 := by simpa only [Nat.sub_self, s.q_zero] using hqpos
    simpa only [show k + 2 - 1 = k + 1 by omega] using
      (exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_unconditional
        (Ω := Ω) s β h ε (r := 1) le_rfl (by omega) hβ hm01 hleft
          (Or.inl hq12) hq12 ht₀ hmin hnear hsmall hfar)

/-- Complete initial-level right side for the depth-one scheme (`k=1`). -/
theorem exists_uniform_constrainedPhi_positive_away_initial_right_k1
    (s : RSBScheme 1) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ 1 → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ 1 → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (_hη : 0 < η)
    (hmin : ∀ s' : RSBScheme 1,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q 2) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 2 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨ρ0, hρ0, δ0, hδ0, Htube⟩ :=
    exists_uniform_constrainedPhi_initial_q2_tube (Ω := Ω)
      s β h ε (by omega) hβ hmass hqstrict ht₀ hmin hnear hsmall hfar
  have hm01 := hmass 0 (by omega)
  have hm12 := hmass 1 (by omega)
  have hq12 := hqstrict 1 (by omega) (by omega)
  have hleft : s.q 0 < s.q 1 ∨ s.q 1 = 0 := by
    rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hqzero | hqpos
    · exact Or.inr hqzero.symm
    · exact Or.inl (by simpa only [s.q_zero] using hqpos)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h le_rfl (by omega) hβ hm01 hleft (Or.inl hq12) hmin
  let ρ : ℝ := min ρ0 1 / 2
  have hρ : 0 < ρ := div_pos (lt_min hρ0 (by norm_num)) (by norm_num)
  have hρle : ρ ≤ ρ0 := by
    dsimp [ρ]
    nlinarith [min_le_left ρ0 1]
  let a := s.q 2 + ρ
  by_cases ha : a ≤ 1
  · obtain ⟨δt, hδt, Htail⟩ :=
      exists_uniform_constrainedPhi_positive_terminal_outer_piece
        (Ω := Ω) s β h hβ (r := 1) le_rfl (by omega)
          (by simpa only [show 1 + 1 = 2 by omega] using hm12)
          hq12 hQ ht₀ (by dsimp [a]; linarith) ha
    refine ⟨min δ0 δt, lt_min hδ0 hδt, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear2 : |u - s.q 2| ≤ ρ
    · have huI : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
      exact (Htube t ht u huI (hnear2.trans hρle) hn sk hatt).trans
        (by linarith [min_le_left δ0 δt])
    · have hlow : a ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear2
        dsimp [a]
        linarith
      have H := Htail (t, u) ⟨ht, ⟨hlow, hu.2⟩⟩ hn sk hatt
      simpa only [Prod.fst, Prod.snd] using
        H.trans (by linarith [min_le_right δ0 δt])
  · refine ⟨δ0, hδ0, ?_⟩
    intro t ht u hu haway n hn sk hatt
    have hnear2 : |u - s.q 2| ≤ ρ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      dsimp [a] at ha
      by_contra H
      have : ρ < u - s.q 2 := lt_of_not_ge H
      linarith [hu.2, ha]
    have huI : u ∈ Icc (-1 : ℝ) 1 :=
      ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
    exact Htube t ht u huI (hnear2.trans hρle) hn sk hatt

/-- Complete initial-level right side for the first nontrivial two-step scheme
(`k=2`).  The four pieces are the `q₂` physical-neighbor tube, the open
outside-trial band up to `q₃`, the terminal `q₃` tube, and the padded terminal
tail. -/
theorem exists_uniform_constrainedPhi_positive_away_initial_right_k2
    (s : RSBScheme 2) (β h ε : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ 2 → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ 2 → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (_hη : 0 < η)
    (hmin : ∀ s' : RSBScheme 2,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q 2) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 3 t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨ρ2raw, hρ2raw, δ2, hδ2, Hq2⟩ :=
    exists_uniform_constrainedPhi_initial_q2_tube (Ω := Ω)
      s β h ε (by omega) hβ hmass hqstrict ht₀ hmin hnear hsmall hfar
  let ρ2 : ℝ := min ρ2raw 1 / 2
  have hρ2 : 0 < ρ2 := div_pos (lt_min hρ2raw (by norm_num)) (by norm_num)
  have hρ2le : ρ2 ≤ ρ2raw := by
    dsimp [ρ2]
    nlinarith [min_le_left ρ2raw 1]
  have hmassFin : StrictMono (fun p : Fin 4 => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hm01 := hmass 0 (by omega)
  have hq12 := hqstrict 1 (by omega) (by omega)
  have hq23 := hqstrict 2 (by omega) (by omega)
  have hleft : s.q 0 < s.q 1 ∨ s.q 1 = 0 := by
    rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hqzero | hqpos
    · exact Or.inr hqzero.symm
    · exact Or.inl (by simpa only [s.q_zero] using hqpos)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h le_rfl (by omega) hβ hm01 hleft (Or.inl hq12) hmin
  let Smid : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q 2 + ρ2) (s.q 3)
  have hSmid : IsCompact Smid := by
    dsimp [Smid]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨δmid, hδmid, Hmid⟩ :=
    exists_uniform_constrainedPhi_right_outside_trial (Ω := Ω) s β h
      (r := 1) (j := 3) hβ (by omega) (by omega) (by omega) (by omega)
      (by omega) hmassFin hq12 hQ ht₀ hSmid
      (fun z hz => hz.1)
      (fun z hz => by
        have hstrict : s.q 2 < s.q 2 + ρ2 := by linarith [hρ2]
        exact ⟨hstrict.trans_le hz.2.1, hz.2.2⟩)
  obtain ⟨ρ3raw, hρ3raw, δ3, hδ3, Hq3⟩ :=
    exists_uniform_constrainedPhi_terminal_lower_tube (Ω := Ω)
      s β h ε (r := 1) (by omega) (by omega) hβ hmass hqstrict
        ht₀ hmin hnear
  let ρ3 : ℝ := min ρ3raw 1 / 2
  have hρ3 : 0 < ρ3 := div_pos (lt_min hρ3raw (by norm_num)) (by norm_num)
  have hρ3le : ρ3 ≤ ρ3raw := by
    dsimp [ρ3]
    nlinarith [min_le_left ρ3raw 1]
  let a : ℝ := s.q 3 + ρ3
  by_cases ha : a ≤ 1
  · have hm13 : s.m 1 < s.m 3 := by
      exact lt_trans (hmass 1 (by omega)) (by
        simpa only [show 2 + 1 = 3 by omega] using hmass 2 (by omega))
    obtain ⟨δtail, hδtail, Htail⟩ :=
      exists_uniform_constrainedPhi_positive_terminal_outer_piece
        (Ω := Ω) s β h hβ (r := 1) le_rfl (by omega) hm13 hq12 hQ
          ht₀ (by dsimp [a]; linarith [hρ3]) ha
    refine ⟨min (min (min δ2 δmid) δ3) δtail,
      lt_min (lt_min (lt_min hδ2 hδmid) hδ3) hδtail, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear2 : |u - s.q 2| ≤ ρ2
    · have huI : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
      have H := Hq2 t ht u huI (hnear2.trans hρ2le) hn sk hatt
      exact H.trans (by
        linarith [min_le_left δ2 δmid,
          min_le_left (min δ2 δmid) δ3,
          min_le_left (min (min δ2 δmid) δ3) δtail])
    · have hlow2 : s.q 2 + ρ2 ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear2
        linarith
      by_cases hu3 : u ≤ s.q 3
      · have H := Hmid (t, u) ⟨ht, ⟨hlow2, hu3⟩⟩ hn sk hatt
        simpa only [Prod.fst, Prod.snd] using H.trans (by
          linarith [min_le_right δ2 δmid,
            min_le_left (min δ2 δmid) δ3,
            min_le_left (min (min δ2 δmid) δ3) δtail])
      · have hq3u : s.q 3 ≤ u := le_of_not_ge hu3
        by_cases hnear3 : |u - s.q 3| ≤ ρ3
        · have H := Hq3 t ht u (hnear3.trans hρ3le) hn sk hatt
          exact H.trans (by
            linarith [min_le_right (min δ2 δmid) δ3,
              min_le_left (min (min δ2 δmid) δ3) δtail])
        · have htail : a ≤ u := by
            rw [abs_of_nonneg (sub_nonneg.mpr hq3u)] at hnear3
            dsimp [a]
            linarith
          have H := Htail (t, u) ⟨ht, ⟨htail, hu.2⟩⟩ hn sk hatt
          simpa only [Prod.fst, Prod.snd] using H.trans (by
            linarith [min_le_right (min (min δ2 δmid) δ3) δtail])
  · refine ⟨min (min δ2 δmid) δ3,
      lt_min (lt_min hδ2 hδmid) hδ3, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear2 : |u - s.q 2| ≤ ρ2
    · have huI : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
      have H := Hq2 t ht u huI (hnear2.trans hρ2le) hn sk hatt
      exact H.trans (by
        linarith [min_le_left δ2 δmid,
          min_le_left (min δ2 δmid) δ3])
    · have hlow2 : s.q 2 + ρ2 ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear2
        linarith
      by_cases hu3 : u ≤ s.q 3
      · have H := Hmid (t, u) ⟨ht, ⟨hlow2, hu3⟩⟩ hn sk hatt
        simpa only [Prod.fst, Prod.snd] using H.trans (by
          linarith [min_le_right δ2 δmid,
            min_le_left (min δ2 δmid) δ3])
      · have hq3u : s.q 3 ≤ u := le_of_not_ge hu3
        have hnear3 : |u - s.q 3| ≤ ρ3 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hq3u)]
          dsimp [a] at ha
          by_contra H
          have : ρ3 < u - s.q 3 := lt_of_not_ge H
          linarith [hu.2, ha]
        have H := Hq3 t ht u (hnear3.trans hρ3le) hn sk hatt
        exact H.trans (by linarith [min_le_right (min δ2 δmid) δ3])

/-- Complete initial-level right side for every scheme of depth at least
three.  After the `q₂` tube and the first open outside-trial band, a finite
family of adjacent stationary compact bands covers `[q₃,q_(k+1)]`; the
terminal tube and padded tail close the endpoint at `1`. -/
theorem exists_uniform_constrainedPhi_positive_away_initial_right_three_le
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hk : 3 ≤ k) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (_hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (s.q 2) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨ρ2raw, hρ2raw, δ2, hδ2, Hq2⟩ :=
    exists_uniform_constrainedPhi_initial_q2_tube (Ω := Ω)
      s β h ε (by omega) hβ hmass hqstrict ht₀ hmin hnear hsmall hfar
  let ρ2 : ℝ := min ρ2raw 1 / 2
  have hρ2 : 0 < ρ2 := div_pos (lt_min hρ2raw (by norm_num)) (by norm_num)
  have hρ2le : ρ2 ≤ ρ2raw := by
    dsimp [ρ2]
    nlinarith [min_le_left ρ2raw 1]
  have hmassFin : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hm01 := hmass 0 (by omega)
  have hq12 := hqstrict 1 (by omega) (by omega)
  have hq23 := hqstrict 2 (by omega) (by omega)
  have hleft : s.q 0 < s.q 1 ∨ s.q 1 = 0 := by
    rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hqzero | hqpos
    · exact Or.inr hqzero.symm
    · exact Or.inl (by simpa only [s.q_zero] using hqpos)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h le_rfl (by omega) hβ hm01 hleft (Or.inl hq12) hmin
  let Sfirst : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q 2 + ρ2) (s.q 3)
  have hSfirst : IsCompact Sfirst := by
    dsimp [Sfirst]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨δfirst, hδfirst, Hfirst⟩ :=
    exists_uniform_constrainedPhi_right_outside_trial (Ω := Ω) s β h
      (r := 1) (j := 3) hβ (by omega) (by omega) (by omega) (by omega)
      (by omega) hmassFin hq12 hQ ht₀ hSfirst
      (fun z hz => hz.1)
      (fun z hz => by
        have hstrict : s.q 2 < s.q 2 + ρ2 := by linarith [hρ2]
        exact ⟨hstrict.trans_le hz.2.1, hz.2.2⟩)
  let X : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q 3) (s.q (k + 1))
  let S : Fin (k + 2) → Set (ℝ × ℝ) := fun j =>
    if 3 ≤ j.val ∧ j.val ≤ k then
      X ∩ ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1)))
    else ∅
  have hS : ∀ j, IsCompact (S j) := by
    intro j
    by_cases hj : 3 ≤ j.val ∧ j.val ≤ k
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
    by_cases he : z.2 = s.q 3
    · let jj : Fin (k + 2) := ⟨3, by omega⟩
      have hjcond : 3 ≤ jj.val ∧ jj.val ≤ k := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q jj.val) (s.q (jj.val + 1))) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, Set.mem_univ _, ?_⟩
      dsimp [jj]
      exact ⟨he.ge, he.le.trans (s.q_mono' 4 (by omega) 3 (by omega))⟩
    · have huq : s.q 3 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm he)
      obtain ⟨j, hj0, hjr, hjtop, hjL, hjU⟩ :=
        section5OutsideRight_exists_interval (r := 2) s (by omega) huq hz.2.2
      let jj : Fin (k + 2) := ⟨j - 1, by omega⟩
      have hjcond : 3 ≤ jj.val ∧ jj.val ≤ k := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q jj.val) (s.q (jj.val + 1))) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, Set.mem_univ _, ?_⟩
      dsimp [jj]
      simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using ⟨hjL.le, hjU⟩
  have hgap : ∀ j, ∃ d > (0 : ℝ), ∀ z ∈ S j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - d := by
    intro j
    by_cases hj : 3 ≤ j.val ∧ j.val ≤ k
    · have hqj : s.q (j.val - 1) < s.q j.val := by
        simpa only [Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using
          hqstrict (j.val - 1) (by omega) (by omega)
      obtain ⟨d, hd, Hd⟩ :=
        exists_uniform_constrainedPhi_gap_on_adjacent_right_stationary
          (Ω := Ω) s β h (r := 1) (j := j.val) hβ (by omega) (by omega)
          (by omega) (by omega) (by omega) hmassFin hqj hq12 hQ ht₀
          (S := S j) (hS j)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1))) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact hz.1.1)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1))) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact (s.q_nonneg (p := j.val) (by omega)).trans hz.2.2.1)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q j.val) (s.q (j.val + 1))) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact ⟨hqj.trans_le hz.2.2.1, hz.2.2.2⟩)
      simpa only [show k + 2 - 1 = k + 1 by omega] using ⟨d, hd, Hd⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro z hz
      have he : S j = ∅ := by dsimp [S]; rw [if_neg hj]
      rw [he] at hz
      exact hz.elim
  obtain ⟨δouter, hδouter, Houter⟩ :=
    exists_uniform_constrainedPhi_gap_of_finite_compact_cover_at_level
      (Ω := Ω) s β h (k + 1) X S hS hcover hgap
  obtain ⟨ρt, hρt, δt, hδt, Hterminal⟩ :=
    exists_uniform_constrainedPhi_terminal_lower_tube (Ω := Ω)
      s β h ε (r := 1) (by omega) (by omega) hβ hmass hqstrict
        ht₀ hmin hnear
  let a : ℝ := s.q (k + 1) + ρt
  by_cases ha : a ≤ 1
  · have hm1top : s.m 1 < s.m (k + 1) := by
      exact (hmass 1 (by omega)).trans_le
        (s.m_mono' (k + 1) (by omega) 2 (by omega))
    obtain ⟨δtail, hδtail, Htail⟩ :=
      exists_uniform_constrainedPhi_positive_terminal_outer_piece
        (Ω := Ω) s β h hβ (r := 1) le_rfl (by omega) hm1top hq12 hQ
          ht₀ (by dsimp [a]; linarith [hρt]) ha
    refine ⟨min (min δ2 δfirst) (min δouter (min δt δtail)),
      lt_min (lt_min hδ2 hδfirst) (lt_min hδouter (lt_min hδt hδtail)), ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear2 : |u - s.q 2| ≤ ρ2
    · have huI : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
      have H := Hq2 t ht u huI (hnear2.trans hρ2le) hn sk hatt
      exact H.trans (by
        have hmin : min (min δ2 δfirst) (min δouter (min δt δtail)) ≤ δ2 :=
          (min_le_left _ _).trans (min_le_left _ _)
        linarith)
    · have hlow2 : s.q 2 + ρ2 ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear2
        linarith
      by_cases hu3 : u ≤ s.q 3
      · have H := Hfirst (t, u) ⟨ht, ⟨hlow2, hu3⟩⟩ hn sk hatt
        simpa only [Prod.fst, Prod.snd, show k + 2 - 1 = k + 1 by omega] using H.trans (by
          have hmin : min (min δ2 δfirst) (min δouter (min δt δtail)) ≤ δfirst :=
            (min_le_left _ _).trans (min_le_right _ _)
          linarith)
      · by_cases hterm : |u - s.q (k + 1)| ≤ ρt
        · have H := Hterminal t ht u hterm hn sk hatt
          exact H.trans (by
            have hmin : min (min δ2 δfirst) (min δouter (min δt δtail)) ≤ δt :=
              (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
            linarith)
        · by_cases htail : a ≤ u
          · have H := Htail (t, u) ⟨ht, ⟨htail, hu.2⟩⟩ hn sk hatt
            simpa only [Prod.fst, Prod.snd, show k + 2 - 1 = k + 1 by omega] using H.trans (by
              have hmin : min (min δ2 δfirst) (min δouter (min δt δtail)) ≤ δtail :=
                (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
              linarith)
          · have hutop : u ≤ s.q (k + 1) := by
              by_contra Hnot
              have htopu : s.q (k + 1) < u := lt_of_not_ge Hnot
              rw [abs_of_pos (sub_pos.mpr htopu)] at hterm
              dsimp [a] at htail
              linarith
            have H := Houter (t, u) ⟨ht, ⟨le_of_not_ge hu3, hutop⟩⟩ hn sk hatt
            exact H.trans (by
              have hmin : min (min δ2 δfirst) (min δouter (min δt δtail)) ≤ δouter :=
                (min_le_right _ _).trans (min_le_left _ _)
              linarith)
  · refine ⟨min (min δ2 δfirst) (min δouter δt),
      lt_min (lt_min hδ2 hδfirst) (lt_min hδouter hδt), ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear2 : |u - s.q 2| ≤ ρ2
    · have huI : u ∈ Icc (-1 : ℝ) 1 :=
        ⟨(by linarith [s.q_nonneg (p := 2) (by omega), hu.1]), hu.2⟩
      have H := Hq2 t ht u huI (hnear2.trans hρ2le) hn sk hatt
      exact H.trans (by
        have hmin : min (min δ2 δfirst) (min δouter δt) ≤ δ2 :=
          (min_le_left _ _).trans (min_le_left _ _)
        linarith)
    · have hlow2 : s.q 2 + ρ2 ≤ u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear2
        linarith
      by_cases hu3 : u ≤ s.q 3
      · have H := Hfirst (t, u) ⟨ht, ⟨hlow2, hu3⟩⟩ hn sk hatt
        simpa only [Prod.fst, Prod.snd, show k + 2 - 1 = k + 1 by omega] using H.trans (by
          have hmin : min (min δ2 δfirst) (min δouter δt) ≤ δfirst :=
            (min_le_left _ _).trans (min_le_right _ _)
          linarith)
      · by_cases hterm : |u - s.q (k + 1)| ≤ ρt
        · have H := Hterminal t ht u hterm hn sk hatt
          exact H.trans (by
            have hmin : min (min δ2 δfirst) (min δouter δt) ≤ δt :=
              (min_le_right _ _).trans (min_le_right _ _)
            linarith)
        · have hutop : u ≤ s.q (k + 1) := by
            by_contra Hnot
            have htopu : s.q (k + 1) < u := lt_of_not_ge Hnot
            rw [abs_of_pos (sub_pos.mpr htopu)] at hterm
            dsimp [a] at ha
            linarith [hu.2]
          have H := Houter (t, u) ⟨ht, ⟨le_of_not_ge hu3, hutop⟩⟩ hn sk hatt
          exact H.trans (by
            have hmin : min (min δ2 δfirst) (min δouter δt) ≤ δouter :=
              (min_le_right _ _).trans (min_le_left _ _)
            linarith)

/-- Unified initial-level right-side theorem. -/
theorem exists_uniform_constrainedPhi_positive_away_initial_right
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hk : 1 ≤ k) (hβ : β ≠ 0)
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
      ∀ u ∈ Icc (s.q 2) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - c := by
  by_cases hkone : k = 1
  · subst k
    simpa only [show 1 + 1 = 2 by omega] using
      (exists_uniform_constrainedPhi_positive_away_initial_right_k1
        (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar)
  · by_cases hktwo : k = 2
    · subst k
      simpa only [show 2 + 1 = 3 by omega] using
        (exists_uniform_constrainedPhi_positive_away_initial_right_k2
          (Ω := Ω) s β h ε hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar)
    · exact exists_uniform_constrainedPhi_positive_away_initial_right_three_le
        (Ω := Ω) s β h ε (by omega) hβ hmass hqstrict ht₀ hη
          hmin hnear hsmall hfar

end SpinGlass.Targets
