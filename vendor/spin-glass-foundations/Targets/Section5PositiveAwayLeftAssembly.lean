module

public import Targets.Section5PositiveAwayImmediateLeft
public import Targets.Section5AdjacentStationaryCompact
public import Targets.Section5FiniteGapCover
public import Targets.Section5OutsideIntervals

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
# Compact assembly below a physical left endpoint

The lower part of the left physical side is partitioned into the finitely
many stationary adjacent trial bands.  The last band is trimmed by the
direct-left endpoint tube; this includes the initial interval below `q₁` when
`r = 2` and `q₁ > 0`.
-/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_constrainedPhi_left_outer_and_immediate
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
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
    (hsep : s.q (r - 2) < s.q (r - 1))
    (hprevpos : 0 < s.q (r - 2)) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) (s.q (r - 1)),
      |u - s.q r| ≥ η → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hleft : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 :=
    (s.overlap_directions_of_strict hqstrict (by omega) hr).2
  have hmassFin : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hmassr : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hmass (r - 1) (by omega)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) hr hβ hmassr (Or.inl hleft) hright hmin
  have hr3 : 3 ≤ r := by
    by_contra hnot
    have hrEq : r = 2 := by omega
    subst r
    simpa [s.q_zero] using hprevpos
  obtain ⟨ρᵢ, hρᵢ, δᵢ, hδᵢ, Himmediate⟩ :=
    exists_uniform_constrainedPhi_immediate_left_band
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  let X : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (0 : ℝ) (s.q (r - 2))
  let S : Fin (k + 2) → Set (ℝ × ℝ) := fun j =>
    if 1 ≤ j.val ∧ j.val + 1 < r then
      X ∩ ((Set.univ : Set ℝ) ×ˢ Icc (s.q (j.val - 1)) (s.q j.val))
    else ∅
  have hS : ∀ j, IsCompact (S j) := by
    intro j
    by_cases hj : 1 ≤ j.val ∧ j.val + 1 < r
    · rw [show S j = X ∩
          ((Set.univ : Set ℝ) ×ˢ Icc (s.q (j.val - 1)) (s.q j.val)) by
          dsimp [S]; rw [if_pos hj]]
      exact (isCompact_Icc.prod isCompact_Icc).inter_right
        (isClosed_univ.prod isClosed_Icc)
    · have hEmpty : S j = ∅ := by
        dsimp [S]; rw [if_neg hj]
      rw [hEmpty]
      exact isCompact_empty
  have hcover : ∀ z ∈ X, ∃ j, z ∈ S j := by
    intro z hz
    have hu0 : 0 ≤ z.2 := hz.2.1
    have huq : z.2 < s.q (r - 1) := by
      exact lt_of_le_of_lt hz.2.2 hsep
    obtain ⟨j, hj0, hjr, hjk, hjL, hjU⟩ :=
      section5OutsideLeft_exists_interval s (r := r) (by omega) hr hu0 huq
    by_cases hjstationary : j + 1 < r
    · let jj : Fin (k + 2) := ⟨j, by omega⟩
      have hjcond : 1 ≤ jj.val ∧ jj.val + 1 < r := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q (jj.val - 1)) (s.q jj.val)) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, ?_⟩
      exact ⟨Set.mem_univ _, ⟨hjL, hjU.le⟩⟩
    · have hjr_eq : j + 1 = r := by omega
      have hjval : j = r - 1 := by omega
      have hpoint : z.2 = s.q (r - 2) := by
        have hlow : s.q (r - 2) ≤ z.2 := by
          have hidx : j - 1 = r - 2 := by omega
          rw [hidx] at hjL
          exact hjL
        exact le_antisymm hz.2.2 hlow
      let jj : Fin (k + 2) := ⟨r - 2, by omega⟩
      have hjcond : 1 ≤ jj.val ∧ jj.val + 1 < r := by
        dsimp [jj]
        omega
      refine ⟨jj, ?_⟩
      rw [show S jj = X ∩
        ((Set.univ : Set ℝ) ×ˢ Icc (s.q (jj.val - 1)) (s.q jj.val)) by
          dsimp [S]; rw [if_pos hjcond]]
      refine ⟨hz, Set.mem_univ _, ?_⟩
      have hidx : jj.val = r - 2 := by rfl
      rw [hidx]
      exact ⟨(s.q_mono' (r - 2) (by omega) (r - 3) (by omega)).trans hpoint.ge,
        hpoint.le⟩
  have hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ z ∈ S j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
    intro j
    by_cases hj : 1 ≤ j.val ∧ j.val + 1 < r
    · have hjk : j.val + 1 ≤ k + 1 := by omega
      have hqj : s.q j.val < s.q (j.val + 1) :=
        hqstrict j.val (by omega) (by omega)
      obtain ⟨δ, hδ, Hδ⟩ :=
        exists_uniform_constrainedPhi_gap_on_adjacent_left_stationary
          (Ω := Ω) s β h hβ hr hj.1 (by omega) hj.2 hmassFin hqj hleft hQ ht₀
          (S := S j) (hS j)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q (j.val - 1)) (s.q j.val)) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact hz.1.1)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q (j.val - 1)) (s.q j.val)) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact (s.q_nonneg (p := j.val - 1) (by omega)).trans hz.2.2.1)
          (fun z hz => by
            rw [show S j = X ∩
              ((Set.univ : Set ℝ) ×ˢ Icc (s.q (j.val - 1)) (s.q j.val)) by
                dsimp [S]; rw [if_pos hj]] at hz
            exact ⟨hz.2.2.1,
              lt_of_le_of_lt hz.2.2.2 hqj⟩)
      exact ⟨δ, hδ, Hδ⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro z hz
      have hEmpty : S j = ∅ := by
        dsimp [S]; rw [if_neg hj]
      rw [hEmpty] at hz
      exact hz.elim
  obtain ⟨δout, hδout, Hout⟩ :=
    exists_uniform_constrainedPhi_gap_of_finite_compact_cover_at_level
      (Ω := Ω) s β h (k + 2 - r) X S hS hcover hgap
  let ρ : ℝ := ρᵢ
  have hρ : 0 < ρ := by
    exact hρᵢ
  refine ⟨ρ, hρ, min δᵢ δout, lt_min hδᵢ hδout, ?_⟩
  intro t ht u hu haway n hn sk hatt
  by_cases hulow : u ≤ s.q (r - 2)
  · have H := Hout (t, u) ⟨ht, ⟨hu.1, hulow⟩⟩ hn sk hatt
    exact H.trans (by linarith [min_le_right δᵢ δout])
  · have hulower : s.q (r - 2) ≤ u := le_of_not_ge hulow
    have huq : u ≤ s.q (r - 1) := hu.2
    have hupper : u ≤ s.q r := le_trans huq (le_of_lt hleft)
    have hband : u ∈ Icc (s.q (r - 2)) (s.q r) := ⟨hulower, hupper⟩
    have H := Himmediate t ht u hband haway hn sk hatt
    have hcases : |u - s.q (r - 1)| ≤ ρ ∨
        u ≤ s.q (r - 1) - ρ := by
      by_cases hnear : |u - s.q (r - 1)| ≤ ρ
      · exact Or.inl hnear
      · right
        have habs : |u - s.q (r - 1)| = s.q (r - 1) - u := by
          rw [abs_of_nonpos (sub_nonpos.mpr huq)]
          ring
        rw [habs] at hnear
        linarith
    exact (H hcases).trans (by linarith [min_le_left δᵢ δout])

 /-- The zero lower-endpoint case is entirely covered by the direct
 left tube: when `q_(r-2)=0`, the lower-left compact remainder has collapsed
 to the endpoint and no stationary trial band is needed. -/
theorem exists_uniform_constrainedPhi_left_immediate_zero_endpoint
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
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
    (hzero : s.q (r - 2) = 0) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) (s.q (r - 1)),
      |u - s.q r| ≥ η → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  obtain ⟨ρ, hρ, δ, hδ, H⟩ :=
    exists_uniform_constrainedPhi_immediate_left_band
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  have hleft : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro t ht u hu haway n hn sk hatt
  have hband : u ∈ Icc (s.q (r - 2)) (s.q r) := by
    refine ⟨?_, ?_⟩
    · simpa [hzero] using hu.1
    · exact hu.2.trans (le_of_lt hleft)
  have hcases : |u - s.q (r - 1)| ≤ ρ ∨
      u ≤ s.q (r - 1) - ρ := by
    by_cases hnear' : |u - s.q (r - 1)| ≤ ρ
    · exact Or.inl hnear'
    · right
      rw [abs_of_nonpos (sub_nonpos.mpr hu.2)] at hnear'
      linarith
  exact H t ht u hband haway hn sk hatt hcases

/-! A uniform entry point for the complete positive left side.  The only
degenerate case is `q_(r-2)=0`, where the endpoint adapter above applies;
otherwise the finite stationary cover applies. -/
theorem exists_uniform_constrainedPhi_positive_away_left_at_level
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
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
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) (s.q (r - 1)),
      |u - s.q r| ≥ η → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  by_cases hzero : s.q (r - 2) = 0
  · exact exists_uniform_constrainedPhi_left_immediate_zero_endpoint
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar hzero
  · have hprevnonneg : 0 ≤ s.q (r - 2) :=
      s.q_nonneg (p := r - 2) (by omega)
    have hprevpos : 0 < s.q (r - 2) := lt_of_le_of_ne hprevnonneg (Ne.symm hzero)
    have hr3 : 3 ≤ r := by
      by_contra hnot
      have hrEq : r = 2 := by omega
      subst r
      simpa [s.q_zero] using hprevpos
    have hsep : s.q (r - 2) < s.q (r - 1) := by
      have H := hqstrict (r - 2) (by omega) (by omega)
      have hidx : r - 2 + 1 = r - 1 := by omega
      rw [hidx] at H
      exact H
    exact exists_uniform_constrainedPhi_left_outer_and_immediate
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
      hsep hprevpos

end SpinGlass.Targets
