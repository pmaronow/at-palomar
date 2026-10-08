module

public import Targets.Section5RightOffDiagonal
public import Targets.Section5ScalarComparisonWitness
public import Targets.Section5FarLeft
public import Targets.Section5CompactWitness

@[expose] public section

/-!
# Right physical-neighbor endpoint witnesses

At the right endpoint of a physical interval the constrained and trial
overlaps agree.  The off-diagonal comparison therefore specializes exactly
to the already proved right scalar comparison.  This file records that
adapter and the finite-cover consequence on the whole time segment
`[0,t₀]`.  The latter is useful when the endpoint is approached from the
next trial interval: the trial overlap remains an independent parameter in
`Section5RightOffDiagonal`.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- At the right physical endpoint, the off-diagonal scalar family has the
same positive witness as the ordinary right comparison.  The assumptions
are exactly the uniform far-smallness assumptions used by Proposition 5.5;
no finite-system inequality is used to manufacture the witness. -/
theorem exists_section5RightOffDiagonalComparison_witness_at_physical_neighbor
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : s.m (r - 1) < s.m r) (hq : s.q r < s.q (r + 1))
    {L₁ t₀ t : ℝ} (hL : 0 < L₁) (ht₀ : t₀ < 1)
    (ht : t ∈ Set.Icc 0 t₀)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (s.q (r + 1) - s.q r))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r), ∃ ℓ : ℝ,
      0 < section5RightOffDiagonalComparisonDeficit s β h r m ℓ
        (t, (s.q (r + 1), s.q (r + 1))) := by
  have hsmall' : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (s.q (r + 1) - s.q r) ^ 2 := by
    exact section5FarLeft_smallness hβ hL ht₀ ht.2 hfar hsmall
  obtain ⟨m, hm, ℓ, H⟩ := exists_section5RightComparison_witness_of_gap
    s β h ε hr0 hr hmass (⟨ht.1, ht.2.trans ht₀.le⟩ : t ∈ Set.Icc 0 1)
    ⟨hq.le, le_rfl⟩ hmin hnear hsmall'
  refine ⟨m, hm, ℓ, ?_⟩
  simpa only [section5RightOffDiagonalComparisonDeficit_diag] using H

/-- A single positive deficit works uniformly for every time in `[0,t₀]` at
the right physical endpoint.  The auxiliary mass and lambda may vary in the
finite-cover proof, but the resulting `δ` is chosen before the system size
and disorder. -/
theorem exists_constrainedPhi_compact_right_physical_neighbor_gap
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : s.m (r - 1) < s.m r) (hq : s.q r < s.q (r + 1))
    {L₁ t₀ : ℝ} (hL : 0 < L₁) (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (s.q (r + 1) - s.q r))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ {t : ℝ}, t ∈ Set.Icc 0 t₀ →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      Nonempty (AT.ConstrainedPair n (s.q (r + 1))) →
        constrainedPhi n s β h sk.U (k + 2 - r) t (s.q (r + 1)) ≤
          2 * guerraPsi s β h t - δ := by
  let S : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0 : ℝ) t₀ ×ˢ
      ({s.q (r + 1)} ×ˢ {s.q (r + 1)})
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod (isCompact_singleton.prod isCompact_singleton)
  let I := {m : ℝ // m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r)} × ℝ
  let f := fun (i : I) =>
    section5RightOffDiagonalComparisonDeficit s β h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S := by
    dsimp [f]
    exact (continuous_section5RightOffDiagonalComparisonDeficit s β h hr
      ((s.m_nonneg (by omega)).trans i.1.2.1) i.2).continuousOn
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    rcases z with ⟨tz, ⟨uz, vz⟩⟩
    have ht : tz ∈ Set.Icc (0 : ℝ) t₀ := hz.1
    have hz₁ : uz = s.q (r + 1) := by
      simpa only [Set.mem_singleton_iff] using hz.2.1
    have hz₂ : vz = s.q (r + 1) := by
      simpa only [Set.mem_singleton_iff] using hz.2.2
    obtain ⟨m, hm, ℓ, H⟩ :=
      exists_section5RightOffDiagonalComparison_witness_at_physical_neighbor
        s β h ε hr0 hr hβ hmass hq hL ht₀ ht hmin hnear hfar hsmall
    refine ⟨(⟨m, hm⟩, ℓ), ?_⟩
    rw [hz₁, hz₂]
    simpa only [f, section5RightOffDiagonalComparisonDeficit_diag] using H
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro t ht n hn sk hatt
  letI := hatt
  let z : ℝ × (ℝ × ℝ) := (t, (s.q (r + 1), s.q (r + 1)))
  have hz : z ∈ S := by
    exact ⟨ht, by simp [z]⟩
  obtain ⟨i, hi⟩ := Hδ z hz
  have H := constrainedPhi_le_section5RightComparison hn s β h sk hr0 hr
    i.1.2 ⟨ht.1, ht.2.trans ht₀.le⟩ ⟨hq.le, le_rfl⟩ i.2
  dsimp [f] at hi
  have hi' : δ ≤ 2 * guerraPsi s β h t -
      section5RightComparison s β h r i.1.1 i.2 (t, s.q (r + 1)) := by
    simpa only [z, section5RightOffDiagonalComparisonDeficit_diag,
      section5RightComparisonDeficit] using hi
  linarith

end SpinGlass.Targets
