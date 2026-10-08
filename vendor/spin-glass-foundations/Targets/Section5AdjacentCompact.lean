module

public import Targets.Section5AdjacentDeficit
public import Targets.Section5InterleavedCompact

@[expose] public section

/-!
# Continuous gluing at an adjacent trial breakpoint

The scalar witnesses on neighboring trial intervals are continuous up to
their common breakpoint.  This module packages the elementary piecewise
continuity argument; it is the missing topological bridge needed before a
finite compact cover can include exact trial breakpoints.
-/

open MeasureTheory ProbabilityTheory Real Set Topology

namespace SpinGlass.Targets

noncomputable def section5InterleavedLambdaDeficit_adjacentGlue {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ} (ℓ : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 ≤ s.q j then
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ
  else
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ

set_option maxHeartbeats 10000000 in
theorem continuousOn_section5InterleavedLambdaDeficit_adjacentGlue {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ}
    (hj : j + 1 ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ)
      {z : ℝ × ℝ | z.2 ∈ Icc (s.q (j - 1)) (s.q (j + 1))} := by
  let S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ∈ Icc (s.q (j - 1)) (s.q (j + 1))}
  let p : (ℝ × ℝ) → Prop := fun z => z.2 ≤ s.q j
  let f : (ℝ × ℝ) → ℝ := fun z =>
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ
  let g : (ℝ × ℝ) → ℝ := fun z =>
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ
  have hclosed : IsClosed {z : ℝ × ℝ | p z} := by
    dsimp [p]
    exact isClosed_le continuous_snd continuous_const
  have hqnonneg (i : ℕ) (hi : i ≤ k + 2) : 0 ≤ s.q i := s.q_nonneg hi
  have hf : ContinuousOn f (S ∩ closure {z | p z}) := by
    have Hf := continuousOn_section5InterleavedLambdaDeficit_trial s β h r (j := j) (by omega) ℓ
    have Hf' : ContinuousOn (fun z =>
      section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ)
      (S ∩ closure {z | p z}) := by
      apply Hf.mono
      intro z hz
      have hp : p z := by
        rw [hclosed.closure_eq] at hz
        exact hz.2
      have hS := hz.1
      have hu0 : 0 ≤ z.2 :=
        (hqnonneg (j - 1) (by omega)).trans hS.1
      change |z.2| ∈ Icc (s.q (j - 1)) (s.q j)
      rw [abs_of_nonneg hu0]
      exact ⟨hS.1, hp⟩
    simpa only [f] using Hf'
  have hg : ContinuousOn g (S ∩ closure {z | ¬ p z}) := by
    have Hg' : ContinuousOn (fun z =>
      section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ)
      (S ∩ closure {z | ¬ p z}) := by
      have Hg := continuousOn_section5InterleavedLambdaDeficit_trial s β h r
        (j := j + 1) (by omega) ℓ
      apply Hg.mono
      intro z hz
      have hge : s.q j ≤ z.2 := by
        have hzcl : z ∈ closure {z | s.q j < z.2} := by
          simpa only [p, not_le] using hz.2
        exact closure_lt_subset_le continuous_const continuous_snd hzcl
      have hS := hz.1
      have hu0 : 0 ≤ z.2 :=
        (hqnonneg (j - 1) (by omega)).trans hS.1
      change |z.2| ∈ Icc (s.q ((j + 1) - 1)) (s.q (j + 1))
      rw [abs_of_nonneg hu0]
      exact ⟨hge, hS.2⟩
    exact Hg'
  have hboundary : ∀ z ∈ S ∩ frontier {z | p z}, f z = g z := by
    intro z hz
    have heq : z.2 = s.q j := by
      exact frontier_le_subset_eq continuous_snd continuous_const hz.2
    dsimp [f, g]
    rw [heq]
    exact section5InterleavedLambdaDeficit_adjacent_boundary s β h r (j := j) hj z.1 ℓ
  have H := ContinuousOn.if (s := S) (p := p) (f := f) (g := g)
    hboundary hf hg
  change ContinuousOn (fun z => if p z then f z else g z) S at H
  change ContinuousOn (fun z => if z.2 ≤ s.q j then
    section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ else
    section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ) S
  exact H

/-/ A compact positive-overlap band spanning two adjacent trial intervals can
be handled by the glued scalar witness.  The common breakpoint is included
because the two scalar deficits agree there. -/
theorem exists_uniform_constrainedPhi_gap_on_adjacent_trial
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j)
    (hj : j + 1 ≤ k + 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (huneg : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (j - 1)) (s.q (j + 1)))
    (hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hdom : S ⊆ {z : ℝ × ℝ | z.2 ∈ Icc (s.q (j - 1)) (s.q (j + 1))} := by
    intro z hz
    exact hu z hz
  have hcont (ℓ : ℝ) : ContinuousOn
      (section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ) S :=
    (continuousOn_section5InterleavedLambdaDeficit_adjacentGlue s β h r hj ℓ).mono hdom
  obtain ⟨δ, hδ, H⟩ := exists_uniform_positive_of_compact_witnesses hS
    (fun ℓ z => section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z)
    hcont hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨ℓ, hℓ⟩ := H z hz
  by_cases hleft : z.2 ≤ s.q j
  · have htrial : |z.2| ∈ Icc (s.q (j - 1)) (s.q j) := by
      rw [abs_of_nonneg (huneg z hz)]
      exact ⟨(hu z hz).1, hleft⟩
    have HB := constrainedPhi_le_guerraPsi_sub_interleavedLambdaDeficit hn s β h sk
      hr0 hr (j := j) hj0 (by omega) (ht z hz) htrial hatt ℓ
    have hglue : section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z =
        section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ := by
      simp only [section5InterleavedLambdaDeficit_adjacentGlue, hleft, ↓reduceIte]
    rw [hglue] at hℓ
    linarith
  · have hright : s.q j ≤ z.2 := le_of_not_ge hleft
    have htrial : |z.2| ∈ Icc (s.q j) (s.q (j + 1)) := by
      rw [abs_of_nonneg (huneg z hz)]
      exact ⟨hright, (hu z hz).2⟩
    have HB := constrainedPhi_le_guerraPsi_sub_interleavedLambdaDeficit hn s β h sk
      hr0 hr (by omega) (j := j + 1) (by omega) (ht z hz) htrial hatt ℓ
    have hglue : section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z =
        section5InterleavedLambdaDeficit s β h r (j + 1) z.1 z.2 ℓ := by
      simp only [section5InterleavedLambdaDeficit_adjacentGlue, hleft, ↓reduceIte]
    rw [hglue] at hℓ
    linarith

end SpinGlass.Targets
