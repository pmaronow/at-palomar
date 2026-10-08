module

public import Targets.Section5ScalarComparisonWitness
public import Targets.Section5CompactWitness

@[expose] public section

/-!
# Compact uniform far-neighbor free-energy gaps

The compactness argument uses the genuine continuous scalar comparisons,
indexed by an admissible fixed mass and lambda. At each parameter point,
optimality supplies such a strictly improving witness. A finite cover gives
one positive deficit before the parameter point, system size and disorder.
Neither the constrained free energy nor the witness selection is assumed
continuous in the constrained overlap.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A compact set of far-left neighboring points has one positive actual
free-energy deficit, uniformly over all its points and all system sizes.
The positive baseline is the genuine requirement of the downward mass move. -/
theorem exists_constrainedPhi_compact_left_gap
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Set.Icc 0 1)
    (hu : ∀ z ∈ S, z.2 ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - z.1) * (β ^ 2 / 2) * (s.q r - z.2) ^ 2) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      Nonempty (AT.ConstrainedPair n z.2) →
        constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
          2 * guerraPsi s β h z.1 - δ := by
  let I := {m : ℝ // m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r)} × ℝ
  let f := fun (i : I) => section5LeftComparisonDeficit s β h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S :=
    (continuous_section5LeftComparisonDeficit s β h hr
      ((div_nonneg hmpos.le (by norm_num)).trans i.1.2.1) i.2).continuousOn
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    obtain ⟨m, hm, ℓ, H⟩ := exists_section5LeftComparison_witness_of_gap s β h ε
      hr0 hr hmpos hgap (ht z hz) (hu z hz) hmin hnear (hsmall z hz)
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  letI := hatt
  obtain ⟨i, hi⟩ := Hδ z hz
  have H := constrainedPhi_le_section5LeftComparison hn s β h sk hr0 hr i.1.2
    (ht z hz) (hu z hz) i.2
  change δ ≤ 2 * guerraPsi s β h z.1 - section5LeftComparison s β h r i.1.1 i.2 z at hi
  exact H.trans (by linarith)

/-- The compact uniform far-right gap uses the original auxiliary mass
interval, including mass increases above one at the terminal level. -/
theorem exists_constrainedPhi_compact_right_gap
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Set.Icc 0 1)
    (hu : ∀ z ∈ S, z.2 ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : ∀ z ∈ S, 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - z.1) * (β ^ 2 / 2) * (z.2 - s.q r) ^ 2) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      Nonempty (AT.ConstrainedPair n z.2) →
        constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
          2 * guerraPsi s β h z.1 - δ := by
  let I := {m : ℝ // m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r)} × ℝ
  let f := fun (i : I) => section5RightComparisonDeficit s β h r i.1.1 i.2
  have hc (i : I) : ContinuousOn (f i) S :=
    (continuous_section5RightComparisonDeficit s β h hr
      ((s.m_nonneg (by omega)).trans i.1.2.1) i.2).continuousOn
  have hp : ∀ z ∈ S, ∃ i : I, 0 < f i z := by
    intro z hz
    obtain ⟨m, hm, ℓ, H⟩ := exists_section5RightComparison_witness_of_gap s β h ε
      hr0 hr hgap (ht z hz) (hu z hz) hmin hnear (hsmall z hz)
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  letI := hatt
  obtain ⟨i, hi⟩ := Hδ z hz
  have H := constrainedPhi_le_section5RightComparison hn s β h sk hr0 hr i.1.2
    (ht z hz) (hu z hz) i.2
  change δ ≤ 2 * guerraPsi s β h z.1 - section5RightComparison s β h r i.1.1 i.2 z at hi
  exact H.trans (by linarith)

end SpinGlass.Targets
