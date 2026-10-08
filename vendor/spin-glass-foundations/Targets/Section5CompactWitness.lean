module

public import Targets.Section5InterleavedMajorant
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Compactness for continuous scalar witnesses

Strictness may use a different scalar witness at each parameter point. A
finite subcover selects a positive common gap; neither the witness selection
nor the constrained free energy needs to be continuous. Applications must
still prove continuity and strict positivity of their actual scalar family.
-/

open Set Filter Topology

namespace SpinGlass.Targets

/-- Continuous scalar witnesses that are pointwise strictly positive on a
compact set admit one uniformly positive bound. The witnessing index may
vary with the point and is not required to vary continuously. -/
theorem exists_uniform_positive_of_compact_witnesses
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    (f : I → X → ℝ) (hf : ∀ i, ContinuousOn (f i) S)
    (hpos : ∀ x ∈ S, ∃ i, 0 < f i x) :
    ∃ δ > (0 : ℝ), ∀ x ∈ S, ∃ i, δ ≤ f i x := by
  classical
  by_cases hne : S.Nonempty
  · letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    choose w hw using (fun x : S => hpos x x.property)
    let U : S → Set S := fun p => {x | f (w p) p / 2 < f (w p) x}
    have hopen : ∀ p, IsOpen (U p) := by
      intro p
      exact isOpen_lt continuous_const (continuousOn_iff_continuous_restrict.mp (hf (w p)))
    have hcover : (univ : Set S) ⊆ ⋃ p, U p := by
      intro x _
      exact mem_iUnion.mpr ⟨x, half_lt_self (hw x)⟩
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp (hT (mem_univ (⟨x, hx⟩ : S)))
      exact ⟨p, hp⟩
    refine ⟨T.inf' hTne (fun p => f (w p) p / 2), ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hTne).mpr (fun p _ => half_pos (hw p))
    · intro x hx
      obtain ⟨p, hp, H⟩ := mem_iUnion₂.mp (hT (mem_univ (⟨x, hx⟩ : S)))
      exact ⟨w p, (Finset.inf'_le _ hp).trans (le_of_lt H)⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end SpinGlass.Targets
