module

public import Targets.Section5CompactWitness

@[expose] public section

/-!
# Finite compact-cover bookkeeping

The trial intervals form a finite family.  This lemma packages the harmless
minimum over their compact constants, while retaining the pointwise witness
choice inside each interval.  It is only bookkeeping: all scalar positivity
and continuity hypotheses remain explicit.
-/

open Set

namespace SpinGlass.Targets

theorem exists_uniform_positive_of_finite_compact_witnesses
    {J X I : Type*} [Fintype J] [TopologicalSpace X]
    (S : J → Set X) (f : J → I → X → ℝ)
    (hS : ∀ j, IsCompact (S j))
    (hf : ∀ j i, ContinuousOn (f j i) (S j))
    (hpos : ∀ j x, x ∈ S j → ∃ i, 0 < f j i x) :
    ∃ δ > (0 : ℝ), ∀ j x, x ∈ S j → ∃ i, δ ≤ f j i x := by
  classical
  have H (j : J) : ∃ δ > (0 : ℝ), ∀ x ∈ S j, ∃ i, δ ≤ f j i x := by
    exact exists_uniform_positive_of_compact_witnesses (hS j) (f j)
      (fun i => hf j i) (fun x hx => hpos j x hx)
  choose δ hδ Hδ using H
  by_cases hne : (Finset.univ : Finset J).Nonempty
  · let δ₀ : ℝ := Finset.univ.inf' hne δ
    refine ⟨δ₀, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hne).mpr (fun j _ => hδ j)
    · intro j x hx
      exact (Hδ j x hx).imp fun i hi =>
        (Finset.inf'_le _ (Finset.mem_univ j)).trans hi
  · refine ⟨1, by norm_num, ?_⟩
    intro j
    exact (hne ⟨j, Finset.mem_univ j⟩).elim

end SpinGlass.Targets
