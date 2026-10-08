module

public import Targets.Section5InterleavingFilter

@[expose] public section

/-!
# Stable sorting and deletion of a tagged zero-variance entry

The adjacent-trial gluing uses stable sorting on tagged entries.  Removing a
particular tag after sorting is the same as removing it before sorting.  This
is an exact list identity: equal sorting keys are allowed, because tags are
distinct and the non-strict sorting relation is antisymmetric on the tagged
entries themselves.
-/

namespace SpinGlass.Targets

open List

/-- Stable insertion sort commutes with deleting one occurrence from its
input list.  The statement is deliberately independent of the particular
mass key used by the Section 5 construction. -/
theorem insertionSort_erase_eq
    {α : Type*} [BEq α] [LawfulBEq α]
    {r : α → α → Prop} [DecidableRel r] [Std.Total r] [IsTrans α r]
    [Std.Antisymm r] {l : List α} (x : α) :
    (l.insertionSort r).erase x = (l.erase x).insertionSort r := by
  have hp : (l.insertionSort r).erase x ~ (l.erase x).insertionSort r := by
    exact (List.Perm.erase x (List.perm_insertionSort r l)).trans
      (List.perm_insertionSort r (l.erase x)).symm
  apply List.Perm.eq_of_pairwise' (r := r)
  · exact (List.pairwise_insertionSort r l).sublist List.erase_sublist
  · exact List.pairwise_insertionSort r (l.erase x)
  · exact hp

end SpinGlass.Targets
