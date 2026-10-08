module

/- Compatibility adaptation: explicitly unfold sum-tag list filtering. -/
public import Targets.Section5Interleaving

@[expose] public section

/-!
# Recovering the source lists from the tagged interleaving

The stable sorting construction retains each physical and interpolation tag.
Filtering by its source recovers that source in its original order, even when
different tags have equal masses. These exact list identities support deletion
of the zero-variance operators at the interpolation endpoints; this module
does not itself identify the mixed vector cascade.
-/

namespace SpinGlass.Targets

/-- An enumeration whose left-tag positions are increasing recovers the entire
left source list when the right tags are removed. -/
theorem ofFn_filterMap_inl_of_strictMono {N A B : ℕ}
    (e : Fin N ≃ Fin A ⊕ Fin B)
    (he : StrictMono (fun p : Fin A => e.symm (Sum.inl p))) :
    (List.ofFn e).filterMap (Sum.elim some (fun _ => none)) = List.finRange A := by
  have hp : (List.ofFn e).Pairwise (fun a b => e.symm a < e.symm b) := by
    apply List.pairwise_ofFn.mpr
    intro p q hpq
    simpa only [Equiv.symm_apply_apply] using hpq
  have hs : ((List.ofFn e).filterMap (Sum.elim some (fun _ => none))).Pairwise
      (fun a b => a < b) := by
    apply hp.filterMap
    intro a a' haa b hab b' hab'
    cases a with
    | inl p =>
      cases a' with
      | inl q =>
        simp only [Sum.elim_inl, Option.some.injEq] at hab hab'
        subst b
        subst b'
        exact he.lt_iff_lt.mp haa
      | inr q => simp at hab'
    | inr p => simp at hab
  apply hs.eq_of_mem_iff (List.sortedLT_finRange A).pairwise
  intro p
  constructor
  · intro _
    exact List.mem_finRange p
  · intro _
    apply List.mem_filterMap.mpr
    exact ⟨Sum.inl p, List.mem_ofFn.mpr ⟨e.symm (Sum.inl p),
      e.apply_symm_apply (Sum.inl p)⟩, rfl⟩

/-- The corresponding recovery of the right source list. -/
theorem ofFn_filterMap_inr_of_strictMono {N A B : ℕ}
    (e : Fin N ≃ Fin A ⊕ Fin B)
    (he : StrictMono (fun p : Fin B => e.symm (Sum.inr p))) :
    (List.ofFn e).filterMap (Sum.elim (fun _ => none) some) = List.finRange B := by
  have hp : (List.ofFn e).Pairwise (fun a b => e.symm a < e.symm b) := by
    apply List.pairwise_ofFn.mpr
    intro p q hpq
    simpa only [Equiv.symm_apply_apply] using hpq
  have hs : ((List.ofFn e).filterMap (Sum.elim (fun _ => none) some)).Pairwise
      (fun a b => a < b) := by
    apply hp.filterMap
    intro a a' haa b hab b' hab'
    cases a with
    | inl p => simp at hab
    | inr p =>
      cases a' with
      | inl q => simp at hab'
      | inr q =>
        simp only [Sum.elim_inr, Option.some.injEq] at hab hab'
        subst b
        subst b'
        exact he.lt_iff_lt.mp haa
  apply hs.eq_of_mem_iff (List.sortedLT_finRange B).pairwise
  intro p
  constructor
  · intro _
    exact List.mem_finRange p
  · intro _
    apply List.mem_filterMap.mpr
    exact ⟨Sum.inr p, List.mem_ofFn.mpr ⟨e.symm (Sum.inr p),
      e.apply_symm_apply (Sum.inr p)⟩, rfl⟩

/-- Filtering the actual interleaving to physical tags preserves exactly the
original physical order, without a strict-mass hypothesis. -/
theorem section5Interleaving_filterMap_physical {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) :
    (List.ofFn (section5Interleaving s r j)).filterMap
      (Sum.elim some (fun _ => none)) = List.finRange (k + 2) :=
  ofFn_filterMap_inl_of_strictMono _ (strictMono_section5Interleaving_physical s r j)

/-- Filtering to interpolation tags preserves the inserted source order,
including its repeated inserted mass and zero-mass levels. -/
theorem section5Interleaving_filterMap_interpolating {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).filterMap
      (Sum.elim (fun _ => none) some) = List.finRange (k + 3) :=
  ofFn_filterMap_inr_of_strictMono _ (strictMono_section5Interleaving_interpolating s r hj)

private theorem filter_isLeft_eq_map_filterMap {α β : Type*} (l : List (α ⊕ β)) :
    l.filter Sum.isLeft =
      (l.filterMap (Sum.elim some (fun _ => none))).map Sum.inl := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp [List.filter_cons, List.filterMap_cons, Sum.isLeft, Sum.isRight, ih]

private theorem filter_isRight_eq_map_filterMap {α β : Type*} (l : List (α ⊕ β)) :
    l.filter Sum.isRight =
      (l.filterMap (Sum.elim (fun _ => none) some)).map Sum.inr := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp [List.filter_cons, List.filterMap_cons, Sum.isLeft, Sum.isRight, ih]

/-- Keeping the physical tags, rather than projecting them, recovers the
original tagged physical list. This form directly matches operator deletion. -/
theorem section5Interleaving_filter_physical {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) :
    (List.ofFn (section5Interleaving s r j)).filter Sum.isLeft =
      (List.finRange (k + 2)).map Sum.inl := by
  rw [filter_isLeft_eq_map_filterMap, section5Interleaving_filterMap_physical]

/-- The corresponding exact tagged list after deleting physical entries. -/
theorem section5Interleaving_filter_interpolating {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).filter Sum.isRight =
      (List.finRange (k + 3)).map Sum.inr := by
  rw [filter_isRight_eq_map_filterMap,
    section5Interleaving_filterMap_interpolating s r hj]

end SpinGlass.Targets
