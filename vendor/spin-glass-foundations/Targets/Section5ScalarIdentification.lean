module

public import Targets.ParisiCascadeIdentification
public import Targets.Section5Interleaving

@[expose] public section

/-!
# Identification of the sorted tagged scalar endpoint

The scalar list is outermost first. Tagged entries are grouped by their
original level, using the actual variance identity (5.49), and each equal-mass
block is merged by the Gaussian semigroup. Sorting may reorder equal original
masses without changing the actual scalar cascade.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The scalar Gaussian operators attached to the actual paired-mass
interleaving, in forward (outermost-first) order. -/
noncomputable def section5InterleavedScalarSteps {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) : List (ℝ × ℝ) :=
  List.ofFn (fun i =>
    (section5TagScalarMass s r j (section5Interleaving s r j i),
     section5TaggedVariance s β t u j (section5Interleaving s r j i)))

/-- The actual nondecreasing-mass scalar rearrangement used in (5.50). -/
noncomputable def section5SortedScalarSteps {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) : List (ℝ × ℝ) := by
  classical
  exact (section5InterleavedScalarSteps s β t u r j).insertionSort
    (fun a b => a.1 ≤ b.1)

/-- Original scalar operators in forward order; the recursion `parisiF`
integrates these operators in reverse index order. -/
noncomputable def section5OriginalScalarSteps {k : ℕ} (s : RSBScheme k)
    (β : ℝ) : List (ℝ × ℝ) :=
  List.ofFn (fun p : Fin (k + 2) => (s.m p, β ^ 2 * (s.q (p + 1) - s.q p)))

private noncomputable def tagList {k : ℕ} (s : RSBScheme k) (r j : ℕ) :=
  List.ofFn (section5Interleaving s r j)

private noncomputable def levelBlock {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (p : Fin (k + 2)) :=
  (tagList s r j).filter (fun a => section5TagOriginalLevel j a = p)

private noncomputable def groupedTags {k : ℕ} (s : RSBScheme k) (r j : ℕ) :=
  (List.finRange (k + 2)).flatMap (levelBlock s r j)

private theorem tagList_nodup {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    (tagList s r j).Nodup := List.nodup_ofFn.mpr (section5Interleaving s r j).injective

private theorem mem_tagList {k : ℕ} (s : RSBScheme k) (r j : ℕ) (a : Section5MassTag k) :
    a ∈ tagList s r j := List.mem_ofFn.mpr ⟨(section5Interleaving s r j).symm a,
      (section5Interleaving s r j).apply_symm_apply a⟩

private theorem mem_levelBlock {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (p : Fin (k + 2)) (a : Section5MassTag k) :
    a ∈ levelBlock s r j p ↔ section5TagOriginalLevel j a = p := by
  simp only [levelBlock, List.mem_filter, decide_eq_true_eq,
    mem_tagList, true_and]

private theorem groupedTags_perm {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) : (groupedTags s r j).Perm (tagList s r j) := by
  have hn : (groupedTags s r j).Nodup := by
    apply List.nodup_flatMap.mpr
    constructor
    · intro p _
      exact (tagList_nodup s r j).filter _
    · apply (List.nodup_finRange (k + 2)).imp
      intro p q hpq a ha hb
      have ha' := (mem_levelBlock s r j p a).mp ha
      have hb' := (mem_levelBlock s r j q a).mp hb
      exact hpq (Fin.ext (ha'.symm.trans hb'))
  apply (List.perm_ext_iff_of_nodup hn (tagList_nodup s r j)).mpr
  intro a
  simp only [mem_tagList, iff_true, groupedTags, List.mem_flatMap]
  exact ⟨⟨section5TagOriginalLevel j a, by
    have H := section5TagOriginalLevel_le hj a
    omega⟩, List.mem_finRange _, (mem_levelBlock s r j _ a).mpr rfl⟩

private theorem groupedTags_mass_sorted {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    (groupedTags s r j).Pairwise
      (fun a b => section5TagScalarMass s r j a ≤ section5TagScalarMass s r j b) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    apply ((tagList_nodup s r j).filter _).imp_of_mem
    intro a b ha hb _
    simp only [section5TagScalarMass_eq_original,
      (mem_levelBlock s r j p a).mp ha, (mem_levelBlock s r j p b).mp hb, le_refl]
  · apply (List.sortedLT_finRange (k + 2)).pairwise.imp
    intro p q hpq a ha b hb
    rw [section5TagScalarMass_eq_original, section5TagScalarMass_eq_original,
      (mem_levelBlock s r j p a).mp ha, (mem_levelBlock s r j q b).mp hb]
    exact s.m_mono' q (by omega) p hpq.le

private theorem sum_filter_map {α : Type*} (l : List α) (f : α → ℝ)
    (P : α → Prop) [DecidablePred P] :
    ((l.filter fun a => decide (P a)).map f).sum =
      (l.map fun a => if P a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : P a <;> simp [ha, ih]

private theorem levelBlock_variance_sum {k : ℕ} (s : RSBScheme k) (β t u : ℝ)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (p : Fin (k + 2)) :
    ((levelBlock s r j p).map (section5TaggedVariance s β t u j)).sum =
      β ^ 2 * (s.q (p + 1) - s.q p) := by
  have H := section5Interleaving_variance_grouping s β t u r hj0 hj
    (fun l => if l = (p : ℕ) then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at H
  rw [levelBlock, sum_filter_map, tagList, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [H]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp only [if_neg (show (q : ℕ) ≠ p from fun he => hqp (Fin.ext he))]
  · simp

private theorem levelBlock_cascade {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (p : Fin (k + 2)) {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade ((levelBlock s r j p).map (fun a =>
      (section5TagScalarMass s r j a, section5TaggedVariance s β t u j a))) Q =
      parisiStep (s.m p) (β ^ 2 * (s.q (p + 1) - s.q p)) Q := by
  have he : (levelBlock s r j p).map (fun a =>
      (section5TagScalarMass s r j a, section5TaggedVariance s β t u j a)) =
      ((levelBlock s r j p).map (section5TaggedVariance s β t u j)).map
        (fun v => (s.m p, v)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, section5TagScalarMass_eq_original,
      (mem_levelBlock s r j p a).mp ha]
  rw [he, parisiListCascade_constant_mass]
  · rw [levelBlock_variance_sum s β t u r hj0 hj p]
  · intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact section5TaggedVariance_nonneg s β ht hj hu a
  · exact hQ
  · exact hmQ

private theorem grouped_cascade {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (levels : List (Fin (k + 2))) {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade ((levels.flatMap (levelBlock s r j)).map (fun a =>
      (section5TagScalarMass s r j a, section5TaggedVariance s β t u j a))) Q =
      parisiListCascade (levels.map (fun p : Fin (k + 2) =>
        (s.m p, β ^ 2 * (s.q (p + 1) - s.q p)))) Q := by
  induction levels with
  | nil => rfl
  | cons p levels ih =>
    rw [List.flatMap_cons, List.map_append, parisiListCascade_append, ih,
      List.map_cons, parisiListCascade_cons]
    exact levelBlock_cascade s β r ht hj0 hj hu p
      (parisiListCascade_props _ hQ hmQ).1 (parisiListCascade_props _ hQ hmQ).2

/-- Exact identification of the actual scalar sorted list with the original
Gaussian operator list, for any measurable terminal with linear growth.
Repeated masses and all zero-variance faces are included. -/
theorem section5SortedScalarSteps_cascade_eq_original {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade (section5SortedScalarSteps s β t u r j) Q =
      parisiListCascade (section5OriginalScalarSteps s β) Q := by
  classical
  let F := fun a => (section5TagScalarMass s r j a, section5TaggedVariance s β t u j a)
  have he : (tagList s r j).map F = section5InterleavedScalarSteps s β t u r j := by
    simp only [tagList, section5InterleavedScalarSteps, List.map_ofFn, F, Function.comp_def]
  have hp : (section5SortedScalarSteps s β t u r j).Perm ((groupedTags s r j).map F) := by
    have hp' := ((groupedTags_perm s r hj).map F).symm
    rw [he] at hp'
    exact (List.perm_insertionSort _ _).trans hp'
  have hs : (section5SortedScalarSteps s β t u r j).Pairwise
      (fun a b : ℝ × ℝ => a.1 ≤ b.1) := by
    letI : Std.Total (fun a b : ℝ × ℝ => a.1 ≤ b.1) := ⟨fun a b => le_total _ _⟩
    letI : IsTrans (ℝ × ℝ) (fun a b => a.1 ≤ b.1) := ⟨fun _ _ _ => le_trans⟩
    exact List.pairwise_insertionSort _ _
  have hs' : ((groupedTags s r j).map F).Pairwise (fun a b : ℝ × ℝ => a.1 ≤ b.1) :=
    List.pairwise_map.mpr (groupedTags_mass_sorted s r j)
  have hv : ∀ a ∈ section5SortedScalarSteps s β t u r j, 0 ≤ a.2 := by
    intro a ha
    have ha' : a ∈ section5InterleavedScalarSteps s β t u r j :=
      (List.mem_insertionSort _).mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha'
    exact section5TaggedVariance_nonneg s β ht hj hu _
  rw [parisiListCascade_eq_of_perm_of_sorted hp hs hs' hv hQ hmQ]
  simpa only [groupedTags, section5OriginalScalarSteps, List.ofFn_eq_map, F] using
    grouped_cascade s β r ht hj0 hj hu (List.finRange (k + 2)) hQ hmQ

private theorem original_suffix_cascade {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (L : ℕ) (hL : L ≤ k + 2) :
    parisiListCascade (List.ofFn (fun p : Fin L =>
      (s.m (k + 2 - L + p), β ^ 2 *
        (s.q (k + 3 - L + p) - s.q (k + 2 - L + p)))))
      (fun x => Real.log (Real.cosh x)) = parisiF s β L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.ofFn_succ, parisiListCascade_cons, parisiF]
    have he : (fun p : Fin L =>
        (s.m (k + 2 - (L + 1) + p.succ), β ^ 2 *
          (s.q (k + 3 - (L + 1) + p.succ) - s.q (k + 2 - (L + 1) + p.succ)))) =
        (fun p : Fin L => (s.m (k + 2 - L + p), β ^ 2 *
          (s.q (k + 3 - L + p) - s.q (k + 2 - L + p)))) := by
      funext p
      simp only [Fin.val_succ]
      rw [show k + 2 - (L + 1) + ((p : ℕ) + 1) = k + 2 - L + p by omega,
        show k + 3 - (L + 1) + ((p : ℕ) + 1) = k + 3 - L + p by omega]
    rw [he, ih (by omega)]
    simp only [Fin.val_zero, Nat.add_zero,
      show k + 2 - (L + 1) = k + 1 - L by omega,
      show k + 3 - (L + 1) = k + 2 - L by omega]

/-- Forward list order agrees exactly with the original backward recursion:
the innermost operator has index `k+1` and the outermost has index zero. -/
theorem section5OriginalScalarSteps_cascade_eq_parisiF {k : ℕ} (s : RSBScheme k)
    (β : ℝ) :
    parisiListCascade (section5OriginalScalarSteps s β)
      (fun x => Real.log (Real.cosh x)) = parisiF s β (k + 2) := by
  simpa only [section5OriginalScalarSteps, Nat.sub_self, zero_add,
    show k + 3 - (k + 2) = 1 by omega, Nat.add_comm 1] using
    original_suffix_cascade s β (k + 2) le_rfl

/-- The genuine sorted tagged scalar endpoint is the original Parisi
recursion, not a modified scheme or an assumed grouping identity. -/
theorem section5SortedScalarSteps_cascade_eq_parisiF {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    parisiListCascade (section5SortedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) = parisiF s β (k + 2) := by
  exact (section5SortedScalarSteps_cascade_eq_original s β r ht hj0 hj hu
    (parisiF_props s β 0).2.1 (parisiF_props s β 0).1).trans
      (section5OriginalScalarSteps_cascade_eq_parisiF s β)

/-- The non-strict scalar inequality (5.50) for the actual tagged operators,
with its sorted endpoint now identified with the original recursion. -/
theorem section5InterleavedScalarSteps_cascade_le_parisiF {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (x : ℝ) :
    parisiListCascade (section5InterleavedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) x ≤ parisiF s β (k + 2) x := by
  classical
  rw [← section5SortedScalarSteps_cascade_eq_parisiF s β r ht hj0 hj hu]
  apply parisiListCascade_insertionSort_le _
    (parisiF_props s β 0).2.1 (parisiF_props s β 0).1
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  constructor
  · rw [section5TagScalarMass_eq_original]
    exact s.m_nonneg (section5TagOriginalLevel_le hj _)
  · exact section5TaggedVariance_nonneg s β ht hj hu _

end SpinGlass.Targets
