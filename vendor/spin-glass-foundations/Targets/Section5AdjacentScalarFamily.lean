module

public import Targets.Section5InterleavedScalarContinuity
public import Targets.Section5AdjacentBoundary
public import Targets.Section5AdjacentScalar
public import Targets.Section5StableSortFilter

@[expose] public section

/-!
# Adjacent inserted trials at a common breakpoint

At `u = q j`, the two inserted tagged lists differ only by the tagged
interpolation entry at position `j`.  Its variance is zero in both trials.
This file records the exact finite sorting/deletion argument needed to remove
that entry.  The final cascade equality is deliberately stated for the
list-level mixed scalar recursion; the bridge to the recursively indexed
family is included below.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private abbrev AdjTag (k : ℕ) := Section5MassTag k

private noncomputable def adjRawMass {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a : AdjTag k) : ℝ := section5TaggedMass s r j a

private noncomputable def adjKey {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a : AdjTag k) : ℝ ×ₗ Fin ((k + 2) + (k + 3)) :=
  (adjRawMass s r j a, finSumFinEquiv a)

private noncomputable def adjOrder {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (a b : AdjTag k) : Prop := adjKey s r j a ≤ adjKey s r j b

private noncomputable instance adjOrderDecidable {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) : DecidableRel (adjOrder s r j) :=
  fun _ _ => by classical exact inferInstance

private theorem adjRawMass_at_interleaving {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (i : Fin ((k + 2) + (k + 3))) :
    adjRawMass s r j (section5Interleaving s r j i) =
      section5UnsortedMass s r j (Tuple.sort (section5UnsortedMass s r j) i) := by
  exact congrFun (section5InterleavedMass_eq_sort s r j) i

private theorem adjKey_pairwise {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (_hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).Pairwise (adjOrder s r j) := by
  apply List.pairwise_ofFn.mpr
  intro i q hij
  have hmono := (Tuple.eq_sort_iff (f := section5UnsortedMass s r j)
    (σ := Tuple.sort (section5UnsortedMass s r j))).mp rfl |>.1 hij.le
  have hraw : adjRawMass s r j (section5Interleaving s r j i) ≤
      adjRawMass s r j (section5Interleaving s r j q) := by
    rw [adjRawMass_at_interleaving, adjRawMass_at_interleaving]
    exact hmono
  unfold adjOrder adjKey
  change toLex
      (adjRawMass s r j (section5Interleaving s r j i),
        finSumFinEquiv (section5Interleaving s r j i)) ≤
    toLex
      (adjRawMass s r j (section5Interleaving s r j q),
        finSumFinEquiv (section5Interleaving s r j q))
  rw [Prod.Lex.toLex_le_toLex]
  rcases hraw.eq_or_lt with heq | hlt
  · right
    refine ⟨heq, ?_⟩
    have heq' : section5UnsortedMass s r j (Tuple.sort
        (section5UnsortedMass s r j) i) =
        section5UnsortedMass s r j (Tuple.sort
          (section5UnsortedMass s r j) q) := by
      simpa only [adjRawMass_at_interleaving] using heq
    have hs := (Tuple.eq_sort_iff (f := section5UnsortedMass s r j)
      (σ := Tuple.sort (section5UnsortedMass s r j))).mp rfl |>.2 i q hij heq'
    simpa [section5Interleaving] using hs.le
  · exact Or.inl hlt

private theorem adjKey_pairwise_source {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (hj : j ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).Pairwise (adjOrder s r j) := by
  exact adjKey_pairwise s r j hj

private noncomputable def adjSourceTags {k : ℕ} : List (AdjTag k) :=
  List.ofFn (finSumFinEquiv.symm : Fin ((k + 2) + (k + 3)) → AdjTag k)

private theorem adjSortedTagList_eq_insertionSort {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (hj : j ≤ k + 1) :
    List.ofFn (section5Interleaving s r j) =
      (adjSourceTags (k := k)).insertionSort (adjOrder s r j) := by
  classical
  letI : DecidableRel (adjOrder s r j) := fun a b => inferInstance
  letI : Std.Total (adjOrder s r j) := ⟨fun a b => le_total _ _⟩
  letI : IsTrans (AdjTag k) (adjOrder s r j) := ⟨fun a b c => le_trans⟩
  letI : Std.Antisymm (adjOrder s r j) := ⟨fun a b h₁ h₂ => by
    have hk : adjKey s r j a = adjKey s r j b := le_antisymm h₁ h₂
    have hi := congrArg (fun z : ℝ ×ₗ Fin ((k + 2) + (k + 3)) => z.2) hk
    exact finSumFinEquiv.injective hi⟩
  let σ := Tuple.sort (section5UnsortedMass s r j)
  let e₀ : Fin ((k + 2) + (k + 3)) ≃ AdjTag k := finSumFinEquiv.symm
  have hp : (List.ofFn (e₀ ∘ σ)).Perm (List.ofFn e₀) :=
    Equiv.Perm.ofFn_comp_perm σ e₀
  have hp' : (List.ofFn (section5Interleaving s r j)).Perm
      (adjSourceTags (k := k)) := by
    simpa [section5Interleaving, e₀, σ, Function.comp_def, adjSourceTags] using hp
  have hsort : ((adjSourceTags (k := k)).insertionSort (adjOrder s r j)).Pairwise
      (adjOrder s r j) := by
    exact List.pairwise_insertionSort _ _
  exact List.Perm.eq_of_pairwise' (adjKey_pairwise s r j hj) hsort
    (hp'.trans (List.perm_insertionSort _ _).symm)

theorem section5TagScalarMass_adjacent_boundary_of_ne
    {k : ℕ} (s : RSBScheme k) {r j : ℕ} (hj : j ≤ k + 1)
    (tag : Section5MassTag k)
    (htag : tag ≠ Sum.inr ⟨j, by omega⟩) :
    section5TagScalarMass s r j tag =
      section5TagScalarMass s r (j + 1) tag := by
  rw [section5TagScalarMass_eq_original, section5TagScalarMass_eq_original]
  rcases tag with p | p
  · rfl
  · by_cases hp : (p : ℕ) < j
    · have hp' : (p : ℕ) ≤ j := by omega
      simp [section5TagOriginalLevel, hp, hp']
    · by_cases he : (p : ℕ) = j
      · exfalso
        apply htag
        congr 1
        exact Fin.ext he
      · have hp' : ¬(p : ℕ) ≤ j := by omega
        simp [section5TagOriginalLevel, hp, hp']

private theorem adjOrder_congr_of_ne {k : ℕ} (s : RSBScheme k)
    {r j : ℕ} (hj : j ≤ k + 1) {a b : Section5MassTag k}
    (ha : a ≠ Sum.inr ⟨j, by omega⟩) (hb : b ≠ Sum.inr ⟨j, by omega⟩) :
    adjOrder s r j a b ↔ adjOrder s r (j + 1) a b := by
  simp only [adjOrder, adjKey, adjRawMass]
  rw [section5TaggedMass_adjacent_boundary_of_ne s hj a ha,
    section5TaggedMass_adjacent_boundary_of_ne s hj b hb]

private theorem mixedScalarListCascade'_congr_of_mem {α : Type*}
    (mode mode' : α → Section5GaussianMode) (m m' v v' : α → ℝ)
    (l : List α) (F : Unit → ℝ → ℝ × ℝ → ℝ)
    (hm : ∀ a ∈ l, m a = m' a) (hv : ∀ a ∈ l, v a = v' a)
    (hmode : ∀ a ∈ l, mode a = mode' a) :
    mixedScalarListCascade' mode m v l F =
      mixedScalarListCascade' mode' m' v' l F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hm b (List.mem_cons_of_mem a hb))
      (fun b hb => hv b (List.mem_cons_of_mem a hb))
      (fun b hb => hmode b (List.mem_cons_of_mem a hb))
    simp only [mixedScalarListCascade', List.foldr]
    rw [hm a List.mem_cons_self, hv a List.mem_cons_self,
      hmode a List.mem_cons_self]
    exact congrArg (mixedScalarStep' (mode' a) (m' a) (v' a)) ih'

private theorem adjacent_filter_erase {k : ℕ} (x : Section5MassTag k)
    (l : List (Section5MassTag k)) (hn : l.Nodup) :
    l.filter (fun a => a != x) = l.erase x := by
  letI : ReflBEq (AdjTag k) := ⟨by
    intro a
    cases a with
    | inl p => change (p == p) = true; exact beq_self_eq_true p
    | inr p => change (p == p) = true; exact beq_self_eq_true p⟩
  letI : LawfulBEq (AdjTag k) := ⟨by
    intro a b h
    cases a with
    | inl p =>
      cases b with
      | inl q =>
        change (p == q) = true at h
        exact congrArg Sum.inl (LawfulBEq.eq_of_beq (α := Fin (k + 2)) h)
      | inr q => change false = true at h; contradiction
    | inr p =>
      cases b with
      | inl q => change false = true at h; contradiction
      | inr q =>
        change (p == q) = true at h
        exact congrArg Sum.inr (LawfulBEq.eq_of_beq (α := Fin (k + 3)) h)⟩
  exact hn.erase_eq_filter x |>.symm

private theorem section5TaggedVariance_adjacent_boundary_zero
    {k : ℕ} (s : RSBScheme k) (β t : ℝ) {j : ℕ} (hj : j ≤ k + 1) :
    section5TaggedVariance s β t (s.q j) j (Sum.inr ⟨j, by omega⟩) = 0 := by
  simp only [section5TaggedVariance, Sum.elim_inr]
  simp [section5Rho]

theorem section5SortedTagList_adjacent_boundary_erase
    {k : ℕ} (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj : j + 1 ≤ k + 1) :
    (List.ofFn (section5Interleaving s r j)).erase (Sum.inr ⟨j, by omega⟩) =
      (List.ofFn (section5Interleaving s r (j + 1))).erase
        (Sum.inr ⟨j, by omega⟩) := by
  classical
  letI : ReflBEq (AdjTag k) := ⟨by
    intro a
    cases a with
    | inl p => change (p == p) = true; exact beq_self_eq_true p
    | inr p => change (p == p) = true; exact beq_self_eq_true p⟩
  letI : LawfulBEq (AdjTag k) := ⟨by
    intro a b h
    cases a with
    | inl p =>
      cases b with
      | inl q =>
        change (p == q) = true at h
        exact congrArg Sum.inl (LawfulBEq.eq_of_beq (α := Fin (k + 2)) h)
      | inr q => change false = true at h; contradiction
    | inr p =>
      cases b with
      | inl q => change false = true at h; contradiction
      | inr q =>
        change (p == q) = true at h
        exact congrArg Sum.inr (LawfulBEq.eq_of_beq (α := Fin (k + 3)) h)⟩
  let x : Section5MassTag k := Sum.inr ⟨j, by omega⟩
  letI : Std.Total (adjOrder s r j) := ⟨fun a b => le_total _ _⟩
  letI : IsTrans (AdjTag k) (adjOrder s r j) := ⟨fun a b c => le_trans⟩
  letI : Std.Antisymm (adjOrder s r j) := ⟨fun a b h₁ h₂ => by
    have hk : adjKey s r j a = adjKey s r j b := le_antisymm h₁ h₂
    have hi := congrArg (fun z : ℝ ×ₗ Fin ((k + 2) + (k + 3)) => z.2) hk
    exact finSumFinEquiv.injective hi⟩
  have hpj := adjSortedTagList_eq_insertionSort s r j (by omega)
  have hpj1 := adjSortedTagList_eq_insertionSort s r (j + 1) (by omega)
  have hpairj : ((List.ofFn (section5Interleaving s r j)).erase x).Pairwise
      (adjOrder s r j) :=
    List.Pairwise.sublist (l₁ := (List.ofFn (section5Interleaving s r j)).erase x)
      (l₂ := List.ofFn (section5Interleaving s r j)) List.erase_sublist
      (adjKey_pairwise s r j (by omega))
  have hpairj1 : ((List.ofFn (section5Interleaving s r (j + 1))).erase x).Pairwise
      (adjOrder s r j) := by
    apply ((adjKey_pairwise s r (j + 1) (by omega)).sublist List.erase_sublist).imp_of_mem
    intro a b ha hb hab
    apply (adjOrder_congr_of_ne s (by omega) ?_ ?_).mpr hab
    · intro hax
      subst a
      have hn : x ∉ (List.ofFn (section5Interleaving s r (j + 1))).erase x :=
        (List.nodup_ofFn.mpr (section5Interleaving s r (j + 1)).injective).not_mem_erase
      exact hn ha
    · intro hbx
      subst b
      have hn : x ∉ (List.ofFn (section5Interleaving s r (j + 1))).erase x :=
        (List.nodup_ofFn.mpr (section5Interleaving s r (j + 1)).injective).not_mem_erase
      exact hn hb
  have hpermj : (List.ofFn (section5Interleaving s r j)).Perm
      (adjSourceTags (k := k)) := by
    rw [hpj]
    exact List.perm_insertionSort _ _
  have hpermj1 : (List.ofFn (section5Interleaving s r (j + 1))).Perm
      (adjSourceTags (k := k)) := by
    rw [hpj1]
    exact List.perm_insertionSort _ _
  have hperm : ((List.ofFn (section5Interleaving s r j)).erase x).Perm
      ((List.ofFn (section5Interleaving s r (j + 1))).erase x) := by
    exact (hpermj.erase x).trans (hpermj1.erase x).symm
  exact List.Perm.eq_of_pairwise' hpairj hpairj1 hperm

private theorem mixedScalarCascade_congr {P : Type*}
    (mode mode' : ℕ → Section5GaussianMode) (m m' : ℕ → ℝ)
    (v v' : ℕ → P → ℝ) (j : ℕ) (p : P)
    (hmode : ∀ i < j, mode i = mode' i)
    (hm : ∀ i < j, m i = m' i)
    (hv : ∀ i < j, v i = v' i)
    (l : ℝ) (x : ℝ × ℝ) :
    mixedScalarCascade mode m v j p l x =
      mixedScalarCascade mode' m' v' j p l x := by
  induction j generalizing p l x with
  | zero => rfl
  | succ j ih =>
    rw [mixedScalarCascade, mixedScalarCascade, hmode j (by omega),
      hm j (by omega), hv j (by omega)]
    cases mode' j <;> simp only [GTFrame.finiteStep]
    all_goals
      have H : mixedScalarCascade mode m v j =
          mixedScalarCascade mode' m' v' j := by
        funext p' l' x'
        exact ih (p := p') (l := l') (x := x')
          (fun i hi => hmode i (by omega)) (fun i hi => hm i (by omega))
          (fun i hi => hv i (by omega))
      rw [H]

set_option maxHeartbeats 800000 in
private theorem section5InterleavedScalarV_eq_tagListCascade {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r j : ℕ) (t u l : ℝ) :
    section5InterleavedScalarV s β h r j t u l =
      mixedScalarListCascade' (section5TaggedMode r j (decide (u < 0)))
        (section5TaggedMass s r j)
        (section5TaggedVariance s β t |u| j)
        (List.ofFn (section5Interleaving s r j))
        (fun _ l z => coupledSite l z.1 z.2) () l (h, h) := by
  unfold section5InterleavedScalarV
  let N := (k + 2) + (k + 3)
  have hmode (i : Fin N) :
      section5ReverseMode s r j (decide (u < 0)) i =
        section5TaggedMode r j (decide (u < 0))
          (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    unfold section5ReverseMode
    congr 1
  have hmass (i : Fin N) :
      section5ReverseMass s r j i = section5TaggedMass s r j
        (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    unfold section5ReverseMass
    congr 1
  have hv (i : Fin N) :
      section5ReverseVariance s β t |u| r j i = section5TaggedVariance s β t |u| j
        (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    unfold section5ReverseVariance
    apply congrArg (section5TaggedVariance s β t |u| j)
    rfl
  have hN : 0 < N := by dsimp [N]; omega
  have H := mixedScalarCascade'_ofFn_reverse
    (N := N)
    (mode := section5TaggedMode r j (decide (u < 0)))
    (m := section5TaggedMass s r j)
    (v := section5TaggedVariance s β t |u| j)
    (a := fun n => section5Interleaving s r j
      ⟨n % N, Nat.mod_lt _ hN⟩) l (h, h)
  have ha : (fun p : Fin N => section5Interleaving s r j
      ⟨(p : ℕ) % N, Nat.mod_lt _ hN⟩) = section5Interleaving s r j := by
    funext p
    apply congrArg (section5Interleaving s r j)
    apply Fin.ext
    exact Nat.mod_eq_of_lt p.isLt
  rw [ha] at H
  have hmode' (i : ℕ) (hi : i < N) :
      section5ReverseMode s r j (decide (u < 0)) i =
        section5TaggedMode r j (decide (u < 0))
          (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    exact hmode ⟨i, hi⟩
  have hmass' (i : ℕ) (hi : i < N) :
      section5ReverseMass s r j i = section5TaggedMass s r j
        (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    exact hmass ⟨i, hi⟩
  have hv' (i : ℕ) (hi : i < N) :
      section5ReverseVariance s β t |u| r j i =
        section5TaggedVariance s β t |u| j
          (section5Interleaving s r j ⟨N - 1 - i, by omega⟩) := by
    exact hv ⟨i, hi⟩
  have Hc := mixedScalarCascade_congr
    (mode := section5ReverseMode s r j (decide (u < 0)))
    (mode' := fun i => section5TaggedMode r j (decide (u < 0))
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    (m := section5ReverseMass s r j)
    (m' := fun i => section5TaggedMass s r j
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    (v := fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    (v' := fun i (_ : Unit) => section5TaggedVariance s β t |u| j
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    N () hmode' hmass' (fun i hi => funext (fun z => hv' i hi)) l (h, h)
  have Hmod := mixedScalarCascade_congr
    (mode := fun i => section5TaggedMode r j (decide (u < 0))
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    (mode' := fun i => section5TaggedMode r j (decide (u < 0))
      (section5Interleaving s r j ⟨(N - 1 - i) % N, Nat.mod_lt _ hN⟩))
    (m := fun i => section5TaggedMass s r j
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    (m' := fun i => section5TaggedMass s r j
      (section5Interleaving s r j ⟨(N - 1 - i) % N, Nat.mod_lt _ hN⟩))
    (v := fun i (_ : Unit) => section5TaggedVariance s β t |u| j
      (section5Interleaving s r j ⟨N - 1 - i, by omega⟩))
    (v' := fun i (_ : Unit) => section5TaggedVariance s β t |u| j
      (section5Interleaving s r j ⟨(N - 1 - i) % N, Nat.mod_lt _ hN⟩))
    N ()
    (fun i hi => by
      congr 2
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (show N - 1 - i < N by omega)).symm)
    (fun i hi => by
      congr 2
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (show N - 1 - i < N by omega)).symm)
    (fun i hi => funext (fun _ => by
      congr 2
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (show N - 1 - i < N by omega)).symm))
    l (h, h)
  exact Hc.trans (Hmod.trans H)

set_option maxHeartbeats 800000 in
theorem section5InterleavedScalarV_adjacent_boundary {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ}
    (hj : j + 1 ≤ k + 1) (t l : ℝ) :
    section5InterleavedScalarV s β h r j t (s.q j) l =
      section5InterleavedScalarV s β h r (j + 1) t (s.q j) l := by
  classical
  letI : ReflBEq (AdjTag k) := ⟨by
    intro a
    cases a with
    | inl p => change (p == p) = true; exact beq_self_eq_true p
    | inr p => change (p == p) = true; exact beq_self_eq_true p⟩
  letI : LawfulBEq (AdjTag k) := ⟨by
    intro a b h'
    cases a with
    | inl p =>
      cases b with
      | inl q =>
        change (p == q) = true at h'
        exact congrArg Sum.inl (LawfulBEq.eq_of_beq (α := Fin (k + 2)) h')
      | inr q => change false = true at h'; contradiction
    | inr p =>
      cases b with
      | inl q => change false = true at h'; contradiction
      | inr q =>
        change (p == q) = true at h'
        exact congrArg Sum.inr (LawfulBEq.eq_of_beq (α := Fin (k + 3)) h')⟩
  let x : Section5MassTag k := Sum.inr ⟨j, by omega⟩
  let L : List (Section5MassTag k) := List.ofFn (section5Interleaving s r j)
  let L' : List (Section5MassTag k) := List.ofFn (section5Interleaving s r (j + 1))
  have hLnodup : L.Nodup := by
    dsimp [L]
    exact List.nodup_ofFn.mpr (section5Interleaving s r j).injective
  have hL'nodup : L'.Nodup := by
    dsimp [L']
    exact List.nodup_ofFn.mpr (section5Interleaving s r (j + 1)).injective
  have hLerase : L.erase x = L'.erase x := by
    exact section5SortedTagList_adjacent_boundary_erase s r hj
  have hkeep (a : Section5MassTag k) (ha : a ∈ L) (hk : (a != x) = false) :
      section5TaggedVariance s β t (s.q j) j a = 0 := by
    have hax : a = x := by
      by_contra hne
      have hb : (a != x) = true := bne_iff_ne.mpr hne
      rw [hb] at hk
      contradiction
    subst a
    dsimp [x]
    exact section5TaggedVariance_adjacent_boundary_zero s β t (by omega)
  have hkeep' (a : Section5MassTag k) (ha : a ∈ L') (hk : (a != x) = false) :
      section5TaggedVariance s β t (s.q j) (j + 1) a = 0 := by
    have hax : a = x := by
      by_contra hne
      have hb : (a != x) = true := bne_iff_ne.mpr hne
      rw [hb] at hk
      contradiction
    subst a
    rw [← section5TaggedVariance_adjacent_boundary s β t (by omega)]
    dsimp [x]
    exact section5TaggedVariance_adjacent_boundary_zero s β t (by omega)
  have Hj := mixedScalarListCascade'_filter
    (mode := section5TaggedMode r j (decide ((s.q j) < 0)))
    (m := section5TaggedMass s r j)
    (v := section5TaggedVariance s β t (s.q j) j)
    L (fun a => a != x)
    (fun a ha hk => hkeep a ha hk)
    (fun _ l z => coupledSite l z.1 z.2)
  have Hj' := mixedScalarListCascade'_filter
    (mode := section5TaggedMode r (j + 1) (decide ((s.q j) < 0)))
    (m := section5TaggedMass s r (j + 1))
    (v := section5TaggedVariance s β t (s.q j) (j + 1))
    L' (fun a => a != x)
    (fun a ha hk => hkeep' a ha hk)
    (fun _ l z => coupledSite l z.1 z.2)
  rw [section5InterleavedScalarV_eq_tagListCascade,
    section5InterleavedScalarV_eq_tagListCascade]
  have hq : 0 ≤ s.q j := s.q_nonneg (by omega)
  rw [abs_of_nonneg hq]
  rw [show L = List.ofFn (section5Interleaving s r j) by rfl] at Hj
  rw [show L' = List.ofFn (section5Interleaving s r (j + 1)) by rfl] at Hj'
  rw [Hj, Hj']
  rw [adjacent_filter_erase x L hLnodup, adjacent_filter_erase x L' hL'nodup,
    hLerase]
  have H := mixedScalarListCascade'_congr_of_mem
    (mode := section5TaggedMode r j (decide ((s.q j) < 0)))
    (mode' := section5TaggedMode r (j + 1) (decide ((s.q j) < 0)))
    (m := section5TaggedMass s r j)
    (m' := section5TaggedMass s r (j + 1))
    (v := section5TaggedVariance s β t (s.q j) j)
    (v' := section5TaggedVariance s β t (s.q j) (j + 1))
    (l := L'.erase x)
    (F := fun _ l z => coupledSite l z.1 z.2)
    (by intro a ha; exact section5TaggedMass_adjacent_boundary_of_ne s (by omega) a (by
      intro hax; exact hL'nodup.not_mem_erase (hax ▸ ha)))
    (by intro a ha; exact section5TaggedVariance_adjacent_boundary s β t (by omega) a)
    (by
      intro a ha
      apply section5TaggedMode_adjacent_boundary_of_ne (r := r) (j := j)
        (by omega) (decide ((s.q j) < 0)) a
      intro hax
      exact hL'nodup.not_mem_erase (hax ▸ ha))
  exact congrFun (congrFun (congrFun H ()) l) (h, h)

end SpinGlass.Targets
