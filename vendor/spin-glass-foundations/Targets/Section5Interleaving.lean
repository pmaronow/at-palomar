module

public import Targets.TalagrandSection5
public import Targets.SecondInterpolationAlgebra
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The tagged finite interleaving in Proposition 5.7

The two mass lists retain distinct tags, including when their values coincide.
Mathlib's stable tuple sort provides the permutation: equal masses are ordered
by their original index, with physical entries before interpolating entries.
The paper's `k` is the present project's `k + 1`, so there are `2 * k + 5`
entries. This module supplies the finite construction and exact regrouping;
it does not yet assert the interleaved cascade or Proposition 5.7.
-/

open scoped BigOperators

namespace SpinGlass.Targets

/-- Stable sorting preserves the order of two input positions whenever their
values are nondecreasing. Equal values remain separately indexed. -/
theorem stableSort_position_lt_of_le {N : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin N → α) {i j : Fin N} (hij : i < j) (hf : f i ≤ f j) :
    (Tuple.sort f).symm i < (Tuple.sort f).symm j := by
  have hs := Tuple.monotone_sort f
  have ht := (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).mp rfl
  by_contra h
  have hle := le_of_not_gt h
  have hne : (Tuple.sort f).symm j ≠ (Tuple.sort f).symm i := by
    exact fun he => hij.ne (Equiv.injective _ he).symm
  have hlt := lt_of_le_of_ne hle hne
  have hmass : f j ≤ f i := by simpa only [Function.comp_apply,
    Equiv.apply_symm_apply] using hs hle
  have H := ht.2 _ _ hlt (by
    simpa only [Equiv.apply_symm_apply] using (le_antisymm hmass hf))
  simp only [Equiv.apply_symm_apply] at H
  exact (lt_asymm hij H)

/-- The physical masses, in forward order, before merging with the inserted
interpolation masses. -/
noncomputable def section5PhysicalMass {k : ℕ} (s : RSBScheme k) (r p : ℕ) : ℝ :=
  if p < r then s.m p / 2 else s.m p

/-- A tag records both its source list and its original position. -/
abbrev Section5MassTag (k : ℕ) := Fin (k + 2) ⊕ Fin (k + 3)

/-- The two actual mass lists, without identifying equal entries. -/
noncomputable def section5TaggedMass {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    Section5MassTag k → ℝ :=
  Sum.elim (fun p => section5PhysicalMass s r p)
    (fun p => section5Mass s j (s.m (j - 1)) p)

/-- Concatenating the lists fixes a deterministic tie order. -/
noncomputable def section5UnsortedMass {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    Fin ((k + 2) + (k + 3)) → ℝ :=
  Fin.append (fun p => section5PhysicalMass s r p)
    (fun p => section5Mass s j (s.m (j - 1)) p)

/-- A genuine bijection from sorted positions to original tagged entries. -/
noncomputable def section5Interleaving {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    Fin ((k + 2) + (k + 3)) ≃ Section5MassTag k :=
  (Tuple.sort (section5UnsortedMass s r j)).trans finSumFinEquiv.symm

/-- The nondecreasing mass at a merged position. -/
noncomputable def section5InterleavedMass {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (i : Fin ((k + 2) + (k + 3))) : ℝ :=
  section5TaggedMass s r j (section5Interleaving s r j i)

theorem section5Interleaving_card (k : ℕ) :
    Fintype.card (Section5MassTag k) = 2 * k + 5 := by
  simp only [Section5MassTag, Fintype.card_sum, Fintype.card_fin]
  omega

theorem section5InterleavedMass_eq_sort {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    section5InterleavedMass s r j =
      section5UnsortedMass s r j ∘ Tuple.sort (section5UnsortedMass s r j) := by
  funext i
  simp only [section5InterleavedMass, section5Interleaving, Equiv.trans_apply,
    Function.comp_apply]
  generalize Tuple.sort (section5UnsortedMass s r j) i = p
  induction p using Fin.addCases <;>
    simp [section5TaggedMass, section5UnsortedMass]

/-- Sortedness requires no strict-mass or generic-position hypothesis. -/
theorem monotone_section5InterleavedMass {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    Monotone (section5InterleavedMass s r j) := by
  rw [section5InterleavedMass_eq_sort]
  exact Tuple.monotone_sort _

theorem section5InterleavedMass_at_tag {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (tag : Section5MassTag k) :
    section5InterleavedMass s r j ((section5Interleaving s r j).symm tag) =
      section5TaggedMass s r j tag := by
  simp only [section5InterleavedMass, Equiv.apply_symm_apply]

theorem monotone_section5PhysicalMass {k : ℕ} (s : RSBScheme k) (r : ℕ) :
    Monotone (fun p : Fin (k + 2) => section5PhysicalMass s r p) := by
  intro p q hpq
  have h := s.m_mono' q (by omega) p hpq
  have hp := s.m_nonneg (show (p : ℕ) ≤ k + 1 by omega)
  by_cases hp' : (p : ℕ) < r
  · by_cases hq' : (q : ℕ) < r
    · simpa only [section5PhysicalMass, if_pos hp', if_pos hq'] using
        div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    · simp only [section5PhysicalMass, if_pos hp', if_neg hq']
      linarith
  · have hq' : ¬(q : ℕ) < r := by omega
    simpa only [section5PhysicalMass, if_neg hp', if_neg hq'] using h

theorem monotone_section5InterpolatingMass {k : ℕ} (s : RSBScheme k)
    {j : ℕ} (hj : j ≤ k + 1) :
    Monotone (fun p : Fin (k + 3) => section5Mass s j (s.m (j - 1)) p) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro p
  change section5Mass s j (s.m (j - 1)) p ≤ section5Mass s j (s.m (j - 1)) (p + 1)
  apply section5Mass_mono s hj _ (by omega)
  constructor
  · linarith [s.m_nonneg (show j - 1 ≤ k + 1 by omega)]
  · exact s.m_mono' j hj (j - 1) (by omega)

/-- The physical source list embeds in strictly increasing merged positions,
even when its mass values have repetitions. -/
theorem strictMono_section5Interleaving_physical {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) :
    StrictMono (fun p : Fin (k + 2) =>
      (section5Interleaving s r j).symm (Sum.inl p)) := by
  intro p q hpq
  apply stableSort_position_lt_of_le
  · exact hpq
  · simpa [section5UnsortedMass] using (monotone_section5PhysicalMass s r) hpq.le

/-- The interpolation source list also embeds in strictly increasing merged
positions, including the inserted mass and zero-mass cases. -/
theorem strictMono_section5Interleaving_interpolating {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) :
    StrictMono (fun p : Fin (k + 3) =>
      (section5Interleaving s r j).symm (Sum.inr p)) := by
  intro p q hpq
  apply stableSort_position_lt_of_le
  · simpa using hpq
  · simpa [section5UnsortedMass] using (monotone_section5InterpolatingMass s hj) hpq.le

/-- Equal physical/interpolation masses have a fixed tie rule, but neither
tag is discarded. -/
theorem section5Interleaving_physical_before_interpolating_of_eq {k : ℕ}
    (s : RSBScheme k) (r j : ℕ) (p : Fin (k + 2)) (q : Fin (k + 3))
    (he : section5PhysicalMass s r p = section5Mass s j (s.m (j - 1)) q) :
    (section5Interleaving s r j).symm (Sum.inl p) <
      (section5Interleaving s r j).symm (Sum.inr q) := by
  apply stableSort_position_lt_of_le
  · change (p : ℕ) < k + 2 + (q : ℕ)
    omega
  · simpa [section5UnsortedMass] using he.le

theorem section5PhysicalMass_mem_Icc {k : ℕ} (s : RSBScheme k) (r : ℕ)
    (p : Fin (k + 2)) : section5PhysicalMass s r p ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := s.m_nonneg (show (p : ℕ) ≤ k + 1 by omega)
  have h1 := s.m_le_one (show (p : ℕ) ≤ k + 1 by omega)
  unfold section5PhysicalMass
  split_ifs <;> constructor <;> linarith

theorem section5TaggedMass_mem_Icc {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (tag : Section5MassTag k) :
    section5TaggedMass s r j tag ∈ Set.Icc (0 : ℝ) 1 := by
  rcases tag with p | p
  · exact section5PhysicalMass_mem_Icc s r p
  · change section5Mass s j (s.m (j - 1)) p ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact section5Mass_nonneg s hj (s.m_nonneg (by omega)) (by omega)
    · unfold section5Mass
      split_ifs with hp hp
      · have h0 := s.m_nonneg (show (p : ℕ) ≤ k + 1 by omega)
        have h1 := s.m_le_one (show (p : ℕ) ≤ k + 1 by omega)
        linarith
      · exact s.m_le_one (by omega)
      · exact s.m_le_one (by omega)

theorem section5InterleavedMass_mem_Icc {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavedMass s r j i ∈ Set.Icc (0 : ℝ) 1 :=
  section5TaggedMass_mem_Icc s r hj _

/-- The sorted masses have the required zero initial endpoint. -/
theorem section5InterleavedMass_zero {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) :
    section5InterleavedMass s r j 0 = 0 := by
  have hlo := (section5InterleavedMass_mem_Icc s r hj 0).1
  have hhi := monotone_section5InterleavedMass s r j
    (Fin.zero_le ((section5Interleaving s r j).symm (Sum.inl 0)))
  rw [section5InterleavedMass_at_tag] at hhi
  simp only [section5TaggedMass, Sum.elim_inl, Fin.val_zero, section5PhysicalMass,
    s.m_zero, zero_div, ite_self] at hhi
  exact le_antisymm hhi hlo

/-- The sorted masses have the required final endpoint one. -/
theorem section5InterleavedMass_last {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    section5InterleavedMass s r j ⟨(k + 2) + (k + 3) - 1, by omega⟩ = 1 := by
  let last : Fin ((k + 2) + (k + 3)) := ⟨(k + 2) + (k + 3) - 1, by omega⟩
  have hhi := (section5InterleavedMass_mem_Icc s r hj last).2
  have hl : (section5Interleaving s r j).symm (Sum.inr (Fin.last (k + 2))) ≤ last := by
    exact Fin.le_last _
  have hlo := monotone_section5InterleavedMass s r j hl
  rw [section5InterleavedMass_at_tag] at hlo
  change section5Mass s j (s.m (j - 1)) (k + 2) ≤ _ at hlo
  rw [(section5Mass_endpoints s hj0 hj _).2] at hlo
  exact le_antisymm hhi hlo

/-- Recovering the physical source positions as an order embedding. -/
noncomputable def section5InterleavingPhysicalEmbedding {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) : Fin (k + 2) ↪o Fin ((k + 2) + (k + 3)) :=
  OrderEmbedding.ofStrictMono _ (strictMono_section5Interleaving_physical s r j)

/-- Recovering the interpolating source positions as an order embedding. -/
noncomputable def section5InterleavingInterpolatingEmbedding {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) : Fin (k + 3) ↪o Fin ((k + 2) + (k + 3)) :=
  OrderEmbedding.ofStrictMono _ (strictMono_section5Interleaving_interpolating s r hj)

/-- Exact regrouping by the original source tags. This transports frozen
variance sums, interpolating variance sums, and weighted corrections without
identifying equal mass values. -/
theorem section5Interleaving_sum {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    {α : Type*} [AddCommMonoid α] (F : Section5MassTag k → α) :
    (∑ i, F (section5Interleaving s r j i)) =
      (∑ p : Fin (k + 2), F (Sum.inl p)) +
        ∑ p : Fin (k + 3), F (Sum.inr p) := by
  rw [(section5Interleaving s r j).sum_comp F, Fintype.sum_sum_type]

/-- Which original level supplies the scalar mass of a tagged entry. The
inserted interpolation level and its predecessor belong to the same original
level; equal numerical masses at different levels remain distinguishable. -/
def section5TagOriginalLevel {k : ℕ} (j : ℕ) : Section5MassTag k → ℕ :=
  Sum.elim (fun p => p) (fun p => if (p : ℕ) < j then p else p - 1)

/-- The correlation type is attached to the tag, not inferred from a numerical
mass equality. The sign of a shared interpolation field is handled separately. -/
def section5TagShared {k : ℕ} (r j : ℕ) : Section5MassTag k → Prop :=
  Sum.elim (fun p => (p : ℕ) < r) (fun p => (p : ℕ) < j)

/-- The scalar mass after the shared-field comparison, as in Proposition 5.11. -/
noncomputable def section5TagScalarMass {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (tag : Section5MassTag k) : ℝ := by
  classical
  exact if section5TagShared r j tag then 2 * section5TaggedMass s r j tag
    else section5TaggedMass s r j tag

theorem section5TagScalarMass_eq_original {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (tag : Section5MassTag k) :
    section5TagScalarMass s r j tag = s.m (section5TagOriginalLevel j tag) := by
  rcases tag with p | p
  · simp only [section5TagScalarMass, section5TagShared, section5TaggedMass,
      section5TagOriginalLevel, Sum.elim_inl, section5PhysicalMass]
    split_ifs <;> ring
  · simp only [section5TagScalarMass, section5TagShared, section5TaggedMass,
      section5TagOriginalLevel, Sum.elim_inr, section5Mass]
    split_ifs with hp he
    · ring
    · subst j
      rfl
    · rfl

theorem section5TagOriginalLevel_le {k : ℕ} {j : ℕ} (hj : j ≤ k + 1)
    (tag : Section5MassTag k) : section5TagOriginalLevel j tag ≤ k + 1 := by
  rcases tag with p | p <;> dsimp [section5TagOriginalLevel]
  · omega
  · split_ifs <;> omega

/-- The one-replica variance assigned to each actual source tag. Physical
tags carry the frozen variance; interpolation tags carry its complementary
inserted overlap increment. -/
noncomputable def section5TaggedVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (j : ℕ) : Section5MassTag k → ℝ :=
  Sum.elim (fun p => (1 - t) * (β ^ 2 * (s.q (p + 1) - s.q p)))
    (fun p => t * (β ^ 2 *
      (section5Rho s j u (p + 1) - section5Rho s j u p)))

theorem section5TaggedVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u : ℝ} {j : ℕ} (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (tag : Section5MassTag k) :
    0 ≤ section5TaggedVariance s β t u j tag := by
  rcases tag with p | p
  · exact mul_nonneg (sub_nonneg.mpr ht.2) (mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono p (by omega))))
  · exact mul_nonneg ht.1 (mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (section5Rho_mono s hj hu (by omega))))

/-- Tagged increments of the SK trial energy; physical tags have zero
interpolating increment. This is the discrete correction before constructing
the cumulative merged overlap sequence. -/
noncomputable def section5TaggedTrialIncrement {k : ℕ} (s : RSBScheme k)
    (β u : ℝ) (j : ℕ) : Section5MassTag k → ℝ :=
  Sum.elim (fun _ => 0) (fun p => β ^ 2 / 2 *
    (section5Rho s j u (p + 1) ^ 2 - section5Rho s j u p ^ 2))

/-- The distinguished interpolation tag whose left overlap is the inserted
overlap. Uniqueness comes from the tag, without numerical-mass uniqueness. -/
noncomputable def section5InterleavingCutoff {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) : Fin ((k + 2) + (k + 3)) :=
  (section5Interleaving s r j).symm (Sum.inr ⟨j, by omega⟩)

/-- The tagged form of Talagrand's telescoping correction (5.36). This uses
the already checked actual inserted-sequence correction, at its baseline mass.
No interleaved Gaussian-cascade identity is asserted by this algebraic result. -/
theorem section5Interleaving_correction {k : ℕ} (s : RSBScheme k) (β u : ℝ)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    (∑ i, (if i < section5InterleavingCutoff s r hj then (2 : ℝ) else 1) *
      section5InterleavedMass s r j i *
        section5TaggedTrialIncrement s β u j (section5Interleaving s r j i)) =
      2 * parisiCorrection s β := by
  have hcut (p : Fin (k + 3)) :
      (section5Interleaving s r j).symm (Sum.inr p) < section5InterleavingCutoff s r hj ↔
        (p : ℕ) < j :=
    (strictMono_section5Interleaving_interpolating s r hj).lt_iff_lt
  have H := section5Interleaving_sum s r j (fun tag =>
    (if (section5Interleaving s r j).symm tag < section5InterleavingCutoff s r hj
      then (2 : ℝ) else 1) * section5TaggedMass s r j tag *
      section5TaggedTrialIncrement s β u j tag)
  simp only [Equiv.symm_apply_apply] at H
  simp only [section5TaggedTrialIncrement, Sum.elim_inl, Sum.elim_inr,
    mul_zero, Finset.sum_const_zero, zero_add] at H
  simp_rw [hcut] at H
  refine H.trans ?_
  have hc := section5Correction_eq s β u (s.m (j - 1)) hj0 hj
  rw [pairCascadeCorrection_eq_split] at hc
  simp only [sub_self, zero_mul, add_zero] at hc
  convert hc using 1
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

private theorem inserted_weighted_increment_sum {k : ℕ} (s : RSBScheme k)
    (W : ℕ → ℝ) (u : ℝ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    (∑ p : Fin (k + 3), W (if (p : ℕ) < j then p else p - 1) *
      (section5Rho s j u (p + 1) - section5Rho s j u p)) =
      ∑ p : Fin (k + 2), W p * (s.q (p + 1) - s.q p) := by
  let f := fun p : ℕ => W (if p < j then p else p - 1) *
    (section5Rho s j u (p + 1) - section5Rho s j u p)
  let g := fun p : ℕ => W p * (s.q (p + 1) - s.q p)
  have hbefore (p : ℕ) (hp : p + 1 < j) : f p = g p := by
    simp only [f, g, section5Rho, if_pos (by omega : p < j), if_pos hp]
  have hsplit : f (j - 1) + f j = g (j - 1) := by
    have he : j - 1 + 1 = j := by omega
    simp only [f, g, section5Rho, he, if_pos (by omega : j - 1 < j),
      lt_self_iff_false, if_false, if_true, if_neg (show ¬j + 1 < j by omega),
      if_neg (show j + 1 ≠ j by omega), Nat.add_sub_cancel]
    ring
  have hafter (p : ℕ) (hp : j < p) : f p = g (p - 1) := by
    simp only [f, g, section5Rho, if_neg (by omega : ¬p < j),
      if_neg (by omega : p ≠ j), if_neg (by omega : ¬p + 1 < j),
      if_neg (by omega : p + 1 ≠ j), Nat.add_sub_cancel,
      show p - 1 + 1 = p by omega]
  have hsum : ∀ L, j ≤ L → (∑ p ∈ Finset.range (L + 1), f p) =
      ∑ p ∈ Finset.range L, g p := by
    intro L hL
    induction L, hL using Nat.le_induction with
    | base =>
      have he : j - 1 + 1 = j := by omega
      have hf := Finset.sum_range_succ f (j - 1)
      have hg := Finset.sum_range_succ g (j - 1)
      rw [he] at hf hg
      have hprefix : (∑ p ∈ Finset.range (j - 1), f p) =
          ∑ p ∈ Finset.range (j - 1), g p :=
        Finset.sum_congr rfl fun p hp => hbefore p (by
          simp only [Finset.mem_range] at hp
          omega)
      rw [Finset.sum_range_succ, hf, hprefix, hg]
      linarith [hsplit]
    | succ L hL ih =>
      rw [Finset.sum_range_succ, ih, hafter (L + 1) (by omega),
        Nat.add_sub_cancel, Finset.sum_range_succ]
  simpa only [← Fin.sum_univ_eq_sum_range] using hsum (k + 2) (by omega)

/-- Exact variance grouping by original level, in a weighted form valid even
when different original levels have equal masses. Taking indicator weights
gives the precise per-level variance assertion behind (5.49). -/
theorem section5Interleaving_variance_grouping {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (W : ℕ → ℝ) :
    (∑ i, W (section5TagOriginalLevel j (section5Interleaving s r j i)) *
      section5TaggedVariance s β t u j (section5Interleaving s r j i)) =
      ∑ p : Fin (k + 2), W p * (β ^ 2 * (s.q (p + 1) - s.q p)) := by
  rw [section5Interleaving_sum s r j (fun tag =>
    W (section5TagOriginalLevel j tag) * section5TaggedVariance s β t u j tag)]
  simp only [section5TagOriginalLevel, section5TaggedVariance, Sum.elim_inl, Sum.elim_inr]
  have h := inserted_weighted_increment_sum s W u hj0 hj
  have hleft (p : Fin (k + 2)) :
      W p * ((1 - t) * (β ^ 2 * (s.q (p + 1) - s.q p))) =
        ((1 - t) * β ^ 2) * (W p * (s.q (p + 1) - s.q p)) := by ring
  have hright (p : Fin (k + 3)) :
      W (if (p : ℕ) < j then p else p - 1) *
        (t * (β ^ 2 * (section5Rho s j u (p + 1) - section5Rho s j u p))) =
      (t * β ^ 2) * (W (if (p : ℕ) < j then p else p - 1) *
        (section5Rho s j u (p + 1) - section5Rho s j u p)) := by ring
  simp_rw [hleft, hright, ← Finset.mul_sum, h]
  have he : (1 - t) * β ^ 2 + t * β ^ 2 = β ^ 2 := by ring
  rw [← add_mul, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The numerical-mass version groups all original levels having that mass.
It deliberately does not assume that equal masses label a unique level. -/
theorem section5Interleaving_variance_grouping_by_mass {k : ℕ} (s : RSBScheme k)
    (β t u a : ℝ) (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    (∑ i, if section5TagScalarMass s r j (section5Interleaving s r j i) = a then
      section5TaggedVariance s β t u j (section5Interleaving s r j i) else 0) =
      ∑ p : Fin (k + 2), if s.m p = a then β ^ 2 * (s.q (p + 1) - s.q p) else 0 := by
  classical
  have H := section5Interleaving_variance_grouping s β t u r hj0 hj
    (fun p => if s.m p = a then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at H
  simpa only [section5TagScalarMass_eq_original] using H

/-- The finite shared-before-independent order condition in (5.44), retaining
the nonzero variances and positive shared mass required there. This definition
is not an assertion that equality in the actual cascade implies the condition. -/
def Section5InterleavingEqualityOrder {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) : Prop :=
  ∀ b c : Section5MassTag k,
    0 < section5TaggedVariance s β t u j b →
    0 < section5TaggedVariance s β t u j c →
    ¬section5TagShared r j b → section5TagShared r j c →
    0 < section5TagScalarMass s r j c →
    (section5Interleaving s r j).symm c < (section5Interleaving s r j).symm b

/-- The scalar sorting equality condition is needed only between entries
whose actual variances are positive. Zero-variance tags remain present. -/
def Section5InterleavingScalarOrder {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) : Prop :=
  ∀ b c : Section5MassTag k,
    0 < section5TaggedVariance s β t u j b →
    0 < section5TaggedVariance s β t u j c →
    (section5Interleaving s r j).symm b < (section5Interleaving s r j).symm c →
    section5TagScalarMass s r j b ≤ section5TagScalarMass s r j c

theorem section5InterleavingScalarOrder_of_monotone {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ)
    (hm : Monotone (fun i => section5TagScalarMass s r j (section5Interleaving s r j i))) :
    Section5InterleavingScalarOrder s β t u r j := by
  intro b c _ _ hbc
  simpa only [Equiv.apply_symm_apply] using hm hbc.le

/-- A positive-variance independent/shared witness with reversed scalar
masses prevents (5.44) and (5.51) from holding simultaneously. -/
theorem section5Interleaving_equality_orders_incompatible {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) (b c : Section5MassTag k)
    (hbv : 0 < section5TaggedVariance s β t u j b)
    (hcv : 0 < section5TaggedVariance s β t u j c)
    (hb : ¬section5TagShared r j b) (hc : section5TagShared r j c)
    (hc0 : 0 < section5TagScalarMass s r j c)
    (hbc : section5TagScalarMass s r j b < section5TagScalarMass s r j c) :
    ¬(Section5InterleavingEqualityOrder s β t u r j ∧
      Section5InterleavingScalarOrder s β t u r j) := by
  rintro ⟨horder, hmono⟩
  have hp := horder b c hbv hcv hb hc hc0
  have H := hmono c b hcv hbv hp
  exact (not_le_of_gt hbc) H

/-- Talagrand's left outside-neighbor witnesses: the physical tag `r-1` is
shared, and the inserted interpolation tag `j` is independent. Positivity of
their actual variances is explicit; boundary overlaps are not silently removed. -/
theorem section5Interleaving_left_outside_obstruction {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) {r j : ℕ} (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - u)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ¬(Section5InterleavingEqualityOrder s β t u r j ∧
      Section5InterleavingScalarOrder s β t u r j) := by
  let b : Section5MassTag k := Sum.inr ⟨j, by omega⟩
  let c : Section5MassTag k := Sum.inl ⟨r - 1, by omega⟩
  have hb : ¬section5TagShared r j b := lt_irrefl j
  have hc : section5TagShared r j c := by change r - 1 < r; omega
  have hcb : section5TagScalarMass s r j b = s.m (j - 1) := by
    rw [section5TagScalarMass_eq_original]
    simp [b, section5TagOriginalLevel]
  have hcc : section5TagScalarMass s r j c = s.m (r - 1) := by
    rw [section5TagScalarMass_eq_original]
    rfl
  refine section5Interleaving_equality_orders_incompatible s β t u r j b c ?_ ?_ hb hc ?_ ?_
  · simpa [b, section5TaggedVariance, section5Rho,
      show ¬j + 1 < j by omega] using hbv
  · simpa only [c, section5TaggedVariance, Sum.elim_inl,
      show r - 1 + 1 = r by omega] using hcv
  · rw [hcc, ← s.m_zero]
    exact hm (show (0 : Fin (k + 2)) < ⟨r - 1, by omega⟩ by change 0 < r - 1; omega)
  · rw [hcb, hcc]
    exact hm (show (⟨j - 1, by omega⟩ : Fin (k + 2)) < ⟨r - 1, by omega⟩ by
      change j - 1 < r - 1
      omega)

/-- Talagrand's right outside-neighbor witnesses: the interpolation tag `j-1`
is shared and the physical tag `r` is independent. Actual variance positivity
remains an explicit requirement for the strictness mechanism. -/
theorem section5Interleaving_right_outside_obstruction {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) {r j : ℕ} (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (u - s.q (j - 1)))) :
    ¬(Section5InterleavingEqualityOrder s β t u r j ∧
      Section5InterleavingScalarOrder s β t u r j) := by
  let b : Section5MassTag k := Sum.inl ⟨r, by omega⟩
  let c : Section5MassTag k := Sum.inr ⟨j - 1, by omega⟩
  have hb : ¬section5TagShared r j b := lt_irrefl r
  have hc : section5TagShared r j c := by change j - 1 < j; omega
  have hcb : section5TagScalarMass s r j b = s.m r := by
    rw [section5TagScalarMass_eq_original]
    rfl
  have hcc : section5TagScalarMass s r j c = s.m (j - 1) := by
    rw [section5TagScalarMass_eq_original]
    simp only [c, section5TagOriginalLevel, Sum.elim_inr, if_pos (show j - 1 < j by omega)]
  refine section5Interleaving_equality_orders_incompatible s β t u r j b c ?_ ?_ hb hc ?_ ?_
  · exact hbv
  · simpa only [c, section5TaggedVariance, Sum.elim_inr, section5Rho,
      show j - 1 + 1 = j by omega, lt_self_iff_false, if_false, if_true,
      if_pos (show j - 1 < j by omega)] using hcv
  · rw [hcc, ← s.m_zero]
    exact hm (show (0 : Fin (k + 2)) < ⟨j - 1, by omega⟩ by change 0 < j - 1; omega)
  · rw [hcb, hcc]
    exact hm (show (⟨r, by omega⟩ : Fin (k + 2)) < ⟨j - 1, by omega⟩ by
      change r < j - 1
      omega)

end SpinGlass.Targets
