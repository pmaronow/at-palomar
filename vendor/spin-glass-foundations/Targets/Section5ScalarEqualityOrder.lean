module

public import Targets.ParisiCascadeStrictSorting
public import Targets.Section5ScalarIdentification

@[expose] public section

/-!
# Equality rigidity for the actual tagged scalar endpoint

This supplies Talagrand's scalar equality condition (5.51): equality at one
field with the original Parisi recursion forces the original interleaved
scalar masses to be ordered on positive-variance tags. The outside-neighbor
corollaries still display the paired equality-order premise (5.44); they do
not assume or assert the missing pressure comparison.
-/

namespace SpinGlass.Targets

private theorem interleaved_admissible {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    ∀ a ∈ section5InterleavedScalarSteps s β t u r j,
      a.1 ∈ Set.Icc 0 1 ∧ 0 ≤ a.2 := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  constructor
  · rw [section5TagScalarMass_eq_original]
    exact ⟨s.m_nonneg (section5TagOriginalLevel_le hj _),
      s.m_le_one (section5TagOriginalLevel_le hj _)⟩
  · exact section5TaggedVariance_nonneg s β ht hj hu _

private theorem positive_order_iff_tagged_order {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j : ℕ) :
    ParisiPositiveMassOrder (section5InterleavedScalarSteps s β t u r j) ↔
      Section5InterleavingScalarOrder s β t u r j := by
  constructor
  · intro H b c hb hc hbc
    have hp := List.pairwise_ofFn.mp H hbc
    simp only [Equiv.apply_symm_apply] at hp
    exact hp hb hc
  · intro H
    apply List.pairwise_ofFn.mpr
    intro b c hbc hb hc
    exact H _ _ hb hc (by simpa only [Equiv.symm_apply_apply] using hbc)

/-- Genuine scalar sorting equality implies (5.51) on every pair of tags with
positive actual variance. Equality at just one field suffices. -/
theorem section5InterleavedScalarSteps_eq_implies_order {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (x : ℝ)
    (he : parisiListCascade (section5InterleavedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) x = parisiF s β (k + 2) x) :
    Section5InterleavingScalarOrder s β t u r j := by
  apply (positive_order_iff_tagged_order s β t u r j).mp
  apply parisiListCascade_positive_order_of_sorting_eq _
    (interleaved_admissible s β r ht hj hu) x
  exact he.trans (congrFun (section5SortedScalarSteps_cascade_eq_parisiF s β r
    ht hj0 hj hu) x).symm

/-- Failure of (5.51) forces a strict scalar deficit relative to the original
Parisi recursion, including interleavings with additional zero-variance tags. -/
theorem section5InterleavedScalarSteps_lt_of_not_order {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {t u : ℝ} (r : ℕ) {j : ℕ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hn : ¬Section5InterleavingScalarOrder s β t u r j) (x : ℝ) :
    parisiListCascade (section5InterleavedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) x < parisiF s β (k + 2) x := by
  have H := parisiListCascade_insertionSort_lt_of_not_positive_order _
    (interleaved_admissible s β r ht hj hu)
    (fun hp => hn ((positive_order_iff_tagged_order s β t u r j).mp hp)) x
  exact H.trans_eq (congrFun (section5SortedScalarSteps_cascade_eq_parisiF s β r
    ht hj0 hj hu) x)

/-- In the left outside-neighbor regime, the paired equality-order condition
forces strictness of the actual scalar comparison. Witness variances must be
positive; boundary overlaps are not silently excluded. -/
theorem section5InterleavedScalarSteps_lt_left_of_paired_order {k : ℕ}
    (s : RSBScheme k) (β : ℝ) {t u : ℝ} {r j : ℕ}
    (ht : t ∈ Set.Icc 0 1) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - u)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1))))
    (hpaired : Section5InterleavingEqualityOrder s β t u r j) (x : ℝ) :
    parisiListCascade (section5InterleavedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) x < parisiF s β (k + 2) x := by
  apply section5InterleavedScalarSteps_lt_of_not_order s β r ht hj0 (by omega) hu
  exact fun hs => section5Interleaving_left_outside_obstruction s β t u hr hj0 hjr
    hm hbv hcv ⟨hpaired, hs⟩

/-- The analogous right outside-neighbor scalar strictness, with the paired
equality-order premise and both positive witness variances kept explicit. -/
theorem section5InterleavedScalarSteps_lt_right_of_paired_order {k : ℕ}
    (s : RSBScheme k) (β : ℝ) {t u : ℝ} {r j : ℕ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (u - s.q (j - 1))))
    (hpaired : Section5InterleavingEqualityOrder s β t u r j) (x : ℝ) :
    parisiListCascade (section5InterleavedScalarSteps s β t u r j)
      (fun x => Real.log (Real.cosh x)) x < parisiF s β (k + 2) x := by
  apply section5InterleavedScalarSteps_lt_of_not_order s β r ht (by omega) hj hu
  exact fun hs => section5Interleaving_right_outside_obstruction s β t u hj hrj
    hm hbv hcv ⟨hpaired, hs⟩

end SpinGlass.Targets
