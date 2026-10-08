module

public import Targets.Milestones
public import Mathlib.Data.Nat.Find

@[expose] public section

/-!
# Breakpoint-safe trial intervals outside the neighboring overlap range

The left regime uses half-open intervals `[q_(j-1),q_j)`, whereas the right
regime uses `(q_(j-1),q_j]`. First-crossing selection therefore includes exact
breakpoint overlaps, repeated overlaps, and zero initial overlaps. The trial
index never exceeds `k + 1`; no extension to the final interval is asserted.
-/

namespace SpinGlass.Targets

/-- A first strict crossing selects a left-closed adjacent interval. No
monotonicity is needed for this finite first-crossing fact. -/
theorem exists_nat_adjacent_Ico {α : Type*} [LinearOrder α]
    (q : ℕ → α) {N : ℕ} {u : α} (hzero : q 0 ≤ u) (hN : u < q N) :
    ∃ j, 1 ≤ j ∧ j ≤ N ∧ q (j - 1) ≤ u ∧ u < q j := by
  classical
  have hex : ∃ j, u < q j := ⟨N, hN⟩
  let j := Nat.find hex
  have hj : u < q j := Nat.find_spec hex
  have hjN : j ≤ N := Nat.find_min' hex hN
  have hjpos : 1 ≤ j := by
    by_contra h
    have he : j = 0 := by omega
    rw [he] at hj
    exact (not_lt_of_ge hzero) hj
  have hprev : q (j - 1) ≤ u := by
    exact le_of_not_gt (Nat.find_min hex (by change j - 1 < j; omega))
  exact ⟨j, hjpos, hjN, hprev, hj⟩

/-- A first weak crossing selects a right-closed adjacent interval. No
monotonicity or distinct-breakpoint assumption is needed. -/
theorem exists_nat_adjacent_Ioc {α : Type*} [LinearOrder α]
    (q : ℕ → α) {N : ℕ} {u : α} (hzero : q 0 < u) (hN : u ≤ q N) :
    ∃ j, 1 ≤ j ∧ j ≤ N ∧ q (j - 1) < u ∧ u ≤ q j := by
  classical
  have hex : ∃ j, u ≤ q j := ⟨N, hN⟩
  let j := Nat.find hex
  have hj : u ≤ q j := Nat.find_spec hex
  have hjN : j ≤ N := Nat.find_min' hex hN
  have hjpos : 1 ≤ j := by
    by_contra h
    have he : j = 0 := by omega
    rw [he] at hj
    exact (not_le_of_gt hzero) hj
  have hprev : q (j - 1) < u := by
    exact lt_of_not_ge (Nat.find_min hex (by change j - 1 < j; omega))
  exact ⟨j, hjpos, hjN, hprev, hj⟩

/-- Every nonnegative overlap strictly below `q_(r-1)` has an admissible
trial interval strictly to the left of the physical index. Equality with
the lower trial breakpoint is deliberately allowed. -/
theorem section5OutsideLeft_exists_interval {k : ℕ} (s : RSBScheme k)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u < s.q (r - 1)) :
    ∃ j, 1 ≤ j ∧ j < r ∧ j ≤ k + 1 ∧ s.q (j - 1) ≤ u ∧ u < s.q j := by
  obtain ⟨j, hj0, hj, huj, hjU⟩ := exists_nat_adjacent_Ico s.q
    (by simpa only [s.q_zero] using hu0) hu
  exact ⟨j, hj0, by omega, by omega, huj, hjU⟩

/-- Every overlap above `q_(r+1)` and no larger than `q_(k+1)` has an
admissible trial interval strictly to the right. Equality with the upper
trial breakpoint is deliberately allowed. -/
theorem section5OutsideRight_exists_interval {k : ℕ} (s : RSBScheme k)
    {r : ℕ} (hr : r ≤ k + 1) {u : ℝ}
    (hu : s.q (r + 1) < u) (hutop : u ≤ s.q (k + 1)) :
    ∃ j, 1 ≤ j ∧ r + 1 < j ∧ j ≤ k + 1 ∧ s.q (j - 1) < u ∧ u ≤ s.q j := by
  have hu0 : s.q 0 < u :=
    (s.q_mono' (r + 1) (by omega) 0 (Nat.zero_le _)).trans_lt hu
  obtain ⟨j, hj0, hjtop, hjU, huj⟩ := exists_nat_adjacent_Ioc s.q hu0 hutop
  have hrj : r + 1 < j := by
    by_contra h
    have hjr : j ≤ r + 1 := le_of_not_gt h
    exact (not_le_of_gt hu) (huj.trans (s.q_mono' (r + 1) (by omega) j hjr))
  exact ⟨j, hj0, hrj, hjtop, hjU, huj⟩

end SpinGlass.Targets
