module

public import Targets.SecondInterpolationAlgebra
public import Targets.TalagrandRightInterpolation

@[expose] public section

/-!
# The right-interval deterministic correction

The generic split-correction identity is reused at sharing cutoff `r+1`.
Only the two pieces of `[q_r,q_(r+1)]` change. The resulting correction is
the dual counterpart of (5.9), not an assertion about the pressure derivative.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Exact right-interval counterpart of the deterministic correction in (5.9).
The baseline is `m_r` and the changed interval is `[q_r,u]`. -/
theorem section5RightCorrection_eq {k : ℕ} (s : RSBScheme k) (β u m : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) :
    pairCascadeCorrection β (section5RightMass s r m) (section5RightRho s r u)
      (fun l => section5RightRho s r u (min l (r + 1))) (k + 2) =
      2 * parisiCorrection s β +
        (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2)) := by
  let θ := fun x : ℝ => β ^ 2 / 2 * x ^ 2
  let f := fun p => (if p < r + 1 then (2 : ℝ) else 1) * section5RightMass s r m p *
    (θ (section5RightRho s r u (p + 1)) - θ (section5RightRho s r u p))
  let g := fun p => s.m p * (θ (s.q (p + 1)) - θ (s.q p))
  let δ := (m - s.m r) * (θ u - θ (s.q r))
  have hbefore (p : ℕ) (hp : p < r) : f p = g p := by
    simp only [f, g, section5RightMass, section5Mass, section5RightRho, section5Rho,
      if_pos hp, if_pos (show p < r + 1 by omega), if_pos (show p + 1 < r + 1 by omega)]
    ring
  have hnew : f r = m * (θ u - θ (s.q r)) := by
    simp only [f, section5RightMass, section5Mass, section5RightRho, section5Rho,
      if_pos (Nat.lt_succ_self r), lt_self_iff_false, if_false, if_true]
    ring
  have hnext : f (r + 1) = s.m r * (θ (s.q (r + 1)) - θ u) := by
    simp [f, section5RightMass, section5Mass, section5RightRho, section5Rho]
  have hafter (p : ℕ) (hp : r + 1 < p) : f p = g (p - 1) := by
    simp only [f, g, section5RightMass, section5Mass, section5RightRho, section5Rho,
      if_neg (show ¬p < r by omega), if_neg (show p ≠ r by omega),
      if_neg (show ¬p < r + 1 by omega), if_neg (show p ≠ r + 1 by omega),
      if_neg (show ¬p + 1 < r + 1 by omega), if_neg (show p + 1 ≠ r + 1 by omega),
      Nat.add_sub_cancel, show p - 1 + 1 = p by omega, one_mul]
  have hpartial : ∀ j, r + 1 ≤ j → (∑ p ∈ Finset.range (j + 1), f p) =
      (∑ p ∈ Finset.range j, g p) + δ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have hprefix : (∑ p ∈ Finset.range r, f p) = ∑ p ∈ Finset.range r, g p :=
        Finset.sum_congr rfl (fun p hp => hbefore p (Finset.mem_range.mp hp))
      rw [Finset.sum_range_succ f (r + 1), Finset.sum_range_succ f r,
        hprefix, hnew, hnext, Finset.sum_range_succ g r]
      dsimp [g, δ]
      ring
    | succ j hj ih =>
      rw [Finset.sum_range_succ f (j + 1), ih, hafter (j + 1) (by omega),
        Nat.add_sub_cancel, Finset.sum_range_succ g j]
      ring
  have hbase : (∑ p ∈ Finset.range (k + 2), g p) = 2 * parisiCorrection s β := by
    rw [Finset.sum_range_succ']
    simp only [g, s.m_zero, zero_mul, add_zero, parisiCorrection, θ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  calc
    _ = ∑ p ∈ Finset.range (k + 3), f p := by
      rw [pairCascadeCorrection_eq_split]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f, θ]
      ring
    _ = (∑ p ∈ Finset.range (k + 2), g p) + δ := hpartial (k + 2) (by omega)
    _ = _ := by rw [hbase]; dsimp [δ, θ]; ring

/-- At the original mass the deterministic correction is exactly the original
twice-Parisi correction, independently of the chosen right overlap. -/
theorem section5RightCorrection_baseline {k : ℕ} (s : RSBScheme k) (β u : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) :
    pairCascadeCorrection β (section5RightMass s r (s.m r)) (section5RightRho s r u)
      (fun l => section5RightRho s r u (min l (r + 1))) (k + 2) =
      2 * parisiCorrection s β := by
  simp only [section5RightCorrection_eq s β u (s.m r) hr, sub_self, zero_mul, add_zero]

end SpinGlass.Targets
