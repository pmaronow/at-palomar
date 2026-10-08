module

/-
# The actual inserted scalar Parisi functional

Talagrand (4.27)--(4.37): admissible insertion, identification with the split
recursion, and the two optimality comparisons. These are comparisons of the
actual functional, not assumptions about an auxiliary variation.
-/
public import Targets.TalagrandSection5Zero
public import Targets.Section4NestedMonotone
public import Targets.SecondInterpolationAlgebra
public import Targets.RSBSchemeMassReduction

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

theorem section4Mass_mono {k : ℕ} (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1)
    {m : ℝ} (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    {p : ℕ} (hp : p ≤ k + 1) : section4Mass s r m p ≤ section4Mass s r m (p + 1) := by
  unfold section4Mass
  by_cases hlt : p < r
  · by_cases heq : p + 1 = r
    · simpa only [if_pos hlt, if_neg (show ¬p + 1 < r by omega), if_pos heq,
        show r - 1 = p by omega] using hm.1
    · simpa only [if_pos hlt, if_pos (show p + 1 < r by omega)] using
        s.m_mono p (by omega)
  · by_cases heq : p = r
    · subst p
      simpa only [lt_self_iff_false, if_false, if_true,
        if_neg (show ¬r + 1 < r by omega), if_neg (show r + 1 ≠ r by omega),
        Nat.add_sub_cancel] using hm.2
    · simp only [if_neg hlt, if_neg heq, if_neg (show ¬p + 1 < r by omega),
        if_neg (show p + 1 ≠ r by omega), Nat.add_sub_cancel]
      exact s.m_mono' p hp (p - 1) (by omega)

/-- Insert the mass and overlap of (4.27)--(4.29). Endpoints and zero masses are allowed. -/
noncomputable def RSBScheme.insertLevel {k : ℕ} (s : RSBScheme k) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) : RSBScheme (k + 1) where
  m := section4Mass s r m
  q := section5Rho s r u
  m_zero := by simp [section4Mass, show 0 < r by omega, s.m_zero]
  m_top := by
    simp [section4Mass, show ¬k + 1 + 1 < r by omega,
      show k + 1 + 1 ≠ r by omega, s.m_top]
  m_mono _ hp := section4Mass_mono s hr hm hp
  q_zero := (section5Rho_endpoints s hr0 hr u).1
  q_top := (section5Rho_endpoints s hr0 hr u).2
  q_mono _ hp := section5Rho_mono s hr hu hp

/-- The inserted scheme has exactly the Section 4 split variances at `v=ξ'(q_r)-ξ'(u)`. -/
theorem section4_inserted_variance {k : ℕ} (s : RSBScheme k) (β u : ℝ) (r p : ℕ) :
    β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p) =
      section5Variance s β r p (β ^ 2 * (s.q r - u)) := by
  simpa [section5InterpolationVariance, section5FrozenVariance] using
    section5InterpolationVariance_zero s β 1 u r p

/-- Identification of every finite prefix with the actual inserted Parisi recursion. -/
theorem parisiF_insertLevel {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    {j : ℕ} (hj : j ≤ k + 3) :
    parisiF (s.insertLevel r hr0 hr m u hm hu) β j =
      scalarFieldCascade (fun i => section4Mass s r m (k + 2 - i))
        (fun i => section5Variance s β r (k + 2 - i) (β ^ 2 * (s.q r - u))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parisiF, scalarFieldCascade, ih (by omega)]
    change parisiStep (section4Mass s r m (k + 2 - j))
      (β ^ 2 * (section5Rho s r u (k + 3 - j) - section5Rho s r u (k + 2 - j))) _ = _
    rw [show k + 3 - j = (k + 2 - j) + 1 by omega, section4_inserted_variance]

/-- The correction of the scalar insertion, obtained from the already checked (5.9) algebra. -/
theorem parisiCorrection_insertLevel {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    parisiCorrection (s.insertLevel r hr0 hr m u hm hu) β =
      parisiCorrection s β + (m - s.m (r - 1)) * (β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2)) := by
  let s' := s.insertLevel r hr0 hr m u hm hu
  have hsum : (∑ p ∈ Finset.range (k + 3), s'.m p *
      (β ^ 2 / 2 * (s'.q (p + 1) ^ 2 - s'.q p ^ 2))) =
      2 * parisiCorrection s' β := by
    rw [Finset.sum_range_succ']
    simp only [s'.m_zero, zero_mul, add_zero, parisiCorrection, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hpair : pairCascadeCorrection β (section5Mass s r m) (section5Rho s r u)
      (fun l => section5Rho s r u (min l r)) (k + 2) = 2 * parisiCorrection s' β := by
    rw [← hsum, pairCascadeCorrection_eq_split]
    apply Finset.sum_congr rfl
    intro p _
    change (if p < r then (2 : ℝ) else 1) * section5Mass s r m p *
      (β ^ 2 / 2 * (section5Rho s r u (p + 1) ^ 2 - section5Rho s r u p ^ 2)) =
      section4Mass s r m p *
        (β ^ 2 / 2 * (section5Rho s r u (p + 1) ^ 2 - section5Rho s r u p ^ 2))
    unfold section5Mass section4Mass
    split_ifs <;> ring
  have H := section5Correction_eq s β u m hr0 hr
  rw [hpair] at H
  dsimp [s'] at H
  linarith

/-- The actual variation (4.37). Arguments are inserted mass, then overlap. -/
noncomputable def section4Phi {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m u : ℝ) : ℝ :=
  Real.log 2 + section4T s β h r m (β ^ 2 * (s.q r - u)) - parisiCorrection s β +
    (s.m (r - 1) - m) * (β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2))

/-- Talagrand (4.37), for the admissible inserted scheme rather than an abstract function. -/
theorem parisiFunctional_insertLevel {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    parisiFunctional (s.insertLevel r hr0 hr m u hm hu) β h = section4Phi s β h r m u := by
  change Real.log 2 + parisiF (s.insertLevel r hr0 hr m u hm hu) β (k + 3) h -
    parisiCorrection (s.insertLevel r hr0 hr m u hm hu) β = _
  rw [parisiF_insertLevel s β r hr0 hr m u hm hu le_rfl,
    parisiCorrection_insertLevel s β r hr0 hr m u hm hu]
  change Real.log 2 + section4T s β h r m (β ^ 2 * (s.q r - u)) - _ = _
  unfold section4Phi
  ring

theorem section4Phi_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    section4Phi s β h r (s.m (r - 1)) u = parisiFunctional s β h := by
  have hv := section5SplitVariance_mem s β (t := 1) (by constructor <;> norm_num) hu
  simp only [one_mul] at hv
  simp only [section4Phi, section4T_baseline s β h hr0 hr hv, sub_self, zero_mul, add_zero]
  rfl

/-- At the original upper overlap, the inserted mass has no effect on the functional. -/
theorem section4Phi_at_upper_overlap {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    section4Phi s β h r m (s.q r) = parisiFunctional s β h := by
  simp only [section4Phi, sub_self, mul_zero, section4T_zero_variance s β h hr0 hr m,
    add_zero]
  rfl

/-- Talagrand (4.30): near-global minimality applies to the actual inserted competitor. -/
theorem section4Phi_near_min {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    section4Phi s β h r (s.m (r - 1)) u - ε ≤ section4Phi s β h r m u := by
  have H := parisiValue_le (s.insertLevel r hr0 hr m u hm hu) β h
  rw [parisiFunctional_insertLevel] at H
  rw [section4Phi_baseline s β h hr0 hr hu]
  linarith

/-- Talagrand (4.31): at the upper mass, merge the equal adjacent levels and
apply the original fixed-level minimality hypothesis. -/
theorem section4Phi_upper_mass_min {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4Phi s β h r (s.m (r - 1)) u ≤ section4Phi s β h r (s.m r) u := by
  have hm : s.m r ∈ Set.Icc (s.m (r - 1)) (s.m r) :=
    ⟨s.m_mono' r hr (r - 1) (by omega), le_rfl⟩
  let s' := s.insertLevel r hr0 hr (s.m r) u hm hu
  have heq : s'.m r = s'.m (r + 1) := by
    simp [s', RSBScheme.insertLevel, section4Mass, show ¬r + 1 < r by omega]
  have H := hmin (s'.mergeEqualMass r hr heq)
  rw [parisiFunctional_mergeEqualMass] at H
  change parisiFunctional s β h ≤ parisiFunctional (s.insertLevel r hr0 hr (s.m r) u hm hu) β h at H
  rwa [parisiFunctional_insertLevel, ← section4Phi_baseline s β h hr0 hr hu] at H

end SpinGlass.Targets
