module

public import Targets.Section4RightVariation
public import Targets.Section4InsertedScheme
public import Targets.RightInterpolationAlgebra

@[expose] public section

/-!
# Actual inserted schemes for the right scalar variation

The dual construction inserts overlap `u` after `q_r` and assigns mass `m`
to `[q_r,u]`. Its corrected scalar value is exactly an admissible Parisi
functional when `m_(r-1) ≤ m ≤ m_r`. At the lower mass an equal-mass merge
returns a genuine fixed-level competitor. No padded minimality is required.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Insert the right overlap and its lower-interval mass, including terminal
levels and zero masses. -/
noncomputable def RSBScheme.insertRightLevel {k : ℕ} (s : RSBScheme k) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) : RSBScheme (k + 1) where
  m := section4Mass s r m
  q := section5RightRho s r u
  m_zero := by simp [section4Mass, show 0 < r by omega, s.m_zero]
  m_top := by
    simp [section4Mass, show ¬k + 1 + 1 < r by omega,
      show k + 1 + 1 ≠ r by omega, s.m_top]
  m_mono _ hp := section4Mass_mono s hr hm hp
  q_zero := (section5RightRho_endpoints s hr u).1
  q_top := (section5RightRho_endpoints s hr u).2
  q_mono _ hp := section5RightRho_mono s hr hu hp

/-- The inserted variances agree exactly with the actual right split. -/
theorem section4_right_inserted_variance {k : ℕ} (s : RSBScheme k)
    (β u : ℝ) (r p : ℕ) :
    β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p) =
      section5RightVariance s β r p (β ^ 2 * (u - s.q r)) := by
  simpa [section5RightInterpolationVariance, section5FrozenVariance] using
    section5RightInterpolationVariance_zero s β 1 u r p

/-- Every finite prefix of the right insertion is the actual right scalar
cascade, not a baseline-only comparison. -/
theorem parisiF_insertRightLevel {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    {j : ℕ} (hj : j ≤ k + 3) :
    parisiF (s.insertRightLevel r hr0 hr m u hm hu) β j =
      scalarFieldCascade (fun i => section4Mass s r m (k + 2 - i))
        (fun i => section5RightVariance s β r (k + 2 - i) (β ^ 2 * (u - s.q r))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parisiF, scalarFieldCascade, ih (by omega)]
    change parisiStep (section4Mass s r m (k + 2 - j))
      (β ^ 2 * (section5RightRho s r u (k + 3 - j) - section5RightRho s r u (k + 2 - j))) _ = _
    rw [show k + 3 - j = (k + 2 - j) + 1 by omega, section4_right_inserted_variance]

/-- The scalar correction follows from the previously checked right
interpolation algebra, with its shared half-masses retained. -/
theorem parisiCorrection_insertRightLevel {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    parisiCorrection (s.insertRightLevel r hr0 hr m u hm hu) β =
      parisiCorrection s β + (m - s.m r) * (β ^ 2 / 4 * (u ^ 2 - s.q r ^ 2)) := by
  let s' := s.insertRightLevel r hr0 hr m u hm hu
  have hsum : (∑ p ∈ Finset.range (k + 3), s'.m p *
      (β ^ 2 / 2 * (s'.q (p + 1) ^ 2 - s'.q p ^ 2))) =
      2 * parisiCorrection s' β := by
    rw [Finset.sum_range_succ']
    simp only [s'.m_zero, zero_mul, add_zero, parisiCorrection, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hpair : pairCascadeCorrection β (section5RightMass s r m) (section5RightRho s r u)
      (fun l => section5RightRho s r u (min l (r + 1))) (k + 2) =
      2 * parisiCorrection s' β := by
    rw [← hsum, pairCascadeCorrection_eq_split]
    apply Finset.sum_congr rfl
    intro p _
    change (if p < r + 1 then (2 : ℝ) else 1) * section5RightMass s r m p *
      (β ^ 2 / 2 * (section5RightRho s r u (p + 1) ^ 2 - section5RightRho s r u p ^ 2)) =
      section4Mass s r m p *
        (β ^ 2 / 2 * (section5RightRho s r u (p + 1) ^ 2 - section5RightRho s r u p ^ 2))
    unfold section5RightMass section5Mass section4Mass
    split_ifs <;> first | omega | ring
  have H := section5RightCorrection_eq s β u m hr
  rw [hpair] at H
  dsimp [s'] at H
  linarith

/-- The actual corrected right variation, with mass then overlap arguments. -/
noncomputable def section4RightPhi {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m u : ℝ) : ℝ :=
  Real.log 2 + section4RightT s β h r m (β ^ 2 * (u - s.q r)) - parisiCorrection s β +
    (s.m r - m) * (β ^ 2 / 4 * (u ^ 2 - s.q r ^ 2))

/-- The corrected right scalar variation is an actual inserted functional. -/
theorem parisiFunctional_insertRightLevel {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    parisiFunctional (s.insertRightLevel r hr0 hr m u hm hu) β h =
      section4RightPhi s β h r m u := by
  change Real.log 2 + parisiF (s.insertRightLevel r hr0 hr m u hm hu) β (k + 3) h -
    parisiCorrection (s.insertRightLevel r hr0 hr m u hm hu) β = _
  rw [parisiF_insertRightLevel s β r hr0 hr m u hm hu le_rfl,
    parisiCorrection_insertRightLevel s β r hr0 hr m u hm hu]
  change Real.log 2 + section4RightT s β h r m (β ^ 2 * (u - s.q r)) - _ = _
  unfold section4RightPhi
  ring

/-- At baseline mass the right variation is the original functional. -/
theorem section4RightPhi_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    section4RightPhi s β h r (s.m r) u = parisiFunctional s β h := by
  have hv := section5RightSplitVariance_mem s β (t := 1) ⟨zero_le_one, le_rfl⟩ hu
  simp only [one_mul] at hv
  simp only [section4RightPhi, section4RightT_baseline s β h hr hv,
    sub_self, zero_mul, add_zero]
  rfl

/-- At the original lower overlap the inserted mass has no effect. -/
theorem section4RightPhi_at_lower_overlap {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m : ℝ) :
    section4RightPhi s β h r m (s.q r) = parisiFunctional s β h := by
  simp only [section4RightPhi, sub_self, mul_zero,
    section4RightT_zero_variance s β h hr m, add_zero]
  rfl

/-- Near-global optimality applies to every admissible right insertion. -/
theorem section4RightPhi_near_min {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    section4RightPhi s β h r (s.m r) u - ε ≤ section4RightPhi s β h r m u := by
  have H := parisiValue_le (s.insertRightLevel r hr0 hr m u hm hu) β h
  rw [parisiFunctional_insertRightLevel] at H
  rw [section4RightPhi_baseline s β h hr hu]
  linarith

/-- At the lower admissible mass, merge equal adjacent levels and use the
original fixed-level minimum. This includes the first and terminal intervals. -/
theorem section4RightPhi_lower_mass_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4RightPhi s β h r (s.m r) u ≤ section4RightPhi s β h r (s.m (r - 1)) u := by
  have hm : s.m (r - 1) ∈ Set.Icc (s.m (r - 1)) (s.m r) :=
    ⟨le_rfl, s.m_mono' r hr (r - 1) (by omega)⟩
  let s' := s.insertRightLevel r hr0 hr (s.m (r - 1)) u hm hu
  have heq : s'.m (r - 1) = s'.m (r - 1 + 1) := by
    simp [s', RSBScheme.insertRightLevel, section4Mass,
      show r - 1 < r by omega, Nat.sub_add_cancel hr0]
  have H := hmin (s'.mergeEqualMass (r - 1) (by omega) heq)
  rw [parisiFunctional_mergeEqualMass] at H
  change parisiFunctional s β h ≤
    parisiFunctional (s.insertRightLevel r hr0 hr (s.m (r - 1)) u hm hu) β h at H
  rwa [parisiFunctional_insertRightLevel, ← section4RightPhi_baseline s β h hr hu] at H

end SpinGlass.Targets
