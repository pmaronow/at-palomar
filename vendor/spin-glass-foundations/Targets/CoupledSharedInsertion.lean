module

public import Targets.CoupledReindex

@[expose] public section

/-!
# Exact insertion of a shared zero-variance level

The right-interval dual construction in Talagrand Section 5 inserts its redundant
level on the shared side of the branching point. The existing insertion theorem
handles the independent side. This adapter keeps the branching index unchanged.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

@[simp] theorem sharedStepPi_variance_zero (n : ℕ) (m : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : sharedStepPi n m 0 A = A := by
  funext x y
  by_cases hm : m / 2 = 0
  · simp [sharedStepPi, parisiStepPi, hm, Pi.add_def]
  · have hm' : m ≠ 0 := by aesop
    simp only [sharedStepPi, parisiStepPi, if_neg hm, Real.sqrt_zero, zero_mul,
      add_zero, integral_const, probReal_univ, one_smul, Real.log_exp]
    field_simp

theorem coupledFieldCascade_insert_shared_prefix (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (hj : j ≤ d) (c : ℝ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (insertLevel m d c) (insertLevel v d 0) d A j =
      coupledFieldCascade n m v d A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < d := by omega
    simp only [coupledFieldCascade, if_pos hlt, insertLevel, ih (by omega)]

/-- Inserting a shared zero-variance level does not change the actual cascade,
including at mass zero; the independent-depth cutoff stays at `d`. -/
theorem coupledFieldCascade_insert_shared_zero (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (c : ℝ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (insertLevel m d c) (insertLevel v d 0) d A (d + j + 1) =
      coupledFieldCascade n m v d A (d + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, coupledFieldCascade, insertLevel, lt_self_iff_false,
      if_false, if_true, sharedStepPi_variance_zero]
    exact coupledFieldCascade_insert_shared_prefix n m v d d le_rfl c A
  | succ j ih =>
    have he : d + (j + 1) = d + j + 1 := by omega
    rw [he]
    conv_rhs => rw [coupledFieldCascade]
    rw [coupledFieldCascade]
    simp only [if_neg (show ¬d + j + 1 < d by omega),
      if_neg (show ¬d + j < d by omega), insertLevel,
      if_neg (show d + j + 1 ≠ d by omega), Nat.add_sub_cancel, ih]

/-- The sharing cutoff may move across a zero-variance level. -/
theorem coupledFieldCascade_cutoff_zero (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (hv : v d = 0) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n m v (d + 1) A j = coupledFieldCascade n m v d A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [coupledFieldCascade, ih]
    by_cases hj : j < d
    · simp only [if_pos hj, if_pos (show j < d + 1 by omega)]
    · by_cases he : j = d
      · subst j
        simp [hv]
      · simp only [if_neg hj, if_neg (show ¬j < d + 1 by omega)]

end SpinGlass.Targets
