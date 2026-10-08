module

/-
# Deleting a zero-variance level and changing physical field coordinates

These exact identities connect the inserted Section 5 interpolation to the
existing constrained pressure. No mass strictness or analytic differentiation
is needed for these endpoint changes of variables.
-/
public import Targets.CoupledEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

@[simp] theorem independentStepPi_variance_zero (n : ℕ) (m : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : independentStepPi n m 0 A = A := by
  funext x y
  by_cases hm : m = 0
  · simp [independentStepPi, hm]
  · simp [independentStepPi, hm, Real.log_exp]

/-- Only the levels actually traversed matter. -/
theorem coupledFieldCascade_congr (n : ℕ) (m v m' v' : ℕ → ℝ) (d j : ℕ)
    (hm : ∀ i < j, m i = m' i) (hv : ∀ i < j, v i = v' i)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n m v d A j = coupledFieldCascade n m' v' d A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [coupledFieldCascade, hm j (by omega), hv j (by omega),
      ih (fun i hi => hm i (by omega)) (fun i hi => hv i (by omega))]

/-- Insert a new entry at index d; indices describe integration order. -/
def insertLevel (f : ℕ → ℝ) (d : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  if j < d then f j else if j = d then c else f (j - 1)

theorem coupledFieldCascade_insert_prefix (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (hj : j ≤ d) (c : ℝ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (insertLevel m d c) (insertLevel v d 0) (d + 1) A j =
      coupledFieldCascade n m v d A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < d := by omega
    simp only [coupledFieldCascade, if_pos hlt, if_pos (show j < d + 1 by omega),
      insertLevel, ih (by omega)]

/-- The inserted zero-variance independent level is the identity, even at mass zero. -/
theorem coupledFieldCascade_insert_zero (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (c : ℝ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (insertLevel m d c) (insertLevel v d 0) (d + 1) A (d + j + 1) =
      coupledFieldCascade n m v d A (d + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, coupledFieldCascade, if_pos (show d < d + 1 by omega),
      insertLevel, lt_self_iff_false, if_false, if_true, independentStepPi_variance_zero]
    exact coupledFieldCascade_insert_prefix n m v d d le_rfl c A
  | succ j ih =>
    have he : d + (j + 1) = d + j + 1 := by omega
    rw [he]
    conv_rhs => rw [coupledFieldCascade]
    rw [coupledFieldCascade]
    simp only [if_neg (show ¬d + j + 1 < d + 1 by omega),
      if_neg (show ¬d + j < d by omega), insertLevel,
      if_neg (show ¬d + j + 1 < d by omega), if_neg (show d + j + 1 ≠ d by omega),
      Nat.add_sub_cancel, ih]

theorem independentStepPi_affine (n : ℕ) (m v c b : ℝ) (hc : 0 ≤ c)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    independentStepPi n m (c ^ 2 * v) A (fun i => c * x i + b) (fun i => c * y i + b) =
      independentStepPi n m v
        (fun x y => A (fun i => c * x i + b) (fun i => c * y i + b)) x y := by
  have hs : Real.sqrt (c ^ 2 * v) = c * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  simp only [independentStepPi, hs]
  have he (x z : Fin n → ℝ) : (fun i => c * x i + b + c * Real.sqrt v * z i) =
      fun i => c * (x i + Real.sqrt v * z i) + b := by funext i; ring
  simp only [he]

theorem sharedStepPi_affine (n : ℕ) (m v c b : ℝ) (hc : 0 ≤ c)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    sharedStepPi n m (c ^ 2 * v) A (fun i => c * x i + b) (fun i => c * y i + b) =
      sharedStepPi n m v
        (fun x y => A (fun i => c * x i + b) (fun i => c * y i + b)) x y := by
  have hs : Real.sqrt (c ^ 2 * v) = c * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  simp only [sharedStepPi, parisiStepPi, hs, Pi.add_def, Pi.zero_apply, zero_add]
  have he (x z : Fin n → ℝ) : (fun i => c * x i + b + c * Real.sqrt v * z i) =
      fun i => c * (x i + Real.sqrt v * z i) + b := by funext i; ring
  simp only [he]

/-- Move a common field scale and external field from the terminal to every
Gaussian increment. This is an equality of the actual nested integrals. -/
theorem coupledFieldCascade_affine (n : ℕ) (m v : ℕ → ℝ) (d j : ℕ)
    (c b : ℝ) (hc : 0 ≤ c)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascade n m (fun j => c ^ 2 * v j) d A j
        (fun i => c * x i + b) (fun i => c * y i + b) =
      coupledFieldCascade n m v d
        (fun x y => A (fun i => c * x i + b) (fun i => c * y i + b)) j x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he : (fun x y => coupledFieldCascade n m (fun j => c ^ 2 * v j) d A j
        (fun i => c * x i + b) (fun i => c * y i + b)) =
        coupledFieldCascade n m v d
          (fun x y => A (fun i => c * x i + b) (fun i => c * y i + b)) j :=
      funext fun x => funext (ih x)
    simp only [coupledFieldCascade]
    split_ifs
    · rw [independentStepPi_affine n _ _ c b hc, he]
    · rw [sharedStepPi_affine n _ _ c b hc, he]

/-- The original coupled cascade is a specialization of the exposed-level one. -/
theorem coupledCascade_eq_fieldCascade {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (d j : ℕ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledCascade n s β d A j =
      coupledFieldCascade n
        (fun j => if j < d then s.m (k + 1 - j) else s.m (k + 1 - j) / 2)
        (fun j => β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) d A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [coupledCascade, coupledFieldCascade, ih, one_mul]
    split_ifs
    · rfl
    · rw [show 2 * (s.m (k + 1 - j) / 2) = s.m (k + 1 - j) by ring]

end SpinGlass.Targets
