module

public import Targets.RSBSchemeTerminalPadding
public import Targets.CoupledReindex

@[expose] public section

/-!
# Exact original free-energy identities under terminal padding

The extra terminal mass-one level has zero variance. Removing this innermost
identity step shifts both the cascade depth and the independent cutoff by one.
The correction sum is unchanged as well. These are algebraic identities, with
no assumption of minimality or strict masses for the padded scheme.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The redundant innermost independent step is the identity. -/
theorem coupledCascade_padOneLast_succ {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (d : ℕ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (j : ℕ) :
    coupledCascade n s.padOneLast β (d + 1) A (j + 1) =
      coupledCascade n s β d A j := by
  induction j with
  | zero =>
    simp [coupledCascade, RSBScheme.padOneLast]
  | succ j ih =>
    rw [coupledCascade, ih, coupledCascade]
    simp only [Nat.add_lt_add_iff_right,
      show k + 1 + 1 - (j + 1) = k + 1 - j by omega,
      show k + 1 + 2 - (j + 1) = k + 2 - j by omega,
      s.padOneLast_m (p := k + 1 - j) (by omega),
      s.padOneLast_q (p := k + 2 - j) (by omega),
      s.padOneLast_q (p := k + 1 - j) (by omega)]

/-- Padding preserves the actual constrained free energy and its normalization.
The original disorder and the original external field are unchanged. -/
theorem constrainedPhi_padOneLast {Ω : Type*} [MeasureSpace Ω] {n k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) (d : ℕ) (t u : ℝ) :
    constrainedPhi n s.padOneLast β h U (d + 1) t u =
      constrainedPhi n s β h U d t u := by
  simp only [constrainedPhi, show k + 1 + 2 = (k + 2) + 1 by omega,
    coupledCascade_padOneLast_succ]

/-- The added terminal correction summand vanishes exactly. -/
theorem parisiCorrection_padOneLast {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiCorrection s.padOneLast β = parisiCorrection s β := by
  unfold parisiCorrection
  rw [Finset.sum_range_succ]
  have hz : s.padOneLast.q (k + 1 + 2) = s.padOneLast.q (k + 1 + 1) := by
    simp [RSBScheme.padOneLast]
  rw [hz, sub_self, mul_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  rw [s.padOneLast_m (by omega), s.padOneLast_q (by omega),
    s.padOneLast_q (by omega)]

/-- In particular the original comparison function `ψ` is unchanged. -/
theorem guerraPsi_padOneLast {k : ℕ} (s : RSBScheme k) (β h t : ℝ) :
    guerraPsi s.padOneLast β h t = guerraPsi s β h t := by
  simp only [guerraPsi, show k + 1 + 2 = (k + 2) + 1 by omega,
    parisiF_padOneLast_succ, parisiCorrection_padOneLast]

end SpinGlass.Targets
