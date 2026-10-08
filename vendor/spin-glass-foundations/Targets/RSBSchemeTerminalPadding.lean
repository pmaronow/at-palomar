module

public import Targets.Section4NeighborFactors

@[expose] public section

/-!
# Redundant terminal mass-one padding

Appending mass one at overlap one adds a zero-variance innermost scalar
step. The original physical masses and overlaps are unchanged, and the
scalar recursion is merely shifted by one level. No minimality of the
padded scheme is asserted or needed for the terminal factor adapters.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Append a redundant mass-one level and a repeated terminal overlap one. -/
noncomputable def RSBScheme.padOneLast {k : ℕ} (s : RSBScheme k) : RSBScheme (k + 1) where
  m p := s.m (min p (k + 1))
  q p := s.q (min p (k + 2))
  m_zero := by simp [s.m_zero]
  m_top := by simp [s.m_top]
  m_mono p hp := s.m_mono' (min (p + 1) (k + 1)) (by omega)
    (min p (k + 1)) (by omega)
  q_zero := by simp [s.q_zero]
  q_top := by simp [s.q_top]
  q_mono p hp := s.q_mono' (min (p + 1) (k + 2)) (by omega)
    (min p (k + 2)) (by omega)

/-- All original physical masses are preserved exactly. -/
theorem RSBScheme.padOneLast_m {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) :
    s.padOneLast.m p = s.m p := by simp only [padOneLast, min_eq_left hp]

/-- All original physical overlaps are preserved exactly. -/
theorem RSBScheme.padOneLast_q {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 2) :
    s.padOneLast.q p = s.q p := by simp only [padOneLast, min_eq_left hp]

/-- The added innermost step has zero variance. -/
theorem parisiF_padOneLast_succ {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    parisiF s.padOneLast β (j + 1) = parisiF s β j := by
  induction j with
  | zero =>
    funext x
    simp [parisiF, RSBScheme.padOneLast, s.q_top, parisiStep_zero_var]
  | succ j ih =>
    rw [parisiF, ih, parisiF]
    simp only [show k + 1 + 1 - (j + 1) = k + 1 - j by omega,
      show k + 1 + 2 - (j + 1) = k + 2 - j by omega,
      RSBScheme.padOneLast_m s (p := k + 1 - j) (by omega),
      RSBScheme.padOneLast_q s (p := k + 2 - j) (by omega),
      RSBScheme.padOneLast_q s (p := k + 1 - j) (by omega)]

/-- The genuine scalar first derivatives obey the same shift identity. -/
theorem parisiFDeriv_padOneLast_succ {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    parisiFDeriv s.padOneLast β (j + 1) = parisiFDeriv s β j := by
  funext x
  have H := (parisiF_C2_props s.padOneLast β (j + 1)).1.1 x
  rw [parisiF_padOneLast_succ] at H
  exact H.unique ((parisiF_C2_props s β j).1.1 x)

/-- The genuine scalar Hessians are also unchanged by terminal padding. -/
theorem parisiFSecond_padOneLast_succ {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    parisiFSecond s.padOneLast β (j + 1) = parisiFSecond s β j := by
  funext x
  have H := (parisiF_C2_props s.padOneLast β (j + 1)).1.2.1 x
  rw [parisiFDeriv_padOneLast_succ] at H
  exact H.unique ((parisiF_C2_props s β j).1.2.1 x)

end SpinGlass.Targets
