module

public import Targets.Section4NeighborFactors
public import Targets.Section4StationarityTerminal

@[expose] public section

/-!
# Scalar identities at a zero initial overlap

When `q₁ = 0`, both initial variances vanish. The genuine normalized
squared-slope and squared-Hessian factors are therefore scalar squares.
Fixed-level stationarity forces the scalar first derivative to vanish.
The second-order one-sided optimality estimate is proved separately in
`Section4ZeroOverlapCurvature`; these identities are its scalar inputs.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- At zero initial overlap, the first scalar step has total variance
`β² q₂`; this identifies the slope used in the admissible right variation. -/
theorem stepD1_initial_totalVariance {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hq : s.q 1 = 0) :
    stepD1 (parisiF s β k) (parisiFDeriv s β k) (s.m 1) (β ^ 2 * s.q 2) h =
      parisiFDeriv s β (k + 1) h := by
  simp only [parisiFDeriv, show k + 1 - k = 1 by omega,
    show k + 2 - k = 2 by omega, hq, sub_zero]

/-- The corresponding scalar Hessian is the original recursion's genuine
second derivative, including in the replica-symmetric case. -/
theorem stepD2_initial_totalVariance {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hq : s.q 1 = 0) :
    stepD2 (parisiF s β k) (parisiFDeriv s β k) (parisiFSecond s β k)
      (s.m 1) (β ^ 2 * s.q 2) h = parisiFSecond s β (k + 1) h := by
  simp only [parisiFSecond, show k + 1 - k = 1 by omega,
    show k + 2 - k = 2 by omega, hq, sub_zero]

/-- At zero initial overlap the actual endpoint factor is a scalar square,
independently of the inserted mass. No derivative at a singleton is used. -/
theorem section4TVarianceQ_initial_zero_eq_sq {k : ℕ} (s : RSBScheme k)
    (β h m : ℝ) (hq : s.q 1 = 0) :
    section4TVarianceQ s β h 1 m 0 = (parisiFDeriv s β (k + 1) h) ^ 2 := by
  simp only [section4TVarianceQ, Nat.sub_self, section4VarianceQ,
    hq, s.q_zero, sub_self, mul_zero, pairedSecondMean_zero_variance,
    stepD1_parisiF_zero_variance, show k + 2 - 1 = k + 1 by omega]

/-- The actual Hessian-square factor at zero initial overlap is exactly
the square of the original scalar second derivative. -/
theorem section4THessianSquare_initial_zero_eq_sq {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hq : s.q 1 = 0) :
    section4THessianSquare s β h 1 0 = (parisiFSecond s β (k + 1) h) ^ 2 := by
  simp only [section4THessianSquare, Nat.sub_self, section4VarianceR,
    hq, s.q_zero, sub_self, mul_zero, pairedSecondMean_zero_variance,
    stepD2_parisiF_zero_variance, show k + 2 - 1 = k + 1 by omega]

/-- Fixed-level minimality with a positive first mass gap forces the actual
scalar slope to vanish when the first overlap is zero. The terminal RS case
is included via the already proved all-level stationarity theorem. -/
theorem parisiFDeriv_initial_zero_of_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (hq : s.q 1 = 0)
    (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    parisiFDeriv s β (k + 1) h = 0 := by
  have H := section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h
    (r := 1) le_rfl (by omega) hβ (by simpa only [Nat.sub_self] using hm)
    (Or.inr hq) hright hmin
  rw [section4TVarianceQ_initial_zero_eq_sq s β h _ hq, hq] at H
  exact sq_eq_zero_iff.mp H

end SpinGlass.Targets
