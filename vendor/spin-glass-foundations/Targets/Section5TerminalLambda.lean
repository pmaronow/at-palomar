module

public import Targets.RSBSchemeTerminalPadding
public import Targets.Section5RightLambdaFactor
public import Targets.Section4RightFactor
public import Targets.Section4TerminalFactors

@[expose] public section

/-!
# The terminal right lambda factor through redundant padding

The padded scheme adds a zero-variance innermost independent step. Deleting
that identity step and shifting the arrays gives equality of the entire
original and padded right lambda families. No padded minimality is used.
This permits reuse of the checked nonterminal lambda derivative for the
original terminal right interval, which need not have zero overlap length.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Delete a zero-variance innermost independent step. All masses, including
zero, are allowed; only the evaluated variance at the chosen parameter matters. -/
theorem splitScalarCascade_delete_zero_first {P : Type*}
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (d j : ℕ) (p : P) (hzero : v 0 p = 0) :
    splitScalarCascade m v (d + 1) (j + 1) p =
      splitScalarCascade (fun i => m (i + 1)) (fun i => v (i + 1)) d j p := by
  induction j with
  | zero =>
    funext ℓ x
    simp only [splitScalarCascade, Nat.zero_lt_succ, if_true, GTFrame.finiteStep]
    by_cases hm : m 0 = 0
    · simp [hm, GTFrame.step0, hzero]
    · simp [hm, GTFrame.stepM, hzero, Real.log_exp]
  | succ j ih =>
    funext ℓ x
    conv_lhs => rw [splitScalarCascade]
    conv_rhs => rw [splitScalarCascade]
    simp only [Nat.add_lt_add_iff_right, GTFrame.finiteStep]
    split_ifs <;> simp only [GTFrame.step0, GTFrame.stepM, ih]

/-- Every original physical right paired mass is unchanged by padding. -/
theorem section5RightMass_padOneLast {k : ℕ} (s : RSBScheme k)
    {r : ℕ} (hr : r ≤ k + 1) (m : ℝ) {p : ℕ} (hp : p ≤ k + 2) :
    section5RightMass s.padOneLast r m p = section5RightMass s r m p := by
  unfold section5RightMass section5Mass
  split_ifs with hlt heq
  · rw [RSBScheme.padOneLast_m s (by omega)]
  · rfl
  · rw [RSBScheme.padOneLast_m s (by omega)]

/-- Every original physical right split variance is unchanged by padding. -/
theorem section5RightVariance_padOneLast {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {p : ℕ} (hp : p ≤ k + 2) (v : ℝ) :
    section5RightVariance s.padOneLast β r p v = section5RightVariance s β r p v := by
  unfold section5RightVariance
  split_ifs with hlt heq heq'
  · rw [RSBScheme.padOneLast_q s (by omega), RSBScheme.padOneLast_q s (by omega)]
  · rfl
  · rw [RSBScheme.padOneLast_q s (by omega), RSBScheme.padOneLast_q s (by omega)]
  · rw [RSBScheme.padOneLast_q s (by omega), RSBScheme.padOneLast_q s (by omega)]

/-- Redundant terminal padding preserves the entire right lambda family,
not just its value at zero. The inserted scalar mass and split variance are
arbitrary. No optimality assumption on either scheme is required. -/
theorem section5RightV_padOneLast {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m v : ℝ) :
    section5RightV s.padOneLast β h r m v = section5RightV s β h r m v := by
  have hd : k + 1 + 2 - r = (k + 2 - r) + 1 := by omega
  have hz : section5RightVariance s.padOneLast β r (k + 1 + 2) v = 0 := by
    simp only [section5RightVariance, if_neg (show ¬k + 1 + 2 < r by omega),
      if_neg (show k + 1 + 2 ≠ r by omega), if_neg (show k + 1 + 2 ≠ r + 1 by omega)]
    simp [RSBScheme.padOneLast, show k + 1 + 2 - 1 = k + 2 by omega]
  have H := splitScalarCascade_delete_zero_first
    (fun i => section5RightMass s.padOneLast r m (k + 1 + 2 - i))
    (fun i => section5RightVariance s.padOneLast β r (k + 1 + 2 - i))
    (k + 2 - r) (k + 3) v (by simpa only [Nat.sub_zero] using hz)
  have He := splitScalarCascade_congr_at
    (fun i => section5RightMass s.padOneLast r m (k + 1 + 2 - (i + 1)))
    (fun i => section5RightMass s r m (k + 2 - i))
    (fun i => section5RightVariance s.padOneLast β r (k + 1 + 2 - (i + 1)))
    (fun i => section5RightVariance s β r (k + 2 - i))
    (k + 2 - r) (k + 3) v v
    (fun i _ => by
      rw [show k + 1 + 2 - (i + 1) = k + 2 - i by omega]
      exact section5RightMass_padOneLast s hr m (by omega))
    (fun i _ => by
      rw [show k + 1 + 2 - (i + 1) = k + 2 - i by omega]
      exact section5RightVariance_padOneLast s β hr (by omega) v)
  unfold section5RightV
  rw [hd, show k + 1 + 3 = k + 3 + 1 by omega]
  exact congrArg (fun F ℓ => F ℓ (h, h)) (H.trans He)

/-- The original baseline family's genuine zero-lambda derivative is the
padded right factor, including the original terminal interval. -/
theorem hasDerivAt_section5RightV_zero_Q_padded {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (section5RightV s β h r (s.m r) v)
      (section4RightQ s.padOneLast β h r v) 0 := by
  have hvp : v ∈ Set.Icc 0 (β ^ 2 * (s.padOneLast.q (r + 1) - s.padOneLast.q r)) := by
    rw [RSBScheme.padOneLast_q s (p := r + 1) (by omega),
      RSBScheme.padOneLast_q s (p := r) (by omega)]
    exact hv
  have H := hasDerivAt_section5RightV_zero_Q s.padOneLast β h hr hvp
  change HasDerivAt (section5RightV s.padOneLast β h r (s.padOneLast.m r) v)
    (section4RightQ s.padOneLast β h r v) 0 at H
  rw [RSBScheme.padOneLast_m s hr, section5RightV_padOneLast s β h hr] at H
  exact H

/-- Numerical form of the genuine derivative, after exact family padding. -/
theorem deriv_section5RightV_zero_eq_Q_padded {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    deriv (section5RightV s β h r (s.m r) v) 0 = section4RightQ s.padOneLast β h r v :=
  (hasDerivAt_section5RightV_zero_Q_padded s β h hr hv).deriv

/-- The genuine zero-lambda derivative is the original scheme's right
squared-slope factor at every physical level, including the terminal one.
No minimization property of the padded scheme is assumed. -/
theorem hasDerivAt_section5RightV_zero_Q_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (section5RightV s β h r (s.m r) v) (section4RightQ s β h r v) 0 := by
  simpa only [section4RightQ_padOneLast s β h hr v] using
    hasDerivAt_section5RightV_zero_Q_padded s β h hr hv

/-- The right lambda-factor identity now includes the actual terminal
interval and both variance endpoints, with all quantities on the original
scheme. Differentiability is proved before taking the numerical derivative. -/
theorem deriv_section5RightV_zero_eq_Q_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    deriv (section5RightV s β h r (s.m r) v) 0 = section4RightQ s β h r v :=
  (hasDerivAt_section5RightV_zero_Q_all_levels s β h hr hv).deriv

end SpinGlass.Targets
