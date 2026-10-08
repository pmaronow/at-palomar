module

public import Targets.RSBSchemeTerminalPadding
public import Targets.Section4RightFactor

@[expose] public section

/-!
# Terminal padding for the actual Section 4 factors

The redundant terminal mass-one step disappears at zero variance. The entire
split recursion, squared-slope factor, and squared-Hessian factor are unchanged
by this padding, including the auxiliary left index `k+2`. Consequently the
original terminal right factors inherit the already checked nonterminal
calculus, without any assumption that the padded scheme minimizes a functional.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem section4Mass_padOneLast {k : ℕ} (s : RSBScheme k) {r p : ℕ}
    (hr : r ≤ k + 2) (hp : p ≤ k + 2) (m : ℝ) :
    section4Mass s.padOneLast r m p = section4Mass s r m p := by
  unfold section4Mass
  split_ifs with hlt heq
  · exact s.padOneLast_m (by omega)
  · rfl
  · exact s.padOneLast_m (by omega)

private theorem section5Variance_padOneLast {k : ℕ} (s : RSBScheme k) (β : ℝ) {r p : ℕ}
    (hr : r ≤ k + 2) (hp : p ≤ k + 2) (v : ℝ) :
    section5Variance s.padOneLast β r p v = section5Variance s β r p v := by
  unfold section5Variance
  split_ifs with hlt heq hnext
  · rw [s.padOneLast_q hp, s.padOneLast_q (by omega)]
  · rfl
  · rw [s.padOneLast_q hr, s.padOneLast_q (by omega)]
  · rw [s.padOneLast_q (by omega), s.padOneLast_q hp]

/-- The whole split scalar recursion is shifted by one redundant innermost
level. This includes arbitrary split masses and variances and the auxiliary
last left index, not just baseline physical parameters. -/
theorem section4Cascade_padOneLast_succ {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 2) (m v : ℝ) (j : ℕ) :
    scalarFieldCascade (fun l => section4Mass s.padOneLast r m (k + 1 + 2 - l))
      (fun l => section5Variance s.padOneLast β r (k + 1 + 2 - l) v) (j + 1) =
      scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) j := by
  induction j with
  | zero =>
    have hvar : section5Variance s.padOneLast β r (k + 1 + 2) v = 0 := by
      simp [section5Variance, show r < k + 1 + 2 by omega, RSBScheme.padOneLast,
        show k + 1 + 2 - 1 = k + 2 by omega]
    simp only [scalarFieldCascade, Nat.sub_zero, hvar]
    funext x
    exact parisiStep_zero_var _ _ x
  | succ j ih =>
    rw [scalarFieldCascade, ih, scalarFieldCascade,
      show k + 1 + 2 - (j + 1) = k + 2 - j by omega,
      section4Mass_padOneLast s hr (by omega), section5Variance_padOneLast s β hr (by omega)]

/-- Every squared-slope factor is unchanged by terminal padding. The
auxiliary index `k+2` is included, enabling the terminal right interval. -/
theorem section4VarianceQ_padOneLast {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 2) (m : ℝ) (j : ℕ) (v : ℝ)
    (x y : Fin 1 → ℝ) :
    section4VarianceQ s.padOneLast β r m j v x y = section4VarianceQ s β r m j v x y := by
  induction j generalizing x y with
  | zero =>
    simp only [section4VarianceQ, s.padOneLast_m (p := r - 1) (by omega), s.padOneLast_q hr,
      s.padOneLast_q (p := r - 1) (by omega), show k + 1 + 2 - r = (k + 2 - r) + 1 by omega,
      parisiF_padOneLast_succ, parisiFDeriv_padOneLast_succ]
  | succ j ih =>
    have hG : section4VarianceQ s.padOneLast β r m j v = section4VarianceQ s β r m j v := by
      funext x y
      exact ih x y
    rw [section4VarianceQ, section4VarianceQ]
    dsimp only
    rw [hG,
      show k + 1 + 2 - (k + 1 + 2 - r + 2 + j) = k + 2 - (k + 2 - r + 2 + j) by omega,
      s.padOneLast_m (by omega), s.padOneLast_q (by omega), s.padOneLast_q (by omega),
      show k + 1 + 2 - r + 2 + j = (k + 2 - r + 2 + j) + 1 by omega,
      section4Cascade_padOneLast_succ s β hr]

/-- The same whole-recursion padding identity holds for squared Hessians,
without any stationarity or regularity hypotheses. -/
theorem section4VarianceR_padOneLast {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 2) (m : ℝ) (j : ℕ) (v : ℝ)
    (x y : Fin 1 → ℝ) :
    section4VarianceR s.padOneLast β r m j v x y = section4VarianceR s β r m j v x y := by
  induction j generalizing x y with
  | zero =>
    simp only [section4VarianceR, s.padOneLast_m (p := r - 1) (by omega), s.padOneLast_q hr,
      s.padOneLast_q (p := r - 1) (by omega), show k + 1 + 2 - r = (k + 2 - r) + 1 by omega,
      parisiF_padOneLast_succ, parisiFDeriv_padOneLast_succ, parisiFSecond_padOneLast_succ]
  | succ j ih =>
    have hG : section4VarianceR s.padOneLast β r m j v = section4VarianceR s β r m j v := by
      funext x y
      exact ih x y
    rw [section4VarianceR, section4VarianceR]
    dsimp only
    rw [hG,
      show k + 1 + 2 - (k + 1 + 2 - r + 2 + j) = k + 2 - (k + 2 - r + 2 + j) by omega,
      s.padOneLast_m (by omega), s.padOneLast_q (by omega), s.padOneLast_q (by omega),
      show k + 1 + 2 - r + 2 + j = (k + 2 - r + 2 + j) + 1 by omega,
      section4Cascade_padOneLast_succ s β hr]

/-- The final normalized slope factor is unchanged by terminal padding. -/
theorem section4TVarianceQ_padOneLast {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 2) (m v : ℝ) :
    section4TVarianceQ s.padOneLast β h r m v = section4TVarianceQ s β h r m v :=
  section4VarianceQ_padOneLast s β hr0 hr m (r - 1) v 0 (fun _ => h)

/-- The final actual Hessian-square factor is unchanged by terminal padding. -/
theorem section4THessianSquare_padOneLast {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 2) (v : ℝ) :
    section4THessianSquare s.padOneLast β h r v = section4THessianSquare s β h r v := by
  simp only [section4THessianSquare, s.padOneLast_m (p := r - 1) (by omega),
    section4VarianceR_padOneLast s β hr0 hr]

/-- Whole-interval equality of the original right slope factor and its padded
counterpart, including the original terminal right interval. -/
theorem section4RightQ_padOneLast {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (v : ℝ) :
    section4RightQ s.padOneLast β h r v = section4RightQ s β h r v := by
  simp only [section4RightQ, s.padOneLast_m hr, s.padOneLast_q (p := r + 1) (by omega),
    s.padOneLast_q (p := r) (by omega),
    section4TVarianceQ_padOneLast s β h (r := r + 1) (by omega) (by omega)]

/-- Whole-interval equality of the original right Hessian-square factor and
its padded counterpart. -/
theorem section4RightR_padOneLast {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (v : ℝ) :
    section4RightR s.padOneLast β h r v = section4RightR s β h r v := by
  simp only [section4RightR, s.padOneLast_q (p := r + 1) (by omega), s.padOneLast_q (p := r) (by omega),
    section4THessianSquare_padOneLast s β h (r := r + 1) (by omega) (by omega)]

/-- Endpoint-safe right-factor calculus now includes the terminal interval.
No padded-scheme minimality is used. -/
theorem hasDerivWithinAt_section4RightQ_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivWithinAt (section4RightQ s β h r) (section4RightR s β h r v)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) v := by
  have H := hasDerivWithinAt_section4RightQ s.padOneLast β h hr
    (v := v) (by simpa only [s.padOneLast_q (p := r + 1) (by omega),
      s.padOneLast_q (p := r) (by omega)] using hv)
  have he : section4RightQ s.padOneLast β h r = section4RightQ s β h r :=
    funext (section4RightQ_padOneLast s β h hr)
  simpa only [he, section4RightR_padOneLast s β h hr,
    s.padOneLast_q (p := r + 1) (by omega), s.padOneLast_q (p := r) (by omega)] using H

/-- Closed-interval continuity of the right slope factor at every physical
level, including the terminal one. -/
theorem continuousOn_section4RightQ_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) :
    ContinuousOn (section4RightQ s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :=
  fun _ hv => (hasDerivWithinAt_section4RightQ_all_levels s β h hr hv).continuousWithinAt

/-- The original terminal right Hessian-square factor has the same uniform
Lipschitz constant as every nonterminal factor. -/
theorem section4RightR_lipschitz_uniform_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |section4RightR s β h r v - section4RightR s β h r w| ≤ 535 * |v - w| := by
  have H := section4RightR_lipschitz_uniform s.padOneLast β h hr
    (v := v) (w := w)
    (by simpa only [s.padOneLast_q (p := r + 1) (by omega), s.padOneLast_q (p := r) (by omega)] using hv)
    (by simpa only [s.padOneLast_q (p := r + 1) (by omega), s.padOneLast_q (p := r) (by omega)] using hw)
  simpa only [section4RightR_padOneLast s β h hr] using H

/-- Padding transfers the right zero-endpoint slope to the original left
zero-endpoint slope, including the original terminal level. -/
theorem section4RightQ_padOneLast_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4RightQ s.padOneLast β h r 0 = section4TVarianceQ s β h r (s.m (r - 1)) 0 := by
  unfold section4RightQ
  rw [sub_zero, section4TVarianceQ_neighbor_full_eq_zero s.padOneLast β h hr0 hr,
    s.padOneLast_m (p := r - 1) (by omega), section4TVarianceQ_padOneLast s β h hr0 (by omega)]

/-- The analogous original-left endpoint transfer for the padded right
Hessian-square factor. -/
theorem section4RightR_padOneLast_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4RightR s.padOneLast β h r 0 = section4THessianSquare s β h r 0 := by
  unfold section4RightR
  rw [sub_zero, section4THessianSquare_neighbor_full_eq_zero s.padOneLast β h hr0 hr,
    section4THessianSquare_padOneLast s β h hr0 (by omega)]

/-- Neighboring slope endpoints agree at every original physical level,
including the terminal interval interpreted by the auxiliary next index. -/
theorem section4TVarianceQ_neighbor_full_eq_zero_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4TVarianceQ s β h (r + 1) (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r)) =
      section4TVarianceQ s β h r (s.m (r - 1)) 0 := by
  have H := section4RightQ_padOneLast_zero s β h hr0 hr
  rw [section4RightQ_padOneLast s β h hr] at H
  simpa only [section4RightQ, sub_zero] using H

/-- Neighboring squared-Hessian endpoints agree at every physical level,
including the original terminal right interval. -/
theorem section4THessianSquare_neighbor_full_eq_zero_all_levels {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4THessianSquare s β h (r + 1) (β ^ 2 * (s.q (r + 1) - s.q r)) =
      section4THessianSquare s β h r 0 := by
  have H := section4RightR_padOneLast_zero s β h hr0 hr
  rw [section4RightR_padOneLast s β h hr] at H
  simpa only [section4RightR, sub_zero] using H

end SpinGlass.Targets
