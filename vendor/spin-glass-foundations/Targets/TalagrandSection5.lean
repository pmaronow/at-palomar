module

/-
# The inserted-level construction of Talagrand, Section 5

The paper's k is this project's k+1. Forward indices p describe (5.5)--(5.13);
the actual cascades integrate them in reverse order. `w` denotes the second
interpolation time and `v` the split variance in (5.10)--(5.16).

This file treats the positive-overlap, left-interval construction. It does not
assert the covariance derivative bound of Theorem 3.1 or the optimality estimates.
-/
public import Targets.CoupledEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The inserted overlap sequence (5.5). -/
def section5Rho {k : ℕ} (s : RSBScheme k) (r : ℕ) (u : ℝ) (p : ℕ) : ℝ :=
  if p < r then s.q p else if p = r then u else s.q (p - 1)

/-- The masses in (5.6), before reversing the level order. -/
noncomputable def section5Mass {k : ℕ} (s : RSBScheme k) (r : ℕ) (m : ℝ) (p : ℕ) : ℝ :=
  if p < r then s.m p / 2 else if p = r then m else s.m (p - 1)

/-- The one-site increment variances (5.10)--(5.13), with SK covariance. -/
def section5Variance {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (p : ℕ) (v : ℝ) : ℝ :=
  if r < p then β ^ 2 * (s.q p - s.q (p - 1))
  else if p = r then v
  else if p + 1 = r then β ^ 2 * (s.q r - s.q (r - 1)) - v
  else β ^ 2 * (s.q (p + 1) - s.q p)

/-- The frozen Z variance in (5.7); it is exactly zero at the inserted level. -/
def section5FrozenVariance {k : ℕ} (s : RSBScheme k) (β t : ℝ) (r p : ℕ) : ℝ :=
  (1 - t) * (if p < r then β ^ 2 * (s.q (p + 1) - s.q p)
    else if p = r then 0 else β ^ 2 * (s.q p - s.q (p - 1)))

/-- The combined Z + sqrt(1-w)y variance in the second interpolation. -/
def section5InterpolationVariance {k : ℕ} (s : RSBScheme k) (β t u : ℝ)
    (r p : ℕ) (w : ℝ) : ℝ :=
  section5FrozenVariance s β t r p +
    (1 - w) * t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p)

theorem section5Mass_nonneg {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) {p : ℕ} (hp : p ≤ k + 2) :
    0 ≤ section5Mass s r m p := by
  unfold section5Mass
  split_ifs with hpr hpr
  · exact div_nonneg (s.m_nonneg (by omega)) (by norm_num)
  · exact hm
  · exact s.m_nonneg (by omega)

/-- The allowed inserted-mass interval in (5.6) gives a nondecreasing sequence. -/
theorem section5Mass_mono {k : ℕ} (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1)
    {m : ℝ} (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    {p : ℕ} (hp : p ≤ k + 1) : section5Mass s r m p ≤ section5Mass s r m (p + 1) := by
  unfold section5Mass
  by_cases hlt : p < r
  · by_cases heq : p + 1 = r
    · have hnl : ¬p + 1 < r := by omega
      have hi : r - 1 = p := by omega
      simpa only [if_pos hlt, if_neg hnl, if_pos heq, hi] using hm.1
    · have hl : p + 1 < r := by omega
      simp only [if_pos hlt, if_pos hl]
      exact div_le_div_of_nonneg_right (s.m_mono p (by omega)) (by norm_num)
  · by_cases heq : p = r
    · subst p
      simpa only [lt_self_iff_false, if_false, if_true,
        if_neg (show ¬r + 1 < r by omega), if_neg (show r + 1 ≠ r by omega),
        Nat.add_sub_cancel] using hm.2
    · have hnl : ¬p + 1 < r := by omega
      have hne : p + 1 ≠ r := by omega
      simp only [if_neg hlt, if_neg heq, if_neg hnl, if_neg hne, Nat.add_sub_cancel]
      exact s.m_mono' p hp (p - 1) (by omega)

theorem section5Mass_endpoints {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    section5Mass s r m 0 = 0 ∧ section5Mass s r m (k + 2) = 1 := by
  simp only [section5Mass, if_pos (show 0 < r by omega),
    if_neg (show ¬k + 2 < r by omega), if_neg (show k + 2 ≠ r by omega)]
  simp [s.m_zero, s.m_top, show k + 2 - 1 = k + 1 by omega]

theorem section5Rho_mono {k : ℕ} (s : RSBScheme k) {r : ℕ} (hr : r ≤ k + 1)
    {u : ℝ} (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    {p : ℕ} (hp : p ≤ k + 2) : section5Rho s r u p ≤ section5Rho s r u (p + 1) := by
  unfold section5Rho
  by_cases hlt : p < r
  · by_cases heq : p + 1 = r
    · have hnl : ¬p + 1 < r := by omega
      have hi : r - 1 = p := by omega
      simpa only [if_pos hlt, if_neg hnl, if_pos heq, hi] using hu.1
    · have hl : p + 1 < r := by omega
      simp only [if_pos hlt, if_pos hl]
      exact s.q_mono p (by omega)
  · by_cases heq : p = r
    · subst p
      simpa only [lt_self_iff_false, if_false, if_true,
        if_neg (show ¬r + 1 < r by omega), if_neg (show r + 1 ≠ r by omega),
        Nat.add_sub_cancel] using hu.2
    · have hnl : ¬p + 1 < r := by omega
      have hne : p + 1 ≠ r := by omega
      simp only [if_neg hlt, if_neg heq, if_neg hnl, if_neg hne, Nat.add_sub_cancel]
      exact s.q_mono' p hp (p - 1) (by omega)

theorem section5Rho_endpoints {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (u : ℝ) :
    section5Rho s r u 0 = 0 ∧ section5Rho s r u (k + 3) = 1 := by
  simp only [section5Rho, if_pos (show 0 < r by omega),
    if_neg (show ¬k + 3 < r by omega), if_neg (show k + 3 ≠ r by omega)]
  simp [s.q_zero, s.q_top, show k + 3 - 1 = k + 2 by omega]

theorem section5Variance_continuous {k : ℕ} (s : RSBScheme k) (β : ℝ) (r p : ℕ) :
    Continuous (section5Variance s β r p) := by
  unfold section5Variance
  split_ifs <;> fun_prop

theorem section5Variance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ) {r : ℕ}
    (hr : r ≤ k + 1) {p : ℕ} (hp : p ≤ k + 2) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    0 ≤ section5Variance s β r p v := by
  unfold section5Variance
  split_ifs with hpr hpr hpr
  · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono' p hp (p - 1) (by omega)))
  · exact hv.1
  · exact sub_nonneg.mpr hv.2
  · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))

/-- At the disorder-free endpoint the combined variances are exactly (5.16),
not those of the original t=0 Guerra cascade. -/
theorem section5InterpolationVariance_zero {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) :
    section5InterpolationVariance s β t u r p 0 =
      section5Variance s β r p (t * (β ^ 2 * (s.q r - u))) := by
  unfold section5InterpolationVariance section5FrozenVariance section5Variance section5Rho
  by_cases hlt : p < r
  · have hne : p ≠ r := by omega
    have hng : ¬r < p := by omega
    simp only [if_pos hlt, if_neg hng, if_neg hne]
    by_cases heq : p + 1 = r
    · have hnl : ¬p + 1 < r := by omega
      simp only [if_pos heq, if_neg hnl]
      have hprev : r - 1 = p := by omega
      rw [hprev, heq]
      ring
    · have hl : p + 1 < r := by omega
      simp only [if_neg heq, if_pos hl]
      ring
  · by_cases heq : p = r
    · subst p
      simp
      ring
    · have hgt : r < p := by omega
      have hnl : ¬p + 1 < r := by omega
      have hne : p + 1 ≠ r := by omega
      simp only [if_neg hlt, if_neg heq, if_pos hgt, if_neg hnl, if_neg hne,
        Nat.add_sub_cancel]
      ring

@[simp] theorem section5InterpolationVariance_one {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) :
    section5InterpolationVariance s β t u r p 1 = section5FrozenVariance s β t r p := by
  simp [section5InterpolationVariance]

@[simp] theorem section5FrozenVariance_inserted {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (r : ℕ) : section5FrozenVariance s β t r r = 0 := by
  simp [section5FrozenVariance]

theorem section5SplitVariance_mem {k : ℕ} (s : RSBScheme k) (β : ℝ) {r : ℕ}
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    t * (β ^ 2 * (s.q r - u)) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) := by
  have ha : 0 ≤ β ^ 2 * (s.q r - u) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.2)
  constructor
  · exact mul_nonneg ht.1 ha
  · calc
      t * (β ^ 2 * (s.q r - u)) ≤ 1 * (β ^ 2 * (s.q r - u)) :=
        mul_le_mul_of_nonneg_right ht.2 ha
      _ ≤ β ^ 2 * (s.q r - s.q (r - 1)) := by nlinarith [sq_nonneg β, hu.1]

/-- All variances along the second interpolation are nonnegative, including
both endpoints and degenerate overlap levels. -/
theorem section5InterpolationVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc 0 1) : 0 ≤ section5InterpolationVariance s β t u r p w := by
  have hzero : 0 ≤ section5InterpolationVariance s β t u r p 0 := by
    rw [section5InterpolationVariance_zero]
    exact section5Variance_nonneg s β hr hp (section5SplitVariance_mem s β ht hu)
  have hfrozen : 0 ≤ section5FrozenVariance s β t r p := by
    unfold section5FrozenVariance
    apply mul_nonneg (sub_nonneg.mpr ht.2)
    split_ifs with hlt heq
    · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono' p hp (p - 1) (by omega)))
  have he : section5InterpolationVariance s β t u r p w =
      w * section5FrozenVariance s β t r p +
        (1 - w) * section5InterpolationVariance s β t u r p 0 := by
    unfold section5InterpolationVariance
    ring
  rw [he]
  exact add_nonneg (mul_nonneg hw.1 hfrozen) (mul_nonneg (sub_nonneg.mpr hw.2) hzero)

/-- Talagrand's V(lambda,m,v) in (5.15), including the outer zero-mass level. -/
noncomputable def section5V {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m v ℓ : ℝ) : ℝ :=
  splitScalarCascade (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j))
    (k + 3 - r) (k + 3) v ℓ (h, h)

/-- The canonical Gaussian, field-only constrained endpoint with the inserted
level. This is a concrete finite nested integral, not a hypothesized bound. -/
noncomputable def section5FieldEndpoint {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h u : ℝ) (r : ℕ) (m v : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j) v) (k + 3 - r)
    (constrainedBase n (0 : EnergySpace n) 0 0 u) (k + 3) (fun _ => h) (fun _ => h)

/-- The normalized endpoint inequality of (5.17) for the explicit Section 5
Gaussian construction. The second-interpolation derivative bound is not used. -/
theorem section5FieldEndpoint_le {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β h u : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5FieldEndpoint n s β h u r m v ≤ 2 * Real.log 2 + section5V s β h r m v ℓ - ℓ * u := by
  have H := constrainedFieldCascade_le hn
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j))
    (k + 3 - r) (k + 3) v
    (fun j => section5Variance_nonneg s β hr (by omega) hv) u ℓ h hu
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hnR.le)
  simpa only [section5FieldEndpoint, section5V, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul] using H'

/-- The actual lambda derivative of V follows from the reused tilted recursion.
Identification with U' in Lemma 5.8 is a separate remaining step. -/
theorem hasDerivAt_section5V {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (v ℓ : ℝ) :
    HasDerivAt (section5V s β h r m v)
      (splitScalarCascadeD (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5Variance s β r (k + 2 - j))
        (k + 3 - r) (k + 3) v ℓ (h, h)) ℓ := by
  exact (splitScalarCascade_good _ _
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j))
    (k + 3 - r) (k + 3)).hasDeriv v ℓ (h, h)

end SpinGlass.Targets
