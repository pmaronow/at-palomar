module

public import Targets.Section5VarianceFaces

@[expose] public section

/-!
# The actual second-interpolation coefficient paths

The square-root coefficients are differentiable before time one even when a
variance vanishes: such a coordinate is identically zero. These are genuine
coefficient derivatives, not a substitute for differentiating the full cascade.
-/

open Real

namespace SpinGlass.Targets

/-- The totalized expression is also correct on a constant zero-variance face. -/
theorem hasDerivAt_sqrt_affineVariance {A B w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : w < 1) :
    HasDerivAt (fun z => Real.sqrt (A + (1 - z) * B))
      (-B / (2 * Real.sqrt (A + (1 - w) * B))) w := by
  rcases affineVariance_pos_or_eq_zero hA hB hw with hpos | hz
  · have H := (Real.hasDerivAt_sqrt hpos.ne').comp w
      ((((hasDerivAt_id w).const_sub 1).mul_const B).const_add A)
    convert! H using 1
    ring
  · have hAz : A = 0 := by simpa using hz 1
    have hBz : B = 0 := by simpa [hAz] using hz 0
    simpa [hAz, hBz] using (hasDerivAt_const w (0 : ℝ))

/-- The disorder coefficient has a genuine derivative also when `t=0`. -/
theorem hasDerivAt_sqrt_mul_time {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    HasDerivAt (fun z => Real.sqrt (z * t)) (t / (2 * Real.sqrt (w * t))) w := by
  rcases eq_or_lt_of_le ht with hz | hpos
  · subst t
    simpa using (hasDerivAt_const w (0 : ℝ))
  · have H := (Real.hasDerivAt_sqrt (mul_pos hw hpos).ne').comp w
      ((hasDerivAt_id w).mul_const t)
    convert! H using 1
    ring

/-- The actual left field-variance speed, in the paper's forward level order. -/
theorem hasDerivAt_section5InterpolationVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) (w : ℝ) :
    HasDerivAt (section5InterpolationVariance s β t u r p)
      (-(t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p))) w := by
  have H := (((((hasDerivAt_id w).const_sub 1).mul_const t).mul_const (β ^ 2)).mul_const
    (section5Rho s r u (p + 1) - section5Rho s r u p)).const_add
      (section5FrozenVariance s β t r p)
  simpa only [section5InterpolationVariance, zero_add, neg_mul, one_mul] using! H

/-- The left field amplitude, including coincident overlaps and zero frozen variance. -/
theorem hasDerivAt_section5InterpolationAmplitude {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) (hw : w < 1) :
    HasDerivAt (fun z => Real.sqrt (section5InterpolationVariance s β t u r p z))
      (-(t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p)) /
        (2 * Real.sqrt (section5InterpolationVariance s β t u r p w))) w := by
  have hA : 0 ≤ section5FrozenVariance s β t r p := by
    simpa only [section5InterpolationVariance_one] using
      section5InterpolationVariance_nonneg s β hr hp ht hu (w := 1) ⟨by norm_num, le_rfl⟩
  have hB : 0 ≤ t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p) :=
    mul_nonneg (mul_nonneg ht.1 (sq_nonneg β)) (sub_nonneg.mpr (section5Rho_mono s hr hu hp))
  simpa only [section5InterpolationVariance, mul_assoc] using
    hasDerivAt_sqrt_affineVariance hA hB hw

/-- The actual right field-variance speed. -/
theorem hasDerivAt_section5RightInterpolationVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) (w : ℝ) :
    HasDerivAt (section5RightInterpolationVariance s β t u r p)
      (-(t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p))) w := by
  have H := (((((hasDerivAt_id w).const_sub 1).mul_const t).mul_const (β ^ 2)).mul_const
    (section5RightRho s r u (p + 1) - section5RightRho s r u p)).const_add
      (section5FrozenVariance s β t r p)
  simpa only [section5RightInterpolationVariance, zero_add, neg_mul, one_mul] using! H

/-- The right field amplitude uses the actual shifted overlap sequence. -/
theorem hasDerivAt_section5RightInterpolationAmplitude {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) (hw : w < 1) :
    HasDerivAt (fun z => Real.sqrt (section5RightInterpolationVariance s β t u r p z))
      (-(t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p)) /
        (2 * Real.sqrt (section5RightInterpolationVariance s β t u r p w))) w := by
  have hA : 0 ≤ section5FrozenVariance s β t r p := by
    simpa only [section5RightInterpolationVariance_one] using
      section5RightInterpolationVariance_nonneg s β hr hp ht hu (w := 1) ⟨by norm_num, le_rfl⟩
  have hB : 0 ≤ t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p) :=
    mul_nonneg (mul_nonneg ht.1 (sq_nonneg β)) (sub_nonneg.mpr (section5RightRho_mono s hr hu hp))
  simpa only [section5RightInterpolationVariance, mul_assoc] using
    hasDerivAt_sqrt_affineVariance hA hB hw

end SpinGlass.Targets
