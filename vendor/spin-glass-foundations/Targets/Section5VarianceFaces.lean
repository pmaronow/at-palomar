module

/-
# Zero-variance coordinates of the actual second interpolation

In the interior interpolation interval, every varying Gaussian coordinate has
positive variance. A variance which vanishes there is identically zero, so the
chain rule need not assume a two-sided variance derivative at zero. This
retains coincident overlaps and degenerate Gaussian increments.
-/
public import Targets.TalagrandRightInterpolation

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A nonnegative frozen variance plus a nonnegative decaying variance is
either positive before time one, or identically zero. -/
theorem affineVariance_pos_or_eq_zero {A B w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : w < 1) : 0 < A + (1 - w) * B ∨ (∀ z : ℝ, A + (1 - z) * B = 0) := by
  by_cases hpos : 0 < A + (1 - w) * B
  · exact Or.inl hpos
  · right
    have hprod : 0 ≤ (1 - w) * B := mul_nonneg (by linarith) hB
    have hAn : A ≤ 0 := by linarith
    have hAz : A = 0 := le_antisymm hAn hA
    have hBp : (1 - w) * B ≤ 0 := by linarith
    have hBn : B ≤ 0 := by
      by_contra hBn
      have H := mul_pos (show 0 < 1 - w by linarith) (lt_of_not_ge hBn)
      linarith
    have hBz : B = 0 := le_antisymm hBn hB
    intro z
    simp [hAz, hBz]

/-- Actual left-interval variances require no artificial strict-overlap assumption. -/
theorem section5InterpolationVariance_pos_or_eq_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w < 1) :
    0 < section5InterpolationVariance s β t u r p w ∨
      (∀ z : ℝ, section5InterpolationVariance s β t u r p z = 0) := by
  have hA : 0 ≤ section5FrozenVariance s β t r p := by
    simpa only [section5InterpolationVariance, sub_self, zero_mul, add_zero] using
      section5InterpolationVariance_nonneg s β hr hp ht hu (w := 1) ⟨by norm_num, le_rfl⟩
  have hB : 0 ≤ t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p) :=
    mul_nonneg (mul_nonneg ht.1 (sq_nonneg β)) (sub_nonneg.mpr (section5Rho_mono s hr hu hp))
  simpa only [section5InterpolationVariance, mul_assoc] using affineVariance_pos_or_eq_zero hA hB hw

/-- The same zero-face alternative for the actual dual right-interval variances. -/
theorem section5RightInterpolationVariance_pos_or_eq_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w < 1) :
    0 < section5RightInterpolationVariance s β t u r p w ∨
      (∀ z : ℝ, section5RightInterpolationVariance s β t u r p z = 0) := by
  have hA : 0 ≤ section5FrozenVariance s β t r p := by
    simpa only [section5RightInterpolationVariance_one] using
      section5RightInterpolationVariance_nonneg s β hr hp ht hu (w := 1) ⟨by norm_num, le_rfl⟩
  have hB : 0 ≤ t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p) :=
    mul_nonneg (mul_nonneg ht.1 (sq_nonneg β)) (sub_nonneg.mpr (section5RightRho_mono s hr hu hp))
  simpa only [section5RightInterpolationVariance, mul_assoc] using affineVariance_pos_or_eq_zero hA hB hw

end SpinGlass.Targets
