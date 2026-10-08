module

public import Targets.Section5AdjacentCompact
public import Targets.Section5InterleavedStrict

@[expose] public section

/-!
# Strict scalar witnesses across nonphysical adjacent breakpoints

These lemmas provide the positivity input for the compact glued family away
from the physical overlap and its two neighboring trial bands.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

theorem section5InterleavedLambdaDeficit_adjacentGlue_pos_left
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j + 1 ≤ k + 1)
    (hjr : j + 1 < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q j < s.q (j + 1))
    (hqr : s.q (r - 1) < s.q r)
    (hu0 : 0 ≤ u) (hu : u ∈ Ico (s.q (j - 1)) (s.q (j + 1))) :
    0 < section5InterleavedLambdaDeficit_adjacentGlue
      (j := j) s β h r 0 (t, u) := by
  have htime : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1))) :=
    mul_pos (sub_pos.mpr ht.2)
      (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqr))
  by_cases hle : u ≤ s.q j
  · by_cases heq : u = s.q j
    · subst u
      rw [section5InterleavedLambdaDeficit_adjacentGlue, if_pos le_rfl,
        section5InterleavedLambdaDeficit_adjacent_boundary s β h r hj t 0]
      simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
      have hqnonneg : 0 ≤ s.q j := s.q_nonneg (by omega)
      have htrial : |s.q j| ∈ Icc (s.q ((j + 1) - 1)) (s.q (j + 1)) := by
        rw [abs_of_nonneg hqnonneg]
        exact ⟨by simp, hqj.le⟩
      have hbv : 0 < t * (β ^ 2 * (s.q (j + 1) - |s.q j|)) := by
        rw [abs_of_nonneg hqnonneg]
        exact mul_pos ht.1
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqj))
      exact sub_pos.mpr
        (section5InterleavedScalarV_zero_lt_left_outside s β h
          (r := r) (j := j + 1) (t := t) (u := s.q j)
          htime hr (by omega) hjr htrial hm hbv hcv)
    · rw [section5InterleavedLambdaDeficit_adjacentGlue, if_pos hle]
      simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
      have htrial : |u| ∈ Icc (s.q (j - 1)) (s.q j) := by
        rw [abs_of_nonneg hu0]
        exact ⟨hu.1, hle⟩
      have hbv : 0 < t * (β ^ 2 * (s.q j - |u|)) := by
        rw [abs_of_nonneg hu0]
        exact mul_pos ht.1 (mul_pos (sq_pos_of_ne_zero hβ)
          (sub_pos.mpr (lt_of_le_of_ne hle heq)))
      exact sub_pos.mpr
        (section5InterleavedScalarV_zero_lt_left_outside s β h
          (r := r) (j := j) (t := t) (u := u)
          htime hr hj0 (by omega) htrial hm hbv hcv)
  · have hju : s.q j < u := lt_of_not_ge hle
    rw [section5InterleavedLambdaDeficit_adjacentGlue, if_neg hle]
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    have htrial : |u| ∈ Icc (s.q ((j + 1) - 1)) (s.q (j + 1)) := by
      rw [abs_of_nonneg hu0]
      exact ⟨by simpa using hju.le, hu.2.le⟩
    have hbv : 0 < t * (β ^ 2 * (s.q (j + 1) - |u|)) := by
      rw [abs_of_nonneg hu0]
      exact mul_pos ht.1 (mul_pos (sq_pos_of_ne_zero hβ)
        (sub_pos.mpr hu.2))
    exact sub_pos.mpr
      (section5InterleavedScalarV_zero_lt_left_outside s β h
        (r := r) (j := j + 1) (t := t) (u := u)
        htime hr (by omega) hjr htrial hm hbv hcv)

theorem section5InterleavedLambdaDeficit_adjacentGlue_pos_right
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hj0 : 2 ≤ j) (hj : j + 1 ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q (j - 1) < s.q j)
    (hqr : s.q r < s.q (r + 1))
    (hu0 : 0 ≤ u) (hu : u ∈ Ioc (s.q (j - 1)) (s.q (j + 1))) :
    0 < section5InterleavedLambdaDeficit_adjacentGlue
      (j := j) s β h r 0 (t, u) := by
  have htime : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    mul_pos (sub_pos.mpr ht.2)
      (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqr))
  by_cases hle : u ≤ s.q j
  · rw [section5InterleavedLambdaDeficit_adjacentGlue, if_pos hle]
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    have htrial : |u| ∈ Icc (s.q (j - 1)) (s.q j) := by
      rw [abs_of_nonneg hu0]
      exact ⟨hu.1.le, hle⟩
    have hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1))) := by
      rw [abs_of_nonneg hu0]
      exact mul_pos ht.1 (mul_pos (sq_pos_of_ne_zero hβ)
        (sub_pos.mpr hu.1))
    exact sub_pos.mpr
      (section5InterleavedScalarV_zero_lt_right_outside s β h
        (r := r) (j := j) (t := t) (u := u)
        htime (by omega) hrj htrial hm hbv hcv)
  · have hju : s.q j < u := lt_of_not_ge hle
    rw [section5InterleavedLambdaDeficit_adjacentGlue, if_neg hle]
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    have htrial : |u| ∈ Icc (s.q ((j + 1) - 1)) (s.q (j + 1)) := by
      rw [abs_of_nonneg hu0]
      exact ⟨by simpa using hju.le, hu.2⟩
    have hcv : 0 < t * (β ^ 2 * (|u| - s.q ((j + 1) - 1))) := by
      rw [abs_of_nonneg hu0]
      simpa only [Nat.add_sub_cancel] using
        mul_pos ht.1 (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hju))
    exact sub_pos.mpr
      (section5InterleavedScalarV_zero_lt_right_outside s β h
        (r := r) (j := j + 1) (t := t) (u := u)
        htime (by omega) (by omega) htrial hm hbv hcv)

end SpinGlass.Targets
