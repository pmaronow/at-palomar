module

public import Targets.Section4ZeroOverlapCurvature
public import Targets.Section5RightUniform
public import Targets.Section4StationarityReduction

@[expose] public section

/-!
# The zero-first-overlap case of the local-right estimate

At a zero first overlap, one-sided optimality supplies endpoint curvature
without a near-optimality error. The existing right-factor calculus and
lambda gain therefore apply with the same beta-only constant. Combining
this boundary case with the positive-left-gap estimate covers every level
of a reduced scheme, including the terminal level.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The local-right quadratic deficit when the first overlap is zero.
No near-optimality assumption is needed in this boundary case. A collapsed
right interval is treated by the actual non-strict interpolation bound. -/
theorem constrainedPhi_local_right_initial_zero
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc 0 (s.q 2)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hlocal : section5LocalLeftConstant β 535 * u ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * u ^ 2 := by
  have hu' : u ∈ Set.Icc (s.q 1) (s.q (1 + 1)) := by simpa only [hq] using hu
  by_cases hq2 : 0 < s.q 2
  · have hQ : section4RightQ s β h 1 0 = s.q 1 := by
      rw [section4RightQ, sub_zero,
        section4TVarianceQ_neighbor_full_eq_zero_all_levels s β h le_rfl (by omega)]
      exact section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h le_rfl (by omega)
        hβ hm (Or.inr hq) (Or.inl (by simpa only [hq] using hq2)) hmin
    have hR : β ^ 2 * section4RightR s β h 1 0 ≤ 1 + 0 := by
      rw [section4RightR, sub_zero,
        section4THessianSquare_neighbor_full_eq_zero_all_levels s β h le_rfl (by omega), add_zero]
      exact section4THessianSquare_initial_zero_le_of_min s β h hβ hq hm hq2 hmin
    have hc := section5LocalLeftConstant_bounds β 535 (by norm_num)
    have hu_small : 535 * β ^ 4 * (u - s.q 1) ≤ (1 - t₀) / 4 := by
      rw [hq, sub_zero]
      have H := mul_le_mul_of_nonneg_right hc.2.1 hu.1
      nlinarith only [H, hlocal]
    have H := constrainedPhi_local_right_of_endpoint_curvature hn s β h sk
      (r := 1) le_rfl (by omega) ht ht₀ (le_refl 0) hu' hQ hR
      (by linarith) hu_small
    have hcoeff : (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 ≤ (1 - t₀) ^ 2 / 8 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith [hc.1])
    have Hgain := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg u)
    simp only [show k + 2 - 1 = k + 1 by omega, hq, sub_zero] at H
    linarith
  · have hu0 : u = 0 := by linarith [hu.1, hu.2]
    have H := constrainedPhi_le_guerraPsi_right hn s β h sk
      (r := 1) le_rfl (by omega) ⟨ht.1, ht.2.trans ht₀.le⟩ hu'
    simpa only [show k + 2 - 1 = k + 1 by omega, hu0, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, sub_zero] using H

/-- Proposition 5.2 in the exact-covariance SK setting for reduced schemes:
every physical level, including zero first overlap and terminal right intervals.
All analytic, stationarity and curvature inputs are proved. Exact scheme
reduction is available separately for the original convergence theorem. -/
theorem constrainedPhi_local_right_of_reduced_min
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β 535 * (u - s.q r) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * (u - s.q r) ^ 2 := by
  have hm : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega)
  by_cases hz : r = 1 ∧ s.q 1 = 0
  · rcases hz with ⟨rfl, hq⟩
    have H := constrainedPhi_local_right_initial_zero hn s β h sk hβ hq
      (hmass 0 (by omega)) ht ht₀ (by simpa only [hq] using hu) hmin
      (by simpa only [hq, sub_zero] using hlocal)
    simpa only [show k + 2 - 1 = k + 1 by omega, hq, sub_zero] using H
  · have hleft : s.q (r - 1) < s.q r := by
      by_cases hr1 : r = 1
      · subst r
        have hne : s.q 1 ≠ 0 := fun h => hz ⟨rfl, h⟩
        simpa only [Nat.sub_self, s.q_zero] using
          lt_of_le_of_ne (s.q_nonneg (p := 1) (by omega)) (Ne.symm hne)
      · simpa only [Nat.sub_add_cancel hr0] using hqstrict (r - 1) (by omega) (by omega)
    exact constrainedPhi_local_right_uniform hn s β h ε sk hr0 hr hβ hm hleft
      (s.overlap_directions_of_strict hqstrict hr0 hr).2 ht ht₀ hu hmin hnear hsmall hlocal

end SpinGlass.Targets
