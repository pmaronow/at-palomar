module

public import Targets.Section4ZeroOverlap
public import Targets.Section4ZeroOverlapVariation
public import Targets.OneSidedCurvature

@[expose] public section

/-!
# Curvature at a zero first overlap

The same-level right variation is an actual admissible competitor, with inner
mass `m₁` and outer mass zero. Stationarity makes its scalar slope vanish.
The inward derivative of its squared-slope expectation and one-sided
second-order minimality then give the endpoint Hessian bound directly.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- At a zero first overlap, genuine fixed-level minimality gives the
endpoint Hessian bound without a near-optimality error. The positive next
overlap supplies the admissible inward direction. -/
theorem section4THessianSquare_initial_zero_le_of_min {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (hβ : β ≠ 0) (hq : s.q 1 = 0)
    (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 := by
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hm1 : 0 < s.m 1 := by simpa only [s.m_zero] using hm
  have hS : stepD1 (parisiF s β k) (parisiFDeriv s β k)
      (s.m 1) (β ^ 2 * s.q 2) h = 0 := by
    rw [stepD1_initial_totalVariance s β h hq]
    exact parisiFDeriv_initial_zero_of_min s β h hβ hq hm
      (Or.inl (by simpa only [hq] using hq2)) hmin
  let Q := zeroOuterSquaredSlope (parisiF s β k) (parisiFDeriv s β k)
    (s.m 1) (β ^ 2 * s.q 2) h
  let c := β ^ 2 * s.m 1 / 2
  have hc : 0 < c := div_pos (mul_pos hB hm1) (by norm_num)
  have hQ0 : Q 0 = 0 := by
    dsimp only [Q]
    rw [zeroOuterSquaredSlope_zero, hS]
    norm_num
  have hDQ : HasDerivWithinAt Q (parisiFSecond s β (k + 1) h ^ 2)
      (Set.Icc 0 (β ^ 2 * s.q 2)) 0 := by
    have H := hasDerivWithinAt_zeroOuterSquaredSlope_zero
      (parisiF_hasLinearGrowth s β k) (parisiF_C2_props s β k).1
      (continuous_parisiFSecond s β k)
      (show s.m 1 ∈ Set.Icc 0 1 from ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩)
      (mul_pos hB hq2) hS
    simpa only [stepD2_initial_totalVariance s β h hq] using H
  have hmap : Set.MapsTo (fun u : ℝ => β ^ 2 * u)
      (Set.Icc 0 (s.q 2)) (Set.Icc 0 (β ^ 2 * s.q 2)) := by
    intro u hu
    exact ⟨mul_nonneg hB.le hu.1, mul_le_mul_of_nonneg_left hu.2 hB.le⟩
  have hdQ : HasDerivWithinAt (fun u => Q (β ^ 2 * u))
      (parisiFSecond s β (k + 1) h ^ 2 * β ^ 2) (Set.Icc 0 (s.q 2)) 0 := by
    have hDQ' : HasDerivWithinAt Q (parisiFSecond s β (k + 1) h ^ 2)
        (Set.Icc 0 (β ^ 2 * s.q 2)) (β ^ 2 * 0) := by simpa only [mul_zero] using hDQ
    have H := hDQ'.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul (β ^ 2)).hasDerivWithinAt hmap
    simpa only [mul_zero, mul_one] using! H
  have hd2 : HasDerivWithinAt (fun u => c * (u - Q (β ^ 2 * u)))
      (c * (1 - β ^ 2 * parisiFSecond s β (k + 1) h ^ 2))
      (Set.Icc 0 (s.q 2)) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).hasDerivWithinAt).sub hdQ).const_mul c using 1
    ring
  obtain ⟨f, hfmin, hfd⟩ := exists_section4ZeroOverlap_comparator s β h hq hmin
  have H := oneSidedCurvature_nonneg_of_min hq2 hfmin hfd
    (show c * (0 - Q (β ^ 2 * 0)) = 0 by simp only [mul_zero, hQ0, sub_self]) hd2
  have hbound : 0 ≤ 1 - β ^ 2 * parisiFSecond s β (k + 1) h ^ 2 :=
    (mul_nonneg_iff_of_pos_left hc).mp H
  rw [section4THessianSquare_initial_zero_eq_sq s β h hq]
  linarith

end SpinGlass.Targets
