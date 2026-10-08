module

public import Targets.Section4UPrime
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# Endpoint derivatives of the actual Section 4 functions

The paper's `U'(0)` is an inward derivative. We prove the derivative within
the closed physical variance interval, using a continuous extension only for
the FTC, and then transfer back to the actual U on that interval. No derivative
of the artificial extension is asserted to be a two-sided derivative of U.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual U has the expected inward derivative at both variance endpoints.
The `HasDerivWithinAt` formulation also covers a degenerate interval; uniqueness
of a numerical `derivWithin` is asserted separately only for a positive gap. -/
theorem hasDerivWithinAt_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivWithinAt (section4U s β h r)
      (section4TVarianceQ s β h r (s.m (r - 1)) v)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v := by
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  have ha : 0 ≤ a := hv.1.trans hv.2
  let Q := section4TVarianceQ s β h r (s.m (r - 1))
  let Qe : ℝ → ℝ := fun z => Q (Set.projIcc 0 a ha z)
  have hc : ContinuousOn Q (Set.Icc 0 a) :=
    continuousOn_section4TVarianceQ_variance s β h hr0 hr ⟨s.m_nonneg (by omega), hm.le⟩
  have hce : Continuous Qe := hc.restrict.comp continuous_projIcc
  have heq (z : ℝ) (hz : z ∈ Set.Icc 0 a) : Qe z = Q z := by
    simp only [Qe, Set.projIcc_of_mem ha hz]
  have hU (z : ℝ) (hz : z ∈ Set.Icc 0 a) :
      section4U s β h r z = ∫ w in (0 : ℝ)..z, Qe w := by
    rw [section4U_eq_integral s β h hr0 hr hm hz]
    apply intervalIntegral.integral_congr
    intro w hw
    rw [Set.uIcc_of_le hz.1] at hw
    exact (heq w ⟨hw.1, hw.2.trans hz.2⟩).symm
  have H := intervalIntegral.integral_hasDerivAt_right (hce.intervalIntegrable 0 v)
    hce.stronglyMeasurable.stronglyMeasurableAtFilter hce.continuousAt
  rw [heq v hv] at H
  exact H.hasDerivWithinAt.congr_of_mem hU hv

/-- Numerical inward derivative of U on a nondegenerate physical interval. -/
theorem derivWithin_section4U_eq {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1)
    (ha : 0 < β ^ 2 * (s.q r - s.q (r - 1))) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    derivWithin (section4U s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v =
      section4TVarianceQ s β h r (s.m (r - 1)) v :=
  (hasDerivWithinAt_section4U s β h hr0 hr hm hv).derivWithin
    (uniqueDiffOn_Icc ha v hv)

/-- Talagrand's overlap first-variation formula on the closed interval,
including the upper endpoint corresponding to variance zero. -/
theorem hasDerivWithinAt_section4FirstVariation_overlap {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (section4FirstVariation s β h r)
      (β ^ 2 / 2 * (u - section4TVarianceQ s β h r (s.m (r - 1))
        (β ^ 2 * (s.q r - u)))) (Set.Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : Set.MapsTo (fun z => β ^ 2 * (s.q r - z))
      (Set.Icc (s.q (r - 1)) (s.q r))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
    intro z hz
    exact ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left (by linarith [hz.1]) (sq_nonneg β)⟩
  have H := (hasDerivWithinAt_section4U s β h hr0 hr hm (hmap hu)).comp u
    (((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2)).hasDerivWithinAt hmap
  have HP := ((((hasDerivAt_id u).pow 2).const_sub (s.q r ^ 2)).const_mul
    (β ^ 2 / 4)).hasDerivWithinAt (s := Set.Icc (s.q (r - 1)) (s.q r))
  convert! (H.div_const 2).sub HP using 1
  simp only [id_eq]
  ring

end SpinGlass.Targets
