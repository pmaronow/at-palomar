module

public import Targets.Section4Curvature
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Initial-interval curvature from the actual endpoint identity

The initial mass is compulsory zero, so raising it is not a fixed-level
competitor. For the short initial interval we instead use the genuine
stationarity identity `Q(0) = q₁`, the integral identity `Q' = -R`, and `Q ≥ 0`.
The only unproved analytic input is stated explicitly: a Lipschitz bound for
the actual Hessian-square factor on its physical variance interval.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem integral_ge_endpoint_affine_of_lipschitz
    {R : ℝ → ℝ} {a L : ℝ} (ha : 0 ≤ a)
    (hR : ContinuousOn R (Set.Icc 0 a))
    (hLip : ∀ v ∈ Set.Icc 0 a, ∀ w ∈ Set.Icc 0 a,
      |R v - R w| ≤ L * |v - w|) :
    a * R 0 - L * a ^ 2 / 2 ≤ ∫ v in (0 : ℝ)..a, R v := by
  have hf : IntervalIntegrable (fun v : ℝ => R 0 - L * v) volume 0 a :=
    (continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hg : IntervalIntegrable R volume 0 a :=
    (hR.mono (by rw [Set.uIcc_of_le ha])).intervalIntegrable
  have H := intervalIntegral.integral_mono_on ha hf hg fun v hv => by
    have Hv := (abs_le.mp (hLip 0 ⟨le_rfl, ha⟩ v hv)).2
    rw [zero_sub, abs_neg, abs_of_nonneg hv.1] at Hv
    linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => R 0) volume 0 a :=
    intervalIntegrable_const
  have hlin : IntervalIntegrable (fun v : ℝ => L * v) volume 0 a :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst hlin] at H
  rw [intervalIntegral.integral_const_mul L (fun v : ℝ => v)] at H
  simpa only [intervalIntegral.integral_const,
    integral_id, sub_zero, zero_pow (by norm_num : 2 ≠ 0), smul_eq_mul,
    mul_div_assoc] using H

/-- On the initial interval, endpoint stationarity and the nonnegative squared
slope bound the integral of the actual Hessian-square factor by `q₁`. This uses
only a genuine fixed-level minimizer and the inward overlap directions. -/
theorem section4THessianSquare_initial_integral_le_overlap_of_min
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (hβ : β ≠ 0)
    (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    (∫ v in (0 : ℝ)..(β ^ 2 * s.q 1), section4THessianSquare s β h 1 v) ≤
      s.q 1 := by
  have ha : 0 ≤ β ^ 2 * s.q 1 := mul_nonneg (sq_nonneg β) hq.le
  have hzero := section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h
    (r := 1) le_rfl (by omega) hβ (by simpa using hm)
    (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq)) hright hmin
  have H := section4TVarianceQ_baseline_sub_eq_integral s β h
    (r := 1) le_rfl (by omega) (v := 0) (w := β ^ 2 * s.q 1)
    (by simpa only [Nat.sub_self, s.q_zero, sub_zero, Set.mem_Icc] using And.intro le_rfl ha)
    (by simpa only [Nat.sub_self, s.q_zero, sub_zero, Set.mem_Icc] using And.intro ha le_rfl) ha
  rw [hzero, intervalIntegral.integral_neg] at H
  have hnonneg := (section4TVarianceQ_mem_Icc s β h 1
    (m := s.m (1 - 1))
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ (β ^ 2 * s.q 1)).1
  linarith

/-- The short initial interval has curvature bounded by its length, conditional
only on a Lipschitz constant for the actual factor `R`. No lower-endpoint sign
for the first variation is assumed. The positive initial gap is explicit. -/
theorem section4FirstVariation_initial_curvature_le_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) (hβ : β ≠ 0)
    (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤
          L * |v - w|) :
    -section4FirstVariationD2 s β h 1 (s.q 1) ≤ L * β ^ 6 * s.q 1 / 4 := by
  have hc : ContinuousOn (section4THessianSquare s β h 1)
      (Set.Icc 0 (β ^ 2 * s.q 1)) := by
    simpa only [Nat.sub_self, s.q_zero, sub_zero] using
      continuousOn_section4THessianSquare s β h (r := 1) le_rfl (by omega)
  have H := (integral_ge_endpoint_affine_of_lipschitz
    (mul_nonneg (sq_nonneg β) hq.le) hc hLip).trans
    (section4THessianSquare_initial_integral_le_overlap_of_min s β h hβ hm hq hright hmin)
  have Hb : β ^ 2 * section4THessianSquare s β h 1 0 - 1 ≤
      L * β ^ 4 * s.q 1 / 2 := by
    apply (mul_le_mul_iff_left₀ hq).mp
    nlinarith only [H]
  have Hfinal := mul_le_mul_of_nonneg_left Hb
    (div_nonneg (sq_nonneg β) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [section4FirstVariationD2, sub_self, mul_zero]
  nlinarith only [Hfinal]

/-- The initial short-gap contribution has the sixth-root rate used in
Proposition 4.10. The Hessian Lipschitz bound is an explicit remaining input. -/
theorem section4FirstVariation_initial_short_curvature_bound
    {k : ℕ} (s : RSBScheme k) (β h L ε : ℝ) (hβ : β ≠ 0)
    (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1) (hL : 0 ≤ L)
    (hshort : s.q 1 ≤ ε ^ (1 / 6 : ℝ))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤
          L * |v - w|) :
    -section4FirstVariationD2 s β h 1 (s.q 1) ≤
      L * β ^ 6 / 4 * ε ^ (1 / 6 : ℝ) := by
  apply (section4FirstVariation_initial_curvature_le_of_hessian_lipschitz
    s β h L hβ hm hq hright hmin hLip).trans
  have H := mul_le_mul_of_nonneg_left hshort
    (div_nonneg (mul_nonneg hL (by positivity : 0 ≤ β ^ 6)) (by norm_num : (0 : ℝ) ≤ 4))
  convert H using 1
  ring

end SpinGlass.Targets
