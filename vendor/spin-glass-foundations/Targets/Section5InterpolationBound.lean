module

public import Targets.Section5CovarianceIdentity
public import Targets.RightInterpolationAlgebra

@[expose] public section

/-!
# The second-interpolation inequality for the actual Section 5 constructions

The SK positive-overlap left and right paths satisfy the covariance derivative
bound, and closed-interval continuity transports it to their endpoints. The
left result is the interpolation estimate (5.9). This does not supply the
uniform optimality gain of Theorem 2.4 or the remaining signed-overlap cases.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Theorem 3.1's derivative estimate for the actual left Section 5 path. -/
theorem deriv_section5Interpolation_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5Interpolation n s β h sk.U r m t u) w ≤
      -t * (2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - u ^ 2))) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  rw [(hasDerivAt_section5Interpolation_replica hn s β h sk hr hm0 ht hu hw).deriv]
  rw [← section5Correction_eq s β u m hr0 hr]
  exact averagedReplicaPressureDerivative_le
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u β ht.1
    (section5Mass s r m) (section5Rho s r u)
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w) r (k + 2)
    (section5Mass_endpoints s hr0 hr m).1 (section5Mass_endpoints s hr0 hr m).2
    (fun j => section5Mass_nonneg s hr hm0 (by omega))
    (fun j => section5InterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s hr hm (by omega))
    (section5Rho_endpoints s hr0 hr u).1 (section5Rho_endpoints s hr0 hr u).2
    (by omega) (by simp [section5Rho])
    (fun _ => h) (fun _ => h)

/-- Closed-interval endpoint transport: the actual estimate (5.9). -/
theorem section5Interpolation_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      section5Interpolation n s β h sk.U r m t u 0 -
      t * (2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - u ^ 2))) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have hc := continuousOn_section5Interpolation s β h sk.hU hr hm0 ht hu
  have hd : DifferentiableOn ℝ (section5Interpolation n s β h sk.U r m t u)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact differentiableOn_section5Interpolation s β h sk.hU hr hm0 ht hu
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5Interpolation n s β h sk.U r m t u) w ≤
        -t * (2 * parisiCorrection s β +
          (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - u ^ 2))) := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5Interpolation_le hn s β h sk hr0 hr hm ht hu hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5Interpolation_one n s β h sk.U hr0 hr m u ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

/-- The dual right path satisfies the corresponding deterministic correction. -/
theorem deriv_section5RightInterpolation_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5RightInterpolation n s β h sk.U r m t u) w ≤
      -t * (2 * parisiCorrection s β +
        (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2))) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  rw [(hasDerivAt_section5RightInterpolation_replica hn s β h sk hr hm0 ht hu hw).deriv]
  rw [← section5RightCorrection_eq s β u m hr]
  have H := averagedReplicaPressureDerivative_le
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u β ht.1
    (section5RightMass s r m) (section5RightRho s r u)
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w) (r + 1) (k + 2)
    (section5RightMass_endpoints s hr0 hr m).1 (section5RightMass_endpoints s hr0 hr m).2
    (fun j => section5RightMass_nonneg s hr hm0 (by omega))
    (fun j => section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5RightMass_mono s hr hm (by omega))
    (section5RightRho_endpoints s hr u).1 (section5RightRho_endpoints s hr u).2
    (by omega) (by simp [section5RightRho, section5Rho])
    (fun _ => h) (fun _ => h)
  simpa only [show k + 2 + 1 - (r + 1) = k + 2 - r by omega,
    show k + 2 + 1 = k + 3 by omega] using! H

/-- Endpoint transport for the dual construction, with no endpoint derivative assumption. -/
theorem section5RightInterpolation_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      section5RightInterpolation n s β h sk.U r m t u 0 -
      t * (2 * parisiCorrection s β +
        (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2))) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hc := continuousOn_section5RightInterpolation s β h sk.hU hr hm0 ht hu
  have hd : DifferentiableOn ℝ (section5RightInterpolation n s β h sk.U r m t u)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact differentiableOn_section5RightInterpolation s β h sk.hU hr hm0 ht hu
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5RightInterpolation n s β h sk.U r m t u) w ≤
        -t * (2 * parisiCorrection s β +
          (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2))) := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5RightInterpolation_le hn s β h sk hr0 hr hm ht hu hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5RightInterpolation_one n s β h sk.U hr0 hr m u ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

end SpinGlass.Targets
