module

public import Targets.Section5InterpolationBound

@[expose] public section

/-!
# The initial interpolation after conditioning on the frozen field

Only the interpolating shared variance remains outside the independent prefix.
The two external fields are arbitrary: the exact second-replica reflection used
for negative overlaps must reflect its field as well. All analytic statements
below concern the actual cascade and reuse its simultaneous derivative.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]

/-- The original initial variance profile with the frozen outer component
removed. Its final shared variance is entirely interpolating. -/
noncomputable def section5ConditionedInitialVariance (s : RSBScheme k)
    (β t u : ℝ) (p : ℕ) (w : ℝ) : ℝ :=
  if p = 0 then (1 - w) * t * (β ^ 2 * u)
  else section5InterpolationVariance s β t u 1 p w

/-- Conditional positive-overlap path with arbitrary two-replica fields. -/
noncomputable def section5ConditionedInitialInterpolation (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (Z : Ω → EnergySpace n) (t u : ℝ)
    (x y : Fin n → ℝ) (w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • Z ω) u)
      (k + 3) x y ∂ℙ

theorem section5ConditionedInitialVariance_nonneg (s : RSBScheme k) (β : ℝ)
    {t u w : ℝ} {p : ℕ} (hp : p ≤ k + 2)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    (hw : w ∈ Set.Icc 0 1) :
    0 ≤ section5ConditionedInitialVariance s β t u p w := by
  unfold section5ConditionedInitialVariance
  split_ifs with hp0
  · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) ht.1)
      (mul_nonneg (sq_nonneg β) hu.1)
  · exact section5InterpolationVariance_nonneg s β (by omega) hp ht
      (by simpa only [Nat.sub_self, s.q_zero] using hu) hw

theorem hasDerivAt_section5ConditionedInitialVariance (s : RSBScheme k)
    (β t u : ℝ) (p : ℕ) (w : ℝ) :
    HasDerivAt (section5ConditionedInitialVariance s β t u p)
      (-(t * β ^ 2 * (section5Rho s 1 u (p + 1) - section5Rho s 1 u p))) w := by
  unfold section5ConditionedInitialVariance
  by_cases hp : p = 0
  · subst p
    simpa [section5Rho, s.q_zero,
      mul_assoc] using
      (((hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id w)).mul_const t).mul_const
        (β ^ 2 * u)
  · simpa only [if_neg hp] using
      hasDerivAt_section5InterpolationVariance s β t u 1 p w

theorem section5ConditionedInitialVariance_pos_or_eq_zero (s : RSBScheme k) (β : ℝ)
    {p : ℕ} (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1)) (hw : w < 1) :
    0 < section5ConditionedInitialVariance s β t u p w ∨
      ∀ z, section5ConditionedInitialVariance s β t u p z = 0 := by
  by_cases hp0 : p = 0
  · subst p
    have hnonneg : 0 ≤ t * (β ^ 2 * u) :=
      mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) hu.1)
    rcases hnonneg.eq_or_lt with hz | hz
    · right
      intro z
      simp [section5ConditionedInitialVariance, mul_assoc, ← hz]
    · left
      simpa [section5ConditionedInitialVariance, mul_assoc] using
        mul_pos (sub_pos.mpr hw) hz
  · simpa only [section5ConditionedInitialVariance, if_neg hp0] using
      section5InterpolationVariance_pos_or_eq_zero s β (by omega) hp ht
        (by simpa only [Nat.sub_self, s.q_zero] using hu) hw

theorem section5ConditionedInitialVelocity_zero_of_not_pos
    (s : RSBScheme k) (β : ℝ) {p : ℕ} (hp : p ≤ k + 2)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    (hw : w < 1) (hz : ¬0 < section5ConditionedInitialVariance s β t u p w) :
    -(t * β ^ 2 * (section5Rho s 1 u (p + 1) - section5Rho s 1 u p)) = 0 := by
  obtain hpos | he := section5ConditionedInitialVariance_pos_or_eq_zero s β hp ht hu hw
  · exact (hz hpos).elim
  have H := hasDerivAt_section5ConditionedInitialVariance s β t u p w
  rw [show section5ConditionedInitialVariance s β t u p = fun _ => 0 from funext he] at H
  exact H.unique (hasDerivAt_const w 0)

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Closed-interval continuity, including all zero-variance faces, follows
from the actual jointly continuous Gaussian cascade. -/
theorem continuousOn_section5ConditionedInitialInterpolation
    (s : RSBScheme k) (β : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    ContinuousOn (section5ConditionedInitialInterpolation n s β Z t u x y)
      (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => by
      unfold section5ConditionedInitialVariance
      split_ifs
      · fun_prop
      · unfold section5InterpolationVariance
        fun_prop)
    (fun j w hw => section5ConditionedInitialVariance_nonneg s β (by omega) ht hu hw)
    (k + 2) (k + 3) (fun _ => x) (fun _ => y) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

private theorem conditioned_sqrt_time_derivative_mul {t w : ℝ}
    (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

set_option maxHeartbeats 800000 in
/-- Genuine averaged simultaneous derivative, identified with the same
actual split-replica law as every disorder-trace and field-heat contribution.
No frozen-field covariance or derivative identity is supplied as a premise. -/
theorem hasDerivAt_section5ConditionedInitialInterpolation_replica
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)]
    (x y : Fin n → ℝ) :
    HasDerivAt (section5ConditionedInitialInterpolation n s β sk.U t u x y)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5Rho s 1 u (k + 2 - j + 1) -
          section5Rho s 1 u (k + 2 - j))))
        (k + 2) (k + 3) x y) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace sk.hU
    (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega)) (k + 2) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => hasDerivAt_section5ConditionedInitialVariance s β t u (k + 2 - j) w)
    (show ∀ᶠ z in 𝓝 w, ∀ j,
      0 ≤ section5ConditionedInitialVariance s β t u (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5ConditionedInitialVariance_nonneg s β (by omega) ht hu ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5ConditionedInitialVariance s β t u (k + 2 - j) w ∨
      (section5ConditionedInitialVariance s β t u (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5ConditionedInitialVariance_pos_or_eq_zero s β
        (p := k + 2 - j) (by omega) ht hu hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz)) x y
  apply (H.const_mul (1 / (n : ℝ))).congr_deriv
  rw [conditioned_sqrt_time_derivative_mul ht.1 hw.1]
  exact normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j) w)
    (fun j => -(t * β ^ 2 * (section5Rho s 1 u (k + 2 - j + 1) -
      section5Rho s 1 u (k + 2 - j))))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg s β (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (k + 2) (k + 3)
    (fun l _ hz => section5ConditionedInitialVelocity_zero_of_not_pos s β (by omega) ht hu hw.2 hz)
    x y

/-- The actual conditional pressure has the original deterministic correction,
independently of the two fields on which the frozen Gaussian is conditioned. -/
theorem deriv_section5ConditionedInitialInterpolation_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)]
    (x y : Fin n → ℝ) :
    deriv (section5ConditionedInitialInterpolation n s β sk.U t u x y) w ≤
      -t * (2 * parisiCorrection s β) := by
  rw [(hasDerivAt_section5ConditionedInitialInterpolation_replica hn s β h sk ht hu hw x y).deriv]
  have H := averagedReplicaPressureDerivative_le
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u β ht.1
    (section5Mass s 1 0) (section5Rho s 1 u)
    (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j) w) 1 (k + 2)
    (section5Mass_endpoints s (by omega) (by omega) 0).1
    (section5Mass_endpoints s (by omega) (by omega) 0).2
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg s β (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s (by omega)
      (show (0 : ℝ) ∈ Set.Icc (s.m (1 - 1) / 2) (s.m 1) from by
        simp only [Nat.sub_self, s.m_zero, zero_div, Set.mem_Icc, le_refl, true_and]
        exact s.m_nonneg (by omega)) (by omega))
    (section5Rho_endpoints s (by omega) (by omega) u).1
    (section5Rho_endpoints s (by omega) (by omega) u).2
    (by omega) (by simp [section5Rho]) x y
  rw [section5Correction_eq s β u 0 (by omega) (by omega)] at H
  simpa only [show k + 2 + 1 - 1 = k + 2 by omega,
    show k + 2 + 1 = k + 3 by omega, Nat.sub_self, s.m_zero,
    sub_self, zero_mul, add_zero] using! H

/-- Endpoint transport for the genuine conditioned path. This is ready for
integration over the frozen Gaussian and exact second-replica reflection. -/
theorem section5ConditionedInitialInterpolation_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    section5ConditionedInitialInterpolation n s β sk.U t u x y 1 ≤
      section5ConditionedInitialInterpolation n s β sk.U t u x y 0 -
        t * (2 * parisiCorrection s β) := by
  have hc := continuousOn_section5ConditionedInitialInterpolation s β sk.hU ht hu x y
  have hd : DifferentiableOn ℝ
      (section5ConditionedInitialInterpolation n s β sk.U t u x y)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro w hw
    exact (hasDerivAt_section5ConditionedInitialInterpolation_replica hn s β h sk ht hu hw x y).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5ConditionedInitialInterpolation n s β sk.U t u x y) w ≤
        -t * (2 * parisiCorrection s β) := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5ConditionedInitialInterpolation_le hn s β h sk ht hu hw x y
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  simp only [sub_zero, mul_one] at H
  linarith

end SpinGlass.Targets
