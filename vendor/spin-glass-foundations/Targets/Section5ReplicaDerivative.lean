module

public import Targets.CoupledReplicaField
public import Targets.Section5PressureDerivative

@[expose] public section

/-!
# The actual second-interpolation derivatives in overlap form

The original disorder trace and every original-level heat contribution are
identified under one actual averaged split law. A vanishing variance has zero
physical velocity, so no derivative at a zero variance is assumed. Summation
of the level contributions into the final covariance inequality is separate.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Explicit overlap form of the normalized trace-plus-heat derivative.
The supplied `a` is the actual variance velocity, not a new hypothesis on the
derivative. The split index is measured from the innermost level. -/
noncomputable def averagedReplicaPressureDerivative (Z : Ω → EnergySpace n)
    (u β t : ℝ) (m v a : ℕ → ℝ) (d J : ℕ) (x y : Fin n → ℝ) : ℝ :=
  t / 2 * (β ^ 2 * (1 + u ^ 2) -
    averagedConstrainedReplicaMoment Z m v d 0 J u (fun p q => pairSKCovariance β p.1 q.1) x y +
    ∑ l : Fin J, m l *
      (averagedConstrainedReplicaMoment Z m v d l (J - l) u
        (fun p q => pairSKCovariance β p.1 q.1) x y -
      averagedConstrainedReplicaMoment Z m v d (l + 1) (J - (l + 1)) u
        (fun p q => pairSKCovariance β p.1 q.1) x y)) +
  ∑ l : Fin J, a l / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (J - l) u
    (if l < d then 2 else 2 * (1 + u))
    (fun p q => pairFieldCovariance 1 1 (if l < d then 0 else 1) p.1 q.1) x y

/-- Site normalization cancels exactly N and N/2 in the checked contractions. -/
theorem normalized_trace_heat_eq_replica
    (hn : 0 < n) (β h t : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v a : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d J : ℕ) (ha : ∀ l < J, ¬0 < v l → a l = 0) (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d J (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) +
      ∑ l : Fin J, a l * (if 0 < v l then
        ∫ ω, constrainedLevelVarianceD (Z ω) u m v d l (J - (l + 1)) (v l) x y else 0)) =
      averagedReplicaPressureDerivative Z u β t m v a d J x y := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he (l : Fin J) : a l * (if 0 < v l then
      ∫ ω, constrainedLevelVarianceD (Z ω) u m v d l (J - (l + 1)) (v l) x y else 0) =
      (n : ℝ) * (a l / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (J - l) u
        (if l < d then 2 else 2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1 (if l < d then 0 else 1) p.1 q.1) x y) := by
    by_cases hp : 0 < v l
    · rw [if_pos hp]
      have hi : J - (l + 1) + 1 = J - l := by omega
      by_cases hl : (l : ℕ) < d
      · rw [integral_constrainedLevelVarianceD_independent_overlap hn hZ u m v hm hv d l
          (J - (l + 1)) hl x y, hi, if_pos hl, if_pos hl]
        ring
      · rw [integral_constrainedLevelVarianceD_shared_overlap hn hZ u m v hm hv d l
          (J - (l + 1)) hl x y, hi, if_neg hl, if_neg hl]
        ring
    · simp only [ha l l.isLt hp, zero_mul, zero_div, mul_zero]
  rw [integral_constrainedPairFieldCascadeSecond_SK_trace hn β h sk hZ u m v hm hv d J x y]
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold averagedReplicaPressureDerivative
  field_simp

/-- A zero physical left variance contributes zero velocity. -/
theorem section5InterpolationVelocity_zero_of_not_pos
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w < 1) (hz : ¬0 < section5InterpolationVariance s β t u r p w) :
    -(t * β ^ 2 * (section5Rho s r u (p + 1) - section5Rho s r u p)) = 0 := by
  obtain hpos | he := section5InterpolationVariance_pos_or_eq_zero s β hr hp ht hu hw
  · exact (hz hpos).elim
  have H := hasDerivAt_section5InterpolationVariance s β t u r p w
  rw [show section5InterpolationVariance s β t u r p = fun _ => 0 from funext he] at H
  exact H.unique (hasDerivAt_const w 0)

/-- The right interpolation has the same endpoint-safe zero-velocity property. -/
theorem section5RightInterpolationVelocity_zero_of_not_pos
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w < 1) (hz : ¬0 < section5RightInterpolationVariance s β t u r p w) :
    -(t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p)) = 0 := by
  obtain hpos | he := section5RightInterpolationVariance_pos_or_eq_zero s β hr hp ht hu hw
  · exact (hz hpos).elim
  have H := hasDerivAt_section5RightInterpolationVariance s β t u r p w
  rw [show section5RightInterpolationVariance s β t u r p = fun _ => 0 from funext he] at H
  exact H.unique (hasDerivAt_const w 0)

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged left pressure derivative, with all heat and
disorder terms under the same normalized split-replica weights. -/
theorem hasDerivAt_section5Interpolation_replica
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5Interpolation n s β h sk.U r m t u)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5Rho s r u (k + 2 - j + 1) -
          section5Rho s r u (k + 2 - j))))
        (k + 3 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_section5Interpolation_trace s β h sk.hU hr hm ht hu hw).congr_deriv
  exact normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w)
    (fun j => -(t * β ^ 2 * (section5Rho s r u (k + 2 - j + 1) -
      section5Rho s r u (k + 2 - j))))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5InterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (k + 3 - r) (k + 3)
    (fun l _ hz => section5InterpolationVelocity_zero_of_not_pos s β hr (by omega) ht hu hw.2 hz)
    (fun _ => h) (fun _ => h)

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged right pressure derivative with the dual cutoff.
Zero-mass and coincident-overlap cases are retained. -/
theorem hasDerivAt_section5RightInterpolation_replica
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5RightInterpolation n s β h sk.U r m t u)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5RightRho s r u (k + 2 - j + 1) -
          section5RightRho s r u (k + 2 - j))))
        (k + 2 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_section5RightInterpolation_trace s β h sk.hU hr hm ht hu hw).congr_deriv
  exact normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w)
    (fun j => -(t * β ^ 2 * (section5RightRho s r u (k + 2 - j + 1) -
      section5RightRho s r u (k + 2 - j))))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hw.1.le, hw.2.le⟩)
    (k + 2 - r) (k + 3)
    (fun l _ hz => section5RightInterpolationVelocity_zero_of_not_pos s β hr (by omega) ht hu hw.2 hz)
    (fun _ => h) (fun _ => h)

end SpinGlass.Targets
