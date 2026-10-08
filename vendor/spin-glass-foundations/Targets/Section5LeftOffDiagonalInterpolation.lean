module

public import Targets.Section5RightOffDiagonalInterpolation
public import Targets.Section5ScalarComparisonContinuity

@[expose] public section

/-!
# Actual left off-diagonal interpolation

The trial overlap `v` determines the auxiliary covariance path, while the
constrained overlap `u` is kept independent.  This is the left counterpart of
`Section5RightOffDiagonalInterpolation` and is used at a physical left
breakpoint, including when the constraint lies on the other side.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def section5InterpolationVarianceOffDiagonal
    (s : RSBScheme k) (β t v : ℝ) (r p : ℕ) (w : ℝ) : ℝ :=
  section5FrozenVariance s β t r p +
    (1 - w) * t * β ^ 2 *
      (section5Rho s r v (p + 1) - section5Rho s r v p)

noncomputable def section5InterpolationOffDiagonal
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u v w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
      (fun j => section5InterpolationVarianceOffDiagonal s β t v r
        (k + 2 - j) w) (k + 3 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

theorem section5InterpolationVarianceOffDiagonal_nonneg
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t v w : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc 0 1) :
    0 ≤ section5InterpolationVarianceOffDiagonal s β t v r p w := by
  simpa only [section5InterpolationVarianceOffDiagonal,
    section5InterpolationVariance] using
    section5InterpolationVariance_nonneg s β hr hp ht hv hw

theorem hasDerivAt_section5InterpolationVarianceOffDiagonal
    (s : RSBScheme k) (β t v : ℝ) (r p : ℕ) {w : ℝ} :
    HasDerivAt (section5InterpolationVarianceOffDiagonal s β t v r p)
      (-(t * β ^ 2 * (section5Rho s r v (p + 1) -
        section5Rho s r v p))) w := by
  unfold section5InterpolationVarianceOffDiagonal
  have H := (((hasDerivAt_id w).const_sub 1).mul_const t).mul_const (β ^ 2)
    |>.mul_const (section5Rho s r v (p + 1) -
      section5Rho s r v p) |>.const_add (section5FrozenVariance s β t r p)
  simpa only [zero_add, neg_mul, one_mul] using! H

theorem section5InterpolationOffDiagonal_zero
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u v : ℝ) :
    section5InterpolationOffDiagonal n s β h U r m t u v 0 =
      section5FieldEndpoint n s β h u r m
        (t * (β ^ 2 * (s.q r - v))) := by
  simp only [section5InterpolationOffDiagonal, zero_mul, Real.sqrt_zero,
    zero_smul, constrainedPairFieldBase_zero, integral_const, probReal_univ,
    smul_eq_mul, one_mul, section5FieldEndpoint, one_div]
  congr 2
  funext j
  exact section5InterpolationVariance_zero s β t v r (k + 2 - j)

set_option maxHeartbeats 4000000 in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem section5InterpolationOffDiagonal_one
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u v : ℝ) {t : ℝ}
    (ht : t ≤ 1) :
    section5InterpolationOffDiagonal n s β h U r m t u v 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  unfold section5InterpolationOffDiagonal
  simp only [section5InterpolationVarianceOffDiagonal, one_mul, sub_self,
    zero_mul, constrainedPhi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [add_zero]
  exact section5Cascade_one s β h (U ω) hr0 hr m u ht

theorem section5InterpolationOffDiagonal_velocity_zero_of_not_pos
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t v w : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r)) (hw : w < 1)
    (hz : ¬ 0 < section5InterpolationVarianceOffDiagonal s β t v r p w) :
    -(t * β ^ 2 * (section5Rho s r v (p + 1) -
      section5Rho s r v p)) = 0 := by
  have hz' : ¬ 0 < section5InterpolationVariance s β t v r p w := by
    simpa only [section5InterpolationVarianceOffDiagonal,
      section5InterpolationVariance] using hz
  exact section5InterpolationVelocity_zero_of_not_pos s β hr hp ht hv hw hz'

theorem continuousOn_section5InterpolationOffDiagonal
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u v : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn
      (section5InterpolationOffDiagonal n s β h Z r m t u v)
      (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVarianceOffDiagonal s β t v r
      (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => by unfold section5InterpolationVarianceOffDiagonal; fun_prop)
    (fun j w hw => section5InterpolationVarianceOffDiagonal_nonneg s β hr
      (by omega) ht hv hw)
    (k + 3 - r) (k + 3) (fun _ _ => h) (fun _ _ => h)
      continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

set_option maxHeartbeats 800000 in
theorem hasDerivAt_section5InterpolationOffDiagonal_replica
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ}
    (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt
      (section5InterpolationOffDiagonal n s β h sk.U r m t u v)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVarianceOffDiagonal s β t v r
          (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5Rho s r v (k + 2 - j + 1) -
          section5Rho s r v (k + 2 - j))))
        (k + 3 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  let a : ℝ → ℝ := fun z => Real.sqrt (z * t)
  let vv : ℕ → ℝ → ℝ := fun j z =>
    section5InterpolationVarianceOffDiagonal s β t v r (k + 2 - j) z
  let mass : ℕ → ℝ := fun j => section5Mass s r m (k + 2 - j)
  let vel : ℕ → ℝ := fun j =>
    -(t * β ^ 2 * (section5Rho s r v (k + 2 - j + 1) -
      section5Rho s r v (k + 2 - j)))
  have hmass : ∀ l, 0 ≤ mass l := by
    intro l
    exact section5Mass_nonneg s hr hm (by omega)
  have hvv : ∀ l < k + 3, HasDerivAt (vv l) (vel l) w := by
    intro l hl
    dsimp [vv, vel]
    exact hasDerivAt_section5InterpolationVarianceOffDiagonal s β t v r
      (k + 2 - l)
  have hvv_nonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ vv l z := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    intro l
    exact section5InterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hz.1.le, hz.2.le⟩
  have hvv_face : ∀ l < k + 3, 0 < vv l w ∨
      (vv l =ᶠ[𝓝 w] fun _ => 0) := by
    intro l hl
    have H := section5InterpolationVariance_pos_or_eq_zero s β
      (p := k + 2 - l) hr (by omega) ht hv hw.2
    change 0 < section5InterpolationVariance s β t v r (k + 2 - l) w ∨
      (section5InterpolationVariance s β t v r (k + 2 - l) =ᶠ[𝓝 w]
        fun _ => 0)
    rcases H with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := hasDerivAt_constrainedPairGaussian_path_trace sk.hU a u mass vv
    hmass (k + 3 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    hvv hvv_nonneg hvv_face (fun _ => h) (fun _ => h)
  have heq : (fun z => (1 / (n : ℝ)) * ∫ ω,
      coupledFieldCascade n mass (fun l => vv l z) (k + 3 - r)
        (constrainedPairFieldBase n (a z • sk.U ω) u) (k + 3)
        (fun _ => h) (fun _ => h) ∂ℙ) =
      section5InterpolationOffDiagonal n s β h sk.U r m t u v := by
    funext z
    rfl
  rw [← heq]
  apply (H.const_mul (1 / (n : ℝ))).congr_deriv
  have hnorm := normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u mass
    (fun l => vv l w) vel hmass
    (fun l => section5InterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hw.1.le, hw.2.le⟩)
    (k + 3 - r) (k + 3)
    (fun l hl hz => by
      exact section5InterpolationOffDiagonal_velocity_zero_of_not_pos s β hr
        (by omega) ht hv hw.2 hz)
    (fun _ => h) (fun _ => h)
  have hsqrt : t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
    by_cases hz : t = 0
    · simp [hz]
    · have hs : Real.sqrt (w * t) ≠ 0 :=
        (Real.sqrt_pos.mpr (mul_pos hw.1
          (lt_of_le_of_ne ht.1 (Ne.symm hz)))).ne'
      field_simp [hs]
      have hs' : Real.sqrt (t * w) ≠ 0 := by simpa only [mul_comm] using hs
      exact mul_inv_cancel₀ hs'
  dsimp [a, mass, vv, vel] at hnorm ⊢
  rw [hsqrt]
  exact hnorm

theorem deriv_section5InterpolationOffDiagonal_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {m t u v w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5InterpolationOffDiagonal n s β h sk.U r m t u v) w ≤
      -t * (2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 *
          (s.q r ^ 2 - v ^ 2))) +
      t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  rw [(hasDerivAt_section5InterpolationOffDiagonal_replica hn s β h sk
    hr ((div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1)
    ht hv hw).deriv]
  rw [← section5Correction_eq s β v m hr0 hr]
  simpa only [show k + 3 + 1 - (r + 1) = k + 3 - r by omega,
    show k + 3 + 1 = k + 4 by omega, Pi.smul_apply] using
    (averagedReplicaPressureDerivative_le_mismatch
    (Z := fun ω => Real.sqrt (w * t) • sk.U ω)
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u v β ht.1
    (section5Mass s r m) (section5Rho s r v)
    (fun j => section5InterpolationVarianceOffDiagonal s β t v r
      (k + 2 - j) w) r (k + 2)
    (section5Mass_endpoints s hr0 hr m).1
    (section5Mass_endpoints s hr0 hr m).2
    (fun j => section5Mass_nonneg s hr
      ((div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1) (by omega))
    (fun j => section5InterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s hr hm (by omega))
    (section5Rho_endpoints s hr0 hr v).1 (section5Rho_endpoints s hr0 hr v).2
    (by omega) (by simp [section5Rho])
    (fun _ => h) (fun _ => h))

set_option maxHeartbeats 1200000 in
theorem section5InterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {m t u v ℓ : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * Real.log 2 + section5V s β h r m
          (t * (β ^ 2 * (s.q r - v))) ℓ - ℓ * u -
        t * (2 * parisiCorrection s β +
          (m - s.m (r - 1)) * (β ^ 2 / 2 *
            (s.q r ^ 2 - v ^ 2))) +
        t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have hc := continuousOn_section5InterpolationOffDiagonal s β h sk.hU hr hm0 ht hv
    (m := m) (t := t) (u := u) (v := v)
  have hd : DifferentiableOn ℝ
      (section5InterpolationOffDiagonal n s β h sk.U r m t u v)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw =>
      (hasDerivAt_section5InterpolationOffDiagonal_replica hn s β h sk hr hm0
        ht hv hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5InterpolationOffDiagonal n s β h sk.U r m t u v) w ≤
        -t * (2 * parisiCorrection s β +
          (m - s.m (r - 1)) * (β ^ 2 / 2 *
            (s.q r ^ 2 - v ^ 2))) +
          t * (β ^ 2 / 2) * (u - v) ^ 2 := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5InterpolationOffDiagonal_le hn s β h sk
      hr0 hr (m := m) (t := t) (u := u) (v := v) hm ht hv hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5InterpolationOffDiagonal_one n s β h sk.U hr0 hr m u v ht.2] at H
  have H0 := section5InterpolationOffDiagonal_zero n s β h sk.U r m t u v
  have H0' := section5FieldEndpoint_le hn s β h u hr (m := m)
    (v := t * (β ^ 2 * (s.q r - v))) hm0
    (by
      have hβ : 0 ≤ β ^ 2 := sq_nonneg β
      constructor
      · exact mul_nonneg ht.1
          (mul_nonneg hβ (sub_nonneg.mpr hv.2))
      · nlinarith [mul_nonneg hβ (sub_nonneg.mpr hv.1),
          mul_nonneg hβ (sub_nonneg.mpr hv.2), ht.2])
    (by
      obtain ⟨p⟩ := (inferInstance : Nonempty (AT.ConstrainedPair n u))
      exact ⟨p.1.1, p.1.2, p.2⟩) ℓ
  simp only [sub_zero, mul_one] at H
  linarith

end SpinGlass.Targets
