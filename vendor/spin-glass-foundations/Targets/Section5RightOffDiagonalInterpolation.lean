module

public import Targets.Section5RightPhysicalNeighborWitness
public import Targets.Section5ReplicaDerivative
public import Targets.Section5InterpolationBound
public import Targets.Section5CompactTube

@[expose] public section

/-!
# Actual right off-diagonal interpolation

The constrained overlap `u` and the right-trial overlap `v` are independent
parameters.  The trial covariance path uses `v`, while the constrained pair
and its external fields use `u`.  The derivative is reduced to the checked
off-diagonal covariance inequality, so the only transport loss is the
quadratic mismatch `t β² (u-v)²/2`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def section5RightTrialComparison
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ : ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * Real.log 2 + section5RightV s β h r m
      (p.1 * (β ^ 2 * (p.2.2 - s.q r))) ℓ - ℓ * p.2.1 -
    p.1 * (2 * parisiCorrection s β +
      (m - s.m r) * (β ^ 2 / 2 * (p.2.2 ^ 2 - s.q r ^ 2)))

noncomputable def section5RightTrialDeficit
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ : ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * guerraPsi s β h p.1 - section5RightTrialComparison s β h r m ℓ p

theorem section5RightTrialDeficit_diag
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ t v : ℝ) :
    section5RightTrialDeficit s β h r m ℓ (t, (v, v)) =
      section5RightComparisonDeficit s β h r m ℓ (t, v) := by
  rfl

theorem continuous_section5RightTrialDeficit
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5RightTrialDeficit s β h r m ℓ) := by
  have H : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      2 * guerraPsi s β h p.1) := by
    unfold guerraPsi
    fun_prop
  have HV := (continuous_section5RightV_variance_lambda s β h hr hm).comp
    (show Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (p.1 * (β ^ 2 * (p.2.2 - s.q r)), ℓ)) by fun_prop)
  have HC : Continuous (section5RightTrialComparison s β h r m ℓ) := by
    unfold section5RightTrialComparison
    exact ((continuous_const.add HV).sub
      (continuous_const.mul continuous_snd.fst)).sub
      (continuous_fst.mul (by fun_prop))
  exact H.sub HC

noncomputable def section5RightInterpolationVarianceOffDiagonal
    (s : RSBScheme k) (β t v : ℝ) (r p : ℕ) (w : ℝ) : ℝ :=
  section5FrozenVariance s β t r p +
    (1 - w) * t * β ^ 2 *
      (section5RightRho s r v (p + 1) - section5RightRho s r v p)

noncomputable def section5RightInterpolationOffDiagonal
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u v w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
      (fun j => section5RightInterpolationVarianceOffDiagonal s β t v r
        (k + 2 - j) w) (k + 2 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

theorem section5RightInterpolationVarianceOffDiagonal_nonneg
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t v w : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Icc 0 1) :
    0 ≤ section5RightInterpolationVarianceOffDiagonal s β t v r p w := by
  unfold section5RightInterpolationVarianceOffDiagonal
  apply add_nonneg
  · unfold section5FrozenVariance
    apply mul_nonneg (sub_nonneg.mpr ht.2)
    split_ifs with hlt heq
    · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg β)
        (sub_nonneg.mpr (s.q_mono' p hp (p - 1) (by omega)))
  · exact mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) ht.1)
      (sq_nonneg β)) (sub_nonneg.mpr (section5RightRho_mono s hr hv hp))

theorem hasDerivAt_section5RightInterpolationVarianceOffDiagonal
    (s : RSBScheme k) (β t v : ℝ) (r p : ℕ) {w : ℝ} :
    HasDerivAt
      (section5RightInterpolationVarianceOffDiagonal s β t v r p)
      (-(t * β ^ 2 * (section5RightRho s r v (p + 1) -
        section5RightRho s r v p))) w := by
  unfold section5RightInterpolationVarianceOffDiagonal
  have H := (((hasDerivAt_id w).const_sub 1).mul_const t).mul_const (β ^ 2)
    |>.mul_const (section5RightRho s r v (p + 1) -
      section5RightRho s r v p) |>.const_add (section5FrozenVariance s β t r p)
  simpa only [zero_add, neg_mul, one_mul] using! H

theorem section5RightInterpolationOffDiagonal_zero
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u v : ℝ) :
    section5RightInterpolationOffDiagonal n s β h U r m t u v 0 =
      section5RightFieldEndpoint n s β h u r m
        (t * (β ^ 2 * (v - s.q r))) := by
  simp only [section5RightInterpolationOffDiagonal, zero_mul, Real.sqrt_zero,
    zero_smul, constrainedPairFieldBase_zero, integral_const, probReal_univ,
    smul_eq_mul, one_mul, section5RightFieldEndpoint, one_div]
  congr 2
  funext j
  exact section5RightInterpolationVariance_zero s β t v r (k + 2 - j)

set_option maxHeartbeats 4000000 in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem section5RightInterpolationOffDiagonal_one
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m u v : ℝ) {t : ℝ}
    (ht : t ≤ 1) :
    section5RightInterpolationOffDiagonal n s β h U r m t u v 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  unfold section5RightInterpolationOffDiagonal
  simp only [section5RightInterpolationVarianceOffDiagonal, one_mul, sub_self,
    zero_mul, constrainedPhi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [add_zero]
  exact section5RightCascade_one s β h (U ω) hr0 hr m u ht

theorem section5RightOffDiagonalVelocity_zero_of_not_pos
    (s : RSBScheme k) (β : ℝ) {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2)
    {t v w : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1))) (hw : w < 1)
    (hz : ¬ 0 < section5RightInterpolationVarianceOffDiagonal s β t v r p w) :
    -(t * β ^ 2 * (section5RightRho s r v (p + 1) -
      section5RightRho s r v p)) = 0 := by
  have hz' : ¬ 0 < section5RightInterpolationVariance s β t v r p w := by
    simpa only [section5RightInterpolationVarianceOffDiagonal,
      section5RightInterpolationVariance] using hz
  exact section5RightInterpolationVelocity_zero_of_not_pos s β hr hp ht hv hw hz'

set_option maxHeartbeats 800000 in
theorem hasDerivAt_section5RightInterpolationOffDiagonal_replica
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ}
    (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt
      (section5RightInterpolationOffDiagonal n s β h sk.U r m t u v)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVarianceOffDiagonal s β t v r
          (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5RightRho s r v (k + 2 - j + 1) -
          section5RightRho s r v (k + 2 - j))))
        (k + 2 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  let a : ℝ → ℝ := fun z => Real.sqrt (z * t)
  let vv : ℕ → ℝ → ℝ := fun j z =>
    section5RightInterpolationVarianceOffDiagonal s β t v r (k + 2 - j) z
  let mass : ℕ → ℝ := fun j => section5RightMass s r m (k + 2 - j)
  let vel : ℕ → ℝ := fun j =>
    -(t * β ^ 2 * (section5RightRho s r v (k + 2 - j + 1) -
      section5RightRho s r v (k + 2 - j)))
  have hmass : ∀ l, 0 ≤ mass l := by
    intro l
    exact section5RightMass_nonneg s hr hm (by omega)
  have hvv : ∀ l < k + 3, HasDerivAt (vv l)
      (vel l) w := by
    intro l hl
    dsimp [vv, vel]
    exact hasDerivAt_section5RightInterpolationVarianceOffDiagonal s β t v r
      (k + 2 - l)
  have hvv_nonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ vv l z := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    intro l
    exact section5RightInterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hz.1.le, hz.2.le⟩
  have hvv_face : ∀ l < k + 3, 0 < vv l w ∨
      (vv l =ᶠ[𝓝 w] fun _ => 0) := by
    intro l hl
    have H := section5RightInterpolationVariance_pos_or_eq_zero s β
      (p := k + 2 - l) hr (by omega) ht hv hw.2
    change 0 < section5RightInterpolationVariance s β t v r (k + 2 - l) w ∨
      (section5RightInterpolationVariance s β t v r (k + 2 - l) =ᶠ[𝓝 w]
        fun _ => 0)
    rcases H with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := hasDerivAt_constrainedPairGaussian_path_trace sk.hU a u mass vv
    hmass (k + 2 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    hvv hvv_nonneg hvv_face (fun _ => h) (fun _ => h)
  have heq : (fun z => (1 / (n : ℝ)) * ∫ ω,
      coupledFieldCascade n mass (fun l => vv l z) (k + 2 - r)
        (constrainedPairFieldBase n (a z • sk.U ω) u) (k + 3)
        (fun _ => h) (fun _ => h) ∂ℙ) =
      section5RightInterpolationOffDiagonal n s β h sk.U r m t u v := by
    funext z
    rfl
  rw [← heq]
  apply (H.const_mul (1 / (n : ℝ))).congr_deriv
  have hnorm := normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u mass
    (fun l => vv l w) vel hmass
    (fun l => section5RightInterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hw.1.le, hw.2.le⟩)
    (k + 2 - r) (k + 3)
    (fun l hl hz => by
      exact section5RightOffDiagonalVelocity_zero_of_not_pos s β hr (by omega)
        ht hv hw.2 hz)
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

theorem deriv_section5RightInterpolationOffDiagonal_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1)
    {m t u v w : ℝ} (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5RightInterpolationOffDiagonal n s β h sk.U r m t u v) w ≤
      -t * (2 * parisiCorrection s β +
        (m - s.m r) * (β ^ 2 / 2 * (v ^ 2 - s.q r ^ 2))) +
      t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  rw [(hasDerivAt_section5RightInterpolationOffDiagonal_replica hn s β h sk
    hr ((s.m_nonneg (by omega)).trans hm.1) ht hv hw).deriv]
  rw [← section5RightCorrection_eq s β v m hr]
  simpa only [show k + 2 + 1 - (r + 1) = k + 2 - r by omega,
    show k + 2 + 1 = k + 3 by omega, Pi.smul_apply] using
    (averagedReplicaPressureDerivative_le_mismatch
    (Z := fun ω => Real.sqrt (w * t) • sk.U ω)
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u v β ht.1
    (section5RightMass s r m) (section5RightRho s r v)
    (fun j => section5RightInterpolationVarianceOffDiagonal s β t v r
      (k + 2 - j) w) (r + 1) (k + 2)
    (section5RightMass_endpoints s hr0 hr m).1
    (section5RightMass_endpoints s hr0 hr m).2
    (fun j => section5RightMass_nonneg s hr
      ((s.m_nonneg (by omega)).trans hm.1) (by omega))
    (fun j => section5RightInterpolationVarianceOffDiagonal_nonneg s β hr (by omega)
      ht hv ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5RightMass_mono s hr hm (by omega))
    (section5RightRho_endpoints s hr v).1 (section5RightRho_endpoints s hr v).2
    (by omega) (by simp [section5RightRho, section5Rho])
    (fun _ => h) (fun _ => h))

theorem continuousOn_section5RightInterpolationOffDiagonal
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u v : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn
      (section5RightInterpolationOffDiagonal n s β h Z r m t u v)
      (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVarianceOffDiagonal s β t v r
      (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => by
      unfold section5RightInterpolationVarianceOffDiagonal
      fun_prop)
    (fun j w hw => section5RightInterpolationVarianceOffDiagonal_nonneg s β hr
      (by omega) ht hv hw)
    (k + 2 - r) (k + 3) (fun _ _ => h) (fun _ _ => h)
      continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

set_option maxHeartbeats 1200000 in
theorem section5RightInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {m t u v ℓ : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * Real.log 2 + section5RightV s β h r m
          (t * (β ^ 2 * (v - s.q r))) ℓ - ℓ * u -
        t * (2 * parisiCorrection s β +
          (m - s.m r) * (β ^ 2 / 2 * (v ^ 2 - s.q r ^ 2))) +
        t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hc := continuousOn_section5RightInterpolationOffDiagonal s β h sk.hU hr
    (m := m) (t := t) (u := u) (v := v) hm0 ht hv
  have hd : DifferentiableOn ℝ
      (section5RightInterpolationOffDiagonal n s β h sk.U r m t u v)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw =>
      (hasDerivAt_section5RightInterpolationOffDiagonal_replica hn s β h sk hr hm0
        ht hv hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5RightInterpolationOffDiagonal n s β h sk.U r m t u v) w ≤
        -t * (2 * parisiCorrection s β +
          (m - s.m r) * (β ^ 2 / 2 * (v ^ 2 - s.q r ^ 2))) +
          t * (β ^ 2 / 2) * (u - v) ^ 2 := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5RightInterpolationOffDiagonal_le hn s β h sk
      hr0 hr (m := m) (t := t) (u := u) (v := v) (w := w) hm ht hv hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5RightInterpolationOffDiagonal_one n s β h sk.U hr0 hr m u v ht.2] at H
  have H0 := section5RightInterpolationOffDiagonal_zero n s β h sk.U r m t u v
  have H0' := section5RightFieldEndpoint_le_offDiagonal hn s β h
    (r := r) (m := m) (t := t) (u := u) (v := v) (ℓ := ℓ) hr hm0 ht hv
    (by
      obtain ⟨p⟩ := (inferInstance : Nonempty (AT.ConstrainedPair n u))
      exact ⟨p.1.1, p.1.2, p.2⟩)
  simp only [sub_zero, mul_one] at H
  linarith

set_option maxHeartbeats 1200000 in
theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : s.m (r - 1) < s.m r) (hq : s.q r < s.q (r + 1))
    {L₁ t₀ : ℝ} (hL : 0 < L₁) (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (s.q (r + 1) - s.q r))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q (r + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let I : Type :=
    {m : ℝ // m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r)} × ℝ
  let f : I → (ℝ × ℝ) → ℝ := fun i z =>
    section5RightTrialDeficit s β h r i.1.1 i.2
      (z.1, (z.2, s.q (r + 1)))
  have hf : ∀ i : I, Continuous (f i) := by
    intro i
    have H := continuous_section5RightTrialDeficit s β h hr
      ((s.m_nonneg (by omega)).trans i.1.2.1) i.2
    exact H.comp (by fun_prop)
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∃ i : I, 0 < f i (t, s.q (r + 1)) := by
    intro t ht
    obtain ⟨m, hm, ℓ, H⟩ :=
      exists_section5RightOffDiagonalComparison_witness_at_physical_neighbor
        s β h ε hr0 hr hβ hmass hq hL ht₀ ht hmin hnear hfar hsmall
    refine ⟨(⟨m, hm⟩, ℓ), ?_⟩
    change 0 < section5RightTrialDeficit s β h r m ℓ
      (t, (s.q (r + 1), s.q (r + 1)))
    rw [section5RightTrialDeficit_diag]
    simpa only [section5RightOffDiagonalComparisonDeficit_diag] using H
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Set.Icc (0 : ℝ) t₀)
      isCompact_Icc f hf (s.q (r + 1)) hpos
  let C : ℝ := β ^ 2 / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let ρ : ℝ := min 1 (min ρ₀ (δ₀ / (4 * (C + 1))))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    refine lt_min (by norm_num) (lt_min hρ₀ ?_)
    exact div_pos hδ₀ (by positivity)
  have hρle1 : ρ ≤ 1 := min_le_left _ _
  have hρle0 : ρ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρleδ : ρ ≤ δ₀ / (4 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, δ₀ / 2, by positivity, ?_⟩
  intro t ht u hu htu n hn sk hatt
  obtain ⟨i, hi⟩ := Htube t ht u (htu.trans hρle0)
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have hm := i.1.2
  have Hactual := section5RightInterpolationOffDiagonal_endpoint_bound hn s β h sk
    hr0 hr (m := i.1.1) (t := t) (u := u) (v := s.q (r + 1))
      (ℓ := i.2) hm ⟨ht.1, ht.2.trans ht₀.le⟩ ⟨hq.le, le_rfl⟩
  have hsq : (u - s.q (r + 1)) ^ 2 ≤ ρ := by
    rw [← sq_abs]
    have hmul := mul_self_le_mul_self (abs_nonneg (u - s.q (r + 1))) htu
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
    nlinarith
  have hCρ : C * (u - s.q (r + 1)) ^ 2 ≤ δ₀ / 4 := by
    have hden : 0 < C + 1 := by linarith
    have hmul : C * ρ ≤ C * (δ₀ / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hρleδ hC
    have hfrac : C * (δ₀ / (4 * (C + 1))) ≤ δ₀ / 4 := by
      field_simp [ne_of_gt hden]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hsq hC).trans (hmul.trans hfrac)
  have htime : t * C * (u - s.q (r + 1)) ^ 2 ≤ δ₀ / 4 := by
    have h₁ := mul_le_mul_of_nonneg_right hCρ ht.1
    have h₂ : t * (δ₀ / 4) ≤ δ₀ / 4 := by
      nlinarith [ht.2, hδ₀]
    dsimp [C] at *
    nlinarith
  dsimp [f] at hi
  dsimp [section5RightTrialDeficit] at hi
  dsimp [section5RightTrialComparison] at hi
  dsimp [C] at htime
  linarith

end SpinGlass.Targets
