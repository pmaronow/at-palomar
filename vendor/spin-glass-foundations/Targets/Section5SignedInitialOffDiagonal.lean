module

public import Targets.Section5SignedInitialConditioning
public import Targets.Section5OffDiagonalAlgebra

@[expose] public section

/-!
# Off-diagonal conditioned initial interpolation

The constrained overlap `u` and the nonnegative trial endpoint `v` are kept
separate.  This is the signed-initial analogue of the interleaved
off-diagonal path and is needed to cross the breakpoint `u = -q₁`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

private theorem offdiag_conditioned_sqrt_time_derivative_mul {t w : ℝ}
    (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

noncomputable def section5ConditionedInitialInterpolationOffDiagonal
    (n : ℕ) (s : RSBScheme k) (β : ℝ) (Z : Ω → EnergySpace n)
    (t u v : ℝ) (x y : Fin n → ℝ) (w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • Z ω) u)
      (k + 3) x y ∂ℙ

theorem continuousOn_section5ConditionedInitialInterpolationOffDiagonal
    (s : RSBScheme k) (β : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {t u v : ℝ} (ht : t ∈ Icc 0 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    ContinuousOn
      (section5ConditionedInitialInterpolationOffDiagonal n s β Z t u v x y)
      (Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => by
      unfold section5ConditionedInitialVariance
      split_ifs
      · fun_prop
      · unfold section5InterpolationVariance
        fun_prop)
    (fun j w hw => section5ConditionedInitialVariance_nonneg s β (by omega) ht hv hw)
    (k + 2) (k + 3) (fun _ => x) (fun _ => y) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

theorem hasDerivAt_section5ConditionedInitialInterpolationOffDiagonal
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {t u v w : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1)
    (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    HasDerivAt
      (section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t u v x y)
      (averagedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) u β t
        (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j) w)
        (fun j => -(t * β ^ 2 * (section5Rho s 1 v (k + 2 - j + 1) -
          section5Rho s 1 v (k + 2 - j))))
        (k + 2) (k + 3) x y) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace sk.hU
    (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega)) (k + 2) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => hasDerivAt_section5ConditionedInitialVariance s β t v (k + 2 - j) w)
    (show ∀ᶠ z in 𝓝 w, ∀ j,
      0 ≤ section5ConditionedInitialVariance s β t v (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5ConditionedInitialVariance_nonneg s β (by omega) ht hv
        ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5ConditionedInitialVariance s β t v (k + 2 - j) w ∨
      (section5ConditionedInitialVariance s β t v (k + 2 - j) =ᶠ[𝓝 w]
        fun _ => 0) from by
      intro j hj
      rcases section5ConditionedInitialVariance_pos_or_eq_zero s β
        (p := k + 2 - j) (by omega) ht hv hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz)) x y
  apply (H.const_mul (1 / (n : ℝ))).congr_deriv
  rw [offdiag_conditioned_sqrt_time_derivative_mul ht.1 hw.1]
  exact normalized_trace_heat_eq_replica hn β h t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j) w)
    (fun j => -(t * β ^ 2 * (section5Rho s 1 v (k + 2 - j + 1) -
      section5Rho s 1 v (k + 2 - j))))
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg s β (by omega) ht hv
      ⟨hw.1.le, hw.2.le⟩)
    (k + 2) (k + 3)
    (fun l _ hz => section5ConditionedInitialVelocity_zero_of_not_pos
      s β (by omega) ht hv hw.2 hz) x y

theorem deriv_section5ConditionedInitialInterpolationOffDiagonal_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {t u v w : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1)
    (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Ioo 0 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    deriv (section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t u v x y) w ≤
      -t * (2 * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  rw [(hasDerivAt_section5ConditionedInitialInterpolationOffDiagonal
    hn s β h sk ht hu hv hw x y).deriv]
  have H := averagedReplicaPressureDerivative_le_mismatch
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u v β ht.1
    (section5Mass s 1 0) (section5Rho s 1 v)
    (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j) w)
    1 (k + 2)
    (section5Mass_endpoints s (by omega) (by omega) 0).1
    (section5Mass_endpoints s (by omega) (by omega) 0).2
    (fun j => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun j => section5ConditionedInitialVariance_nonneg s β (by omega) ht hv
      ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s (by omega)
      (show (0 : ℝ) ∈ Icc (s.m (1 - 1) / 2) (s.m 1) from by
        simp only [Nat.sub_self, s.m_zero, zero_div, mem_Icc, le_refl, true_and]
        exact s.m_nonneg (by omega)) (by omega))
    (section5Rho_endpoints s (by omega) (by omega) v).1
    (section5Rho_endpoints s (by omega) (by omega) v).2
    (by omega) (by simp [section5Rho]) x y
  rw [section5Correction_eq s β v 0 (by omega) (by omega)] at H
  simpa only [show k + 2 + 1 - 1 = k + 2 by omega,
    show k + 2 + 1 = k + 3 by omega, Nat.sub_self, s.m_zero,
    sub_self, zero_mul, add_zero] using! H

theorem section5ConditionedInitialInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1))
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t u v x y 1 ≤
      section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t u v x y 0 -
        t * (2 * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  have hc := continuousOn_section5ConditionedInitialInterpolationOffDiagonal
    s β sk.hU ht hu hv x y
  have hd : DifferentiableOn ℝ
      (section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t u v x y)
      (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro w hw
    exact (hasDerivAt_section5ConditionedInitialInterpolationOffDiagonal
      hn s β h sk ht hu hv hw x y).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Icc (0 : ℝ) 1),
      deriv (section5ConditionedInitialInterpolationOffDiagonal
        n s β sk.U t u v x y) w ≤
        -t * (2 * parisiCorrection s β) +
          t * (β ^ 2 / 2) * (u - v) ^ 2 := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5ConditionedInitialInterpolationOffDiagonal_le
      hn s β h sk ht hu hv hw x y
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  simp only [sub_zero, mul_one] at H
  linarith

theorem integrable_section5ConditionedInitialInterpolationOffDiagonal_frozen
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) {t u v w : ℝ} (ht : t ∈ Icc 0 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 (s.q 1)) (hw : w ∈ Icc 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    Integrable (fun z => section5ConditionedInitialInterpolationOffDiagonal
      n s β Z t u v
      (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
      (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) w)
      (piGauss n) := by
  exact (integrable_constrainedPairFieldCascade_frozen_pair hZ (Real.sqrt (w * t))
    ((1 - t) * (β ^ 2 * s.q 1)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t v (k + 2 - j) w)
    (fun _ => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun _ => section5ConditionedInitialVariance_nonneg s β (by omega) ht hv hw)
    (k + 2) (k + 3) (fun _ => h)).integral_prod_right.const_mul (1 / (n : ℝ))

theorem section5ConditionedInitialInterpolationOffDiagonal_one_eq
    (s : RSBScheme k) (β : ℝ) (Z : Ω → EnergySpace n)
    (t u v : ℝ) (x y : Fin n → ℝ) :
    section5ConditionedInitialInterpolationOffDiagonal n s β Z t u v x y 1 =
      section5ConditionedInitialInterpolation n s β Z t u x y 1 := by
  unfold section5ConditionedInitialInterpolationOffDiagonal
    section5ConditionedInitialInterpolation
  congr 2
  funext j
  simp [section5ConditionedInitialVariance]

/-- Signed off-diagonal path after conditioning on the retained positive
field. The original overlaps `u,v` are negative; the conditioned state space
has overlap `-u` and the trial path ends at `-v`. -/
noncomputable def section5SignedInitialInterpolationOffDiagonal
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (Z : Ω → EnergySpace n)
    (t u v w : ℝ) : ℝ :=
  ∫ z, section5ConditionedInitialInterpolationOffDiagonal n s β Z t (-u) (-v)
    (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
    (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) w ∂piGauss n

/-- Direct reflected form of the off-diagonal signed path.  The constraint is
`u`, while every trial covariance (including the anti-shared prefix) uses
`v`. -/
noncomputable def section5SignedInitialInterpolationOffDiagonalDirect
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (Z : Ω → EnergySpace n)
    (t u v w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, section5SignedInitialOuter n s β t v w
    (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5InterpolationVariance s β t (-v) 1 (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • Z ω) u) (k + 2))
    (fun _ => h) (fun _ => h) ∂ℙ

theorem section5SignedInitial_anti_prefix_offDiagonal_eq_conditioned
    (s : RSBScheme k) (β t u v w : ℝ) (U : EnergySpace n)
    (hU : ∀ σ, U (configFlip n σ) = U σ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 ((1 - w) * t * (β ^ 2 * (-v)))
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1))
      (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5InterpolationVariance s β t (-v) 1 (k + 2 - j) w)
        (k + 2) (constrainedPairFieldBase n U u) (k + 2)) x y =
      coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5ConditionedInitialVariance s β t (-v) (k + 2 - j) w)
        (k + 2) (constrainedPairFieldBase n U (-u)) (k + 3) x (-y) := by
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5InterpolationVariance s β t (-v) 1 (k + 2 - j) w
  let V' := fun j => section5ConditionedInitialVariance s β t (-v) (k + 2 - j) w
  have hV : ∀ j < k + 2, V j = V' j := by
    intro j hj
    simp only [V, V', section5ConditionedInitialVariance,
      if_neg (show k + 2 - j ≠ 0 by omega)]
  have he (x y : Fin n → ℝ) :
      coupledFieldCascade n M V (k + 2) (constrainedPairFieldBase n U u) (k + 2) x (-y) =
      coupledFieldCascade n M V' (k + 2) (constrainedPairFieldBase n U (-u))
        (k + 2) x y := by
    have H := coupledFieldCascade_independent_flip_second M V (d := k + 2) le_rfl
      (constrainedPairFieldBase_flip U hU u) x (-y)
    rw [coupledFieldCascade_congr_variance M V V' (k + 2) (k + 2)
      (constrainedPairFieldBase n U (-u)) hV, neg_neg] at H
    exact H
  rw [coupledLinearStep_anti_flip_second]
  change sharedStepPi n 0 ((1 - w) * t * (β ^ 2 * (-v)))
    (fun x y => coupledFieldCascade n M V (k + 2)
      (constrainedPairFieldBase n U u) (k + 2) x (-y)) x (-y) = _
  rw [show (fun x y => coupledFieldCascade n M V (k + 2)
      (constrainedPairFieldBase n U u) (k + 2) x (-y)) =
      coupledFieldCascade n M V' (k + 2) (constrainedPairFieldBase n U (-u)) (k + 2)
      from funext fun x => funext (he x)]
  change _ = coupledFieldCascade n M V' (k + 2)
    (constrainedPairFieldBase n U (-u)) ((k + 2) + 1) x (-y)
  conv_rhs => rw [coupledFieldCascade, if_neg (lt_irrefl _)]
  simp only [M, V', Nat.sub_self, section5Mass, section5ConditionedInitialVariance,
    show (0 : ℕ) < 1 by omega, if_true, s.m_zero, zero_div, mul_zero]

/-- Conditioning/reflection identity for separated signed constraint and trial
overlaps. -/
theorem section5SignedInitialInterpolationOffDiagonal_eq_direct
    (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u v w : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) (hw : w ∈ Icc 0 1)
    [Nonempty (AT.ConstrainedPair n u)] :
    section5SignedInitialInterpolationOffDiagonalDirect n s β h sk.U t u v w =
      section5SignedInitialInterpolationOffDiagonal n s β h sk.U t u v w := by
  letI := constrainedPair_nonempty_neg (n := n) u
  have hvn : -v ∈ Icc 0 (s.q 1) := by constructor <;> linarith [hv.1, hv.2]
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5InterpolationVariance s β t (-v) 1 (k + 2 - j) w
  let V' := fun j => section5ConditionedInitialVariance s β t (-v) (k + 2 - j) w
  let b := (1 - t) * (β ^ 2 * s.q 1)
  have hm (j) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hvV (j) : 0 ≤ V j :=
    (section5SignedInitial_variances_nonneg s β ht hv hw).2.2 _ (by omega)
  have hvV' (j) : 0 ≤ V' j :=
    section5ConditionedInitialVariance_nonneg s β (by omega) ht hvn hw
  let G := fun (ω : Ω) (z : Fin n → ℝ) => coupledFieldCascade n M V' (k + 2)
    (constrainedPairFieldBase n (Real.sqrt (w * t) • sk.U ω) (-u)) (k + 3)
    (fun i => h + Real.sqrt b * z i) (fun i => -(h + Real.sqrt b * z i))
  have hi : Integrable (fun p : Ω × (Fin n → ℝ) => G p.1 p.2)
      ((ℙ : Measure Ω).prod (piGauss n)) :=
    integrable_constrainedPairFieldCascade_frozen_pair sk.hU (Real.sqrt (w * t)) b
      (-u) M V' hm hvV' (k + 2) (k + 3) (fun _ => h)
  have he : section5SignedInitialInterpolationOffDiagonalDirect n s β h sk.U t u v w =
      (1 / (n : ℝ)) * ∫ ω, ∫ z, G ω z ∂piGauss n ∂ℙ := by
    unfold section5SignedInitialInterpolationOffDiagonalDirect
    congr 1
    apply integral_congr_ae
    filter_upwards [skDisorder_even_ae β h sk] with ω hω
    have hscaled : ∀ σ, (Real.sqrt (w * t) • sk.U ω) (configFlip n σ) =
        (Real.sqrt (w * t) • sk.U ω) σ := by
      intro σ
      simpa only [PiLp.smul_apply, smul_eq_mul] using
        congrArg (fun z => Real.sqrt (w * t) * z) (hω σ)
    rw [section5SignedInitialOuter, coupledLinearStep_shared, mul_zero,
      coupledLinearStep_zero_signed_shared_commute
        (constrainedPairFieldCascade_growth (Real.sqrt (w * t) • sk.U ω) u M V hm hvV
          (k + 2) (k + 2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z =>
      section5SignedInitial_anti_prefix_offDiagonal_eq_conditioned s β t u v w
        (Real.sqrt (w * t) • sk.U ω) hscaled
        (fun i => h + Real.sqrt b * z i) (fun i => h + Real.sqrt b * z i)
  rw [he, integral_integral_swap hi, ← integral_const_mul]
  rfl

theorem section5SignedInitialInterpolationOffDiagonal_one
    (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u v : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    section5SignedInitialInterpolationOffDiagonal n s β h sk.U t u v 1 =
      constrainedPhi n s β h sk.U (k + 1) t u := by
  rw [← section5SignedInitialInterpolationOffDiagonal_eq_direct s β h sk
    ht hu hv (w := 1) ⟨zero_le_one, le_rfl⟩]
  unfold section5SignedInitialInterpolationOffDiagonalDirect constrainedPhi
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    simpa only [section5SignedInitialOuter_one, section5InterpolationVariance_one,
      one_mul] using
      section5SignedInitialCascade_one s β h (sk.U ω) u ht.2

theorem section5SignedInitialInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      section5SignedInitialInterpolationOffDiagonal n s β h sk.U t u v 0 -
        t * (2 * parisiCorrection s β) + t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  letI : Nonempty (AT.ConstrainedPair n (-u)) := constrainedPair_nonempty_neg (n := n) u
  have hupos : -u ∈ Icc 0 1 := by
    constructor
    · linarith [hu.2]
    · linarith [hu.1]
  have hvpos : -v ∈ Icc 0 (s.q 1) := by constructor <;> linarith [hv.1, hv.2]
  have hi0 := integrable_section5ConditionedInitialInterpolationOffDiagonal_frozen
    s β h sk.hU ht hupos hvpos (w := 0) ⟨le_rfl, zero_le_one⟩
  have hi1 := integrable_section5ConditionedInitialInterpolationOffDiagonal_frozen
    s β h sk.hU ht hupos hvpos (w := 1) ⟨zero_le_one, le_rfl⟩
  rw [← section5SignedInitialInterpolationOffDiagonal_one s β h sk ht hu hv]
  unfold section5SignedInitialInterpolationOffDiagonal
  calc
    _ ≤ ∫ z, section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t (-u) (-v)
        (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
        (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) 0 -
          t * (2 * parisiCorrection s β) +
          t * (β ^ 2 / 2) * ((-u) - (-v)) ^ 2 ∂piGauss n :=
      integral_mono hi1 ((hi0.sub (integrable_const _)).add (integrable_const _))
        (fun z => section5ConditionedInitialInterpolationOffDiagonal_endpoint_bound
          hn s β h sk ht hupos hvpos _ _)
    _ = _ := by
      have hmismatch : (-u - -v) ^ 2 = (u - v) ^ 2 := by ring
      rw [hmismatch]
      let f : (Fin n → ℝ) → ℝ := fun z =>
        section5ConditionedInitialInterpolationOffDiagonal n s β sk.U t (-u) (-v)
          (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
          (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) 0
      have hf : Integrable f (piGauss n) := by simpa [f] using hi0
      change (∫ z, (f z - t * (2 * parisiCorrection s β)) +
        t * (β ^ 2 / 2) * (u - v) ^ 2 ∂piGauss n) = _
      calc
        _ = (∫ z, f z - t * (2 * parisiCorrection s β) ∂piGauss n) +
            ∫ _ : Fin n → ℝ, t * (β ^ 2 / 2) * (u - v) ^ 2 ∂piGauss n :=
          integral_add (hf.sub (integrable_const _)) (integrable_const _)
        _ = ((∫ z, f z ∂piGauss n) -
              ∫ _ : Fin n → ℝ, t * (2 * parisiCorrection s β) ∂piGauss n) +
            ∫ _ : Fin n → ℝ, t * (β ^ 2 / 2) * (u - v) ^ 2 ∂piGauss n := by
          rw [integral_sub hf (integrable_const _)]
        _ = _ := by
          simp [f]

end SpinGlass.Targets
