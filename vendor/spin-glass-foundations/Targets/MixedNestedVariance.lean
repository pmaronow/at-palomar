module

public import Targets.MixedCascadeVariance
public import Targets.CoupledNestedVariance

@[expose] public section

/-!
# Actual individual-variance differentiation through mixed outer levels

The Gaussian heat theorem supplies the varying level. The already checked mixed
parameter chain rule propagates it through every remaining unchanged level.
Only the varying variance must be positive; all masses and other variances may
vanish, and independent/shared/opposite levels may occur in any order.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n p : ℕ}

noncomputable def mixedSpatialHeat (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ)
    (mass : ℝ) (A B x y : Fin n → ℝ) : ℝ :=
  mixedCascadeSpatialSecond mode m v j U u A B A B x y +
    mass * (mixedCascadeSpatialFirst mode m v j U u A B x y) ^ 2

theorem measurable_mixedSpatialHeat (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (mass : ℝ) (A B : Fin n → ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => mixedSpatialHeat U u mode m v j mass A B q.1 q.2) :=
  (measurable_mixedCascadeSpatialSecond U u mode m v hm hv j A B A B).add
    (((measurable_mixedCascadeSpatialFirst U u mode m v hm hv j A B).pow_const 2).const_mul mass)

theorem mixedSpatialHeat_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (mass : ℝ) (A B x y : Fin n → ℝ) :
    |mixedSpatialHeat U u mode m v j mass A B x y| ≤
      (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 A + l1 B) ^ 2 := by
  have hS := add_nonneg (l1_nonneg A) (l1_nonneg B)
  have hfirst := mixedConstrainedCascadeD_field_abs_le U u mode m v hm hv j A B x y
  change |mixedCascadeSpatialFirst mode m v j U u A B x y| ≤ _ at hfirst
  have hsquare : (mixedCascadeSpatialFirst mode m v j U u A B x y) ^ 2 ≤ (l1 A + l1 B) ^ 2 := by
    nlinarith [sq_abs (mixedCascadeSpatialFirst mode m v j U u A B x y), abs_nonneg
      (mixedCascadeSpatialFirst mode m v j U u A B x y)]
  have hs := mul_le_mul_of_nonneg_left hsquare (abs_nonneg mass)
  have hsecond := mixedConstrainedCascadeDD_field_abs_le U u mode m v hm hv j A B A B x y
  change |mixedCascadeSpatialSecond mode m v j U u A B A B x y| ≤ _ at hsecond
  have H := abs_add_le (mixedCascadeSpatialSecond mode m v j U u A B A B x y)
    (mass * (mixedCascadeSpatialFirst mode m v j U u A B x y) ^ 2)
  rw [abs_mul, abs_of_nonneg (sq_nonneg (mixedCascadeSpatialFirst mode m v j U u A B x y))] at H
  change |_ + _| ≤ _
  nlinarith

noncomputable def mixedLinearHeat (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ)
    (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (∑ i, coupledLinearMean mass variance A B
    (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j)
    (mixedSpatialHeat U u mode m v j mass (A i) (B i)) x y) / 2

theorem measurable_mixedLinearHeat (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => mixedLinearHeat U u mode m v j mass variance A B q.1 q.2) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ fun i _ => measurable_coupledLinearMean
    (mixedConstrainedCascade_growth U u mode m v hm hv j).measurable
    (measurable_mixedSpatialHeat U u mode m v hm hv j mass (A i) (B i)) A B mass variance

theorem mixedLinearHeat_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) :
    |mixedLinearHeat U u mode m v j mass variance A B x y| ≤ constrainedLinearHeatBound m j mass A B := by
  have hb (i : Fin p) : |coupledLinearMean mass variance A B
      (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j)
      (mixedSpatialHeat U u mode m v j mass (A i) (B i)) x y| ≤
        (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 (A i) + l1 (B i)) ^ 2 :=
    pairedTiltMean_abs_le ((mixedConstrainedCascade_growth U u mode m v hm hv j).linear_input A B x y)
      ((measurable_mixedSpatialHeat U u mode m v hm hv j mass (A i) (B i)).comp
        ((measurable_const.add (measurable_pairedFieldLinear A)).prodMk
          (measurable_const.add (measurable_pairedFieldLinear B))))
      (fun z => mixedSpatialHeat_abs_le U u mode m v hm hv j mass (A i) (B i) _ _) 0
  unfold mixedLinearHeat constrainedLinearHeatBound
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (∑ i, |coupledLinearMean mass variance A B
      (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j)
      (mixedSpatialHeat U u mode m v j mass (A i) (B i)) x y|) / 2 := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ i, (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 (A i) + l1 (B i)) ^ 2) / 2 := by
      gcongr with i; exact hb i
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A genuine variance-parameter package on every bounded positive interval. -/
theorem mixedLinearStep_paramDeriv (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    {mass : ℝ} (hmass : 0 ≤ mass) (M : ℝ) (A B : Fin p → Fin n → ℝ) :
    CoupledParamDeriv
      (fun w => coupledLinearStep mass w A B (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j))
      (fun w => mixedLinearHeat U u mode m v j mass w A B)
      (Set.Ioo 0 M) (constrainedLinearHeatBound m j mass A B) := by
  have hg := mixedConstrainedCascade_growth U u mode m v hm hv j
  obtain ⟨C, D, hD, hb⟩ := hg.bound
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hDL : 0 ≤ D * L := mul_nonneg hD
    (Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _))
  refine ⟨?_, fun w _ => measurable_coupledLinearStep hg.measurable A B mass w,
    fun w _ => measurable_mixedLinearHeat U u mode m v hm hv j mass w A B,
    ⟨C + stepK p mass M (D * L), D, hD, ?_⟩,
    fun w _ x y => mixedLinearHeat_abs_le U u mode m v hm hv j mass w A B x y⟩
  · intro w hw x y
    exact hasDerivAt_mixedConstrainedField_linear_variance U u mode m v hm hv j A B x y mass hw.1
  · intro w hw x y
    have H := parisiStepPi_abs_le (C := C + D * (l1 x + l1 y)) hmass hw.1.le hDL
      (coupled_linear_growth_bound hD hb A B x y) (hg.linear_input A B x y).measurable (0 : Fin p → ℝ)
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at H
    have HK := stepK_mono_variance (n := p) hmass hDL hw.2.le
    change |parisiStepPi p mass w _ 0| ≤ _
    nlinarith

theorem coupledLinearStep_opposite (mass variance : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep mass variance (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -Pi.single i 1) F = mixedVectorStep n .opposite mass variance F := by
  have hn (z : Fin n → ℝ) : pairedFieldLinear (fun i : Fin n => -Pi.single i 1) z = -z := by
    rw [pairedFieldLinear]
    simp only [smul_neg, Finset.sum_neg_distrib]
    exact congrArg Neg.neg (pairedFieldLinear_coordinates z)
  funext x y
  simp only [coupledLinearStep, pairedFieldLinear_coordinates, hn]
  simp only [mixedVectorStep,
    AT.gtVectorStep, parisiStepPi, Pi.zero_apply, zero_add, Pi.add_def, Pi.neg_def, neg_mul]
  rfl

theorem mixedVectorCascade_update_variance_prefix
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (ℓ j : ℕ)
    (hj : j ≤ ℓ) (w : ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorCascade n mode m (Function.update v ℓ w) F j = mixedVectorCascade n mode m v F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mixedVectorCascade, Function.update_of_ne (show j ≠ ℓ by omega), ih (by omega)]

theorem mixedVectorCascade_update_variance_level
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (ℓ : ℕ)
    (w : ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorCascade n mode m (Function.update v ℓ w) F (ℓ + 1) =
      mixedVectorStep n (mode ℓ) (m ℓ) w (mixedVectorCascade n mode m v F ℓ) := by
  simp only [mixedVectorCascade, Function.update_self,
    mixedVectorCascade_update_variance_prefix mode m v ℓ ℓ le_rfl w F]
  rfl

noncomputable def mixedLevelHeat (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (ℓ : ℕ)
    (w : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  match mode ℓ with
  | .independent => mixedLinearHeat U u mode m v ℓ (m ℓ) w
      (independentLeftDirection n) (independentRightDirection n)
  | .shared => mixedLinearHeat U u mode m v ℓ (m ℓ) w
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
  | .opposite => mixedLinearHeat U u mode m v ℓ (m ℓ) w
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -Pi.single i 1)

noncomputable def mixedLevelHeatBound (n : ℕ)
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  match mode ℓ with
  | .independent => constrainedLinearHeatBound m ℓ (m ℓ)
      (independentLeftDirection n) (independentRightDirection n)
  | .shared => constrainedLinearHeatBound m ℓ (m ℓ)
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
  | .opposite => constrainedLinearHeatBound m ℓ (m ℓ)
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -Pi.single i 1)

noncomputable def mixedLevelVarianceD (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (ℓ : ℕ) :
    ℕ → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => mixedLevelHeat U u mode m v ℓ
  | j + 1 => fun w => mixedVectorMean n (mode (ℓ + 1 + j)) (m (ℓ + 1 + j)) (v (ℓ + 1 + j))
      (mixedVectorCascade n mode m (Function.update v ℓ w) (constrainedPairFieldBase n U u) (ℓ + 1 + j))
      (mixedLevelVarianceD U u mode m v ℓ j w)

theorem mixedLevelVarianceD_base_props (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (ℓ : ℕ) (M : ℝ) :
    CoupledParamDeriv
      (fun w => mixedVectorCascade n mode m (Function.update v ℓ w) (constrainedPairFieldBase n U u) (ℓ + 1))
      (mixedLevelVarianceD U u mode m v ℓ 0) (Set.Ioo 0 M) (mixedLevelHeatBound n mode m ℓ) := by
  change CoupledParamDeriv _ (fun w => mixedLevelHeat U u mode m v ℓ w) _ _
  simp only [mixedVectorCascade_update_variance_level, mixedLevelHeat, mixedLevelHeatBound]
  cases he : mode ℓ with
  | independent =>
    have H := mixedLinearStep_paramDeriv U u mode m v hm hv ℓ (hm ℓ) M
      (independentLeftDirection n) (independentRightDirection n)
    apply H.congr_eq_on isOpen_Ioo
    · intro w _
      rw [coupledLinearStep_independent]
      exact mixedVectorStep_independent_eq (m ℓ) w (mixedConstrainedCascade_growth U u mode m v hm hv ℓ)
    · intro _ _; rfl
  | shared =>
    simpa only [coupledLinearStep_shared, mixedVectorStep_shared_eq] using
      mixedLinearStep_paramDeriv U u mode m v hm hv ℓ (hm ℓ) M
        (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
  | opposite =>
    simpa only [coupledLinearStep_opposite] using
      mixedLinearStep_paramDeriv U u mode m v hm hv ℓ (hm ℓ) M
        (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -Pi.single i 1)

/-- The true single-variance derivative package through all unchanged outer
mixed levels, with no added outer-depth loss in its uniform bound. -/
theorem mixedLevelVarianceD_props (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (ℓ j : ℕ) (M : ℝ) :
    CoupledParamDeriv
      (fun w => mixedVectorCascade n mode m (Function.update v ℓ w) (constrainedPairFieldBase n U u) (ℓ + 1 + j))
      (mixedLevelVarianceD U u mode m v ℓ j) (Set.Ioo 0 M) (mixedLevelHeatBound n mode m ℓ) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using mixedLevelVarianceD_base_props U u mode m v hm hv ℓ M
  | succ j ih =>
    rw [show ℓ + 1 + (j + 1) = (ℓ + 1 + j) + 1 by omega]
    simp only [mixedVectorCascade, mixedLevelVarianceD,
      Function.update_of_ne (show ℓ + 1 + j ≠ ℓ by omega)]
    exact ih.mixedStep isOpen_Ioo (mode (ℓ + 1 + j)) (hm (ℓ + 1 + j)) (hv (ℓ + 1 + j))

theorem hasDerivAt_mixedConstrainedCascade_variance (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (ℓ j : ℕ) (x y : Fin n → ℝ)
    {w : ℝ} (hw : 0 < w) :
    HasDerivAt
      (fun z => mixedVectorCascade n mode m (Function.update v ℓ z) (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y)
      (mixedLevelVarianceD U u mode m v ℓ j w x y) w :=
  (mixedLevelVarianceD_props U u mode m v hm hv ℓ j (w + 1)).deriv w ⟨hw, by linarith⟩ x y

theorem mixedConstrainedCascade_variance_deriv_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (ℓ j : ℕ) (x y : Fin n → ℝ)
    {w : ℝ} (hw : 0 < w) :
    |deriv (fun z => mixedVectorCascade n mode m (Function.update v ℓ z)
      (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y) w| ≤ mixedLevelHeatBound n mode m ℓ := by
  rw [(hasDerivAt_mixedConstrainedCascade_variance U u mode m v hm hv ℓ j x y hw).deriv]
  exact (mixedLevelVarianceD_props U u mode m v hm hv ℓ j (w + 1)).bound w ⟨hw, by linarith⟩ x y

end SpinGlass.Targets
