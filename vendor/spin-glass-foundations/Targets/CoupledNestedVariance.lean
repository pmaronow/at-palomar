module

/-
# An individual variance derivative through the actual paired cascade

The varying level uses the checked heat generator. All remaining outer levels
reuse the normalized parameter chain rule. The varying variance is positive;
all masses and all unchanged variances may vanish.
-/
public import Targets.CoupledCascadeVariance

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n p : ℕ}

/-- The explicit growth constant is monotone in the Gaussian variance. -/
theorem stepK_mono_variance {mass D v w : ℝ} (hm : 0 ≤ mass) (hD : 0 ≤ D)
    (hvw : v ≤ w) : stepK n mass v D ≤ stepK n mass w D := by
  unfold stepK
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hm)
    apply Real.log_le_log (integral_exp_pos (integrable_exp_l1 _))
    apply integral_mono (integrable_exp_l1 _) (integrable_exp_l1 _)
    intro z
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvw) hD) hm) (l1_nonneg z)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvw) hD) (l1Moment_nonneg n)

/-- A finite Gaussian field increment, with an arbitrary fixed direction in
each replica for each independent Gaussian coordinate. -/
noncomputable def coupledLinearStep (mass variance : ℝ)
    (A B : Fin p → Fin n → ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  parisiStepPi p mass variance
    (fun z => F (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)) 0

noncomputable def coupledLinearMean (mass variance : ℝ)
    (A B : Fin p → Fin n → ℝ) (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  pairedTiltMean mass variance
    (fun z => F (x + pairedFieldLinear A z) (y + pairedFieldLinear B z))
    (fun z => G (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)) 0

theorem coupled_linear_growth_bound {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {C D : ℝ} (hD : 0 ≤ D) (hb : ∀ x y, |F x y| ≤ C + D * (l1 x + l1 y))
    (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) (z : Fin p → ℝ) :
    |F (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)| ≤
      C + D * (l1 x + l1 y) + D * (∑ i, (l1 (A i) + l1 (B i))) * l1 z := by
  have hab : l1 (pairedFieldLinear A z) + l1 (pairedFieldLinear B z) ≤
      (∑ i, (l1 (A i) + l1 (B i))) * l1 z := by
    rw [Finset.sum_add_distrib]
    nlinarith [l1_pairedFieldLinear_le A z, l1_pairedFieldLinear_le B z]
  nlinarith [hb (x + pairedFieldLinear A z) (y + pairedFieldLinear B z),
    l1_add_le x (pairedFieldLinear A z), l1_add_le y (pairedFieldLinear B z)]

theorem CoupledGrowth.linear_input {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) :
    GuerraGrowth (fun z => F (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)) := by
  obtain ⟨C, D, hD, hb⟩ := hF.bound
  exact ⟨hF.measurable.comp
    ((measurable_const.add (measurable_pairedFieldLinear A)).prodMk
      (measurable_const.add (measurable_pairedFieldLinear B))),
    C + D * (l1 x + l1 y), D * ∑ i, (l1 (A i) + l1 (B i)),
    mul_nonneg hD (Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)),
    coupled_linear_growth_bound hD hb A B x y⟩

private theorem measurable_linear_shift (A B : Fin p → Fin n → ℝ) (variance : ℝ) :
    Measurable (fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin p → ℝ) =>
      (q.1.1 + pairedFieldLinear A (fun i => Real.sqrt variance * q.2 i),
        q.1.2 + pairedFieldLinear B (fun i => Real.sqrt variance * q.2 i))) := by
  exact (measurable_fst.fst.add ((measurable_pairedFieldLinear A).comp (by fun_prop))).prodMk
    (measurable_fst.snd.add ((measurable_pairedFieldLinear B).comp (by fun_prop)))

theorem measurable_coupledLinearStep
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F q.1 q.2))
    (A B : Fin p → Fin n → ℝ) (mass variance : ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => coupledLinearStep mass variance A B F q.1 q.2) := by
  have hf := hF.comp (measurable_linear_shift A B variance)
  simp only [coupledLinearStep, parisiStepPi, Pi.zero_apply, zero_add]
  split_ifs
  · exact hf.stronglyMeasurable.integral_prod_right'.measurable
  · exact (((hf.const_mul mass).exp.stronglyMeasurable.integral_prod_right').measurable.log).const_mul _

theorem measurable_coupledLinearMean
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F q.1 q.2))
    (hG : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => G q.1 q.2))
    (A B : Fin p → Fin n → ℝ) (mass variance : ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => coupledLinearMean mass variance A B F G q.1 q.2) := by
  have hf := hF.comp (measurable_linear_shift A B variance)
  have hg := hG.comp (measurable_linear_shift A B variance)
  simp only [coupledLinearMean, pairedTiltMean, tiltWeightPi_eq_exp_div,
    Pi.zero_apply, zero_add, ← mul_div_assoc, integral_div]
  exact (hg.mul (hf.const_mul mass).exp).stronglyMeasurable.integral_prod_right'.measurable.div
    ((hf.const_mul mass).exp.stronglyMeasurable.integral_prod_right'.measurable)

/-- The local Hessian-plus-square term of the actual constrained inner cascade. -/
noncomputable def constrainedSpatialHeat (U : EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d j : ℕ) (mass : ℝ) (A B x y : Fin n → ℝ) : ℝ :=
  constrainedPairCascadeSpatialSecond m v d j U u A B A B x y +
    mass * (constrainedPairCascadeSpatialFirst m v d j U u A B x y) ^ 2

theorem measurable_constrainedSpatialHeat (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass : ℝ) (A B : Fin n → ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => constrainedSpatialHeat U u m v d j mass A B q.1 q.2) :=
  (measurable_constrainedPairCascadeSpatialSecond U u m v hm hv d j A B A B).add
    (((measurable_constrainedPairCascadeSpatialFirst U u m v hm hv d j A B).pow_const 2).const_mul mass)

theorem constrainedSpatialHeat_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass : ℝ) (A B x y : Fin n → ℝ) :
    |constrainedSpatialHeat U u m v d j mass A B x y| ≤
      (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 A + l1 B) ^ 2 := by
  have hS := add_nonneg (l1_nonneg A) (l1_nonneg B)
  have hfirst := constrainedPairCascadeSpatialFirst_abs_le U u m v hm hv d j A B x y
  have hsquare : (constrainedPairCascadeSpatialFirst m v d j U u A B x y) ^ 2 ≤ (l1 A + l1 B) ^ 2 := by
    nlinarith [sq_abs (constrainedPairCascadeSpatialFirst m v d j U u A B x y), abs_nonneg
      (constrainedPairCascadeSpatialFirst m v d j U u A B x y)]
  have hs := mul_le_mul_of_nonneg_left hsquare (abs_nonneg mass)
  have hsecond := constrainedPairCascadeSpatialSecond_abs_le U u m v hm hv d j A B A B x y
  have H := abs_add_le (constrainedPairCascadeSpatialSecond m v d j U u A B A B x y)
    (mass * (constrainedPairCascadeSpatialFirst m v d j U u A B x y) ^ 2)
  rw [abs_mul, abs_of_nonneg (sq_nonneg (constrainedPairCascadeSpatialFirst m v d j U u A B x y))] at H
  change |_ + _| ≤ _
  nlinarith

noncomputable def constrainedLinearHeat (U : EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d j : ℕ) (mass variance : ℝ)
    (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (∑ i, coupledLinearMean mass variance A B
    (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j)
    (constrainedSpatialHeat U u m v d j mass (A i) (B i)) x y) / 2

/-- No outer-depth factor occurs in this bound. -/
noncomputable def constrainedLinearHeatBound (m : ℕ → ℝ) (j : ℕ) (mass : ℝ)
    (A B : Fin p → Fin n → ℝ) : ℝ :=
  (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) / 2 * ∑ i, (l1 (A i) + l1 (B i)) ^ 2

theorem measurable_constrainedLinearHeat (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => constrainedLinearHeat U u m v d j mass variance A B q.1 q.2) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ fun i _ => measurable_coupledLinearMean
    (constrainedPairFieldCascade_growth U u m v hm hv d j).measurable
    (measurable_constrainedSpatialHeat U u m v hm hv d j mass (A i) (B i)) A B mass variance

theorem constrainedLinearHeat_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) :
    |constrainedLinearHeat U u m v d j mass variance A B x y| ≤ constrainedLinearHeatBound m j mass A B := by
  have hb (i : Fin p) : |coupledLinearMean mass variance A B
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j)
      (constrainedSpatialHeat U u m v d j mass (A i) (B i)) x y| ≤
        (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 (A i) + l1 (B i)) ^ 2 :=
    pairedTiltMean_abs_le ((constrainedPairFieldCascade_growth U u m v hm hv d j).linear_input A B x y)
      ((measurable_constrainedSpatialHeat U u m v hm hv d j mass (A i) (B i)).comp
        ((measurable_const.add (measurable_pairedFieldLinear A)).prodMk
          (measurable_const.add (measurable_pairedFieldLinear B))))
      (fun z => constrainedSpatialHeat_abs_le U u m v hm hv d j mass (A i) (B i) _ _) 0
  unfold constrainedLinearHeat constrainedLinearHeatBound
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (∑ i, |coupledLinearMean mass variance A B
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j)
      (constrainedSpatialHeat U u m v d j mass (A i) (B i)) x y|) / 2 := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ i, (2 + 4 * ∑ l ∈ Finset.range j, |m l| + |mass|) * (l1 (A i) + l1 (B i)) ^ 2) / 2 := by
      gcongr with i; exact hb i
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- All local analytic hypotheses for the actual one-level variance derivative,
uniformly on a bounded positive variance interval. -/
theorem constrainedLinearStep_paramDeriv (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) {mass : ℝ} (hmass : 0 ≤ mass) (M : ℝ)
    (A B : Fin p → Fin n → ℝ) :
    CoupledParamDeriv
      (fun w => coupledLinearStep mass w A B (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j))
      (fun w => constrainedLinearHeat U u m v d j mass w A B)
      (Set.Ioo 0 M) (constrainedLinearHeatBound m j mass A B) := by
  have hg := constrainedPairFieldCascade_growth U u m v hm hv d j
  obtain ⟨C, D, hD, hb⟩ := hg.bound
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hDL : 0 ≤ D * L := mul_nonneg hD
    (Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _))
  refine ⟨?_, fun w _ => measurable_coupledLinearStep hg.measurable A B mass w,
    fun w _ => measurable_constrainedLinearHeat U u m v hm hv d j mass w A B,
    ⟨C + stepK p mass M (D * L), D, hD, ?_⟩,
    fun w _ x y => constrainedLinearHeat_abs_le U u m v hm hv d j mass w A B x y⟩
  · intro w hw x y
    exact hasDerivAt_constrainedPairField_linear_variance U u m v hm hv d j A B x y mass hw.1
  · intro w hw x y
    have H := parisiStepPi_abs_le (C := C + D * (l1 x + l1 y)) hmass hw.1.le hDL
      (coupled_linear_growth_bound hD hb A B x y) (hg.linear_input A B x y).measurable (0 : Fin p → ℝ)
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at H
    have HK := stepK_mono_variance (n := p) hmass hDL hw.2.le
    change |parisiStepPi p mass w _ 0| ≤ _
    nlinarith

/-- Changing an unvisited variance leaves the actual inner cascade unchanged. -/
theorem coupledFieldCascade_update_variance_prefix
    (m v : ℕ → ℝ) (d ℓ j : ℕ) (hj : j ≤ ℓ) (w : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n m (Function.update v ℓ w) d F j = coupledFieldCascade n m v d F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [coupledFieldCascade, Function.update_of_ne (show j ≠ ℓ by omega), ih (by omega)]

theorem coupledFieldCascade_update_variance_level
    (m v : ℕ → ℝ) (d ℓ : ℕ) (w : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n m (Function.update v ℓ w) d F (ℓ + 1) =
      if ℓ < d then independentStepPi n (m ℓ) w (coupledFieldCascade n m v d F ℓ)
      else sharedStepPi n (2 * m ℓ) w (coupledFieldCascade n m v d F ℓ) := by
  simp only [coupledFieldCascade, Function.update_self,
    coupledFieldCascade_update_variance_prefix m v d ℓ ℓ le_rfl w F]

/-- The seed of the derivative at the actual varying level. -/
noncomputable def constrainedLevelHeat (U : EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d ℓ : ℕ) (w : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  if ℓ < d then constrainedLinearHeat U u m v d ℓ (m ℓ) w
    (independentLeftDirection n) (independentRightDirection n)
  else constrainedLinearHeat U u m v d ℓ (m ℓ) w
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)

noncomputable def constrainedLevelHeatBound (n : ℕ) (m : ℕ → ℝ) (d ℓ : ℕ) : ℝ :=
  if ℓ < d then constrainedLinearHeatBound m ℓ (m ℓ)
    (independentLeftDirection n) (independentRightDirection n)
  else constrainedLinearHeatBound m ℓ (m ℓ)
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)

/-- Propagation of the seed through the actual unchanged outer levels. All
weights use the same variance-modified actual cascade as the pressure. -/
noncomputable def constrainedLevelVarianceD (U : EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d ℓ : ℕ) : ℕ → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => constrainedLevelHeat U u m v d ℓ
  | j + 1 => fun w =>
      if ℓ + 1 + j < d then
        pairedIndependentMean (m (ℓ + 1 + j)) (v (ℓ + 1 + j))
          (coupledFieldCascade n m (Function.update v ℓ w) d (constrainedPairFieldBase n U u) (ℓ + 1 + j))
          (constrainedLevelVarianceD U u m v d ℓ j w)
      else
        pairedSharedMean (m (ℓ + 1 + j)) (v (ℓ + 1 + j))
          (coupledFieldCascade n m (Function.update v ℓ w) d (constrainedPairFieldBase n U u) (ℓ + 1 + j))
          (constrainedLevelVarianceD U u m v d ℓ j w)

theorem coupledLinearStep_independent (mass variance : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep mass variance (independentLeftDirection n) (independentRightDirection n) F =
      independentStepPi n mass variance F := by
  funext x y
  simp only [coupledLinearStep, pairedFieldLinear_independent_left,
    pairedFieldLinear_independent_right, independentStepPi_eq_packed]

theorem coupledLinearStep_shared (mass variance : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep mass variance (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) F =
      sharedStepPi n (2 * mass) variance F := by
  funext x y
  simp only [coupledLinearStep, pairedFieldLinear_coordinates, sharedStepPi,
    show 2 * mass / 2 = mass by ring]

theorem constrainedLevelVarianceD_base_props (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ : ℕ) (M : ℝ) :
    CoupledParamDeriv
      (fun w => coupledFieldCascade n m (Function.update v ℓ w) d (constrainedPairFieldBase n U u) (ℓ + 1))
      (constrainedLevelVarianceD U u m v d ℓ 0) (Set.Ioo 0 M) (constrainedLevelHeatBound n m d ℓ) := by
  rw [show constrainedLevelVarianceD U u m v d ℓ 0 = fun w => constrainedLevelHeat U u m v d ℓ w from rfl]
  simp only [coupledFieldCascade_update_variance_level, constrainedLevelHeat, constrainedLevelHeatBound]
  by_cases hℓ : ℓ < d
  · simp only [if_pos hℓ]
    have H := constrainedLinearStep_paramDeriv U u m v hm hv d ℓ (hm ℓ) M
      (independentLeftDirection n) (independentRightDirection n)
    simpa only [coupledLinearStep_independent] using H
  · simp only [if_neg hℓ]
    have H := constrainedLinearStep_paramDeriv U u m v hm hv d ℓ (hm ℓ) M
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
    simpa only [coupledLinearStep_shared] using H

/-- Actual one-level variance differentiation through every remaining outer
level, with a field-uniform bound independent of the number of those levels. -/
theorem constrainedLevelVarianceD_props (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (M : ℝ) :
    CoupledParamDeriv
      (fun w => coupledFieldCascade n m (Function.update v ℓ w) d (constrainedPairFieldBase n U u) (ℓ + 1 + j))
      (constrainedLevelVarianceD U u m v d ℓ j) (Set.Ioo 0 M) (constrainedLevelHeatBound n m d ℓ) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using constrainedLevelVarianceD_base_props U u m v hm hv d ℓ M
  | succ j ih =>
    rw [show ℓ + 1 + (j + 1) = (ℓ + 1 + j) + 1 by omega]
    simp only [coupledFieldCascade, constrainedLevelVarianceD,
      Function.update_of_ne (show ℓ + 1 + j ≠ ℓ by omega)]
    by_cases h : ℓ + 1 + j < d
    · simpa only [if_pos h] using ih.independentStep isOpen_Ioo (hm (ℓ + 1 + j)) (hv (ℓ + 1 + j))
    · simpa only [if_neg h] using ih.sharedStep isOpen_Ioo (hm (ℓ + 1 + j)) (hv (ℓ + 1 + j))

/-- A derivative of the original full cascade with one original variance
changed, not a derivative assumption on an auxiliary pressure. -/
theorem hasDerivAt_constrainedFieldCascade_variance (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt
      (fun z => coupledFieldCascade n m (Function.update v ℓ z) d (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y)
      (constrainedLevelVarianceD U u m v d ℓ j w x y) w :=
  (constrainedLevelVarianceD_props U u m v hm hv d ℓ j (w + 1)).deriv w ⟨hw, by linarith⟩ x y

theorem constrainedFieldCascade_variance_deriv_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    |deriv (fun z => coupledFieldCascade n m (Function.update v ℓ z) d
      (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y) w| ≤ constrainedLevelHeatBound n m d ℓ := by
  rw [(hasDerivAt_constrainedFieldCascade_variance U u m v hm hv d ℓ j x y hw).deriv]
  exact (constrainedLevelVarianceD_props U u m v hm hv d ℓ j (w + 1)).bound w ⟨hw, by linarith⟩ x y

theorem measurable_constrainedLevelVarianceD (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) {w : ℝ} (hw : 0 < w) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => constrainedLevelVarianceD U u m v d ℓ j w q.1 q.2) :=
  (constrainedLevelVarianceD_props U u m v hm hv d ℓ j (w + 1)).measurable_deriv w ⟨hw, by linarith⟩

/-- Independent directions have norm one; shared directions have norm two.
The bound is linear in the number of sites and has no outer-depth factor. -/
theorem constrainedLevelHeatBound_eq (n : ℕ) (m : ℕ → ℝ) (d ℓ : ℕ) :
    constrainedLevelHeatBound n m d ℓ =
      (if ℓ < d then 1 else 2) * (n : ℝ) *
        (2 + 4 * ∑ l ∈ Finset.range ℓ, |m l| + |m ℓ|) := by
  classical
  have hs (i : Fin n) : l1 (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
    simp [l1, Pi.single_apply, apply_ite abs]
  have hz : l1 (0 : Fin n → ℝ) = 0 := by simp [l1]
  unfold constrainedLevelHeatBound constrainedLinearHeatBound
  split_ifs
  · rw [Fin.sum_univ_add]
    simp only [independentLeftDirection_castAdd, independentRightDirection_castAdd,
      independentLeftDirection_natAdd, independentRightDirection_natAdd, hs, hz,
      add_zero, zero_add, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring
  · simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem constrainedFieldCascade_variance_deriv_abs_le_explicit (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    |deriv (fun z => coupledFieldCascade n m (Function.update v ℓ z) d
      (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y) w| ≤
      (if ℓ < d then 1 else 2) * (n : ℝ) *
        (2 + 4 * ∑ l ∈ Finset.range ℓ, |m l| + |m ℓ|) := by
  simpa only [constrainedLevelHeatBound_eq] using
    constrainedFieldCascade_variance_deriv_abs_le U u m v hm hv d ℓ j x y hw

/-- Unvisited levels contribute zero, without any positivity condition. -/
theorem hasDerivAt_constrainedFieldCascade_variance_before (U : EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d ℓ j : ℕ) (hj : j ≤ ℓ) (x y : Fin n → ℝ) (w : ℝ) :
    HasDerivAt (fun z => coupledFieldCascade n m (Function.update v ℓ z) d
      (constrainedPairFieldBase n U u) j x y) 0 w := by
  simp only [coupledFieldCascade_update_variance_prefix m v d ℓ j hj]
  exact hasDerivAt_const w _

end SpinGlass.Targets
