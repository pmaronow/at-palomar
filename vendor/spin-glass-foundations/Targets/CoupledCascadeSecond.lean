module

/-
# The full mixed disorder Hessian of a coupled cascade

Each actual tilted average differentiates to a tilted derivative plus the
mass covariance. The one-field rule and all first-derivative regularity are
reused from `CoupledCascadeDeriv`; independent levels consist of two such
steps, while shared levels consist of one. Variances remain fixed here.
-/
public import Targets.CoupledCascadeDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.Measurable

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- Mixed derivative of a second-field tilted observable. -/
noncomputable def pairedSecondCovariance (m v : ℝ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedSecondMean m v A (fun x y => GW x y + m * G x y * AW x y) x y -
    m * pairedSecondMean m v A G x y * pairedSecondMean m v A AW x y

/-- The tilted covariance rule preserves all local analytic hypotheses,
including a field-independent derivative bound. -/
theorem CoupledParamDeriv.tiltSecond
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH m v : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s) :
    CoupledParamDeriv (fun a => pairedSecondMean m v (A a) (G a))
      (fun a => pairedSecondCovariance m v (A a) (AW a) (G a) (GW a))
      s (BH + 2 * |m| * BV * BW) ∧
    (∀ a ∈ s, ∀ x y, |pairedSecondMean m v (A a) (G a) x y| ≤ BV) := by
  have hb : ∀ a ∈ s, ∀ x y, |pairedSecondMean m v (A a) (G a) x y| ≤ BV := by
    intro a ha x y
    exact pairedTiltMean_abs_le ((hA.growth_at ha).section_right x)
      ((hG.measurable a ha).comp (measurable_const.prodMk measurable_id)) (hGB a ha x) y
  refine ⟨⟨?_, ?_, ?_, ⟨BV, 0, le_rfl, ?_⟩, ?_⟩, hb⟩
  · intro a ha x y
    exact hasDerivAt_pairedSecondMean hA hG hGB (hs.mem_nhds ha) x y
  · intro a ha
    exact measurable_pairedSecondMean (hA.measurable a ha) (hG.measurable a ha) m v
  · intro a ha
    exact (measurable_pairedSecondMean (hA.measurable a ha)
      ((hG.measurable_deriv a ha).add
        (((hG.measurable a ha).const_mul m).mul (hA.measurable_deriv a ha))) m v).sub
      (((measurable_pairedSecondMean (hA.measurable a ha) (hG.measurable a ha) m v).const_mul m).mul
        (measurable_pairedSecondMean (hA.measurable a ha) (hA.measurable_deriv a ha) m v))
  · intro a ha x y
    simpa only [zero_mul, add_zero] using hb a ha x y
  · intro a ha x y
    have hBV : 0 ≤ BV := (abs_nonneg _).trans (hGB a ha x y)
    have hobs : ∀ x y, |GW a x y + m * G a x y * AW a x y| ≤ BH + |m| * BV * BW := by
      intro x y
      refine (abs_add_le _ _).trans (add_le_add (hG.bound a ha x y) ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hGB a ha x y) (abs_nonneg m))
        (hA.bound a ha x y) (abs_nonneg _) (mul_nonneg (abs_nonneg m) hBV)
    have hi := pairedTiltMean_abs_le (m := m) (v := v) ((hA.growth_at ha).section_right x)
      (((hG.measurable_deriv a ha).add
        (((hG.measurable a ha).const_mul m).mul (hA.measurable_deriv a ha))).comp
          (measurable_const.prodMk measurable_id)) (hobs x) y
    have hw := pairedTiltMean_abs_le (m := m) (v := v) ((hA.growth_at ha).section_right x)
      ((hA.measurable_deriv a ha).comp (measurable_const.prodMk measurable_id)) (hA.bound a ha x) y
    have hp : |m * pairedSecondMean m v (A a) (G a) x y *
        pairedSecondMean m v (A a) (AW a) x y| ≤ |m| * BV * BW := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb a ha x y) (abs_nonneg m))
        hw (abs_nonneg _) (mul_nonneg (abs_nonneg m) hBV)
    have ht := abs_sub_le
      (pairedSecondMean m v (A a) (fun x y => GW a x y + m * G a x y * AW a x y) x y) 0
      (m * pairedSecondMean m v (A a) (G a) x y * pairedSecondMean m v (A a) (AW a) x y)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    change |pairedSecondMean m v (A a) (fun x y => GW a x y + m * G a x y * AW a x y) x y -
      m * pairedSecondMean m v (A a) (G a) x y * pairedSecondMean m v (A a) (AW a) x y| ≤ _
    change |pairedSecondMean m v (A a) (fun x y => GW a x y + m * G a x y * AW a x y) x y| ≤ _ at hi
    nlinarith

/-- Shared-level mixed derivative, with its actual log-Laplace mass. -/
noncomputable def pairedSharedCovariance (m v : ℝ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedSharedMean m v A (fun x y => GW x y + m * G x y * AW x y) x y -
    m * pairedSharedMean m v A G x y * pairedSharedMean m v A AW x y

theorem CoupledParamDeriv.tiltShared
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH m v : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s) :
    CoupledParamDeriv (fun a => pairedSharedMean m v (A a) (G a))
      (fun a => pairedSharedCovariance m v (A a) (AW a) (G a) (GW a))
      s (BH + 2 * |m| * BV * BW) ∧
    (∀ a ∈ s, ∀ x y, |pairedSharedMean m v (A a) (G a) x y| ≤ BV) := by
  have HA := hA.comp_fields (fun p => p.1 + p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_add_le p.1 p.2, l1_nonneg p.1])
  have HG := hG.comp_fields (fun p => p.1 + p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_add_le p.1 p.2, l1_nonneg p.1])
  have H := HA.tiltSecond HG (fun a ha x y => hGB a ha _ _) hs (m := m) (v := v)
  have H' := H.1.comp_fields (fun p => p.1 - p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_sub_le p.1 p.2, l1_nonneg p.1])
  exact ⟨H', fun a ha x y => H.2 a ha (x - y) y⟩

/-- Independent levels differentiate the inner tilt and then the outer tilt.
This explicit two-stage expression includes both mass covariance terms. -/
noncomputable def pairedIndependentCovariance (m v : ℝ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedSecondCovariance m v (fun y x => parisiStepPi n m v (A x) y)
    (fun y x => pairedSecondMean m v A AW x y)
    (fun y x => pairedSecondMean m v A G x y)
    (fun y x => pairedSecondCovariance m v A AW G GW x y) y x

theorem CoupledParamDeriv.tiltIndependent
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH m v : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s)
    (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a => pairedIndependentMean m v (A a) (G a))
      (fun a => pairedIndependentCovariance m v (A a) (AW a) (G a) (GW a))
      s (BH + 4 * |m| * BV * BW) ∧
    (∀ a ∈ s, ∀ x y, |pairedIndependentMean m v (A a) (G a) x y| ≤ BV) := by
  have H := hA.tiltSecond hG hGB hs (m := m) (v := v)
  have H' := (hA.secondStep hs hm hv).swap.tiltSecond H.1.swap
    (fun a ha x y => H.2 a ha y x) hs (m := m) (v := v)
  have he : BH + 2 * |m| * BV * BW + 2 * |m| * BV * BW = BH + 4 * |m| * BV * BW := by ring
  rw [he] at H'
  exact ⟨H'.1.swap, fun a ha x y => H'.2 a ha y x⟩

/-- An explicit finite-depth bound: an independent level contributes twice the
single-field covariance bound, and a shared level contributes it once. -/
noncomputable def coupledHessianBound (m : ℕ → ℝ) (d : ℕ) (BV BW BH : ℝ) : ℕ → ℝ
  | 0 => BH
  | j + 1 => coupledHessianBound m d BV BW BH j + (if j < d then 4 else 2) * |m j| * BV * BW

/-- Recursively tilted mixed derivative. `AW` is the potential's derivative in
the varying direction, `G` the other first direction, and `GW` the base Hessian. -/
noncomputable def coupledFieldCascadeDD (m v : ℕ → ℝ) (d : ℕ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => GW
  | j + 1 => if j < d then
      pairedIndependentCovariance (m j) (v j) (coupledFieldCascade n m v d A j)
        (coupledFieldCascadeD m v d A AW j) (coupledFieldCascadeD m v d A G j)
        (coupledFieldCascadeDD m v d A AW G GW j)
    else pairedSharedCovariance (m j) (v j) (coupledFieldCascade n m v d A j)
      (coupledFieldCascadeD m v d A AW j) (coupledFieldCascadeD m v d A G j)
      (coupledFieldCascadeDD m v d A AW G GW j)

/-- Full induction for actual nested tilted observables. Both the derivative
formula and its integrability-enabling uniform bound are propagated, not assumed. -/
theorem CoupledParamDeriv.fieldCascadeSecond
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s)
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    CoupledParamDeriv (fun a => coupledFieldCascadeD m v d (A a) (G a) j)
      (fun a => coupledFieldCascadeDD m v d (A a) (AW a) (G a) (GW a) j)
      s (coupledHessianBound m d BV BW BH j) ∧
    (∀ a ∈ s, ∀ x y, |coupledFieldCascadeD m v d (A a) (G a) j x y| ≤ BV) := by
  induction j with
  | zero => exact ⟨hG, hGB⟩
  | succ j ih =>
    have H := hA.fieldCascade hs m v hm hv d j
    simp only [coupledFieldCascadeD, coupledFieldCascadeDD, coupledHessianBound]
    split_ifs with hj
    · exact H.tiltIndependent ih.1 ih.2 hs (hm j) (hv j)
    · exact H.tiltShared ih.1 ih.2 hs

theorem coupledHessianBound_eq_sum (m : ℕ → ℝ) (d j : ℕ) (BV BW BH : ℝ) :
    coupledHessianBound m d BV BW BH j =
      BH + (∑ l ∈ Finset.range j, (if l < d then 4 else 2) * |m l|) * BV * BW := by
  induction j with
  | zero => simp [coupledHessianBound]
  | succ j ih => rw [coupledHessianBound, ih, Finset.sum_range_succ]; ring

/-- The recursively tilted first disorder direction has the recursively tilted
mixed Hessian as its actual derivative at every depth. -/
theorem hasDerivAt_constrainedPairFieldCascadeD (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => coupledFieldCascadeD m v d (constrainedPairFieldBase n (U + b • W) u)
      (constrainedPairDirection (U + b • W) V u) j x y)
      (coupledFieldCascadeDD m v d (constrainedPairFieldBase n (U + a • W) u)
        (constrainedPairDirection (U + a • W) W u) (constrainedPairDirection (U + a • W) V u)
        (constrainedPairSecond n u (U + a • W) V W) j x y) a := by
  exact ((constrainedPairFieldBase_paramDeriv U W u a).fieldCascadeSecond
    (constrainedPairDirection_paramDeriv U V W u a)
    (fun b _ x y => constrainedPairDirection_abs_le (U + b • W) V u x y)
    isOpen_Ioo m v hm hv d j).1.deriv a ⟨by linarith, by linarith⟩ x y

/-- Actual mixed disorder derivative of the actual interacting cascade at any
depth and split. All nonempty-state and zero-mass cases are explicit. -/
theorem hasDerivAt_constrainedPairFieldCascade_second (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => coupledFieldCascade n m v d
        (constrainedPairFieldBase n (U + a • W + b • V) u) j x y) 0)
      (coupledFieldCascadeDD m v d (constrainedPairFieldBase n U u)
        (constrainedPairDirection U W u) (constrainedPairDirection U V u)
        (constrainedPairSecond n u U V W) j x y) 0 := by
  have he (a : ℝ) := (hasDerivAt_constrainedPairFieldCascade (U + a • W) V u m v hm hv d j x y 0).deriv
  simp only [zero_smul, add_zero] at he
  simp only [he]
  simpa only [zero_smul, add_zero] using
    hasDerivAt_constrainedPairFieldCascadeD U V W u m v hm hv d j x y 0

/-- The mixed Hessian, defined by actual derivatives rather than its recursive
candidate expression. -/
noncomputable def constrainedPairFieldCascadeSecond (m v : ℕ → ℝ) (d j : ℕ)
    (U V W : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) : ℝ :=
  deriv (fun a : ℝ => deriv (fun b : ℝ => coupledFieldCascade n m v d
    (constrainedPairFieldBase n (U + a • W + b • V) u) j x y) 0) 0

theorem constrainedPairFieldCascadeSecond_eq (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    constrainedPairFieldCascadeSecond m v d j U V W u x y =
      coupledFieldCascadeDD m v d (constrainedPairFieldBase n U u)
        (constrainedPairDirection U W u) (constrainedPairDirection U V u)
        (constrainedPairSecond n u U V W) j x y :=
  (hasDerivAt_constrainedPairFieldCascade_second U V W u m v hm hv d j x y).deriv

/-- A bound uniform in disorder and fields, sufficient to dominate every fixed
finite-depth mixed derivative in the subsequent Gaussian integration. -/
theorem constrainedPairFieldCascadeSecond_abs_le (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    |constrainedPairFieldCascadeSecond m v d j U V W u x y| ≤
      (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n W := by
  have H := ((constrainedPairFieldBase_paramDeriv U W u 0).fieldCascadeSecond
    (constrainedPairDirection_paramDeriv U V W u 0)
    (fun b _ x y => constrainedPairDirection_abs_le (U + b • W) V u x y)
    isOpen_Ioo m v hm hv d j).1.bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simp only [zero_smul, add_zero] at H
  rw [constrainedPairFieldCascadeSecond_eq U V W u m v hm hv d j x y]
  refine H.trans ?_
  rw [coupledHessianBound_eq_sum]
  have hsum : (∑ l ∈ Finset.range j, (if l < d then 4 else 2) * |m l|) ≤
      4 * ∑ l ∈ Finset.range j, |m l| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right
      (by split_ifs <;> norm_num) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (uAbs_nonneg n V)) (uAbs_nonneg n W)]

/-- Field measurability of the actual mixed Hessian is inherited through every
Gaussian level, including independent interacting levels. -/
theorem measurable_constrainedPairFieldCascadeSecond (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      constrainedPairFieldCascadeSecond m v d j U V W u p.1 p.2) := by
  have H := ((constrainedPairFieldBase_paramDeriv U W u 0).fieldCascadeSecond
    (constrainedPairDirection_paramDeriv U V W u 0)
    (fun b _ x y => constrainedPairDirection_abs_le (U + b • W) V u x y)
    isOpen_Ioo m v hm hv d j).1.measurable_deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [constrainedPairFieldCascadeSecond_eq U V W u m v hm hv d j,
    zero_smul, add_zero] using H

/-- A concrete first disorder direction of the constrained nested cascade. -/
noncomputable def constrainedPairFieldCascadeDirection (m v : ℕ → ℝ) (d j : ℕ)
    (U V : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) : ℝ :=
  coupledFieldCascadeD m v d (constrainedPairFieldBase n U u) (constrainedPairDirection U V u) j x y

theorem hasDerivAt_constrainedPairFieldCascadeDirection (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => constrainedPairFieldCascadeDirection m v d j (U + b • W) V u x y)
      (constrainedPairFieldCascadeSecond m v d j (U + a • W) V W u x y) a := by
  rw [constrainedPairFieldCascadeSecond_eq _ V W u m v hm hv d j x y]
  exact hasDerivAt_constrainedPairFieldCascadeD U V W u m v hm hv d j x y a

/-- Global continuity of the first disorder direction follows from the proved
bounded mixed Hessian and Mathlib's mean value theorem, not a new smoothness hypothesis. -/
theorem continuous_constrainedPairFieldCascadeDirection (V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Continuous (fun U => constrainedPairFieldCascadeDirection m v d j U V u x y) := by
  let K : ℝ := 8 + 16 * ∑ l ∈ Finset.range j, |m l|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C : ℝ := K * uAbs n V * Fintype.card (Config n)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hK (uAbs_nonneg n V)) (Nat.cast_nonneg _)
  apply (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) ?_).continuous
  intro U U'
  change |constrainedPairFieldCascadeDirection m v d j U V u x y -
    constrainedPairFieldCascadeDirection m v d j U' V u x y| ≤ C * ‖U - U'‖
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun a _ => (hasDerivAt_constrainedPairFieldCascadeDirection U' V (U - U') u m v hm hv d j x y a).hasDerivWithinAt)
    (C := C * ‖U - U'‖) (fun a _ => ?_)
  · simpa only [zero_smul, one_smul, add_zero,
      show U' + (U - U') = U by abel, Real.norm_eq_abs] using H
  · rw [Real.norm_eq_abs]
    refine (constrainedPairFieldCascadeSecond_abs_le (U' + a • (U - U')) V (U - U') u
      m v hm hv d j x y).trans ?_
    have H := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm n (U - U'))
      (mul_nonneg hK (uAbs_nonneg n V))
    dsimp only [C]
    simpa only [mul_assoc] using H

/-- Mathlib's measurability theorem for line derivatives applies to the proved
continuous first direction. This supplies disorder measurability of the actual
mixed Hessian without a duplicate joint-Gaussian differentiation development. -/
theorem measurable_constrainedPairFieldCascadeSecond_disorder (V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Measurable (fun U => constrainedPairFieldCascadeSecond m v d j U V W u x y) := by
  have H := measurable_lineDeriv (𝕜 := ℝ) (v := W)
    (continuous_constrainedPairFieldCascadeDirection V u m v hm hv d j x y)
  have he (U : EnergySpace n) :=
    (hasDerivAt_constrainedPairFieldCascadeDirection U V W u m v hm hv d j x y 0).deriv
  simpa only [lineDeriv, he, zero_smul, add_zero] using H

section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Actual Gaussian-coordinate integration by parts for the full constrained
mixed Hessian. All measurability and integrability hypotheses are discharged;
zero spectral variances are inherited from the existing coordinate Stein theorem. -/
theorem stein_constrainedPairFieldCascadeDirection {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) [DecidableEq hZ.ι] (i : hZ.ι)
    (V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, hZ.c i ω * constrainedPairFieldCascadeDirection m v d j (Z ω) V u x y ∂ℙ) =
      (hZ.τ i : ℝ) * ∫ ω, constrainedPairFieldCascadeSecond m v d j (Z ω) V (hZ.w i) u x y ∂ℙ := by
  have hmeas := (continuous_constrainedPairFieldCascadeDirection V u m v hm hv d j x y).measurable
  have hmeas' := measurable_constrainedPairFieldCascadeSecond_disorder V (hZ.w i) u m v hm hv d j x y
  have hb : ∀ U, |constrainedPairFieldCascadeDirection m v d j U V u x y| ≤ 2 * uAbs n V + 0 * ‖U‖ := by
    intro U
    simpa only [zero_mul, add_zero, constrainedPairFieldCascadeDirection] using
      constrainedPairFieldCascadeD_abs_le U V u m v hm hv d j x y
  have hnn : 0 ≤ 2 * uAbs n V := mul_nonneg (by norm_num) (uAbs_nonneg n V)
  have hb' : ∀ U, |constrainedPairFieldCascadeSecond m v d j U V (hZ.w i) u x y| ≤
      (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n (hZ.w i) + 0 * ‖U‖ := by
    intro U
    simpa only [zero_mul, add_zero] using
      constrainedPairFieldCascadeSecond_abs_le U V (hZ.w i) u m v hm hv d j x y
  have hnn' : 0 ≤ (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n (hZ.w i) :=
    mul_nonneg (mul_nonneg (by positivity) (uAbs_nonneg n V)) (uAbs_nonneg n (hZ.w i))
  exact stein_coord_of_hasDerivAt hZ i
    (fun U a => hasDerivAt_constrainedPairFieldCascadeDirection U V (hZ.w i) u m v hm hv d j x y a)
    hmeas hmeas'
    (integrable_coord_mul_comp_of_affine_norm_bound hZ i hmeas hnn le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas hnn le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas' hnn' le_rfl hb')

/-- Coordinate-summed integration by parts, with the actual Hessian trace inside
the expectation. This is the disorder contribution needed by interpolation. -/
theorem stein_constrainedPairFieldCascadeTrace {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, ∑ i : hZ.ι, hZ.c i ω *
      constrainedPairFieldCascadeDirection m v d j (Z ω) (hZ.w i) u x y ∂ℙ) =
      ∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond m v d j (Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ := by
  classical
  have hi (i : hZ.ι) : Integrable (fun ω => hZ.c i ω *
      constrainedPairFieldCascadeDirection m v d j (Z ω) (hZ.w i) u x y) ℙ := by
    apply integrable_coord_mul_comp_of_affine_norm_bound hZ i
      (continuous_constrainedPairFieldCascadeDirection (hZ.w i) u m v hm hv d j x y).measurable
      (C := 2 * uAbs n (hZ.w i)) (D := 0)
      (mul_nonneg (by norm_num) (uAbs_nonneg n (hZ.w i))) le_rfl
    intro U
    simpa only [zero_mul, add_zero, constrainedPairFieldCascadeDirection] using
      constrainedPairFieldCascadeD_abs_le U (hZ.w i) u m v hm hv d j x y
  have hj (i : hZ.ι) : Integrable (fun ω => (hZ.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d j (Z ω) (hZ.w i) (hZ.w i) u x y) ℙ := by
    apply Integrable.const_mul
    apply integrable_comp_of_affine_norm_bound hZ
      (measurable_constrainedPairFieldCascadeSecond_disorder (hZ.w i) (hZ.w i) u m v hm hv d j x y)
      (C := (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n (hZ.w i) * uAbs n (hZ.w i))
      (D := 0) (mul_nonneg (mul_nonneg (by positivity) (uAbs_nonneg n (hZ.w i)))
        (uAbs_nonneg n (hZ.w i))) le_rfl
    intro U
    simpa only [zero_mul, add_zero] using
      constrainedPairFieldCascadeSecond_abs_le U (hZ.w i) (hZ.w i) u m v hm hv d j x y
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  exact stein_constrainedPairFieldCascadeDirection hZ i (hZ.w i) u m v hm hv d j x y

end GaussianDisorder

end SpinGlass.Targets
