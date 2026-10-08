module

public import Targets.MixedCascadeSecond
public import Targets.MixedReplicaWeights
public import Targets.CoupledCascadeVariance

@[expose] public section

/-!
# Genuine Gaussian heat calculus for mixed constrained cascades

The inner mixed cascade is fixed. Its already proved actual spatial derivatives
discharge the analytic hypotheses of the existing finite-dimensional Gaussian
heat theorem. No variance derivative or interpolation comparison is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

noncomputable def mixedCascadeSpatialFirst (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (U : EnergySpace n) (u : ℝ)
    (A B : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
    (constrainedPairFieldDirection U u A B) j

noncomputable def mixedCascadeSpatialSecond (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (U : EnergySpace n) (u : ℝ)
    (A B C D : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
    (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
    (constrainedPairFieldCovariance U u A B C D) j

theorem mixedConstrainedCascade_growth (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) :
    CoupledGrowth (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j) := by
  exact (constrainedPairFieldCascade_growth U u (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) 0 0).mixedCascade mode m v hm hv j

theorem measurable_mixedCascadeSpatialFirst (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedCascadeSpatialFirst mode m v j U u A B p.1 p.2) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).mixedCascade
    isOpen_Ioo mode m v hm hv j).measurable_deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [mixedCascadeSpatialFirst, zero_smul, add_zero] using H

theorem measurable_mixedCascadeSpatialSecond (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B C D : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedCascadeSpatialSecond mode m v j U u A B C D p.1 p.2) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).mixedCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo mode m v hm hv j).1.measurable_deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [mixedCascadeSpatialSecond, zero_smul, add_zero] using H

theorem mixedCascadeSpatialFirst_sum {I : Type*} [Fintype I]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (c : I → ℝ) (A B : I → Fin n → ℝ) (x y : Fin n → ℝ) :
    mixedCascadeSpatialFirst mode m v j U u (∑ i, c i • A i) (∑ i, c i • B i) x y =
      ∑ i, c i * mixedCascadeSpatialFirst mode m v j U u (A i) (B i) x y := by
  classical
  unfold mixedCascadeSpatialFirst
  simp only [show constrainedPairFieldDirection U u (∑ i, c i • A i) (∑ i, c i • B i) =
    fun x y => ∑ i, c i * constrainedPairFieldDirection U u (A i) (B i) x y from
      funext fun x => funext fun y => constrainedPairFieldDirection_sum U u c A B x y]
  exact mixedVectorCascadeD_sum (mixedConstrainedCascade_growth U u mode m v hm hv 0)
    (fun i => measurable_constrainedPairFieldDirection U u (A i) (B i))
    (fun i => constrainedPairFieldDirection_abs_le U u (A i) (B i)) c mode m v hm hv j x y

theorem hasDerivAt_mixedCascadeSpatialLine (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (A B x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun a : ℝ => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j
      (x + a • A) (y + a • B))
      (mixedCascadeSpatialFirst mode m v j U u A B (x + r • A) (y + r • B)) r := by
  have H := hasDerivAt_mixedConstrainedCascade_field U u mode m v hm hv j A B
    (x + r • A) (y + r • B)
  have H' := HasDerivAt.comp_sub_const r r (by simpa only [sub_self] using H)
  apply H'.congr_of_eventuallyEq
  filter_upwards with a
  congr 1 <;> simp only [sub_smul] <;> abel

theorem hasDerivAt_mixedCascadeSpatialFirst_line (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (A B C D x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun a : ℝ => mixedCascadeSpatialFirst mode m v j U u A B
      (x + a • C) (y + a • D))
      (mixedCascadeSpatialSecond mode m v j U u A B C D (x + r • C) (y + r • D)) r := by
  have H := hasDerivAt_mixedConstrainedCascadeD_field U u mode m v hm hv j A B C D
    (x + r • C) (y + r • D)
  have H' := HasDerivAt.comp_sub_const r r (by simpa only [sub_self] using H)
  apply H'.congr_of_eventuallyEq
  filter_upwards with a
  congr 1 <;> simp only [sub_smul] <;> abel

/-- The actual additional finite-dimensional Gaussian level, with arbitrary
physical directions in both replica fields. This includes opposite directions
without changing either external field. -/
theorem hasDerivAt_mixedConstrainedField_linear_variance {p : ℕ}
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ)
    (mass : ℝ) {variance : ℝ} (hvar : 0 < variance) :
    let F := fun z : Fin p → ℝ => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j
      (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)
    HasDerivAt (fun w => parisiStepPi p mass w F 0)
      ((∑ i : Fin p, pairedTiltMean mass variance F (fun z =>
        mixedCascadeSpatialSecond mode m v j U u (A i) (B i) (A i) (B i)
          (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) +
        mass * (mixedCascadeSpatialFirst mode m v j U u (A i) (B i)
          (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)) ^ 2) 0) / 2) variance := by
  classical
  dsimp only
  let L := ∑ i : Fin p, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hLi (i : Fin p) : l1 (A i) + l1 (B i) ≤ L :=
    Finset.single_le_sum (fun l _ => add_nonneg (l1_nonneg _) (l1_nonneg _)) (Finset.mem_univ i)
  let K := 2 + 4 * ∑ l ∈ Finset.range j, |m l|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg := mixedConstrainedCascade_growth U u mode m v hm hv j
  obtain ⟨C, D, hD, hb⟩ := hg.bound
  have hmap : Measurable (fun z : Fin p → ℝ =>
      (x + pairedFieldLinear A z, y + pairedFieldLinear B z)) :=
    (measurable_const.add (measurable_pairedFieldLinear A)).prodMk
      (measurable_const.add (measurable_pairedFieldLinear B))
  apply hasDerivAt_parisiStepPi_variance (C := C + D * (l1 x + l1 y)) (D := D * L)
    (B := L) (H := K * L * L) (mul_nonneg hD hL) hL
    (hg.measurable.comp hmap)
    (fun i => (measurable_mixedCascadeSpatialFirst U u mode m v hm hv j (A i) (B i)).comp hmap)
    (fun i => (measurable_mixedCascadeSpatialSecond U u mode m v hm hv j (A i) (B i) (A i) (B i)).comp hmap)
    ?_ ?_ ?_ ?_ ?_ mass 0 hvar
  · intro z
    dsimp only [Function.comp_apply]
    have hAB : l1 (pairedFieldLinear A z) + l1 (pairedFieldLinear B z) ≤ L * l1 z := by
      have hA := l1_pairedFieldLinear_le A z
      have hB := l1_pairedFieldLinear_le B z
      dsimp only [L]
      rw [Finset.sum_add_distrib]
      nlinarith
    nlinarith [hb (x + pairedFieldLinear A z) (y + pairedFieldLinear B z),
      l1_add_le x (pairedFieldLinear A z), l1_add_le y (pairedFieldLinear B z)]
  · intro i z
    exact (mixedConstrainedCascadeD_field_abs_le U u mode m v hm hv j (A i) (B i) _ _).trans (hLi i)
  · intro i z
    refine (mixedConstrainedCascadeDD_field_abs_le U u mode m v hm hv j (A i) (B i) (A i) (B i) _ _).trans ?_
    change K * (l1 (A i) + l1 (B i)) * (l1 (A i) + l1 (B i)) ≤ K * L * L
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hLi i) hK) (hLi i)
      (add_nonneg (l1_nonneg _) (l1_nonneg _)) (mul_nonneg hK hL)
  · intro z w a
    dsimp only [Function.comp_apply]
    simp only [pairedFieldLinear_add_smul, ← add_assoc]
    have H := hasDerivAt_mixedCascadeSpatialLine U u mode m v hm hv j
      (pairedFieldLinear A w) (pairedFieldLinear B w)
      (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) a
    simp only [pairedFieldLinear, mixedCascadeSpatialFirst_sum U u mode m v hm hv] at H
    simpa only [pairedFieldLinear] using H
  · intro i z a
    dsimp only [Function.comp_apply]
    have H := hasDerivAt_mixedCascadeSpatialFirst_line U u mode m v hm hv j
      (A i) (B i) (A i) (B i) (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) a
    simpa only [pairedFieldLinear_add_smul, pairedFieldLinear_single, ← add_assoc] using H

end SpinGlass.Targets
