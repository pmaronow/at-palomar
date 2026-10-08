module

public import Targets.MixedCascadeDeriv
public import Targets.CoupledReplicaHessian

@[expose] public section

/-!
# Actual second derivatives of arbitrary mixed Gaussian cascades

The covariance rule is uniform across all modes. For independent fields the
two intermediate covariance products cancel by the checked algebraic identity;
opposite fields are a reflected shared tilt. All masses are raw masses.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

/-- The common derivative-of-mean covariance expression for every mode. -/
noncomputable def mixedVectorCovariance (n : ℕ) (mode : Section5GaussianMode) (m v : ℝ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  mixedVectorMean n mode m v A (fun x y => GW x y + m * G x y * AW x y) x y -
    m * mixedVectorMean n mode m v A G x y * mixedVectorMean n mode m v A AW x y

/-- Number of one-field covariance bounds in a mixed Gaussian level. -/
def Section5GaussianMode.covarianceFactor : Section5GaussianMode → ℝ
  | .independent => 4
  | .shared => 2
  | .opposite => 2

/-- Actual mixed covariance recursion, expressed using the common normalized
mean rule rather than mode-dependent unproved Hessian formulas. -/
noncomputable def mixedVectorCascadeDD (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => GW
  | j + 1 => mixedVectorCovariance n (mode j) (m j) (v j)
      (mixedVectorCascade n mode m v A j)
      (mixedVectorCascadeD n mode m v A AW j)
      (mixedVectorCascadeD n mode m v A G j)
      (mixedVectorCascadeDD n mode m v A AW G GW j)

noncomputable def mixedHessianBound (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ)
    (BV BW BH : ℝ) : ℕ → ℝ
  | 0 => BH
  | j + 1 => mixedHessianBound mode m BV BW BH j +
      (mode j).covarianceFactor * |m j| * BV * BW

variable {n : ℕ}

/-- The proved one-step covariance derivative, together with all bounds and
measurability needed to iterate it. Zero mass and variance are included. -/
theorem CoupledParamDeriv.tiltMixed
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH m v : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s)
    (mode : Section5GaussianMode) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a => mixedVectorMean n mode m v (A a) (G a))
      (fun a => mixedVectorCovariance n mode m v (A a) (AW a) (G a) (GW a))
      s (BH + mode.covarianceFactor * |m| * BV * BW) ∧
    (∀ a ∈ s, ∀ x y, |mixedVectorMean n mode m v (A a) (G a) x y| ≤ BV) := by
  cases mode with
  | independent =>
    have H := hA.tiltIndependent hG hGB hs hm hv
    refine ⟨H.1.congr_eq_on hs (fun _ _ => rfl) ?_, H.2⟩
    intro a _
    funext x y
    exact (pairedIndependentCovariance_eq_mean m v (A a) (AW a) (G a) (GW a) x y).symm
  | shared => exact hA.tiltShared hG hGB hs
  | opposite =>
    have H := hA.flip_second.tiltShared hG.flip_second
      (fun a ha x y => hGB a ha x (-y)) hs (m := m) (v := v)
    exact ⟨H.1.flip_second, fun a ha x y => H.2 a ha x (-y)⟩

/-- The actual derivative of the normalized first-derivative recursion at
every mixed depth, with an explicit finite bound. -/
theorem CoupledParamDeriv.mixedCascadeSecond
    {A AW G GW : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BW BV BH : ℝ}
    (hA : CoupledParamDeriv A AW s BW) (hG : CoupledParamDeriv G GW s BH)
    (hGB : ∀ a ∈ s, ∀ x y, |G a x y| ≤ BV) (hs : IsOpen s)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) :
    CoupledParamDeriv (fun a => mixedVectorCascadeD n mode m v (A a) (G a) j)
      (fun a => mixedVectorCascadeDD n mode m v (A a) (AW a) (G a) (GW a) j)
      s (mixedHessianBound mode m BV BW BH j) ∧
    (∀ a ∈ s, ∀ x y, |mixedVectorCascadeD n mode m v (A a) (G a) j x y| ≤ BV) := by
  induction j with
  | zero => exact ⟨hG, hGB⟩
  | succ j ih =>
    exact (hA.mixedCascade hs mode m v hm hv j).tiltMixed ih.1 ih.2 hs (mode j) (hm j) (hv j)

theorem mixedHessianBound_eq_sum (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ)
    (j : ℕ) (BV BW BH : ℝ) :
    mixedHessianBound mode m BV BW BH j =
      BH + (∑ l ∈ Finset.range j, (mode l).covarianceFactor * |m l|) * BV * BW := by
  induction j with
  | zero => simp [mixedHessianBound]
  | succ j ih => rw [mixedHessianBound, ih, Finset.sum_range_succ]; ring

theorem mixedHessianBound_le (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ)
    (j : ℕ) {BV BW BH : ℝ} (hBV : 0 ≤ BV) (hBW : 0 ≤ BW) :
    mixedHessianBound mode m BV BW BH j ≤ BH + 4 * (∑ l ∈ Finset.range j, |m l|) * BV * BW := by
  rw [mixedHessianBound_eq_sum]
  have H : (∑ l ∈ Finset.range j, (mode l).covarianceFactor * |m l|) ≤
      4 * ∑ l ∈ Finset.range j, |m l| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    cases mode l <;> norm_num [Section5GaussianMode.covarianceFactor]
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H hBV) hBW]

/-- Actual disorder differentiation of the transported first direction. -/
theorem hasDerivAt_mixedConstrainedCascadeD (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => mixedVectorCascadeD n mode m v
      (constrainedPairFieldBase n (U + b • W) u) (constrainedPairDirection (U + b • W) V u) j x y)
      (mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n (U + a • W) u)
        (constrainedPairDirection (U + a • W) W u) (constrainedPairDirection (U + a • W) V u)
        (constrainedPairSecond n u (U + a • W) V W) j x y) a :=
  ((constrainedPairFieldBase_paramDeriv U W u a).mixedCascadeSecond
    (constrainedPairDirection_paramDeriv U V W u a)
    (fun b _ x y => constrainedPairDirection_abs_le (U + b • W) V u x y)
    isOpen_Ioo mode m v hm hv j).1.deriv a ⟨by linarith, by linarith⟩ x y

/-- The actual second disorder derivative is the common covariance recursion. -/
theorem hasDerivAt_mixedConstrainedCascade_second (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => mixedVectorCascade n mode m v
        (constrainedPairFieldBase n (U + a • W + b • V) u) j x y) 0)
      (mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairDirection U W u) (constrainedPairDirection U V u)
        (constrainedPairSecond n u U V W) j x y) 0 := by
  have he (a : ℝ) := (hasDerivAt_mixedConstrainedCascade (U + a • W) V u mode m v hm hv j x y 0).deriv
  simp only [zero_smul, add_zero] at he
  simp only [he]
  simpa only [zero_smul, add_zero] using
    hasDerivAt_mixedConstrainedCascadeD U V W u mode m v hm hv j x y 0

/-- Uniform finite-depth domination for the actual disorder covariance. -/
theorem mixedConstrainedCascadeDD_disorder_abs_le (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    |mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairDirection U W u) (constrainedPairDirection U V u)
      (constrainedPairSecond n u U V W) j x y| ≤
      (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n W := by
  have H := ((constrainedPairFieldBase_paramDeriv U W u 0).mixedCascadeSecond
    (constrainedPairDirection_paramDeriv U V W u 0)
    (fun b _ x y => constrainedPairDirection_abs_le (U + b • W) V u x y)
    isOpen_Ioo mode m v hm hv j).1.bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simp only [zero_smul, add_zero] at H
  refine H.trans ((mixedHessianBound_le mode m j
    (mul_nonneg (by norm_num) (uAbs_nonneg n V))
    (mul_nonneg (by norm_num) (uAbs_nonneg n W))).trans_eq ?_)
  ring

/-- The true mixed spatial second derivative, with independent choices of
the first and varying directions in both replicas. -/
theorem hasDerivAt_mixedConstrainedCascade_field_second (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ)
    (A B C D x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => mixedVectorCascade n mode m v
        (constrainedPairFieldBase n U u) j (x + a • C + b • A) (y + a • D + b • B)) 0)
      (mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
        (constrainedPairFieldCovariance U u A B C D) j x y) 0 := by
  have hefun (a b : ℝ) :
      mixedVectorCascade n mode m v (fun x y => constrainedPairFieldBase n U u
        (x + a • C + b • A) (y + a • D + b • B)) j x y =
      mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j
        (x + a • C + b • A) (y + a • D + b • B) := by
    calc
      _ = mixedVectorCascade n mode m v
          (fun x y => constrainedPairFieldBase n U u (x + b • A) (y + b • B)) j
          (x + a • C) (y + a • D) :=
        mixedVectorCascade_translate mode m v j _ (a • C) (a • D) x y
      _ = _ := mixedVectorCascade_translate mode m v j _ (b • A) (b • B) _ _
  have he (a : ℝ) := ((((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).translate_fields
    (a • C) (a • D)).mixedCascade isOpen_Ioo mode m v hm hv j).deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y).deriv
  simp only [hefun, zero_smul, add_zero] at he
  simp only [he]
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).mixedCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo mode m v hm hv j).1.deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [zero_smul, add_zero] using H

/-- The normalized spatial first direction has the actual spatial covariance
as its derivative along any second field direction. -/
theorem hasDerivAt_mixedConstrainedCascadeD_field (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ)
    (A B C D x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j (x + a • C) (y + a • D))
      (mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
        (constrainedPairFieldCovariance U u A B C D) j x y) 0 := by
  have H := hasDerivAt_mixedConstrainedCascade_field_second U u mode m v hm hv j A B C D x y
  have he (a : ℝ) := (hasDerivAt_mixedConstrainedCascade_field U u mode m v hm hv j A B
    (x + a • C) (y + a • D)).deriv
  simp only [he] at H
  exact H

/-- A field-uniform bound for every mixed spatial Hessian. It supplies
domination for the later Gaussian heat generator at fixed finite depth. -/
theorem mixedConstrainedCascadeDD_field_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ)
    (A B C D x y : Fin n → ℝ) :
    |mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
      (constrainedPairFieldCovariance U u A B C D) j x y| ≤
      (2 + 4 * ∑ l ∈ Finset.range j, |m l|) * (l1 A + l1 B) * (l1 C + l1 D) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).mixedCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo mode m v hm hv j).1.bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simp only [zero_smul, add_zero] at H
  refine H.trans ((mixedHessianBound_le mode m j (by positivity : 0 ≤ l1 A + l1 B)
    (by positivity : 0 ≤ l1 C + l1 D)).trans_eq ?_)
  ring

end SpinGlass.Targets
