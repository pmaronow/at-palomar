module

public import Targets.MixedCascadeSecond
public import Targets.MixedReplicaWeights
public import Targets.Section5InterleavedContinuity

@[expose] public section

/-!
# Actual Gaussian disorder differentiation of the mixed cascade

The checked mixed Hessian supplies domination for Mathlib's line-derivative
measurability and the existing finite Gaussian Stein theorem. These results
differentiate the genuine disorder average with all field variances fixed;
the simultaneous varying-variance path is a separate remaining step.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

noncomputable def mixedConstrainedDirection (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (U V : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) : ℝ :=
  mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
    (constrainedPairDirection U V u) j x y

noncomputable def mixedConstrainedSecond (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (U V W : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) : ℝ :=
  mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
    (constrainedPairDirection U W u) (constrainedPairDirection U V u)
    (constrainedPairSecond n u U V W) j x y

theorem continuous_mixedConstrainedDirection (V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    Continuous (fun U => mixedConstrainedDirection mode m v j U V u x y) := by
  let K : ℝ := 8 + 16 * ∑ l ∈ Finset.range j, |m l|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C : ℝ := K * uAbs n V * Fintype.card (Config n)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hK (uAbs_nonneg n V)) (Nat.cast_nonneg _)
  apply (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) ?_).continuous
  intro U U'
  change |mixedConstrainedDirection mode m v j U V u x y -
    mixedConstrainedDirection mode m v j U' V u x y| ≤ C * ‖U - U'‖
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun a _ => (hasDerivAt_mixedConstrainedCascadeD U' V (U - U') u mode m v hm hv j x y a).hasDerivWithinAt)
    (C := C * ‖U - U'‖) (fun a _ => ?_)
  · simpa only [zero_smul, one_smul, add_zero, mixedConstrainedDirection,
      show U' + (U - U') = U by abel, Real.norm_eq_abs] using H
  · rw [Real.norm_eq_abs]
    refine (mixedConstrainedCascadeDD_disorder_abs_le (U' + a • (U - U')) V (U - U') u
      mode m v hm hv j x y).trans ?_
    have H := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm n (U - U'))
      (mul_nonneg hK (uAbs_nonneg n V))
    dsimp only [C]
    simpa only [mul_assoc] using H

theorem measurable_mixedConstrainedSecond (V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    Measurable (fun U => mixedConstrainedSecond mode m v j U V W u x y) := by
  have H := measurable_lineDeriv (𝕜 := ℝ) (v := W)
    (continuous_mixedConstrainedDirection V u mode m v hm hv j x y)
  have he (U : EnergySpace n) :=
    (hasDerivAt_mixedConstrainedCascadeD U V W u mode m v hm hv j x y 0).deriv
  simpa only [lineDeriv, mixedConstrainedDirection, mixedConstrainedSecond, he,
    zero_smul, add_zero] using H

theorem mixedConstrainedDirection_sum {I : Type*} [Fintype I]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ)
    (c : I → ℝ) (V : I → EnergySpace n) (x y : Fin n → ℝ) :
    mixedConstrainedDirection mode m v j U (∑ i, c i • V i) u x y =
      ∑ i, c i * mixedConstrainedDirection mode m v j U (V i) u x y := by
  have he : constrainedPairDirection U (∑ i, c i • V i) u =
      fun x y => ∑ i, c i * constrainedPairDirection U (V i) u x y :=
    funext fun x => funext fun y => constrainedPairDirection_sum U u c V x y
  simp only [mixedConstrainedDirection, he]
  exact mixedVectorCascadeD_sum
    (constrainedPairFieldCascade_growth U u (fun _ => 0) (fun _ => 0)
      (fun _ => le_rfl) (fun _ => le_rfl) 0 0)
    (fun i => by
      have H := (constrainedPairFieldBase_paramDeriv U (V i) u 0).measurable_deriv 0
        ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
      simpa only [zero_smul, add_zero] using H)
    (fun i => constrainedPairDirection_abs_le U (V i) u) c mode m v hm hv j x y

theorem continuous_mixedConstrainedCascade_disorder (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    Continuous (fun U => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y) := by
  simp only [mixedVectorCascade_eq_list]
  exact continuous_mixedConstrainedList_disorder mode m v (List.range j).reverse
    (fun a _ => hm a) (fun a _ => hv a) u x y

section Gaussian

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The actual radial direction uses the original spectral representation. -/
theorem mixedConstrainedDirection_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) (ω : Ω) :
    mixedConstrainedDirection mode m v j (a • Z ω) (Z ω) u x y =
      ∑ i : hZ.ι, hZ.c i ω * mixedConstrainedDirection mode m v j (a • Z ω) (hZ.w i) u x y := by
  conv_lhs => arg 6; rw [hZ.repr]
  exact mixedConstrainedDirection_sum _ u mode m v hm hv j (fun i => hZ.c i ω) hZ.w x y

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurable_mixedConstrainedDirection_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    Measurable (fun ω => mixedConstrainedDirection mode m v j (a • Z ω) (Z ω) u x y) := by
  simp_rw [mixedConstrainedDirection_radial hZ a u mode m v hm hv j x y]
  exact Finset.measurable_sum _ fun i _ => (hZ.c_meas i).mul
    ((continuous_mixedConstrainedDirection (hZ.w i) u mode m v hm hv j x y).measurable.comp
      (hZ.repr_measurable.const_smul a))

/-- Gaussian-coordinate Stein with all domination supplied by actual derivatives. -/
theorem stein_mixedConstrainedCascade_scaled {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) [DecidableEq hZ.ι] (i : hZ.ι)
    (a : ℝ) (V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, hZ.c i ω * mixedConstrainedDirection mode m v j (a • Z ω) V u x y ∂ℙ) =
      (hZ.τ i : ℝ) * ∫ ω, a * mixedConstrainedSecond mode m v j (a • Z ω) V (hZ.w i) u x y ∂ℙ := by
  let Φ := fun U => mixedConstrainedDirection mode m v j (a • U) V u x y
  let Φ' := fun U => a * mixedConstrainedSecond mode m v j (a • U) V (hZ.w i) u x y
  have hmeas : Measurable Φ :=
    (continuous_mixedConstrainedDirection V u mode m v hm hv j x y).measurable.comp (by fun_prop)
  have hmeas' : Measurable Φ' :=
    ((measurable_mixedConstrainedSecond V (hZ.w i) u mode m v hm hv j x y).comp
      (by fun_prop)).const_mul a
  have hb (U : EnergySpace n) : |Φ U| ≤ 2 * uAbs n V + 0 * ‖U‖ := by
    simpa only [Φ, zero_mul, add_zero, mixedConstrainedDirection] using
      mixedConstrainedCascadeD_disorder_abs_le (a • U) V u mode m v hm hv j x y
  let C := |a| * ((8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n (hZ.w i))
  have hV := uAbs_nonneg n V
  have hW := uAbs_nonneg n (hZ.w i)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb' (U : EnergySpace n) : |Φ' U| ≤ C + 0 * ‖U‖ := by
    simp only [Φ', abs_mul, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left
      (mixedConstrainedCascadeDD_disorder_abs_le _ V (hZ.w i) u mode m v hm hv j x y) (abs_nonneg a)
  apply stein_coord_of_hasDerivAt hZ i (Φ := Φ) (Φ' := Φ') ?_ hmeas hmeas'
    (integrable_coord_mul_comp_of_affine_norm_bound hZ i hmeas (by positivity) le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas (by positivity) le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas' hC le_rfl hb')
  intro U b
  have H := (hasDerivAt_mixedConstrainedCascadeD (a • U) V (hZ.w i) u
    mode m v hm hv j x y (a * b)).comp b ((hasDerivAt_id b).const_mul a)
  simpa only [Φ, Φ', mixedConstrainedDirection, mixedConstrainedSecond,
    Function.comp_def, smul_add, smul_smul, mul_comm, mul_one] using H

/-- Differentiation passes through the actual mixed Gaussian average. -/
theorem hasDerivAt_mixedConstrainedGaussian_amplitude {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => ∫ ω, mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (b • Z ω) u) j x y ∂ℙ)
      (∫ ω, mixedConstrainedDirection mode m v j (a • Z ω) (Z ω) u x y ∂ℙ) a := by
  have hint : Integrable (fun ω => mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (a • Z ω) u) j x y) ℙ := by
    simp only [mixedVectorCascade_eq_list]
    exact integrable_mixedConstrainedList_amplitude hZ a u mode m v (List.range j).reverse
      (fun b _ => hm b) (fun b _ => hv b) x y
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
    (F := fun b ω => mixedVectorCascade n mode m v (constrainedPairFieldBase n (b • Z ω) u) j x y)
    (F' := fun b ω => mixedConstrainedDirection mode m v j (b • Z ω) (Z ω) u x y)
    (s := Set.univ) (bound := fun ω => 2 * Fintype.card (Config n) * ‖Z ω‖)
    Filter.univ_mem ?_ hint
    (measurable_mixedConstrainedDirection_radial hZ a u mode m v hm hv j x y).aestronglyMeasurable
    ?_ ((integrable_norm_of_gaussian hZ).const_mul _) ?_).2
  · exact Filter.Eventually.of_forall fun b =>
      ((continuous_mixedConstrainedCascade_disorder u mode m v hm hv j x y).measurable.comp
        (hZ.repr_measurable.const_smul b)).aestronglyMeasurable
  · filter_upwards with ω b _
    rw [Real.norm_eq_abs]
    exact (mixedConstrainedCascadeD_disorder_abs_le (b • Z ω) (Z ω) u mode m v hm hv j x y).trans
      (by nlinarith [uAbs_le_card_mul_norm n (Z ω)])
  · filter_upwards with ω b _
    simpa only [zero_add, mixedConstrainedDirection] using
      hasDerivAt_mixedConstrainedCascade 0 (Z ω) u mode m v hm hv j x y b

/-- Radial Stein uses the same full mixed Hessian at every original spectral
coordinate, including zero spectral variances. -/
theorem stein_mixedConstrainedCascade_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, mixedConstrainedDirection mode m v j (a • Z ω) (Z ω) u x y ∂ℙ) =
      a * ∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        mixedConstrainedSecond mode m v j (a • Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ := by
  classical
  have hi (i : hZ.ι) : Integrable (fun ω => hZ.c i ω *
      mixedConstrainedDirection mode m v j (a • Z ω) (hZ.w i) u x y) ℙ := by
    have hW := uAbs_nonneg n (hZ.w i)
    apply integrable_coord_mul_comp_of_affine_norm_bound hZ i
      ((continuous_mixedConstrainedDirection (hZ.w i) u mode m v hm hv j x y).measurable.comp
        (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
      (C := 2 * uAbs n (hZ.w i)) (D := 0) (by positivity) le_rfl
    intro U
    simpa only [zero_mul, add_zero, mixedConstrainedDirection, Function.comp_apply] using
      mixedConstrainedCascadeD_disorder_abs_le (a • U) (hZ.w i) u mode m v hm hv j x y
  have hH (i : hZ.ι) : Integrable (fun ω =>
      mixedConstrainedSecond mode m v j (a • Z ω) (hZ.w i) (hZ.w i) u x y) ℙ := by
    have hW := uAbs_nonneg n (hZ.w i)
    apply integrable_comp_of_affine_norm_bound hZ
      ((measurable_mixedConstrainedSecond (hZ.w i) (hZ.w i) u mode m v hm hv j x y).comp
        (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
      (C := (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n (hZ.w i) * uAbs n (hZ.w i))
      (D := 0) (by positivity) le_rfl
    intro U
    simpa only [zero_mul, add_zero, mixedConstrainedSecond, Function.comp_apply] using
      mixedConstrainedCascadeDD_disorder_abs_le (a • U) (hZ.w i) (hZ.w i) u mode m v hm hv j x y
  simp_rw [mixedConstrainedDirection_radial hZ a u mode m v hm hv j x y]
  rw [integral_finsetSum _ (fun i _ => hi i),
    integral_finsetSum _ (fun i _ => (hH i).const_mul (hZ.τ i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [stein_mixedConstrainedCascade_scaled hZ i a (hZ.w i) u mode m v hm hv j x y,
    integral_const_mul, integral_const_mul]
  ring

/-- The actual disorder-amplitude derivative after Gaussian integration by parts. -/
theorem hasDerivAt_mixedConstrainedGaussian_amplitude_trace {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => ∫ ω, mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (b • Z ω) u) j x y ∂ℙ)
      (a * ∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        mixedConstrainedSecond mode m v j (a • Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ) a := by
  rw [← stein_mixedConstrainedCascade_radial hZ a u mode m v hm hv j x y]
  exact hasDerivAt_mixedConstrainedGaussian_amplitude hZ a u mode m v hm hv j x y

end Gaussian

end SpinGlass.Targets
