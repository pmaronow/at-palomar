module

/-
# The Gaussian-disorder contribution to the second interpolation

All field variances are fixed in this module. The actual constrained nested
cascade is differentiated in its disorder amplitude, then Gaussian Stein
identifies this derivative with the full nested disorder Hessian trace.
This is one contribution to, not the full derivative of, Section 5's interpolation.
-/
public import Targets.CoupledCascadeVariance

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem constrainedPairDirection_sum {ι : Type*} [Fintype ι]
    (U : EnergySpace n) (u : ℝ) (c : ι → ℝ) (V : ι → EnergySpace n)
    (x y : Fin n → ℝ) :
    constrainedPairDirection U (∑ i, c i • V i) u x y =
      ∑ i, c i * constrainedPairDirection U (V i) u x y := by
  classical
  have he (σ : Config n) : (∑ i, c i • V i) σ = ∑ i, c i * V i σ := by
    change (WithLp.ofLp (∑ i, c i • V i)) σ = _
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simp only [constrainedPairDirection, he, ← Finset.sum_add_distrib, ← mul_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

/-- Finite linearity of the genuine recursively tilted disorder direction. -/
theorem constrainedPairFieldCascadeDirection_sum {ι : Type*} [Fintype ι]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (c : ι → ℝ) (V : ι → EnergySpace n) (x y : Fin n → ℝ) :
    constrainedPairFieldCascadeDirection m v d j U (∑ i, c i • V i) u x y =
      ∑ i, c i * constrainedPairFieldCascadeDirection m v d j U (V i) u x y := by
  classical
  unfold constrainedPairFieldCascadeDirection
  induction j generalizing x y with
  | zero => exact constrainedPairDirection_sum U u c V x y
  | succ j ih =>
    have hg (i : ι) := ((constrainedPairFieldBase_paramDeriv U (V i) u 0).fieldCascade
      isOpen_Ioo m v hm hv d j).measurable_deriv 0
        (show (0 : ℝ) ∈ guerraLineNbhd 0 by constructor <;> norm_num [guerraLineNbhd])
    simp only [zero_smul, add_zero] at hg
    have hb (i : ι) := constrainedPairFieldCascadeD_abs_le U (V i) u m v hm hv d j
    have he : coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (constrainedPairDirection U (∑ i, c i • V i) u) j =
        fun x y => ∑ i, c i * coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
          (constrainedPairDirection U (V i) u) j x y := funext fun x => funext fun y => ih x y
    simp only [coupledFieldCascadeD]
    split_ifs
    · rw [he]
      exact pairedIndependentMean_sum (constrainedPairFieldCascade_growth U u m v hm hv d j)
        hg hb c (hm j) (hv j) x y
    · rw [he]
      exact pairedSharedMean_sum (constrainedPairFieldCascade_growth U u m v hm hv d j)
        hg hb c (m j) (v j) x y

/-- Disorder stability of the full actual cascade, with no loss in the depth. -/
theorem constrainedPairFieldCascade_disorder_dist_le (U U' : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    |coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y -
      coupledFieldCascade n m v d (constrainedPairFieldBase n U' u) j x y| ≤
      2 * uAbs n (U - U') := by
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun a _ => (hasDerivAt_constrainedPairFieldCascade U' (U - U') u m v hm hv d j x y a).hasDerivWithinAt)
    (C := 2 * uAbs n (U - U')) (fun a _ => ?_)
  · simpa only [zero_smul, one_smul, add_zero,
      show U' + (U - U') = U by abel, Real.norm_eq_abs] using H
  · exact constrainedPairFieldCascadeD_abs_le _ _ u m v hm hv d j x y

theorem continuous_constrainedPairFieldCascade_disorder (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Continuous (fun U => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨2 * Fintype.card (Config n), by positivity⟩) ?_).continuous
  intro U U'
  change |_ - _| ≤ (2 * Fintype.card (Config n)) * ‖U - U'‖
  exact (constrainedPairFieldCascade_disorder_dist_le U U' u m v hm hv d j x y).trans
    (by nlinarith [uAbs_le_card_mul_norm n (U - U')])

section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The direction along the random disorder is its actual finite spectral sum. -/
theorem constrainedPairFieldCascadeDirection_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) (ω : Ω) :
    constrainedPairFieldCascadeDirection m v d j (a • Z ω) (Z ω) u x y =
      ∑ i : hZ.ι, hZ.c i ω *
        constrainedPairFieldCascadeDirection m v d j (a • Z ω) (hZ.w i) u x y := by
  conv_lhs => arg 6; rw [hZ.repr]
  exact constrainedPairFieldCascadeDirection_sum _ u m v hm hv d j (fun i => hZ.c i ω) hZ.w x y

/-- Amplitude-scaled coordinate Stein, retaining the original spectral variances. -/
theorem stein_constrainedPairFieldCascade_scaled {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) [DecidableEq hZ.ι] (i : hZ.ι)
    (a : ℝ) (V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, hZ.c i ω * constrainedPairFieldCascadeDirection m v d j (a • Z ω) V u x y ∂ℙ) =
      (hZ.τ i : ℝ) * ∫ ω, a *
        constrainedPairFieldCascadeSecond m v d j (a • Z ω) V (hZ.w i) u x y ∂ℙ := by
  let Φ := fun U => constrainedPairFieldCascadeDirection m v d j (a • U) V u x y
  let Φ' := fun U => a * constrainedPairFieldCascadeSecond m v d j (a • U) V (hZ.w i) u x y
  have hmeas : Measurable Φ :=
    (continuous_constrainedPairFieldCascadeDirection V u m v hm hv d j x y).measurable.comp
      (by fun_prop)
  have hmeas' : Measurable Φ' :=
    ((measurable_constrainedPairFieldCascadeSecond_disorder V (hZ.w i) u m v hm hv d j x y).comp
      (by fun_prop)).const_mul a
  have hb (U : EnergySpace n) : |Φ U| ≤ 2 * uAbs n V + 0 * ‖U‖ := by
    simpa only [Φ, zero_mul, add_zero, constrainedPairFieldCascadeDirection] using
      constrainedPairFieldCascadeD_abs_le (a • U) V u m v hm hv d j x y
  let C := |a| * ((8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n V * uAbs n (hZ.w i))
  have hV := uAbs_nonneg n V
  have hW := uAbs_nonneg n (hZ.w i)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb' (U : EnergySpace n) : |Φ' U| ≤ C + 0 * ‖U‖ := by
    simp only [Φ', abs_mul, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left
      (constrainedPairFieldCascadeSecond_abs_le _ V (hZ.w i) u m v hm hv d j x y) (abs_nonneg a)
  apply stein_coord_of_hasDerivAt hZ i (Φ := Φ) (Φ' := Φ') ?_ hmeas hmeas'
    (integrable_coord_mul_comp_of_affine_norm_bound hZ i hmeas (by positivity) le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas (by positivity) le_rfl hb)
    (integrable_comp_of_affine_norm_bound hZ hmeas' hC le_rfl hb')
  intro U b
  have H := (hasDerivAt_constrainedPairFieldCascadeDirection (a • U) V (hZ.w i) u
    m v hm hv d j x y (a * b)).comp b ((hasDerivAt_id b).const_mul a)
  simpa only [Φ, Φ', Function.comp_def, smul_add, smul_smul, mul_comm, mul_one] using H

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Measurability of the actual random radial direction, without assuming a
joint measurability theorem for arbitrary directional derivatives. -/
theorem measurable_constrainedPairFieldCascade_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Measurable (fun ω => constrainedPairFieldCascadeDirection m v d j (a • Z ω) (Z ω) u x y) := by
  simp_rw [constrainedPairFieldCascadeDirection_radial hZ a u m v hm hv d j x y]
  exact Finset.measurable_sum _ fun i _ => (hZ.c_meas i).mul
    ((continuous_constrainedPairFieldCascadeDirection (hZ.w i) u m v hm hv d j x y).measurable.comp
      (hZ.repr_measurable.const_smul a))

/-- Gaussian integrability of the genuine cascade at every disorder amplitude. -/
theorem integrable_constrainedPairFieldCascade_amplitude {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Integrable (fun ω => coupledFieldCascade n m v d (constrainedPairFieldBase n (a • Z ω) u) j x y) ℙ := by
  let F := fun U => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y
  apply integrable_comp_of_affine_norm_bound hZ
    ((continuous_constrainedPairFieldCascade_disorder u m v hm hv d j x y).measurable.comp
      (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
    (C := |F 0|) (D := 2 * Fintype.card (Config n) * |a|) (abs_nonneg _) (by positivity)
  intro U
  have H := constrainedPairFieldCascade_disorder_dist_le (a • U) 0 u m v hm hv d j x y
  have Hb := uAbs_le_card_mul_norm n (a • U)
  simp only [sub_zero] at H
  simp only [norm_smul, Real.norm_eq_abs] at Hb
  have Ht := abs_add_le (F (a • U) - F 0) (F 0)
  rw [sub_add_cancel] at Ht
  change |F (a • U) - F 0| ≤ _ at H
  change |F (a • U)| ≤ _
  nlinarith

/-- Differentiation under the outer Gaussian expectation in the actual
disorder amplitude; the dominating bound is independent of that amplitude. -/
theorem hasDerivAt_constrainedPairGaussian_amplitude {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => ∫ ω, coupledFieldCascade n m v d
      (constrainedPairFieldBase n (b • Z ω) u) j x y ∂ℙ)
      (∫ ω, constrainedPairFieldCascadeDirection m v d j (a • Z ω) (Z ω) u x y ∂ℙ) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
    (F := fun b ω => coupledFieldCascade n m v d (constrainedPairFieldBase n (b • Z ω) u) j x y)
    (F' := fun b ω => constrainedPairFieldCascadeDirection m v d j (b • Z ω) (Z ω) u x y)
    (s := Set.univ) (bound := fun ω => 2 * Fintype.card (Config n) * ‖Z ω‖)
    Filter.univ_mem ?_ (integrable_constrainedPairFieldCascade_amplitude hZ a u m v hm hv d j x y)
    (measurable_constrainedPairFieldCascade_radial hZ a u m v hm hv d j x y).aestronglyMeasurable
    ?_ ((integrable_norm_of_gaussian hZ).const_mul _) ?_).2
  · exact Filter.Eventually.of_forall fun b =>
      ((continuous_constrainedPairFieldCascade_disorder u m v hm hv d j x y).measurable.comp
        (hZ.repr_measurable.const_smul b)).aestronglyMeasurable
  · filter_upwards with ω b _
    rw [Real.norm_eq_abs]
    exact (constrainedPairFieldCascadeD_abs_le (b • Z ω) (Z ω) u m v hm hv d j x y).trans
      (by nlinarith [uAbs_le_card_mul_norm n (Z ω)])
  · filter_upwards with ω b _
    simpa only [zero_add, constrainedPairFieldCascadeDirection] using
      hasDerivAt_constrainedPairFieldCascade 0 (Z ω) u m v hm hv d j x y b

/-- Radial Gaussian integration by parts for the full actual nested cascade. -/
theorem stein_constrainedPairFieldCascade_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, constrainedPairFieldCascadeDirection m v d j (a • Z ω) (Z ω) u x y ∂ℙ) =
      a * ∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond m v d j (a • Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ := by
  classical
  have hi (i : hZ.ι) : Integrable (fun ω => hZ.c i ω *
      constrainedPairFieldCascadeDirection m v d j (a • Z ω) (hZ.w i) u x y) ℙ := by
    have hW := uAbs_nonneg n (hZ.w i)
    apply integrable_coord_mul_comp_of_affine_norm_bound hZ i
      ((continuous_constrainedPairFieldCascadeDirection (hZ.w i) u m v hm hv d j x y).measurable.comp
        (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
      (C := 2 * uAbs n (hZ.w i)) (D := 0) (by positivity) le_rfl
    intro U
    simpa only [zero_mul, add_zero, constrainedPairFieldCascadeDirection, Function.comp_apply] using
      constrainedPairFieldCascadeD_abs_le (a • U) (hZ.w i) u m v hm hv d j x y
  have hH (i : hZ.ι) : Integrable (fun ω =>
      constrainedPairFieldCascadeSecond m v d j (a • Z ω) (hZ.w i) (hZ.w i) u x y) ℙ := by
    have hW := uAbs_nonneg n (hZ.w i)
    apply integrable_comp_of_affine_norm_bound hZ
      ((measurable_constrainedPairFieldCascadeSecond_disorder (hZ.w i) (hZ.w i) u m v hm hv d j x y).comp
        (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
      (C := (8 + 16 * ∑ l ∈ Finset.range j, |m l|) * uAbs n (hZ.w i) * uAbs n (hZ.w i))
      (D := 0) (by positivity) le_rfl
    intro U
    simpa only [zero_mul, add_zero, Function.comp_apply] using
      constrainedPairFieldCascadeSecond_abs_le (a • U) (hZ.w i) (hZ.w i) u m v hm hv d j x y
  simp_rw [constrainedPairFieldCascadeDirection_radial hZ a u m v hm hv d j x y]
  rw [integral_finsetSum _ (fun i _ => hi i),
    integral_finsetSum _ (fun i _ => (hH i).const_mul (hZ.τ i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [stein_constrainedPairFieldCascade_scaled hZ i a (hZ.w i) u m v hm hv d j x y,
    integral_const_mul, integral_const_mul]
  ring

/-- Amplitude derivative after the actual radial Stein contraction. -/
theorem hasDerivAt_constrainedPairGaussian_amplitude_trace {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => ∫ ω, coupledFieldCascade n m v d
      (constrainedPairFieldBase n (b • Z ω) u) j x y ∂ℙ)
      (a * ∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond m v d j (a • Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ) a := by
  rw [← stein_constrainedPairFieldCascade_radial hZ a u m v hm hv d j x y]
  exact hasDerivAt_constrainedPairGaussian_amplitude hZ a u m v hm hv d j x y

/-- The disorder-only pressure at fixed paired-field variances. -/
noncomputable def constrainedDisorderPressure (Z : Ω → EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d j : ℕ) (x y : Fin n → ℝ) (t : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, coupledFieldCascade n m v d
    (constrainedPairFieldBase n (Real.sqrt t • Z ω) u) j x y ∂ℙ

/-- The genuine Gaussian-disorder term of the interpolation derivative, with
the correct `1/(2N)` normalization. No replica-weight identity is assumed. -/
theorem hasDerivAt_constrainedDisorderPressure {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (constrainedDisorderPressure Z u m v d j x y)
      ((1 / (n : ℝ)) * ((∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond m v d j (Real.sqrt t • Z ω)
          (hZ.w i) (hZ.w i) u x y ∂ℙ) / 2)) t := by
  have H := (hasDerivAt_constrainedPairGaussian_amplitude_trace hZ (Real.sqrt t) u m v hm hv d j x y).comp
    t (Real.hasDerivAt_sqrt ht.ne')
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have Hd := H.const_mul (1 / (n : ℝ))
  apply Hd.congr_deriv
  field_simp

/-- The actual fixed-field pressure is continuous even at zero disorder
variance. This follows from the checked amplitude derivative, not an endpoint
variance derivative. -/
theorem continuous_constrainedDisorderPressure {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    Continuous (constrainedDisorderPressure Z u m v d j x y) := by
  have H : Continuous (fun a => ∫ ω, coupledFieldCascade n m v d
      (constrainedPairFieldBase n (a • Z ω) u) j x y ∂ℙ) :=
    (show Differentiable ℝ _ from fun a =>
      (hasDerivAt_constrainedPairGaussian_amplitude hZ a u m v hm hv d j x y).differentiableAt).continuous
  exact (H.comp Real.continuous_sqrt).const_mul (1 / (n : ℝ))

end GaussianDisorder

end SpinGlass.Targets
