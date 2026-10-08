module

/-
# Differentiation through interacting paired Gaussian levels

The independent level is two successive existing one-field transforms (Fubini),
and the shared level is the existing diagonal-shift transform. All masses may
vanish. This file concerns fixed Gaussian variances and a parameter in the
terminal function, not yet the varying-variance interpolation derivative.
-/
public import Targets.ConstrainedFiniteState

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- A normalized one-field tilted mean. -/
noncomputable def pairedTiltMean (m v : ℝ) (A G : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ z, G (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z ∂piGauss n

/-- Bounded observables remain bounded under the normalized tilt; no Lipschitz
assumption on the observable or the potential is needed. -/
theorem pairedTiltMean_abs_le {m v B : ℝ} {A G : (Fin n → ℝ) → ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hB : ∀ y, |G y| ≤ B)
    (x : Fin n → ℝ) : |pairedTiltMean m v A G x| ≤ B := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  have hW : Integrable (tiltWeightPi n m v A x) (piGauss n) := by
    change Integrable (fun z => tiltWeightPi n m v A x z) (piGauss n)
    by_cases hm : m = 0
    · simp only [tiltWeightPi, hm]; exact integrable_const (1 : ℝ)
    · simp only [tiltWeightPi, if_neg hm]
      exact (integrable_exp_shift_pi (m := m) (v := v) hD hb hA.measurable x).div_const _
  have hnorm : ∀ z, |G (fun i => x i + Real.sqrt v * z i) *
      tiltWeightPi n m v A x z| ≤ B * tiltWeightPi n m v A x z := by
    intro z
    rw [abs_mul, abs_of_nonneg (tiltWeightPi_nonneg hD hb hA.measurable x z)]
    exact mul_le_mul_of_nonneg_right (hB _) (tiltWeightPi_nonneg hD hb hA.measurable x z)
  have hi : Integrable (fun z => G (fun i => x i + Real.sqrt v * z i) *
      tiltWeightPi n m v A x z) (piGauss n) :=
    (hW.const_mul B).mono' (((hG.comp (measurable_shift v x)).mul
      (measurable_tiltWeightPi hA.measurable x)).aestronglyMeasurable) (by
        filter_upwards with z; simpa only [Real.norm_eq_abs] using hnorm z)
  calc
    |pairedTiltMean m v A G x| ≤ ∫ z,
        |G (fun i => x i + Real.sqrt v * z i) * tiltWeightPi n m v A x z| ∂piGauss n :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, B * tiltWeightPi n m v A x z ∂piGauss n :=
      integral_mono hi.abs (hW.const_mul B) hnorm
    _ = B := by rw [integral_const_mul, tiltWeightPi_integral_one hD hb hA.measurable x, mul_one]

/-- Tilt in the second field, retaining the first field as a parameter. -/
noncomputable def pairedSecondMean (m v : ℝ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedTiltMean m v (A x) (G x) y

theorem measurable_pairedSecondMean {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 p.2))
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (m v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => pairedSecondMean m v A G p.1 p.2) := by
  have ha : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      A p.1.1 (fun i => p.1.2 i + Real.sqrt v * p.2 i)) :=
    hA.comp (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (p.1.1, fun i => p.1.2 i + Real.sqrt v * p.2 i)) (by fun_prop)
  have hg : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      G p.1.1 (fun i => p.1.2 i + Real.sqrt v * p.2 i)) :=
    hG.comp (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (p.1.1, fun i => p.1.2 i + Real.sqrt v * p.2 i)) (by fun_prop)
  simp only [pairedSecondMean, pairedTiltMean, tiltWeightPi]
  by_cases hm : m = 0
  · simp only [hm, if_true, mul_one]
    exact (hg.stronglyMeasurable.integral_prod_right' (ν := piGauss n)).measurable
  · simp only [if_neg hm, ← mul_div_assoc, integral_div]
    exact ((hg.mul (ha.const_mul m).exp).stronglyMeasurable.integral_prod_right'.measurable).div
      ((ha.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable)

/-- Local uniform analytic hypotheses for a terminal parameter. The derivative
bound is independent of both fields, as for finite-state disorder directions. -/
structure CoupledParamDeriv (A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (s : Set ℝ) (B : ℝ) : Prop where
  deriv : ∀ a ∈ s, ∀ x y, HasDerivAt (fun b => A b x y) (D a x y) a
  measurable : ∀ a ∈ s, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => A a p.1 p.2)
  measurable_deriv : ∀ a ∈ s, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => D a p.1 p.2)
  growth : ∃ C L : ℝ, 0 ≤ L ∧ ∀ a ∈ s, ∀ x y, |A a x y| ≤ C + L * (l1 x + l1 y)
  bound : ∀ a ∈ s, ∀ x y, |D a x y| ≤ B

theorem CoupledParamDeriv.growth_at {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {B : ℝ} (h : CoupledParamDeriv A D s B) {a : ℝ} (ha : a ∈ s) :
    CoupledGrowth (A a) := by
  obtain ⟨C, L, hL, hb⟩ := h.growth
  exact ⟨h.measurable a ha, C, L, hL, hb a ha⟩

theorem CoupledParamDeriv.swap {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {B : ℝ} (h : CoupledParamDeriv A D s B) :
    CoupledParamDeriv (fun a x y => A a y x) (fun a x y => D a y x) s B := by
  obtain ⟨C, L, hL, hb⟩ := h.growth
  refine ⟨fun a ha x y => h.deriv a ha y x,
    fun a ha => (h.measurable a ha).comp measurable_swap,
    fun a ha => (h.measurable_deriv a ha).comp measurable_swap,
    ⟨C, L, hL, ?_⟩, fun a ha x y => h.bound a ha y x⟩
  intro a ha x y; simpa only [add_comm] using hb a ha y x

/-- Differentiation and all hypotheses propagate through smoothing in one field. -/
theorem CoupledParamDeriv.secondStep {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {B m v : ℝ} (h : CoupledParamDeriv A D s B)
    (hs : IsOpen s) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a x y => parisiStepPi n m v (A a x) y)
      (fun a x y => pairedSecondMean m v (A a) (D a) x y) s B := by
  obtain ⟨C, L, hL, hb⟩ := h.growth
  refine ⟨?_, fun a ha => measurable_secondStepPi (h.measurable a ha) m v,
    fun a ha => measurable_pairedSecondMean (h.measurable a ha) (h.measurable_deriv a ha) m v,
    ⟨C + stepK n m v L, L, hL, ?_⟩, ?_⟩
  · intro a ha x y
    exact hasDerivAt_parisiStepPi_param (A := fun a => A a x) (A' := fun a => D a x)
      (C := C + L * l1 x) (D := L) (C' := B) (D' := 0) y (hs.mem_nhds ha) hL le_rfl
      (fun b hb y => h.deriv b hb x y)
      (fun b hb => (h.growth_at hb).section_right x |>.measurable)
      (fun b hb => (h.measurable_deriv b hb).comp (measurable_const.prodMk measurable_id))
      (fun b hbs y => by nlinarith [hb b hbs x y])
      (fun b hb y => by simpa only [zero_mul, add_zero] using h.bound b hb x y)
  · intro a ha x y
    have H := parisiStepPi_abs_le (C := C + L * l1 x) hm hv hL
      (fun z => by nlinarith [hb a ha x z]) (h.growth_at ha |>.section_right x |>.measurable) y
    nlinarith
  · intro a ha x y
    exact pairedTiltMean_abs_le ((h.growth_at ha).section_right x)
      ((h.measurable_deriv a ha).comp (measurable_const.prodMk measurable_id)) (h.bound a ha x) y

/-- Fixed measurable field substitutions preserve terminal-parameter calculus. -/
theorem CoupledParamDeriv.comp_fields
    {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {B K : ℝ}
    (h : CoupledParamDeriv A D s B)
    (f g : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
    (hf : Measurable f) (hg : Measurable g) (hK : 0 ≤ K)
    (hfg : ∀ p, l1 (f p) + l1 (g p) ≤ K * (l1 p.1 + l1 p.2)) :
    CoupledParamDeriv (fun a x y => A a (f (x, y)) (g (x, y)))
      (fun a x y => D a (f (x, y)) (g (x, y))) s B := by
  obtain ⟨C, L, hL, hb⟩ := h.growth
  refine ⟨fun a ha x y => h.deriv a ha _ _,
    fun a ha => (h.measurable a ha).comp (hf.prodMk hg),
    fun a ha => (h.measurable_deriv a ha).comp (hf.prodMk hg),
    ⟨C, L * K, mul_nonneg hL hK, ?_⟩, fun a ha x y => h.bound a ha _ _⟩
  intro a ha x y
  calc
    _ ≤ C + L * (l1 (f (x, y)) + l1 (g (x, y))) := hb a ha _ _
    _ ≤ C + L * K * (l1 x + l1 y) := by nlinarith [hfg (x, y)]

/-- The two successive normalized tilts in an independent level. -/
noncomputable def pairedIndependentMean (m v : ℝ)
    (A D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedTiltMean m v (fun w => parisiStepPi n m v (A w) y)
    (fun w => pairedSecondMean m v A D w y) x

/-- A shared tilt written in coordinates consisting of the field difference
and the second field. Here `m` is the actual log-Laplace mass. -/
noncomputable def pairedSharedMean (m v : ℝ)
    (A D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) : ℝ :=
  pairedSecondMean m v (fun p q => A (p + q) q) (fun p q => D (p + q) q) (x - y) y

theorem sharedStepPi_eq_difference_step (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    sharedStepPi n (2 * m) v A x y =
      parisiStepPi n m v (fun z => A (x - y + z) z) y := by
  have he : ∀ z : Fin n → ℝ,
      x - y + (fun i => y i + Real.sqrt v * z i) = x + (fun i => Real.sqrt v * z i) := by
    intro z; ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [sharedStepPi, parisiStepPi, show 2 * m / 2 = m by ring,
    Pi.zero_apply, zero_add, he, Pi.add_def]

/-- Actual independent steps preserve local derivative regularity; the
interacting partition function is not assumed to factor between replicas. -/
theorem CoupledParamDeriv.independentStep
    {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {B m v : ℝ}
    (h : CoupledParamDeriv A D s B) (hs : IsOpen s) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a => independentStepPi n m v (A a))
      (fun a => pairedIndependentMean m v (A a) (D a)) s B := by
  have H := ((h.secondStep hs hm hv).swap.secondStep hs hm hv).swap
  have he : ∀ a ∈ s, ∀ x y, independentStepPi n m v (A a) x y =
      parisiStepPi n m v (fun w => parisiStepPi n m v (A a w) y) x :=
    fun a ha => independentStepPi_eq_nested m v (h.growth_at ha)
  refine ⟨?_, ?_, H.measurable_deriv, ?_, H.bound⟩
  · intro a ha x y
    apply (H.deriv a ha x y).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds ha] with b hb
    exact he b hb x y
  · intro a ha
    exact (h.growth_at ha |>.independentStep hm hv).measurable
  · obtain ⟨C, L, hL, hb⟩ := H.growth
    exact ⟨C, L, hL, fun a ha x y => by rw [he a ha x y]; exact hb a ha x y⟩

/-- Actual shared steps preserve local derivative regularity, at the actual
mass `m` (the legacy shared-step API takes `2*m`). -/
theorem CoupledParamDeriv.sharedStep
    {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {B m v : ℝ}
    (h : CoupledParamDeriv A D s B) (hs : IsOpen s) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a => sharedStepPi n (2 * m) v (A a))
      (fun a => pairedSharedMean m v (A a) (D a)) s B := by
  have H := h.comp_fields (fun p => p.1 + p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_add_le p.1 p.2, l1_nonneg p.1])
  have H' := (H.secondStep hs hm hv).comp_fields (fun p => p.1 - p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_sub_le p.1 p.2, l1_nonneg p.1])
  change CoupledParamDeriv (fun a x y => sharedStepPi n (2 * m) v (A a) x y)
    (fun a x y => pairedSharedMean m v (A a) (D a) x y) s B
  simpa only [sharedStepPi_eq_difference_step, pairedSharedMean] using H'

/-- The actual nested first derivative: each level applies its normalized tilt
to the previous derivative. -/
noncomputable def coupledFieldCascadeD (m v : ℕ → ℝ) (d : ℕ)
    (A D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => D
  | j + 1 => if j < d then
      pairedIndependentMean (m j) (v j) (coupledFieldCascade n m v d A j)
        (coupledFieldCascadeD m v d A D j)
    else pairedSharedMean (m j) (v j) (coupledFieldCascade n m v d A j)
      (coupledFieldCascadeD m v d A D j)

/-- Local regularity and the same uniform first-derivative bound persist through
every level of the actual interacting coupled cascade. -/
theorem CoupledParamDeriv.fieldCascade
    {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {B : ℝ}
    (h : CoupledParamDeriv A D s B) (hs : IsOpen s)
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    CoupledParamDeriv (fun a => coupledFieldCascade n m v d (A a) j)
      (fun a => coupledFieldCascadeD m v d (A a) (D a) j) s B := by
  induction j with
  | zero => exact h
  | succ j ih =>
    simp only [coupledFieldCascade, coupledFieldCascadeD]
    split_ifs
    · exact ih.independentStep hs (hm j) (hv j)
    · exact ih.sharedStep hs (hm j) (hv j)

/-- The finite-state first derivative at the constrained terminal. -/
noncomputable def constrainedPairDirection (U V : EnergySpace n) (u : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ p : AT.ConstrainedPair n u,
    constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)

theorem measurable_constrainedPairDirection (U V : EnergySpace n) (u : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => constrainedPairDirection U V u p.1 p.2) := by
  classical
  unfold constrainedPairDirection constrainedPairGibbs AT.gtStateGibbs AT.gtStatePartition
    pairFieldPotential
  fun_prop

theorem constrainedPairDirection_abs_le (U V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    |constrainedPairDirection U V u x y| ≤ 2 * uAbs n V := by
  classical
  have hb (p : AT.ConstrainedPair n u) : |V p.1.1 + V p.1.2| ≤ 2 * uAbs n V := by
    exact (abs_add_le _ _).trans (by linarith [abs_le_uAbs n V p.1.1, abs_le_uAbs n V p.1.2])
  calc
    |constrainedPairDirection U V u x y| ≤ ∑ p : AT.ConstrainedPair n u,
        |constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p * (2 * uAbs n V) := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
      exact mul_le_mul_of_nonneg_left (hb p) (constrainedPairGibbs_nonneg n U u x y p)
    _ = 2 * uAbs n V := by rw [← Finset.sum_mul, sum_constrainedPairGibbs, one_mul]

/-- Uniform field growth along bounded disorder lines is obtained by comparing
with the already constructed disorder-free constrained terminal. -/
theorem constrainedPairFieldBase_dist_zero (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    |constrainedPairFieldBase n U u x y - constrainedPairFieldBase n 0 u x y| ≤ 2 * uAbs n U := by
  classical
  simp only [constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
    AT.gtStatePartition]
  apply abs_log_sum_exp_sub_le_on Finset.univ Finset.univ_nonempty
  intro p _
  simp only [map_zero, PiLp.zero_apply, pairDisorderCLM_apply, add_sub_add_right_eq_sub,
    sub_zero]
  exact (abs_add_le _ _).trans (by linarith [abs_le_uAbs n U p.1.1, abs_le_uAbs n U p.1.2])

/-- The analytic hypotheses are discharged for the actual terminal, not assumed.
The same derivative bound is uniform in the disorder-line parameter and fields. -/
theorem constrainedPairFieldBase_paramDeriv (U V : EnergySpace n) (u r : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] :
    CoupledParamDeriv (fun a => constrainedPairFieldBase n (U + a • V) u)
      (fun a => constrainedPairDirection (U + a • V) V u) (guerraLineNbhd r) (2 * uAbs n V) := by
  classical
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have hzero := constrainedBase_growth (0 : EnergySpace n) 0 u
    (t := 0) (by constructor <;> norm_num) ⟨p.1.1, p.1.2, p.2⟩
  obtain ⟨C, L, hL, hb⟩ := hzero.bound
  refine ⟨fun a _ x y => hasDerivAt_constrainedPairFieldBase n u U V x y a,
    ?_, fun a _ => measurable_constrainedPairDirection _ _ _,
    ⟨C + 2 * (uAbs n U + (|r| + 1) * uAbs n V), L, hL, ?_⟩,
    fun a _ x y => constrainedPairDirection_abs_le _ _ _ x y⟩
  · intro a _
    simp only [constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
      AT.gtStatePartition, pairFieldPotential]
    fun_prop
  · intro a ha x y
    have hz := hb x y
    rw [← constrainedPairFieldBase_zero] at hz
    have hd := constrainedPairFieldBase_dist_zero (U + a • V) u x y
    have hU := uAbs_add_smul_le n U V a
    have ha' := mul_le_mul_of_nonneg_right (abs_le_abs_add_one_of_mem_guerraLineNbhd ha)
      (uAbs_nonneg n V)
    have habs := abs_add_le
      (constrainedPairFieldBase n (U + a • V) u x y - constrainedPairFieldBase n 0 u x y)
      (constrainedPairFieldBase n 0 u x y)
    rw [sub_add_cancel] at habs
    linarith

/-- Actual first disorder derivative at every depth of the interacting paired
cascade, for arbitrary nonnegative masses and fixed variances. -/
theorem hasDerivAt_constrainedPairFieldCascade (U V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => coupledFieldCascade n m v d (constrainedPairFieldBase n (U + b • V) u) j x y)
      (coupledFieldCascadeD m v d (constrainedPairFieldBase n (U + a • V) u)
        (constrainedPairDirection (U + a • V) V u) j x y) a := by
  exact ((constrainedPairFieldBase_paramDeriv U V u a).fieldCascade
    isOpen_Ioo m v hm hv d j).deriv a ⟨by linarith, by linarith⟩ x y

/-- The actual recursively tilted first disorder derivative has no depth loss. -/
theorem constrainedPairFieldCascadeD_abs_le (U V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (x y : Fin n → ℝ) :
    |coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
      (constrainedPairDirection U V u) j x y| ≤ 2 * uAbs n V := by
  have H := ((constrainedPairFieldBase_paramDeriv U V u 0).fieldCascade
    isOpen_Ioo m v hm hv d j).bound 0 ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [zero_smul, add_zero] using H

/-- The second-field tilted-observable derivative has the exact mass covariance
term. It is the mixed second-derivative rule when `G` is another first direction. -/
theorem hasDerivAt_pairedSecondMean
    {A A' G G' : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BA BG BG' m v a : ℝ}
    (hA : CoupledParamDeriv A A' s BA) (hG : CoupledParamDeriv G G' s BG')
    (hGB : ∀ b ∈ s, ∀ x y, |G b x y| ≤ BG) (hs : s ∈ 𝓝 a)
    (x y : Fin n → ℝ) :
    HasDerivAt (fun b => pairedSecondMean m v (A b) (G b) x y)
      (pairedSecondMean m v (A a) (fun x y => G' a x y + m * G a x y * A' a x y) x y -
        m * pairedSecondMean m v (A a) (G a) x y * pairedSecondMean m v (A a) (A' a) x y) a := by
  obtain ⟨C, L, hL, hb⟩ := hA.growth
  exact hasDerivAt_tiltAvg_param_pi (A := fun b => A b x) (A' := fun b => A' b x)
    (G := fun b => G b x) (G' := fun b => G' b x)
    (C := C + L * l1 x) (D := L) y hs hL
    (fun b hb y => hA.deriv b hb x y) (fun b hb y => hG.deriv b hb x y)
    (fun b hb => (hA.measurable b hb).comp (measurable_const.prodMk measurable_id))
    (fun b hb => (hA.measurable_deriv b hb).comp (measurable_const.prodMk measurable_id))
    (fun b hb => (hG.measurable b hb).comp (measurable_const.prodMk measurable_id))
    (fun b hb => (hG.measurable_deriv b hb).comp (measurable_const.prodMk measurable_id))
    (fun b hbs y => by nlinarith [hb b hbs x y])
    (fun b hb => hA.bound b hb x) (fun b hb => hGB b hb x) (fun b hb => hG.bound b hb x)

/-- The shared-step covariance coefficient is the actual mass `m`, not `m/2`:
the legacy API's halving has already been accounted for. -/
theorem hasDerivAt_pairedSharedMean
    {A A' G G' : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {s : Set ℝ} {BA BG BG' m v a : ℝ}
    (hA : CoupledParamDeriv A A' s BA) (hG : CoupledParamDeriv G G' s BG')
    (hGB : ∀ b ∈ s, ∀ x y, |G b x y| ≤ BG) (hs : s ∈ 𝓝 a)
    (x y : Fin n → ℝ) :
    HasDerivAt (fun b => pairedSharedMean m v (A b) (G b) x y)
      (pairedSharedMean m v (A a) (fun x y => G' a x y + m * G a x y * A' a x y) x y -
        m * pairedSharedMean m v (A a) (G a) x y * pairedSharedMean m v (A a) (A' a) x y) a := by
  have H := hA.comp_fields (fun p => p.1 + p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_add_le p.1 p.2, l1_nonneg p.1])
  have H' := hG.comp_fields (fun p => p.1 + p.2) (fun p => p.2)
    (by fun_prop) measurable_snd (K := 2) (by norm_num)
    (fun p => by nlinarith [l1_add_le p.1 p.2, l1_nonneg p.1])
  exact hasDerivAt_pairedSecondMean H H' (fun b hb x y => hGB b hb _ _) hs (x - y) y

/-- The terminal mixed Hessian is bounded uniformly in the disorder and fields.
This elementary finite-state bound is sufficient for differentiating a tilt. -/
theorem constrainedPairSecond_abs_le (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    |constrainedPairSecond n u U V W x y| ≤ 8 * uAbs n V * uAbs n W := by
  classical
  have hdir (Z : EnergySpace n) (p : AT.ConstrainedPair n u) :
      |Z p.1.1 + Z p.1.2| ≤ 2 * uAbs n Z :=
    (abs_add_le _ _).trans (by linarith [abs_le_uAbs n Z p.1.1, abs_le_uAbs n Z p.1.2])
  have hmoment : |∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
      (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2)| ≤ (2 * uAbs n V) * (2 * uAbs n W) := by
    calc
      _ ≤ ∑ p : AT.ConstrainedPair n u, |constrainedPairGibbs n U u x y p *
          (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : AT.ConstrainedPair n u,
          constrainedPairGibbs n U u x y p * ((2 * uAbs n V) * (2 * uAbs n W)) := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul, abs_mul, abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hdir V p) (hdir W p) (abs_nonneg _)
            (mul_nonneg (by norm_num) (uAbs_nonneg n V)))
          (constrainedPairGibbs_nonneg n U u x y p)
      _ = _ := by rw [← Finset.sum_mul, sum_constrainedPairGibbs, one_mul]
  have hprod : |constrainedPairDirection U V u x y * constrainedPairDirection U W u x y| ≤
      (2 * uAbs n V) * (2 * uAbs n W) := by
    rw [abs_mul]
    exact mul_le_mul (constrainedPairDirection_abs_le U V u x y)
      (constrainedPairDirection_abs_le U W u x y) (abs_nonneg _)
      (mul_nonneg (by norm_num) (uAbs_nonneg n V))
  rw [constrainedPairSecond_eq_covariance]
  calc
    _ ≤ |∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
        (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2)| +
        |constrainedPairDirection U V u x y * constrainedPairDirection U W u x y| := by
          simpa only [sub_eq_add_neg, abs_neg, constrainedPairDirection] using! abs_add_le
            (∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
              (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2))
            (-(constrainedPairDirection U V u x y * constrainedPairDirection U W u x y))
    _ ≤ (2 * uAbs n V) * (2 * uAbs n W) + (2 * uAbs n V) * (2 * uAbs n W) :=
      add_le_add hmoment hprod
    _ = _ := by ring

/-- Actual terminal first directions themselves satisfy the local analytic
hypotheses, with their actual mixed Hessian as derivative. -/
theorem constrainedPairDirection_paramDeriv (U V W : EnergySpace n) (u r : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] :
    CoupledParamDeriv (fun a => constrainedPairDirection (U + a • W) V u)
      (fun a => constrainedPairSecond n u (U + a • W) V W)
      (guerraLineNbhd r) (8 * uAbs n V * uAbs n W) := by
  refine ⟨?_, fun a _ => measurable_constrainedPairDirection _ _ _, ?_,
    ⟨2 * uAbs n V, 0, le_rfl, ?_⟩, fun a _ x y => constrainedPairSecond_abs_le _ _ _ _ x y⟩
  · intro a _ x y
    simpa only [constrainedPairDirection, constrainedPairSecond_eq_covariance] using
      hasDerivAt_constrainedPairMean n u U W x y (fun p => V p.1.1 + V p.1.2) a
  · intro a _
    simp only [constrainedPairSecond_eq_covariance]
    unfold constrainedPairGibbs AT.gtStateGibbs AT.gtStatePartition pairFieldPotential
    fun_prop
  · intro a _ x y
    simpa only [zero_mul, add_zero] using constrainedPairDirection_abs_le (U + a • W) V u x y

/-- Actual mixed disorder derivative after one shared Gaussian level. The
terminal Hessian and the mass covariance term both occur with their exact signs.
The formula includes mass zero, and does not assume the desired Hessian identity. -/
theorem hasDerivAt_sharedConstrainedPair_second (U V W : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => sharedStepPi n (2 * m) v
        (constrainedPairFieldBase n (U + a • W + b • V) u) x y) 0)
      (pairedSharedMean m v (constrainedPairFieldBase n U u)
          (fun x y => constrainedPairSecond n u U V W x y +
            m * constrainedPairDirection U V u x y * constrainedPairDirection U W u x y) x y -
        m * pairedSharedMean m v (constrainedPairFieldBase n U u) (constrainedPairDirection U V u) x y *
          pairedSharedMean m v (constrainedPairFieldBase n U u) (constrainedPairDirection U W u) x y) 0 := by
  have he (a : ℝ) := (((constrainedPairFieldBase_paramDeriv (U + a • W) V u 0).sharedStep
    isOpen_Ioo hm hv).deriv 0 ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y).deriv
  simp only [zero_smul, add_zero] at he
  simp only [he]
  simpa only [zero_smul, add_zero] using hasDerivAt_pairedSharedMean
    (constrainedPairFieldBase_paramDeriv U W u 0) (constrainedPairDirection_paramDeriv U V W u 0)
    (fun a _ x y => constrainedPairDirection_abs_le (U + a • W) V u x y)
    (guerraLineNbhd_mem_nhds 0) x y

end SpinGlass.Targets
