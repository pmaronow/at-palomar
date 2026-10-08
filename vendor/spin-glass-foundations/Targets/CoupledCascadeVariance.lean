module

/-
# Gaussian variance calculus for actual paired cascades

The inner constrained cascade is fixed. We differentiate a genuine additional
Gaussian level, using the proved spatial derivatives and Gaussian Stein.
-/
public import Targets.CoupledCascadeField

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem integrable_pairedTiltMean {A G : (Fin n → ℝ) → ℝ} {B m v : ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hb : ∀ y, |G y| ≤ B)
    (x : Fin n → ℝ) :
    Integrable (fun z => G (fun i => x i + Real.sqrt v * z i) *
      tiltWeightPi n m v A x z) (piGauss n) := by
  obtain ⟨C, D, hD, hAb⟩ := hA.bound
  have hW : Integrable (fun z => tiltWeightPi n m v A x z) (piGauss n) := by
    rw [show (fun z => tiltWeightPi n m v A x z) = fun z =>
      Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) /
        ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂piGauss n by
          funext z; exact tiltWeightPi_eq_exp_div m v A x z]
    exact (integrable_exp_shift_pi hD hAb hA.measurable x).div_const _
  refine (hW.const_mul B).mono'
    (((hG.comp (measurable_shift v x)).mul (measurable_tiltWeightPi hA.measurable x)).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tiltWeightPi_nonneg hD hAb hA.measurable x z)]
  exact mul_le_mul_of_nonneg_right (hb _) (tiltWeightPi_nonneg hD hAb hA.measurable x z)

theorem pairedTiltMean_sum {ι : Type*} [Fintype ι]
    {A : (Fin n → ℝ) → ℝ} {G : ι → (Fin n → ℝ) → ℝ} {B : ι → ℝ}
    (hA : GuerraGrowth A) (hG : ∀ i, Measurable (G i))
    (hb : ∀ i y, |G i y| ≤ B i) (c : ι → ℝ) (m v : ℝ) (x : Fin n → ℝ) :
    pairedTiltMean m v A (fun y => ∑ i, c i * G i y) x =
      ∑ i, c i * pairedTiltMean m v A (G i) x := by
  classical
  simp only [pairedTiltMean, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (integrable_pairedTiltMean hA (hG i) (hb i) x).const_mul (c i))]
  simp only [integral_const_mul]

theorem pairedIndependentMean_sum {ι : Type*} [Fintype ι]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : ι → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ι → ℝ}
    (hA : CoupledGrowth A)
    (hG : ∀ i, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G i p.1 p.2))
    (hb : ∀ i x y, |G i x y| ≤ B i) (c : ι → ℝ) {m v : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ v) (x y : Fin n → ℝ) :
    pairedIndependentMean m v A (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * pairedIndependentMean m v A (G i) x y := by
  classical
  have hinner (w : Fin n → ℝ) :
      pairedSecondMean m v A (fun x y => ∑ i, c i * G i x y) w y =
        ∑ i, c i * pairedSecondMean m v A (G i) w y :=
    pairedTiltMean_sum (hA.section_right w)
      (fun i => (hG i).comp (measurable_const.prodMk measurable_id)) (fun i => hb i w) c m v y
  have houter : GuerraGrowth (fun w => parisiStepPi n m v (A w) y) := by
    obtain ⟨C, D, hD, hAb⟩ := hA.bound
    refine ⟨(measurable_secondStepPi hA.measurable m v).comp
      (measurable_id.prodMk measurable_const), C + D * l1 y + stepK n m v D, D, hD, ?_⟩
    intro w
    have H := parisiStepPi_abs_le (C := C + D * l1 w) hm hv hD
      (fun z => by nlinarith [hAb w z]) (hA.section_right w).measurable y
    nlinarith
  simp only [pairedIndependentMean, hinner]
  exact pairedTiltMean_sum houter
    (fun i => (measurable_pairedSecondMean hA.measurable (hG i) m v).comp
      (measurable_id.prodMk measurable_const))
    (fun i w => pairedTiltMean_abs_le (hA.section_right w)
      ((hG i).comp (measurable_const.prodMk measurable_id)) (hb i w) y) c m v x

theorem pairedSharedMean_sum {ι : Type*} [Fintype ι]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : ι → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ι → ℝ}
    (hA : CoupledGrowth A)
    (hG : ∀ i, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G i p.1 p.2))
    (hb : ∀ i x y, |G i x y| ≤ B i) (c : ι → ℝ) (m v : ℝ) (x y : Fin n → ℝ) :
    pairedSharedMean m v A (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * pairedSharedMean m v A (G i) x y := by
  obtain ⟨C, D, hD, hAb⟩ := hA.bound
  have hg : GuerraGrowth (fun z => A (x - y + z) z) := by
    refine ⟨hA.measurable.comp (f := fun z => (x - y + z, z)) (by fun_prop),
      C + D * l1 (x - y), 2 * D, by positivity, ?_⟩
    intro z
    nlinarith [hAb (x - y + z) z, l1_add_le (x - y) z]
  exact pairedTiltMean_sum hg (fun i => (hG i).comp
    (f := fun z => (x - y + z, z)) (by fun_prop))
    (fun i z => hb i (x - y + z) z) c m v y

theorem constrainedPairFieldDirection_sum {ι : Type*} [Fintype ι]
    (U : EnergySpace n) (u : ℝ) (c : ι → ℝ) (A B : ι → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    constrainedPairFieldDirection U u (∑ i, c i • A i) (∑ i, c i • B i) x y =
      ∑ i, c i * constrainedPairFieldDirection U u (A i) (B i) x y := by
  classical
  have hpot (p : AT.ConstrainedPair n u) :
      pairFieldPotential n u (∑ i, c i • A i) (∑ i, c i • B i) p =
        ∑ i, c i * pairFieldPotential n u (A i) (B i) p := by
    simp only [pairFieldPotential, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j i => spin n p.1.1 j * (c i * A i j)),
      Finset.sum_comm (f := fun j i => spin n p.1.2 j * (c i * B i j))]
    simp only [mul_left_comm]
  simp only [constrainedPairFieldDirection, hpot, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem constrainedPairFieldCascade_growth (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    CoupledGrowth (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 0 0).fieldCascade
    isOpen_Ioo m v hm hv d j).growth_at
      (a := 0) ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [zero_smul, add_zero] using H

/-- Linearity of the actual propagated spatial derivative, including all
normalizing denominators in the paired Gaussian recursion. -/
theorem constrainedPairCascadeSpatialFirst_sum {ι : Type*} [Fintype ι]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (c : ι → ℝ) (A B : ι → Fin n → ℝ) (x y : Fin n → ℝ) :
    constrainedPairCascadeSpatialFirst m v d j U u (∑ i, c i • A i) (∑ i, c i • B i) x y =
      ∑ i, c i * constrainedPairCascadeSpatialFirst m v d j U u (A i) (B i) x y := by
  classical
  simp only [constrainedPairCascadeSpatialFirst_eq U u m v hm hv d]
  induction j generalizing x y with
  | zero => exact constrainedPairFieldDirection_sum U u c A B x y
  | succ j ih =>
    have hg (i : ι) := measurable_constrainedPairCascadeSpatialFirst U u m v hm hv d j (A i) (B i)
    have hb (i : ι) := constrainedPairCascadeSpatialFirst_abs_le U u m v hm hv d j (A i) (B i)
    simp only [constrainedPairCascadeSpatialFirst_eq U u m v hm hv d] at hg hb
    simp only [coupledFieldCascadeD]
    split_ifs
    · rw [show coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u (∑ i, c i • A i) (∑ i, c i • B i)) j =
          fun x y => ∑ i, c i * coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
            (constrainedPairFieldDirection U u (A i) (B i)) j x y from funext fun x => funext fun y => ih x y]
      exact pairedIndependentMean_sum (constrainedPairFieldCascade_growth U u m v hm hv d j)
        hg hb c (hm j) (hv j) x y
    · rw [show coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u (∑ i, c i • A i) (∑ i, c i • B i)) j =
          fun x y => ∑ i, c i * coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
            (constrainedPairFieldDirection U u (A i) (B i)) j x y from funext fun x => funext fun y => ih x y]
      exact pairedSharedMean_sum (constrainedPairFieldCascade_growth U u m v hm hv d j)
        hg hb c (m j) (v j) x y

/-- The previously proved point-zero spatial derivative, transported to an
arbitrary point on the same physical field line. -/
theorem hasDerivAt_constrainedPairCascadeSpatialLine (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun a : ℝ => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
      (x + a • A) (y + a • B))
      (constrainedPairCascadeSpatialFirst m v d j U u A B (x + r • A) (y + r • B)) r := by
  have H := hasDerivAt_constrainedPairFieldCascade_field U u m v hm hv d j A B
    (x + r • A) (y + r • B)
  rw [← constrainedPairCascadeSpatialFirst_eq U u m v hm hv d j] at H
  have H' := HasDerivAt.comp_sub_const r r (by simpa only [sub_self] using H)
  apply H'.congr_of_eventuallyEq
  filter_upwards with a
  congr 1 <;> simp only [sub_smul] <;> abel

theorem hasDerivAt_constrainedPairCascadeSpatialFirst_line (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B C D x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun a : ℝ => constrainedPairCascadeSpatialFirst m v d j U u A B
      (x + a • C) (y + a • D))
      (constrainedPairCascadeSpatialSecond m v d j U u A B C D
        (x + r • C) (y + r • D)) r := by
  have H := hasDerivAt_constrainedPairFieldCascade_field_second U u m v hm hv d j A B C D
    (x + r • C) (y + r • D)
  rw [← constrainedPairCascadeSpatialSecond_eq U u m v hm hv d j] at H
  change HasDerivAt (fun a : ℝ => constrainedPairCascadeSpatialFirst m v d j U u A B
    (x + r • C + a • C) (y + r • D + a • D)) _ 0 at H
  have H' := HasDerivAt.comp_sub_const r r (by simpa only [sub_self] using H)
  apply H'.congr_of_eventuallyEq
  filter_upwards with a
  congr 1 <;> simp only [sub_smul] <;> abel

theorem abs_sum_coord_mul_le {F : Fin n → (Fin n → ℝ) → ℝ} {B : ℝ}
    (hb : ∀ i y, |F i y| ≤ B) (x z : Fin n → ℝ) :
    |∑ i, z i * F i x| ≤ B * l1 z := by
  calc
    _ ≤ ∑ i, |z i * F i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |z i| * B := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i x) (abs_nonneg _)
    _ = B * l1 z := by rw [← Finset.sum_mul]; ring

/-- Heat generator of a genuine N-dimensional log-Laplace transform. Its
hypotheses are spatial regularity and growth, not a variance derivative. -/
theorem hasDerivAt_parisiStepPi_variance
    {A : (Fin n → ℝ) → ℝ} {A' A'' : Fin n → (Fin n → ℝ) → ℝ}
    {C D B H : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hAm : Measurable A) (hA'm : ∀ i, Measurable (A' i)) (hA''m : ∀ i, Measurable (A'' i))
    (hb : ∀ y, |A y| ≤ C + D * l1 y)
    (hb' : ∀ i y, |A' i y| ≤ B) (hb'' : ∀ i y, |A'' i y| ≤ H)
    (hline : ∀ (x z : Fin n → ℝ) (a : ℝ),
      HasDerivAt (fun b => A (x + b • z)) (∑ i, z i * A' i (x + a • z)) a)
    (hsecond : ∀ (i : Fin n) (y : Fin n → ℝ) (a : ℝ),
      HasDerivAt (fun b => A' i (y + b • Pi.single i 1))
        (A'' i (y + a • Pi.single i 1)) a)
    (m : ℝ) (x : Fin n → ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => parisiStepPi n m w A x)
      ((∑ i, pairedTiltMean m v A (fun y => A'' i y + m * (A' i y) ^ 2) x) / 2) v := by
  classical
  have hLip (y y' : Fin n → ℝ) : |A y - A y'| ≤ B * l1 (y - y') := by
    have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun a _ => (hline y' (y - y') a).hasDerivWithinAt)
      (C := B * l1 (y - y')) (fun a _ => ?_)
    · simpa only [zero_smul, one_smul, add_zero, add_sub_cancel, Real.norm_eq_abs] using H
    · simpa only [Real.norm_eq_abs] using abs_sum_coord_mul_le hb' (y' + a • (y - y')) (y - y')
  let F : ℝ → (Fin n → ℝ) → ℝ := fun a z => A (x + a • z)
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun a z => ∑ i, z i * A' i (x + a • z)
  have hd := hasDerivAt_parisiStepPi_param (A := F) (A' := F') (m := m) (v := 1)
    (C := C + D * l1 x) (D := D * (|Real.sqrt v| + 1)) (C' := 0) (D' := B)
    (x := 0) (u₀ := Real.sqrt v) (s := guerraLineNbhd (Real.sqrt v))
    (isOpen_Ioo.mem_nhds ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩)
    (by positivity) hB (fun a _ z => hline x z a)
    (fun a _ => hAm.comp (f := fun z => x + a • z) (by fun_prop))
    (fun a _ => Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul
      ((hA'm i).comp (f := fun z => x + a • z) (by fun_prop)))
    (fun a ha z => by
      have hza : l1 (a • z) = |a| * l1 z := l1_const_smul a z
      have ha' := abs_le_abs_add_one_of_mem_guerraLineNbhd ha
      have hh := l1_add_le x (a • z)
      rw [hza] at hh
      have h1 := mul_le_mul_of_nonneg_right ha' (l1_nonneg z)
      dsimp only [F]
      nlinarith [hb (x + a • z)])
    (fun a _ z => by simpa only [zero_add] using abs_sum_coord_mul_le hb' (x + a • z) z)
  have hweight (z : Fin n → ℝ) : tiltWeightPi n m 1 (F (Real.sqrt v)) 0 z =
      tiltWeightPi n m v A x z := by
    simp only [tiltWeightPi, F, Real.sqrt_one, Pi.zero_apply, one_mul, zero_add,
      Pi.add_def, Pi.smul_def, smul_eq_mul]
  have hdv := hd.comp v (Real.hasDerivAt_sqrt hv.ne')
  have hfun : (fun w => parisiStepPi n m 1 (F (Real.sqrt w)) 0) =
      fun w => parisiStepPi n m w A x := by
    funext w
    simp only [parisiStepPi, F, Real.sqrt_one, Pi.zero_apply, zero_add, one_mul,
      Pi.add_def, Pi.smul_def, smul_eq_mul]
  simp only [Function.comp_def, hfun, F', Real.sqrt_one, Pi.zero_apply, one_mul, zero_add,
    hweight] at hdv
  have hStein (i : Fin n) := stein_tiltWeightPi (A := A) (A' := A' i) (G := A' i) (G' := A'' i)
    (m := m) (v := v) i x hD hB hAm (hA'm i) (hA'm i) (hA''m i) hb hLip
    (hb' i) (hb' i) (hb'' i) (fun y a => by
      simpa [Pi.single_apply] using hline y (Pi.single i 1) a) (hsecond i)
  have hi (i : Fin n) : Integrable (fun z => z i *
      (A' i (fun l => x l + Real.sqrt v * z l) * tiltWeightPi n m v A x z)) (piGauss n) :=
    integrable_coord_mul_tiltWeightPi i x hD hB hAm (hA'm i) hb hLip (hb' i)
  apply hdv.congr_deriv
  simp only [Finset.sum_mul, mul_assoc, Pi.add_def, Pi.smul_def, smul_eq_mul]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hStein]
  rw [← Finset.mul_sum]
  simp only [pairedTiltMean]
  have he : ∀ i, (fun z : Fin n → ℝ =>
      (A'' i (fun l => x l + Real.sqrt v * z l) +
        m * A' i (fun l => x l + Real.sqrt v * z l) * A' i (fun l => x l + Real.sqrt v * z l)) *
        tiltWeightPi n m v A x z) =
      (fun z => (A'' i (fun l => x l + Real.sqrt v * z l) +
        m * (A' i (fun l => x l + Real.sqrt v * z l)) ^ 2) * tiltWeightPi n m v A x z) := by
    intro i; funext z; ring
  simp only [he]
  field_simp

/-- A fixed finite family of physical field directions, driven by independent
standard Gaussian coordinates. It includes separate and shared replica fields. -/
noncomputable def pairedFieldLinear {p : ℕ} (A : Fin p → Fin n → ℝ) (z : Fin p → ℝ) :
    Fin n → ℝ := ∑ i, z i • A i

theorem measurable_pairedFieldLinear {p : ℕ} (A : Fin p → Fin n → ℝ) :
    Measurable (pairedFieldLinear A) := by
  unfold pairedFieldLinear
  fun_prop

theorem pairedFieldLinear_add_smul {p : ℕ} (A : Fin p → Fin n → ℝ)
    (z w : Fin p → ℝ) (a : ℝ) :
    pairedFieldLinear A (z + a • w) = pairedFieldLinear A z + a • pairedFieldLinear A w := by
  simp only [pairedFieldLinear, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

@[simp] theorem pairedFieldLinear_single {p : ℕ} (A : Fin p → Fin n → ℝ) (i : Fin p) :
    pairedFieldLinear A (Pi.single i 1) = A i := by
  classical
  simp [pairedFieldLinear, Pi.single_apply]

theorem l1_pairedFieldLinear_le {p : ℕ} (A : Fin p → Fin n → ℝ) (z : Fin p → ℝ) :
    l1 (pairedFieldLinear A z) ≤ (∑ i, l1 (A i)) * l1 z := by
  classical
  calc
    _ ≤ ∑ l : Fin n, ∑ i : Fin p, |z i * A i l| := by
      apply Finset.sum_le_sum
      intro l _
      simpa only [pairedFieldLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun i : Fin p => z i * A i l)
    _ = ∑ i : Fin p, |z i| * l1 (A i) := by
      rw [Finset.sum_comm]
      simp only [l1, abs_mul, Finset.mul_sum]
    _ ≤ ∑ i : Fin p, l1 z * l1 (A i) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => abs_nonneg (z l)) (Finset.mem_univ i)) (l1_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Positive-variance heat formula for a genuine fixed inner constrained
cascade and arbitrary finite Gaussian field directions. Every analytic
hypothesis of the N-site heat generator is discharged here. -/
theorem hasDerivAt_constrainedPairField_linear_variance {p : ℕ}
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ)
    (mass : ℝ) {variance : ℝ} (hvar : 0 < variance) :
    let F := fun z : Fin p → ℝ => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
      (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)
    HasDerivAt (fun w => parisiStepPi p mass w F 0)
      ((∑ i : Fin p, pairedTiltMean mass variance F (fun z =>
        constrainedPairCascadeSpatialSecond m v d j U u (A i) (B i) (A i) (B i)
          (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) +
        mass * (constrainedPairCascadeSpatialFirst m v d j U u (A i) (B i)
          (x + pairedFieldLinear A z) (y + pairedFieldLinear B z)) ^ 2) 0) / 2) variance := by
  classical
  dsimp only
  let L := ∑ i : Fin p, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hLi (i : Fin p) : l1 (A i) + l1 (B i) ≤ L :=
    Finset.single_le_sum (fun l _ => add_nonneg (l1_nonneg _) (l1_nonneg _)) (Finset.mem_univ i)
  let K := 2 + 4 * ∑ l ∈ Finset.range j, |m l|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg := constrainedPairFieldCascade_growth U u m v hm hv d j
  obtain ⟨C, D, hD, hb⟩ := hg.bound
  have hmap : Measurable (fun z : Fin p → ℝ =>
      (x + pairedFieldLinear A z, y + pairedFieldLinear B z)) :=
    (measurable_const.add (measurable_pairedFieldLinear A)).prodMk
      (measurable_const.add (measurable_pairedFieldLinear B))
  apply hasDerivAt_parisiStepPi_variance (C := C + D * (l1 x + l1 y)) (D := D * L)
    (B := L) (H := K * L * L) (mul_nonneg hD hL) hL
    (hg.measurable.comp hmap)
    (fun i => (measurable_constrainedPairCascadeSpatialFirst U u m v hm hv d j (A i) (B i)).comp hmap)
    (fun i => (measurable_constrainedPairCascadeSpatialSecond U u m v hm hv d j (A i) (B i) (A i) (B i)).comp hmap)
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
    exact (constrainedPairCascadeSpatialFirst_abs_le U u m v hm hv d j (A i) (B i) _ _).trans (hLi i)
  · intro i z
    refine (constrainedPairCascadeSpatialSecond_abs_le U u m v hm hv d j (A i) (B i) (A i) (B i) _ _).trans ?_
    change K * (l1 (A i) + l1 (B i)) * (l1 (A i) + l1 (B i)) ≤ K * L * L
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hLi i) hK) (hLi i)
      (add_nonneg (l1_nonneg _) (l1_nonneg _)) (mul_nonneg hK hL)
  · intro z w a
    dsimp only [Function.comp_apply]
    simp only [pairedFieldLinear_add_smul, ← add_assoc]
    have H := hasDerivAt_constrainedPairCascadeSpatialLine U u m v hm hv d j
      (pairedFieldLinear A w) (pairedFieldLinear B w)
      (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) a
    simp only [pairedFieldLinear, constrainedPairCascadeSpatialFirst_sum U u m v hm hv d] at H
    simpa only [pairedFieldLinear] using H
  · intro i z a
    dsimp only [Function.comp_apply]
    have H := hasDerivAt_constrainedPairCascadeSpatialFirst_line U u m v hm hv d j
      (A i) (B i) (A i) (B i) (x + pairedFieldLinear A z) (y + pairedFieldLinear B z) a
    simpa only [pairedFieldLinear_add_smul, pairedFieldLinear_single, ← add_assoc] using H

@[simp] theorem pairedFieldLinear_coordinates (z : Fin n → ℝ) :
    pairedFieldLinear (fun i : Fin n => Pi.single i 1) z = z := by
  classical
  ext l
  simp [pairedFieldLinear, Pi.single_apply]

theorem pairedSharedMean_eq_shift (mass variance : ℝ)
    (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    pairedSharedMean mass variance F G x y =
      pairedTiltMean mass variance (fun z => F (x + z) (y + z))
        (fun z => G (x + z) (y + z)) 0 := by
  have he (z : Fin n → ℝ) : x - y + (fun i => y i + Real.sqrt variance * z i) =
      x + (fun i => Real.sqrt variance * z i) := by
    ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [pairedSharedMean, pairedSecondMean, pairedTiltMean, tiltWeightPi,
    Pi.zero_apply, zero_add, he, Pi.add_def]

/-- The actual shared one-level variance derivative, at its actual mass.
The legacy `sharedStepPi` parameter is twice that mass. -/
theorem hasDerivAt_sharedStepPi_constrained_variance
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass : ℝ) (x y : Fin n → ℝ) {variance : ℝ} (hvar : 0 < variance) :
    let F := coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
    HasDerivAt (fun w => sharedStepPi n (2 * mass) w F x y)
      ((∑ i : Fin n, pairedSharedMean mass variance F (fun x y =>
        constrainedPairCascadeSpatialSecond m v d j U u (Pi.single i 1) (Pi.single i 1)
          (Pi.single i 1) (Pi.single i 1) x y +
        mass * (constrainedPairCascadeSpatialFirst m v d j U u (Pi.single i 1) (Pi.single i 1) x y) ^ 2)
        x y) / 2) variance := by
  have H := hasDerivAt_constrainedPairField_linear_variance U u m v hm hv d j
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) x y mass hvar
  dsimp only at H ⊢
  simp only [pairedFieldLinear_coordinates] at H
  simpa only [sharedStepPi, show 2 * mass / 2 = mass by ring,
    pairedSharedMean_eq_shift] using H

/-- Packing two independent N-site Gaussian fields into `2N` coordinates. -/
noncomputable def pairedGaussianSplit (n : ℕ) :
    (Fin (n + n) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ))

theorem measurePreserving_pairedGaussianSplit (n : ℕ) :
    MeasurePreserving (pairedGaussianSplit n) (piGauss (n + n)) ((piGauss n).prod (piGauss n)) := by
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1) finSumFinEquiv.symm)

@[simp] theorem pairedGaussianSplit_fst (z : Fin (n + n) → ℝ) (i : Fin n) :
    (pairedGaussianSplit n z).1 i = z (Fin.castAdd n i) := by
  simp [pairedGaussianSplit, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft']

@[simp] theorem pairedGaussianSplit_snd (z : Fin (n + n) → ℝ) (i : Fin n) :
    (pairedGaussianSplit n z).2 i = z (Fin.natAdd n i) := by
  simp [pairedGaussianSplit, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft']

noncomputable def independentLeftDirection (n : ℕ) (i : Fin (n + n)) : Fin n → ℝ :=
  (pairedGaussianSplit n (Pi.single i 1)).1

noncomputable def independentRightDirection (n : ℕ) (i : Fin (n + n)) : Fin n → ℝ :=
  (pairedGaussianSplit n (Pi.single i 1)).2

@[simp] theorem independentLeftDirection_castAdd (i : Fin n) :
    independentLeftDirection n (Fin.castAdd n i) = Pi.single i 1 := by
  classical
  ext l
  simp [independentLeftDirection, Pi.single_apply]

@[simp] theorem independentRightDirection_castAdd (i : Fin n) :
    independentRightDirection n (Fin.castAdd n i) = 0 := by
  classical
  ext l
  simp [independentRightDirection, Pi.single_apply]
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_addNat, Fin.val_castAdd] at hh
  omega

@[simp] theorem independentLeftDirection_natAdd (i : Fin n) :
    independentLeftDirection n (Fin.natAdd n i) = 0 := by
  classical
  ext l
  simp [independentLeftDirection, Pi.single_apply]
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_addNat, Fin.val_castAdd] at hh
  omega

@[simp] theorem independentRightDirection_natAdd (i : Fin n) :
    independentRightDirection n (Fin.natAdd n i) = Pi.single i 1 := by
  classical
  ext l
  simp [independentRightDirection, Pi.single_apply]

theorem pairedFieldLinear_independent_left (z : Fin (n + n) → ℝ) :
    pairedFieldLinear (independentLeftDirection n) z = (pairedGaussianSplit n z).1 := by
  classical
  ext l
  simp [pairedFieldLinear, independentLeftDirection, Pi.single_apply]

theorem pairedFieldLinear_independent_right (z : Fin (n + n) → ℝ) :
    pairedFieldLinear (independentRightDirection n) z = (pairedGaussianSplit n z).2 := by
  classical
  ext l
  simp [pairedFieldLinear, independentRightDirection, Pi.single_apply]

theorem independentStepPi_eq_packed (mass variance : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    independentStepPi n mass variance F x y =
      parisiStepPi (n + n) mass variance
        (fun z => F (x + (pairedGaussianSplit n z).1) (y + (pairedGaussianSplit n z).2)) 0 := by
  have hshift (z : Fin (n + n) → ℝ) :
      pairedGaussianSplit n (fun i => Real.sqrt variance * z i) =
        ((fun i => Real.sqrt variance * (pairedGaussianSplit n z).1 i),
          (fun i => Real.sqrt variance * (pairedGaussianSplit n z).2 i)) := by
    ext i <;> simp
  have hmap := measurePreserving_pairedGaussianSplit n
  unfold independentStepPi parisiStepPi
  simp only [Pi.zero_apply, zero_add, hshift, Pi.add_def]
  split_ifs
  · exact (hmap.integral_comp' (fun z => F (fun i => x i + Real.sqrt variance * z.1 i)
      (fun i => y i + Real.sqrt variance * z.2 i))).symm
  · congr 2
    exact (hmap.integral_comp' (fun z => Real.exp (mass * F (fun i => x i + Real.sqrt variance * z.1 i)
      (fun i => y i + Real.sqrt variance * z.2 i)))).symm

/-- The genuine independent level has the `2N`-coordinate heat generator.
The packed directions are the separate replica spins, not a common field. -/
theorem hasDerivAt_independentStepPi_constrained_variance
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (mass : ℝ) (x y : Fin n → ℝ) {variance : ℝ} (hvar : 0 < variance) :
    let F := coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
    let P := fun z => F (x + (pairedGaussianSplit n z).1) (y + (pairedGaussianSplit n z).2)
    HasDerivAt (fun w => independentStepPi n mass w F x y)
      ((∑ i : Fin (n + n), pairedTiltMean mass variance P (fun z =>
        constrainedPairCascadeSpatialSecond m v d j U u
          (independentLeftDirection n i) (independentRightDirection n i)
          (independentLeftDirection n i) (independentRightDirection n i)
          (x + (pairedGaussianSplit n z).1) (y + (pairedGaussianSplit n z).2) +
        mass * (constrainedPairCascadeSpatialFirst m v d j U u
          (independentLeftDirection n i) (independentRightDirection n i)
          (x + (pairedGaussianSplit n z).1) (y + (pairedGaussianSplit n z).2)) ^ 2) 0) / 2) variance := by
  have H := hasDerivAt_constrainedPairField_linear_variance U u m v hm hv d j
    (independentLeftDirection n) (independentRightDirection n) x y mass hvar
  dsimp only at H ⊢
  simpa only [pairedFieldLinear_independent_left, pairedFieldLinear_independent_right,
    independentStepPi_eq_packed] using H

end SpinGlass.Targets
