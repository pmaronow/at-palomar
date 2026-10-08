module

/-
# Spatial derivatives of the actual constrained paired cascade

Separate directions in the two replica fields are represented by finite-state
spin observables. RSAT's finite-state differential calculus supplies the terminal
derivatives, and the already proved paired-cascade calculus propagates them.
No covariance or variance derivative of the interpolation is assumed here.
-/
public import Targets.CoupledCascadeSecond

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators ContDiff

namespace SpinGlass.Targets

variable {n : ℕ}

/-- A pair-field direction as an element of the finite-state energy space. -/
noncomputable def pairFieldVector (n : ℕ) (u : ℝ) (A B : Fin n → ℝ) :
    AT.GTStateSpace (AT.ConstrainedPair n u) := WithLp.toLp 2 (pairFieldPotential n u A B)

@[simp] theorem pairFieldVector_apply (n : ℕ) (u : ℝ) (A B : Fin n → ℝ)
    (p : AT.ConstrainedPair n u) : pairFieldVector n u A B p = pairFieldPotential n u A B p := rfl

theorem pairFieldPotential_shift (u a : ℝ) (x y A B : Fin n → ℝ)
    (p : AT.ConstrainedPair n u) :
    pairFieldPotential n u (x + a • A) (y + a • B) p =
      pairFieldPotential n u x y p + a * pairFieldPotential n u A B p := by
  simp only [pairFieldPotential, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  simp_rw [show ∀ q b : ℝ, q * (a * b) = a * (q * b) by intros; ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem pairFieldVector_shift (u a : ℝ) (x y A B : Fin n → ℝ) :
    pairFieldVector n u (x + a • A) (y + a • B) =
      pairFieldVector n u x y + a • pairFieldVector n u A B := by
  ext p
  simp only [pairFieldVector_apply, pairFieldPotential_shift, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]

theorem constrainedPairFieldBase_eq_fieldState (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) :
    constrainedPairFieldBase n U u x y =
      AT.gtStateLogPartition 0 (pairDisorderCLM n u U + pairFieldVector n u x y) := by
  simp only [constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
    AT.gtStatePartition, PiLp.add_apply, pairFieldVector_apply, Pi.zero_apply, add_zero]

theorem constrainedPairGibbs_eq_fieldState (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ)
    (p : AT.ConstrainedPair n u) :
    constrainedPairGibbs n U u x y p =
      AT.gtStateGibbs 0 (pairDisorderCLM n u U + pairFieldVector n u x y) p := by
  simp only [constrainedPairGibbs, AT.gtStateGibbs, AT.gtStatePartition,
    PiLp.add_apply, pairFieldVector_apply, Pi.zero_apply, add_zero]

/-- The observable for arbitrary separate replica-field directions. -/
noncomputable def constrainedPairFieldDirection (U : EnergySpace n) (u : ℝ)
    (A B x y : Fin n → ℝ) : ℝ :=
  ∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p * pairFieldPotential n u A B p

/-- The terminal spatial covariance, with separate directions for each replica. -/
noncomputable def constrainedPairFieldCovariance (U : EnergySpace n) (u : ℝ)
    (A B C D x y : Fin n → ℝ) : ℝ :=
  (∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
    pairFieldPotential n u C D p * pairFieldPotential n u A B p) -
    constrainedPairFieldDirection U u C D x y * constrainedPairFieldDirection U u A B x y

theorem hasDerivAt_constrainedPairFieldBase_field (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => constrainedPairFieldBase n U u (x + b • A) (y + b • B))
      (constrainedPairFieldDirection U u A B (x + a • A) (y + a • B)) a := by
  have hlin := ((hasDerivAt_id a).smul_const (pairFieldVector n u A B)).const_add
    (pairDisorderCLM n u U + pairFieldVector n u x y)
  have H := ((AT.contDiff_gtStateLogPartition (0 : AT.ConstrainedPair n u → ℝ)).differentiable
    (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt a hlin
  simpa only [constrainedPairFieldBase_eq_fieldState, constrainedPairFieldDirection,
    constrainedPairGibbs_eq_fieldState, pairFieldVector_shift, add_assoc,
    AT.fderiv_gtStateLogPartition_apply, pairFieldVector_apply,
    Function.comp_apply, id_eq, one_smul] using! H

theorem hasDerivAt_constrainedPairFieldDirection_field (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B C D x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => constrainedPairFieldDirection U u A B (x + b • C) (y + b • D))
      (constrainedPairFieldCovariance U u A B C D (x + a • C) (y + a • D)) a := by
  have hlin := ((hasDerivAt_id a).smul_const (pairFieldVector n u C D)).const_add
    (pairDisorderCLM n u U + pairFieldVector n u x y)
  have hfirst := (contDiff_infty.mp
    (AT.contDiff_gtStateLogPartition (0 : AT.ConstrainedPair n u → ℝ)) 2).fderiv_right
    (m := 1) (by norm_num)
  have H := (hfirst.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt a hlin
  have HH := H.clm_apply (hasDerivAt_const a (pairFieldVector n u A B))
  simpa only [constrainedPairFieldDirection, constrainedPairFieldCovariance,
    constrainedPairGibbs_eq_fieldState, pairFieldVector_shift, add_assoc,
    AT.fderiv_gtStateLogPartition_apply, AT.second_fderiv_gtStateLogPartition_apply,
    pairFieldVector_apply, Function.comp_apply, id_eq, one_smul,
    ContinuousLinearMap.map_zero, zero_add, add_zero] using! HH

theorem pairFieldPotential_abs_le (u : ℝ) (A B : Fin n → ℝ) (p : AT.ConstrainedPair n u) :
    |pairFieldPotential n u A B p| ≤ l1 A + l1 B := by
  have hb (σ : Config n) (A : Fin n → ℝ) : |∑ i, spin n σ i * A i| ≤ l1 A := by
    calc
      _ ≤ ∑ i, |spin n σ i * A i| := Finset.abs_sum_le_sum_abs _ _
      _ = l1 A := by simp only [abs_mul, abs_spin, one_mul, l1]
  exact (abs_add_le _ _).trans (add_le_add (hb p.1.1 A) (hb p.1.2 B))

private theorem constrainedPairMean_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ)
    (F : AT.ConstrainedPair n u → ℝ) {K : ℝ} (hF : ∀ p, |F p| ≤ K) :
    |∑ p, constrainedPairGibbs n U u x y p * F p| ≤ K := by
  classical
  calc
    _ ≤ ∑ p, |constrainedPairGibbs n U u x y p * F p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, constrainedPairGibbs n U u x y p * K := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
      exact mul_le_mul_of_nonneg_left (hF p) (constrainedPairGibbs_nonneg n U u x y p)
    _ = K := by rw [← Finset.sum_mul, sum_constrainedPairGibbs, one_mul]

theorem constrainedPairFieldDirection_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B x y : Fin n → ℝ) :
    |constrainedPairFieldDirection U u A B x y| ≤ l1 A + l1 B :=
  constrainedPairMean_abs_le U u x y _ (pairFieldPotential_abs_le u A B)

theorem constrainedPairFieldCovariance_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B C D x y : Fin n → ℝ) :
    |constrainedPairFieldCovariance U u A B C D x y| ≤ 2 * (l1 A + l1 B) * (l1 C + l1 D) := by
  have ht := constrainedPairMean_abs_le U u x y
    (fun p => pairFieldPotential n u C D p * pairFieldPotential n u A B p)
    (K := (l1 C + l1 D) * (l1 A + l1 B)) (fun p => by
      rw [abs_mul]
      exact mul_le_mul (pairFieldPotential_abs_le u C D p)
        (pairFieldPotential_abs_le u A B p) (abs_nonneg _)
        (add_nonneg (l1_nonneg C) (l1_nonneg D)))
  have hp : |constrainedPairFieldDirection U u C D x y * constrainedPairFieldDirection U u A B x y| ≤
      (l1 C + l1 D) * (l1 A + l1 B) := by
    rw [abs_mul]
    exact mul_le_mul (constrainedPairFieldDirection_abs_le U u C D x y)
      (constrainedPairFieldDirection_abs_le U u A B x y) (abs_nonneg _)
      (add_nonneg (l1_nonneg C) (l1_nonneg D))
  simp only [← mul_assoc] at ht
  have ha := abs_sub_le
    (∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
      pairFieldPotential n u C D p * pairFieldPotential n u A B p) 0
    (constrainedPairFieldDirection U u C D x y * constrainedPairFieldDirection U u A B x y)
  simp only [sub_zero, zero_sub, abs_neg] at ha
  change |(∑ p : AT.ConstrainedPair n u, constrainedPairGibbs n U u x y p *
    pairFieldPotential n u C D p * pairFieldPotential n u A B p) -
    constrainedPairFieldDirection U u C D x y * constrainedPairFieldDirection U u A B x y| ≤ _
  nlinarith

theorem measurable_constrainedPairFieldDirection (U : EnergySpace n) (u : ℝ) (A B : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => constrainedPairFieldDirection U u A B p.1 p.2) := by
  unfold constrainedPairFieldDirection constrainedPairGibbs AT.gtStateGibbs AT.gtStatePartition
    pairFieldPotential
  fun_prop

theorem measurable_constrainedPairFieldCovariance (U : EnergySpace n) (u : ℝ)
    (A B C D : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      constrainedPairFieldCovariance U u A B C D p.1 p.2) := by
  unfold constrainedPairFieldCovariance constrainedPairFieldDirection constrainedPairGibbs
    AT.gtStateGibbs AT.gtStatePartition pairFieldPotential
  fun_prop

/-- Actual field-line terminal regularity; each replica may have a different
direction. The derivative bound is the sum of the two directional l1 norms. -/
theorem constrainedPairFieldBase_fieldParamDeriv (U : EnergySpace n) (u r : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B : Fin n → ℝ) :
    CoupledParamDeriv (fun a x y => constrainedPairFieldBase n U u (x + a • A) (y + a • B))
      (fun a x y => constrainedPairFieldDirection U u A B (x + a • A) (y + a • B))
      (guerraLineNbhd r) (l1 A + l1 B) := by
  have hz : CoupledGrowth (constrainedPairFieldBase n U u) := by
    simpa only [zero_smul, add_zero] using
      (constrainedPairFieldBase_paramDeriv U 0 u 0).growth_at
        (a := 0) ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  obtain ⟨C, L, hL, hb⟩ := hz.bound
  refine ⟨fun a _ x y => hasDerivAt_constrainedPairFieldBase_field U u A B x y a,
    fun a _ => hz.measurable.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (p.1 + a • A, p.2 + a • B)) (by fun_prop),
    fun a _ => (measurable_constrainedPairFieldDirection U u A B).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + a • A, p.2 + a • B)) (by fun_prop),
    ⟨C + L * ((|r| + 1) * (l1 A + l1 B)), L, hL, ?_⟩,
    fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _⟩
  intro a ha x y
  have hsm (Z : Fin n → ℝ) : l1 (a • Z) = |a| * l1 Z := l1_const_smul a Z
  have hx := l1_add_le x (a • A)
  have hy := l1_add_le y (a • B)
  rw [hsm] at hx hy
  have hab := mul_le_mul_of_nonneg_right (abs_le_abs_add_one_of_mem_guerraLineNbhd ha)
    (add_nonneg (l1_nonneg A) (l1_nonneg B))
  nlinarith [hb (x + a • A) (y + a • B)]

/-- Actual field-direction regularity, with its finite-state covariance as the
derivative in another arbitrary two-replica direction. -/
theorem constrainedPairFieldDirection_fieldParamDeriv (U : EnergySpace n) (u r : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (A B C D : Fin n → ℝ) :
    CoupledParamDeriv (fun a x y => constrainedPairFieldDirection U u A B (x + a • C) (y + a • D))
      (fun a x y => constrainedPairFieldCovariance U u A B C D (x + a • C) (y + a • D))
      (guerraLineNbhd r) (2 * (l1 A + l1 B) * (l1 C + l1 D)) := by
  refine ⟨fun a _ x y => hasDerivAt_constrainedPairFieldDirection_field U u A B C D x y a,
    fun a _ => (measurable_constrainedPairFieldDirection U u A B).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + a • C, p.2 + a • D)) (by fun_prop),
    fun a _ => (measurable_constrainedPairFieldCovariance U u A B C D).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + a • C, p.2 + a • D)) (by fun_prop),
    ⟨l1 A + l1 B, 0, le_rfl, ?_⟩,
    fun a _ x y => constrainedPairFieldCovariance_abs_le U u A B C D _ _⟩
  intro a _ x y
  simpa only [zero_mul, add_zero] using constrainedPairFieldDirection_abs_le U u A B (x + a • C) (y + a • D)

/-- Constant translations preserve the local terminal-parameter hypotheses. -/
theorem CoupledParamDeriv.translate_fields
    {A D : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K : ℝ}
    (h : CoupledParamDeriv A D s K) (X Y : Fin n → ℝ) :
    CoupledParamDeriv (fun a x y => A a (x + X) (y + Y))
      (fun a x y => D a (x + X) (y + Y)) s K := by
  obtain ⟨C, L, hL, hb⟩ := h.growth
  refine ⟨fun a ha x y => h.deriv a ha _ _,
    fun a ha => (h.measurable a ha).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + X, p.2 + Y)) (by fun_prop),
    fun a ha => (h.measurable_deriv a ha).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + X, p.2 + Y)) (by fun_prop),
    ⟨C + L * (l1 X + l1 Y), L, hL, ?_⟩, fun a ha x y => h.bound a ha _ _⟩
  intro a ha x y
  nlinarith [hb a ha (x + X) (y + Y), l1_add_le x X, l1_add_le y Y]

/-- Separate physical translations commute with the actual paired recursion. -/
theorem coupledFieldCascade_translate (m v : ℕ → ℝ) (d j : ℕ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (X Y x y : Fin n → ℝ) :
    coupledFieldCascade n m v d (fun x y => A (x + X) (y + Y)) j x y =
      coupledFieldCascade n m v d A j (x + X) (y + Y) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    simp only [coupledFieldCascade]
    split_ifs
    · simp only [independentStepPi]
      simp_rw [ih]
      simp only [Pi.add_def, add_right_comm]
    · simp only [sharedStepPi, ih]
      congr 1
      funext z
      congr 1 <;> abel

/-- Actual first spatial derivative at every depth, with separate directions
in the two fields and the exact recursively tilted spin observable. -/
theorem hasDerivAt_constrainedPairFieldCascade_field (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B x y : Fin n → ℝ) :
    HasDerivAt (fun a : ℝ => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
      (x + a • A) (y + a • B))
      (coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j x y) 0 := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).fieldCascade
    isOpen_Ioo m v hm hv d j).deriv 0 ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [coupledFieldCascade_translate, zero_smul, add_zero] using H

/-- Actual mixed spatial derivative at every depth. The first direction is
`(A,B)` and the varying direction is `(C,D)`; no replica equality is required. -/
theorem hasDerivAt_constrainedPairFieldCascade_field_second (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B C D x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => coupledFieldCascade n m v d
        (constrainedPairFieldBase n U u) j (x + a • C + b • A) (y + a • D + b • B)) 0)
      (coupledFieldCascadeDD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
        (constrainedPairFieldCovariance U u A B C D) j x y) 0 := by
  have hefun (a b : ℝ) :
      coupledFieldCascade n m v d (fun x y => constrainedPairFieldBase n U u
        (x + a • C + b • A) (y + a • D + b • B)) j x y =
        coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
          (x + a • C + b • A) (y + a • D + b • B) := by
    calc
      _ = coupledFieldCascade n m v d
          (fun x y => constrainedPairFieldBase n U u (x + b • A) (y + b • B)) j
          (x + a • C) (y + a • D) :=
        coupledFieldCascade_translate m v d j _ (a • C) (a • D) x y
      _ = _ := coupledFieldCascade_translate m v d j _ (b • A) (b • B) _ _
  have he (a : ℝ) := ((((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).translate_fields
    (a • C) (a • D)).fieldCascade isOpen_Ioo m v hm hv d j).deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y).deriv
  simp only [hefun, zero_smul, add_zero] at he
  simp only [he]
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).fieldCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo m v hm hv d j).1.deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [zero_smul, add_zero] using H

/-- The actual first spatial derivative, before identification with tilted spins. -/
noncomputable def constrainedPairCascadeSpatialFirst (m v : ℕ → ℝ) (d j : ℕ)
    (U : EnergySpace n) (u : ℝ) (A B x y : Fin n → ℝ) : ℝ :=
  deriv (fun a : ℝ => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j
    (x + a • A) (y + a • B)) 0

theorem constrainedPairCascadeSpatialFirst_eq (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B x y : Fin n → ℝ) :
    constrainedPairCascadeSpatialFirst m v d j U u A B x y =
      coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j x y :=
  (hasDerivAt_constrainedPairFieldCascade_field U u m v hm hv d j A B x y).deriv

/-- The actual mixed spatial derivative; the second pair of directions varies
the first derivative in the first pair of directions. -/
noncomputable def constrainedPairCascadeSpatialSecond (m v : ℕ → ℝ) (d j : ℕ)
    (U : EnergySpace n) (u : ℝ) (A B C D x y : Fin n → ℝ) : ℝ :=
  deriv (fun a : ℝ => deriv (fun b : ℝ => coupledFieldCascade n m v d
    (constrainedPairFieldBase n U u) j (x + a • C + b • A) (y + a • D + b • B)) 0) 0

theorem constrainedPairCascadeSpatialSecond_eq (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B C D x y : Fin n → ℝ) :
    constrainedPairCascadeSpatialSecond m v d j U u A B C D x y =
      coupledFieldCascadeDD m v d (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
        (constrainedPairFieldCovariance U u A B C D) j x y :=
  (hasDerivAt_constrainedPairFieldCascade_field_second U u m v hm hv d j A B C D x y).deriv

theorem constrainedPairCascadeSpatialFirst_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B x y : Fin n → ℝ) :
    |constrainedPairCascadeSpatialFirst m v d j U u A B x y| ≤ l1 A + l1 B := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).fieldCascade
    isOpen_Ioo m v hm hv d j).bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [constrainedPairCascadeSpatialFirst_eq U u m v hm hv d j,
    zero_smul, add_zero] using H

theorem constrainedPairCascadeSpatialSecond_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B C D x y : Fin n → ℝ) :
    |constrainedPairCascadeSpatialSecond m v d j U u A B C D x y| ≤
      (2 + 4 * ∑ l ∈ Finset.range j, |m l|) * (l1 A + l1 B) * (l1 C + l1 D) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).fieldCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo m v hm hv d j).1.bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simp only [zero_smul, add_zero] at H
  rw [constrainedPairCascadeSpatialSecond_eq U u m v hm hv d j]
  refine H.trans ?_
  rw [coupledHessianBound_eq_sum]
  have hsum : (∑ l ∈ Finset.range j, (if l < d then 4 else 2) * |m l|) ≤
      4 * ∑ l ∈ Finset.range j, |m l| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right
      (by split_ifs <;> norm_num) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (add_nonneg (l1_nonneg A) (l1_nonneg B)))
    (add_nonneg (l1_nonneg C) (l1_nonneg D))]

theorem measurable_constrainedPairCascadeSpatialFirst (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      constrainedPairCascadeSpatialFirst m v d j U u A B p.1 p.2) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).fieldCascade
    isOpen_Ioo m v hm hv d j).measurable_deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [constrainedPairCascadeSpatialFirst_eq U u m v hm hv d j,
    zero_smul, add_zero] using H

theorem measurable_constrainedPairCascadeSpatialSecond (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d j : ℕ) (A B C D : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      constrainedPairCascadeSpatialSecond m v d j U u A B C D p.1 p.2) := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 C D).fieldCascadeSecond
    (constrainedPairFieldDirection_fieldParamDeriv U u 0 A B C D)
    (fun a _ x y => constrainedPairFieldDirection_abs_le U u A B _ _)
    isOpen_Ioo m v hm hv d j).1.measurable_deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩
  simpa only [constrainedPairCascadeSpatialSecond_eq U u m v hm hv d j,
    zero_smul, add_zero] using H

/-- Separate coordinates yield the individual replica spins. -/
theorem pairFieldPotential_left_single (u : ℝ) (i : Fin n) (p : AT.ConstrainedPair n u) :
    pairFieldPotential n u (Pi.single i 1) 0 p = spin n p.1.1 i := by
  classical
  simp [pairFieldPotential, Pi.single_apply]

theorem pairFieldPotential_right_single (u : ℝ) (i : Fin n) (p : AT.ConstrainedPair n u) :
    pairFieldPotential n u 0 (Pi.single i 1) p = spin n p.1.2 i := by
  classical
  simp [pairFieldPotential, Pi.single_apply]

/-- A signed shared coordinate gives the combined spin used in the existing
signed covariance contraction. No positivity assumption on the sign is needed. -/
theorem pairFieldPotential_shared_single (u e : ℝ) (i : Fin n) (p : AT.ConstrainedPair n u) :
    pairFieldPotential n u (Pi.single i 1) (e • Pi.single i 1) p =
      spin n p.1.1 i + e * spin n p.1.2 i := by
  classical
  simp [pairFieldPotential, Pi.single_apply, mul_comm]

end SpinGlass.Targets
