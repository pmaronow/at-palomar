module

public import Targets.Section5SignedInitialInterpolation
public import Targets.Section5ConditionedInitialInterpolation
public import Targets.SKSpinFlip
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-!
# Exact second-replica reflection through the initial field cascade

Independent Gaussian increments are invariant under reflection of the second
replica. An anti-shared increment then becomes an ordinary shared increment
at the reflected external field. These identities use the actual Gaussian
integrals, including zero masses and zero variances.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Negating all coordinates preserves the actual product Gaussian law. -/
theorem measurePreserving_neg_piGauss (n : ℕ) :
    MeasurePreserving (fun z : Fin n → ℝ => -z) (piGauss n) (piGauss n) := by
  have H : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  exact measurePreserving_pi (fun _ : Fin n => gaussianReal 0 1)
    (fun _ : Fin n => gaussianReal 0 1) (fun _ => H)

/-- Reflection commutes with an independent two-replica Gaussian step.
The measurable-equivalence change of variables needs no extra growth input. -/
theorem independentStepPi_flip_second {n : ℕ} (m v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    independentStepPi n m v (fun x y => F x (-y)) x y =
      independentStepPi n m v F x (-y) := by
  have hp : MeasurePreserving (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1, -z.2))
      ((piGauss n).prod (piGauss n)) ((piGauss n).prod (piGauss n)) :=
    (MeasurePreserving.id (piGauss n)).prod (measurePreserving_neg_piGauss n)
  have he : MeasurableEmbedding
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1, -z.2)) :=
    MeasurableEmbedding.id.prodMap measurableEmbedding_neg
  have hchange (f : ℝ → ℝ) :
      (∫ z, f (F (fun i => x i + Real.sqrt v * z.1 i)
        (-(fun i => y i + Real.sqrt v * z.2 i))) ∂(piGauss n).prod (piGauss n)) =
      ∫ z, f (F (fun i => x i + Real.sqrt v * z.1 i)
        (fun i => (-y) i + Real.sqrt v * z.2 i)) ∂(piGauss n).prod (piGauss n) := by
    convert hp.integral_comp he
      (fun z => f (F (fun i => x i + Real.sqrt v * z.1 i)
        (fun i => (-y) i + Real.sqrt v * z.2 i))) using 1
    congr 1
    funext z
    congr 2
    funext i
    simp only [Pi.neg_apply, mul_neg, neg_add_rev]
    ring
  by_cases hm : m = 0
  · simpa only [independentStepPi, if_pos hm, id_eq] using hchange id
  · simp only [independentStepPi, if_neg hm]
    rw [hchange (fun z => Real.exp (m * z))]

/-- Every independent prefix preserves the second-replica terminal reflection. -/
theorem coupledFieldCascade_independent_flip_second {n : ℕ} (m v : ℕ → ℝ)
    {d j : ℕ} (hj : j ≤ d)
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hFG : ∀ x y, F x y = G x (-y)) (x y : Fin n → ℝ) :
    coupledFieldCascade n m v d F j x y =
      coupledFieldCascade n m v d G j x (-y) := by
  induction j generalizing x y with
  | zero => exact hFG x y
  | succ j ih =>
    have he : coupledFieldCascade n m v d F j =
        fun x y => coupledFieldCascade n m v d G j x (-y) :=
      funext fun x => funext fun y => ih (by omega) x y
    simp only [coupledFieldCascade, if_pos (show j < d by omega), he]
    exact independentStepPi_flip_second (m j) (v j) _ x y

/-- The anti-shared mass-zero step is the ordinary shared step after
reflection of the second replica, at the reflected external field. -/
theorem coupledLinearStep_anti_flip_second {n : ℕ} (v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 v (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1)) F x y =
      sharedStepPi n 0 v (fun x y => F x (-y)) x (-y) := by
  have hn (z : Fin n → ℝ) :
      pairedFieldLinear (fun i : Fin n => -(Pi.single i 1)) z = -z := by
    ext i
    simp [pairedFieldLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [coupledLinearStep, pairedFieldLinear_coordinates, hn,
    sharedStepPi, zero_div, parisiStepPi, ↓reduceIte, Pi.zero_apply, zero_add]
  congr 1
  funext z
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.neg_apply, neg_add_rev, neg_neg]
  ring

/-- Exact reflection of the signed initial prefix into the conditioned
positive-overlap cascade. The frozen field is deliberately not included here;
it remains an ordinary outer expectation at arbitrary shifted fields. -/
theorem section5SignedInitial_anti_prefix_eq_conditioned {n k : ℕ}
    (s : RSBScheme k) (β t u w : ℝ) (U : EnergySpace n)
    (hU : ∀ σ, U (configFlip n σ) = U σ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 ((1 - w) * t * (β ^ 2 * (-u)))
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1))
      (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5InterpolationVariance s β t (-u) 1 (k + 2 - j) w)
        (k + 2) (constrainedPairFieldBase n U u) (k + 2)) x y =
      coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5ConditionedInitialVariance s β t (-u) (k + 2 - j) w)
        (k + 2) (constrainedPairFieldBase n U (-u)) (k + 3) x (-y) := by
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5InterpolationVariance s β t (-u) 1 (k + 2 - j) w
  let V' := fun j => section5ConditionedInitialVariance s β t (-u) (k + 2 - j) w
  have hV : ∀ j < k + 2, V j = V' j := by
    intro j hj
    simp only [V, V', section5ConditionedInitialVariance,
      if_neg (show k + 2 - j ≠ 0 by omega)]
  have he (x y : Fin n → ℝ) :
      coupledFieldCascade n M V (k + 2) (constrainedPairFieldBase n U u) (k + 2) x (-y) =
      coupledFieldCascade n M V' (k + 2) (constrainedPairFieldBase n U (-u)) (k + 2) x y := by
    have H := coupledFieldCascade_independent_flip_second M V (d := k + 2) le_rfl
      (constrainedPairFieldBase_flip U hU u) x (-y)
    rw [coupledFieldCascade_congr_variance M V V' (k + 2) (k + 2)
      (constrainedPairFieldBase n U (-u)) hV, neg_neg] at H
    exact H
  rw [coupledLinearStep_anti_flip_second]
  change sharedStepPi n 0 ((1 - w) * t * (β ^ 2 * (-u)))
    (fun x y => coupledFieldCascade n M V (k + 2)
      (constrainedPairFieldBase n U u) (k + 2) x (-y)) x (-y) = _
  rw [show (fun x y => coupledFieldCascade n M V (k + 2)
      (constrainedPairFieldBase n U u) (k + 2) x (-y)) =
      coupledFieldCascade n M V' (k + 2) (constrainedPairFieldBase n U (-u)) (k + 2)
      from funext fun x => funext (he x)]
  change _ = coupledFieldCascade n M V' (k + 2)
    (constrainedPairFieldBase n U (-u)) ((k + 2) + 1) x (-y)
  conv_rhs => rw [coupledFieldCascade, if_neg (lt_irrefl _)]
  simp only [M, V', Nat.sub_self, section5Mass, section5ConditionedInitialVariance,
    show (0 : ℕ) < 1 by omega, if_true, s.m_zero, zero_div, mul_zero]

end SpinGlass.Targets
