module

public import Targets.Section5InterpolationBound
public import Targets.CoupledSharedInsertion

@[expose] public section

/-!
# The genuine signed initial interpolation, with its frozen shared field

For negative overlap the interpolating Gaussian field is anti-shared, but the
original frozen field remains positively shared. Since the initial mass is
zero, these are two ordinary Gaussian expectations outside the independent
prefix. Keeping them separate preserves the exact original pressure endpoint.

This module proves the construction and both endpoint identities only. The
simultaneous signed pressure derivative and its covariance inequality are not
assumed or asserted here.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- At mass and variance zero an arbitrary linear Gaussian step is evaluation. -/
theorem coupledLinearStep_zero_mass_zero_variance {n p : ℕ}
    (A B : Fin p → Fin n → ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep 0 0 A B F = F := by
  funext x y
  simp [coupledLinearStep, parisiStepPi, pairedFieldLinear]

/-- The positively shared frozen field is followed by the negatively shared
interpolating field. Both masses are the actual compulsory initial mass zero. -/
noncomputable def section5SignedInitialOuter {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β t u w : ℝ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  coupledLinearStep 0 ((1 - w) * t * (β ^ 2 * (-u)))
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1))
    (coupledLinearStep 0 ((1 - t) * (β ^ 2 * s.q 1))
      (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) F) x y

/-- The original positive shared field survives at interpolation time one. -/
theorem section5SignedInitialOuter_one {n k : ℕ} (s : RSBScheme k) (β t u : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    section5SignedInitialOuter n s β t u 1 F =
      sharedStepPi n 0 ((1 - t) * (β ^ 2 * s.q 1)) F := by
  funext x y
  simp only [section5SignedInitialOuter, sub_self, zero_mul,
    coupledLinearStep_zero_mass_zero_variance, coupledLinearStep_shared, mul_zero]

/-- The sum of the two signed field kernels has the genuine combined
cross-covariance, while preserving each replica's marginal variance. -/
theorem section5SignedInitial_outer_kernel {n k : ℕ} (s : RSBScheme k)
    (β t u w : ℝ) (p q : Config n × Config n) :
    ((1 - t) * (β ^ 2 * s.q 1)) * pairFieldCovariance 1 1 1 p q +
      ((1 - w) * t * (β ^ 2 * (-u))) * pairFieldCovariance 1 1 (-1) p q =
    pairFieldCovariance 1
      ((1 - t) * (β ^ 2 * s.q 1) - (1 - w) * t * (β ^ 2 * u))
      ((1 - t) * (β ^ 2 * s.q 1) + (1 - w) * t * (β ^ 2 * u)) p q := by
  simp only [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

variable {Ω : Type*} [MeasureSpace Ω]

/-- The actual signed initial path. The trial overlap for the nonnegative
variance sequence is `-u`, while the constrained terminal still uses `u`. -/
noncomputable def section5SignedInitialInterpolation {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, section5SignedInitialOuter n s β t u w
    (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5InterpolationVariance s β t (-u) 1 (k + 2 - j) w)
      (k + 2) (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 2))
    (fun _ => h) (fun _ => h) ∂ℙ

/-- The genuine zero-time field endpoint retains both the frozen positive
shared field and the independent inserted variance. -/
noncomputable def section5SignedInitialFieldEndpoint {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h t u : ℝ) : ℝ :=
  (1 / (n : ℝ)) * section5SignedInitialOuter n s β t u 0
    (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5Variance s β 1 (k + 2 - j) (t * (β ^ 2 * (s.q 1 + u))))
      (k + 2) (constrainedPairFieldBase n 0 u) (k + 2))
    (fun _ => h) (fun _ => h)

/-- Nonnegativity of every actual variance, including both frozen/interpolating
outer components. Neither zero first overlap nor endpoint times are removed. -/
theorem section5SignedInitial_variances_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    (hw : w ∈ Set.Icc 0 1) :
    0 ≤ (1 - t) * (β ^ 2 * s.q 1) ∧
    0 ≤ (1 - w) * t * (β ^ 2 * (-u)) ∧
    ∀ p ≤ k + 2, 0 ≤ section5InterpolationVariance s β t (-u) 1 p w := by
  refine ⟨mul_nonneg (sub_nonneg.mpr ht.2)
    (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) ht.1)
      (mul_nonneg (sq_nonneg β) (neg_nonneg.mpr hu.2)), ?_⟩
  intro p hp
  apply section5InterpolationVariance_nonneg s β (by omega) hp ht _ hw
  simp only [Nat.sub_self, s.q_zero]
  constructor <;> linarith [hu.1, hu.2]

/-- Exact physical endpoint of the signed/frozen construction. The external
field and the original positive shared Gaussian field are unchanged. -/
theorem section5SignedInitialCascade_one {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (U : EnergySpace n) (u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    section5SignedInitialOuter n s β t u 1
      (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
        (fun j => section5InterpolationVariance s β t (-u) 1 (k + 2 - j) 1)
        (k + 2) (constrainedPairFieldBase n (Real.sqrt t • U) u) (k + 2))
      (fun _ => h) (fun _ => h) =
    coupledCascade n s β (k + 1) (constrainedBase n U h t u) (k + 2) 0 0 := by
  simp only [section5SignedInitialOuter_one, section5InterpolationVariance_one]
  have H := section5Cascade_one s β h U (r := 1) (by omega) (by omega) 0 u ht
  have he : coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5FrozenVariance s β t 1 (k + 2 - j)) (k + 2)
      (constrainedPairFieldBase n (Real.sqrt t • U) u) (k + 3) =
      sharedStepPi n 0 ((1 - t) * (β ^ 2 * s.q 1))
        (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
          (fun j => section5FrozenVariance s β t 1 (k + 2 - j)) (k + 2)
          (constrainedPairFieldBase n (Real.sqrt t • U) u) (k + 2)) := by
    rw [show k + 3 = (k + 2) + 1 by omega, coupledFieldCascade]
    simp [section5Mass, section5FrozenVariance, s.m_zero, s.q_zero]
  simpa only [show k + 3 - 1 = k + 2 by omega,
    show k + 2 - 1 = k + 1 by omega, he] using H

/-- Averaging the exact physical endpoint gives the original constrained free
energy, not a reflected-field or modified-scheme surrogate. -/
theorem section5SignedInitialInterpolation_one {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    section5SignedInitialInterpolation n s β h U t u 1 =
      constrainedPhi n s β h U (k + 1) t u := by
  simp only [section5SignedInitialInterpolation, one_mul,
    section5SignedInitialCascade_one s β h _ u ht, constrainedPhi]

/-- Exact zero-time endpoint, retaining its positive frozen field. -/
theorem section5SignedInitialInterpolation_zero [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (t u : ℝ) :
    section5SignedInitialInterpolation n s β h U t u 0 =
      section5SignedInitialFieldEndpoint n s β h t u := by
  simp only [section5SignedInitialInterpolation, zero_mul, Real.sqrt_zero, zero_smul,
    section5InterpolationVariance_zero, sub_neg_eq_add, integral_const,
    probReal_univ, smul_eq_mul, one_mul, section5SignedInitialFieldEndpoint]

end SpinGlass.Targets
