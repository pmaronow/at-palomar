module

public import Lemmas.AT.Definitions
public import Lemmas.Cavity.Estimates
public import Mathlib.Tactic
public import Lemmas.Concentration.Weak

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

universe u

/-!
# Cavity approximation

This file is written against `Lemmas.AT.Definitions`.

The fixed change of basis in `ATDefs` has row order `(V,U,D)`:

  V = 2 B - 3 C,
  U = A - 4 B + 3 C,
  D = A - 2 B + C.

The analytic theorem `cavityModeRemainder_bound_from_lastSpin` is exactly the
last-spin Gaussian interpolation argument from the appendix.  Everything after
that theorem is deterministic finite-dimensional algebra.
-/

/-! ## Deterministic mode algebra -/

def cavityModeMatrix (β q r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β ^ 2 * cavityKappa q r, β ^ 2 * cavityZeta q r, 0;
     0, β ^ 2 * cavityKappa q r, 0;
     0, 0, β ^ 2 * (1 - 2 * q + r)]

def cavityModeSource (q r : ℝ) : Fin 3 → ℝ :=
  ![cavityZeta q r, cavityKappa q r, 1 - 2 * q + r]

/-- The cavity matrix is triangular in the `(V,U,D)` basis. -/
theorem cavityChangeMatrix_mul_cavityMatrix (β q r : ℝ) :
    cavityChangeMatrix * cavityMatrix β q r =
      cavityModeMatrix β q r * cavityChangeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cavityChangeMatrix, cavityMatrix, cavityModeMatrix,
      cavityKappa, cavityZeta, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- The source vector in the `(V,U,D)` basis is `(ζ,κ,1-2q+r)`. -/
theorem cavityChangeMatrix_mulVec_theta (q r : ℝ) :
    cavityChangeMatrix.mulVec (theta q r) = cavityModeSource q r := by
  ext i
  fin_cases i <;>
    simp [cavityChangeMatrix, theta, cavityModeSource, cavityKappa,
      cavityZeta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- `cavityChangeMatrix` sends `(A,B,C)` to `(V,U,D)`. -/
theorem cavityChangeMatrix_mulVec_cavityVector
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) :
    cavityChangeMatrix.mulVec (cavityVector path s) =
      ![cavityV path s, cavityU path s, cavityD path s] := by
  ext i
  fin_cases i <;>
    simp [cavityChangeMatrix, cavityVector, cavityV, cavityU, cavityD,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- Explicit `(V,U,D)` form of the vector remainder. -/
theorem cavityChangeMatrix_mulVec_cavityRemainder
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) :
    cavityChangeMatrix.mulVec (cavityRemainder path s) =
      ![
        cavityV path s -
          s * β ^ 2 *
            (cavityZeta q (rsR β h) * cavityU path s +
              cavityKappa q (rsR β h) * cavityV path s) -
          (1 / (N : ℝ)) * cavityZeta q (rsR β h),
        cavityU path s -
          s * β ^ 2 * cavityKappa q (rsR β h) * cavityU path s -
          (1 / (N : ℝ)) * cavityKappa q (rsR β h),
        cavityD path s -
          s * β ^ 2 * (1 - 2 * q + rsR β h) * cavityD path s -
          (1 / (N : ℝ)) * (1 - 2 * q + rsR β h)
      ] := by
  have hmul :
      cavityChangeMatrix.mulVec
          ((cavityMatrix β q (rsR β h)).mulVec (cavityVector path s)) =
        (cavityModeMatrix β q (rsR β h)).mulVec
          ![cavityV path s, cavityU path s, cavityD path s] := by
    calc
      cavityChangeMatrix.mulVec
          ((cavityMatrix β q (rsR β h)).mulVec (cavityVector path s)) =
          (cavityChangeMatrix * cavityMatrix β q (rsR β h)).mulVec
            (cavityVector path s) := by
              rw [Matrix.mulVec_mulVec]
      _ = (cavityModeMatrix β q (rsR β h) * cavityChangeMatrix).mulVec
            (cavityVector path s) := by
              rw [cavityChangeMatrix_mul_cavityMatrix]
      _ = (cavityModeMatrix β q (rsR β h)).mulVec
            (cavityChangeMatrix.mulVec (cavityVector path s)) := by
              rw [Matrix.mulVec_mulVec]
      _ = (cavityModeMatrix β q (rsR β h)).mulVec
            ![cavityV path s, cavityU path s, cavityD path s] := by
              rw [cavityChangeMatrix_mulVec_cavityVector]
  have hmode :
      (cavityModeMatrix β q (rsR β h)).mulVec
          ![cavityV path s, cavityU path s, cavityD path s] =
        ![β ^ 2 * cavityKappa q (rsR β h) * cavityV path s +
            β ^ 2 * cavityZeta q (rsR β h) * cavityU path s,
          β ^ 2 * cavityKappa q (rsR β h) * cavityU path s,
          β ^ 2 * (1 - 2 * q + rsR β h) * cavityD path s] := by
    ext i
    fin_cases i <;>
      simp [cavityModeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [cavityRemainder, Matrix.mulVec_sub, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hmul,
    hmode,
    cavityChangeMatrix_mulVec_cavityVector,
    cavityChangeMatrix_mulVec_theta]
  ext i
  fin_cases i <;>
    simp [cavityModeSource, smul_eq_mul] <;>
    ring

/-- At the RS fixed point the replicon coefficient is the AT parameter. -/
theorem beta_sq_mul_repliconCoefficient_eq_atParameter
    {β h q : ℝ} (hq : q = rsQ β h) :
    β ^ 2 * (1 - 2 * q + rsR β h) = atParameter β h := by
  subst q
  exact (atParameter_eq_beta_sq_mul_one_sub_two_q_add_r β h).symm

/-- The fourth RS moment is nonnegative. -/
theorem rsR_nonneg (β h : ℝ) : 0 ≤ rsR β h := by
  rw [rsR_eq_gaussian_tanh_fourth]
  unfold standardGaussianExpectation
  exact integral_nonneg fun z ↦ by positivity

/-- The fourth RS moment is at most the second RS moment. -/
theorem rsR_le_rsQ {β h : ℝ} (hh : 0 < h) : rsR β h ≤ rsQ β h := by
  let X : ℝ → ℝ := fun z ↦ h + β * Real.sqrt (rsQ β h) * z
  have htanh : Continuous (fun x : ℝ ↦ Real.tanh x) := by
    simp_rw [Real.tanh_eq]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  have hInt2 : Integrable (fun z ↦ Real.tanh (X z) ^ 2) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  have hInt4 : Integrable (fun z ↦ Real.tanh (X z) ^ 4) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 4 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  rw [rsR_eq_gaussian_tanh_fourth]
  calc
    standardGaussianExpectation (fun z ↦ Real.tanh (X z) ^ 4) ≤
        standardGaussianExpectation (fun z ↦ Real.tanh (X z) ^ 2) := by
      unfold standardGaussianExpectation
      apply integral_mono_ae hInt4 hInt2
      filter_upwards [] with z
      have ht : |Real.tanh (X z)| ≤ 1 := (Real.abs_tanh_lt_one _).le
      have ht2' := mul_self_le_mul_self (abs_nonneg (Real.tanh (X z))) ht
      have ht2 : Real.tanh (X z) ^ 2 ≤ 1 := by
        simpa [pow_two] using ht2'
      nlinarith [sq_nonneg (Real.tanh (X z)),
        mul_nonneg (sq_nonneg (Real.tanh (X z))) (sub_nonneg.mpr ht2)]
    _ = rsQ β h := (rsQ_eq_gaussian_tanh_sq hh).symm

/-- The cubic overlap moment is nonnegative. -/
theorem thirdMoment_nonneg
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) :
    0 ≤ thirdMoment path s := by
  unfold thirdMoment quenchedReplicaAverage replicaGibbsAverage
  apply integral_nonneg
  intro ω
  apply Finset.sum_nonneg
  intro σs _
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ ↦
      SpinGlass.gibbs_pmf_nonneg (N := N) (H := fullPathHamiltonian path s ω)
        (σs i))
    (by positivity)

/-! ## Inverting the fixed mode change -/

/-- The matrix displayed in `ATDefs` really is the inverse mode change. -/
theorem cavityChangeMatrixInv_mul_cavityChangeMatrix :
    cavityChangeMatrixInv * cavityChangeMatrix =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cavityChangeMatrixInv, cavityChangeMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Explicit action of the inverse mode change. -/
theorem cavityChangeMatrixInv_mulVec_eq (x : Fin 3 → ℝ) :
    cavityChangeMatrixInv.mulVec x =
      ![-x 0 - 2 * x 1 + 3 * x 2,
        -x 0 - (3 / 2 : ℝ) * x 1 + (3 / 2 : ℝ) * x 2,
        -x 0 - x 1 + x 2] := by
  ext i
  fin_cases i <;>
    simp [cavityChangeMatrixInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The inverse change of basis costs at most a factor `6` in the sup norm. -/
theorem cavityChangeMatrixInv_mulVec_norm_le (x : Fin 3 → ℝ) :
    ‖cavityChangeMatrixInv.mulVec x‖ ≤ 6 * ‖x‖ := by
  rw [cavityChangeMatrixInv_mulVec_eq,
    pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))]
  have h0 : ‖x 0‖ ≤ ‖x‖ := norm_le_pi_norm x 0
  have h1 : ‖x 1‖ ≤ ‖x‖ := norm_le_pi_norm x 1
  have h2 : ‖x 2‖ ≤ ‖x‖ := norm_le_pi_norm x 2
  intro i
  fin_cases i
  · calc
      ‖-x 0 - 2 * x 1 + 3 * x 2‖ ≤
          ‖-x 0 - 2 * x 1‖ + ‖3 * x 2‖ := norm_add_le _ _
      _ ≤ (‖-x 0‖ + ‖2 * x 1‖) + ‖3 * x 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖x 0‖ + 2 * ‖x 1‖ + 3 * ‖x 2‖ := by
        simp [norm_mul]
      _ ≤ 6 * ‖x‖ := by linarith
  · calc
      ‖-x 0 - (3 / 2 : ℝ) * x 1 + (3 / 2 : ℝ) * x 2‖ ≤
          ‖-x 0 - (3 / 2 : ℝ) * x 1‖ + ‖(3 / 2 : ℝ) * x 2‖ :=
        norm_add_le _ _
      _ ≤ (‖-x 0‖ + ‖(3 / 2 : ℝ) * x 1‖) +
          ‖(3 / 2 : ℝ) * x 2‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖x 0‖ + (3 / 2 : ℝ) * ‖x 1‖ + (3 / 2 : ℝ) * ‖x 2‖ := by
        simp [norm_mul]
      _ ≤ 6 * ‖x‖ := by linarith [norm_nonneg x]
  · calc
      ‖-x 0 - x 1 + x 2‖ ≤ ‖-x 0 - x 1‖ + ‖x 2‖ := norm_add_le _ _
      _ ≤ (‖-x 0‖ + ‖x 1‖) + ‖x 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖x 0‖ + ‖x 1‖ + ‖x 2‖ := by simp
      _ ≤ 6 * ‖x‖ := by linarith [norm_nonneg x]

/-- Recover the original remainder from the three scalar mode remainders. -/
theorem cavityRemainder_eq_inverseModeRemainder
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) :
    cavityRemainder path s =
      cavityChangeMatrixInv.mulVec
        (cavityChangeMatrix.mulVec (cavityRemainder path s)) := by
  calc
    cavityRemainder path s =
        (1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec (cavityRemainder path s) := by
      simp
    _ = (cavityChangeMatrixInv * cavityChangeMatrix).mulVec
          (cavityRemainder path s) := by
      rw [cavityChangeMatrixInv_mul_cavityChangeMatrix]
    _ = cavityChangeMatrixInv.mulVec
          (cavityChangeMatrix.mulVec (cavityRemainder path s)) := by
      rw [Matrix.mulVec_mulVec]

/-! ## The analytic last-spin estimate -/

/--
Mode version of the cavity estimate.  By
`cavityChangeMatrix_mulVec_cavityRemainder`, this is exactly the three scalar
relations

  V_s = s β² (ζ U_s + κ V_s) + ζ/N + O(η),
  U_s = s β² κ U_s + κ/N + O(η),
  D_s = s β² (1-2q+r) D_s + (1-2q+r)/N + O(η).

At `q = rsQ β h`, the third coefficient satisfies
`β² (1-2q+r) = atParameter β h`.
-/
def HasCavityModeRemainderBound
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {K : Set (ℝ × ℝ)}
    (_data : UniformATData K) (C : ℝ) : Prop :=
  0 < C ∧
    ∀ {N : ℕ}, 0 < N → ∀ {β h q s : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ path : RSSmartPathDisorder Ω N β h q,
        ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ ≤
          C * cavityErrorScale path s

/--
This is the one genuinely analytic block: the last-spin cavity interpolation.
Its proof is the appendix argument:

* write `Q = Q⁻ + ε₁ε₂/N`;
* construct `ν_{s,u}`;
* prove the Gaussian derivative identity;
* obtain the uniform cubic-moment bound by backward Gronwall;
* replace the endpoint quadratic products;
* apply the derivative identity twice to `G_A,G_B,G_C`;
* use the three-valued edge rule at `u = 0`;
* control the diagonal `E_A,E_B,E_C` terms.

The conclusion is exactly the norm form of the three scalar estimates above.
-/
theorem cavityModeRemainder_bound_from_lastSpin
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ C : ℝ, HasCavityModeRemainderBound (Ω := Ω) data C := by
  let C : ℝ :=
    360000 * (1 + data.βmax ^ 4) * Real.exp (64 * data.βmax ^ 2)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro N hN β h q s hK hq hs path
    have hβ : 0 < β := data.β_pos (β, h) hK
    have hh : 0 < h := data.h_pos (β, h) hK
    have hβmax : β ≤ data.βmax := data.β_bound (β, h) hK
    have hβsq : β ^ 2 ≤ data.βmax ^ 2 := by
      have hp : 0 ≤ (data.βmax - β) * (data.βmax + β) :=
        mul_nonneg (sub_nonneg.mpr hβmax) (add_nonneg data.βmax_pos.le hβ.le)
      nlinarith
    have hβfour : β ^ 4 ≤ data.βmax ^ 4 := by
      have hp :
          0 ≤ (data.βmax ^ 2 - β ^ 2) * (data.βmax ^ 2 + β ^ 2) :=
        mul_nonneg (sub_nonneg.mpr hβsq)
          (add_nonneg (sq_nonneg data.βmax) (sq_nonneg β))
      nlinarith
    have hexp :
        Real.exp (64 * β ^ 2) ≤ Real.exp (64 * data.βmax ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hqI : q ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hq]
      exact rsQ_mem_Icc β h
    have hrI : rsR β h ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact rsR_nonneg β h
      · calc
          rsR β h ≤ rsQ β h := rsR_le_rsQ hh
          _ = q := hq.symm
          _ ≤ 1 := hqI.2
    have hscale : 0 ≤ cavityErrorScale path s := by
      unfold cavityErrorScale
      have ht : 0 ≤ thirdMoment path s := thirdMoment_nonneg path s
      positivity
    calc
      ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ ≤
          360000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) *
            cavityErrorScale path s :=
        CavityEstimates.cavityModeRemainder_norm_bound path hN hh hq hqI hrI hs
      _ ≤ C * cavityErrorScale path s := by
        dsimp [C]
        gcongr

/-! ## Final cavity proposition -/

/--
The mode estimate implies the `ATDefs.HasCavityRemainderBound` estimate.
The loss of the harmless numerical factor `6` is only the norm of the fixed
inverse change of basis.
-/
theorem exists_hasCavityRemainderBound
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ C : ℝ, HasCavityRemainderBound (Ω := Ω) data C := by
  obtain ⟨C, hCpos, hC⟩ :=
    cavityModeRemainder_bound_from_lastSpin (Ω := Ω) data
  refine ⟨6 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro N hN β h q s hK hq hs path
  rw [cavityRemainder_eq_inverseModeRemainder]
  calc
    ‖cavityChangeMatrixInv.mulVec
        (cavityChangeMatrix.mulVec (cavityRemainder path s))‖ ≤
        6 * ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ :=
      cavityChangeMatrixInv_mulVec_norm_le _
    _ ≤ 6 * (C * cavityErrorScale path s) :=
      mul_le_mul_of_nonneg_left (hC hN hK hq hs path) (by norm_num)
    _ = (6 * C) * cavityErrorScale path s := by ring

/-! ## Pre-absorption estimate -/

/-- Uniform form of `A_s ≤ C_K / N + C_K * ν_s[|Q₁₂|^3]`. -/
def HasCavityPreAbsorptionBound
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {K : Set (ℝ × ℝ)}
    (_data : UniformATData K) (C : ℝ) : Prop :=
  0 < C ∧
    ∀ {N : ℕ}, 0 < N → ∀ {β h q s : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ path : RSSmartPathDisorder Ω N β h q,
        A path s ≤ C / (N : ℝ) + C * thirdMoment path s

/-- The cavity proposition and the strict AT gap imply the pre-absorption
bound for the centered-overlap second moment. -/
theorem exists_hasCavityPreAbsorptionBound
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ C : ℝ, HasCavityPreAbsorptionBound (Ω := Ω) data C := by
  obtain ⟨C, hCpos, hC⟩ :=
    cavityModeRemainder_bound_from_lastSpin (Ω := Ω) data
  let L : ℝ := (8 + C) / data.gap
  let M : ℝ := (8 * data.βmax ^ 2 * L + 8 + C) / data.gap
  let Cstar : ℝ := M + 5 * L
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos (by linarith) data.gap_pos
  have hMpos : 0 < M := by
    dsimp [M]
    apply div_pos _ data.gap_pos
    have hp : 0 ≤ 8 * data.βmax ^ 2 * L := by positivity
    linarith
  have hCstarpos : 0 < Cstar := by dsimp [Cstar]; positivity
  refine ⟨Cstar, hCstarpos, ?_⟩
  intro N hN β h q s hK hq hs path
  subst q
  have hβ : 0 < β := data.β_pos (β, h) hK
  have hh : 0 < h := data.h_pos (β, h) hK
  have hβmax : β ≤ data.βmax := data.β_bound (β, h) hK
  have hβsq : β ^ 2 ≤ data.βmax ^ 2 := by
    have hp : 0 ≤ (data.βmax - β) * (data.βmax + β) :=
      mul_nonneg (sub_nonneg.mpr hβmax) (add_nonneg data.βmax_pos.le hβ.le)
    nlinarith
  have hqIcc := rsQ_mem_Icc β h
  have hq0 : 0 ≤ rsQ β h := hqIcc.1
  have hq1 : rsQ β h ≤ 1 := hqIcc.2
  have hr0 : 0 ≤ rsR β h := rsR_nonneg β h
  have hrq : rsR β h ≤ rsQ β h := rsR_le_rsQ hh
  have hqSq : rsQ β h ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hqIcc.1 (sub_nonneg.mpr hqIcc.2)]
  have hκabs : |cavityKappa (rsQ β h) (rsR β h)| ≤ 8 := by
    rw [abs_le]
    constructor <;> simp only [cavityKappa] <;> linarith
  have hζabs : |cavityZeta (rsQ β h) (rsR β h)| ≤ 8 := by
    rw [abs_le]
    constructor <;> simp only [cavityZeta] <;> nlinarith
  have hcabs : |1 - 2 * rsQ β h + rsR β h| ≤ 8 := by
    rw [abs_le]
    constructor <;> linarith
  have hα0 : 0 ≤ atParameter β h := by
    rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
    exact mul_nonneg (sq_nonneg β)
      (by
        unfold standardGaussianExpectation
        exact integral_nonneg fun z ↦ by positivity)
  have hκLe :
      β ^ 2 * cavityKappa (rsQ β h) (rsR β h) ≤ atParameter β h := by
    rw [atParameter_eq_beta_sq_mul_one_sub_two_q_add_r]
    simp only [cavityKappa]
    have hp := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hrq)
    nlinarith
  have hAT : atParameter β h ≤ 1 - data.gap := data.strictAT (β, h) hK
  have hgapOne : data.gap ≤ 1 := by linarith
  have hdenκ :
      data.gap ≤ 1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h) := by
    by_cases hκ0 : 0 ≤ cavityKappa (rsQ β h) (rsR β h)
    · have hcoef0 : 0 ≤ β ^ 2 * cavityKappa (rsQ β h) (rsR β h) :=
        mul_nonneg (sq_nonneg β) hκ0
      have hscoef := mul_le_of_le_one_left hcoef0 hs.2
      nlinarith
    · have hterm : s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hs.1 (sq_nonneg β)) (le_of_not_ge hκ0)
      linarith
  have hdenD : data.gap ≤ 1 - s * atParameter β h := by
    have hsα := mul_le_of_le_one_left hα0 hs.2
    linarith
  have hN1 : 1 ≤ N := hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hinv0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hrpow : (N : ℝ) ^ (-(3 : ℝ) / 2) ≤ 1 / (N : ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hNreal
      (by norm_num : (-(3 : ℝ) / 2) ≤ -1)
    simpa [Real.rpow_neg_one, one_div] using hp
  have hthird0 : 0 ≤ thirdMoment path s := thirdMoment_nonneg path s
  have hE0 : 0 ≤ 1 / (N : ℝ) + thirdMoment path s := by positivity
  have hinvE : 1 / (N : ℝ) ≤ 1 / (N : ℝ) + thirdMoment path s := by linarith
  let R : Fin 3 → ℝ := cavityChangeMatrix.mulVec (cavityRemainder path s)
  have hRnorm : ‖R‖ ≤ C * (1 / (N : ℝ) + thirdMoment path s) := by
    calc
      ‖R‖ ≤ C * cavityErrorScale path s := hC hN hK rfl hs path
      _ ≤ C * (1 / (N : ℝ) + thirdMoment path s) := by
        apply mul_le_mul_of_nonneg_left _ hCpos.le
        unfold cavityErrorScale
        linarith
  have hRcomp (i : Fin 3) :
      |R i| ≤ C * (1 / (N : ℝ) + thirdMoment path s) := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm R i).trans hRnorm
  have hmode := cavityChangeMatrix_mulVec_cavityRemainder (s := s) path
  have hUeq :
      (1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * cavityU path s =
        (1 / (N : ℝ)) * cavityKappa (rsQ β h) (rsR β h) + R 1 := by
    have hc : R 1 = cavityU path s -
        s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h) * cavityU path s -
        (1 / (N : ℝ)) * cavityKappa (rsQ β h) (rsR β h) := by
      simpa [R] using congrFun hmode (1 : Fin 3)
    rw [hc]
    ring
  have hDeq :
      (1 - s * atParameter β h) * cavityD path s =
        (1 / (N : ℝ)) * (1 - 2 * rsQ β h + rsR β h) + R 2 := by
    have hc : R 2 = cavityD path s -
        s * β ^ 2 * (1 - 2 * rsQ β h + rsR β h) * cavityD path s -
        (1 / (N : ℝ)) * (1 - 2 * rsQ β h + rsR β h) := by
      simpa [R] using congrFun hmode (2 : Fin 3)
    rw [atParameter_eq_beta_sq_mul_one_sub_two_q_add_r, hc]
    ring
  have hVeq :
      (1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * cavityV path s =
        s * β ^ 2 * cavityZeta (rsQ β h) (rsR β h) * cavityU path s +
          (1 / (N : ℝ)) * cavityZeta (rsQ β h) (rsR β h) + R 0 := by
    have hc : R 0 = cavityV path s -
        s * β ^ 2 *
          (cavityZeta (rsQ β h) (rsR β h) * cavityU path s +
            cavityKappa (rsQ β h) (rsR β h) * cavityV path s) -
        (1 / (N : ℝ)) * cavityZeta (rsQ β h) (rsR β h) := by
      simpa [R] using congrFun hmode (0 : Fin 3)
    rw [hc]
    ring
  have hUgap : data.gap * |cavityU path s| ≤
      (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by
    calc
      data.gap * |cavityU path s| ≤
          (1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * |cavityU path s| :=
        mul_le_mul_of_nonneg_right hdenκ (abs_nonneg _)
      _ = |(1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * cavityU path s| := by
        rw [abs_mul, abs_of_nonneg (le_trans data.gap_pos.le hdenκ)]
      _ = |(1 / (N : ℝ)) * cavityKappa (rsQ β h) (rsR β h) + R 1| := by rw [hUeq]
      _ ≤ |(1 / (N : ℝ)) * cavityKappa (rsQ β h) (rsR β h)| + |R 1| := abs_add_le _ _
      _ ≤ (1 / (N : ℝ)) * 8 + C * (1 / (N : ℝ) + thirdMoment path s) := by
        rw [abs_mul, abs_of_nonneg hinv0]
        exact add_le_add (mul_le_mul_of_nonneg_left hκabs hinv0) (hRcomp 1)
      _ ≤ (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by nlinarith
  have hU : |cavityU path s| ≤ L * (1 / (N : ℝ) + thirdMoment path s) := by
    have hswap : |cavityU path s| * data.gap ≤
        (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by
      simpa only [mul_comm] using hUgap
    have hd := (le_div_iff₀ data.gap_pos).2 hswap
    calc
      |cavityU path s| ≤ ((8 + C) * (1 / (N : ℝ) + thirdMoment path s)) / data.gap := hd
      _ = L * (1 / (N : ℝ) + thirdMoment path s) := by dsimp [L]; field_simp
  have hDgap : data.gap * |cavityD path s| ≤
      (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by
    calc
      data.gap * |cavityD path s| ≤ (1 - s * atParameter β h) * |cavityD path s| :=
        mul_le_mul_of_nonneg_right hdenD (abs_nonneg _)
      _ = |(1 - s * atParameter β h) * cavityD path s| := by
        rw [abs_mul, abs_of_nonneg (le_trans data.gap_pos.le hdenD)]
      _ = |(1 / (N : ℝ)) * (1 - 2 * rsQ β h + rsR β h) + R 2| := by rw [hDeq]
      _ ≤ |(1 / (N : ℝ)) * (1 - 2 * rsQ β h + rsR β h)| + |R 2| := abs_add_le _ _
      _ ≤ (1 / (N : ℝ)) * 8 + C * (1 / (N : ℝ) + thirdMoment path s) := by
        rw [abs_mul, abs_of_nonneg hinv0]
        exact add_le_add (mul_le_mul_of_nonneg_left hcabs hinv0) (hRcomp 2)
      _ ≤ (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by nlinarith
  have hD : |cavityD path s| ≤ L * (1 / (N : ℝ) + thirdMoment path s) := by
    have hswap : |cavityD path s| * data.gap ≤
        (8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by
      simpa only [mul_comm] using hDgap
    have hd := (le_div_iff₀ data.gap_pos).2 hswap
    calc
      |cavityD path s| ≤ ((8 + C) * (1 / (N : ℝ) + thirdMoment path s)) / data.gap := hd
      _ = L * (1 / (N : ℝ) + thirdMoment path s) := by dsimp [L]; field_simp
  have hcoupling :
      |s * β ^ 2 * cavityZeta (rsQ β h) (rsR β h) * cavityU path s| ≤
        8 * data.βmax ^ 2 * L * (1 / (N : ℝ) + thirdMoment path s) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg (sq_nonneg β)]
    calc
      s * β ^ 2 * |cavityZeta (rsQ β h) (rsR β h)| * |cavityU path s| ≤
          1 * data.βmax ^ 2 * 8 * (L * (1 / (N : ℝ) + thirdMoment path s)) := by
        gcongr
        exact hs.2
      _ = 8 * data.βmax ^ 2 * L * (1 / (N : ℝ) + thirdMoment path s) := by ring
  have hVgap : data.gap * |cavityV path s| ≤
      (8 * data.βmax ^ 2 * L + 8 + C) * (1 / (N : ℝ) + thirdMoment path s) := by
    calc
      data.gap * |cavityV path s| ≤
          (1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * |cavityV path s| :=
        mul_le_mul_of_nonneg_right hdenκ (abs_nonneg _)
      _ = |(1 - s * β ^ 2 * cavityKappa (rsQ β h) (rsR β h)) * cavityV path s| := by
        rw [abs_mul, abs_of_nonneg (le_trans data.gap_pos.le hdenκ)]
      _ = |s * β ^ 2 * cavityZeta (rsQ β h) (rsR β h) * cavityU path s +
            (1 / (N : ℝ)) * cavityZeta (rsQ β h) (rsR β h) + R 0| := by rw [hVeq]
      _ ≤ |s * β ^ 2 * cavityZeta (rsQ β h) (rsR β h) * cavityU path s| +
            |(1 / (N : ℝ)) * cavityZeta (rsQ β h) (rsR β h)| + |R 0| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 8 * data.βmax ^ 2 * L * (1 / (N : ℝ) + thirdMoment path s) +
          (1 / (N : ℝ)) * 8 + C * (1 / (N : ℝ) + thirdMoment path s) := by
        have hz : |(1 / (N : ℝ)) * cavityZeta (rsQ β h) (rsR β h)| ≤
            (1 / (N : ℝ)) * 8 := by
          rw [abs_mul, abs_of_nonneg hinv0]
          exact mul_le_mul_of_nonneg_left hζabs hinv0
        exact add_le_add (add_le_add hcoupling hz) (hRcomp 0)
      _ ≤ (8 * data.βmax ^ 2 * L + 8 + C) *
          (1 / (N : ℝ) + thirdMoment path s) := by nlinarith
  have hV : |cavityV path s| ≤ M * (1 / (N : ℝ) + thirdMoment path s) := by
    have hswap : |cavityV path s| * data.gap ≤
        (8 * data.βmax ^ 2 * L + 8 + C) *
          (1 / (N : ℝ) + thirdMoment path s) := by
      simpa only [mul_comm] using hVgap
    have hd := (le_div_iff₀ data.gap_pos).2 hswap
    calc
      |cavityV path s| ≤ ((8 * data.βmax ^ 2 * L + 8 + C) *
          (1 / (N : ℝ) + thirdMoment path s)) / data.gap := hd
      _ = M * (1 / (N : ℝ) + thirdMoment path s) := by dsimp [M]; field_simp
  have hAeq : A path s = -cavityV path s - 2 * cavityU path s + 3 * cavityD path s := by
    simp only [cavityV, cavityU, cavityD]
    ring
  calc
    A path s ≤ |A path s| := le_abs_self _
    _ = |-cavityV path s - 2 * cavityU path s + 3 * cavityD path s| := by rw [hAeq]
    _ ≤ |cavityV path s| + 2 * |cavityU path s| + 3 * |cavityD path s| := by
      calc
        _ ≤ |-cavityV path s - 2 * cavityU path s| + |3 * cavityD path s| := abs_add_le _ _
        _ ≤ (|-cavityV path s| + |2 * cavityU path s|) + |3 * cavityD path s| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by simp [abs_mul]
    _ ≤ (M + 5 * L) * (1 / (N : ℝ) + thirdMoment path s) := by nlinarith
    _ = Cstar / (N : ℝ) + Cstar * thirdMoment path s := by
      dsimp [Cstar]
      ring

end SpinGlass.AT
