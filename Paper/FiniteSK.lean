module

public import Paper.Targets
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Finite Sherrington--Kirkpatrick model integrability

The concrete product Gaussian coupling law has probability mass one.
Every Hamiltonian, every exponential weight, the partition function, and
its logarithm are genuinely integrable, including the harmless size-zero
case. Thus the finite free-energy expectations do not use Bochner's junk
value for a nonintegrable function.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper

instance skCouplingLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (skCouplingLaw n) := by
  unfold skCouplingLaw
  infer_instance

/-- A Gaussian coupling coordinate is integrable under the independent product law. -/
theorem integrable_skCoupling_coordinate {n : ℕ} (ij : SKEdge n) :
    Integrable (fun g : SKCouplings n => g ij) (skCouplingLaw n) := by
  apply integrable_eval
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl

/-- The actual finite SK Hamiltonian is an integrable affine Gaussian function. -/
theorem integrable_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Integrable (fun g => skHamiltonian β h g σ) (skCouplingLaw n) := by
  unfold skHamiltonian
  apply Integrable.add
  · apply Integrable.const_mul
    apply integrable_finsetSum
    intro ij hij
    exact ((integrable_skCoupling_coordinate ij).mul_const
      (spinSign (σ ij.val.1))).mul_const (spinSign (σ ij.val.2))
  · exact integrable_const _

/-- An exponential Hamiltonian factors into independent Gaussian exponential moments. -/
theorem integrable_exp_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Integrable (fun g => Real.exp (skHamiltonian β h g σ)) (skCouplingLaw n) := by
  let a : SKEdge n → ℝ := fun ij =>
    β / Real.sqrt (n : ℝ) * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)
  let b : ℝ := h * ∑ i : Fin n, spinSign (σ i)
  have hprod : Integrable (fun g : SKCouplings n => ∏ ij, Real.exp (a ij * g ij))
      (skCouplingLaw n) := by
    exact Integrable.fintype_prod (fun ij =>
      integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a ij))
  have heq : (fun g : SKCouplings n => Real.exp (skHamiltonian β h g σ)) =
      fun g => Real.exp b * ∏ ij, Real.exp (a ij * g ij) := by
    funext g
    have hH : skHamiltonian β h g σ = b + ∑ ij, a ij * g ij := by
      unfold skHamiltonian a b
      rw [Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    rw [hH, Real.exp_add, Real.exp_sum]
  rw [heq]
  exact hprod.const_mul _

theorem continuous_skHamiltonian {n : ℕ} (β h : ℝ) (σ : SKConfiguration n) :
    Continuous (fun g => skHamiltonian β h g σ) := by
  unfold skHamiltonian
  fun_prop

/-- The finite partition function is positive because every exponential weight is positive. -/
theorem skPartitionFunction_pos {n : ℕ} (β h : ℝ) (g : SKCouplings n) :
    0 < skPartitionFunction β h g := by
  unfold skPartitionFunction
  exact Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Each single exponential weight is bounded by the full partition function. -/
theorem exp_skHamiltonian_le_partition {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : Real.exp (skHamiltonian β h g σ) ≤ skPartitionFunction β h g := by
  exact Finset.single_le_sum (fun τ _ => (Real.exp_pos _).le) (Finset.mem_univ σ)

/-- The logarithm of the partition function dominates each Hamiltonian. -/
theorem skHamiltonian_le_log_partition {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : skHamiltonian β h g σ ≤ Real.log (skPartitionFunction β h g) := by
  have hh := Real.log_le_log (Real.exp_pos (skHamiltonian β h g σ))
    (exp_skHamiltonian_le_partition β h g σ)
  simpa only [Real.log_exp] using hh

/-- A finite sum of integrable exponential Hamiltonians is integrable. -/
theorem integrable_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Integrable (fun g : SKCouplings n => skPartitionFunction β h g) (skCouplingLaw n) := by
  unfold skPartitionFunction
  apply integrable_finsetSum
  intro σ hσ
  exact integrable_exp_skHamiltonian β h σ

theorem continuous_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Continuous (fun g : SKCouplings n => skPartitionFunction β h g) := by
  unfold skPartitionFunction
  apply continuous_finsetSum
  intro σ hσ
  exact Real.continuous_exp.comp (continuous_skHamiltonian β h σ)

/-- A simple domination sufficient for logarithmic integrability. Any fixed
configuration can be used in the lower bound. -/
theorem abs_log_skPartitionFunction_le {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) :
    |Real.log (skPartitionFunction β h g)| ≤ skPartitionFunction β h g + |skHamiltonian β h g σ| := by
  have hZ := skPartitionFunction_pos β h g
  have hupper := Real.log_le_sub_one_of_pos hZ
  have hlower := skHamiltonian_le_log_partition β h g σ
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (skHamiltonian β h g σ)]
  · linarith [abs_nonneg (skHamiltonian β h g σ)]

/-- The concrete finite free-energy integrand is genuinely integrable for all parameters. -/
theorem integrable_log_skPartitionFunction {n : ℕ} (β h : ℝ) :
    Integrable (fun g : SKCouplings n => Real.log (skPartitionFunction β h g))
      (skCouplingLaw n) := by
  let σ : SKConfiguration n := fun _ => true
  have hdom := (integrable_skPartitionFunction (n := n) β h).add
    (integrable_skHamiltonian β h σ).abs
  apply hdom.mono'
  · exact ((continuous_skPartitionFunction β h).log
      (fun g => ne_of_gt (skPartitionFunction_pos β h g))).aestronglyMeasurable
  · filter_upwards [] with g
    rw [Real.norm_eq_abs]
    exact abs_log_skPartitionFunction_le β h g σ

/-- At size zero, the Hamiltonian vanishes under the totalized real normalization. -/
@[simp] theorem skHamiltonian_zero (β h : ℝ) (g : SKCouplings 0) (σ : SKConfiguration 0) :
    skHamiltonian β h g σ = 0 := by
  simp [skHamiltonian]

/-- There is one configuration at size zero, and its exponential weight is one. -/
@[simp] theorem skPartitionFunction_zero (β h : ℝ) (g : SKCouplings 0) :
    skPartitionFunction β h g = 1 := by
  simp [skPartitionFunction]

/-- The finite free energy has its explicitly stipulated harmless zero-size value. -/
@[simp] theorem finiteSKFreeEnergy_zero (β h : ℝ) : finiteSKFreeEnergy β h 0 = 0 := by
  simp [finiteSKFreeEnergy]

end Paper
