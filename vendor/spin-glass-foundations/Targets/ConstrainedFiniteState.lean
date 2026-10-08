module

/-
# Finite-state calculus for the second-interpolation terminal

The actual constrained terminal is identified with RSAT's general finite-state
log partition. Its first and mixed second disorder derivatives are therefore
Gibbs means and covariances. The upstream finite-state formulas, not its
RS-only final comparison theorem, are used here.
-/
public import Targets.TalagrandSecondInterpolation
public import Lemmas.GuerraTalagrand.Bound.Comparison

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ContDiff

namespace SpinGlass.Targets

/-- The disorder of a pair state is the sum of its two replica energies. -/
noncomputable def pairDisorderCLM (n : ℕ) (u : ℝ) :
    EnergySpace n →L[ℝ] AT.GTStateSpace (AT.ConstrainedPair n u) :=
  AT.gtCoefficientCLM (fun p => std_basis n p.1.1 + std_basis n p.1.2)

@[simp] theorem pairDisorderCLM_apply (n : ℕ) (u : ℝ) (U : EnergySpace n)
    (p : AT.ConstrainedPair n u) : pairDisorderCLM n u U p = U p.1.1 + U p.1.2 := by
  simp only [pairDisorderCLM, AT.gtCoefficientCLM_apply, inner_add_left,
    inner_std_basis_apply]

/-- The physical fields supply the deterministic finite-state potential. -/
noncomputable def pairFieldPotential (n : ℕ) (u : ℝ) (x y : Fin n → ℝ)
    (p : AT.ConstrainedPair n u) : ℝ :=
  (∑ i, spin n p.1.1 i * x i) + ∑ i, spin n p.1.2 i * y i

/-- Exact bridge, with the positive-Hamiltonian convention of Talagrand. -/
theorem constrainedPairFieldBase_eq_gtStateLogPartition (n : ℕ) (U : EnergySpace n)
    (u : ℝ) (x y : Fin n → ℝ) :
    constrainedPairFieldBase n U u x y =
      AT.gtStateLogPartition (pairFieldPotential n u x y) (pairDisorderCLM n u U) := by
  classical
  unfold constrainedPairFieldBase AT.gtStateLogPartition AT.gtStatePartition
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : Config n × Config n =>
    if overlap n p.1 p.2 = u then
      Real.exp ((U p.1 + ∑ i, spin n p.1 i * x i) + (U p.2 + ∑ i, spin n p.2 i * y i)) else 0)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun p : Config n × Config n => overlap n p.1 p.2 = u)
    (Finset.univ.filter fun p : Config n × Config n => overlap n p.1 p.2 = u) (by simp)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [pairDisorderCLM_apply, pairFieldPotential]
  congr 1
  ring

/-- Gibbs weights on attainable constrained pairs, without indicator junk values. -/
noncomputable def constrainedPairGibbs (n : ℕ) (U : EnergySpace n) (u : ℝ)
    (x y : Fin n → ℝ) (p : AT.ConstrainedPair n u) : ℝ :=
  AT.gtStateGibbs (pairFieldPotential n u x y) (pairDisorderCLM n u U) p

theorem constrainedPairGibbs_nonneg (n : ℕ) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) (p : AT.ConstrainedPair n u) :
    0 ≤ constrainedPairGibbs n U u x y p := AT.gtStateGibbs_nonneg _ _ _

theorem sum_constrainedPairGibbs (n : ℕ) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    ∑ p, constrainedPairGibbs n U u x y p = 1 := AT.sum_gtStateGibbs _ _

theorem contDiff_constrainedPairFieldBase (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun U => constrainedPairFieldBase n U u x y) := by
  simp only [constrainedPairFieldBase_eq_gtStateLogPartition]
  exact (AT.contDiff_gtStateLogPartition _).comp (pairDisorderCLM n u).contDiff

/-- The first disorder derivative is a mean of the pair energy direction. -/
theorem hasDerivAt_constrainedPairFieldBase (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (U V : EnergySpace n)
    (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => constrainedPairFieldBase n (U + b • V) u x y)
      (∑ p, constrainedPairGibbs n (U + a • V) u x y p * (V p.1.1 + V p.1.2)) a := by
  have hlin := (pairDisorderCLM n u).hasFDerivAt.comp_hasDerivAt a
    (((hasDerivAt_id a).smul_const V).const_add U)
  have H := ((AT.contDiff_gtStateLogPartition (pairFieldPotential n u x y)).differentiable
    (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt a hlin
  simpa only [constrainedPairFieldBase_eq_gtStateLogPartition,
    AT.fderiv_gtStateLogPartition_apply, pairDisorderCLM_apply, constrainedPairGibbs,
    Function.comp_apply, id_eq, one_smul] using! H

/-- Differentiating one actual constrained Gibbs weight reuses the finite-state
Gibbs derivative; its centered direction is bounded on this finite state space. -/
theorem hasDerivAt_constrainedPairGibbs (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (U V : EnergySpace n)
    (x y : Fin n → ℝ) (a : ℝ) (p : AT.ConstrainedPair n u) :
    HasDerivAt (fun b => constrainedPairGibbs n (U + b • V) u x y p)
      (constrainedPairGibbs n (U + a • V) u x y p *
        ((V p.1.1 + V p.1.2) - ∑ q, constrainedPairGibbs n (U + a • V) u x y q *
          (V q.1.1 + V q.1.2))) a := by
  have hlin := (pairDisorderCLM n u).hasFDerivAt.comp_hasDerivAt a
    (((hasDerivAt_id a).smul_const V).const_add U)
  have H := ((AT.contDiff_gtStateGibbs (pairFieldPotential n u x y) p).differentiable
    (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt a hlin
  simpa only [AT.fderiv_gtStateGibbs_apply, pairDisorderCLM_apply, constrainedPairGibbs,
    Function.comp_apply, id_eq, one_smul] using! H

/-- The derivative of a Gibbs mean is its covariance with the pair energy direction. -/
theorem hasDerivAt_constrainedPairMean (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (U V : EnergySpace n)
    (x y : Fin n → ℝ) (F : AT.ConstrainedPair n u → ℝ) (a : ℝ) :
    HasDerivAt (fun b => ∑ p, constrainedPairGibbs n (U + b • V) u x y p * F p)
      ((∑ p, constrainedPairGibbs n (U + a • V) u x y p * F p * (V p.1.1 + V p.1.2)) -
        (∑ p, constrainedPairGibbs n (U + a • V) u x y p * F p) *
        (∑ p, constrainedPairGibbs n (U + a • V) u x y p * (V p.1.1 + V p.1.2))) a := by
  classical
  have H := HasDerivAt.sum (u := Finset.univ) (fun p _ =>
    (hasDerivAt_constrainedPairGibbs n u U V x y a p).mul_const (F p))
  have he : (∑ p, constrainedPairGibbs n (U + a • V) u x y p *
      ((V p.1.1 + V p.1.2) - ∑ q, constrainedPairGibbs n (U + a • V) u x y q *
        (V q.1.1 + V q.1.2)) * F p) =
      (∑ p, constrainedPairGibbs n (U + a • V) u x y p * F p * (V p.1.1 + V p.1.2)) -
        (∑ p, constrainedPairGibbs n (U + a • V) u x y p * F p) *
        (∑ p, constrainedPairGibbs n (U + a • V) u x y p * (V p.1.1 + V p.1.2)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at H
  have hf : (∑ p, fun b : ℝ => constrainedPairGibbs n (U + b • V) u x y p * F p) =
      fun b : ℝ => ∑ p, constrainedPairGibbs n (U + b • V) u x y p * F p := by
    funext b
    simp
  rw [hf] at H
  exact H

/-- An actual mixed second derivative of the constrained terminal, not a formal
candidate expression. This supplies the base case for the nested Hessian induction. -/
theorem hasDerivAt_constrainedPairFieldBase_second (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (U V W : EnergySpace n)
    (x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => deriv (fun b : ℝ => constrainedPairFieldBase n (U + a • W + b • V) u x y) 0)
      ((∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2)) -
        (∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)) *
        (∑ p, constrainedPairGibbs n U u x y p * (W p.1.1 + W p.1.2))) 0 := by
  have he (a : ℝ) := (hasDerivAt_constrainedPairFieldBase n u (U + a • W) V x y 0).deriv
  simp only [zero_smul, add_zero] at he
  simp only [he]
  simpa only [zero_smul, add_zero] using
    hasDerivAt_constrainedPairMean n u U W x y (fun p => V p.1.1 + V p.1.2) 0

/-- Mixed directional Hessian of the actual constrained terminal. -/
noncomputable def constrainedPairSecond (n : ℕ) (u : ℝ) (U V W : EnergySpace n)
    (x y : Fin n → ℝ) : ℝ :=
  deriv (fun a : ℝ => deriv
    (fun b : ℝ => constrainedPairFieldBase n (U + a • W + b • V) u x y) 0) 0

theorem constrainedPairSecond_eq_covariance (n : ℕ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (U V W : EnergySpace n) (x y : Fin n → ℝ) :
    constrainedPairSecond n u U V W x y =
      (∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2)) -
        (∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)) *
        (∑ p, constrainedPairGibbs n U u x y p * (W p.1.1 + W p.1.2)) :=
  (hasDerivAt_constrainedPairFieldBase_second n u U V W x y).deriv

end SpinGlass.Targets
