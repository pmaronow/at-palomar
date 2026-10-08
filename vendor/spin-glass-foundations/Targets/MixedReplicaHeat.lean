module

public import Targets.MixedReplicaHessian

@[expose] public section

/-!
# Outer transport of the genuine mixed spatial heat terms

The replica split is retained at its original inner level while all later
mixed modes are integrated. This supplies the actual Hessian-plus-square
input to the Gaussian heat generator, including opposite sharing.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem mixedOuterMean_comp (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r s : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedOuterMean mode m v A (l + r) s (mixedOuterMean mode m v A l r G) =
      mixedOuterMean mode m v A l (r + s) G := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [mixedOuterMean_succ, ih]
    rw [show r + (s + 1) = (r + s) + 1 by omega, mixedOuterMean_succ]
    simp only [Nat.add_assoc]

theorem mixedOuterMean_add {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v A l r (fun x y => G x y + H x y) x y =
      mixedOuterMean mode m v A l r G x y + mixedOuterMean mode m v A l r H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul] using mixedOuterMean_sum hA h (fun _ => 1) mode m v hm hv l r x y

theorem mixedOuterMean_const_mul {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (c : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v A l r (fun x y => c * G x y) x y =
      c * mixedOuterMean mode m v A l r G x y := by
  simpa using mixedOuterMean_sum (I := Unit) hA (fun _ => hG) (fun _ => c) mode m v hm hv l r x y

theorem mixedReplicaBilinear_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) : CoupledBounded (mixedReplicaBilinear mode m v l r U u f g) := by
  apply CoupledBounded.sum
  intro p
  apply CoupledBounded.sum
  intro q
  have H := mixedConstrainedReplica_measurable_bound U u mode m v hm hv l r p q
  exact ((show CoupledBounded (fun x y => mixedConstrainedReplica mode m v l r U u x y p q)
    from ⟨H.1, 1, H.2⟩).mul (CoupledBounded.const (f p))).mul (CoupledBounded.const (g q))

theorem mixedConstrainedGibbs_diagonal_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (f g : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (fun x y => ∑ p, mixedConstrainedGibbs mode m v j U u x y p * f p * g p) := by
  apply CoupledBounded.sum
  intro p
  have H := mixedConstrainedGibbs_measurable_bound U u mode m v hm hv j p
  exact ((show CoupledBounded (fun x y => mixedConstrainedGibbs mode m v j U u x y p)
    from ⟨H.1, 1, H.2⟩).mul (CoupledBounded.const (f p))).mul (CoupledBounded.const (g p))

theorem mixedReplicaHessianExpression_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (f g : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (mixedReplicaHessianExpression mode m v j U u f g) := by
  exact ((mixedConstrainedGibbs_diagonal_bounded U u mode m v hm hv j f g).sub
    (mixedReplicaBilinear_bounded U u mode m v hm hv 0 j f g)).add
      (CoupledBounded.sum fun l : Fin j =>
        ((mixedReplicaBilinear_bounded U u mode m v hm hv l (j - l) f g).sub
          (mixedReplicaBilinear_bounded U u mode m v hm hv (l + 1) (j - (l + 1)) f g)).const_mul (m l))

theorem mixedOuterMean_replicaBilinear
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r s : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v (constrainedPairFieldBase n U u) (l + r) s
      (mixedReplicaBilinear mode m v l r U u f g) x y =
        mixedReplicaBilinear mode m v l (r + s) U u f g x y := by
  have he (t : ℕ) : mixedReplicaBilinear mode m v l t U u f g =
      mixedOuterMean mode m v (constrainedPairFieldBase n U u) l t
        (fun x y => (∑ p, mixedConstrainedGibbs mode m v l U u x y p * f p) *
          (∑ p, mixedConstrainedGibbs mode m v l U u x y p * g p)) := by
    funext x y
    exact (mixedConstrainedReplica_product_moment U u mode m v hm hv l t f g x y).symm
  rw [he r, he (r + s), mixedOuterMean_comp]

theorem mixedOuterMean_gibbs_diagonal
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v (constrainedPairFieldBase n U u) j r
      (fun x y => ∑ p, mixedConstrainedGibbs mode m v j U u x y p * f p * g p) x y =
      ∑ p, mixedConstrainedGibbs mode m v (j + r) U u x y p * f p * g p := by
  have he (t : ℕ) : (fun x y => ∑ p, mixedConstrainedGibbs mode m v t U u x y p * f p * g p) =
      mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
        (fun x y => ∑ p, constrainedPairGibbs n U u x y p * (f p * g p)) t := by
    funext x y
    simpa only [mul_assoc] using (mixedConstrainedGibbs_moment U u mode m v hm hv t
      (fun p => f p * g p) x y).symm
  change _ = (fun x y => ∑ p, mixedConstrainedGibbs mode m v (j + r) U u x y p * f p * g p) x y
  rw [he j, he (j + r), mixedOuterMean_cascadeD]

/-- All inner covariance splits retained after `r` additional mixed levels. -/
noncomputable def mixedReplicaTransportedHessian
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j r : ℕ) (U : EnergySpace n) (u : ℝ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (∑ p, mixedConstrainedGibbs mode m v (j + r) U u x y p * f p * g p) -
    mixedReplicaBilinear mode m v 0 (j + r) U u f g x y +
    ∑ l : Fin j, m l *
      (mixedReplicaBilinear mode m v l (j + r - l) U u f g x y -
        mixedReplicaBilinear mode m v (l + 1) (j + r - (l + 1)) U u f g x y)

theorem mixedOuterMean_replicaHessian
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v (constrainedPairFieldBase n U u) j r
      (mixedReplicaHessianExpression mode m v j U u f g) x y =
      mixedReplicaTransportedHessian mode m v j r U u f g x y := by
  have hA : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv 0 0
  have hb := fun l t => mixedReplicaBilinear_bounded U u mode m v hm hv l t f g
  have hd := mixedConstrainedGibbs_diagonal_bounded U u mode m v hm hv j f g
  have hs := fun l : Fin j => (hb l (j - l)).sub (hb (l + 1) (j - (l + 1)))
  have ht (l : ℕ) (hl : l ≤ j) :
      mixedOuterMean mode m v (constrainedPairFieldBase n U u) j r
        (mixedReplicaBilinear mode m v l (j - l) U u f g) x y =
      mixedReplicaBilinear mode m v l (j + r - l) U u f g x y := by
    convert mixedOuterMean_replicaBilinear U u mode m v hm hv l (j - l) r f g x y using 1 <;>
      congr 2 <;> omega
  unfold mixedReplicaHessianExpression
  rw [mixedOuterMean_add hA (hd.sub (hb 0 j))
    (CoupledBounded.sum fun l : Fin j => (hs l).const_mul (m l)) mode m v hm hv j r x y,
    mixedOuterMean_sub hA hd (hb 0 j) mode m v hm hv j r x y,
    mixedOuterMean_gibbs_diagonal U u mode m v hm hv j r f g x y,
    mixedOuterMean_sum hA hs (fun l : Fin j => m l) mode m v hm hv j r x y]
  have hz := ht 0 (Nat.zero_le j)
  simp only [Nat.sub_zero] at hz
  rw [hz]
  unfold mixedReplicaTransportedHessian
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [mixedOuterMean_sub hA (hb l (j - l)) (hb (l + 1) (j - (l + 1)))
    mode m v hm hv j r x y, ht l (by omega), ht (l + 1) (by omega)]

/-- Actual spatial Hessian plus squared first derivative, under all remaining
outer mixed means. This is the genuine input of the Gaussian heat generator. -/
theorem mixedOuterMean_spatialHeat_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ) (mass : ℝ)
    (A B x y : Fin n → ℝ) :
    mixedOuterMean mode m v (constrainedPairFieldBase n U u) j r
      (fun x y => mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) (constrainedPairFieldDirection U u A B)
        (constrainedPairFieldCovariance U u A B A B) j x y +
        mass * (mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
          (constrainedPairFieldDirection U u A B) j x y) ^ 2) x y =
      mixedReplicaTransportedHessian mode m v j r U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y +
      mass * mixedReplicaBilinear mode m v j r U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y := by
  let f := pairFieldPotential n u A B
  have hp (x y : Fin n → ℝ) :
      (mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j x y) ^ 2 =
        mixedReplicaBilinear mode m v j 0 U u f f x y := by
    rw [mixedConstrainedCascadeD_field_eq_replica U u mode m v hm hv, pow_two]
    exact mixedConstrainedReplica_product_moment U u mode m v hm hv j 0 f f x y
  simp_rw [mixedConstrainedCascadeDD_field_eq_replica U u mode m v hm hv, hp]
  have hA : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv 0 0
  rw [mixedOuterMean_add hA (mixedReplicaHessianExpression_bounded U u mode m v hm hv j f f)
    ((mixedReplicaBilinear_bounded U u mode m v hm hv j 0 f f).const_mul mass) mode m v hm hv j r,
    mixedOuterMean_replicaHessian U u mode m v hm hv j r f f,
    mixedOuterMean_const_mul hA (mixedReplicaBilinear_bounded U u mode m v hm hv j 0 f f)
      mass mode m v hm hv j r]
  have H := mixedOuterMean_replicaBilinear U u mode m v hm hv j 0 r f f x y
  simpa only [Nat.add_zero, Nat.zero_add] using congrArg
    (fun z => mixedReplicaTransportedHessian mode m v j r U u f f x y + mass * z) H

end SpinGlass.Targets
