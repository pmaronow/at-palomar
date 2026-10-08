module

public import Targets.CoupledReplicaHessian
public import Targets.CoupledReplicaAverage

@[expose] public section

/-!
# The actual SK Hessian trace under split-level replica weights

Contract the genuine nested Hessian with the disorder's spectral covariance,
then justify its outer expectation using the actual normalized split law.
This identifies the disorder part of the simultaneous interpolation derivative;
the heat contribution and its combination with this trace remain separate.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- A covariance kernel averaged against the actual split-level replica law. -/
noncomputable def constrainedReplicaMoment (m v : ℕ → ℝ) (d l r : ℕ)
    (U : EnergySpace n) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q * K p q

/-- Finite covariance contraction preserves the product-before-transport law. -/
theorem constrainedReplicaBilinear_contraction {I : Type*} [Fintype I]
    (m v : ℕ → ℝ) (d l r : ℕ) (U : EnergySpace n) (u : ℝ)
    (c : I → ℝ) (f : I → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    (∑ i, c i * constrainedReplicaBilinear m v d l r U u (f i) (f i) x y) =
      constrainedReplicaMoment m v d l r U u (fun p q => ∑ i, c i * f i p * f i q) x y := by
  unfold constrainedReplicaBilinear constrainedReplicaMoment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem constrainedReplicaMoment_const_mul
    (m v : ℕ → ℝ) (d l r : ℕ) (U : EnergySpace n) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) (c : ℝ) :
    constrainedReplicaMoment m v d l r U u (fun p q => c * K p q) x y =
      c * constrainedReplicaMoment m v d l r U u K x y := by
  unfold constrainedReplicaMoment
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem sum_weighted_diagonal {I S : Type*} [Fintype I] [Fintype S]
    (c : I → ℝ) (P : S → ℝ) (f : I → S → ℝ) :
    (∑ i, c i * ∑ p, P p * f i p * f i p) =
      ∑ p, P p * ∑ i, c i * f i p * f i p := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sum_weighted_differences {I L : Type*} [Fintype I] [Fintype L]
    (c : I → ℝ) (m : L → ℝ) (A B : I → L → ℝ) :
    (∑ i, c i * ∑ l, m l * (A i l - B i l)) =
      ∑ l, m l * ((∑ i, c i * A i l) - ∑ i, c i * B i l) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sum_weighted_covariance {I L : Type*} [Fintype I] [Fintype L]
    (c : I → ℝ) (D B : I → ℝ) (m : L → ℝ) (F G : I → L → ℝ) :
    (∑ i, c i * (D i - B i + ∑ l, m l * (F i l - G i l))) =
      (∑ i, c i * D i) - (∑ i, c i * B i) +
        ∑ l, m l * ((∑ i, c i * F i l) - ∑ i, c i * G i l) := by
  calc
    _ = (∑ i, c i * D i) - (∑ i, c i * B i) +
        ∑ i, c i * ∑ l, m l * (F i l - G i l) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by rw [sum_weighted_differences]

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The same kernel moment after the outer disorder expectation. -/
noncomputable def averagedConstrainedReplicaMoment (Z : Ω → EnergySpace n)
    (m v : ℕ → ℝ) (d l r : ℕ) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, averagedConstrainedCascadeReplica Z u m v d l r x y p q * K p q

theorem integrable_constrainedReplicaMoment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    Integrable (fun ω => constrainedReplicaMoment m v d l r (Z ω) u K x y) := by
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
    (integrable_constrainedCascadeReplica hZ u m v hm hv d l r x y p q).mul_const (K p q)))

theorem integral_constrainedReplicaMoment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    (∫ ω, constrainedReplicaMoment m v d l r (Z ω) u K x y) =
      averagedConstrainedReplicaMoment Z m v d l r u K x y :=
  averagedConstrainedCascadeReplica_moment hZ u m v hm hv d l r x y K

/-- The genuine full nested Hessian contracted with the actual SK covariance.
The diagonal is constant because both replicas satisfy the overlap constraint.
Zero masses, zero variances and arbitrary independent/shared cutoff are retained. -/
theorem constrainedPairFieldCascadeSecond_SK_trace
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d j U (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (β ^ 2 * (1 + u ^ 2) -
        constrainedReplicaMoment m v d 0 j U u (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          constrainedReplicaMoment m v d l (j - l) U u (fun p q => pairSKCovariance β p.1 q.1) x y -
          constrainedReplicaMoment m v d (l + 1) (j - (l + 1)) U u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) := by
  simp only [constrainedPairFieldCascadeSecond_eq_replica U _ _ u m v hm hv d j x y,
    constrainedReplicaHessianExpression]
  rw [sum_weighted_covariance, sum_weighted_diagonal, constrainedReplicaBilinear_contraction]
  simp_rw [constrainedReplicaBilinear_contraction, pairSKCovariance_spectral_sum β h sk,
    pairSKCovariance_self hn β, constrainedReplicaMoment_const_mul]
  rw [← Finset.sum_mul, sum_constrainedCascadeGibbs U u m v hm hv d j x y, one_mul]
  simp_rw [← mul_sub (n : ℝ), mul_left_comm (m _) (n : ℝ)]
  rw [← Finset.mul_sum]
  ring

/-- Outer expectation of the genuine SK Hessian trace is its covariance
telescope under the actual disorder-averaged split weights. All integrability
requirements are discharged, for any measurable disorder input. -/
theorem integral_constrainedPairFieldCascadeSecond_SK_trace
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d j (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (β ^ 2 * (1 + u ^ 2) -
        averagedConstrainedReplicaMoment Z m v d 0 j u (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          averagedConstrainedReplicaMoment Z m v d l (j - l) u
            (fun p q => pairSKCovariance β p.1 q.1) x y -
          averagedConstrainedReplicaMoment Z m v d (l + 1) (j - (l + 1)) u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) := by
  let K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ :=
    fun p q => pairSKCovariance β p.1 q.1
  have hi (l r : ℕ) := integrable_constrainedReplicaMoment hZ u m v hm hv d l r K x y
  have hs : Integrable (fun ω => ∑ l : Fin j, m l * (
      constrainedReplicaMoment m v d l (j - l) (Z ω) u K x y -
      constrainedReplicaMoment m v d (l + 1) (j - (l + 1)) (Z ω) u K x y)) :=
    integrable_finsetSum _ (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp_rw [constrainedPairFieldCascadeSecond_SK_trace hn β h sk _ u m v hm hv d j x y]
  have hlin := integral_add ((integrable_const (β ^ 2 * (1 + u ^ 2))).sub (hi 0 j)) hs
  simp only [Pi.sub_apply, K] at hlin
  rw [integral_const_mul, hlin,
    integral_sub (integrable_const (β ^ 2 * (1 + u ^ 2))) (hi 0 j), integral_const,
    probReal_univ, smul_eq_mul, one_mul,
    integral_constrainedReplicaMoment hZ u m v hm hv d 0 j _ x y]
  congr 2
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin j)) (fun l _ => ((hi l (j - l)).sub
      (hi (l + 1) (j - (l + 1)))).const_mul (m l))
  simp only [Pi.sub_apply, K] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_sub (hi l (j - l)) (hi (l + 1) (j - (l + 1))),
    integral_constrainedReplicaMoment hZ u m v hm hv,
    integral_constrainedReplicaMoment hZ u m v hm hv]

end Disorder

end SpinGlass.Targets
