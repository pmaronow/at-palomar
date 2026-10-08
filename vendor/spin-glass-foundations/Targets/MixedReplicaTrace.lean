module

public import Targets.MixedReplicaHessian
public import Targets.MixedDisorderInterpolation
public import Targets.CoupledReplicaTrace

@[expose] public section

/-!
# Actual SK spectral contraction for the mixed replica law

The genuine mixed Hessian is contracted with the original SK spectral
covariance. Its split-level moments use the product-before-transport replica
weights. The resulting disorder-amplitude derivative retains those pointwise
moments inside the actual disorder integral; it is not a varying-variance
interpolation formula or an assumed replica identity.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- A kernel averaged under the actual mixed split-level replica law. -/
noncomputable def mixedReplicaMoment (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (l r : ℕ) (U : EnergySpace n) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, mixedConstrainedReplica mode m v l r U u x y p q * K p q

/-- Finite spectral contraction of the actual mixed bilinear observable. -/
theorem mixedReplicaBilinear_contraction {I : Type*} [Fintype I]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (U : EnergySpace n) (u : ℝ) (c : I → ℝ)
    (f : I → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    (∑ i, c i * mixedReplicaBilinear mode m v l r U u (f i) (f i) x y) =
      mixedReplicaMoment mode m v l r U u (fun p q => ∑ i, c i * f i p * f i q) x y := by
  unfold mixedReplicaBilinear mixedReplicaMoment
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

theorem mixedReplicaMoment_const_mul
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (U : EnergySpace n) (u : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) (c : ℝ) :
    mixedReplicaMoment mode m v l r U u (fun p q => c * K p q) x y =
      c * mixedReplicaMoment mode m v l r U u K x y := by
  unfold mixedReplicaMoment
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem mixedReplicaMoment_add
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (U : EnergySpace n) (u : ℝ)
    (K L : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedReplicaMoment mode m v l r U u (fun p q => K p q + L p q) x y =
      mixedReplicaMoment mode m v l r U u K x y + mixedReplicaMoment mode m v l r U u L x y := by
  simp only [mixedReplicaMoment, mul_add, Finset.sum_add_distrib]

theorem mixedReplicaMoment_sub
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (U : EnergySpace n) (u : ℝ)
    (K L : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedReplicaMoment mode m v l r U u (fun p q => K p q - L p q) x y =
      mixedReplicaMoment mode m v l r U u K x y - mixedReplicaMoment mode m v l r U u L x y := by
  simp only [mixedReplicaMoment, mul_sub, Finset.sum_sub_distrib]

theorem mixedReplicaMoment_sum {I : Type*} [Fintype I]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (U : EnergySpace n) (u : ℝ)
    (K : I → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedReplicaMoment mode m v l r U u (fun p q => ∑ i, K i p q) x y =
      ∑ i, mixedReplicaMoment mode m v l r U u (K i) x y := by
  unfold mixedReplicaMoment
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The genuine mixed Hessian contracted with the original SK covariance.
All three Gaussian modes, zero masses and zero variances are included. -/
theorem mixedConstrainedSecond_SK_trace (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      mixedConstrainedSecond mode m v j U (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (β ^ 2 * (1 + u ^ 2) -
        mixedReplicaMoment mode m v 0 j U u (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          mixedReplicaMoment mode m v l (j - l) U u (fun p q => pairSKCovariance β p.1 q.1) x y -
          mixedReplicaMoment mode m v (l + 1) (j - (l + 1)) U u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) := by
  simp only [mixedConstrainedSecond,
    mixedConstrainedCascadeDD_disorder_eq_replica U _ _ u mode m v hm hv j x y,
    mixedReplicaHessianExpression]
  rw [sum_weighted_covariance, sum_weighted_diagonal, mixedReplicaBilinear_contraction]
  simp_rw [mixedReplicaBilinear_contraction, pairSKCovariance_spectral_sum β h sk,
    pairSKCovariance_self hn β, mixedReplicaMoment_const_mul]
  rw [← Finset.sum_mul, sum_mixedConstrainedGibbs U u mode m v hm hv j x y, one_mul]
  simp_rw [← mul_sub (n : ℝ), mul_left_comm (m _) (n : ℝ)]
  rw [← Finset.mul_sum]
  ring

/-- Actual SK amplitude differentiation, with all covariance terms identified
as moments of the genuine pointwise split-replica law. The field variances
are fixed while the disorder amplitude varies. -/
theorem hasDerivAt_mixedConstrainedGaussian_amplitude_SK
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => ∫ ω, mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (b • sk.U ω) u) j x y)
      (a * n * ∫ ω, β ^ 2 * (1 + u ^ 2) -
        mixedReplicaMoment mode m v 0 j (a • sk.U ω) u
          (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          mixedReplicaMoment mode m v l (j - l) (a • sk.U ω) u
            (fun p q => pairSKCovariance β p.1 q.1) x y -
          mixedReplicaMoment mode m v (l + 1) (j - (l + 1)) (a • sk.U ω) u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) a := by
  have H := hasDerivAt_mixedConstrainedGaussian_amplitude_trace sk.hU a u mode m v hm hv j x y
  simp_rw [mixedConstrainedSecond_SK_trace hn β h sk _ u mode m v hm hv j x y] at H
  simpa only [integral_const_mul, mul_assoc] using H

/-- Free-energy normalization cancels the system-size factor in the actual
SK amplitude derivative. This does not yet vary the field variances. -/
theorem hasDerivAt_mixedConstrainedFreeEnergy_amplitude_SK
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (a u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    HasDerivAt (fun b => (1 / (n : ℝ)) * ∫ ω, mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (b • sk.U ω) u) j x y)
      (a * ∫ ω, β ^ 2 * (1 + u ^ 2) -
        mixedReplicaMoment mode m v 0 j (a • sk.U ω) u
          (fun p q => pairSKCovariance β p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          mixedReplicaMoment mode m v l (j - l) (a • sk.U ω) u
            (fun p q => pairSKCovariance β p.1 q.1) x y -
          mixedReplicaMoment mode m v (l + 1) (j - (l + 1)) (a • sk.U ω) u
            (fun p q => pairSKCovariance β p.1 q.1) x y)) a := by
  have H := (hasDerivAt_mixedConstrainedGaussian_amplitude_SK hn β h sk a u mode m v
    hm hv j x y).const_mul (1 / (n : ℝ))
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have he (X : ℝ) : (1 / (n : ℝ)) * (a * n * X) = a * X := by
    field_simp [hnR]
  simpa only [he] using H

end Disorder

end SpinGlass.Targets
