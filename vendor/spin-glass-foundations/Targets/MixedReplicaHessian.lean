module

public import Targets.MixedReplicaWeights
public import Targets.MixedCascadeSecond
public import Targets.CoupledCovarianceTelescope

@[expose] public section

/-!
# Actual mixed-cascade Hessians under the split-replica law

The checked mixed covariance rule has the same normalized-mean form for all
three modes. Finite linearity expands it into the actual split-replica
weights, without identifying the two physical and trial sharing cutoffs.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem mixedVectorMean_bounded_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : ∀ i, CoupledBounded (G i)) (c : I → ℝ)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * mixedVectorMean n mode m v A (G i) x y := by
  choose B hb using fun i => (hG i).bound
  exact mixedVectorMean_sum hA (fun i => (hG i).measurable) hb c mode hm hv x y

theorem mixedVectorMean_add {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun x y => G x y + H x y) x y =
      mixedVectorMean n mode m v A G x y + mixedVectorMean n mode m v A H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul] using
    mixedVectorMean_bounded_sum hA h (fun _ => 1) mode hm hv x y

theorem mixedVectorMean_const_mul {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (c : ℝ)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun x y => c * G x y) x y =
      c * mixedVectorMean n mode m v A G x y := by
  simpa using mixedVectorMean_bounded_sum (I := Unit) hA (fun _ => hG) (fun _ => c) mode hm hv x y

theorem mixedVectorMean_sub {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun x y => G x y - H x y) x y =
      mixedVectorMean n mode m v A G x y - mixedVectorMean n mode m v A H x y := by
  have H' := mixedVectorMean_add hA hG (hH.const_mul (-1)) mode hm hv x y
  rw [mixedVectorMean_const_mul hA hH (-1) mode hm hv x y] at H'
  simpa only [neg_one_mul, sub_eq_add_neg] using H'

theorem CoupledBounded.mixedCascadeDD {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) :
    CoupledBounded (mixedVectorCascadeDD n mode m v A AW G GW j) := by
  induction j with
  | zero => exact hGW
  | succ j ih =>
    have hg := hG.mixedCascadeD hA mode m v hm hv j
    have haw := hAW.mixedCascadeD hA mode m v hm hv j
    have hg' := hG.mixedCascadeD hA mode m v hm hv (j + 1)
    have haw' := hAW.mixedCascadeD hA mode m v hm hv (j + 1)
    exact ((ih.add ((hg.const_mul (m j)).mul haw)).mixedMean
      (hA.mixedCascade mode m v hm hv j) (mode j) (hm j) (hv j)).sub
        ((hg'.const_mul (m j)).mul haw')

/-- Actual normalized transport through `r` outer levels starting at `l`. -/
noncomputable def mixedOuterMean (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (l r : ℕ)
    (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  mixedVectorCascadeD n (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
    (mixedVectorCascade n mode m v A l) G r

theorem mixedOuterMean_zero (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : mixedOuterMean mode m v A l 0 G = G := rfl

theorem mixedOuterMean_from_zero (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedOuterMean mode m v A 0 j G = mixedVectorCascadeD n mode m v A G j := by
  simp only [mixedOuterMean, Nat.zero_add, mixedVectorCascade]

theorem mixedOuterMean_succ (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedOuterMean mode m v A l (r + 1) G =
      mixedVectorMean n (mode (l + r)) (m (l + r)) (v (l + r))
        (mixedVectorCascade n mode m v A (l + r)) (mixedOuterMean mode m v A l r G) := by
  simp only [mixedOuterMean, mixedVectorCascadeD, mixedVectorCascade_add_levels]

theorem CoupledBounded.mixedOuterMean {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hA : CoupledGrowth A)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) :
    CoupledBounded (mixedOuterMean mode m v A l r G) :=
  hG.mixedCascadeD (hA.mixedCascade mode m v hm hv l) _ _ _
    (fun i => hm (l + i)) (fun i => hv (l + i)) r

theorem mixedOuterMean_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : ∀ i, CoupledBounded (G i)) (c : I → ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v A l r (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * mixedOuterMean mode m v A l r (G i) x y := by
  choose B hb using fun i => (hG i).bound
  exact mixedVectorCascadeD_sum (hA.mixedCascade mode m v hm hv l)
    (fun i => (hG i).measurable) hb c _ _ _
    (fun i => hm (l + i)) (fun i => hv (l + i)) r x y

theorem mixedOuterMean_sub {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v A l r (fun x y => G x y - H x y) x y =
      mixedOuterMean mode m v A l r G x y - mixedOuterMean mode m v A l r H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul, neg_one_mul, sub_eq_add_neg] using
    mixedOuterMean_sum hA h (![1, -1]) mode m v hm hv l r x y

theorem mixedOuterMean_cascadeD (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedOuterMean mode m v A l r (mixedVectorCascadeD n mode m v A G l) =
      mixedVectorCascadeD n mode m v A G (l + r) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [mixedOuterMean_succ, ih]; rfl

/-- The common actual one-level covariance rule, with finite linearity justified. -/
theorem mixedVectorCascadeDD_succ_covariance
    {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    mixedVectorCascadeDD n mode m v A AW G GW (j + 1) x y =
      mixedVectorMean n (mode j) (m j) (v j) (mixedVectorCascade n mode m v A j)
        (mixedVectorCascadeDD n mode m v A AW G GW j) x y +
      m j * (mixedVectorMean n (mode j) (m j) (v j) (mixedVectorCascade n mode m v A j)
        (fun x y => mixedVectorCascadeD n mode m v A G j x y *
          mixedVectorCascadeD n mode m v A AW j x y) x y -
        mixedVectorCascadeD n mode m v A G (j + 1) x y *
          mixedVectorCascadeD n mode m v A AW (j + 1) x y) := by
  have hp := (hG.mixedCascadeD hA mode m v hm hv j).mul (hAW.mixedCascadeD hA mode m v hm hv j)
  simp only [mixedVectorCascadeDD, mixedVectorCovariance, mul_assoc]
  rw [mixedVectorMean_add (hA.mixedCascade mode m v hm hv j)
    (CoupledBounded.mixedCascadeDD hA hAW hG hGW mode m v hm hv j)
    (hp.const_mul (m j)) (mode j) (hm j) (hv j),
    mixedVectorMean_const_mul (hA.mixedCascade mode m v hm hv j) hp (m j) (mode j) (hm j) (hv j)]
  simp only [mixedVectorCascadeD]
  ring

/-- Full covariance expansion of the genuine mixed Hessian recursion. -/
theorem mixedVectorCascadeDD_expansion
    {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    mixedVectorCascadeDD n mode m v A AW G GW j x y =
      mixedOuterMean mode m v A 0 j GW x y +
      ∑ l : Fin j, m l *
        (mixedOuterMean mode m v A l (j - l)
          (fun x y => mixedVectorCascadeD n mode m v A G l x y *
            mixedVectorCascadeD n mode m v A AW l x y) x y -
        mixedOuterMean mode m v A (l + 1) (j - (l + 1))
          (fun x y => mixedVectorCascadeD n mode m v A G (l + 1) x y *
            mixedVectorCascadeD n mode m v A AW (l + 1) x y) x y) := by
  classical
  let P (l : ℕ) := fun x y => mixedVectorCascadeD n mode m v A G l x y *
    mixedVectorCascadeD n mode m v A AW l x y
  have hP (l : ℕ) : CoupledBounded (P l) :=
    (hG.mixedCascadeD hA mode m v hm hv l).mul (hAW.mixedCascadeD hA mode m v hm hv l)
  induction j generalizing x y with
  | zero => simp only [mixedVectorCascadeDD, mixedOuterMean_zero, Fin.sum_univ_zero, add_zero]
  | succ j ih =>
    let R (l : Fin j) := fun x y =>
      mixedOuterMean mode m v A l (j - l) (P l) x y -
        mixedOuterMean mode m v A (l + 1) (j - (l + 1)) (P (l + 1)) x y
    have hR (l : Fin j) : CoupledBounded (R l) :=
      ((hP l).mixedOuterMean hA mode m v hm hv l (j - l)).sub
        ((hP (l + 1)).mixedOuterMean hA mode m v hm hv (l + 1) (j - (l + 1)))
    have he (l : Fin j) :
        mixedVectorMean n (mode j) (m j) (v j) (mixedVectorCascade n mode m v A j) (R l) x y =
        mixedOuterMean mode m v A l (j + 1 - l) (P l) x y -
          mixedOuterMean mode m v A (l + 1) (j + 1 - (l + 1)) (P (l + 1)) x y := by
      have h1 : j + 1 - l = (j - l) + 1 := by omega
      have h2 : j + 1 - (l + 1) = (j - (l + 1)) + 1 := by omega
      have h3 : l + (j - l) = j := by omega
      have h4 : l + 1 + (j - (l + 1)) = j := by omega
      rw [h1, h2, mixedOuterMean_succ, mixedOuterMean_succ, h3, h4]
      exact mixedVectorMean_sub (hA.mixedCascade mode m v hm hv j)
        ((hP l).mixedOuterMean hA mode m v hm hv l (j - l))
        ((hP (l + 1)).mixedOuterMean hA mode m v hm hv (l + 1) (j - (l + 1)))
        (mode j) (hm j) (hv j) x y
    have hih : mixedVectorCascadeDD n mode m v A AW G GW j = fun x y =>
        mixedOuterMean mode m v A 0 j GW x y + ∑ l : Fin j, m l * R l x y :=
      funext fun x => funext fun y => ih x y
    rw [mixedVectorCascadeDD_succ_covariance hA hAW hG hGW mode m v hm hv j x y, hih,
      mixedVectorMean_add (hA.mixedCascade mode m v hm hv j)
        (hGW.mixedOuterMean hA mode m v hm hv 0 j)
        (CoupledBounded.sum (fun l => (hR l).const_mul (m l))) (mode j) (hm j) (hv j),
      mixedVectorMean_bounded_sum (hA.mixedCascade mode m v hm hv j) hR
        (fun l => m l) (mode j) (hm j) (hv j)]
    simp_rw [he]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel_left, Nat.sub_self,
      mixedOuterMean_zero, mixedOuterMean_succ, Nat.zero_add, Nat.add_zero]
    dsimp only [P]
    ring

/-- Bilinear observable under the actual product-before-transport replica law. -/
noncomputable def mixedReplicaBilinear (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (l r : ℕ) (U : EnergySpace n) (u : ℝ) (f g : AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, mixedConstrainedReplica mode m v l r U u x y p q * f p * g q

/-- The actual split-replica covariance telescope of a mixed Hessian. -/
noncomputable def mixedReplicaHessianExpression (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (j : ℕ) (U : EnergySpace n) (u : ℝ) (f g : AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  (∑ p, mixedConstrainedGibbs mode m v j U u x y p * f p * g p) -
    mixedReplicaBilinear mode m v 0 j U u f g x y +
    ∑ l : Fin j, m l * (mixedReplicaBilinear mode m v l (j - l) U u f g x y -
      mixedReplicaBilinear mode m v (l + 1) (j - (l + 1)) U u f g x y)

private theorem bounded_terminalMean (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (f : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p) := by
  have hp (p : AT.ConstrainedPair n u) : CoupledBounded (fun x y => constrainedPairGibbs n U u x y p) := by
    refine ⟨measurable_constrainedPairGibbs_fields U u p, 1, fun x y => ?_⟩
    rw [abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
    exact AT.gtStateGibbs_le_one _ _ _
  simpa only [mul_comm] using CoupledBounded.sum (fun p => (hp p).const_mul (f p))

/-- The actual finite-state covariance yields the full mixed split-replica
expansion, with no replica or covariance identity among the hypotheses. -/
theorem mixedVectorCascadeDD_constrained_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * g p)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p)
      (fun x y => (∑ p, constrainedPairGibbs n U u x y p * (f p * g p)) -
        (∑ p, constrainedPairGibbs n U u x y p * f p) *
          (∑ p, constrainedPairGibbs n U u x y p * g p)) j x y =
      mixedReplicaHessianExpression mode m v j U u f g x y := by
  let A := constrainedPairFieldBase n U u
  let M (f : AT.ConstrainedPair n u → ℝ) := fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p
  have hA : CoupledGrowth A := constrainedPairFieldCascade_growth U u m v hm hv 0 0
  have hM (f : AT.ConstrainedPair n u → ℝ) : CoupledBounded (M f) := bounded_terminalMean U u f
  have hp (l r : ℕ) :
      mixedOuterMean mode m v A l r
        (fun x y => mixedVectorCascadeD n mode m v A (M f) l x y *
          mixedVectorCascadeD n mode m v A (M g) l x y) x y =
        mixedReplicaBilinear mode m v l r U u f g x y := by
    dsimp only [mixedOuterMean, A, M, mixedReplicaBilinear]
    simp_rw [mixedConstrainedGibbs_moment U u mode m v hm hv]
    exact mixedConstrainedReplica_product_moment U u mode m v hm hv l r f g x y
  have H := mixedVectorCascadeDD_expansion hA (hM g) (hM f)
    ((hM (fun p => f p * g p)).sub ((hM f).mul (hM g))) mode m v hm hv j x y
  rw [mixedOuterMean_sub hA (hM (fun p => f p * g p)) ((hM f).mul (hM g))
    mode m v hm hv 0 j x y] at H
  have hp0 : mixedOuterMean mode m v A 0 j (fun x y => M f x y * M g x y) x y =
      mixedReplicaBilinear mode m v 0 j U u f g x y := by
    simpa only [mixedVectorCascadeD] using hp 0 j
  rw [hp0, mixedOuterMean_from_zero] at H
  simp_rw [hp] at H
  simpa only [A, M, mixedConstrainedGibbs_moment U u mode m v hm hv,
    mixedReplicaHessianExpression, mul_assoc] using H

/-- The genuine mixed disorder Hessian has the actual replica expansion. -/
theorem mixedConstrainedCascadeDD_disorder_eq_replica
    (U V W : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairDirection U W u) (constrainedPairDirection U V u)
      (constrainedPairSecond n u U V W) j x y =
      mixedReplicaHessianExpression mode m v j U u
        (fun p => V p.1.1 + V p.1.2) (fun p => W p.1.1 + W p.1.2) x y := by
  have he : constrainedPairSecond n u U V W = fun x y =>
      (∑ p, constrainedPairGibbs n U u x y p * ((V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2))) -
      (∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)) *
        (∑ p, constrainedPairGibbs n U u x y p * (W p.1.1 + W p.1.2)) := by
    funext x y
    simp only [constrainedPairSecond_eq_covariance, mul_assoc]
  rw [he]
  exact mixedVectorCascadeDD_constrained_replica U u mode m v hm hv j _ _ x y

/-- Separate-replica field directions use exactly the same split law. -/
theorem mixedConstrainedCascadeDD_field_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B C D x y : Fin n → ℝ) :
    mixedVectorCascadeDD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairFieldDirection U u C D) (constrainedPairFieldDirection U u A B)
      (constrainedPairFieldCovariance U u A B C D) j x y =
      mixedReplicaHessianExpression mode m v j U u
        (pairFieldPotential n u A B) (pairFieldPotential n u C D) x y := by
  have he : constrainedPairFieldCovariance U u A B C D = fun x y =>
      (∑ p, constrainedPairGibbs n U u x y p *
        (pairFieldPotential n u A B p * pairFieldPotential n u C D p)) -
      (∑ p, constrainedPairGibbs n U u x y p * pairFieldPotential n u A B p) *
        (∑ p, constrainedPairGibbs n U u x y p * pairFieldPotential n u C D p) := by
    funext x y
    simp only [constrainedPairFieldCovariance, constrainedPairFieldDirection]
    congr 1
    · apply Finset.sum_congr rfl
      intro p _
      ring
    · ring
  rw [he]
  exact mixedVectorCascadeDD_constrained_replica U u mode m v hm hv j _ _ x y

theorem hasDerivAt_mixedConstrainedCascadeD_field_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B C D x y : Fin n → ℝ) :
    HasDerivAt
      (fun a : ℝ => mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j (x + a • C) (y + a • D))
      (mixedReplicaHessianExpression mode m v j U u
        (pairFieldPotential n u A B) (pairFieldPotential n u C D) x y) 0 := by
  simpa only [mixedConstrainedCascadeDD_field_eq_replica U u mode m v hm hv] using
    hasDerivAt_mixedConstrainedCascadeD_field U u mode m v hm hv j A B C D x y

/-- Adjacent-mass summation by parts retains both endpoint coefficients. -/
theorem mixedReplicaHessianExpression_mass_telescope
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ) (U : EnergySpace n) (u : ℝ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedReplicaHessianExpression mode m v (j + 1) U u f g x y =
      (∑ p, mixedConstrainedGibbs mode m v (j + 1) U u x y p * f p * g p) +
        (m 0 - 1) * mixedReplicaBilinear mode m v 0 (j + 1) U u f g x y -
        m j * mixedReplicaBilinear mode m v (j + 1) 0 U u f g x y +
        ∑ l : Fin j, (m (l + 1) - m l) *
          mixedReplicaBilinear mode m v (l + 1) (j - l) U u f g x y := by
  let B := fun l => mixedReplicaBilinear mode m v l (j + 1 - l) U u f g x y
  have H := replicaCovariance_mass_telescope m B
    (∑ p, mixedConstrainedGibbs mode m v (j + 1) U u x y p * f p * g p) j
  simp only [B, Nat.sub_zero, Nat.sub_self] at H
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at H
  have he (l : Fin j) : j + 1 - (l + 1) = j - l := by omega
  simp only [he] at H
  unfold mixedReplicaHessianExpression
  exact H

end SpinGlass.Targets
