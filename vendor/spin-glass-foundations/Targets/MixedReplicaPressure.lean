module

public import Targets.MixedReplicaField
public import Targets.MixedCovarianceTelescope

@[expose] public section

/-!
# Actual mixed trace and heat covariance telescope

The disorder trace and each original-level variance heat term use the same
actual split-replica law. This module identifies their normalized combination
with the signed trial covariance expression. It is an identity of the genuine
components, not an assumption about a simultaneously varying pressure.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- Linearity of the actual heat expression in its contracted kernel and
diagonal, retaining the raw mass of the differentiated level. -/
theorem mixedReplicaHeatExpression_const_mul
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j r : ℕ)
    (U : EnergySpace n) (u D a : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedReplicaHeatExpression mode m v j r U u (a * D) (fun p q => a * K p q) x y =
      a * mixedReplicaHeatExpression mode m v j r U u D K x y := by
  simp only [mixedReplicaHeatExpression, mixedReplicaMoment_const_mul,
    mul_sub, mul_add, Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  · ring

section Pointwise

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Actual SK trace minus the actual mixed field heat, with finite reversal
and free-energy normalization made explicit. Zero trial increments and zero
unchanged variances are included; no division by an increment is used. -/
theorem mixedConstrained_trace_sub_heat_eq_covariance
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (U : EnergySpace n) (t u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (M ρ c v : ℕ → ℝ) (κ : ℕ)
    (hm : ∀ i, 0 ≤ M (κ - i)) (hv : ∀ i, 0 ≤ v i)
    (hm0 : M 0 = 0) (hmκ : M κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (hinc : ∀ l < κ + 1, c (κ - l + 1) - c (κ - l) =
      (ρ (κ - l + 1) - ρ (κ - l)) * (mode l).correlation)
    (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) *
      (t / 2 * (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
          mixedConstrainedSecond mode (fun i => M (κ - i)) v (κ + 1)
            U (sk.hU.w i) (sk.hU.w i) u x y) -
        t * ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
          mixedLevelVarianceD U u mode (fun i => M (κ - i)) v l
            (κ + 1 - (l + 1)) (v l) x y) =
      pairCovarianceExpression β t u M ρ c κ
        (fun p => mixedConstrainedReplica mode (fun i => M (κ - i)) v
          (κ - p) (κ + 1 - (κ - p)) U u x y) := by
  let m := fun i => M (κ - i)
  let μ := fun i => mixedConstrainedReplica mode m v i (κ + 1 - i) U u x y
  let A := fun i => mixedReplicaMoment mode m v i (κ + 1 - i) U u
    (fun p q => pairSKCovariance β p.1 q.1) x y
  let B := fun i l => mixedReplicaMoment mode m v i (κ + 1 - i) U u
    (fun p q => pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
      (c (κ - l + 1) - c (κ - l)) p.1 q.1) x y
  let D := fun l => 2 * β ^ 2 * ((ρ (κ - l + 1) - ρ (κ - l)) +
    u * (c (κ - l + 1) - c (κ - l)))
  have hheat (l : Fin (κ + 1)) :
      β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        mixedLevelVarianceD U u mode m v l (κ + 1 - (l + 1)) (v l) x y =
      (n : ℝ) / 2 * ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l) := by
    rw [mixedLevelVarianceD_overlap hn U u mode m v hm hv]
    have hsum : (l : ℕ) + (κ + 1 - (l + 1) + 1) = κ + 1 := by omega
    have hrest : κ + 1 - (l + 1) + 1 = κ + 1 - l := by omega
    have hK (p q : AT.ConstrainedPair n u) :
        pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
          (c (κ - l + 1) - c (κ - l)) p.1 q.1 =
        (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) *
          pairFieldCovariance 1 1 (mode l).correlation p.1 q.1 := by
      rw [hinc l l.isLt]
      simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
      ring
    have hD : D l = (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) *
        (2 * (1 + (mode l).correlation * u)) := by
      dsimp [D]
      rw [hinc l l.isLt]
      ring
    have HH := mixedReplicaHeatExpression_const_mul mode m v l
      (κ + 1 - (l + 1) + 1) U u (2 * (1 + (mode l).correlation * u))
      (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)))
      (fun p q => pairFieldCovariance 1 1 (mode l).correlation p.1 q.1) x y
    rw [← hD] at HH
    simp_rw [← hK] at HH
    rw [mixedReplicaHeatExpression, hsum, hrest] at HH
    change (D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) + m l * B l l = _ at HH
    rw [HH, hrest]
    ring
  rw [mixedConstrainedSecond_SK_trace hn β h sk U u mode m v hm hv]
  change (1 / (n : ℝ)) *
    (t / 2 * (n * (β ^ 2 * (1 + u ^ 2) - A 0 +
      ∑ i : Fin (κ + 1), m i * (A i - A (i + 1)))) -
      t * ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        mixedLevelVarianceD U u mode m v l (κ + 1 - (l + 1)) (v l) x y) = _
  simp_rw [hheat]
  rw [← Finset.mul_sum]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have H := pairCovarianceExpression_eq_trace_sub_increment_heat β t u M ρ c κ
    hm0 hmκ hρ0 hc0 hρ1 hc1 μ
  change t / 2 * ((β ^ 2 * (1 + u ^ 2) - A 0 +
    ∑ i : Fin (κ + 1), m i * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) = _ at H
  rw [← H]
  change (1 / (n : ℝ)) * (t / 2 * (n * _) - t * (n / 2 * _)) = _
  field_simp [hnR]

end Pointwise

end SpinGlass.Targets
