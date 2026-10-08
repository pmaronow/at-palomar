module

public import Targets.CoupledCovarianceTelescope
public import Targets.Section5ReplicaDerivative

@[expose] public section

/-!
# The actual averaged second-interpolation covariance identity

Match the backward level order in the differentiated pressure with the forward
trial-field covariance expression. The weights are the actual normalized split
law, not newly hypothesized probability weights.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Exact covariance identity for the actual averaged pressure derivative,
with the original independent/shared cutoff and all physical coefficients. -/
theorem averagedReplicaPressureDerivative_eq_covariance
    (Z : Ω → EnergySpace n) (u β t : ℝ) (m ρ v : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = u)
    (x y : Fin n → ℝ) :
    averagedReplicaPressureDerivative Z u β t (fun j => m (κ - j)) v
      (fun j => -(t * β ^ 2 * (ρ (κ - j + 1) - ρ (κ - j)))) (κ + 1 - τ) (κ + 1) x y =
      pairCovarianceExpression β t u m ρ (fun p => ρ (min p τ)) κ
        (fun p => averagedConstrainedCascadeReplica Z u (fun j => m (κ - j)) v
          (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y) := by
  let μ := fun i => averagedConstrainedCascadeReplica Z u (fun j => m (κ - j)) v
    (κ + 1 - τ) i (κ + 1 - i) x y
  let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
  let H := fun l =>
    ((if κ - l < τ then 2 * (1 + u) else 2) - B 0 l +
      ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) + m (κ - l) * B l l
  have hc (l : Fin (κ + 1)) :
      (if (l : ℕ) < κ + 1 - τ then (0 : ℝ) else 1) =
        (if κ - l < τ then 1 else 0) := by
    have hl := l.isLt
    split_ifs <;> first | rfl | omega
  have hd (l : Fin (κ + 1)) :
      (if (l : ℕ) < κ + 1 - τ then (2 : ℝ) else 2 * (1 + u)) =
        (if κ - l < τ then 2 * (1 + u) else 2) := by
    have hl := l.isLt
    split_ifs <;> first | rfl | omega
  have hh (l : Fin (κ + 1)) :
      averagedConstrainedReplicaHeatExpression Z (fun j => m (κ - j)) v (κ + 1 - τ)
        l (κ + 1 - l) u (if (l : ℕ) < κ + 1 - τ then 2 else 2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1
          (if (l : ℕ) < κ + 1 - τ then 0 else 1) p.1 q.1) x y = H l := by
    have hi : (l : ℕ) + (κ + 1 - l) = κ + 1 := by omega
    simp only [averagedConstrainedReplicaHeatExpression, hi, hc, hd,
      averagedConstrainedReplicaMoment, H, B, μ, Nat.sub_zero]
  have hsum := pairCovarianceExpression_eq_trace_sub_heat β t u m ρ τ κ
    hm0 hmκ hρ0 hρ1 hτ hu μ
  change t / 2 *
    ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
        m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) * H l) = _ at hsum
  rw [← hsum]
  unfold averagedReplicaPressureDerivative
  simp_rw [hh]
  change t / 2 *
    (β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
      m (κ - i) * (A i - A (i + 1))) +
    (∑ l : Fin (κ + 1), -(t * β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) / 2 * H l) = _
  have he (l : Fin (κ + 1)) :
      -(t * β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) / 2 * H l =
        -(t / 2) * (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) * H l) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- The actual covariance derivative is bounded by the deterministic
correction. Positivity and normalization come from the actual averaged split
weights. Repeated masses and zero variances are allowed. -/
theorem averagedReplicaPressureDerivative_le
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (u β : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ v : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hm : ∀ i, 0 ≤ m (κ - i)) (hv : ∀ i, 0 ≤ v i)
    (hmono : ∀ p < κ, m p ≤ m (p + 1))
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = u)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    averagedReplicaPressureDerivative Z u β t (fun j => m (κ - j)) v
      (fun j => -(t * β ^ 2 * (ρ (κ - j + 1) - ρ (κ - j)))) (κ + 1 - τ) (κ + 1) x y ≤
      -t * pairCascadeCorrection β m ρ (fun p => ρ (min p τ)) κ := by
  rw [averagedReplicaPressureDerivative_eq_covariance Z u β t m ρ v τ κ
    hm0 hmκ hρ0 hρ1 hτ hu x y]
  apply pairCovarianceExpression_le β u ht m ρ (fun p => ρ (min p τ)) κ hmκ hmono
    hρ0 (by simpa using hρ0) hρ1 (by simpa only [min_eq_right hτ] using hu)
  · intro p _ a b
    exact averagedConstrainedCascadeReplica_nonneg Z u (fun j => m (κ - j)) v hm hv
      (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y a b
  · intro p _
    exact sum_averagedConstrainedCascadeReplica hZ u (fun j => m (κ - j)) v hm hv
      (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y

end SpinGlass.Targets
