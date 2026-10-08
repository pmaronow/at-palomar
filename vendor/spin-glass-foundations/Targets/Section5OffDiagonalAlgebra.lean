module

public import Targets.Section5CovarianceIdentity

@[expose] public section

/-!
# Trial/constraint overlap mismatch

The covariance square completion does not require the terminal cross-overlap
of the Gaussian trial path to equal the constrained overlap.  If these two
numbers are `v` and `u`, respectively, the only loss is the explicit
quadratic term `t * β² / 2 * (u-v)²`.  This endpoint-safe form is the bridge
used to pass a strict physical-neighbor estimate through that breakpoint.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The heat diagonal telescopes with the constrained and trial overlaps
kept distinct. -/
theorem sum_pairField_heat_diagonal_mismatch (β u v : ℝ) (ρ : ℕ → ℝ)
    (τ κ : ℕ) (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hτ : τ ≤ κ + 1) (hv : ρ τ = v) :
    (∑ l ∈ Finset.range (κ + 1),
      β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        (if κ - l < τ then 2 * (1 + u) else 2)) =
      2 * β ^ 2 * (1 + u * v) := by
  let F := fun p => 2 * β ^ 2 * (ρ p + u * ρ (min p τ))
  have he (p : ℕ) : β ^ 2 * (ρ (p + 1) - ρ p) *
      (if p < τ then 2 * (1 + u) else 2) = F (p + 1) - F p := by
    by_cases hp : p < τ
    · simp only [F, if_pos hp, min_eq_left (by omega : p + 1 ≤ τ),
        min_eq_left (by omega : p ≤ τ)]
      ring
    · simp only [F, if_neg hp, min_eq_right (by omega : τ ≤ p + 1),
        min_eq_right (by omega : τ ≤ p)]
      ring
  simp_rw [he]
  have hrev := Finset.sum_range_reflect (fun p => F (p + 1) - F p) (κ + 1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [hrev, Finset.sum_range_sub]
  simp only [F, hρ0, hρ1, min_eq_right hτ, Nat.zero_min, hv]
  ring

/-- Square completion with an arbitrary terminal trial cross-overlap. -/
theorem pairCovarianceExpression_eq_mismatch {n : ℕ} (β t u v : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    pairCovarianceExpression β t u m ρ c κ μ =
      -t * pairCascadeCorrection β m ρ c κ +
        t * (β ^ 2 / 2) * (v ^ 2 - u ^ 2) -
          pairCovarianceRemainder β t u m ρ c κ μ := by
  classical
  have he (l : ℕ) (hl : l < κ) :
      (∑ p, ∑ q, μ l p q * (pairSKCovariance β p.1 q.1 -
        pairFieldCovariance β (ρ (l + 1)) (c (l + 1)) p.1 q.1)) =
      (∑ p, ∑ q, μ l p q *
        pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * pairTrialEnergy β (ρ (l + 1)) (c (l + 1)) := by
    simp_rw [pairCovariance_completion, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    rw [hμ l hl, one_mul]
    unfold pairTrialEnergy
    ring
  unfold pairCovarianceExpression pairCovarianceRemainder
  rw [pairCascadeCorrection_telescope β m ρ c κ hm hρ0 hc0, hρ1, hc1]
  have hs := Finset.sum_congr rfl (fun l hl =>
    congrArg (fun x => (m l - m (l + 1)) * x)
      (he l (Finset.mem_range.mp hl)))
  rw [hs]
  have hd (l : ℕ) : (m l - m (l + 1)) *
      ((∑ p, ∑ q, μ l p q *
        pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * pairTrialEnergy β (ρ (l + 1)) (c (l + 1))) =
      2 * ((m (l + 1) - m l) *
        pairTrialEnergy β (ρ (l + 1)) (c (l + 1))) -
      (m (l + 1) - m l) * ∑ p, ∑ q,
        μ l p q * pairCovarianceDefect β (ρ (l + 1))
          (c (l + 1)) p.1 q.1 := by ring
  simp_rw [hd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold pairTrialEnergy
  ring

/-- The mismatch version of the deterministic covariance upper bound. -/
theorem pairCovarianceExpression_le_mismatch {n : ℕ} (β u v : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm : m κ = 1) (hmono : ∀ l < κ, m l ≤ m (l + 1))
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ0 : ∀ l < κ, ∀ p q, 0 ≤ μ l p q)
    (hμ1 : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    pairCovarianceExpression β t u m ρ c κ μ ≤
      -t * pairCascadeCorrection β m ρ c κ +
        t * (β ^ 2 / 2) * (v ^ 2 - u ^ 2) := by
  rw [pairCovarianceExpression_eq_mismatch β t u v m ρ c κ hm hρ0 hc0 hρ1 hc1 μ hμ1]
  exact sub_le_self _
    (pairCovarianceRemainder_nonneg β u ht m ρ c κ hmono μ hμ0)

variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The differentiated pressure equals the usual covariance expression plus
the explicit linear endpoint-mismatch term. -/
theorem averagedReplicaPressureDerivative_eq_covariance_mismatch
    (Z : Ω → EnergySpace n) (u v β t : ℝ) (m ρ wvar : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hτ : τ ≤ κ + 1) (hv : ρ τ = v)
    (x y : Fin n → ℝ) :
    averagedReplicaPressureDerivative Z u β t (fun j => m (κ - j)) wvar
      (fun j => -(t * β ^ 2 * (ρ (κ - j + 1) - ρ (κ - j))))
      (κ + 1 - τ) (κ + 1) x y =
      pairCovarianceExpression β t u m ρ (fun p => ρ (min p τ)) κ
        (fun p => averagedConstrainedCascadeReplica Z u
          (fun j => m (κ - j)) wvar (κ + 1 - τ)
          (κ - p) (κ + 1 - (κ - p)) x y) +
        t * β ^ 2 * u * (u - v) := by
  let μ := fun i => averagedConstrainedCascadeReplica Z u
    (fun j => m (κ - j)) wvar (κ + 1 - τ) i (κ + 1 - i) x y
  let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
  let H := fun l =>
    ((if κ - l < τ then 2 * (1 + u) else 2) - B 0 l +
      ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
      m (κ - l) * B l l
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
      averagedConstrainedReplicaHeatExpression Z (fun j => m (κ - j)) wvar
        (κ + 1 - τ) l (κ + 1 - l) u
        (if (l : ℕ) < κ + 1 - τ then 2 else 2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1
          (if (l : ℕ) < κ + 1 - τ then 0 else 1) p.1 q.1) x y = H l := by
    have hi : (l : ℕ) + (κ + 1 - l) = κ + 1 := by omega
    simp only [averagedConstrainedReplicaHeatExpression, hi, hc, hd,
      averagedConstrainedReplicaMoment, H, B, μ, Nat.sub_zero]
  simp only [averagedReplicaPressureDerivative]
  simp_rw [hh]
  change t / 2 *
    (β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
      m (κ - i) * (A i - A (i + 1))) +
    (∑ l : Fin (κ + 1),
      -(t * β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) / 2 * H l) = _
  simp_rw [show ∀ l : Fin (κ + 1),
      -(t * β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) / 2 * H l =
        -(t / 2) * (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) * H l) by
    intro l; ring]
  dsimp [H]
  rw [← Finset.mul_sum]
  rw [neg_mul, ← sub_eq_add_neg, ← mul_sub]
  rw [replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A
    (fun l => β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)))
    (fun l => if κ - l < τ then 2 * (1 + u) else 2) B
    (β ^ 2 * (1 + u ^ 2)) κ (by simpa using hmκ) (by simpa using hm0)]
  have hdiag : (∑ l : Fin (κ + 1),
      β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        (if κ - l < τ then 2 * (1 + u) else 2)) =
      2 * β ^ 2 * (1 + u * v) := by
    rw [Fin.sum_univ_eq_sum_range (fun l =>
      β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        (if κ - l < τ then 2 * (1 + u) else 2)) (κ + 1)]
    simpa only [Finset.sum_range] using
      (sum_pairField_heat_diagonal_mismatch β u v ρ τ κ hρ0 hρ1 hτ hv)
  rw [hdiag]
  have hb (i : ℕ) : replicaHeatTail
      (fun i l => β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) * B i l)
      (κ + 1) i =
      ∑ p, ∑ q, μ i p q * pairFieldCovariance β
        (ρ (κ + 1 - i)) (ρ (min (κ + 1 - i) τ)) p.1 q.1 :=
    replicaHeatTail_pairFieldCovariance β ρ hρ0 τ κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ + 1 - i))
      (ρ (min (κ + 1 - i) τ)) p.1 q.1
  change t / 2 * (β ^ 2 * (1 + u ^ 2) -
      2 * β ^ 2 * (1 + u * v) +
      ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ,
    replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (pairSKCovariance β a.1 b.1 -
          pairFieldCovariance β (ρ (p + 1))
            (ρ (min (p + 1) τ)) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [pairCovarianceExpression]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z)
      (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  ring

/-- Covariance derivative bound for a trial path ending at `v` while the
finite state space is constrained at `u`. -/
theorem averagedReplicaPressureDerivative_le_mismatch
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (u v β : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m ρ wvar : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hm : ∀ i, 0 ≤ m (κ - i)) (hwvar : ∀ i, 0 ≤ wvar i)
    (hmono : ∀ p < κ, m p ≤ m (p + 1))
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hτ : τ ≤ κ + 1) (hv : ρ τ = v)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    averagedReplicaPressureDerivative Z u β t (fun j => m (κ - j)) wvar
      (fun j => -(t * β ^ 2 * (ρ (κ - j + 1) - ρ (κ - j))))
      (κ + 1 - τ) (κ + 1) x y ≤
      -t * pairCascadeCorrection β m ρ (fun p => ρ (min p τ)) κ +
        t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  rw [averagedReplicaPressureDerivative_eq_covariance_mismatch Z u v β t m ρ
    wvar τ κ hm0 hmκ hρ0 hρ1 hτ hv x y]
  have H := pairCovarianceExpression_le_mismatch β u v ht m ρ
    (fun p => ρ (min p τ)) κ hmκ hmono hρ0 (by simpa using hρ0)
    hρ1 (by simpa only [min_eq_right hτ] using hv)
    (fun p => averagedConstrainedCascadeReplica Z u (fun j => m (κ - j))
      wvar (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y)
    (fun p hp a b => averagedConstrainedCascadeReplica_nonneg Z u
      (fun j => m (κ - j)) wvar hm hwvar (κ + 1 - τ)
      (κ - p) (κ + 1 - (κ - p)) x y a b)
    (fun p hp => sum_averagedConstrainedCascadeReplica hZ u
      (fun j => m (κ - j)) wvar hm hwvar (κ + 1 - τ)
      (κ - p) (κ + 1 - (κ - p)) x y)
  nlinarith only [H]

end SpinGlass.Targets
