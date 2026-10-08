module

public import Targets.CoupledCovarianceTelescope

@[expose] public section

/-!
# Covariance telescoping with arbitrary signed trial increments

The existing finite replica telescope does not require one sharing cutoff.
Here the heat kernels are written as increments of a general two-replica trial
matrix. This includes signed shared increments and zero increments at frozen
physical tags. This is finite algebra, not an assumed pressure derivative.
-/

open scoped BigOperators

namespace SpinGlass.Targets

/-- Linearity of the trial-field covariance in its diagonal and cross entries. -/
theorem pairFieldCovariance_sub {n : ℕ} (β q q' c c' : ℝ) (a b : Config n × Config n) :
    pairFieldCovariance β q' c' a b - pairFieldCovariance β q c a b =
      pairFieldCovariance β (q' - q) (c' - c) a b := by
  simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
  ring

/-- Reversed field increments telescope under the same split law, for any
cross-overlap path. No positivity or division by an increment is used. -/
theorem replicaHeatTail_pairField_increments {n : ℕ} {u : ℝ}
    (β : ℝ) (ρ c : ℕ → ℝ) (hρ : ρ 0 = 0) (hc : c 0 = 0) (κ i : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    replicaHeatTail (fun a l => ∑ p, ∑ q, μ a p q *
      pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
        (c (κ - l + 1) - c (κ - l)) p.1 q.1) (κ + 1) i =
      ∑ p, ∑ q, μ i p q * pairFieldCovariance β (ρ (κ + 1 - i)) (c (κ + 1 - i)) p.1 q.1 := by
  let C := fun a j => ∑ p, ∑ q, μ a p q * pairFieldCovariance β (ρ j) (c j) p.1 q.1
  have he (a l : ℕ) : (∑ p, ∑ q, μ a p q *
      pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
        (c (κ - l + 1) - c (κ - l)) p.1 q.1) = C a (κ - l + 1) - C a (κ - l) := by
    simp only [C, ← Finset.sum_sub_distrib, ← mul_sub, pairFieldCovariance_sub]
  simp_rw [he]
  rw [replicaHeatTail_reverse_increments]
  have hzero : C i 0 = 0 := by
    simp [C, hρ, hc, pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
  rw [hzero, sub_zero]

/-- The diagonal contractions depend only on the trial matrix's endpoints. -/
theorem sum_pairField_increment_diagonal (β u : ℝ) (ρ c : ℕ → ℝ) (κ : ℕ)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u) :
    (∑ l : Fin (κ + 1), 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))) =
      2 * β ^ 2 * (1 + u ^ 2) := by
  let F := fun p => 2 * β ^ 2 * (ρ p + u * c p)
  have he (l : ℕ) : 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l))) =
      F (κ - l + 1) - F (κ - l) := by dsimp [F]; ring
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun l => F (κ - l + 1) - F (κ - l)) (κ + 1)]
  have hrev := Finset.sum_range_reflect (fun p => F (p + 1) - F p) (κ + 1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [hrev, Finset.sum_range_sub]
  simp only [F, hρ0, hc0, hρ1, hc1]
  ring

/-- The SK trace minus the heat from arbitrary trial-matrix increments is
exactly the existing square-completion expression. The same actual split law
must be used in both terms; no relation to a derivative is postulated here. -/
theorem pairCovarianceExpression_eq_trace_sub_increment_heat {n : ℕ}
    (β t u : ℝ) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
    let B := fun i l => ∑ p, ∑ q, μ i p q *
      pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
        (c (κ - l + 1) - c (κ - l)) p.1 q.1
    let D := fun l => 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))
    t / 2 *
      ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
          m (κ - i) * (A i - A (i + 1))) -
        ∑ l : Fin (κ + 1),
          ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
            m (κ - l) * B l l)) =
      pairCovarianceExpression β t u m ρ c κ (fun p => μ (κ - p)) := by
  dsimp only
  let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
      (c (κ - l + 1) - c (κ - l)) p.1 q.1
  let D := fun l => 2 * β ^ 2 *
    ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))
  change t / 2 *
    ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1), m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1),
        ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
          m (κ - l) * B l l)) = _
  have H := replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A (fun _ => 1) D B
    (β ^ 2 * (1 + u ^ 2)) κ (by simpa using hmκ) (by simpa using hm0)
  simp only [one_mul] at H
  rw [H]
  have hd : (∑ l : Fin (κ + 1), D l) = 2 * β ^ 2 * (1 + u ^ 2) :=
    sum_pairField_increment_diagonal β u ρ c κ hρ0 hc0 hρ1 hc1
  rw [hd]
  have hb (i : ℕ) : replicaHeatTail B (κ + 1) i =
      ∑ p, ∑ q, μ i p q * pairFieldCovariance β (ρ (κ + 1 - i)) (c (κ + 1 - i)) p.1 q.1 :=
    replicaHeatTail_pairField_increments β ρ c hρ0 hc0 κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ + 1 - i)) (c (κ + 1 - i)) p.1 q.1
  change t / 2 * (β ^ 2 * (1 + u ^ 2) - 2 * β ^ 2 * (1 + u ^ 2) +
    ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ, replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (pairSKCovariance β a.1 b.1 - pairFieldCovariance β (ρ (p + 1)) (c (p + 1)) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [pairCovarianceExpression]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z) (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  ring

end SpinGlass.Targets
