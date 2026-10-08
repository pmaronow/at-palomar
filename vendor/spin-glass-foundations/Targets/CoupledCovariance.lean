module

/-
# Four-replica covariance identities for Talagrand's second interpolation

The normalized SK pair covariance is a sum of four squared overlaps. The
field covariance supplies its linear part, leaving a nonnegative squared
matrix difference. This is the algebra used on pp. 239--241 of Talagrand (2006).
The actual terminal Hessian contraction is also proved; the induction through
the positive-mass cascade and disorder integration by parts remain separate.
-/
public import Targets.ConstrainedFiniteState

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Normalized covariance of the two replica energies (four cross overlaps). -/
noncomputable def pairSKCovariance {n : ℕ} (β : ℝ) (p q : Config n × Config n) : ℝ :=
  β ^ 2 / 2 * ∑ a : Fin 2, ∑ b : Fin 2, (AT.pairOverlapMatrix p q a b) ^ 2

/-- The matrix of trial self and cross overlaps. Cross entries may be signed. -/
def pairTrialMatrix (q c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![q, c; c, q]

/-- Linear covariance contribution of the two Gaussian fields. -/
noncomputable def pairFieldCovariance {n : ℕ} (β q c : ℝ) (p z : Config n × Config n) : ℝ :=
  β ^ 2 * ∑ a : Fin 2, ∑ b : Fin 2, pairTrialMatrix q c a b * AT.pairOverlapMatrix p z a b

/-- The sum of the four nonnegative convexity remainders in Theorem 3.1. -/
noncomputable def pairCovarianceDefect {n : ℕ} (β q c : ℝ) (p z : Config n × Config n) : ℝ :=
  β ^ 2 / 2 * ∑ a : Fin 2, ∑ b : Fin 2,
    (AT.pairOverlapMatrix p z a b - pairTrialMatrix q c a b) ^ 2

theorem pairCovarianceDefect_nonneg {n : ℕ} (β q c : ℝ) (p z : Config n × Config n) :
    0 ≤ pairCovarianceDefect β q c p z := by
  unfold pairCovarianceDefect
  positivity

/-- Reuse RSAT's scalar quadratic covariance identity in each matrix entry. -/
theorem sk_entry_remainder (β x q : ℝ) :
    β ^ 2 / 2 * x ^ 2 - β ^ 2 * q * x + β ^ 2 / 2 * q ^ 2 =
      β ^ 2 / 2 * (x - q) ^ 2 := by
  have H := AT.gtCovariance_remainder β 0 1 x q
  simp only [AT.gtCovarianceFunction, sub_self, mul_zero, zero_mul, zero_add, one_mul] at H
  nlinarith only [H]

theorem pairCovariance_completion {n : ℕ} (β q c : ℝ) (p z : Config n × Config n) :
    pairSKCovariance β p z - pairFieldCovariance β q c p z =
      pairCovarianceDefect β q c p z - β ^ 2 * (q ^ 2 + c ^ 2) := by
  have he (a b : Fin 2) := sk_entry_remainder β
    (AT.pairOverlapMatrix p z a b) (pairTrialMatrix q c a b)
  have H := congrArg (fun f : Fin 2 → Fin 2 → ℝ => ∑ a, ∑ b, f a b)
    (funext fun a => funext (he a))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at H
  have hQ : (∑ a : Fin 2, ∑ b : Fin 2, pairTrialMatrix q c a b ^ 2) = 2 * (q ^ 2 + c ^ 2) := by
    simp [pairTrialMatrix, Fin.sum_univ_two]
    ring
  rw [hQ] at H
  unfold pairSKCovariance pairFieldCovariance pairCovarianceDefect
  have hl : (∑ a : Fin 2, ∑ b : Fin 2, β ^ 2 * pairTrialMatrix q c a b *
      AT.pairOverlapMatrix p z a b) =
      β ^ 2 * ∑ a : Fin 2, ∑ b : Fin 2, pairTrialMatrix q c a b * AT.pairOverlapMatrix p z a b := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hl] at H
  nlinarith only [H]

theorem pairSKCovariance_self {n : ℕ} (hn : 0 < n) (β : ℝ) {u : ℝ}
    (p : AT.ConstrainedPair n u) : pairSKCovariance β p.1 p.1 = β ^ 2 * (1 + u ^ 2) := by
  simp [pairSKCovariance, AT.pairOverlapMatrix_self hn, Fin.sum_univ_two]
  ring

/-- The constrained diagonal matches the terminal trial matrix exactly. -/
theorem pairCovarianceDefect_self {n : ℕ} (hn : 0 < n) (β : ℝ) {u : ℝ}
    (p : AT.ConstrainedPair n u) : pairCovarianceDefect β 1 u p.1 p.1 = 0 := by
  simp [pairCovarianceDefect, AT.pairOverlapMatrix_self hn, pairTrialMatrix]

/-- Independent replica field directions contract to the two diagonal overlaps. -/
theorem independent_pair_spin_contraction {n : ℕ} (hn : 0 < n)
    (p q : Config n × Config n) :
    (∑ i, (spin n p.1 i * spin n q.1 i + spin n p.2 i * spin n q.2 i)) =
      n * (AT.pairOverlapMatrix p q 0 0 + AT.pairOverlapMatrix p q 1 1) := by
  rw [Finset.sum_add_distrib, AT.spin_sum_eq_mul_overlap hn, AT.spin_sum_eq_mul_overlap hn]
  simp [AT.pairOverlapMatrix, AT.pairConfig, mul_add]

/-- Shared or anti-shared field directions produce the two additional cross overlaps. -/
theorem shared_pair_spin_contraction {n : ℕ} (hn : 0 < n) {e : ℝ} (he : e ^ 2 = 1)
    (p q : Config n × Config n) :
    (∑ i, (spin n p.1 i + e * spin n p.2 i) * (spin n q.1 i + e * spin n q.2 i)) =
      n * (AT.pairOverlapMatrix p q 0 0 + AT.pairOverlapMatrix p q 1 1 +
        e * (AT.pairOverlapMatrix p q 0 1 + AT.pairOverlapMatrix p q 1 0)) := by
  have hex (i : Fin n) :
      (spin n p.1 i + e * spin n p.2 i) * (spin n q.1 i + e * spin n q.2 i) =
      spin n p.1 i * spin n q.1 i + spin n p.2 i * spin n q.2 i +
        e * (spin n p.1 i * spin n q.2 i + spin n p.2 i * spin n q.1 i) := by
    calc
      _ = spin n p.1 i * spin n q.1 i + e ^ 2 * (spin n p.2 i * spin n q.2 i) +
          e * (spin n p.1 i * spin n q.2 i + spin n p.2 i * spin n q.1 i) := by ring
      _ = _ := by rw [he, one_mul]
  simp only [hex, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [AT.spin_sum_eq_mul_overlap hn]
  simp [AT.pairOverlapMatrix, AT.pairConfig]
  ring

/-- Finite contraction of Gibbs covariances, with no probabilistic assumptions
needed for the rearrangement itself. -/
theorem sum_covariance_contraction {I S : Type*} [Fintype I] [Fintype S]
    (c : I → ℝ) (P : S → ℝ) (v : I → S → ℝ) :
    (∑ i, c i * ((∑ p, P p * v i p * v i p) -
      (∑ p, P p * v i p) * (∑ p, P p * v i p))) =
      (∑ p, P p * (∑ i, c i * v i p * v i p)) -
        ∑ p, ∑ q, P p * P q * (∑ i, c i * v i p * v i q) := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hd : (∑ i, c i * (∑ p, P p * v i p * v i p)) =
      ∑ p, P p * (∑ i, c i * v i p * v i p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Contract the actual spectral coordinates of the abstract SK disorder.
This is (3.34)'s sum of four covariances, not an assumed covariance formula. -/
theorem pairSKCovariance_spectral_sum {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (p q : Config n × Config n) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      (sk.hU.w i p.1 + sk.hU.w i p.2) * (sk.hU.w i q.1 + sk.hU.w i q.2)) =
      n * pairSKCovariance β p q := by
  have he (i : sk.hU.ι) : (sk.hU.τ i : ℝ) *
      (sk.hU.w i p.1 + sk.hU.w i p.2) * (sk.hU.w i q.1 + sk.hU.w i q.2) =
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.1 * sk.hU.w i q.1) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.1 * sk.hU.w i q.2) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.2 * sk.hU.w i q.1) +
      (sk.hU.τ i : ℝ) * (sk.hU.w i p.2 * sk.hU.w i q.2) := by ring
  simp_rw [he, Finset.sum_add_distrib, sk_covariance_spectral_sum β h sk]
  simp [pairSKCovariance, AT.pairOverlapMatrix, AT.pairConfig, Fin.sum_univ_two, sk_cov_kernel]
  ring

/-- The actual constrained terminal Hessian contracted with the SK covariance.
The diagonal is constant precisely because the state space fixes the overlap. -/
theorem constrainedPairSecond_SK_trace {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairSecond n u U (sk.hU.w i) (sk.hU.w i) x y) =
      n * (β ^ 2 * (1 + u ^ 2) - ∑ p : AT.ConstrainedPair n u, ∑ q : AT.ConstrainedPair n u,
        constrainedPairGibbs n U u x y p * constrainedPairGibbs n U u x y q *
          pairSKCovariance β p.1 q.1) := by
  simp only [constrainedPairSecond_eq_covariance]
  rw [sum_covariance_contraction]
  simp_rw [pairSKCovariance_spectral_sum β h sk, pairSKCovariance_self hn β]
  rw [← Finset.sum_mul, sum_constrainedPairGibbs, one_mul]
  have he : (∑ p : AT.ConstrainedPair n u, ∑ q : AT.ConstrainedPair n u,
      constrainedPairGibbs n U u x y p * constrainedPairGibbs n U u x y q *
        (n * pairSKCovariance β p.1 q.1)) =
      n * ∑ p : AT.ConstrainedPair n u, ∑ q : AT.ConstrainedPair n u,
        constrainedPairGibbs n U u x y p * constrainedPairGibbs n U u x y q *
          pairSKCovariance β p.1 q.1 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  ring

end SpinGlass.Targets
