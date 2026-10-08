module

/-
# The algebraic last step of Theorem 3.1

The four-replica covariance expression splits into the deterministic cascade
correction minus a nonnegative sum of squares. This file proves that statement
for normalized nonnegative finite replica weights. It does NOT identify this
expression with the derivative of `section5Interpolation`; the nested Gaussian
differentiation and integration-by-parts step remains to be proved.
-/
public import Targets.CoupledCovariance
public import Mathlib.Algebra.BigOperators.Module

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Half the quadratic energy of the symmetric two-replica trial matrix. -/
noncomputable def pairTrialEnergy (β q c : ℝ) : ℝ := β ^ 2 / 2 * (q ^ 2 + c ^ 2)

/-- The correction in Theorem 3.1, with forward level indices. -/
noncomputable def pairCascadeCorrection (β : ℝ) (m ρ c : ℕ → ℝ) (κ : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (κ + 1), m p *
    (pairTrialEnergy β (ρ (p + 1)) (c (p + 1)) - pairTrialEnergy β (ρ p) (c p))

/-- Summation by parts is reused from Mathlib, with the zero initial energy. -/
theorem pairCascadeCorrection_telescope (β : ℝ) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm : m κ = 1) (hρ : ρ 0 = 0) (hc : c 0 = 0) :
    pairCascadeCorrection β m ρ c κ = pairTrialEnergy β (ρ (κ + 1)) (c (κ + 1)) -
      ∑ l ∈ Finset.range κ, (m (l + 1) - m l) * pairTrialEnergy β (ρ (l + 1)) (c (l + 1)) := by
  have H := Finset.sum_range_by_parts m
    (fun p => pairTrialEnergy β (ρ (p + 1)) (c (p + 1)) - pairTrialEnergy β (ρ p) (c p)) (κ + 1)
  have hz : pairTrialEnergy β (ρ 0) (c 0) = 0 := by simp [pairTrialEnergy, hρ, hc]
  simp_rw [Finset.sum_range_sub (fun p => pairTrialEnergy β (ρ p) (c p))] at H
  simp only [hz, sub_zero, Nat.add_sub_cancel, hm, smul_eq_mul, one_mul] at H
  exact H

/-- The explicit covariance expression obtained after the intended nested IBP.
Index l of mu represents the paper's measure mu_(l+1). -/
noncomputable def pairCovarianceExpression {n : ℕ} (β t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) : ℝ :=
  t / 2 * (-β ^ 2 * (1 + u ^ 2) + ∑ l ∈ Finset.range κ,
    (m l - m (l + 1)) * ∑ p, ∑ q, μ l p q *
      (pairSKCovariance β p.1 q.1 - pairFieldCovariance β (ρ (l + 1)) (c (l + 1)) p.1 q.1))

/-- The algebraic square remainder; it is not yet a theorem about eta'. -/
noncomputable def pairCovarianceRemainder {n : ℕ} (β t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) : ℝ :=
  t / 2 * ∑ l ∈ Finset.range κ, (m (l + 1) - m l) * ∑ p, ∑ q,
    μ l p q * pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1

theorem pairCovarianceRemainder_nonneg {n : ℕ} (β u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : ∀ l < κ, m l ≤ m (l + 1))
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∀ p q, 0 ≤ μ l p q) : 0 ≤ pairCovarianceRemainder β t u m ρ c κ μ := by
  apply mul_nonneg (div_nonneg ht (by norm_num))
  apply Finset.sum_nonneg
  intro l hl
  have hl' := Finset.mem_range.mp hl
  apply mul_nonneg (sub_nonneg.mpr (hm l hl'))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (hμ l hl' p q) (pairCovarianceDefect_nonneg _ _ _ _ _)

/-- Exact completion of the four overlap squares and the two telescoping sums.
All hypotheses concern explicit finite coefficients and weights, not eta'. -/
theorem pairCovarianceExpression_eq {n : ℕ} (β t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    pairCovarianceExpression β t u m ρ c κ μ =
      -t * pairCascadeCorrection β m ρ c κ - pairCovarianceRemainder β t u m ρ c κ μ := by
  classical
  have he (l : ℕ) (hl : l < κ) :
      (∑ p, ∑ q, μ l p q * (pairSKCovariance β p.1 q.1 -
        pairFieldCovariance β (ρ (l + 1)) (c (l + 1)) p.1 q.1)) =
      (∑ p, ∑ q, μ l p q * pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * pairTrialEnergy β (ρ (l + 1)) (c (l + 1)) := by
    simp_rw [pairCovariance_completion, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hμ l hl, one_mul]
    unfold pairTrialEnergy
    ring
  unfold pairCovarianceExpression pairCovarianceRemainder
  rw [pairCascadeCorrection_telescope β m ρ c κ hm hρ0 hc0, hρ1, hc1]
  have hs := Finset.sum_congr rfl (fun l hl => congrArg (fun x => (m l - m (l + 1)) * x)
    (he l (Finset.mem_range.mp hl)))
  rw [hs]
  have hd (l : ℕ) : (m l - m (l + 1)) *
      ((∑ p, ∑ q, μ l p q * pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * pairTrialEnergy β (ρ (l + 1)) (c (l + 1))) =
      2 * ((m (l + 1) - m l) * pairTrialEnergy β (ρ (l + 1)) (c (l + 1))) -
      (m (l + 1) - m l) * ∑ p, ∑ q,
        μ l p q * pairCovarianceDefect β (ρ (l + 1)) (c (l + 1)) p.1 q.1 := by ring
  simp_rw [hd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold pairTrialEnergy
  ring

theorem pairCovarianceExpression_le {n : ℕ} (β u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1) (hmono : ∀ l < κ, m l ≤ m (l + 1))
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ0 : ∀ l < κ, ∀ p q, 0 ≤ μ l p q) (hμ1 : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    pairCovarianceExpression β t u m ρ c κ μ ≤ -t * pairCascadeCorrection β m ρ c κ := by
  rw [pairCovarianceExpression_eq β t u m ρ c κ hm hρ0 hc0 hρ1 hc1 μ hμ1]
  exact sub_le_self _ (pairCovarianceRemainder_nonneg β u ht m ρ c κ hmono μ hμ0)

/-- The min(l,tau) cross-overlap path doubles exactly the shared-level correction. -/
theorem pairCascadeCorrection_eq_split (β : ℝ) (m ρ : ℕ → ℝ) (κ τ : ℕ) :
    pairCascadeCorrection β m ρ (fun l => ρ (min l τ)) κ =
      ∑ p ∈ Finset.range (κ + 1), (if p < τ then (2 : ℝ) else 1) * m p *
        (β ^ 2 / 2 * (ρ (p + 1) ^ 2 - ρ p ^ 2)) := by
  apply Finset.sum_congr rfl
  intro p _
  unfold pairTrialEnergy
  by_cases hp : p < τ
  · simp only [if_pos hp, min_eq_left (by omega : p ≤ τ), min_eq_left (by omega : p + 1 ≤ τ)]
    ring
  · simp only [if_neg hp, min_eq_right (by omega : τ ≤ p), min_eq_right (by omega : τ ≤ p + 1)]
    ring

/-- The same deterministic correction applies to the signed shared-field branch. -/
theorem pairCascadeCorrection_eq_signed_split (β : ℝ) (m ρ : ℕ → ℝ) (κ τ : ℕ)
    {e : ℝ} (he : e ^ 2 = 1) :
    pairCascadeCorrection β m ρ (fun l => e * ρ (min l τ)) κ =
      ∑ p ∈ Finset.range (κ + 1), (if p < τ then (2 : ℝ) else 1) * m p *
        (β ^ 2 / 2 * (ρ (p + 1) ^ 2 - ρ p ^ 2)) := by
  simpa only [pairCascadeCorrection, pairTrialEnergy, mul_pow, he, one_mul] using
    pairCascadeCorrection_eq_split β m ρ κ τ

/-- The correction in (5.9), for the actual inserted Section 5 sequences.
This identifies the deterministic term; it does not assume or assert (5.9)'s
pressure inequality before the nested IBP has been proved. -/
theorem section5Correction_eq {k : ℕ} (s : RSBScheme k) (β u m : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    pairCascadeCorrection β (section5Mass s r m) (section5Rho s r u)
      (fun l => section5Rho s r u (min l r)) (k + 2) =
      2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - u ^ 2)) := by
  let θ := fun x : ℝ => β ^ 2 / 2 * x ^ 2
  let f := fun p => (if p < r then (2 : ℝ) else 1) * section5Mass s r m p *
    (θ (section5Rho s r u (p + 1)) - θ (section5Rho s r u p))
  let g := fun p => s.m p * (θ (s.q (p + 1)) - θ (s.q p))
  let δ := (m - s.m (r - 1)) * (θ (s.q r) - θ u)
  have hbefore (p : ℕ) (hp : p + 1 < r) : f p = g p := by
    simp only [f, g, section5Mass, section5Rho, if_pos (by omega : p < r), if_pos hp]
    ring
  have hsplit : f (r - 1) = s.m (r - 1) * (θ u - θ (s.q (r - 1))) := by
    have hi : r - 1 + 1 = r := by omega
    simp only [f, section5Mass, section5Rho, hi, if_pos (by omega : r - 1 < r),
      lt_self_iff_false, if_false, if_true]
    ring
  have hnew : f r = m * (θ (s.q r) - θ u) := by
    simp [f, section5Mass, section5Rho, show ¬r + 1 < r by omega]
  have hafter (p : ℕ) (hp : r < p) : f p = g (p - 1) := by
    simp only [f, g, section5Mass, section5Rho, if_neg (by omega : ¬p < r),
      if_neg (by omega : p ≠ r), if_neg (by omega : ¬p + 1 < r),
      if_neg (by omega : p + 1 ≠ r), Nat.add_sub_cancel,
      show p - 1 + 1 = p by omega, one_mul]
  have hpartial : ∀ j, r ≤ j → (∑ p ∈ Finset.range (j + 1), f p) =
      (∑ p ∈ Finset.range j, g p) + δ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have hi : r - 1 + 1 = r := by omega
      have hf := Finset.sum_range_succ f (r - 1)
      have hg := Finset.sum_range_succ g (r - 1)
      rw [hi] at hf hg
      have hprefix : (∑ p ∈ Finset.range (r - 1), f p) = ∑ p ∈ Finset.range (r - 1), g p := by
        exact Finset.sum_congr rfl (fun p hp => hbefore p (by simp only [Finset.mem_range] at hp; omega))
      rw [Finset.sum_range_succ, hf, hprefix, hsplit, hnew, hg]
      dsimp [g, δ]
      rw [hi]
      ring
    | succ j hj ih =>
      rw [Finset.sum_range_succ, ih, hafter (j + 1) (by omega), Nat.add_sub_cancel,
        Finset.sum_range_succ]
      ring
  have hbase : (∑ p ∈ Finset.range (k + 2), g p) = 2 * parisiCorrection s β := by
    rw [Finset.sum_range_succ']
    simp only [g, s.m_zero, zero_mul, add_zero, parisiCorrection, θ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  calc
    _ = ∑ p ∈ Finset.range (k + 3), f p := by
      rw [pairCascadeCorrection_eq_split]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f, θ]
      ring
    _ = (∑ p ∈ Finset.range (k + 2), g p) + δ := hpartial (k + 2) (by omega)
    _ = _ := by rw [hbase]; dsimp [δ, θ]; ring

end SpinGlass.Targets
