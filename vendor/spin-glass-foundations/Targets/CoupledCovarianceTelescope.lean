module

public import Targets.SecondInterpolationAlgebra

@[expose] public section

/-!
# Finite covariance algebra for the physical second interpolation

The heat generators and disorder trace use the same backward-indexed replica
law. Summing the heat generators produces a covariance telescope of exactly
the same form as the disorder trace. This file proves that finite algebra and
the trial-field kernel increments; it does not assume a pressure derivative.
-/

open scoped BigOperators

namespace SpinGlass.Targets

/-- The sum of all remaining field-kernel increments under split `i`.
The first index denotes the replica split; the second is the heat level. -/
noncomputable def replicaHeatTail (B : ℕ → ℕ → ℝ) (J i : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico i J, B i l

/-- Swap the triangular sum in the actual heat formula, reusing Mathlib's
finite interval summation theorem. Both the zero split and the diagonal seed
are retained. No positivity or nonzero increment is needed. -/
theorem replicaHeatSum_telescope (m D : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (J : ℕ) :
    (∑ l ∈ Finset.range J,
      ((D l - B 0 l + ∑ i ∈ Finset.range l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) =
      (∑ l ∈ Finset.range J, D l) - replicaHeatTail B J 0 +
        ∑ i ∈ Finset.range J, m i *
          (replicaHeatTail B J i - replicaHeatTail B J (i + 1)) := by
  have hswap := Finset.sum_Ico_Ico_comm' 0 J
    (fun i l => m i * (B i l - B (i + 1) l))
  simp only [Nat.Ico_zero_eq_range] at hswap
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← hswap]
  simp only [replicaHeatTail, Nat.Ico_zero_eq_range]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hiJ : i < J := Finset.mem_range.mp hi
  rw [← Finset.mul_sum, ← mul_add, Finset.sum_sub_distrib,
    Finset.sum_eq_sum_Ico_succ_bot hiJ (B i)]
  ring

/-- The `Fin` form matches the original-level sums in the checked heat and
pressure derivatives. -/
theorem replicaHeatSum_telescope_fin (m D : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (J : ℕ) :
    (∑ l : Fin J,
      ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) =
      (∑ l : Fin J, D l) - replicaHeatTail B J 0 +
        ∑ i : Fin J, m i *
          (replicaHeatTail B J i - replicaHeatTail B J (i + 1)) := by
  have hin (l : ℕ) : (∑ i : Fin l, m i * (B i l - B (i + 1) l)) =
      ∑ i ∈ Finset.range l, m i * (B i l - B (i + 1) l) :=
    Fin.sum_univ_eq_sum_range (fun i => m i * (B i l - B (i + 1) l)) l
  simp_rw [hin]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    D l - B 0 l + (∑ i ∈ Finset.range l, m i * (B i l - B (i + 1) l)) +
      m l * B l l) J,
    Fin.sum_univ_eq_sum_range D J,
    Fin.sum_univ_eq_sum_range (fun i =>
      m i * (replicaHeatTail B J i - replicaHeatTail B J (i + 1))) J]
  exact replicaHeatSum_telescope m D B J

/-- Variance coefficients can be incorporated into the field increments
before applying the common covariance telescope. -/
theorem replicaHeatSum_weighted_fin (m a D : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (J : ℕ) :
    (∑ l : Fin J, a l *
      ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) =
      (∑ l : Fin J, a l * D l) - replicaHeatTail (fun i l => a l * B i l) J 0 +
        ∑ i : Fin J, m i *
          (replicaHeatTail (fun i l => a l * B i l) J i -
            replicaHeatTail (fun i l => a l * B i l) J (i + 1)) := by
  rw [← replicaHeatSum_telescope_fin m (fun l => a l * D l) (fun i l => a l * B i l)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [mul_add, mul_sub, Finset.mul_sum, mul_left_comm]

/-- Adjacent-mass summation by parts, including both endpoint coefficients. -/
theorem replicaCovariance_mass_telescope (m A : ℕ → ℝ) (D : ℝ) (κ : ℕ) :
    D - A 0 + (∑ i ∈ Finset.range (κ + 1), m i * (A i - A (i + 1))) =
      D + (m 0 - 1) * A 0 - m κ * A (κ + 1) +
        ∑ i ∈ Finset.range κ, (m (i + 1) - m i) * A (i + 1) := by
  have h := Finset.sum_range_by_parts m (fun i => A (i + 1) - A i) (κ + 1)
  simp only [Finset.sum_range_sub, Nat.add_sub_cancel, smul_eq_mul] at h
  have hg := Finset.sum_range_sub m κ
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  have he : (∑ i ∈ Finset.range (κ + 1), m i * (A i - A (i + 1))) =
      -∑ i ∈ Finset.range (κ + 1), m i * (A (i + 1) - A i) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he]
  rw [Finset.sum_sub_distrib] at hg
  rw [hg] at h
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith only [h]

/-- Subtracting the total heat telescope from the SK telescope combines
the two kernels under the same split law. -/
theorem replicaTrace_sub_heatSum (m A D : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (S : ℝ) (κ : ℕ) (hm0 : m 0 = 1) (hmκ : m κ = 0) :
    (S - A 0 + ∑ i ∈ Finset.range (κ + 1), m i * (A i - A (i + 1))) -
      (∑ l ∈ Finset.range (κ + 1),
        ((D l - B 0 l + ∑ i ∈ Finset.range l, m i * (B i l - B (i + 1) l)) +
          m l * B l l)) =
      S - (∑ l ∈ Finset.range (κ + 1), D l) +
        ∑ i ∈ Finset.range κ, (m (i + 1) - m i) *
          (A (i + 1) - replicaHeatTail B (κ + 1) (i + 1)) := by
  rw [replicaHeatSum_telescope]
  have hlin :
      (S - A 0 + ∑ i ∈ Finset.range (κ + 1), m i * (A i - A (i + 1))) -
        ((∑ l ∈ Finset.range (κ + 1), D l) - replicaHeatTail B (κ + 1) 0 +
          ∑ i ∈ Finset.range (κ + 1), m i *
            (replicaHeatTail B (κ + 1) i - replicaHeatTail B (κ + 1) (i + 1))) =
      (S - ∑ l ∈ Finset.range (κ + 1), D l) -
        (A 0 - replicaHeatTail B (κ + 1) 0) +
        ∑ i ∈ Finset.range (κ + 1), m i *
          ((A i - replicaHeatTail B (κ + 1) i) -
            (A (i + 1) - replicaHeatTail B (κ + 1) (i + 1))) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hlin]
  simpa only [hm0, hmκ, sub_self, zero_mul, add_zero, sub_zero] using
    replicaCovariance_mass_telescope m (fun i => A i - replicaHeatTail B (κ + 1) i)
      (S - ∑ l ∈ Finset.range (κ + 1), D l) κ

/-- Coefficient-weighted `Fin` version for the actual pressure formulas. -/
theorem replicaTrace_sub_weighted_heat_fin (m A a D : ℕ → ℝ) (B : ℕ → ℕ → ℝ)
    (S : ℝ) (κ : ℕ) (hm0 : m 0 = 1) (hmκ : m κ = 0) :
    (S - A 0 + ∑ i : Fin (κ + 1), m i * (A i - A (i + 1))) -
      (∑ l : Fin (κ + 1), a l *
        ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
          m l * B l l)) =
      S - (∑ l : Fin (κ + 1), a l * D l) +
        ∑ i : Fin κ, (m (i + 1) - m i) *
          (A (i + 1) - replicaHeatTail (fun i l => a l * B i l) (κ + 1) (i + 1)) := by
  have hc (X : ℕ → ℝ) (T : ℝ) :
      T - X 0 + (∑ i : Fin (κ + 1), m i * (X i - X (i + 1))) =
        T + ∑ i : Fin κ, (m (i + 1) - m i) * X (i + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => m i * (X i - X (i + 1))) (κ + 1),
      Fin.sum_univ_eq_sum_range (fun i => (m (i + 1) - m i) * X (i + 1)) κ,
      replicaCovariance_mass_telescope]
    simp only [hm0, hmκ, sub_self, zero_mul, add_zero, sub_zero]
  rw [replicaHeatSum_weighted_fin, hc, hc]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Every physical independent/shared field increment is the difference of
the trial covariance at the two adjacent forward overlap levels. -/
theorem pairFieldCovariance_split_increment {n : ℕ} (β : ℝ) (ρ : ℕ → ℝ)
    (τ p : ℕ) (a b : Config n × Config n) :
    pairFieldCovariance β (ρ (p + 1)) (ρ (min (p + 1) τ)) a b -
      pairFieldCovariance β (ρ p) (ρ (min p τ)) a b =
      β ^ 2 * (ρ (p + 1) - ρ p) *
        (if p < τ then
          AT.pairOverlapMatrix a b 0 0 + AT.pairOverlapMatrix a b 1 1 +
            (AT.pairOverlapMatrix a b 0 1 + AT.pairOverlapMatrix a b 1 0)
        else AT.pairOverlapMatrix a b 0 0 + AT.pairOverlapMatrix a b 1 1) := by
  by_cases hp : p < τ
  · simp [if_pos hp, min_eq_left (by omega : p + 1 ≤ τ),
      min_eq_left (by omega : p ≤ τ), pairFieldCovariance, pairTrialMatrix,
      Fin.sum_univ_two]
    ring
  · simp [if_neg hp, min_eq_right (by omega : τ ≤ p + 1),
      min_eq_right (by omega : τ ≤ p), pairFieldCovariance, pairTrialMatrix,
      Fin.sum_univ_two]
    ring

/-- Reversing the finite cascade order changes a suffix of increments into
a forward prefix. This remains valid for repeated overlap levels. -/
theorem replicaHeatTail_reverse_increments (C : ℕ → ℕ → ℝ) (κ i : ℕ) :
    replicaHeatTail (fun a l => C a (κ - l + 1) - C a (κ - l)) (κ + 1) i =
      C i (κ + 1 - i) - C i 0 := by
  unfold replicaHeatTail
  rw [Finset.sum_Ico_reflect (fun p => C i (p + 1) - C i p) i (by omega),
    Nat.sub_self, Nat.Ico_zero_eq_range, Finset.sum_range_sub]

/-- Kernel form matching the independent/shared overlap contractions of the
actual level heat generators. -/
theorem pairFieldCovariance_split_increment_kernel {n : ℕ} (β : ℝ) (ρ : ℕ → ℝ)
    (τ p : ℕ) (a b : Config n × Config n) :
    pairFieldCovariance β (ρ (p + 1)) (ρ (min (p + 1) τ)) a b -
      pairFieldCovariance β (ρ p) (ρ (min p τ)) a b =
      β ^ 2 * (ρ (p + 1) - ρ p) *
        pairFieldCovariance 1 1 (if p < τ then 1 else 0) a b := by
  rw [pairFieldCovariance_split_increment]
  by_cases hp : p < τ
  · simp only [if_pos hp]
    norm_num [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
    ring_nf
    simp
  · simp only [if_neg hp]
    norm_num [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]

/-- Under any fixed split law, the remaining physical field increments sum
to the trial covariance at precisely that split's forward overlap level.
No normalization, positivity, or vanishing-increment division is used. -/
theorem replicaHeatTail_pairFieldCovariance {n : ℕ} {u : ℝ}
    (β : ℝ) (ρ : ℕ → ℝ) (hρ : ρ 0 = 0) (τ κ i : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    replicaHeatTail (fun a l => β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
      ∑ p, ∑ q, μ a p q * pairFieldCovariance 1 1
        (if κ - l < τ then 1 else 0) p.1 q.1) (κ + 1) i =
      ∑ p, ∑ q, μ i p q *
        pairFieldCovariance β (ρ (κ + 1 - i)) (ρ (min (κ + 1 - i) τ)) p.1 q.1 := by
  let C := fun a j => ∑ p, ∑ q, μ a p q *
    pairFieldCovariance β (ρ j) (ρ (min j τ)) p.1 q.1
  have he (a l : ℕ) : β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
      (∑ p, ∑ q, μ a p q * pairFieldCovariance 1 1
        (if κ - l < τ then 1 else 0) p.1 q.1) = C a (κ - l + 1) - C a (κ - l) := by
    simp only [C, ← Finset.sum_sub_distrib, ← mul_sub,
      pairFieldCovariance_split_increment_kernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  rw [replicaHeatTail_reverse_increments]
  have hzero : C i 0 = 0 := by
    simp [C, hρ, pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
  rw [hzero, sub_zero]

/-- Exact sum of the independent/shared diagonal heat contractions.
The terminal trial matrix is `(1,u;u,1)`. -/
theorem sum_pairField_heat_diagonal (β u : ℝ) (ρ : ℕ → ℝ) (τ κ : ℕ)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = u) :
    (∑ l ∈ Finset.range (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
      (if κ - l < τ then 2 * (1 + u) else 2)) = 2 * β ^ 2 * (1 + u ^ 2) := by
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
  simp only [F, hρ0, hρ1, min_eq_right hτ, Nat.zero_min, hu]
  ring

/-- Reindex adjacent backward masses and splits to the paper's forward
replica convention. The paper's measure at `p+1` is the backward split `κ-p`. -/
theorem replicaMassGap_reverse (m A : ℕ → ℝ) (κ : ℕ) :
    (∑ i ∈ Finset.range κ, (m (κ - (i + 1)) - m (κ - i)) * A (i + 1)) =
      ∑ p ∈ Finset.range κ, (m p - m (p + 1)) * A (κ - p) := by
  have hrev := Finset.sum_range_reflect
    (fun p => (m p - m (p + 1)) * A (κ - p)) κ
  rw [← hrev]
  apply Finset.sum_congr rfl
  intro i hi
  have hiκ : i < κ := Finset.mem_range.mp hi
  congr 2 <;> congr 1 <;> omega

/-- The complete finite covariance sum with the physical SK and variance
coefficients. `μ i` is the actual law at backward split `i`; no equation about
the derivative, and no normalization or positivity of this law, is assumed.
The resulting forward law is exactly `μ (κ-p)` as in the paper. -/
theorem pairCovarianceExpression_eq_trace_sub_heat {n : ℕ}
    (β t u : ℝ) (m ρ : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
    let B := fun i l => ∑ p, ∑ q, μ i p q *
      pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
    t / 2 *
      ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
          m (κ - i) * (A i - A (i + 1))) -
        ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
          (((if κ - l < τ then 2 * (1 + u) else 2) - B 0 l +
              ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
            m (κ - l) * B l l)) =
      pairCovarianceExpression β t u m ρ (fun p => ρ (min p τ)) κ
        (fun p => μ (κ - p)) := by
  dsimp only
  let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
  let a := fun l => β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))
  let D := fun l => if κ - l < τ then 2 * (1 + u) else 2
  change t / 2 *
    ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
        m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), a l *
        ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
          m (κ - l) * B l l)) = _
  rw [replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A a D B
    (β ^ 2 * (1 + u ^ 2)) κ (by simpa using hmκ) (by simpa using hm0)]
  have hd : (∑ l : Fin (κ + 1), a l * D l) = 2 * β ^ 2 * (1 + u ^ 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun l => a l * D l) (κ + 1)]
    exact sum_pairField_heat_diagonal β u ρ τ κ hρ0 hρ1 hτ hu
  rw [hd]
  have hb (i : ℕ) : replicaHeatTail (fun i l => a l * B i l) (κ + 1) i =
      ∑ p, ∑ q, μ i p q *
        pairFieldCovariance β (ρ (κ + 1 - i)) (ρ (min (κ + 1 - i) τ)) p.1 q.1 :=
    replicaHeatTail_pairFieldCovariance β ρ hρ0 τ κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ + 1 - i)) (ρ (min (κ + 1 - i) τ)) p.1 q.1
  change t / 2 * (β ^ 2 * (1 + u ^ 2) - 2 * β ^ 2 * (1 + u ^ 2) +
    ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ,
    replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (pairSKCovariance β a.1 b.1 -
          pairFieldCovariance β (ρ (p + 1)) (ρ (min (p + 1) τ)) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [pairCovarianceExpression]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z) (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  ring

end SpinGlass.Targets
