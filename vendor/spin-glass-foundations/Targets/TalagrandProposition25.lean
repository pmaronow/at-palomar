module

/-
# Talagrand's Proposition 2.5

An expected constrained-pressure deficit makes the corresponding replica
overlap event exponentially unlikely. This is the interior-time statement
needed by the existing concentration-to-convergence theorem; no optimality
assumption or two-replica a priori bound is used here.
-/
public import Targets.CoupledOuterExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}

/-- Proposition 2.5 with the two explicit exponential rates supplied by Lemma 2.6. -/
theorem talagrand_proposition_2_5_explicit (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : constrainedPhi n s β h sk.U d t u ≤ 2 * guerraPhi n s β h sk.U t - ε) :
    guerraReplicaMeasure n s β h sk.U t d (overlapEvent n u) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) +
        Real.exp (-(ε ^ 2 / (128 * (1 + |β|) ^ 2)) * n) := by
  rw [← gaussianCoupledEvent_mean_eq sk s hs ht u hu d hd]
  apply gaussianCoupledEvent_small sk s hn hs ⟨ht.1.le, ht.2.le⟩ u hu d hε
  rw [gaussianCoupledGap_mean_eq sk s hn ⟨ht.1.le, ht.2.le⟩ u hu d hd]
  nlinarith [mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- A strictly positive rate depending only on the scheme, `β`, and the deficit. -/
noncomputable def talagrandEventRate (s : RSBScheme k) (β ε : ℝ) : ℝ :=
  min (s.m 1 * ε / 4) (ε ^ 2 / (128 * (1 + |β|) ^ 2))

theorem talagrandEventRate_pos (s : RSBScheme k) (β : ℝ) (hs : 0 < s.m 1)
    {ε : ℝ} (hε : 0 < ε) : 0 < talagrandEventRate s β ε := by
  unfold talagrandEventRate
  apply lt_min <;> positivity

/-- An explicit `K` for (2.31), independent of `N`, `t`, the overlap and split. -/
noncomputable def talagrandEventConstant (s : RSBScheme k) (β ε : ℝ) : ℝ :=
  2 + 1 / talagrandEventRate s β ε

theorem talagrandEventConstant_pos (s : RSBScheme k) (β : ℝ) (hs : 0 < s.m 1)
    {ε : ℝ} (hε : 0 < ε) : 0 < talagrandEventConstant s β ε := by
  have hr := talagrandEventRate_pos s β hs hε
  unfold talagrandEventConstant
  positivity

theorem talagrandEventConstant_bound (s : RSBScheme k) (β : ℝ) (hs : 0 < s.m 1)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Real.exp (-(s.m 1 * ε / 4) * n) +
      Real.exp (-(ε ^ 2 / (128 * (1 + |β|) ^ 2)) * n) ≤
      talagrandEventConstant s β ε * Real.exp (-(n : ℝ) / talagrandEventConstant s β ε) := by
  let r := talagrandEventRate s β ε
  let K := talagrandEventConstant s β ε
  have hr : 0 < r := talagrandEventRate_pos s β hs hε
  have hK : 0 < K := talagrandEventConstant_pos s β hs hε
  have hK2 : 2 ≤ K := by
    change 2 ≤ 2 + 1 / r
    exact le_add_of_nonneg_right (one_div_nonneg.mpr hr.le)
  have hNr : -(n : ℝ) * r ≤ -(n : ℝ) / K := by
    apply (le_div_iff₀ hK).mpr
    have hrK : 1 ≤ r * K := by
      dsimp [K, talagrandEventConstant]
      change 1 ≤ r * (2 + 1 / r)
      rw [mul_add, mul_one_div_cancel hr.ne']
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hrK (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hfirst : Real.exp (-(s.m 1 * ε / 4) * n) ≤ Real.exp (-(n : ℝ) / K) := by
    apply Real.exp_le_exp.mpr
    apply le_trans _ hNr
    have H := mul_le_mul_of_nonneg_right (min_le_left (s.m 1 * ε / 4)
      (ε ^ 2 / (128 * (1 + |β|) ^ 2))) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    change r * n ≤ _ at H
    nlinarith
  have hsecond : Real.exp (-(ε ^ 2 / (128 * (1 + |β|) ^ 2)) * n) ≤
      Real.exp (-(n : ℝ) / K) := by
    apply Real.exp_le_exp.mpr
    apply le_trans _ hNr
    have H := mul_le_mul_of_nonneg_right (min_le_right (s.m 1 * ε / 4)
      (ε ^ 2 / (128 * (1 + |β|) ^ 2))) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    change r * n ≤ _ at H
    nlinarith
  change _ ≤ K * Real.exp (-(n : ℝ) / K)
  nlinarith [Real.exp_pos (-(n : ℝ) / K),
    mul_le_mul_of_nonneg_right hK2 (Real.exp_pos (-(n : ℝ) / K)).le]

/-- **Lemma 2.6**, now in the original abstract disorder and outer-average formulation.
All means are integrable, and the constant is independent of the system size and time. -/
theorem talagrand_lemma_2_6 (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : (∫ ω, coupledCascade n s β d (constrainedBase n (sk.U ω) h t u) (k + 2) 0 0 ∂ℙ) ≤
      (∫ ω, coupledCascade n s β d (coupledBase n (sk.U ω) h t) (k + 2) 0 0 ∂ℙ) - ε * n) :
    (∫ ω, coupledObservable n s β (sk.U ω) h t d (overlapEvent n u) (k + 2) 0 0 ∂ℙ) ≤
      talagrandEventConstant s β ε * Real.exp (-(n : ℝ) / talagrandEventConstant s β ε) := by
  rw [← integral_gaussianCoupledEvent_eq sk s hs ht u hu d hd]
  apply le_trans (gaussianCoupledEvent_small sk s hn hs ht u hu d hε ?_)
    (talagrandEventConstant_bound s β hs hε n)
  rw [integral_gaussianCoupledGap_eq sk s hn ht u hu d hd]
  unfold coupledGap
  rw [integral_sub (integrable_constrainedCascade_top sk s hn ht u hu d hd)
    (integrable_coupledCascade_top sk s ht d)]
  linarith

/-- **Proposition 2.5, (2.30)--(2.31)** for the exact-covariance SK model on `0<t<1`.
This time domain is sufficient for the existing endpoint-safe Theorem 2.2 deduction.
The constant is explicitly independent of the system size and interpolation time. -/
theorem talagrand_proposition_2_5 (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : constrainedPhi n s β h sk.U d t u ≤ 2 * guerraPhi n s β h sk.U t - ε) :
    guerraReplicaMeasure n s β h sk.U t d (overlapEvent n u) ≤
      talagrandEventConstant s β ε * Real.exp (-(n : ℝ) / talagrandEventConstant s β ε) :=
  (talagrand_proposition_2_5_explicit sk s hn hs ht u hu d hd hε hgap).trans
    (talagrandEventConstant_bound s β hs hε n)

end SpinGlass.Targets
