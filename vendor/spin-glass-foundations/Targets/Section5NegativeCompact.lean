module

public import Targets.Section5InterleavedCompact

@[expose] public section

/-!
# Compact negative-overlap trial bounds

Every negative overlap is outside the positive physical neighborhood.  This
adapter supplies the compactness step for such a trial interval: at positive
time it uses the checked signed scalar strictness, while at time zero it uses
the checked nonzero-lambda quadratic gain and the stationary endpoint value.
The finite-size constrained free energy is never treated as a continuous
function of the overlap.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_negative_trial
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0)
    (htrial : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ := by
    intro z hz
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
        s β h (by omega) hr hj z.2
      rw [hQ] at H
      have hqr : 0 ≤ s.q r := s.q_nonneg (by omega)
      have hdiff : 0 < (s.q r - z.2) ^ 2 / 2 := by
        have hsub : 0 < s.q r - z.2 := sub_pos.mpr (lt_of_lt_of_le (hu z hz) hqr)
        exact div_pos (sq_pos_of_pos hsub) (by norm_num)
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit]
      rw [htzero]
      linarith
    · have htp : 0 < z.1 := lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero)
      have htime : z.1 < 1 := (ht z hz).2.trans_lt ht₀
      have H := section5InterleavedScalarV_zero_lt_negative s β h hβ
        ⟨htp, htime⟩ hr0 hj0 hj hm hq (hu z hz) (htrial z hz)
      exact ⟨0, by
        simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
        exact sub_pos.mpr H⟩
  exact exists_uniform_constrainedPhi_gap_on_compact_trial s β h (by omega) hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial hpos

end SpinGlass.Targets
