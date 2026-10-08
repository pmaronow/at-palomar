module

public import Targets.Section5NegativeTerminal
public import Targets.Section5InterleavedCompact

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! Compact negative-overlap bands beyond the first breakpoint at physical level one. -/
theorem exists_uniform_constrainedPhi_negative_initial_beyond_compact
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2)
    {j : ℕ} (hj0 : 2 ≤ j) (hj : j ≤ k + 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0)
    (hbelow : ∀ z ∈ S, s.q 1 < |z.2|)
    (htrial : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit s β h 1 j z.1 z.2 ℓ := by
    intro z hz
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
        s β h (r := 1) (j := j) le_rfl (by omega) hj hβ hm
        (Or.inl (by simpa only [s.q_zero, Nat.sub_self] using hq1)) (Or.inl hq) hmin z.2
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit]
      rw [htzero]
      have hqj : 0 ≤ s.q 1 := s.q_nonneg (by omega)
      have hsub : 0 < (s.q 1 - z.2) ^ 2 / 2 := by
        exact div_pos (sq_pos_of_pos (sub_pos.mpr
          (lt_of_lt_of_le (hu z hz) hqj))) (by norm_num)
      linarith
    · have htime : z.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      have hH := section5InterleavedScalarV_zero_lt_negative_of_q1_pos
        s β h hβ htime (r := 1) le_rfl hj0 hj
        (by simpa only [s.m_zero, zero_add] using hm) hq1 hq (hu z hz)
        (hbelow z hz) (htrial z hz)
      exact ⟨0, by
        simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
        exact sub_pos.mpr hH⟩
  exact exists_uniform_constrainedPhi_gap_on_compact_trial s β h
    (r := 1) (j := j) le_rfl (by omega) (by omega) hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    htrial hpos

end SpinGlass.Targets
