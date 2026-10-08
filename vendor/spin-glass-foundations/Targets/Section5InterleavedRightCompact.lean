module

public import Targets.Section5InterleavedCompact
public import Targets.Section5StableSortFilter

@[expose] public section

/-!
# Compact right outside-trial bounds

This is the right-hand counterpart of the checked compact left outside-trial
adapter. The half-open lower endpoint supplies the positive interpolating
variance; the upper endpoint may be included. The adjacent breakpoint itself
is handled separately by the stable-tag gluing step.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

theorem exists_uniform_constrainedPhi_right_outside_trial
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j)
    (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q r < s.q (r + 1))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Ioc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hu0 : ∀ z ∈ S, 0 ≤ z.2 := fun z hz =>
    (s.q_nonneg (p := j - 1) (by omega)).trans (hu z hz).1.le
  have htrial : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j) := by
    intro z hz
    rw [abs_of_nonneg (hu0 z hz)]
    exact ⟨(hu z hz).1.le, (hu z hz).2⟩
  apply exists_uniform_constrainedPhi_gap_on_compact_trial s β h hr0 hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial
  intro z hz
  by_cases htzero : z.1 = 0
  · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
      s β h hr0 hr hj z.2
    rw [hQ] at H
    have hltq : s.q r < s.q (j - 1) :=
      lt_of_lt_of_le hq (s.q_mono' (j - 1) (by omega) (r + 1) (by omega))
    have hlt : s.q r < z.2 := hltq.trans_le (hu z hz).1.le
    have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
      div_pos (sq_pos_of_neg (sub_neg.mpr hlt)) (by norm_num)
    refine ⟨ℓ, ?_⟩
    dsimp only [section5InterleavedLambdaDeficit]
    rw [htzero]
    linarith
  · have htp : 0 < z.1 := lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero)
    have htime : z.1 < 1 := (ht z hz).2.trans_lt ht₀
    have H := section5InterleavedScalarV_zero_lt_right_outside s β h
      ⟨htp.le, htime.le⟩ hj hrj (htrial z hz) hm
      (by
        exact mul_pos (sub_pos.mpr htime)
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq)))
      (by
        rw [abs_of_nonneg (hu0 z hz)]
        exact mul_pos htp (mul_pos (sq_pos_of_ne_zero hβ)
          (sub_pos.mpr (hu z hz).1)))
    refine ⟨0, ?_⟩
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    exact sub_pos.mpr H

end SpinGlass.Targets
