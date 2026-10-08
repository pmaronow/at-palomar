module

public import Targets.Section5AdjacentCompact
public import Targets.Section5AdjacentStrict

@[expose] public section

/-!
# Stationary compact gaps across left outside breakpoints

This is the endpoint-stationary version of the positive left adjacent-band
estimate.  Supplying the exact physical stationarity identity avoids an
unnecessary strict right-overlap hypothesis at the terminal physical level.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_gap_on_adjacent_left_stationary
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r j : ℕ} (hβ : β ≠ 0) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j + 1 ≤ k + 1) (hjr : j + 1 < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q j < s.q (j + 1))
    (hqr : s.q (r - 1) < s.q r)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu0 : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Ico (s.q (j - 1)) (s.q (j + 1))) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue
        (j := j) s β h r ℓ z := by
    intro z hz
    by_cases htzero : z.1 = 0
    · by_cases hle : z.2 ≤ s.q j
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
          s β h (r := r) (j := j) (by omega) hr (by omega) z.2
        rw [hQ] at H
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_pos hle, section5InterleavedLambdaDeficit, htzero]
        have hlt : z.2 < s.q r :=
          (hu z hz).2.trans_le (s.q_mono' r (by omega) (j + 1) hjr.le)
        have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
          div_pos (sq_pos_of_pos (sub_pos.mpr hlt)) (by norm_num)
        linarith
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
          s β h (r := r) (j := j + 1) (by omega) hr (by omega) z.2
        rw [hQ] at H
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_neg hle, section5InterleavedLambdaDeficit, htzero]
        have hlt : z.2 < s.q r :=
          (hu z hz).2.trans_le (s.q_mono' r (by omega) (j + 1) hjr.le)
        have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
          div_pos (sq_pos_of_pos (sub_pos.mpr hlt)) (by norm_num)
        linarith
    · have htpos : z.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      exact ⟨0, section5InterleavedLambdaDeficit_adjacentGlue_pos_left
        s β h hβ htpos hr hj0 hj hjr hm hqj hqr
          (hu0 z hz) (hu z hz)⟩
  apply exists_uniform_constrainedPhi_gap_on_adjacent_trial s β h
    (r := r) (j := j) (by omega) hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    hu0 (fun z hz => ⟨(hu z hz).1, (hu z hz).2.le⟩) hpos

/-- The right-side counterpart.  Exact stationarity replaces the strict
left-overlap direction, which is essential at the allowed boundary
`r = 1`, `q 1 = 0`. -/
theorem exists_uniform_constrainedPhi_gap_on_adjacent_right_stationary
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r j : ℕ} (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 2 ≤ j) (hj : j + 1 ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q (j - 1) < s.q j)
    (hqr : s.q r < s.q (r + 1))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu0 : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Ioc (s.q (j - 1)) (s.q (j + 1))) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue
        (j := j) s β h r ℓ z := by
    intro z hz
    by_cases htzero : z.1 = 0
    · by_cases hle : z.2 ≤ s.q j
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
          s β h (r := r) (j := j) hr0 hr (by omega) z.2
        rw [hQ] at H
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_pos hle, section5InterleavedLambdaDeficit, htzero]
        have hlt : s.q r < z.2 := lt_of_lt_of_le hqr
          ((s.q_mono' (j - 1) (by omega) (r + 1) (by omega)).trans_lt
            (hu z hz).1).le
        have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
          div_pos (sq_pos_of_neg (sub_neg.mpr hlt)) (by norm_num)
        linarith
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
          s β h (r := r) (j := j + 1) hr0 hr (by omega) z.2
        rw [hQ] at H
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_neg hle, section5InterleavedLambdaDeficit, htzero]
        have hlt : s.q r < z.2 := lt_of_lt_of_le hqr
          ((s.q_mono' (j - 1) (by omega) (r + 1) (by omega)).trans_lt
            (hu z hz).1).le
        have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
          div_pos (sq_pos_of_neg (sub_neg.mpr hlt)) (by norm_num)
        linarith
    · have htpos : z.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      exact ⟨0, section5InterleavedLambdaDeficit_adjacentGlue_pos_right
        s β h hβ htpos hj0 hj hrj hm hqj hqr
          (hu0 z hz) (hu z hz)⟩
  apply exists_uniform_constrainedPhi_gap_on_adjacent_trial s β h
    (r := r) (j := j) hr0 hr (by omega) hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    hu0 (fun z hz => ⟨(hu z hz).1.le, (hu z hz).2⟩) hpos

end SpinGlass.Targets
