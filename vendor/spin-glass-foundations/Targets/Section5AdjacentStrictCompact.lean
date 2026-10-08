module

public import Targets.Section5AdjacentStrict

@[expose] public section

/-!
# Compact adjacent bands away from the physical overlap

The scalar positivity needed by the adjacent-band compactness theorem is
assembled here from the two endpoint regimes already proved: at positive
time, `Section5AdjacentStrict` supplies the zero-lambda strict comparison; at
time zero, the minimizing-scheme lambda gain supplies a strictly positive
quadratic deficit whenever the band avoids the physical overlap.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_gap_on_adjacent_left_strict
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r j : ℕ} (hβ : β ≠ 0) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j + 1 ≤ k + 1) (hjr : j + 1 < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q j < s.q (j + 1))
    (hqr : s.q (r - 1) < s.q r) (hqnext : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu0 : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Ico (s.q (j - 1)) (s.q (j + 1)))
    (hneq : ∀ z ∈ S, z.2 ≠ s.q r) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hmass : s.m (r - 1) < s.m r := by
    have hfin : (⟨r - 1, by omega⟩ : Fin (k + 2)) < ⟨r, by omega⟩ := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact hm hfin
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z := by
    intro z hz
    by_cases htzero : z.1 = 0
    · by_cases hle : z.2 ≤ s.q j
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
          s β h (r := r) (j := j) (by omega) hr (by omega) hβ
          hmass
          (Or.inl hqr) (Or.inl hqnext) hmin z.2
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_pos hle, section5InterleavedLambdaDeficit, htzero]
        have hsq : 0 < (z.2 - s.q r) ^ 2 / 2 := by
          exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (hneq z hz))) (by norm_num)
        linarith [H]
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
          s β h (r := r) (j := j + 1) (by omega) hr (by omega) hβ
          hmass
          (Or.inl hqr) (Or.inl hqnext) hmin z.2
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_neg hle, section5InterleavedLambdaDeficit, htzero]
        have hsq : 0 < (z.2 - s.q r) ^ 2 / 2 := by
          exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (hneq z hz))) (by norm_num)
        linarith [H]
    · have htpos : z.1 ∈ Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      have H := section5InterleavedLambdaDeficit_adjacentGlue_pos_left
        s β h hβ htpos hr hj0 hj hjr hm hqj hqr
        (hu0 z hz) (hu z hz)
      exact ⟨0, by simpa only using H⟩
  apply exists_uniform_constrainedPhi_gap_on_adjacent_trial s β h
    (r := r) (j := j) (by omega) hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    hu0 (fun z hz => ⟨(hu z hz).1, (hu z hz).2.le⟩) hpos

theorem exists_uniform_constrainedPhi_gap_on_adjacent_right_strict
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r j : ℕ} (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 2 ≤ j) (hj : j + 1 ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q (j - 1) < s.q j)
    (hqprev : s.q (r - 1) < s.q r) (hqr : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu0 : ∀ z ∈ S, 0 ≤ z.2)
    (hu : ∀ z ∈ S, z.2 ∈ Ioc (s.q (j - 1)) (s.q (j + 1)))
    (hneq : ∀ z ∈ S, z.2 ≠ s.q r) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  have hmass : s.m (r - 1) < s.m r := by
    have hfin : (⟨r - 1, by omega⟩ : Fin (k + 2)) < ⟨r, by omega⟩ := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact hm hfin
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit_adjacentGlue (j := j) s β h r ℓ z := by
    intro z hz
    by_cases htzero : z.1 = 0
    · by_cases hle : z.2 ≤ s.q j
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
          s β h (r := r) (j := j) hr0 hr (by omega) hβ
          hmass
          (Or.inl hqprev) (Or.inl hqr) hmin z.2
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_pos hle, section5InterleavedLambdaDeficit, htzero]
        have hsq : 0 < (z.2 - s.q r) ^ 2 / 2 := by
          exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (hneq z hz))) (by norm_num)
        linarith [H]
      · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
          s β h (r := r) (j := j + 1) hr0 hr (by omega) hβ
          hmass
          (Or.inl hqprev) (Or.inl hqr) hmin z.2
        refine ⟨ℓ, ?_⟩
        dsimp only [section5InterleavedLambdaDeficit_adjacentGlue]
        rw [if_neg hle, section5InterleavedLambdaDeficit, htzero]
        have hsq : 0 < (z.2 - s.q r) ^ 2 / 2 := by
          exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (hneq z hz))) (by norm_num)
        linarith [H]
    · have htpos : z.1 ∈ Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      have H := section5InterleavedLambdaDeficit_adjacentGlue_pos_right
        s β h hβ htpos hj0 hj hrj hm hqj hqr
        (hu0 z hz) (hu z hz)
      exact ⟨0, by simpa only using H⟩
  apply exists_uniform_constrainedPhi_gap_on_adjacent_trial s β h
    (r := r) (j := j) hr0 hr (by omega) hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩)
    hu0 (fun z hz => ⟨(hu z hz).1.le, (hu z hz).2⟩) hpos

end SpinGlass.Targets
