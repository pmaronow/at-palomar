module

public import Targets.Section5RightBoundary
public import Targets.Section5LeftUniform
public import Targets.Section5ZeroInitialNegative

@[expose] public section

/-!
# Uniform local neighborhood for a reduced scheme

The local estimates on the two sides of a physical overlap are combined into
one neighborhood.  This is the local part needed by the final compact-cover
argument; the outside compact regions are deliberately left to separate
modules.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The concrete radius used by the reduced local estimate.  The degenerate
left endpoint `q₁ = 0` and right endpoint `qᵣ = 1` omit the corresponding
zero-length neighboring interval. -/
noncomputable def section5LocalReducedRadius {k : ℕ} (s : RSBScheme k)
    (β t₀ : ℝ) (r : ℕ) : ℝ :=
  if s.q r = 1 then
    min ((1 - t₀) / section5LocalLeftConstant β 535)
      (s.q r - s.q (r - 1))
  else if r = 1 ∧ s.q 1 = 0 then
    min ((1 - t₀) / section5LocalLeftConstant β 535) (s.q 2)
  else
    min ((1 - t₀) / section5LocalLeftConstant β 535)
      (min (s.q r - s.q (r - 1)) (s.q (r + 1) - s.q r))

theorem exists_uniform_local_quadratic_reduced_min
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ η > (0 : ℝ), η = section5LocalReducedRadius s β t₀ r ∧
      ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ u ∈ Icc (-1) 1,
      |u - s.q r| ≤ η →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - (1 - t₀) ^ 2 /
          section5LocalLeftConstant β 535 *
          (u - s.q r) ^ 2 := by
  have hL : 0 < section5LocalLeftConstant β 535 :=
    section5LocalLeftConstant_pos β 535 (by norm_num)
  have hqdir := s.overlap_directions_of_strict hqstrict hr0 hr
  by_cases hqr : s.q r = 1
  · let η : ℝ := min ((1 - t₀) / section5LocalLeftConstant β 535)
        (s.q r - s.q (r - 1))
    have hleft : s.q (r - 1) < s.q r := hqdir.1.resolve_right (by
      intro hz
      linarith [hqr])
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (div_pos (sub_pos.mpr ht₀) hL) (sub_pos.mpr hleft)
    refine ⟨η, hη, ?_, ?_⟩
    · simp [section5LocalReducedRadius, hqr, η]
    intro n hn sk t ht u hu hdist hatt
    have huq : u ≤ s.q r := by
      rw [hqr]
      exact hu.2
    have huL : u ∈ Icc (s.q (r - 1)) (s.q r) := by
      constructor
      · have habs := abs_le.mp hdist
        have hηgap : η ≤ s.q r - s.q (r - 1) := min_le_right _ _
        linarith
      · exact huq
    have hlocal : section5LocalLeftConstant β 535 * (s.q r - u) ≤ 1 - t₀ := by
      have hηL : η ≤ (1 - t₀) / section5LocalLeftConstant β 535 := min_le_left _ _
      have hnon : 0 ≤ s.q r - u := sub_nonneg.mpr huq
      have habs : |u - s.q r| = s.q r - u := by
        rw [abs_of_nonpos (sub_nonpos.mpr huq)]
        ring
      rw [← habs]
      have := mul_le_mul_of_nonneg_left (show |u - s.q r| ≤ η from hdist) hL.le
      have hmul : section5LocalLeftConstant β 535 * η ≤ 1 - t₀ := by
        calc
          section5LocalLeftConstant β 535 * η ≤
              section5LocalLeftConstant β 535 *
                ((1 - t₀) / section5LocalLeftConstant β 535) :=
            mul_le_mul_of_nonneg_left hηL hL.le
          _ = 1 - t₀ := mul_div_cancel₀ _ hL.ne'
      linarith
    letI : Nonempty (AT.ConstrainedPair n u) := by
      obtain ⟨σ, τ, hστ⟩ := hatt
      exact ⟨⟨(σ, τ), hστ⟩⟩
    have H := constrainedPhi_local_left_uniform hn s β h ε sk hr0 hr hβ
      (by simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega))
      (Or.inr hqr) ⟨ht.1.le, ht.2.le⟩ ht₀ huL hmin hnear hsmall hlocal
    exact H
  · by_cases hz : r = 1 ∧ s.q 1 = 0
    · rcases hz with ⟨rfl, hq1⟩
      have hq2 : 0 < s.q 2 := by
        rcases hqdir.2 with H | H
        · rw [hq1] at H
          simpa [hq1] using H
        · linarith
      let η : ℝ := min ((1 - t₀) / section5LocalLeftConstant β 535) (s.q 2)
      have hη : 0 < η := by
        dsimp [η]
        exact lt_min (div_pos (sub_pos.mpr ht₀) hL) hq2
      refine ⟨η, hη, ?_, ?_⟩
      · simp [section5LocalReducedRadius, hqr, hq1, η]
      intro n hn sk t ht u hu hdist hatt
      letI : Nonempty (AT.ConstrainedPair n u) := by
        obtain ⟨σ, τ, hστ⟩ := hatt
        exact ⟨⟨(σ, τ), hστ⟩⟩
      by_cases hup : 0 ≤ u
      · have hu2 : u ∈ Icc 0 (s.q 2) := by
          constructor
          · exact hup
          · have habs := abs_le.mp hdist
            have hηq : η ≤ s.q 2 := min_le_right _ _
            linarith
        have hlocal : section5LocalLeftConstant β 535 * u ≤ 1 - t₀ := by
          have hηL : η ≤ (1 - t₀) / section5LocalLeftConstant β 535 := min_le_left _ _
          have huη : u ≤ η := by
            have habs := abs_le.mp hdist
            linarith [habs.1]
          have hmul : section5LocalLeftConstant β 535 * η ≤ 1 - t₀ := by
            calc
              section5LocalLeftConstant β 535 * η ≤
                  section5LocalLeftConstant β 535 *
                    ((1 - t₀) / section5LocalLeftConstant β 535) :=
                mul_le_mul_of_nonneg_left hηL hL.le
              _ = 1 - t₀ := mul_div_cancel₀ _ hL.ne'
          nlinarith
        have H := constrainedPhi_local_right_initial_zero hn s β h sk hβ hq1
          (by simpa using hmass 0 (by omega)) ⟨ht.1.le, ht.2.le⟩ ht₀ hu2 hmin hlocal
        simpa only [show k + 2 - 1 = k + 1 by omega, hq1, sub_zero] using H
      · have huneg : u < 0 := lt_of_not_ge hup
        have hu2 : u ∈ Icc (-(s.q 2)) 0 := by
          constructor
          · have habs := abs_le.mp hdist
            have hηq : η ≤ s.q 2 := min_le_right _ _
            linarith
          · exact huneg.le
        have hlocal : section5LocalLeftConstant β 535 * (-u) ≤ 1 - t₀ := by
          have hηL : η ≤ (1 - t₀) / section5LocalLeftConstant β 535 := min_le_left _ _
          have huη : -u ≤ η := by
            have habs := abs_le.mp hdist
            linarith [habs.2]
          have hmul : section5LocalLeftConstant β 535 * η ≤ 1 - t₀ := by
            calc
              section5LocalLeftConstant β 535 * η ≤
                  section5LocalLeftConstant β 535 *
                    ((1 - t₀) / section5LocalLeftConstant β 535) :=
                mul_le_mul_of_nonneg_left hηL hL.le
              _ = 1 - t₀ := mul_div_cancel₀ _ hL.ne'
          nlinarith
        have H := constrainedPhi_local_negative_initial_zero hn s β h sk hβ hq1
          (by simpa using hmass 0 (by omega)) hq2 ⟨ht.1.le, ht.2.le⟩ ht₀ hu2 hmin hlocal
        simpa only [show k + 2 - 1 = k + 1 by omega, hq1, sub_zero] using H
    · have hleft : s.q (r - 1) < s.q r := by
        apply hqdir.1.resolve_right
        intro hz0
        by_cases hr1 : r = 1
        · apply hz
          exact ⟨hr1, by simpa [hr1] using hz0⟩
        · have H := hqstrict (r - 1) (by omega) (by omega)
          have heq : r - 1 + 1 = r := Nat.sub_add_cancel hr0
          rw [heq, hz0] at H
          linarith [s.q_nonneg (p := r - 1) (by omega)]
      have hqzero : s.q r ≠ 0 := by
        intro hz
        exact (not_lt_of_ge (s.q_nonneg (p := r - 1) (by omega))) (hz ▸ hleft)
      have hqpos : 0 < s.q r := lt_of_le_of_ne
        (s.q_nonneg (p := r) (by omega)) (Ne.symm hqzero)
      have hqright : s.q r < s.q (r + 1) := hqdir.2.resolve_right hqr
      let η : ℝ := min ((1 - t₀) / section5LocalLeftConstant β 535)
        (min (s.q r - s.q (r - 1)) (s.q (r + 1) - s.q r))
      have hη : 0 < η := by
        dsimp [η]
        exact lt_min (div_pos (sub_pos.mpr ht₀) hL)
          (lt_min (sub_pos.mpr hleft) (sub_pos.mpr hqright))
      refine ⟨η, hη, ?_, ?_⟩
      · simp [section5LocalReducedRadius, hqr, hz, η]
      intro n hn sk t ht u hu hdist hatt
      letI : Nonempty (AT.ConstrainedPair n u) := by
        obtain ⟨σ, τ, hστ⟩ := hatt
        exact ⟨⟨(σ, τ), hστ⟩⟩
      by_cases huq : u ≤ s.q r
      · have huI : u ∈ Icc (s.q (r - 1)) (s.q r) := by
          constructor
          · have habs := abs_le.mp hdist
            have hηgap : η ≤ s.q r - s.q (r - 1) :=
              (min_le_right _ _).trans (min_le_left _ _)
            linarith
          · exact huq
        have hlocal : section5LocalLeftConstant β 535 * (s.q r - u) ≤ 1 - t₀ := by
          have hηL : η ≤ (1 - t₀) / section5LocalLeftConstant β 535 := min_le_left _ _
          have habs := abs_le.mp hdist
          have hmul : section5LocalLeftConstant β 535 * η ≤ 1 - t₀ := by
            calc
              section5LocalLeftConstant β 535 * η ≤
                  section5LocalLeftConstant β 535 *
                    ((1 - t₀) / section5LocalLeftConstant β 535) :=
                mul_le_mul_of_nonneg_left hηL hL.le
              _ = 1 - t₀ := mul_div_cancel₀ _ hL.ne'
          nlinarith
        have H := constrainedPhi_local_left_uniform hn s β h ε sk hr0 hr hβ
          (by simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega))
          (Or.inl hqright) ⟨ht.1.le, ht.2.le⟩ ht₀ huI hmin hnear hsmall hlocal
        exact H
      · have huI : u ∈ Icc (s.q r) (s.q (r + 1)) := by
          constructor
          · exact le_of_not_ge huq
          · have habs := abs_le.mp hdist
            have hηgap : η ≤ s.q (r + 1) - s.q r :=
              (min_le_right _ _).trans (min_le_right _ _)
            linarith
        have hlocal : section5LocalLeftConstant β 535 * (u - s.q r) ≤ 1 - t₀ := by
          have hηL : η ≤ (1 - t₀) / section5LocalLeftConstant β 535 := min_le_left _ _
          have habs := abs_le.mp hdist
          have hmul : section5LocalLeftConstant β 535 * η ≤ 1 - t₀ := by
            calc
              section5LocalLeftConstant β 535 * η ≤
                  section5LocalLeftConstant β 535 *
                    ((1 - t₀) / section5LocalLeftConstant β 535) :=
                mul_le_mul_of_nonneg_left hηL hL.le
              _ = 1 - t₀ := mul_div_cancel₀ _ hL.ne'
          nlinarith
        have H := constrainedPhi_local_right_of_reduced_min hn s β h ε sk hβ hmass
          hqstrict hr0 hr ⟨ht.1.le, ht.2.le⟩ ht₀ huI hmin hnear hsmall hlocal
        exact H

end SpinGlass.Targets
