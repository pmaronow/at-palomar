module

public import Targets.Section5PressureGain

@[expose] public section

/-!
# Uniform smallness condition for the far-left overlap interval

In the SK setting the convexity defect underlying Talagrand (5.4) is the
quadratic quantity `β² (y - x)² / 2`. The estimates below put the positive-baseline case of
Proposition 5.5 in its uniform smallness form. They do not cover the initial
mass-zero interval or provide the compactness step needed for Theorem 2.4.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A beta-only choice of the constant `L₃` in the positive-baseline case of
Proposition 5.5. The factor four leaves room for a strict improvement. -/
noncomputable def section5FarLeftBound (β : ℝ) : ℝ :=
  4 * section4OptimalityBound β

theorem section5FarLeftBound_pos (β : ℝ) : 0 < section5FarLeftBound β :=
  mul_pos (by norm_num) (section4OptimalityBound_pos β)

theorem section5FarLeft_smallness {β ε L₁ t₀ t d : ℝ}
    (hβ : β ≠ 0) (hL : 0 < L₁) (ht₀ : t₀ < 1) (ht : t ≤ t₀)
    (hfar : 1 - t₀ ≤ L₁ * d)
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * d ^ 2 := by
  have htime : 0 < 1 - t₀ := sub_pos.mpr ht₀
  have hratio : 0 < (1 - t₀) / L₁ := div_pos htime hL
  have hratio_le : (1 - t₀) / L₁ ≤ d := by
    apply (div_le_iff₀ hL).mpr
    simpa only [mul_comm] using hfar
  have hsq : ((1 - t₀) / L₁) ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ hratio.le hratio_le 2
  have hβsq : 0 < β ^ 2 / 2 := div_pos (sq_pos_of_ne_zero hβ) (by norm_num)
  have hpos : 0 < (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2 :=
    mul_pos (mul_pos htime hβsq) (sq_pos_of_pos hratio)
  have hstep : (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2 ≤
      (1 - t) * (β ^ 2 / 2) * d ^ 2 := by
    calc
      _ ≤ (1 - t₀) * (β ^ 2 / 2) * d ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg htime.le hβsq.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 1 - t₀ ≤ 1 - t) hβsq.le)
        (sq_nonneg d)
  unfold section5FarLeftBound at hsmall
  have hstrict : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2 := by linarith
  exact hstrict.trans_le hstep

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Proposition 5.5 in the positive-baseline SK case, with the smallness
condition independent of the actual time and overlap within the far interval. -/
theorem constrainedPhi_lt_two_guerraPsi_of_far_left
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {L₁ t₀ t u : ℝ}
    (hβ : β ≠ 0) (hL : 0 < L₁) (ht₀ : t₀ < 1) (ht : t ∈ Set.Icc 0 t₀)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (s.q r - u))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  exact constrainedPhi_lt_two_guerraPsi_of_left_gap hn s β h ε sk hr0 hr hmpos hgap
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu hmin hnear
    (section5FarLeft_smallness hβ hL ht₀ ht.2 hfar hsmall)

/-- The same far-left hypothesis gives a strictly positive deficit chosen
before the system size and the disorder. The deficit may still depend on the
scheme, time and overlap; uniformity over those requires the later compactness
argument, not this pointwise statement. -/
theorem exists_constrainedPhi_far_left_uniform_in_size
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {L₁ t₀ t u : ℝ} (hβ : β ≠ 0) (hL : 0 < L₁) (ht₀ : t₀ < 1)
    (ht : t ∈ Set.Icc 0 t₀)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (s.q r - u))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ} (_hn : 0 < n) (sk : SKDisorder (Ω := Ω) n β h),
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - c := by
  exact exists_constrainedPhi_left_gap_uniform_in_size s β h ε hr0 hr hmpos hgap
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu hmin hnear
    (section5FarLeft_smallness hβ hL ht₀ ht.2 hfar hsmall)

end SpinGlass.Targets
