module

public import Targets.Section5ZeroInitialReflection
public import Targets.Section5RightBoundary
public import Targets.Section5FarRight

@[expose] public section

/-!
# Negative overlaps at the first physical level when the first overlap is zero

Original optimality proves zero external field and exact reflection of the
original constrained free energy. The already checked positive local-right,
and far-right bounds therefore apply without a new signed
interpolation. All gaps below are selected before system size and disorder.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The local quadratic estimate on the negative side of a zero first
overlap, using only original fixed-level minimality. -/
theorem constrainedPhi_local_negative_initial_zero
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (-(s.q 2)) 0) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hlocal : section5LocalLeftConstant β 535 * (-u) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * u ^ 2 := by
  letI : Nonempty (AT.ConstrainedPair n (-u)) := constrainedPair_nonempty_neg u
  rw [constrainedPhi_initial_zero_reflection_of_min s β h sk hβ hq hm
    (by simpa only [hq] using hq2) hmin]
  simpa only [neg_sq] using constrainedPhi_local_right_initial_zero hn s β h sk hβ hq hm
    ht ht₀ ⟨neg_nonneg.mpr hu.2, by linarith [hu.1]⟩ hmin hlocal

/-- Far negative overlaps in the first neighboring interval inherit the
actual far-right gap. The original field is not silently changed. -/
theorem exists_constrainedPhi_far_negative_initial_zero
    (s : RSBScheme k) (β h ε : ℝ) {L₁ t₀ t u : ℝ}
    (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    (hL : 0 < L₁) (ht₀ : t₀ < 1) (ht : t ∈ Set.Icc 0 t₀)
    (hu : u ∈ Set.Icc (-(s.q 2)) 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (-u))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - c := by
  obtain ⟨c, hc, H⟩ := exists_constrainedPhi_far_right_uniform_in_size (Ω := Ω)
    s β h ε (r := 1) le_rfl (by omega) hβ hL ht₀ ht
    (by simpa only [Nat.sub_self] using hm)
    (show -u ∈ Set.Icc (s.q 1) (s.q (1 + 1)) from by rw [hq]; constructor <;> linarith [hu.1, hu.2])
    hmin hnear (by simpa only [hq, sub_zero] using hfar) hsmall
  refine ⟨c, hc, fun {n} hn sk hatt => ?_⟩
  letI := hatt
  letI : Nonempty (AT.ConstrainedPair n (-u)) := constrainedPair_nonempty_neg u
  rw [constrainedPhi_initial_zero_reflection_of_min s β h sk hβ hq hm
    (by simpa only [hq] using hq2) hmin]
  simpa only [show k + 2 - 1 = k + 1 by omega] using H hn sk inferInstance

/-- The full negative first neighboring interval, including its left
endpoint, has a size-independent strict gap. Only the already established
beta-only far-right smallness condition is used in the far branch. -/
theorem exists_constrainedPhi_negative_initial_zero_neighbor
    (s : RSBScheme k) (β h ε : ℝ) {t₀ t u : ℝ}
    (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1) (hq2 : 0 < s.q 2)
    (ht₀ : t₀ < 1) (ht : t ∈ Set.Icc 0 t₀) (hu : u ∈ Set.Ico (-(s.q 2)) 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - c := by
  have hL := section5LocalLeftConstant_pos β 535 (by norm_num)
  by_cases hlocal : section5LocalLeftConstant β 535 * (-u) ≤ 1 - t₀
  · refine ⟨(1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * u ^ 2,
      mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) hL)
        (sq_pos_of_ne_zero (ne_of_lt hu.2)), ?_⟩
    intro n hn sk hatt
    letI := hatt
    exact constrainedPhi_local_negative_initial_zero hn s β h sk hβ hq hm hq2 ht ht₀
      ⟨hu.1, hu.2.le⟩ hmin hlocal
  · exact exists_constrainedPhi_far_negative_initial_zero (Ω := Ω) s β h ε hβ hq hm hq2
      hL ht₀ ht ⟨hu.1, hu.2.le⟩ hmin hnear (le_of_lt (lt_of_not_ge hlocal)) hsmall

end SpinGlass.Targets
