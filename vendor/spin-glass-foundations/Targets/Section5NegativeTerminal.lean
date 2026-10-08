module

public import Targets.Section5TerminalPadding
public import Targets.Section5InterleavedBound
public import Targets.Section5OutsideIntervals

@[expose] public section

/-!
# Negative overlaps through the final trial interval

Redundant terminal padding makes the final trial interval admissible for the
proved mixed interpolation. The negative strictness proof needs only the first
positive mass and the first interior overlap gap, not strictness of all padded
masses. Exact padding identities return the estimate to the original scheme.
In particular, zero first overlap is allowed at every physical level `r ≥ 2`.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {k : ℕ}

private theorem negative_gap_with_final_trial
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 2) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  have hmp : 0 < s.padOneLast.m 1 := by
    simpa only [s.padOneLast_m (p := 1) (by omega)] using hm
  have hqp : s.padOneLast.q 1 < s.padOneLast.q 2 := by
    simpa only [s.padOneLast_q (p := 1) (by omega),
      s.padOneLast_q (p := 2) (by omega)] using hq
  have hup : |u| ∈ Set.Icc (s.padOneLast.q (j - 1)) (s.padOneLast.q j) := by
    simpa only [s.padOneLast_q (p := j - 1) (by omega), s.padOneLast_q hj] using hu
  obtain ⟨δ, hδ, _, H⟩ := exists_constrainedPhi_interleaved_gap_negative
    (Ω := Ω) s.padOneLast β h hβ ht hr0 (by omega) hj0 (by omega) hmp hqp huneg hup
  refine ⟨δ, hδ, ?_⟩
  intro n hn sk hatt
  have Hd := H hn sk hatt
  simpa only [show k + 1 + 2 - r = (k + 2 - r) + 1 by omega,
    constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hd

/-- The negative final trial interval has a strict deficit for the original
scheme. No strict-mass or minimality hypothesis on its padding is used. -/
theorem exists_constrainedPhi_gap_negative_terminal
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : 0 < s.m 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : s.q (k + 1) < |u|) (hutop : |u| ≤ 1) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  apply negative_gap_with_final_trial s β h hβ ht hr0 hr (j := k + 2)
    (by omega) le_rfl hm hq huneg
  simpa only [show k + 2 - 1 = k + 1 by omega, s.q_top, Set.mem_Icc]
    using And.intro hu.le hutop

/-- Every negative overlap in `[-1,0)` has a strict original-free-energy
deficit at physical levels at least two, including all trial breakpoints and
zero first overlap. The deficit is chosen before every system size/disorder. -/
theorem exists_constrainedPhi_gap_negative_all_trials
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : 0 < s.m 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hutop : |u| ≤ 1) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  obtain ⟨j, hj0, hj, hprev, hnext⟩ := exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt huneg))
    (show |u| ≤ s.q (k + 2) by simpa only [s.q_top] using hutop)
  exact negative_gap_with_final_trial s β h hβ ht hr0 hr hj0 hj hm hq huneg
    ⟨hprev.le, hnext⟩

/-- At the first physical level, every negative overlap beyond the initial
interval is strict when the first frozen shared field is nondegenerate. The
final trial interval is included, without a supplied trial index. -/
theorem exists_constrainedPhi_gap_negative_first_beyond
    (s : RSBScheme k) (β h : ℝ) {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu1 : s.q 1 < |u|) (hutop : |u| ≤ 1) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  obtain ⟨j, hj0, hj, hprev, hnext⟩ := exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using abs_pos.mpr (ne_of_lt huneg))
    (show |u| ≤ s.q (k + 2) by simpa only [s.q_top] using hutop)
  have hj2 : 2 ≤ j := by
    by_contra h
    have he : j = 1 := by omega
    rw [he] at hnext
    exact (not_le_of_gt hu1) hnext
  have hmp : 0 < s.padOneLast.m 1 := by
    simpa only [s.padOneLast_m (p := 1) (by omega)] using hm
  have hq1p : 0 < s.padOneLast.q 1 := by
    simpa only [s.padOneLast_q (p := 1) (by omega)] using hq1
  have hqp : s.padOneLast.q 1 < s.padOneLast.q 2 := by
    simpa only [s.padOneLast_q (p := 1) (by omega),
      s.padOneLast_q (p := 2) (by omega)] using hq
  have hu1p : s.padOneLast.q 1 < |u| := by
    simpa only [s.padOneLast_q (p := 1) (by omega)] using hu1
  have hup : |u| ∈ Set.Icc (s.padOneLast.q (j - 1)) (s.padOneLast.q j) := by
    simpa only [s.padOneLast_q (p := j - 1) (by omega), s.padOneLast_q hj, Set.mem_Icc]
      using And.intro hprev.le hnext
  obtain ⟨δ, hδ, _, H⟩ := exists_constrainedPhi_interleaved_gap_negative_first
    (Ω := Ω) s.padOneLast β h hβ ht hj2 (by omega) hmp hq1p hqp huneg hu1p hup
  refine ⟨δ, hδ, ?_⟩
  intro n hn sk hatt
  simpa only [constrainedPhi_padOneLast, guerraPsi_padOneLast] using H hn sk hatt

/-- In particular, the final negative trial interval is strict at the first
physical level with positive first overlap. -/
theorem exists_constrainedPhi_gap_negative_first_terminal
    (s : RSBScheme k) (β h : ℝ) {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : s.q (k + 1) < |u|) (hutop : |u| ≤ 1) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  exact exists_constrainedPhi_gap_negative_first_beyond s β h hβ ht hm hq1 hq huneg
    ((s.q_mono' (k + 1) (by omega) 1 (by omega)).trans_lt hu) hutop

end SpinGlass.Targets
