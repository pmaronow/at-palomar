module

public import Targets.Section5InterleavedCompact
public import Targets.Section5NegativeTerminal

@[expose] public section

/-!
# Compact signed terminal interval at the first physical level

The positive-time signed comparison and the time-zero stationary lambda gain
remain valid after redundant terminal padding.  This supplies the compact
version of the last negative trial interval without assuming that the padded
scheme is itself a fixed-level minimizer.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_negative_initial_terminal_padded
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hβ : β ≠ 0) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2)
    (hQ : section4TVarianceQ s β h 1 (s.m 0) 0 = s.q 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0 ∧
      |z.2| ∈ Ioc (s.q (k + 1)) 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let sp := s.padOneLast
  have hmp : 0 < sp.m 1 := by
    simpa only [sp, s.padOneLast_m (p := 1) (by omega)] using hm
  have hq1p : 0 < sp.q 1 := by
    simpa only [sp, s.padOneLast_q (p := 1) (by omega)] using hq1
  have hqp : sp.q 1 < sp.q 2 := by
    simpa only [sp, s.padOneLast_q (p := 1) (by omega),
      s.padOneLast_q (p := 2) (by omega)] using hq
  have hQp : section4TVarianceQ sp β h 1 (sp.m 0) 0 = sp.q 1 := by
    dsimp only [sp]
    rw [s.padOneLast_m (p := 0) (by omega),
      section4TVarianceQ_padOneLast s β h (by omega) (by omega), hQ,
      s.padOneLast_q (p := 1) (by omega)]
  have htrial : ∀ z ∈ S, |z.2| ∈
      Icc (sp.q ((k + 2) - 1)) (sp.q (k + 2)) := by
    intro z hz
    have H := (hu z hz).2
    simpa only [show k + 2 - 1 = k + 1 by omega, sp,
      s.padOneLast_q (p := k + 1) (by omega),
      s.padOneLast_q (p := k + 2) (by omega), s.q_top, Set.mem_Icc] using
      And.intro H.1.le H.2
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit sp β h 1 (k + 2) z.1 z.2 ℓ := by
    intro z hz
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
        sp β h (r := 1) (j := k + 2) le_rfl (by omega) (by omega) z.2
      rw [hQp] at H
      have hsub : 0 < (sp.q 1 - z.2) ^ 2 / 2 := by
        exact div_pos (sq_pos_of_pos (sub_pos.mpr
          (lt_of_lt_of_le (hu z hz).1 (sp.q_nonneg (by omega))))) (by norm_num)
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit]
      rw [htzero]
      linarith
    · have htime : z.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      have hbelow : sp.q 1 < |z.2| := by
        have H := (hu z hz).2.1
        have hmono : sp.q 1 ≤ sp.q (k + 1) := sp.q_mono' (k + 1) (by omega) 1 (by omega)
        have hlast : sp.q (k + 1) = s.q (k + 1) :=
          s.padOneLast_q (p := k + 1) (by omega)
        rw [hlast] at hmono
        exact hmono.trans_lt H
      have H := section5InterleavedScalarV_zero_lt_negative_of_q1_pos
        sp β h hβ htime (r := 1) le_rfl (j := k + 2) (by omega) (by omega)
          hmp hq1p hqp (hu z hz).1 hbelow (htrial z hz)
      refine ⟨0, ?_⟩
      simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
      exact sub_pos.mpr H
  obtain ⟨δ, hδ, H⟩ := exists_uniform_constrainedPhi_gap_on_compact_trial
    (Ω := Ω) sp β h (r := 1) (j := k + 2) le_rfl (by omega)
      (by omega) (by omega) hS
      (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  have Hp := H z hz hn sk hatt
  simpa only [show (k + 1) + 2 - 1 = (k + 1) + 1 by omega,
    sp, constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hp

end SpinGlass.Targets
