module

public import Targets.Section5InterleavedCompact
public import Targets.Section5InterleavedMassPair
public import Targets.Section5TerminalPadding

@[expose] public section

/-!
# Compact terminal trial interval after redundant padding

The final trial interval is represented by the redundant mass-one padding.
The generic compact witness argument applies to the padded scheme (whose last
trial index is now admissible); the exact cascade and Guerra-function
identities then transport the resulting bound back to the original scheme.
The lower endpoint is kept open because the adjacent breakpoint belongs to
the preceding trial interval.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Uniform strictness on the terminal trial interval.  Only the original
scheme is assumed to have the relevant mass and overlap gaps; the padded
scheme is not assumed minimizing or strictly monotone. -/
theorem exists_uniform_constrainedPhi_right_terminal_padded
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hmass : s.m r < s.m (k + 1))
    (hq : s.q r < s.q (r + 1))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Ioc (s.q (k + 1)) 1) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let sp := s.padOneLast
  have hspq (p : ℕ) (hp : p ≤ k + 2) : sp.q p = s.q p :=
    s.padOneLast_q hp
  have hspm (p : ℕ) (hp : p ≤ k + 1) : sp.m p = s.m p :=
    s.padOneLast_m hp
  have hspQ : section4TVarianceQ sp β h r (sp.m (r - 1)) 0 = sp.q r := by
    calc
      section4TVarianceQ sp β h r (sp.m (r - 1)) 0 =
          section4TVarianceQ sp β h r (s.m (r - 1)) 0 := by
            rw [hspm (r - 1) (by omega)]
      _ = section4TVarianceQ s β h r (s.m (r - 1)) 0 :=
        section4TVarianceQ_padOneLast s β h hr0 (by omega) _ _
      _ = s.q r := hQ
      _ = sp.q r := (hspq r (by omega)).symm
  have hspj : k + 2 ≤ (k + 1) + 1 := by omega
  have hspj0 : 1 ≤ k + 2 := by omega
  have hspmass : sp.m r < sp.m ((k + 2) - 1) := by
    rw [show (k + 2) - 1 = k + 1 by omega, hspm r (by omega),
      hspm (k + 1) (by omega)]
    exact hmass
  have hspqgap : sp.q r < sp.q (r + 1) := by
    rw [hspq r (by omega), hspq (r + 1) (by omega)]
    exact hq
  have htrial : ∀ z ∈ S, |z.2| ∈
      Icc (sp.q ((k + 2) - 1)) (sp.q (k + 2)) := by
    intro z hz
    have hqnonneg : 0 ≤ s.q (k + 1) := s.q_nonneg (by omega)
    have hznonneg : 0 ≤ z.2 := hqnonneg.trans (hu z hz).1.le
    rw [abs_of_nonneg hznonneg, show (k + 2) - 1 = k + 1 by omega,
      hspq (k + 1) (by omega), hspq (k + 2) (by omega), s.q_top]
    exact ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hpos : ∀ z ∈ S, ∃ ℓ : ℝ,
      0 < section5InterleavedLambdaDeficit sp β h r (k + 2) z.1 z.2 ℓ := by
    intro z hz
    have hznonneg : 0 ≤ z.2 :=
      (s.q_nonneg (p := k + 1) (by omega)).trans (hu z hz).1.le
    have hqrz : sp.q r < z.2 := by
      have hstep : sp.q r < sp.q (r + 1) := hspqgap
      have htail : sp.q (r + 1) ≤ sp.q (k + 1) :=
        sp.q_mono' (k + 1) (by omega) (r + 1) (by omega)
      have hlast : sp.q (k + 1) < z.2 := by
        rw [hspq (k + 1) (by omega)]
        exact (hu z hz).1
      exact hstep.trans (htail.trans_lt hlast)
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
        sp β h hr0 (by omega) hspj z.2
      have Hq := H
      rw [hspm (r - 1) (by omega),
        section4TVarianceQ_padOneLast s β h hr0 (by omega)] at Hq
      rw [hQ] at Hq
      have hF : parisiF sp β ((k + 1) + 2) h = parisiF s β (k + 2) h := by
        exact congrFun (parisiF_padOneLast_succ s β (k + 2)) h
      rw [hF] at Hq
      have hsq : 0 < (sp.q r - z.2) ^ 2 / 2 :=
        div_pos (sq_pos_of_neg (sub_neg.mpr hqrz)) (by norm_num)
      have hsqS : 0 < (s.q r - z.2) ^ 2 / 2 := by
        rw [← hspq r (by omega)]
        exact hsq
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit]
      rw [htzero, hF]
      linarith
    · have htp : 0 < z.1 := lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero)
      have htime : z.1 < 1 := (ht z hz).2.trans_lt ht₀
      have hcv : 0 < z.1 * (β ^ 2 *
          (|z.2| - sp.q ((k + 2) - 1))) := by
        rw [abs_of_nonneg hznonneg]
        rw [show (k + 2) - 1 = k + 1 by omega,
          hspq (k + 1) (by omega)]
        exact mul_pos htp (mul_pos (sq_pos_of_ne_zero hβ)
          (sub_pos.mpr (hu z hz).1))
      have hbv : 0 < (1 - z.1) *
          (β ^ 2 * (sp.q (r + 1) - sp.q r)) :=
        mul_pos (sub_pos.mpr htime)
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hspqgap))
      have H := section5InterleavedScalarV_zero_lt_right_of_mass_lt sp β h
        ⟨htp.le, htime.le⟩ hspj (by omega) (htrial z hz) hspmass hbv hcv
      refine ⟨0, ?_⟩
      simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
      exact sub_pos.mpr H
  obtain ⟨δ, hδ, H⟩ := exists_uniform_constrainedPhi_gap_on_compact_trial (Ω := Ω)
    sp β h hr0 (by omega) hspj0 hspj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  have Hp := H z hz hn sk hatt
  simpa only [show (k + 1) + 2 - r = (k + 2 - r) + 1 by omega,
    sp, constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hp

end SpinGlass.Targets
