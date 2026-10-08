module

public import Targets.Section5NegativeCompact
public import Targets.Section5TerminalPadding

@[expose] public section

/-!
# Compact negative terminal trial interval

Redundant mass-one padding turns the last signed trial interval into an
ordinary admissible interval.  The compact negative-trial theorem can then be
transported back without changing either the original constrained pressure or
the Guerra comparison function.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_negative_terminal_padded
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : 0 < s.m 1) (hq : s.q 1 < s.q 2)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0 ∧
      |z.2| ∈ Icc (s.q (k + 1)) 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let sp := s.padOneLast
  have hspm : 0 < sp.m 1 := by
    simpa only [sp, s.padOneLast_m (p := 1) (by omega)] using hm
  have hspq : sp.q 1 < sp.q 2 := by
    simpa only [sp, s.padOneLast_q (p := 1) (by omega),
      s.padOneLast_q (p := 2) (by omega)] using hq
  have hspQ : section4TVarianceQ sp β h r (sp.m (r - 1)) 0 = sp.q r := by
    dsimp only [sp]
    rw [s.padOneLast_m (p := r - 1) (by omega),
      section4TVarianceQ_padOneLast s β h (by omega) (by omega),
      hQ, s.padOneLast_q (p := r) (by omega)]
  have htrial : ∀ z ∈ S, |z.2| ∈
      Icc (sp.q ((k + 2) - 1)) (sp.q (k + 2)) := by
    intro z hz
    simpa only [show k + 2 - 1 = k + 1 by omega, sp,
      s.padOneLast_q (p := k + 1) (by omega),
      s.padOneLast_q (p := k + 2) (by omega), s.q_top] using (hu z hz).2
  obtain ⟨δ, hδ, H⟩ := exists_uniform_constrainedPhi_negative_trial
    (Ω := Ω) sp β h hβ hr0 (by omega) (j := k + 2) (by omega) (by omega)
      hspm hspq hspQ ht₀ hS ht (fun z hz => (hu z hz).1) htrial
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  have Hp := H z hz hn sk hatt
  simpa only [show (k + 1) + 2 - r = (k + 2 - r) + 1 by omega,
    sp, constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hp

end SpinGlass.Targets
