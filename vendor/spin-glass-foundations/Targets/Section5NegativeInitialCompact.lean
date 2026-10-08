module

public import Targets.Section5NegativeInitialAssembly
public import Targets.Section5FiniteCompactCover

@[expose] public section

/-!
# Compact initial negative-overlap region

The first trial interval at physical level one is handled by Talagrand's
signed initial estimate.  This adapter turns its explicit `u²` deficit into a
single compact-region gap, including the (vacuous when `q₁ = 0`) endpoint
degeneracy.  It is deliberately separate from the positive-time interleaved
negative adapter, whose scalar strictness starts at the second trial level.
-/

open MeasureTheory ProbabilityTheory Real Set Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_negative_initial_trial
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0 ∧ |z.2| ∈ Icc (0 : ℝ) (s.q 1))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let C : ℝ := (1 - t₀) ^ 2 / 8
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses hS
    (fun (_ : Unit) z => C * z.2 ^ 2)
    (fun _ => continuousOn_const.mul (continuous_snd.continuousOn.pow 2))
    (fun z hz => by
      refine ⟨(), ?_⟩
      have hzneg : z.2 ≠ 0 := ne_of_lt (hu z hz).1
      have hC : 0 < C := by
        dsimp [C]
        positivity
      exact mul_pos hC (sq_pos_of_ne_zero hzneg))
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n z.2) := ⟨⟨(σ, τ), hστ⟩⟩
  have hleft : -s.q 1 ≤ z.2 := by
    have habs : |z.2| ≤ s.q 1 := (hu z hz).2.2
    have hq : 0 ≤ s.q 1 := s.q_nonneg (by omega)
    rw [abs_of_neg (hu z hz).1] at habs
    linarith
  have H := constrainedPhi_initial_signed_uniform hn s β h ε sk hβ hm hright
    (ht z hz) ht₀ ⟨hleft, (hu z hz).1⟩ hmin hnear hsmall
  obtain ⟨i, Hδ'⟩ := Hδ z hz
  dsimp [C] at Hδ'
  linarith

end SpinGlass.Targets
