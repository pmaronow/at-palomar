module

public import Targets.Section5InitialSigned

@[expose] public section

/-!
# Negative initial and first-level interval assembly

The initial signed estimate is put in the same system-size-independent deficit
form as the interleaved estimates. The actual shared field, original minimizing
scheme, and comparison with twice `guerraPsi` are unchanged.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Proposition 5.4 with its positive deficit chosen before all system sizes
and disorders. The endpoint `u = -q₁` is included. -/
theorem exists_constrainedPhi_initial_signed_gap
    (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Ico (-s.q 1) 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > 0, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨(1 - t₀) ^ 2 / 8 * u ^ 2, ?_, ?_⟩
  · exact mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num))
      (sq_pos_of_ne_zero (ne_of_lt hu.2))
  · intro n hn sk hatt
    obtain ⟨σ, τ, hστ⟩ := hatt
    letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
    exact constrainedPhi_initial_signed_uniform hn s β h ε sk hβ hm hright
      ht ht₀ hu hmin hnear hsmall

end SpinGlass.Targets
