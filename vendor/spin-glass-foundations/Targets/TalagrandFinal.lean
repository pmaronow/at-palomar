module

public import Targets.TalagrandTheorem22Integration

@[expose] public section

/-!
# Canonical final theorems in Talagrand's proof

This module sits after the Section 3--5 development in the acyclic import graph.
It gives the checked downstream Theorem 2.2 integration its canonical public name
and then applies the core final-deduction theorem to obtain the Parisi formula.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **Talagrand's Theorem 2.2.** Near-optimal fixed-level minimizing schemes have
interpolated free energy converging to the corresponding Guerra comparison on
every compact time interval below one. -/
theorem talagrand_theorem_2_2 (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun N => guerraPhi N s β h (sk N).U t) atTop
          (𝓝 (guerraPsi s β h t)) := by
  exact talagrand_theorem_2_2_from_theorem_2_4 β h hβ sk ht₀

/-- **The Parisi formula for the exact-covariance SK model.** The free energy
`F_N` converges to the value given by the Parisi variational formula. -/
theorem parisi_formula (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ N : ℕ, SKDisorder (Ω := Ω) N β h) :
    Tendsto (fun N => free_entropy (Ω := Ω) (N := N) (β := β) (h := h) (sk N).U)
      atTop (𝓝 (parisiValue β h)) := by
  apply parisi_formula_of_theorem_2_2 β h hβ sk
  intro t₀ ht₀
  exact talagrand_theorem_2_2 β h hβ sk ht₀

#print axioms talagrand_theorem_2_2
#print axioms parisi_formula

end SpinGlass.Targets
