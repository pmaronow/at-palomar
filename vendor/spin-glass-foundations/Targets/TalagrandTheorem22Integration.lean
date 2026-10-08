module

public import Targets.TalagrandTheorem24
public import Targets.RSBSchemeOverlapReduction

@[expose] public section

/-!
# Theorem 2.4 to Theorem 2.2 integration

This module closes the downstream mathematical integration step. The completed uniform
quadratic estimate of Theorem 2.4 has exactly the hypothesis required by the
strict-mass/strict-overlap reduction, which already contains Proposition 2.3 and
the concentration-to-convergence argument.

`Targets.TalagrandFinal` gives this conclusion the canonical
`talagrand_theorem_2_2` name.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The completed Theorem 2.4 estimate supplies the strict-scheme quadratic
hypothesis needed by the existing reduction, and therefore yields the exact
conclusion of Talagrand's Theorem 2.2. -/
theorem talagrand_theorem_2_2_from_theorem_2_4 (β h : ℝ) (hβ : 0 < β)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun n => guerraPhi n s β h (sk n).U t) atTop
          (𝓝 (guerraPsi s β h t)) := by
  apply talagrand_theorem_2_2_of_strict_mass_overlap_quadratic_bound β h sk ht₀
  exact talagrand_theorem_2_4 β h hβ.ne' sk ht₀

#print axioms talagrand_theorem_2_2_from_theorem_2_4

end SpinGlass.Targets
