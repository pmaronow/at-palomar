module

public import Targets.Section5Theorem24FinalAssembly
public import Targets.Section5ConcreteNegativeAway
public import Targets.Section5PositiveAwayCompleteCases

@[expose] public section

/-!
# Talagrand Theorem 2.4 public entry point

The exact public reduction is provided by
`talagrand_theorem_2_4_of_uniform_signed_away`.  The bridge below shows that
the now-complete negative analysis leaves precisely the concrete positive
away estimate as its only input.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The final public conclusion from a concrete positive-away assembly.
All negative overlaps, sign crossings, compact assembly, and conversion to
the quadratic estimate are discharged internally. -/
theorem talagrand_theorem_2_4_of_positive_away_concrete
    (β h : ℝ) (hβ : β ≠ 0)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hpositive : ∀ {k : ℕ} (s : RSBScheme k) (ε : ℝ),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k,
        parisiFunctional s β h ≤ parisiFunctional s' β h) →
      section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀ →
      section5FarLeftBound β * Real.sqrt ε ≤
        (1 - t₀) * (β ^ 2 / 2) *
          ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2 →
      ∀ η > (0 : ℝ), ∀ r, 1 ≤ r → r ≤ k + 1 →
        ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
          ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
          ∀ {n : ℕ}, 0 < n → ∀ sk' : SKDisorder (Ω := Ω) n β h,
          (∃ σ τ : Config n, overlap n σ τ = u) →
          constrainedPhi n s β h sk'.U (k + 2 - r) t u ≤
            2 * guerraPsi s β h t - c) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k,
        parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
        ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
          constrainedPhi n s β h (sk n).U d t u ≤
            2 * guerraPsi s β h t -
              (u - s.q (k + 2 - d)) ^ 2 / K := by
  by_cases ht₀nonneg : 0 ≤ t₀
  · apply talagrand_theorem_2_4_of_uniform_signed_away β h hβ sk ht₀
    intro k s ε hmass hqstrict hnear hmin hsmall hfar η hη r hr0 hr
    have hpos := hpositive s ε hmass hqstrict hnear hmin hsmall hfar
      η hη r hr0 hr
    obtain ⟨c, hc, Hc⟩ :=
      exists_uniform_constrainedPhi_signed_away_of_positive_concrete
        (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict hnear hmin
          ht₀nonneg ht₀ hsmall hfar hη hpos
    refine ⟨c, hc, ?_⟩
    intro n hn t ht u hu haway hatt
    exact Hc t ht u hu haway hn (sk n) hatt
  · apply talagrand_theorem_2_4_of_uniform_signed_away β h hβ sk ht₀
    intro k s ε hmass hqstrict hnear hmin hsmall hfar η hη r hr0 hr
    refine ⟨1, by norm_num, ?_⟩
    intro n hn t ht
    exact (ht₀nonneg (ht.1.trans ht.2)).elim

/-- Talagrand's Theorem 2.4: the uniform quadratic constrained-free-energy
gap, with the positive and negative overlap assemblies fully discharged. -/
theorem talagrand_theorem_2_4
    (β h : ℝ) (hβ : β ≠ 0)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k,
        parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
        ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
          constrainedPhi n s β h (sk n).U d t u ≤
            2 * guerraPsi s β h t -
              (u - s.q (k + 2 - d)) ^ 2 / K := by
  apply talagrand_theorem_2_4_of_positive_away_concrete β h hβ sk ht₀
  intro k s ε hmass hqstrict hnear hmin hsmall hfar η hη r hr0 hr
  exact exists_uniform_constrainedPhi_positive_away_complete
    (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη
      hmin hnear hsmall hfar

#print axioms talagrand_theorem_2_4

end SpinGlass.Targets
