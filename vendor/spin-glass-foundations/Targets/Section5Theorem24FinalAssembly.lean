module

public import Targets.Section5Theorem24Assembly
public import Targets.Section5Smallness

@[expose] public section

/-!
# Uniform-away input to Talagrand's Theorem 2.4

This is the last quantifier adapter.  A concrete signed compact-region gap,
uniform on `[0,t₀] × [-1,1]` at each physical level, is converted to the
attainable-overlap statement and combined with the checked local estimate.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem talagrand_theorem_2_4_of_uniform_signed_away
    (β h : ℝ) (hβ : β ≠ 0)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hlevel : ∀ {k : ℕ} (s : RSBScheme k) (ε : ℝ),
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
        ∃ c > (0 : ℝ), ∀ {n : ℕ}, 0 < n →
          ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
          η ≤ |u - s.q r| →
          (∃ σ τ : Config n, overlap n σ τ = u) →
          constrainedPhi n s β h (sk n).U (k + 2 - r) t u ≤
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
  · obtain ⟨ε, hε, hsmall, hfar⟩ :=
      exists_section5_common_accuracy β hβ ht₀
    refine ⟨ε, hε, ?_⟩
    intro k s hmass hqstrict hnear hmin
    apply exists_uniform_quadratic_reduced_of_level_away_gaps
      s β h ε sk hβ hmass hqstrict hnear hmin ht₀ hsmall
    intro η hη r hr0 hr
    obtain ⟨c, hc, Hc⟩ := hlevel s ε hmass hqstrict hnear hmin
      hsmall hfar η hη r hr0 hr
    refine ⟨c, hc, ?_⟩
    intro n hn t ht u hu haway
    obtain ⟨σ, τ, hστ⟩ := mem_attainableOverlaps.mp hu
    have huI : u ∈ Icc (-1 : ℝ) 1 := by
      have H := abs_overlap_le_one hn σ τ
      rw [hστ] at H
      exact abs_le.mp H
    exact Hc hn t ⟨ht.1.le, ht.2.le⟩ u huI haway ⟨σ, τ, hστ⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro k s hmass hqstrict hnear hmin
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [] with n
    intro t ht
    exact (ht₀nonneg (ht.1.trans ht.2).le).elim

end SpinGlass.Targets
