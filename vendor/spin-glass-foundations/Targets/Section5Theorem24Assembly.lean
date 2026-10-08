module

public import Targets.Section5UniformLocalRadius
public import Targets.Section5RegionalAssembly

@[expose] public section

/-!
# Final quantifier assembly for Theorem 2.4

Once each physical level has a uniform additive gap away from the common
local radius, the local quadratic estimate and a finite minimum over levels
give Talagrand's single constant `K` with the required quantifier order.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_quadratic_reduced_of_level_away_gaps
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (haway : ∀ η > (0 : ℝ), ∀ r, 1 ≤ r → r ≤ k + 1 →
      ∃ c > (0 : ℝ), ∀ {n : ℕ}, 0 < n →
        ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ u ∈ attainableOverlaps n,
        η ≤ |u - s.q r| →
        constrainedPhi n s β h (sk n).U (k + 2 - r) t u ≤
          2 * guerraPsi s β h t - c) :
    ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t -
          (u - s.q (k + 2 - d)) ^ 2 / K := by
  obtain ⟨η, hη, Hlocal⟩ := exists_uniform_local_quadratic_reduced_all_levels
    (Ω := Ω) s β h ε hβ hmass hqstrict hnear hmin ht₀ hsmall
  have Haway : ∀ d, 1 ≤ d → d ≤ k + 1 →
      ∃ c > (0 : ℝ), ∀ {n : ℕ}, 0 < n →
        ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ u ∈ attainableOverlaps n,
        η ≤ |u - s.q (k + 2 - d)| →
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t - c := by
    intro d hd0 hd
    let r := k + 2 - d
    have hr0 : 1 ≤ r := by omega
    have hr : r ≤ k + 1 := by omega
    obtain ⟨c, hc, Hc⟩ := haway η hη r hr0 hr
    refine ⟨c, hc, ?_⟩
    intro n hn t ht u hu hdist
    have H := Hc hn t ht u hu hdist
    have hdr : k + 2 - r = d := by
      dsimp [r]
      omega
    simpa only [r, hdr] using H
  let a : ℕ → ℝ := fun _ =>
    (1 - t₀) ^ 2 / section5LocalLeftConstant β 535
  let c : ℕ → ℝ := fun d => if hd : 1 ≤ d ∧ d ≤ k + 1 then
    Classical.choose (Haway d hd.1 hd.2) else 1
  have ha : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < a d := by
    intro d hd0 hd
    exact div_pos (sq_pos_of_pos (sub_pos.mpr ht₀))
      (section5LocalLeftConstant_pos β 535 (by norm_num))
  have hc : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < c d := by
    intro d hd0 hd
    simpa [c, hd0, hd] using (Classical.choose_spec (Haway d hd0 hd)).1
  apply exists_uniform_quadratic_bound_of_finite_regional s β h sk a c hη ha hc
  · intro n hn t ht d hd0 hd u hu hdist
    obtain ⟨σ, τ, hστ⟩ := mem_attainableOverlaps.mp hu
    have huI : u ∈ Icc (-1 : ℝ) 1 := by
      have H := abs_overlap_le_one hn σ τ
      rw [hστ] at H
      exact abs_le.mp H
    have H := Hlocal hn (sk n) t ht d hd0 hd u
      huI hdist ⟨σ, τ, hστ⟩
    simpa only [a] using H
  · intro n hn t ht d hd0 hd u hu hdist
    have H := (Classical.choose_spec (Haway d hd0 hd)).2
      hn t ht u hu hdist
    simpa [c, hd0, hd] using H

end SpinGlass.Targets
