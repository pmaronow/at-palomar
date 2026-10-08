module

public import Targets.Section5LocalReducedAssembly

@[expose] public section

/-!
# One local radius for every physical level

The local Section 5 argument naturally returns one positive radius at each
physical overlap.  There are only finitely many physical levels, so their
minimum is still positive.  This module records that elementary finite
minimum with the exact level ordering used by `constrainedPhi`.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_local_quadratic_reduced_all_levels
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ η > (0 : ℝ), ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d, 1 ≤ d → d ≤ k + 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |u - s.q (k + 2 - d)| ≤ η →
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U d t u ≤
        2 * guerraPsi s β h t - (1 - t₀) ^ 2 /
          section5LocalLeftConstant β 535 *
          (u - s.q (k + 2 - d)) ^ 2 := by
  classical
  have Hlevel : ∀ r, 1 ≤ r → r ≤ k + 1 →
      ∃ η > (0 : ℝ), η = section5LocalReducedRadius s β t₀ r ∧
        ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
        |u - s.q r| ≤ η →
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
          2 * guerraPsi s β h t - (1 - t₀) ^ 2 /
            section5LocalLeftConstant β 535 * (u - s.q r) ^ 2 := by
    intro r hr0 hr
    exact exists_uniform_local_quadratic_reduced_min s β h ε hβ hmass
      hqstrict hnear hmin hr0 hr ht₀ hsmall
  let D : Finset ℕ := Finset.Icc 1 (k + 1)
  have hDne : D.Nonempty := ⟨1, by simp [D]⟩
  let e : ℕ → ℝ := fun r => if hr : 1 ≤ r ∧ r ≤ k + 1 then
    Classical.choose (Hlevel r hr.1 hr.2) else 1
  have hepos : ∀ r ∈ D, 0 < e r := by
    intro r hr
    have hr' := Finset.mem_Icc.mp (by simpa [D] using hr)
    simpa [e, hr'.1, hr'.2] using
      (Classical.choose_spec (Hlevel r hr'.1 hr'.2)).1
  let η : ℝ := D.inf' hDne e
  have hη : 0 < η := by
    dsimp [η]
    exact (Finset.lt_inf'_iff hDne).mpr hepos
  refine ⟨η, hη, ?_⟩
  intro n hn sk t ht d hd0 hd u hu hdist hatt
  let r := k + 2 - d
  have hr0 : 1 ≤ r := by omega
  have hr : r ≤ k + 1 := by omega
  have hrD : r ∈ D := by simp [D, hr0, hr]
  have hηe : η ≤ e r := Finset.inf'_le e hrD
  have heq : e r = section5LocalReducedRadius s β t₀ r := by
    have H := (Classical.choose_spec (Hlevel r hr0 hr)).2.1
    simpa [e, hr0, hr] using H
  have hdist' : |u - s.q r| ≤ e r := hdist.trans hηe
  have hdist'' : |u - s.q r| ≤ Classical.choose (Hlevel r hr0 hr) := by
    simpa [e, hr0, hr] using hdist'
  have Hbound := (Classical.choose_spec (Hlevel r hr0 hr)).2.2
    hn sk t ht u hu hdist'' hatt
  have hdr : k + 2 - r = d := by
    dsimp [r]
    omega
  simpa only [r, hdr] using Hbound

end SpinGlass.Targets
