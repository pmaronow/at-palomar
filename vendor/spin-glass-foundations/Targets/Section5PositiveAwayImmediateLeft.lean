module

public import Targets.Section5PositiveAwayPhysicalCore
public import Targets.Section5InterleavedCompact

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
# The immediate-left physical band

The endpoint tube around `q_(r-1)` is joined to the compact outside-trial
estimate on the trimmed remainder.  The statement is useful in particular
for `r = 2`, where this remainder is the initial interval below `q₁`.
-/
theorem exists_uniform_constrainedPhi_immediate_left_band
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (s.q (r - 2)) (s.q r),
      |u - s.q r| ≥ η → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      (|u - s.q (r - 1)| ≤ ρ ∨
        u ≤ s.q (r - 1) - ρ) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hleft : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 :=
    (s.overlap_directions_of_strict hqstrict (by omega) hr).2
  have hmassFin : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hmassr : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hmass (r - 1) (by omega)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) hr hβ hmassr (Or.inl hleft) hright hmin
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_constrainedPhi_physical_left_two_sided
      (Ω := Ω) s β h ε hr0 hr hβ hmass hleft hright ht₀ hmin hnear hsmall hfar
  let ρ : ℝ := min ρ₀ 1 / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_min hρ₀ (by norm_num)) (by norm_num)
  have hρle₀ : ρ ≤ ρ₀ := by
    dsimp [ρ]
    nlinarith [min_le_left ρ₀ 1]
  let S : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q (r - 2)) (s.q (r - 1) - ρ)
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod isCompact_Icc
  have houtside := exists_uniform_constrainedPhi_left_outside_trial
    (Ω := Ω) s β h (j := r - 1) hβ hr (by omega) (by omega) hmassFin hleft hQ ht₀ hS
    (fun z hz => hz.1)
    (fun z hz => by
      refine ⟨hz.2.1, ?_⟩
      exact lt_of_le_of_lt hz.2.2 (sub_lt_self _ hρ))
  obtain ⟨δ₁, hδ₁, Houtside⟩ := houtside
  refine ⟨ρ, hρ, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht u hu haway n hn sk hatt hcases
  rcases hcases with hnearTube | hfarLeft
  · have H := Htube t ht u (hnearTube.trans hρle₀) hn sk hatt
    exact H.trans (by linarith [min_le_left δ₀ δ₁])
  · have huupper : u < s.q (r - 1) := by linarith [hρ]
    have hulower : s.q (r - 2) ≤ u := hu.1
    have huz : (t, u) ∈ S := by
      refine ⟨ht, ?_⟩
      exact ⟨hulower, by linarith [hfarLeft, hρ]⟩
    have H := Houtside (t, u) huz hn sk hatt
    exact H.trans (by linarith [min_le_right δ₀ δ₁])

end SpinGlass.Targets
