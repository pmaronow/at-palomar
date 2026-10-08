module

public import Targets.Section5PhysicalAwayCompact
public import Targets.Section5LeftOffDiagonalTube

@[expose] public section

/-!
# Concrete compact gap on the two physical bands

This is the unconditional physical part of the positive-overlap away-region
assembly.  It combines the checked left and right physical-band compact
estimates; no finite-cover or scalar-gap hypothesis is left abstract here.
The separate outside-trial bands still require their breakpoint glue.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_positive_away_physical_core
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
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) 1,
      (u ∈ Icc (s.q (r - 1)) (s.q r) ∨
        u ∈ Icc (s.q r) (s.q (r + 1))) →
      η ≤ |u - s.q r| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let Xl : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q (r - 1)) (s.q r)
  let Xr : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q r) (s.q (r + 1))
  have hXl : IsCompact Xl := by
    dsimp [Xl]
    exact isCompact_Icc.prod isCompact_Icc
  have hXr : IsCompact Xr := by
    dsimp [Xr]
    exact isCompact_Icc.prod isCompact_Icc
  have htXl : ∀ z ∈ Xl, z.1 ∈ Icc (0 : ℝ) t₀ := by
    intro z hz
    exact hz.1
  have huXl : ∀ z ∈ Xl, z.2 ∈ Icc (s.q (r - 1)) (s.q r) := by
    intro z hz
    exact hz.2
  have htXr : ∀ z ∈ Xr, z.1 ∈ Icc (0 : ℝ) t₀ := by
    intro z hz
    exact hz.1
  have huXr : ∀ z ∈ Xr, z.2 ∈ Icc (s.q r) (s.q (r + 1)) := by
    intro z hz
    exact hz.2
  let Sl : Set (ℝ × ℝ) := Xl ∩ {z | η ≤ |z.2 - s.q r|}
  let Sr : Set (ℝ × ℝ) := Xr ∩ {z | η ≤ |z.2 - s.q r|}
  have hSl : IsCompact Sl := by
    dsimp [Sl]
    exact hXl.inter_right (isClosed_le continuous_const (by fun_prop))
  have hSr : IsCompact Sr := by
    dsimp [Sr]
    exact hXr.inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨δl, hδl, Hl⟩ := exists_uniform_constrainedPhi_physical_left_away
    (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hSl
    (fun z hz => (htXl z hz.1))
    (fun z hz => (huXl z hz.1))
    (fun z hz => hz.2) hmin hnear hsmall hfar
  obtain ⟨δr, hδr, Hr⟩ := exists_uniform_constrainedPhi_physical_right_away
    (Ω := Ω) s β h ε (by omega) hr hβ hmass hqstrict ht₀ hη hSr
    (fun z hz => (htXr z hz.1))
    (fun z hz => (huXr z hz.1))
    (fun z hz => hz.2) hmin hnear hsmall hfar
  refine ⟨min δl δr, lt_min hδl hδr, ?_⟩
  intro t ht u hu hband haway n hn sk hatt
  rcases hband with hl | hrband
  · have H := Hl (t, u) ⟨⟨ht, hl⟩, haway⟩ hn sk hatt
    exact H.trans (by linarith [min_le_left δl δr])
  · have H := Hr (t, u) ⟨⟨ht, hrband⟩, haway⟩ hn sk hatt
    exact H.trans (by linarith [min_le_right δl δr])

theorem exists_uniform_constrainedPhi_positive_away_physical_with_left_tube
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
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) 1,
      (|u - s.q (r - 1)| ≤ ρ ∨
        u ∈ Icc (s.q (r - 1)) (s.q r) ∨
        u ∈ Icc (s.q r) (s.q (r + 1))) →
      η ≤ |u - s.q r| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hqr : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 :=
    (s.overlap_directions_of_strict hqstrict (by omega) hr).2
  obtain ⟨ρ, hρ, δtube, hδtube, Htube⟩ :=
    exists_uniform_constrainedPhi_physical_left_two_sided
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqr hright ht₀ hmin hnear hsmall hfar
  obtain ⟨δcore, hδcore, Hcore⟩ :=
    exists_uniform_constrainedPhi_positive_away_physical_core
      (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict ht₀ hη hmin hnear hsmall hfar
  refine ⟨ρ, hρ, min δtube δcore, lt_min hδtube hδcore, ?_⟩
  intro t ht u hu hregion haway n hn sk hatt
  rcases hregion with hnearleft | hphysical
  · have H := Htube t ht u hnearleft hn sk hatt
    exact H.trans (by linarith [min_le_left δtube δcore])
  · have H := Hcore t ht u hu hphysical haway hn sk hatt
    exact H.trans (by linarith [min_le_right δtube δcore])

theorem exists_uniform_constrainedPhi_positive_away_initial_physical_core
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hβ : β ≠ 0)
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
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) 1,
      η ≤ |u - s.q 1| →
      (u ∈ Icc (0 : ℝ) (s.q 1) ∨
        u ∈ Icc (s.q 1) (s.q 2)) → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hm : s.m 0 < s.m 1 := hmass 0 (Nat.zero_le _)
  have hright : s.q 1 < s.q 2 ∨ s.q 1 = 1 :=
    (s.overlap_directions_of_strict hqstrict (r := 1) le_rfl (by omega)).2
  obtain ⟨δl, hδl, Hl⟩ := constrainedPhi_initial_positive_away_gap
    (Ω := Ω) s β h ε hβ hm hright ht₀ hη hmin hnear hsmall
  let Sr : Set (ℝ × ℝ) :=
    (Icc (0 : ℝ) t₀ ×ˢ Icc (s.q 1) (s.q 2)) ∩
      {z | η ≤ |z.2 - s.q 1|}
  have hSr : IsCompact Sr := by
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const (by fun_prop))
  obtain ⟨δr, hδr, Hr⟩ := exists_uniform_constrainedPhi_physical_right_away
    (Ω := Ω) s β h ε (by norm_num) (by omega) hβ hmass hqstrict ht₀ hη hSr
    (fun z hz => hz.1.1) (fun z hz => hz.1.2) (fun z hz => hz.2)
    hmin hnear hsmall hfar
  refine ⟨min δl δr, lt_min hδl hδr, ?_⟩
  intro t ht u hu haway hband n hn sk hatt
  rcases hband with hl | hrband
  · have H := Hl ht hl haway hn sk hatt
    exact H.trans (by linarith [min_le_left δl δr])
  · have H := Hr (t, u) ⟨⟨ht, hrband⟩, haway⟩ hn sk hatt
    exact H.trans (by linarith [min_le_right δl δr])

end SpinGlass.Targets
