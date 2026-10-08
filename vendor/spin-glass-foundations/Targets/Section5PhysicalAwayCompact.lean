module

public import Targets.Section5FarCompact
public import Targets.Section5RightBoundary
public import Targets.Section5LeftUniform

@[expose] public section

/-!
# Compact gaps inside a physical neighboring interval

Away from the physical overlap, the local quadratic estimate already has a
fixed additive gap.  Where its small-distance hypothesis ends, the compact
far-mass comparison supplies the gap.  The two closed pieces meet at the
threshold, so no limiting point is lost.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem constrainedPhi_initial_positive_away_gap
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > (0 : ℝ), ∀ {t u : ℝ}, t ∈ Icc (0 : ℝ) t₀ →
      u ∈ Icc 0 (s.q 1) → η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  let a := (1 - t₀) ^ 2 / section5LocalLeftConstant β 535
  have ha : 0 < a := div_pos (sq_pos_of_pos (sub_pos.mpr ht₀))
    (section5LocalLeftConstant_pos β 535 (by norm_num))
  refine ⟨a * η ^ 2, mul_pos ha (sq_pos_of_pos hη), ?_⟩
  intro t u ht hu haway n hn sk hatt
  letI : Nonempty (AT.ConstrainedPair n u) := by
    obtain ⟨σ, τ, hστ⟩ := hatt
    exact ⟨⟨(σ, τ), hστ⟩⟩
  have H := constrainedPhi_initial_left_uniform hn s β h ε sk hβ hm hright
    ht ht₀ hu hmin hnear hsmall
  have hsquare : η ^ 2 ≤ (u - s.q 1) ^ 2 := by
    exact (sq_le_sq).2 (by simpa [abs_of_pos hη] using haway)
  have Hmul := mul_le_mul_of_nonneg_left hsquare ha.le
  change a * η ^ 2 ≤ a * (u - s.q 1) ^ 2 at Hmul
  exact H.trans (by linarith)

theorem exists_uniform_constrainedPhi_physical_left_away
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q (r - 1)) (s.q r))
    (haway : ∀ z ∈ S, η ≤ |z.2 - s.q r|)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let L := section5LocalLeftConstant β 535
  let a := (1 - t₀) ^ 2 / L
  let Sl := S ∩ {z | L * (s.q r - z.2) ≤ 1 - t₀}
  let Sf := S ∩ {z | 1 - t₀ ≤ L * (s.q r - z.2)}
  have hL : 0 < L := section5LocalLeftConstant_pos β 535 (by norm_num)
  have ha : 0 < a := div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) hL
  have hSl : IsCompact Sl := hS.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hSf : IsCompact Sf := hS.inter_right (isClosed_le continuous_const (by fun_prop))
  have hm : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using hmass (r - 1) (by omega)
  have hmpos : 0 < s.m (r - 1) := by
    have H := hmass 0 (by omega : 0 ≤ k)
    have Hmono := s.m_mono' (r - 1) (by omega) 1 (by omega)
    simpa only [s.m_zero] using H.trans_le Hmono
  obtain ⟨δf, hδf, Hf⟩ := exists_uniform_constrainedPhi_compact_far_left
    (Ω := Ω) s β h ε (r := r) (by omega) hr hmpos hm hβ hL ht₀ hSf
      (fun z hz => ht z hz.1) (fun z hz => hu z hz.1)
      (fun z hz => hz.2) hmin hnear hfar
  let δl := a * η ^ 2
  have hδl : 0 < δl := mul_pos ha (sq_pos_of_pos hη)
  refine ⟨min δl δf, lt_min hδl hδf, ?_⟩
  intro z hz n hn sk hatt
  by_cases hloc : L * (s.q r - z.2) ≤ 1 - t₀
  · letI : Nonempty (AT.ConstrainedPair n z.2) := by
      obtain ⟨σ, τ, hστ⟩ := hatt
      exact ⟨⟨(σ, τ), hστ⟩⟩
    have H := constrainedPhi_local_left_uniform hn s β h ε sk (by omega) hr hβ hm
      (s.overlap_directions_of_strict hqstrict (by omega) hr).2
      (ht z hz) ht₀ (hu z hz) hmin hnear hsmall (by simpa only [L] using hloc)
    have habs : |z.2 - s.q r| = s.q r - z.2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hu z hz).2)]
      ring
    have hsq : η ^ 2 ≤ (z.2 - s.q r) ^ 2 := by
      exact (sq_le_sq).2 (by simpa [abs_of_pos hη] using haway z hz)
    have hgain : δl ≤ a * (z.2 - s.q r) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq ha.le
    have hminl : min δl δf ≤ δl := min_le_left _ _
    exact H.trans (by simpa only [a, L] using (show
      2 * guerraPsi s β h z.1 - a * (z.2 - s.q r) ^ 2 ≤
        2 * guerraPsi s β h z.1 - min δl δf by linarith))
  · have Hz := Hf z ⟨hz, le_of_not_ge hloc⟩ hn sk hatt
    exact Hz.trans (by linarith [min_le_right δl δf])

theorem exists_uniform_constrainedPhi_physical_right_away
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (hη : 0 < η)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Icc (s.q r) (s.q (r + 1)))
    (haway : ∀ z ∈ S, η ≤ |z.2 - s.q r|)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let L := section5LocalLeftConstant β 535
  let a := (1 - t₀) ^ 2 / L
  let Sl := S ∩ {z | L * (z.2 - s.q r) ≤ 1 - t₀}
  let Sf := S ∩ {z | 1 - t₀ ≤ L * (z.2 - s.q r)}
  have hL : 0 < L := section5LocalLeftConstant_pos β 535 (by norm_num)
  have ha : 0 < a := div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) hL
  have hSl : IsCompact Sl := hS.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hSf : IsCompact Sf := hS.inter_right (isClosed_le continuous_const (by fun_prop))
  have hm : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega)
  obtain ⟨δf, hδf, Hf⟩ := exists_uniform_constrainedPhi_compact_far_right
    (Ω := Ω) s β h ε (r := r) hr0 hr hm hβ hL ht₀ hSf
      (fun z hz => ht z hz.1) (fun z hz => hu z hz.1)
      (fun z hz => hz.2) hmin hnear hfar
  let δl := a * η ^ 2
  have hδl : 0 < δl := mul_pos ha (sq_pos_of_pos hη)
  refine ⟨min δl δf, lt_min hδl hδf, ?_⟩
  intro z hz n hn sk hatt
  by_cases hloc : L * (z.2 - s.q r) ≤ 1 - t₀
  · letI : Nonempty (AT.ConstrainedPair n z.2) := by
      obtain ⟨σ, τ, hστ⟩ := hatt
      exact ⟨⟨(σ, τ), hστ⟩⟩
    have H := constrainedPhi_local_right_of_reduced_min hn s β h ε sk hβ hmass
      hqstrict hr0 hr (ht z hz) ht₀ (hu z hz) hmin hnear hsmall
      (by simpa only [L] using hloc)
    have hsq : η ^ 2 ≤ (z.2 - s.q r) ^ 2 := by
      exact (sq_le_sq).2 (by simpa [abs_of_pos hη] using haway z hz)
    have hgain : δl ≤ a * (z.2 - s.q r) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq ha.le
    have hminl : min δl δf ≤ δl := min_le_left _ _
    exact H.trans (by simpa only [a, L] using (show
      2 * guerraPsi s β h z.1 - a * (z.2 - s.q r) ^ 2 ≤
        2 * guerraPsi s β h z.1 - min δl δf by linarith))
  · have Hz := Hf z ⟨hz, le_of_not_ge hloc⟩ hn sk hatt
    exact Hz.trans (by linarith [min_le_right δl δf])

end SpinGlass.Targets
