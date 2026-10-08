module

public import Targets.Section5RightOffDiagonalInterpolation
public import Targets.Section5LocalRight
public import Targets.TalagrandRightZero
public import Targets.Section5RightUniform
public import Targets.Section5InterleavedRightCompact
public import Targets.Section4StationarityReduction
public import Targets.Section5PositiveAwayOuterPieces
public import Targets.Section4ZeroOverlapCurvature
public import Targets.Section5FiniteGapCover
public import Targets.Section5OutsideIntervals
public import Targets.Section5PositiveAwayTerminalTube

@[expose] public section

/-!
# Right physical-neighbor compact transport

This is the compact-continuity adapter for the right off-diagonal
interpolation.  Unlike the far-neighbor specialization, it takes the
positive scalar witness at the endpoint as an explicit input.  This keeps
the transport argument independent of how the endpoint witness was made
(far mass variation or local lambda curvature).
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/- The local curvature branch supplies the endpoint scalar witness directly.
   Keeping this adapter separate from the tube theorem makes the latter
   reusable for either branch of the physical-gap split. -/
theorem exists_section5RightOffDiagonalComparison_witness_at_physical_neighbor_of_curvature
    (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr : r ≤ k + 1) (hq : s.q r < s.q (r + 1))
    {t t₀ e : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : 535 * β ^ 4 * (s.q (r + 1) - s.q r) ≤ (1 - t₀) / 4)
    (hQ : section4RightQ s β h r 0 = s.q r)
    (hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e) :
    ∃ ℓ : ℝ,
      0 < section5RightOffDiagonalComparisonDeficit s β h r (s.m r) ℓ
        (t, (s.q (r + 1), s.q (r + 1))) := by
  have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hv : t * (β ^ 2 * (s.q (r + 1) - s.q r)) ∈
      Set.Icc (0 : ℝ) (β ^ 2 * (s.q (r + 1) - s.q r)) := by
    exact section5RightSplitVariance_mem s β ht1 ⟨hq.le, le_rfl⟩
  have hslope := section5RightSlope_le_local_of_endpoint_curvature s β h hr
    ht ht₀ he ⟨hq.le, le_rfl⟩ hQ hR he_small hu_small
  obtain ⟨ℓ, hℓ⟩ := section5RightV_lambda_gain s β h hr
    (m := s.m r) ⟨s.m_nonneg hr, (s.m_le_one hr).trans (by norm_num)⟩
    (t * (β ^ 2 * (s.q (r + 1) - s.q r))) (s.q (r + 1))
  rw [section5RightV_zero_baseline s β h hr hv,
    deriv_section5RightV_zero_eq_Q_all_levels s β h hr hv] at hℓ
  refine ⟨ℓ, ?_⟩
  have hsquare : 0 < (section5RightSlope s β h r t (s.q (r + 1))) ^ 2 := by
    have hgap : 0 < s.q (r + 1) - s.q r := sub_pos.mpr hq
    have hcoef : 0 < (1 - t₀) / 2 := by linarith
    have hneg : section5RightSlope s β h r t (s.q (r + 1)) < 0 := by
      have Hneg : -(1 - t₀) / 2 * (s.q (r + 1) - s.q r) < 0 := by
        nlinarith [mul_pos hcoef hgap]
      exact lt_of_le_of_lt hslope Hneg
    exact sq_pos_of_neg hneg
  have Hdef : 0 < section5RightComparisonDeficit s β h r (s.m r) ℓ
      (t, s.q (r + 1)) := by
    unfold section5RightComparisonDeficit section5RightComparison guerraPsi
    dsimp [section5RightSlope] at hsquare
    nlinarith [hℓ, hsquare]
  simpa only [section5RightOffDiagonalComparisonDeficit_diag] using Hdef

set_option maxHeartbeats 1200000 in
theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_of_boundary
    (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hq : s.q r < s.q (r + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∃ m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r), ∃ ℓ : ℝ,
        0 < section5RightOffDiagonalComparisonDeficit s β h r m ℓ
          (t, (s.q (r + 1), s.q (r + 1)))) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q (r + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let I : Type :=
    {m : ℝ // m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r)} × ℝ
  let f : I → (ℝ × ℝ) → ℝ := fun i z =>
    section5RightTrialDeficit s β h r i.1.1 i.2
      (z.1, (z.2, s.q (r + 1)))
  have hf : ∀ i : I, Continuous (f i) := by
    intro i
    have H := continuous_section5RightTrialDeficit s β h hr
      ((s.m_nonneg (by omega)).trans i.1.2.1) i.2
    exact H.comp (by fun_prop)
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      ∃ i : I, 0 < f i (t, s.q (r + 1)) := by
    intro t ht
    obtain ⟨m, hm, ℓ, H⟩ := hboundary t ht
    refine ⟨(⟨m, hm⟩, ℓ), ?_⟩
    change 0 < section5RightTrialDeficit s β h r m ℓ
      (t, (s.q (r + 1), s.q (r + 1)))
    rw [section5RightTrialDeficit_diag]
    exact H
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Set.Icc (0 : ℝ) t₀)
      isCompact_Icc f hf (s.q (r + 1)) hpos
  let C : ℝ := β ^ 2 / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let ρ : ℝ := min 1 (min ρ₀ (δ₀ / (4 * (C + 1))))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    refine lt_min (by norm_num) (lt_min hρ₀ ?_)
    exact div_pos hδ₀ (by positivity)
  have hρle1 : ρ ≤ 1 := min_le_left _ _
  have hρle0 : ρ ≤ ρ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρleδ : ρ ≤ δ₀ / (4 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, δ₀ / 2, by positivity, ?_⟩
  intro t ht u hu htu n hn sk hatt
  obtain ⟨i, hi⟩ := Htube t ht u (htu.trans hρle0)
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have hm := i.1.2
  have Hactual := section5RightInterpolationOffDiagonal_endpoint_bound hn s β h sk
    hr0 hr (m := i.1.1) (t := t) (u := u) (v := s.q (r + 1))
      (ℓ := i.2) hm ⟨ht.1, ht.2.trans ht₀.le⟩ ⟨hq.le, le_rfl⟩
  have hsq : (u - s.q (r + 1)) ^ 2 ≤ ρ := by
    rw [← sq_abs]
    have hmul := mul_self_le_mul_self (abs_nonneg (u - s.q (r + 1))) htu
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
    nlinarith
  have hCρ : C * (u - s.q (r + 1)) ^ 2 ≤ δ₀ / 4 := by
    have hden : 0 < C + 1 := by linarith
    have hmul : C * ρ ≤ C * (δ₀ / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hρleδ hC
    have hfrac : C * (δ₀ / (4 * (C + 1))) ≤ δ₀ / 4 := by
      field_simp [ne_of_gt hden]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hsq hC).trans (hmul.trans hfrac)
  have htime : t * C * (u - s.q (r + 1)) ^ 2 ≤ δ₀ / 4 := by
    have h₁ := mul_le_mul_of_nonneg_right hCρ ht.1
    have h₂ : t * (δ₀ / 4) ≤ δ₀ / 4 := by
      nlinarith [ht.2, hδ₀]
    nlinarith
  dsimp [f] at hi
  dsimp [section5RightTrialDeficit] at hi
  dsimp [section5RightTrialComparison] at hi
  dsimp [C] at htime
  linarith

theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_of_curvature
    (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hq : s.q r < s.q (r + 1))
    {t₀ e : ℝ} (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : 535 * β ^ 4 * (s.q (r + 1) - s.q r) ≤ (1 - t₀) / 4)
    (hQ : section4RightQ s β h r 0 = s.q r)
    (hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q (r + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  apply exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_of_boundary
    s β h hr0 hr hq ht₀
  intro t ht
  obtain ⟨ℓ, hℓ⟩ :=
    exists_section5RightOffDiagonalComparison_witness_at_physical_neighbor_of_curvature
      s β h hr hq ht ht₀ he he_small hu_small hQ hR
  refine ⟨s.m r, ?_, ℓ, hℓ⟩
  constructor
  · exact s.m_mono' r (by omega) (r - 1) (by omega)
  · nlinarith [s.m_nonneg (by omega)]

/- The fully discharged local wrapper.  Its hypotheses are the same
   near-minimizer and reduced-scheme data used by the existing uniform local
   estimate; the endpoint curvature data are reconstructed here and fed to
   the compact off-diagonal transport above. -/
theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_local
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hq : s.q r < s.q (r + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β 535 *
      (s.q (r + 1) - s.q r) ≤ 1 - t₀) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q (r + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hA : 0 ≤ β ^ 6 * 535 / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  have hc : 32 ≤ section5LocalLeftConstant β 535 ∧
      4 * 535 * β ^ 4 ≤ section5LocalLeftConstant β 535 ∧
      16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 ≤
        section5LocalLeftConstant β 535 := by
    have h₁ : 0 ≤ 4 * 535 * β ^ 4 := by positivity
    have h₂ : 0 ≤ 16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hA) hB.le
    unfold section5LocalLeftConstant
    constructor
    · linarith
    constructor <;> linarith
  let e := 4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 *
    ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hA) hB.le) hη
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    have he4 : 16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 *
        ε ^ (1 / 6 : ℝ) = 4 * e := by dsimp [e]; ring
    rw [he4] at H
    linarith
  have hu_small : 535 * β ^ 4 * (s.q (r + 1) - s.q r) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hq.le)
    nlinarith only [H, hlocal]
  have hQ : section4RightQ s β h r 0 = s.q r := by
    rw [section4RightQ, sub_zero,
      section4TVarianceQ_neighbor_full_eq_zero_all_levels s β h hr0 hr]
    exact section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 (by omega)
      hβ hmass (Or.inl hleft) hright hmin
  have Hcurv := section4FirstVariation_curvature_bound_uniform s β h ε hr0 (by omega)
    hβ hmass hleft hright hmin hnear
  simp only [section4FirstVariationD2, sub_self, mul_zero] at Hcurv
  have hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e := by
    rw [section4RightR, sub_zero,
      section4THessianSquare_neighbor_full_eq_zero_all_levels s β h hr0 hr]
    have H : β ^ 2 * section4THessianSquare s β h r 0 - 1 ≤
        (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) *
          ε ^ (1 / 6 : ℝ)) / β ^ 2 := by
      apply (le_div_iff₀ hB).mpr
      nlinarith only [Hcurv]
    have heq : (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) *
        ε ^ (1 / 6 : ℝ)) / β ^ 2 = e := by dsimp [e]; ring
    rw [heq] at H
    linarith
  exact exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_of_curvature
    s β h hr0 hr hq ht₀ he he_small hu_small hQ hR

/- The two cases of the physical-neighbor argument.  The same constant
   `section5LocalLeftConstant β 535` controls both the local curvature tube
   and the complementary far-overlap witness. -/
theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_unconditional
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hq : s.q r < s.q (r + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfarSmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q (r + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let L : ℝ := section5LocalLeftConstant β 535
  have hL : 0 < L := by
    dsimp [L]
    exact section5LocalLeftConstant_pos β 535 (by norm_num)
  by_cases hlocal : L * (s.q (r + 1) - s.q r) ≤ 1 - t₀
  · have hsmall' : L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀ := by
      simpa only [L] using hsmall
    have hlocal' : L * (s.q (r + 1) - s.q r) ≤ 1 - t₀ := hlocal
    exact exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_local
      s β h ε hr0 hr hβ hmass hleft hright hq ht₀ hmin hnear hsmall' hlocal'
  · have hfar : 1 - t₀ ≤ L * (s.q (r + 1) - s.q r) := by
      exact le_of_not_ge hlocal
    have hsmall' : section5FarLeftBound β * Real.sqrt ε ≤
        (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L) ^ 2 := by
      simpa only [L] using hfarSmall
    exact exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal
      s β h ε hr0 hr hβ hmass hq hL ht₀ hmin hnear hfar hsmall'

/- The first complete right-hand band adapter: the physical-neighbor tube is
   glued to the compact open-endpoint outside-trial rectangle. -/
theorem exists_uniform_constrainedPhi_immediate_right_band
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hrk : r + 1 ≤ k) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (_hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (s.q r) (s.q (r + 2)),
      η ≤ |u - s.q r| →
      (|u - s.q (r + 1)| ≤ ρ ∨ s.q (r + 1) + ρ ≤ u) →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hleft : s.q (r - 1) < s.q r := by
    have hp0 : 1 ≤ r - 1 := by omega
    have hpk : r - 1 ≤ k := by omega
    have H := hqstrict (r - 1) hp0 hpk
    have hidx : r - 1 + 1 = r := by omega
    rw [hidx] at H
    exact H
  have hq : s.q r < s.q (r + 1) := hqstrict r (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := Or.inl hq
  have hmassr : s.m (r - 1) < s.m r := by
    have hpk : r - 1 ≤ k := by omega
    have H := hmass (r - 1) hpk
    have hidx : r - 1 + 1 = r := by omega
    rw [hidx] at H
    exact H
  have hqnext : s.q (r + 1) < s.q (r + 2) := hqstrict (r + 1) (by omega) (by omega)
  have hmassFin : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) (by omega) hβ hmassr (Or.inl hleft) hright hmin
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_unconditional
      (Ω := Ω) s β h ε (r := r) (by omega) (by omega) hβ hmassr hleft hright hq
      ht₀ hmin hnear hsmall hfar
  let ρ : ℝ := min ρ₀ 1 / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_min hρ₀ (by norm_num)) (by norm_num)
  have hρle : ρ ≤ ρ₀ := by
    dsimp [ρ]
    nlinarith [min_le_left ρ₀ 1]
  let S : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) t₀ ×ˢ Set.Icc (s.q (r + 1) + ρ) (s.q (r + 2))
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ₁, hδ₁, Houtside⟩ :=
    exists_uniform_constrainedPhi_right_outside_trial (Ω := Ω) s β h
      (r := r) (j := r + 2) hβ (by omega) (by omega) (by omega) (by omega)
      (by omega) hmassFin hq hQ ht₀ hS
      (fun z hz => hz.1)
      (fun z hz => by
        have hstrict : s.q (r + 1) < s.q (r + 1) + ρ := by linarith [hρ]
        have hidx : r + 2 - 1 = r + 1 := by omega
        rw [hidx]
        exact ⟨hstrict.trans_le hz.2.1, hz.2.2⟩)
  refine ⟨ρ, hρ, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht u hu haway hcases n hn sk hatt
  rcases hcases with hnearTube | hout
  · have hu' : u ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · exact (by norm_num : (-1 : ℝ) ≤ 0) |>.trans
          ((s.q_nonneg (p := r) (by omega)).trans hu.1)
      · exact hu.2.trans (s.q_le_one (p := r + 2) (by omega))
    have H := Htube t ht u hu' (hnearTube.trans hρle) hn sk hatt
    exact H.trans (by linarith [min_le_left δ₀ δ₁])
  · have huz : (t, u) ∈ S := by
      refine ⟨ht, ?_⟩
      exact ⟨hout, hu.2⟩
    have H := Houtside (t, u) huz hn sk hatt
    exact H.trans (by linarith [min_le_right δ₀ δ₁])

/- The terminal-level outer side.  At `r=k` there is no nonterminal trial
   interval to the right, so the physical tube is glued directly to the
   padded terminal tail. -/
theorem exists_uniform_constrainedPhi_right_outer_and_terminal_at_last
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hkr : 2 ≤ k)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ η : ℝ} (ht₀ : t₀ < 1) (_hη : 0 < η)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (s.q (k + 1)) 1,
      η ≤ |u - s.q k| → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U 2 t u ≤
        2 * guerraPsi s β h t - δ := by
  have hleft : s.q (k - 1) < s.q k := by
    have hp0 : 1 ≤ k - 1 := by omega
    have hpk : k - 1 ≤ k := by omega
    have H := hqstrict (k - 1) hp0 hpk
    have hidx : k - 1 + 1 = k := by omega
    rw [hidx] at H
    exact H
  have hq : s.q k < s.q (k + 1) := hqstrict k (by omega) (by omega)
  have hright : s.q k < s.q (k + 1) ∨ s.q k = 1 := Or.inl hq
  have hmassk : s.m (k - 1) < s.m k := by
    have hpk : k - 1 ≤ k := by omega
    have H := hmass (k - 1) hpk
    have hidx : k - 1 + 1 = k := by omega
    rw [hidx] at H
    exact H
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (by omega) (by omega) hβ hmassk (Or.inl hleft) hright hmin
  obtain ⟨ρ₀, hρ₀, δ₀, hδ₀, Htube⟩ :=
    exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_unconditional
      (Ω := Ω) s β h ε (r := k) (by omega) (by omega) hβ hmassk hleft hright hq
      ht₀ hmin hnear hsmall hfar
  let ρ : ℝ := min ρ₀ 1 / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_min hρ₀ (by norm_num)) (by norm_num)
  have hρle : ρ ≤ ρ₀ := by
    dsimp [ρ]
    nlinarith [min_le_left ρ₀ 1]
  let a : ℝ := s.q (k + 1) + ρ
  by_cases htail : a ≤ 1
  · let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) t₀ ×ˢ Set.Icc a 1
    have hS : IsCompact S := by
      dsimp [S]
      exact isCompact_Icc.prod isCompact_Icc
    obtain ⟨δ₁, hδ₁, Htail⟩ :=
      exists_uniform_constrainedPhi_positive_terminal_outer_piece
        (Ω := Ω) s β h hβ (by omega) (by omega)
        (hmass k (by omega)) hq hQ ht₀ (by
          dsimp [a]
          linarith [hρ]) htail
    refine ⟨ρ, hρ, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
    intro t ht u hu haway n hn sk hatt
    by_cases hnear' : |u - s.q (k + 1)| ≤ ρ
    · have hu' : u ∈ Set.Icc (-1 : ℝ) 1 := by
        exact ⟨by linarith [s.q_nonneg (p := k + 1) (by omega), hu.1], hu.2⟩
      have H := Htube t ht u hu' (hnear'.trans hρle) hn sk hatt
      simpa only [show k + 2 - k = 2 by omega] using
        H.trans (by linarith [min_le_left δ₀ δ₁])
    · have hlow : a ≤ u := by
        dsimp [a]
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hnear'
        linarith
      have hz : (t, u) ∈ S := by
        simpa only [S, Set.mem_prod, Prod.fst, Prod.snd] using
          (show t ∈ Set.Icc (0 : ℝ) t₀ ∧ u ∈ Set.Icc a 1 from ⟨ht, ⟨hlow, hu.2⟩⟩)
      have H := Htail (t, u) hz hn sk hatt
      simpa only [Prod.fst, Prod.snd, show k + 2 - k = 2 by omega] using
        H.trans (by linarith [min_le_right δ₀ δ₁])
  · refine ⟨ρ, hρ, δ₀, hδ₀, ?_⟩
    intro t ht u hu haway n hn sk hatt
    have hnear' : |u - s.q (k + 1)| ≤ ρ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      dsimp [a] at htail
      by_contra hnnear
      have hgt : ρ < u - s.q (k + 1) := lt_of_not_ge hnnear
      linarith [hu.2, htail]
    have hu' : u ∈ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨by linarith [s.q_nonneg (p := k + 1) (by omega), hu.1], hu.2⟩
    simpa only [show k + 2 - k = 2 by omega] using
      Htube t ht u hu' (hnear'.trans hρle) hn sk hatt

/- Initial zero-overlap endpoint, needed when the last physical level is also
   the first one (`k=1`).  Its curvature data come from the one-sided initial
   boundary lemma rather than from a positive left breakpoint. -/
theorem exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_initial_zero_unconditional
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hk : 1 ≤ k) (hβ : β ≠ 0) (hq0 : s.q 1 = 0)
    (hmass0 : s.m 0 < s.m 1) (hq : s.q 1 < s.q 2)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfarSmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ) t₀, ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      |u - s.q 2| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  let L : ℝ := section5LocalLeftConstant β 535
  have hL : 0 < L := by
    dsimp [L]
    exact section5LocalLeftConstant_pos β 535 (by norm_num)
  have hlocalQ : section4RightQ s β h 1 0 = s.q 1 := by
    rw [section4RightQ, sub_zero,
      section4TVarianceQ_neighbor_full_eq_zero_all_levels s β h (by omega) (by omega)]
    exact section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h (by omega) (by omega)
      hβ hmass0 (Or.inr hq0) (Or.inl hq) hmin
  have hlocalR : β ^ 2 * section4RightR s β h 1 0 ≤ 1 + 0 := by
    rw [section4RightR, sub_zero,
      section4THessianSquare_neighbor_full_eq_zero_all_levels s β h (by omega) (by omega),
      add_zero]
    exact section4THessianSquare_initial_zero_le_of_min s β h hβ hq0 hmass0
      (by simpa [hq0] using hq) hmin
  have hc := section5LocalLeftConstant_bounds β 535 (by norm_num)
  by_cases hlocal : L * (s.q 2 - s.q 1) ≤ 1 - t₀
  · obtain ⟨ρ, hρ, δ, hδ, H⟩ :=
      exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal_of_curvature
        (Ω := Ω) s β h (r := 1) (by omega) (by omega) hq
        ht₀ (le_refl 0) (by linarith) (by
          have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hq.le)
          rw [hq0] at H ⊢
          have ht0nonneg : 0 ≤ 1 - t₀ := by linarith
          nlinarith [hlocal]) hlocalQ hlocalR
    simpa only [show k + 2 - 1 = k + 1 by omega] using ⟨ρ, hρ, δ, hδ, H⟩

  · have hfar : 1 - t₀ ≤ L * (s.q 2 - s.q 1) := le_of_not_ge hlocal
    have hsmall' : section5FarLeftBound β * Real.sqrt ε ≤
        (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L) ^ 2 := by
      simpa only [L] using hfarSmall
    obtain ⟨ρ, hρ, δ, hδ, H⟩ :=
      exists_uniform_constrainedPhi_right_physical_neighbor_offDiagonal
        (Ω := Ω) (k := k) s β h ε (r := 1) (by omega) (by omega) hβ hmass0 hq
          hL ht₀ hmin hnear hfar hsmall'
    simpa only [show k + 2 - 1 = k + 1 by omega] using ⟨ρ, hρ, δ, hδ, H⟩

end SpinGlass.Targets
