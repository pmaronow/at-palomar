module

public import Targets.Section5ScalarComparisonWitness
public import Targets.Section5LocalLeft
public import Targets.Section5RightUniform

@[expose] public section

/-!
# Scalar witnesses at physical neighboring endpoints

These lemmas keep the scalar witness, rather than only its transported
finite-volume consequence.  That witness is the datum needed by the
off-diagonal overlap interpolation near a physical breakpoint.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

/-- A nonzero left lambda slope gives a strict scalar comparison witness. -/
theorem exists_section5LeftComparison_witness_of_slope_ne
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hslope : section5LeftSlope s β h r t u ≠ 0) :
    ∃ ℓ, 0 < section5LeftComparisonDeficit s β h r (s.m (r - 1)) ℓ (t, u) := by
  obtain ⟨ℓ, H⟩ := section5V_baseline_lambda_gain_Q s β h hr0 hr
    (section5SplitVariance_mem s β ht hu) u
  refine ⟨ℓ, ?_⟩
  have hp : 0 < (section5LeftSlope s β h r t u) ^ 2 / 2 :=
    div_pos (sq_pos_of_ne_zero hslope) (by norm_num)
  unfold section5LeftComparisonDeficit section5LeftComparison guerraPsi
  simp only [sub_self, zero_mul, add_zero]
  change section5V s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) ℓ - ℓ * u ≤
    2 * parisiF s β (k + 2) h -
      (section5LeftSlope s β h r t u) ^ 2 / 2 at H
  linarith

/-- The local curvature estimate retains a strict scalar lambda witness at
the left physical-neighbor endpoint. -/
theorem exists_section5LeftComparison_witness_at_neighbor_of_curvature
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t t₀ L e : ℝ}
    (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hL : 0 ≤ L) (he : 0 ≤ e) (hq : s.q (r - 1) < s.q r)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    (hR : β ^ 2 * section4THessianSquare s β h r 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : L * β ^ 4 * (s.q r - s.q (r - 1)) ≤ (1 - t₀) / 4)
    (hLip : ∀ v ∈ Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤
          L * |v - w|) :
    ∃ ℓ, 0 < section5LeftComparisonDeficit s β h r (s.m (r - 1)) ℓ
      (t, s.q (r - 1)) := by
  have hs := section5LeftSlope_ge_local_of_endpoint_curvature s β h hr0 hr
    ht ht₀ hL he ⟨le_rfl, hq.le⟩ hQ hR he_small hu_small hLip
  have hcoef : 0 < (1 - t₀) / 2 * (s.q r - s.q (r - 1)) :=
    mul_pos (div_pos (sub_pos.mpr ht₀) (by norm_num)) (sub_pos.mpr hq)
  apply exists_section5LeftComparison_witness_of_slope_ne s β h hr0 hr
    ⟨ht.1, ht.2.trans ht₀.le⟩ ⟨le_rfl, hq.le⟩
  linarith

/-- The reduced minimizing-scheme hypotheses provide the local endpoint
witness with the project's uniform Hessian constant. -/
theorem exists_section5LeftComparison_witness_at_neighbor_local
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hq : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β 535 *
      (s.q r - s.q (r - 1)) ≤ 1 - t₀) :
    ∃ ℓ, 0 < section5LeftComparisonDeficit s β h r (s.m (r - 1)) ℓ
      (t, s.q (r - 1)) := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hA : 0 ≤ β ^ 6 * 535 / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  let e := 4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) /
    β ^ 2 * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hA) hB.le) hη
  have hc := section5LocalLeftConstant_bounds β 535 (by norm_num : (0 : ℝ) ≤ 535)
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    have he4 : 16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) /
        β ^ 2 * ε ^ (1 / 6 : ℝ) = 4 * e := by
      dsimp [e]
      ring
    rw [he4] at H
    nlinarith only [H, hsmall]
  have hu_small : 535 * β ^ 4 * (s.q r - s.q (r - 1)) ≤
      (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hq.le)
    nlinarith only [H, hlocal]
  have Hcurv :=
    section4FirstVariation_curvature_bound_of_hessian_lipschitz_all_levels
      s β h ε hr0 hr hβ hm hq hright hmin hnear
      (by norm_num : (0 : ℝ) ≤ 535)
      (fun v hv w hw => section4THessianSquare_lipschitz_uniform
        s β h hr0 hr hv hw)
  simp only [section4FirstVariationD2, sub_self, mul_zero] at Hcurv
  have hR : β ^ 2 * section4THessianSquare s β h r 0 ≤ 1 + e := by
    have H : β ^ 2 * section4THessianSquare s β h r 0 - 1 ≤
        (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) *
          ε ^ (1 / 6 : ℝ)) / β ^ 2 := by
      apply (le_div_iff₀ hB).mpr
      nlinarith only [Hcurv]
    have heq : (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) *
        ε ^ (1 / 6 : ℝ)) / β ^ 2 = e := by
      dsimp [e]
      ring
    rw [heq] at H
    linarith
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h hr0 hr hβ hm (Or.inl hq) hright hmin
  exact exists_section5LeftComparison_witness_at_neighbor_of_curvature
    s β h hr0 hr ht ht₀ (by norm_num) he hq hQ hR he_small hu_small
      (fun v hv w hw => section4THessianSquare_lipschitz_uniform
        s β h hr0 hr hv hw)

/-- Local curvature and the far mass variation together give an endpoint
witness with no size assumption on the physical overlap gap. -/
theorem exists_section5LeftComparison_witness_at_physical_neighbor
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ,
      0 < section5LeftComparisonDeficit s β h r m ℓ
        (t, s.q (r - 1)) := by
  have hm : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r from by omega)] using
      hmass (r - 1) (by omega)
  by_cases hlocal : section5LocalLeftConstant β 535 *
      (s.q r - s.q (r - 1)) ≤ 1 - t₀
  · obtain ⟨ℓ, Hℓ⟩ := exists_section5LeftComparison_witness_at_neighbor_local
      s β h ε (show 1 ≤ r by omega) hr hβ hm hq hright ht ht₀
      hmin hnear hsmall hlocal
    exact ⟨s.m (r - 1),
      ⟨by linarith [s.m_nonneg (p := r - 1) (by omega)], hm.le⟩, ℓ, Hℓ⟩
  · have hL : 0 < section5LocalLeftConstant β 535 :=
      section5LocalLeftConstant_pos β 535 (by norm_num)
    have hfarpoint : 1 - t₀ ≤ section5LocalLeftConstant β 535 *
        (s.q r - s.q (r - 1)) := (lt_of_not_ge hlocal).le
    have hmpos : 0 < s.m (r - 1) := by
      have H := hmass 0 (by omega : 0 ≤ k)
      have Hmono := s.m_mono' (r - 1) (by omega) 1 (by omega)
      simpa only [s.m_zero] using H.trans_le Hmono
    exact exists_section5LeftComparison_witness_of_gap s β h ε
      (show 1 ≤ r by omega) hr hmpos hm
      ⟨ht.1, ht.2.trans ht₀.le⟩ ⟨le_rfl, hq.le⟩ hmin hnear
      (section5FarLeft_smallness hβ hL ht₀ ht.2 hfarpoint hfar)

end SpinGlass.Targets
