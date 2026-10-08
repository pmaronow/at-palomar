module

public import Targets.Section5ScalarComparisonContinuity
public import Targets.Section5FarRight
public import Targets.Section5TerminalLambda

@[expose] public section

/-!
# Fixed scalar witnesses at far neighboring overlaps

The existing mass-or-lambda arguments choose an actual auxiliary mass and
lambda with strictly positive scalar comparison deficit. Those witnesses can
then be held fixed while time and overlap vary, using the continuity proved
separately. The construction never infers such a witness from a pointwise
finite-system pressure inequality.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A positive corrected left mass derivative gives a genuine admissible
decrease. Only the already proved actual mass derivative is used. -/
theorem exists_section5LeftMass_improvement {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hmpos : 0 < s.m (r - 1))
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hD : 0 < section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
      t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)) :
    ∃ m ∈ Set.Icc (s.m (r - 1) / 2) (s.m (r - 1)),
      2 * (section4T s β h r m (t * (β ^ 2 * (s.q r - u))) -
        section4T s β h r (s.m (r - 1)) (t * (β ^ 2 * (s.q r - u)))) -
      t * (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - u ^ 2)) < 0 := by
  let v := t * (β ^ 2 * (s.q r - u))
  let c := t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)
  let f := fun m => 2 * section4T s β h r m v - (m - s.m (r - 1)) * c
  have hv := section5SplitVariance_mem s β ht hu
  have hd : HasDerivAt f (section4U s β h r v - c) (s.m (r - 1)) := by
    convert ((hasDerivAt_section4T_mass_baseline s β h hr0 hr hv).const_mul 2).sub
      (((hasDerivAt_id (s.m (r - 1))).sub_const (s.m (r - 1))).mul_const c) using 1 <;>
      first | rfl | ring
  by_contra! H
  have hmin : ∀ m ∈ Set.Icc (s.m (r - 1) / 2) (s.m (r - 1)), f (s.m (r - 1)) ≤ f m := by
    intro m hm
    have HH := H m hm
    dsimp [f, v, c]
    nlinarith
  have Hnonpos := derivative_nonpos_of_min_at_right (by linarith : s.m (r - 1) / 2 < s.m (r - 1))
    hmin hd.hasDerivWithinAt
  exact (not_le_of_gt hD) Hnonpos

/-- A far-left point has an actual fixed admissible mass/lambda witness.
Its strictly positive continuous deficit is suitable for finite-cover reuse. -/
theorem exists_section5LeftComparison_witness_of_gap {k : ℕ}
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (s.q r - u) ^ 2) :
    ∃ m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ : ℝ,
      0 < section5LeftComparisonDeficit s β h r m ℓ (t, u) := by
  have hv := section5SplitVariance_mem s β ht hu
  by_cases hQ : section4TVarianceQ s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) = u
  · have hf := section4FirstVariation_lower_bound s β h ε hr0 hr hgap hu hmin hnear
    have HD := section4U_interpolation_slope_lower_bound_of_factor_eq s β h hr0 hr
      (hgap.trans_le (s.m_le_one hr)) hu ht hQ (by simpa only [neg_mul] using hf)
    have hD : 0 < section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
        t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2) := by linarith
    obtain ⟨m, hm, H⟩ := exists_section5LeftMass_improvement s β h hr0 hr hmpos ht hu hD
    refine ⟨m, ⟨hm.1, hm.2.trans hgap.le⟩, 0, ?_⟩
    have hm0 : 0 ≤ m := (div_nonneg hmpos.le (by norm_num)).trans hm.1
    unfold section5LeftComparisonDeficit section5LeftComparison
    rw [section5V_zero_eq_two_section4T s β h hr0 hr hm0 hv]
    rw [section4T_baseline s β h hr0 hr hv] at H
    simp only [zero_mul, sub_zero, guerraPsi]
    nlinarith
  · obtain ⟨ℓ, H⟩ := section5V_baseline_lambda_gain_Q s β h hr0 hr hv u
    refine ⟨s.m (r - 1), ⟨by linarith, hgap.le⟩, ℓ, ?_⟩
    have HP := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num : (0 : ℝ) < 2)
    unfold section5LeftComparisonDeficit section5LeftComparison guerraPsi
    simp only [sub_self, zero_mul, add_zero]
    linarith

/-- A far-right point has an actual fixed admissible mass/lambda witness.
The mass may exceed one, as allowed by the original right interpolation. -/
theorem exists_section5RightComparison_witness_of_gap {k : ℕ}
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (u - s.q r) ^ 2) :
    ∃ m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r), ∃ ℓ : ℝ,
      0 < section5RightComparisonDeficit s β h r m ℓ (t, u) := by
  have hv := section5RightSplitVariance_mem s β ht hu
  have hmpos : 0 < s.m r := (s.m_nonneg (by omega)).trans_lt hgap
  by_cases hQ : section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) = u
  · have hf := section4RightFirstVariation_upper_bound s β h ε hr0 hr hgap hu hmin hnear
    have HD := section4RightU_interpolation_slope_upper_bound_of_factor_eq s β h hr hmpos
      hu ht hQ hf
    have hD : section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
        t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) < 0 := by linarith
    obtain ⟨m, hm, H⟩ := exists_section5RightMass_improvement s β h hr hmpos ht hu hD
    refine ⟨m, ⟨hgap.le.trans hm.1, hm.2⟩, 0, ?_⟩
    have hm0 : 0 ≤ m := hmpos.le.trans hm.1
    unfold section5RightComparisonDeficit section5RightComparison
    rw [section5RightV_zero_eq_two_section4RightT s β h hr hm0 hv]
    rw [section4RightT_baseline s β h hr hv] at H
    simp only [zero_mul, sub_zero, guerraPsi]
    nlinarith
  · obtain ⟨ℓ, H⟩ := section5RightV_lambda_gain s β h hr
      (m := s.m r) ⟨hmpos.le, (s.m_le_one hr).trans (by norm_num)⟩
      (t * (β ^ 2 * (u - s.q r))) u
    rw [section5RightV_zero_baseline s β h hr hv,
      deriv_section5RightV_zero_eq_Q_all_levels s β h hr hv] at H
    refine ⟨s.m r, ⟨hgap.le, by linarith⟩, ℓ, ?_⟩
    have HP := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num : (0 : ℝ) < 2)
    unfold section5RightComparisonDeficit section5RightComparison guerraPsi
    simp only [sub_self, zero_mul, add_zero]
    linarith

end SpinGlass.Targets
