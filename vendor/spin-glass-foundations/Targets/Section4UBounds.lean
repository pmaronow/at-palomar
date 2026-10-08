module

public import Targets.Section4FirstVariation

@[expose] public section

/-!
# Closed-interval bounds for Talagrand's actual U

The actual baseline mass derivative is obtained as a right-hand difference
quotient. The already proved variance comparison for T then gives monotonicity
and the unit Lipschitz bound for U. No mixed derivative or derivative of U is
assumed. The argument requires the baseline mass to be strictly less than one,
as supplied by the strict-mass reduction on the critical path.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Increasing the variance increases the actual `U` by at most that increase.
The mass quotient approaches the baseline from above, not through an assumed
mixed derivative. Both variance endpoints are included. -/
theorem section4U_sub_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    section4U s β h r w - section4U s β h r v ∈ Set.Icc 0 (w - v) := by
  have hd := (hasDerivAt_section4T_mass_baseline s β h hr0 hr hw).sub
    (hasDerivAt_section4T_mass_baseline s β h hr0 hr hv)
  have hlim := hd.tendsto_slope_zero_right
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ • ((section4T s β h r (s.m (r - 1) + t) w - section4T s β h r (s.m (r - 1) + t) v) -
        (section4T s β h r (s.m (r - 1)) w - section4T s β h r (s.m (r - 1)) v)) ∈
        Set.Icc 0 ((w - v) / 2) := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hm)] with t ht
    have hmt : s.m (r - 1) + t ∈ Set.Icc 0 1 := by
      constructor <;> linarith [s.m_nonneg (p := r - 1) (by omega), ht.1, ht.2]
    have hge : s.m (r - 1) ≤ s.m (r - 1) + t := by linarith [ht.1]
    have hmono := monotoneOn_section4T s β h hr0 hr hmt hge hv hw hvw
    have hdist := section4T_variance_dist_le s β h hr0 hr hmt hge hw hv
    rw [section4T_baseline s β h hr0 hr hw, section4T_baseline s β h hr0 hr hv,
      sub_self, sub_zero, smul_eq_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr hmono), ?_⟩
    rw [← div_eq_inv_mul]
    apply (div_le_iff₀ ht.1).mpr
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hvw)] at hdist
    nlinarith [hdist]
  have H : section4U s β h r w / 2 - section4U s β h r v / 2 ∈ Set.Icc 0 ((w - v) / 2) :=
    isClosed_Icc.mem_of_tendsto hlim hb
  constructor <;> linarith [H.1, H.2]

/-- The actual U is monotone on the full closed split interval. -/
theorem monotoneOn_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) :
    MonotoneOn (section4U s β h r) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  intro v hv w hw hvw
  exact sub_nonneg.mp (section4U_sub_mem_Icc s β h hr0 hr hm hv hw hvw).1

/-- Talagrand's actual U has Lipschitz constant one, independent of level count. -/
theorem section4U_dist_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4U s β h r v - section4U s β h r w| ≤ |v - w| := by
  rcases le_total v w with hvw | hwv
  · have H := section4U_sub_mem_Icc s β h hr0 hr hm hv hw hvw
    rw [abs_sub_comm (section4U s β h r v), abs_of_nonneg H.1,
      abs_sub_comm v, abs_of_nonneg (sub_nonneg.mpr hvw)]
    exact H.2
  · have H := section4U_sub_mem_Icc s β h hr0 hr hm hw hv hwv
    rw [abs_of_nonneg H.1, abs_of_nonneg (sub_nonneg.mpr hwv)]
    exact H.2

theorem lipschitzOnWith_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) :
    LipschitzOnWith 1 (section4U s β h r) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    section4U_dist_le s β h hr0 hr hm hv hw

/-- Continuity is now proved for the actual U, not hypothesized as regularity. -/
theorem continuousOn_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) :
    ContinuousOn (section4U s β h r) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :=
  (lipschitzOnWith_section4U s β h hr0 hr hm).continuousOn

/-- Normalization `U(0)=0` and the closed-interval comparison give `0≤U(v)≤v`. -/
theorem section4U_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4U s β h r v ∈ Set.Icc 0 v := by
  have H := section4U_sub_mem_Icc s β h hr0 hr hm (v := 0)
    ⟨le_refl 0, hv.1.trans hv.2⟩ hv hv.1
  simpa only [section4U_zero_variance s β h hr0 hr, sub_zero] using H

private theorem section4FirstVariation_dist_le_of_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u w : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc (s.q (r - 1)) (s.q r)) (huw : u ≤ w) :
    |section4FirstVariation s β h r u - section4FirstVariation s β h r w| ≤
      β ^ 2 / 2 * (w - u) := by
  have hvu := section5SplitVariance_mem s β (t := 1) (by constructor <;> norm_num) hu
  have hvw := section5SplitVariance_mem s β (t := 1) (by constructor <;> norm_num) hw
  simp only [one_mul] at hvu hvw
  have hvle : β ^ 2 * (s.q r - w) ≤ β ^ 2 * (s.q r - u) := by
    nlinarith [sq_nonneg β]
  have H := section4U_sub_mem_Icc s β h hr0 hr hm hvw hvu hvle
  have hu0 : 0 ≤ u := (s.q_nonneg (p := r - 1) (by omega)).trans hu.1
  have hw1 : w ≤ 1 := hw.2.trans (s.q_le_one (by omega))
  have hsq0 : 0 ≤ w ^ 2 - u ^ 2 := by nlinarith
  have hsq1 : w ^ 2 - u ^ 2 ≤ 2 * (w - u) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huw) (show 0 ≤ 2 - (w + u) by linarith)]
  have hP0 := mul_nonneg (sq_nonneg β) hsq0
  have hP1 := mul_le_mul_of_nonneg_left hsq1 (sq_nonneg β)
  rw [abs_le]
  constructor <;> dsimp only [section4FirstVariation] <;> nlinarith [H.1, H.2]

/-- The actual first variation is Lipschitz in overlap with constant `β²/2`.
This follows from finite differences; no derivative of U is asserted. -/
theorem section4FirstVariation_dist_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u w : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariation s β h r u - section4FirstVariation s β h r w| ≤ β ^ 2 / 2 * |u - w| := by
  rcases le_total u w with huw | hwu
  · rw [abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huw)]
    exact section4FirstVariation_dist_le_of_le s β h hr0 hr hm hu hw huw
  · rw [abs_sub_comm (section4FirstVariation s β h r u), abs_of_nonneg (sub_nonneg.mpr hwu)]
    exact section4FirstVariation_dist_le_of_le s β h hr0 hr hm hw hu hwu

/-- Continuity of the actual first variation on its full overlap interval. -/
theorem continuousOn_section4FirstVariation {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) :
    ContinuousOn (section4FirstVariation s β h r) (Set.Icc (s.q (r - 1)) (s.q r)) := by
  have H : LipschitzOnWith (Real.toNNReal (β ^ 2 / 2)) (section4FirstVariation s β h r)
      (Set.Icc (s.q (r - 1)) (s.q r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    simpa only [Real.dist_eq,
      Real.coe_toNNReal _ (show 0 ≤ β ^ 2 / 2 by positivity)] using
      section4FirstVariation_dist_le s β h hr0 hr hm hu hw
  exact H.continuousOn

/-- The known zero at `q_r` gives an endpoint-safe bound on the first variation. -/
theorem abs_section4FirstVariation_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariation s β h r u| ≤ β ^ 2 / 2 * (s.q r - u) := by
  have H := section4FirstVariation_dist_le s β h hr0 hr hm hu ⟨hu.1.trans hu.2, le_rfl⟩
  simpa only [section4FirstVariation_at_upper_overlap s β h hr0 hr, sub_zero,
    abs_sub_comm u (s.q r), abs_of_nonneg (sub_nonneg.mpr hu.2)] using H

end SpinGlass.Targets
