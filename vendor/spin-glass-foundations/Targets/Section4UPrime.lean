module

public import Targets.Section4VarianceFactorContinuity
public import Targets.Section4UBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The actual first variance derivative of Talagrand's U

Continuity of the normalized squared-slope factor permits a right mass limit
in the already proved integral identity. This proves U'=Q without assuming
interchange of mixed derivatives. The baseline mass is strictly below one.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The normalized factor's integral is continuous in mass, including baseline
mass zero. Its proved unit bound supplies domination on the finite interval. -/
theorem continuousOn_integral_section4TVarianceQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    ContinuousOn (fun m => ∫ z in v..w, section4TVarianceQ s β h r m z) (Set.Icc 0 1) := by
  simp_rw [intervalIntegral.integral_of_le hvw]
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro m hm
    exact (intervalIntegrable_section4TVarianceQ_closed s β h hr0 hr hm hv hw).1.aestronglyMeasurable
  · intro m hm
    filter_upwards with z
    have H := section4TVarianceQ_mem_Icc s β h r hm z
    simpa only [Real.norm_eq_abs, abs_of_nonneg H.1] using H.2
  · exact integrable_const 1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact continuousOn_section4TVarianceQ_mass s β h hr0 hr
      ⟨hv.1.trans hz.1.le, hz.2.trans hw.2⟩

/-- The actual U difference is the integral of the baseline squared-slope factor.
This is a mass difference-quotient limit, not an assumed mixed identity. -/
theorem section4U_sub_eq_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    section4U s β h r w - section4U s β h r v =
      ∫ z in v..w, section4TVarianceQ s β h r (s.m (r - 1)) z := by
  have hb0 := s.m_nonneg (p := r - 1) (by omega)
  have hbase : s.m (r - 1) ∈ Set.Icc 0 1 := ⟨hb0, hm.le⟩
  have hd := (hasDerivAt_section4T_mass_baseline s β h hr0 hr hw).sub
    (hasDerivAt_section4T_mass_baseline s β h hr0 hr hv)
  have hlim := hd.tendsto_slope_zero_right
  have htend : Tendsto (fun t : ℝ => s.m (r - 1) + t)
      (𝓝[>] 0) (𝓝[Set.Icc 0 1] (s.m (r - 1))) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using
        (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun t : ℝ => s.m (r - 1) + t) (𝓝[>] 0) (𝓝 (s.m (r - 1) + 0)))
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hm)] with t ht
      constructor <;> linarith [ht.1, ht.2]
  have hI := ((continuousOn_integral_section4TVarianceQ s β h hr0 hr hv hw hvw)
    (s.m (r - 1)) hbase).tendsto.comp htend
  have hIhalf := hI.div_const 2
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ • ((section4T s β h r (s.m (r - 1) + t) w -
          section4T s β h r (s.m (r - 1) + t) v) -
        (section4T s β h r (s.m (r - 1)) w - section4T s β h r (s.m (r - 1)) v)) =
      (∫ z in v..w, section4TVarianceQ s β h r (s.m (r - 1) + t) z) / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hm)] with t ht
    have hmt : s.m (r - 1) + t ∈ Set.Icc 0 1 := by
      constructor <;> linarith [ht.1, ht.2]
    rw [section4T_baseline s β h hr0 hr hw, section4T_baseline s β h hr0 hr hv,
      sub_self, sub_zero, smul_eq_mul,
      section4T_sub_eq_massGap_mul_integral s β h hr0 hr hmt (by linarith [ht.1]) hv hw hvw]
    field_simp [ht.1.ne']
    ring
  have H := tendsto_nhds_unique (hlim.congr' heq) hIhalf
  linarith

/-- Endpoint-safe integral representation of the actual U. -/
theorem section4U_eq_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4U s β h r v =
      ∫ z in (0 : ℝ)..v, section4TVarianceQ s β h r (s.m (r - 1)) z := by
  have H := section4U_sub_eq_integral s β h hr0 hr hm
    (v := 0) ⟨le_rfl, hv.1.trans hv.2⟩ hv hv.1
  simpa only [section4U_zero_variance s β h hr0 hr, sub_zero] using H

/-- Talagrand's actual U has derivative equal to the actual nested normalized
squared-slope factor, including a zero baseline mass. -/
theorem hasDerivAt_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4U s β h r) (section4TVarianceQ s β h r (s.m (r - 1)) v) v := by
  have hbase : s.m (r - 1) ∈ Set.Icc 0 1 := ⟨s.m_nonneg (by omega), hm.le⟩
  have hc := continuousOn_section4TVarianceQ_variance s β h hr0 hr hbase
  have hnb : Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) ∈ 𝓝 v :=
    Icc_mem_nhds hv.1 hv.2
  have hint := intervalIntegrable_section4TVarianceQ_closed s β h hr0 hr hbase
    (v := 0) ⟨le_rfl, hv.1.le.trans hv.2.le⟩ ⟨hv.1.le, hv.2.le⟩
  have H := intervalIntegral.integral_hasDerivAt_right hint
    ⟨_, hnb, hc.aestronglyMeasurable measurableSet_Icc⟩
    ((hc v ⟨hv.1.le, hv.2.le⟩).continuousAt hnb)
  apply H.congr_of_eventuallyEq
  filter_upwards [hnb] with z hz
  exact section4U_eq_integral s β h hr0 hr hm hz

/-- The derivative's probabilistic range is now proved, not just a Lipschitz consequence. -/
theorem deriv_section4U_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (section4U s β h r) v ∈ Set.Icc 0 1 := by
  rw [(hasDerivAt_section4U s β h hr0 hr hm hv).deriv]
  exact section4TVarianceQ_mem_Icc s β h r ⟨s.m_nonneg (by omega), hm.le⟩ v


/-- The actual overlap first variation now has its expected derivative.
The beta-zero case is constant; otherwise the interior overlap maps to the
interior split-variance interval. This is not an optimality/stationarity claim. -/
theorem hasDerivAt_section4FirstVariation_overlap {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r)) :
    HasDerivAt (section4FirstVariation s β h r)
      (β ^ 2 / 2 * (u - section4TVarianceQ s β h r (s.m (r - 1))
        (β ^ 2 * (s.q r - u)))) u := by
  by_cases hb : β = 0
  · subst β
    change HasDerivAt (fun z => section4FirstVariation s 0 h r z) _ u
    simpa [section4FirstVariation] using
      (hasDerivAt_const u (section4U s 0 h r 0 / 2))
  · have hb2 : 0 < β ^ 2 := sq_pos_of_ne_zero hb
    have hv : β ^ 2 * (s.q r - u) ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))) := by
      constructor
      · exact mul_pos hb2 (sub_pos.mpr hu.2)
      · exact mul_lt_mul_of_pos_left (by linarith [hu.1]) hb2
    have H := (hasDerivAt_section4U s β h hr0 hr hm hv).comp u
      (((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2))
    have HP := (((hasDerivAt_id u).pow 2).const_sub (s.q r ^ 2)).const_mul (β ^ 2 / 4)
    convert! (H.div_const 2).sub HP using 1
    simp only [id_eq]
    ring


end SpinGlass.Targets
