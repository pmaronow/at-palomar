module

public import Targets.Section4RightVarianceBaseline
public import Targets.Section4RightMassDerivative
public import Targets.Section4TerminalFactors
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# The actual right mass derivative has variance derivative Q

A left mass difference quotient of the actual variance integral identity
proves the mixed identity. The variable right mass remains in its actual
outer position throughout. Closed-interval inward derivatives follow by FTC.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual right variance derivative with its normalized factor exposed. -/
theorem hasDerivAt_section4RightT_variance_factor {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 (s.m r)) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (section4RightT s β h r m)
      ((m - s.m r) / 2 * section4RightTVarianceQ s β h r m v) v := by
  rw [← section4RightTVarianceD_eq_massGap_mul]
  exact hasDerivAt_section4RightT_variance s β h hr hm.1 hm.2 hv

/-- Automatic integrability of the nonpositive actual right derivative. -/
theorem intervalIntegrable_section4RightT_variance_factor {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 (s.m r)) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    IntervalIntegrable (fun z => (m - s.m r) / 2 * section4RightTVarianceQ s β h r m z)
      volume v w := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hvw).mpr
  have H : IntegrableOn (fun z => -((m - s.m r) / 2 *
      section4RightTVarianceQ s β h r m z)) (Set.Ioc v w) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg
      (((continuousOn_section4RightT s β h hr hm.1).mono
        (Set.Icc_subset_Icc hv.1 hw.2)).neg)
    · intro z hz
      exact (hasDerivAt_section4RightT_variance_factor s β h hr hm
        ⟨hv.1.trans_lt hz.1, hz.2.trans_le hw.2⟩).neg
    · intro z _
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm.2) (by norm_num))
        (section4RightTVarianceQ_mem_Icc s β h hr m z).1)
  convert! H.neg using 1
  ext z
  exact (neg_neg _).symm

/-- Endpoint-safe integral formula for the actual right variance variation. -/
theorem section4RightT_sub_eq_massGap_mul_integral {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 (s.m r)) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    section4RightT s β h r m w - section4RightT s β h r m v =
      (m - s.m r) / 2 * ∫ z in v..w, section4RightTVarianceQ s β h r m z := by
  rw [← intervalIntegral.integral_const_mul]
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvw
    ((continuousOn_section4RightT s β h hr hm.1).mono (Set.Icc_subset_Icc hv.1 hw.2))
  · intro z hz
    exact hasDerivAt_section4RightT_variance_factor s β h hr hm
      ⟨hv.1.trans_lt hz.1, hz.2.trans_le hw.2⟩
  · exact intervalIntegrable_section4RightT_variance_factor s β h hr hm hv hw hvw

/-- The normalized right factor is integrable even at equal masses; there
the proved reflected-factor identity replaces division by a zero mass gap. -/
theorem intervalIntegrable_section4RightTVarianceQ_closed {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 (s.m r)) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    IntervalIntegrable (section4RightTVarianceQ s β h r m) volume v w := by
  by_cases he : m = s.m r
  · subst m
    have H := ((continuousOn_section4RightQ_all_levels s β h hr).mono
      (Set.uIcc_subset_Icc hv hw)).intervalIntegrable (μ := volume)
    apply H.congr
    intro z hz
    rw [Set.uIoc_of_le hvw] at hz
    exact (section4RightTVarianceQ_baseline_eq s β h hr
      ⟨hv.1.trans hz.1.le, hz.2.trans hw.2⟩).symm
  · have hc : (m - s.m r) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr he) (by norm_num)
    have H := (intervalIntegrable_section4RightT_variance_factor s β h hr hm hv hw hvw).div_const
      ((m - s.m r) / 2)
    simpa only [mul_div_cancel_left₀ _ hc] using H

/-- Bounded dominated convergence permits a mass limit in the variance integral. -/
theorem continuousOn_integral_section4RightTVarianceQ {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    ContinuousOn (fun m => ∫ z in v..w, section4RightTVarianceQ s β h r m z)
      (Set.Icc 0 (s.m r)) := by
  simp_rw [intervalIntegral.integral_of_le hvw]
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro m hm
    exact (intervalIntegrable_section4RightTVarianceQ_closed s β h hr hm hv hw hvw).1.aestronglyMeasurable
  · intro m _
    filter_upwards with z
    have H := section4RightTVarianceQ_mem_Icc s β h hr m z
    simpa only [Real.norm_eq_abs, abs_of_nonneg H.1] using H.2
  · exact integrable_const 1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact (continuousOn_section4RightTVarianceQ_mass s β h hr
      (hv.1.trans hz.1.le)).mono
      (Set.Icc_subset_Icc le_rfl (s.m_le_one hr))

/-- The actual right mass derivative difference equals the reflected-factor
integral, by a genuine mass limit from below. Baseline mass one is included. -/
theorem section4RightU_sub_eq_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    section4RightU s β h r w - section4RightU s β h r v =
      ∫ z in v..w, section4RightQ s β h r z := by
  have hbase : s.m r ∈ Set.Icc 0 (s.m r) := ⟨hm.le, le_rfl⟩
  have hd := (hasDerivAt_section4RightT_mass_baseline s β h hr hw.1).sub
    (hasDerivAt_section4RightT_mass_baseline s β h hr hv.1)
  have hlim := hd.tendsto_slope_zero_left
  have htend : Tendsto (fun t : ℝ => s.m r + t)
      (𝓝[<] 0) (𝓝[Set.Icc 0 (s.m r)] (s.m r)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using
        (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun t : ℝ => s.m r + t) (𝓝[<] 0) (𝓝 (s.m r + 0)))
    · filter_upwards [Ioo_mem_nhdsLT (neg_neg_of_pos hm)] with t ht
      constructor <;> linarith [ht.1, ht.2]
  have hI := ((continuousOn_integral_section4RightTVarianceQ s β h hr hv hw hvw)
    (s.m r) hbase).tendsto.comp htend
  have hIhalf := hI.div_const 2
  have heq : ∀ᶠ t : ℝ in 𝓝[<] 0,
      t⁻¹ • ((section4RightT s β h r (s.m r + t) w -
          section4RightT s β h r (s.m r + t) v) -
        (section4RightT s β h r (s.m r) w - section4RightT s β h r (s.m r) v)) =
      (∫ z in v..w, section4RightTVarianceQ s β h r (s.m r + t) z) / 2 := by
    filter_upwards [Ioo_mem_nhdsLT (neg_neg_of_pos hm)] with t ht
    have hmt : s.m r + t ∈ Set.Icc 0 (s.m r) := by
      constructor <;> linarith [ht.1, ht.2]
    rw [section4RightT_baseline s β h hr hw, section4RightT_baseline s β h hr hv,
      sub_self, sub_zero, smul_eq_mul,
      section4RightT_sub_eq_massGap_mul_integral s β h hr hmt hv hw hvw]
    field_simp [ht.2.ne]
    ring
  have H := tendsto_nhds_unique (hlim.congr' heq) hIhalf
  have hInt : (∫ z in v..w, section4RightTVarianceQ s β h r (s.m r) z) =
      ∫ z in v..w, section4RightQ s β h r z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le hvw] at hz
    exact section4RightTVarianceQ_baseline_eq s β h hr
      ⟨hv.1.trans hz.1, hz.2.trans hw.2⟩
  rw [hInt] at H
  linarith

/-- Endpoint-safe integral representation of the actual right mass derivative. -/
theorem section4RightU_eq_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section4RightU s β h r v = ∫ z in (0 : ℝ)..v, section4RightQ s β h r z := by
  have H := section4RightU_sub_eq_integral s β h hr hm
    (v := 0) ⟨le_rfl, hv.1.trans hv.2⟩ hv hv.1
  simpa only [section4RightU_zero_variance s β h hr, sub_zero] using H

/-- The actual right U has its actual factor as inward derivative everywhere
on the physical interval. No numerical derivative uniqueness is needed for
a degenerate interval. -/
theorem hasDerivWithinAt_section4RightU {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivWithinAt (section4RightU s β h r) (section4RightQ s β h r v)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) v := by
  let a := β ^ 2 * (s.q (r + 1) - s.q r)
  have ha : 0 ≤ a := hv.1.trans hv.2
  let Q := section4RightQ s β h r
  let Qe : ℝ → ℝ := fun z => Q (Set.projIcc 0 a ha z)
  have hc : ContinuousOn Q (Set.Icc 0 a) := continuousOn_section4RightQ_all_levels s β h hr
  have hce : Continuous Qe := hc.restrict.comp continuous_projIcc
  have heq (z : ℝ) (hz : z ∈ Set.Icc 0 a) : Qe z = Q z := by
    simp only [Qe, Set.projIcc_of_mem ha hz]
  have hU (z : ℝ) (hz : z ∈ Set.Icc 0 a) :
      section4RightU s β h r z = ∫ w in (0 : ℝ)..z, Qe w := by
    rw [section4RightU_eq_integral s β h hr hm hz]
    apply intervalIntegral.integral_congr
    intro w hw
    rw [Set.uIcc_of_le hz.1] at hw
    exact (heq w ⟨hw.1, hw.2.trans hz.2⟩).symm
  have H := intervalIntegral.integral_hasDerivAt_right (hce.intervalIntegrable 0 v)
    hce.stronglyMeasurable.stronglyMeasurableAtFilter hce.continuousAt
  rw [heq v hv] at H
  exact H.hasDerivWithinAt.congr_of_mem hU hv

end SpinGlass.Targets
