module

public import Targets.Section4USecond
public import Targets.Section4UEndpoints

@[expose] public section

/-!
# Closed-interval regularity of the actual Hessian-square factor

The bounded-observable continuity theorem and the locked RSAT C2 regularity
give continuity of the actual factor in (4.45), including both split-variance
endpoints and mass zero. At the baseline all outer potentials are unchanged,
so their continuity is reused through the exact semigroup identification.

This yields the inward derivative `Q' = -R` at both endpoints. Continuity alone
does not give the depth-uniform Lipschitz bound required by Lemma 4.9.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem coupledContinuousOn_const_parisiF {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (S : Set ℝ) :
    CoupledContinuousOn (fun (_ : ℝ) (_ y : Fin 1 → ℝ) => parisiF s β j (y 0)) S := by
  obtain ⟨C, D, _, hD, hbound⟩ := parisiF_hasLinearGrowth s β j
  refine ⟨fun _ _ => (parisiF_measurable s β j).comp
    ((measurable_pi_apply 0).comp measurable_snd), ⟨C, D, hD, ?_⟩, ?_⟩
  · intro v hv x y
    have H := hbound (y 0)
    simp only [l1, Fin.sum_univ_one]
    nlinarith [mul_nonneg hD (abs_nonneg (x 0))]
  · intro x y hx hy
    have hc : Continuous (parisiF s β j) := continuous_iff_continuousAt.mpr
      fun z => ((parisiF_C2_props s β j).1.1 z).continuousAt
    exact hc.comp_continuousOn ((continuous_apply 0).comp_continuousOn hy)

private theorem coupledContinuousOn_section4_baseline {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {j : ℕ} (hj : j ≤ r - 1) :
    CoupledContinuousOn
      (fun v (_ y : Fin 1 → ℝ) => scalarFieldCascade
        (fun l => section4Mass s r (s.m (r - 1)) (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (y 0))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  have H := coupledContinuousOn_const_parisiF s β (k + 2 - r + 1 + j)
    (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
  obtain ⟨C, D, hD, hbound⟩ := H.growth
  refine ⟨?_, ⟨C, D, hD, ?_⟩, ?_⟩
  · intro v hv
    simpa only [section4Cascade_baseline s β hr0 hr hv hj] using H.measurable v hv
  · intro v hv x y
    simpa only [section4Cascade_baseline s β hr0 hr hv hj] using hbound v hv x y
  · intro x y hx hy
    exact (H.continuous x y hx hy).congr fun v hv =>
      congrFun (section4Cascade_baseline s β hr0 hr hv hj) (y v 0)

/-- The actual Hessian-square observable is continuous along all continuous
field paths through every outer level, on the closed physical variance interval.
The baseline mass may be zero. -/
theorem section4VarianceR_baseline_continuous_paths {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {j : ℕ} (hj : j ≤ r - 1) :
    let S := Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))
    ∀ x y : ℝ → Fin 1 → ℝ, ContinuousOn x S → ContinuousOn y S →
      ContinuousOn (fun v => section4VarianceR s β r (s.m (r - 1)) j v (x v) (y v)) S := by
  dsimp only
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  let S := Set.Icc (0 : ℝ) a
  have hm : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  induction j with
  | zero =>
    have hA := coupledContinuousOn_const_parisiF s β (k + 2 - r) S
    have hB := hA.scalarStep isCompact_Icc
      (fun _ _ => parisiF_hasLinearGrowth s β (k + 2 - r))
      (fun _ _ => parisiF_measurable s β (k + 2 - r)) hm.1
      (v := id) continuousOn_id (fun _ hv => hv.1)
    intro x y hx hy
    simp only [section4VarianceR]
    apply continuousOn_pairedSecondMean_paths hB isCompact_Icc
    · intro v _
      exact (((measurable_stepD2 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1
        (parisiF_C2_props s β _).2.2 (s.m (r - 1)) v).pow_const 2).comp
        ((measurable_pi_apply 0).comp measurable_snd))
    · intro v hv xx yy
      have HB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2
        (parisiF_C2_props s β (k + 2 - r)).1
        (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _)
        (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (HB.abs_second_le_one (yy 0))
    · intro xx yy hxx hyy
      exact (((continuous_parisiStep_variance_spatial (parisiF_C2_props s β _).1
        (continuous_parisiFSecond s β _) hm.1).2.2).comp_continuousOn
        (continuousOn_id.prodMk ((continuous_apply 0).comp_continuousOn hyy))).pow 2
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact hx
    · exact hy
  | succ j ih =>
    have hF := coupledContinuousOn_section4_baseline s β hr0 hr (j := j) (by omega)
    intro x y hx hy
    exact continuousOn_pairedSecondMean_paths hF isCompact_Icc
      (fun v _ => measurable_section4VarianceR s β r (s.m (r - 1)) j v)
      (fun v hv xx yy => by
        have H := section4VarianceR_mem_Icc s β r hm j v xx yy
        simpa only [abs_of_nonneg H.1] using H.2)
      (ih (by omega)) _ _ continuousOn_const x y hx hy

/-- Continuity of the genuine factor `R` in (4.45), including both physical
variance endpoints, all outer levels and the zero baseline mass. -/
theorem continuousOn_section4THessianSquare {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    ContinuousOn (section4THessianSquare s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :=
  section4VarianceR_baseline_continuous_paths s β hr0 hr (j := r - 1) le_rfl
    (fun _ => 0) (fun _ _ => h) continuousOn_const continuousOn_const

/-- Endpoint-safe integral representation of the actual derivative of Q. -/
theorem section4TVarianceQ_baseline_sub_eq_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    section4TVarianceQ s β h r (s.m (r - 1)) w -
      section4TVarianceQ s β h r (s.m (r - 1)) v =
        ∫ z in v..w, -section4THessianSquare s β h r z := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvw
  · exact (continuousOn_section4TVarianceQ_variance s β h hr0 hr
      ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩).mono
      (Set.Icc_subset_Icc hv.1 hw.2)
  · intro z hz
    exact hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr
      ⟨hv.1.trans_lt hz.1, hz.2.trans_le hw.2⟩
  · exact (((continuousOn_section4THessianSquare s β h hr0 hr).neg).mono
      (Set.uIcc_subset_Icc hv hw)).intervalIntegrable

/-- The numerical factor `-R` is the inward derivative of the actual Q at
both endpoints. Degenerate intervals are allowed in the derivative statement;
uniqueness of `derivWithin` is asserted separately for a positive interval. -/
theorem hasDerivWithinAt_section4TVarianceQ_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivWithinAt (section4TVarianceQ s β h r (s.m (r - 1)))
      (-section4THessianSquare s β h r v)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v := by
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  have ha : 0 ≤ a := hv.1.trans hv.2
  let R := fun v => -section4THessianSquare s β h r v
  let Re := fun z : ℝ => R (Set.projIcc 0 a ha z)
  have hc : ContinuousOn R (Set.Icc 0 a) :=
    (continuousOn_section4THessianSquare s β h hr0 hr).neg
  have hce : Continuous Re := hc.restrict.comp continuous_projIcc
  have heq (z : ℝ) (hz : z ∈ Set.Icc 0 a) : Re z = R z := by
    simp only [Re, Set.projIcc_of_mem ha hz]
  have hQ (z : ℝ) (hz : z ∈ Set.Icc 0 a) :
      section4TVarianceQ s β h r (s.m (r - 1)) z =
        section4TVarianceQ s β h r (s.m (r - 1)) 0 + ∫ w in (0 : ℝ)..z, Re w := by
    have H := section4TVarianceQ_baseline_sub_eq_integral s β h hr0 hr
      (v := 0) ⟨le_rfl, ha⟩ hz hz.1
    have HI : (∫ w in (0 : ℝ)..z, Re w) = ∫ w in (0 : ℝ)..z, R w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le hz.1] at hw
      exact heq w ⟨hw.1, hw.2.trans hz.2⟩
    rw [HI]
    linarith
  have H := (intervalIntegral.integral_hasDerivAt_right (hce.intervalIntegrable 0 v)
    hce.stronglyMeasurable.stronglyMeasurableAtFilter hce.continuousAt).const_add
      (section4TVarianceQ s β h r (s.m (r - 1)) 0)
  rw [heq v hv] at H
  exact H.hasDerivWithinAt.congr_of_mem hQ hv

/-- Numerical inward Q derivative when the physical interval is nondegenerate. -/
theorem derivWithin_section4TVarianceQ_baseline_eq {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (ha : 0 < β ^ 2 * (s.q r - s.q (r - 1))) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    derivWithin (section4TVarianceQ s β h r (s.m (r - 1)))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v =
        -section4THessianSquare s β h r v :=
  (hasDerivWithinAt_section4TVarianceQ_baseline s β h hr0 hr hv).derivWithin
    (uniqueDiffOn_Icc ha v hv)

end SpinGlass.Targets
