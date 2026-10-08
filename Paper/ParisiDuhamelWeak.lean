module

public import Paper.ParisiWeak
public import Paper.VolterraFubini

@[expose] public section

/-!
# Absolute Fubini estimates for the nonlinear weak Duhamel equation

The source is genuinely bounded and measurable, and the adjoint test is
smooth with compact support.  The lemmas below prove the absolute integral
requirements rather than treating changes of integration order formally.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem exists_uniform_integral_norm_sections_bound (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, (∫ x, ‖ψ (t, x)‖) ≤ B := by
  obtain ⟨R, hR⟩ := (hc.image continuous_snd).isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hc
  let K : Set ℝ := Icc (-R) R
  let majorant : ℝ → ℝ := K.indicator (fun _ => M)
  have hmi : Integrable majorant := by
    exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hMb : 0 ≤ M := (norm_nonneg (ψ (0, 0))).trans (hM _)
  refine ⟨M * volume.real K, mul_nonneg hMb ENNReal.toReal_nonneg, ?_⟩
  intro t
  have hb : ∀ x : ℝ, ‖ψ (t, x)‖ ≤ majorant x := by
    intro x
    by_cases hx : x ∈ K
    · simpa [majorant, Set.indicator_of_mem hx] using hM (t, x)
    · have hz : ψ (t, x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hp
        have hr := hR x (mem_image_of_mem Prod.snd hp)
        exact hx (by simpa only [K, mem_Icc, Real.norm_eq_abs, abs_le] using hr)
      simp [majorant, Set.indicator_of_notMem hx, hz]
  have hint := norm_integral_le_of_norm_le (f := fun x => ‖ψ (t, x)‖)
    hmi (.of_forall fun x => by simpa using hb x)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hint
  apply hint.trans_eq
  unfold majorant
  rw [integral_indicator_const M measurableSet_Icc]
  simp [K, smul_eq_mul, mul_comm]

noncomputable def boundedHeatSource (β : ℝ) (F : ℝ × ℝ → ℝ)
    (t s x : ℝ) : ℝ := heatSemigroup (β ^ 2 * (s - t)) (fun y => F (s, y)) x

theorem boundedHeatSource_measurable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => boundedHeatSource β F p.1.1 p.1.2 p.2) := by
  have hm : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      F (p.1.1.2, p.1.2 + Real.sqrt (β ^ 2 * (p.1.1.2 - p.1.1.1)) * p.2)) :=
    hF.comp (by fun_prop)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable

theorem norm_boundedHeatSource_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (t s x : ℝ) :
    ‖boundedHeatSource β F t s x‖ ≤ M :=
  norm_heatSemigroup_le _ _ M (fun y => hb (s, y)) x

noncomputable def boundedVolterraPotential (β : ℝ) (F : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∫ s, if p.1 < s then boundedHeatSource β F p.1 s p.2 else 0 ∂parisiTimeMeasure

theorem boundedVolterraPotential_measurable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) : Measurable (boundedVolterraPotential β F) := by
  have hm := (boundedHeatSource_measurable β F hF).comp
    (show Measurable (fun p : (ℝ × ℝ) × ℝ => ((p.1.1, p.2), p.1.2)) by fun_prop)
  have htri : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 < p.2} :=
    measurableSet_lt (measurable_fst.fst) measurable_snd
  have hi : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      if p.1.1 < p.2 then boundedHeatSource β F p.1.1 p.2 p.1.2 else 0) :=
    hm.ite htri measurable_const
  exact (hi.stronglyMeasurable.integral_prod_right' (ν := parisiTimeMeasure)).measurable

theorem norm_boundedVolterraPotential_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (p : ℝ × ℝ) :
    ‖boundedVolterraPotential β F p‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have h := norm_integral_le_of_norm_le_const (μ := parisiTimeMeasure)
    (f := fun s => if p.1 < s then boundedHeatSource β F p.1 s p.2 else 0) (C := M)
    (.of_forall fun s => by
      split_ifs
      · exact norm_boundedHeatSource_le β F M hb _ _ _
      · simpa using hM)
  simpa [boundedVolterraPotential, parisiTimeMeasure,
    Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

theorem boundedVolterraPotential_eq (β : ℝ) (F : ℝ × ℝ → ℝ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    boundedVolterraPotential β F (t, x) = ∫ s in t..1, boundedHeatSource β F t s x :=
  integral_parisiTime_lower_triangle (fun s => boundedHeatSource β F t s x) t ht

theorem integrable_boundedVolterra_test (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p => boundedVolterraPotential β F p * ψ p)
      (parisiTimeMeasure.prod volume) := by
  have hψi : Integrable ψ (parisiTimeMeasure.prod volume) := by
    unfold parisiTimeMeasure
    exact hψ.integrable_of_hasCompactSupport hc
  have hi := hψi.mul_bdd (boundedVolterraPotential_measurable β F hF).aestronglyMeasurable
    (.of_forall (norm_boundedVolterraPotential_le β F M hb))
  exact hi.congr (.of_forall fun p => mul_comm _ _)

theorem integrable_boundedHeatSource_test_section (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => boundedHeatSource β F t p.1 p.2 * ψ (t, p.2))
      ((volume.restrict (Ioc t 1)).prod volume) := by
  have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
    (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section ψ hc t)
  have hm := (boundedHeatSource_measurable β F hF).comp
    (show Measurable (fun p : ℝ × ℝ => ((t, p.1), p.2)) by fun_prop)
  have hi := (hψi.comp_snd (volume.restrict (Ioc t 1))).mul_bdd hm.aestronglyMeasurable
    (.of_forall fun p => norm_boundedHeatSource_le β F M hb t p.1 p.2)
  exact hi.congr (.of_forall fun p => mul_comm _ _)

theorem integral_boundedVolterra_test_section (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, boundedVolterraPotential β F (t, x) * ψ (t, x)) =
      ∫ s in t..1, ∫ x, boundedHeatSource β F t s x * ψ (t, x) := by
  have hi := integrable_boundedHeatSource_test_section β F hF M hb ψ hψ hc t
  simp_rw [boundedVolterraPotential_eq β F t _ ht]
  simp_rw [← intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_of_le ht.2]
  simp_rw [intervalIntegral.integral_of_le ht.2]
  exact integral_integral_swap hi.swap

noncomputable def boundedHeatTestPair (β : ℝ) (F ψ : ℝ × ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ x, boundedHeatSource β F t s x * ψ (t, x)

theorem boundedHeatTestPair_measurable (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × ℝ => boundedHeatTestPair β F ψ p.1 p.2) := by
  have hm := (boundedHeatSource_measurable β F hF).mul
    (hψ.comp (show Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) by fun_prop))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem norm_boundedHeatTestPair_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (B : ℝ) (hB : ∀ t : ℝ, (∫ x, ‖ψ (t, x)‖) ≤ B) (t s : ℝ) :
    ‖boundedHeatTestPair β F ψ t s‖ ≤ M * B := by
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
    (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section ψ hc t)
  have h := norm_integral_le_of_norm_le
    (f := fun x : ℝ => boundedHeatSource β F t s x * ψ (t, x))
    (hψi.norm.const_mul M) (.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_boundedHeatSource_le β F M hb t s x) (norm_nonneg _))
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hB t) hM)

/-- The change of order over the actual time triangle for a bounded
measurable source tested against a continuous compactly supported function. -/
theorem integral_boundedVolterra_test_swap (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ p, boundedVolterraPotential β F p * ψ p ∂parisiTimeMeasure.prod volume) =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..s, boundedHeatTestPair β F ψ t s := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_uniform_integral_norm_sections_bound ψ hψ hc
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hm : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then boundedHeatTestPair β F ψ p.1 p.2 else (0 : ℝ)) :=
    (boundedHeatTestPair_measurable β F hF ψ hψ.measurable).ite
      (measurableSet_lt measurable_fst measurable_snd) measurable_const
  have hi : Integrable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then boundedHeatTestPair β F ψ p.1 p.2 else 0)
      (parisiTimeMeasure.prod parisiTimeMeasure) :=
    (integrable_const (M * B)).mono' hm.aestronglyMeasurable (.of_forall fun p => by
      split_ifs
      · exact norm_boundedHeatTestPair_le β F M hb ψ hψ hc B hB p.1 p.2
      · simpa using mul_nonneg hM hB0)
  rw [integral_prod (fun p => boundedVolterraPotential β F p * ψ p)
    (integrable_boundedVolterra_test β F hF M hb ψ hψ hc)]
  calc
    _ = ∫ t in (0 : ℝ)..1, ∫ s in t..1, boundedHeatTestPair β F ψ t s := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact integral_boundedVolterra_test_section β F hF M hb ψ hψ hc t ⟨ht.1.le, ht.2⟩
    _ = _ := integral_volterra_swap (boundedHeatTestPair β F ψ) hi

theorem boundedHeatTestPair_adjoint (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t s : ℝ) (hts : t ≤ s) :
    boundedHeatTestPair β F ψ t s =
      ∫ x, F (s, x) * heatSemigroup (β ^ 2 * (s - t)) (fun y => ψ (t, y)) x := by
  exact heatSemigroup_adjoint (β ^ 2 * (s - t)) (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hts))
    (fun y => F (s, y)) (fun y => ψ (t, y)) (hF.comp (by fun_prop))
    ((hψ.comp (by fun_prop)).measurable)
    ((hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section ψ hc t)) M (fun y => hb (s, y))

theorem integrable_boundedSource_heatTest (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (s : ℝ) (_hs : 0 ≤ s) :
    Integrable (fun p : ℝ × ℝ => F (s, p.2) *
      heatSemigroup (β ^ 2 * (s - p.1)) (fun y => ψ (p.1, y)) p.2)
      ((volume.restrict (Ioc (0 : ℝ) s)).prod volume) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_integral_norm_sections_bound ψ hψ hc
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hψmeas : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ψ (p.1.1, p.1.2 + Real.sqrt (β ^ 2 * (s - p.1.1)) * p.2)) :=
    hψ.measurable.comp (by fun_prop)
  have hh := (hψmeas.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hprod : Measurable (fun p : ℝ × ℝ => F (s, p.2) *
      heatSemigroup (β ^ 2 * (s - p.1)) (fun y => ψ (p.1, y)) p.2) :=
    (hF.comp (by fun_prop)).mul hh
  apply (integrable_prod_iff hprod.aestronglyMeasurable).mpr
  have hint : ∀ t ∈ Ioc (0 : ℝ) s,
      Integrable (fun x : ℝ => heatSemigroup (β ^ 2 * (s - t)) (fun y => ψ (t, y)) x) := by
    intro t ht
    have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
      (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section ψ hc t)
    exact integrable_heatSemigroup_volume _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2))
      _ ((hψ.comp (by fun_prop)).measurable) hψi
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hi := (hint t ht).mul_bdd (hF.comp (by fun_prop)).aestronglyMeasurable
      (.of_forall fun x => hb (s, x))
    exact hi.congr (.of_forall fun x => mul_comm _ _)
  · apply (integrable_const (M * B)).mono'
      (hprod.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
      (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_spatial_section ψ hc t)
    have hheat := integral_norm_heatSemigroup_le _
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2))
      (fun y => ψ (t, y)) ((hψ.comp (by fun_prop)).measurable) hψi
    have hnorm := norm_integral_le_of_norm_le
      (f := fun x => ‖F (s, x) * heatSemigroup (β ^ 2 * (s - t)) (fun y => ψ (t, y)) x‖)
      ((hint t ht).norm.const_mul M) (.of_forall fun x => by
        simp only [norm_norm, norm_mul]
        exact mul_le_mul_of_nonneg_right (hb (s, x)) (norm_nonneg _))
    rw [integral_const_mul] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_left (hheat.trans (hB t)) hM)

noncomputable def parisiAdjointSource (β : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -parisiTestT φ p + β ^ 2 / 2 * parisiTestXX φ p

theorem continuous_parisiAdjointSource (β : ℝ) (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (parisiAdjointSource β φ) :=
  (continuous_parisiTestT φ hφ).neg.add (continuous_const.mul (continuous_parisiTestXX φ hφ))

theorem hasCompactSupport_parisiAdjointSource (β : ℝ) (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasCompactSupport (parisiAdjointSource β φ) := by
  exact (hasCompactSupport_parisiTestT φ hφ hc).neg.add
    (hasCompactSupport_parisiTestXX φ hφ hc).mul_left

theorem integral_boundedHeatTestPair_adjointSource (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, boundedHeatTestPair β F (parisiAdjointSource β φ) t s) =
      -(∫ x, F (s, x) * φ (s, x)) := by
  have hψ := continuous_parisiAdjointSource β φ hφ
  have hψc := hasCompactSupport_parisiAdjointSource β φ hφ hc
  have hi := integrable_boundedSource_heatTest β F hF M hb (parisiAdjointSource β φ) hψ hψc s hs
  calc
    _ = ∫ t in (0 : ℝ)..s, ∫ x, F (s, x) *
        heatSemigroup (β ^ 2 * (s - t)) (fun y => parisiAdjointSource β φ (t, y)) x := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hs] at ht
      exact boundedHeatTestPair_adjoint β F hF M hb _ hψ hψc t s ht.2.le
    _ = ∫ x, F (s, x) * (∫ t in (0 : ℝ)..s,
        heatSemigroup (β ^ 2 * (s - t)) (fun y => parisiAdjointSource β φ (t, y)) x) := by
      rw [intervalIntegral.integral_of_le hs, integral_integral_swap hi]
      simp_rw [intervalIntegral.integral_of_le hs, integral_const_mul]
    _ = ∫ x, F (s, x) * (-φ (s, x)) := by
      congr 1
      funext x
      unfold parisiAdjointSource
      rw [integral_heat_adjointSource_positiveTimeTest φ hφ hc hsupp β s x hβ hs]
    _ = _ := by simp only [mul_neg, integral_neg]

/-- The bounded-source Duhamel term satisfies the actual distributional heat
equation. All absolute Fubini obligations follow from boundedness of the
source and compact support of the smooth test. -/
theorem integral_boundedVolterra_adjointSource (β : ℝ) (hβ : β ≠ 0)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) :
    (∫ p, boundedVolterraPotential β F p * parisiAdjointSource β φ p
      ∂parisiTimeMeasure.prod volume) =
      -(∫ p, F p * φ p ∂parisiTimeMeasure.prod volume) := by
  rw [integral_boundedVolterra_test_swap β F hF M hb (parisiAdjointSource β φ)
    (continuous_parisiAdjointSource β φ hφ) (hasCompactSupport_parisiAdjointSource β φ hφ hc)]
  have hFφ : Integrable (fun p => F p * φ p) (parisiTimeMeasure.prod volume) := by
    have hφi : Integrable φ (parisiTimeMeasure.prod volume) :=
      hφ.continuous.integrable_of_hasCompactSupport hc
    have hi := hφi.mul_bdd
      hF.aestronglyMeasurable (.of_forall hb)
    exact hi.congr (.of_forall fun p => mul_comm _ _)
  rw [integral_prod (fun p => F p * φ p) hFφ, ← integral_neg]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact integral_boundedHeatTestPair_adjointSource β hβ F hF M hb φ hφ hc hsupp s hs.1.le

end Paper
