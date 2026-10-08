module

public import Paper.ParisiSelectedState
public import Paper.JTVariational
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # Actual general-measure second moments and variational observables -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Paper

theorem measurable_selectedParisiStateReal (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Measurable (fun ω => selectedParisiStateReal β h hβ μ ω t) := by
  have hm0 := measurable_canonicalParisiItoState β h μ
      (fun s x => parisiGradient β μ (s, x)) (continuous_parisiGradient β μ)
      (fun s x => norm_parisiGradient_le_one β μ (s, x))
      (lipschitzWith_parisiGradient β hβ μ)
  have hm : Measurable (fun ω => selectedParisiItoState β h hβ μ t.toNNReal ω) := by
    exact hm0.comp (f := fun ω : BrownianSample => (t.toNNReal, ω))
      (measurable_const.prodMk measurable_id)
  convert hm using 1
  funext ω
  rw [selectedParisiItoState_eq β h hβ μ
    (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2), Real.coe_toNNReal _ ht.1]

theorem measurable_selectedParisiSecondMoment_integrand (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Measurable (fun ω => parisiGradient β μ (t, selectedParisiStateReal β h hβ μ ω t) ^ 2) :=
  ((continuous_parisiGradient β μ).measurable.comp
    (measurable_const.prodMk (measurable_selectedParisiStateReal β h hβ μ t ht))).pow_const 2

theorem norm_selectedParisiSecondMoment_integrand_le_one (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ω : BrownianSample) :
    ‖parisiGradient β μ (t, selectedParisiStateReal β h hβ μ ω t) ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg _)
    (norm_parisiGradient_le_one β μ (t, selectedParisiStateReal β h hβ μ ω t)) 2

theorem integrable_selectedParisiSecondMoment_integrand (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => parisiGradient β μ (t, selectedParisiStateReal β h hβ μ ω t) ^ 2)
      canonicalBrownianMeasure :=
  (integrable_const (1 : ℝ)).mono'
    (measurable_selectedParisiSecondMoment_integrand β h hβ μ t ht).aestronglyMeasurable
    (.of_forall (norm_selectedParisiSecondMoment_integrand_le_one β h hβ μ t))

theorem continuousOn_selectedParisiSecondMoment (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    ContinuousOn (selectedParisiSecondMoment β h hβ μ) (Icc (0 : ℝ) 1) := by
  apply continuousOn_of_dominated (μ := canonicalBrownianMeasure)
    (F := fun (t : ℝ) ω => parisiGradient β μ
      (t, selectedParisiStateReal β h hβ μ ω t) ^ 2) (bound := fun _ => (1 : ℝ))
  · intro t ht
    exact (measurable_selectedParisiSecondMoment_integrand β h hβ μ t ht).aestronglyMeasurable
  · intro t _
    exact .of_forall (norm_selectedParisiSecondMoment_integrand_le_one β h hβ μ t)
  · exact integrable_const _
  · exact .of_forall fun ω => ((continuous_parisiGradient β μ).comp
      (continuous_id.prodMk (continuous_selectedParisiStateReal β h hβ μ ω))).pow 2
        |>.continuousOn

theorem selectedParisiSecondMoment_nonneg (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) : 0 ≤ selectedParisiSecondMoment β h hβ μ t :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem selectedParisiSecondMoment_le_one (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) : selectedParisiSecondMoment β h hβ μ t ≤ 1 := by
  have hn := norm_integral_le_of_norm_le_const (μ := canonicalBrownianMeasure)
    (.of_forall (norm_selectedParisiSecondMoment_integrand_le_one β h hβ μ t))
  rw [probReal_univ, mul_one] at hn
  change ‖selectedParisiSecondMoment β h hβ μ t‖ ≤ 1 at hn
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)

theorem continuousOn_selectedParisiG (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ContinuousOn (selectedParisiG β h hβ μ) (Icc (0 : ℝ) 1) := by
  change ContinuousOn (fun t => ∫ s in t..1,
    β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s)) (Icc (0 : ℝ) 1)
  have hi : IntegrableOn (fun s => β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_const.mul
      ((continuousOn_selectedParisiSecondMoment β h hβ μ).sub continuousOn_id)).integrableOn_compact
        isCompact_Icc
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval_left hi

theorem continuous_selectedParisiG_overlap (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Continuous (fun q : Overlap => selectedParisiG β h hβ μ q) :=
  (continuousOn_selectedParisiG β h hβ μ).comp_continuous continuous_subtype_val
    (fun q => q.property)

theorem selectedParisiSecondMoment_initial (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    selectedParisiSecondMoment β h hβ μ 0 = parisiGradient β μ (0, h) ^ 2 := by
  simp only [selectedParisiSecondMoment, selectedParisiState_initial,
    integral_const, probReal_univ, one_smul]

theorem selectedParisiG_terminal (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    selectedParisiG β h hβ μ 1 = 0 := by simp only [selectedParisiG, parisiG, intervalIntegral.integral_same]

theorem norm_selectedParisiG_le (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖selectedParisiG β h hβ μ t‖ ≤ β ^ 2 / 2 * (1 - t) := by
  have hb : ∀ s ∈ uIoc t 1,
      ‖β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s)‖ ≤ β ^ 2 / 2 := by
    intro s hs
    rw [uIoc_of_le ht.2] at hs
    have hs0 : 0 ≤ s := ht.1.trans hs.1.le
    have hf0 := selectedParisiSecondMoment_nonneg β h hβ μ s
    have hf1 := selectedParisiSecondMoment_le_one β h hβ μ s
    have ha : ‖selectedParisiSecondMoment β h hβ μ s - s‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.2]
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
    simpa using mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ β ^ 2 / 2)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [selectedParisiG, parisiG, abs_of_nonneg (sub_nonneg.mpr ht.2)] using hi

theorem hasDerivAt_selectedParisiG (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (selectedParisiG β h hβ μ)
      (β ^ 2 / 2 * (t - selectedParisiSecondMoment β h hβ μ t)) t := by
  let f := fun s => β ^ 2 / 2 * (selectedParisiSecondMoment β h hβ μ s - s)
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((continuousOn_selectedParisiSecondMoment β h hβ μ).sub continuousOn_id)
  have hc : ContinuousAt f t := hfc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hi := parisiIntegrable (β := β) (continuousOn_selectedParisiSecondMoment β h hβ μ)
    ⟨ht.1.le, ht.2.le⟩ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hm : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hfc.mono Ioo_subset_Icc_self) t ht
  have hd := intervalIntegral.integral_hasDerivAt_left hi hm hc
  convert hd using 1
  · rfl
  · ring

end Paper
