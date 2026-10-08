module

public import Paper.ParisiControlConvexity

@[expose] public section

/-! Actual time and probability integrability of a bounded control's cost. -/
noncomputable section
open Set MeasureTheory
namespace Paper

def parisiInstantControlCost {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := β ^ 2 / 2 * parisiCDF μ t * A t ω ^ 2

theorem measurable_parisiInstantControlCost {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) :
    Measurable (Function.uncurry (parisiInstantControlCost β μ A)) :=
  (measurable_const.mul ((parisiCDF_measurable μ).comp measurable_fst)).mul (hA.pow_const 2)

theorem norm_parisiInstantControlCost_le {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hb : ∀ t ω, ‖A t ω‖ ≤ 1) (t : ℝ) (ω : Ω) :
    ‖parisiInstantControlCost β μ A t ω‖ ≤ β ^ 2 / 2 := by
  unfold parisiInstantControlCost
  rw [norm_mul, norm_mul, norm_pow,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num)),
    Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
  calc
    _ ≤ β ^ 2 / 2 * 1 * 1 := by
      gcongr
      · exact parisiCDF_le_one μ t
      · exact pow_le_one₀ (norm_nonneg _) (hb t ω)
    _ = _ := by ring

theorem intervalIntegrable_parisiInstantControlCost {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ t ω, ‖A t ω‖ ≤ 1)
    (a b : ℝ) (ω : Ω) :
    IntervalIntegrable (fun t => parisiInstantControlCost β μ A t ω) volume a b := by
  exact (intervalIntegrable_const (c := β ^ 2 / 2)).mono_fun'
    (((measurable_parisiInstantControlCost β μ A hA).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (.of_forall fun t => norm_parisiInstantControlCost_le β μ A hb t ω)

theorem integrable_parisiInstantControlCost_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ t ω, ‖A t ω‖ ≤ 1)
    (a b : ℝ) (hab : a ≤ b) :
    Integrable (fun ω => ∫ t in a..b, parisiInstantControlCost β μ A t ω) P := by
  have hm := (measurable_parisiInstantControlCost β μ A hA).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc a b))
  have hm2 : StronglyMeasurable (fun ω => ∫ t in a..b, parisiInstantControlCost β μ A t ω) := by
    simpa only [intervalIntegral.integral_of_le hab, Function.uncurry, Prod.fst, Prod.snd] using hm
  apply (integrable_const (β ^ 2 / 2 * |b - a|)).mono' hm2.aestronglyMeasurable
  exact .of_forall fun ω => intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => norm_parisiInstantControlCost_le β μ A hb t ω)

theorem parisiInstantControlCost_integral_eq_cost {Ω : Type*} (β : ℝ)
    (μ : ParisiMeasure) (A : ℝ → Ω → ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..1, parisiInstantControlCost β μ A t ω) = parisiControlCost β μ A ω := by
  unfold parisiInstantControlCost parisiControlCost
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

end Paper
