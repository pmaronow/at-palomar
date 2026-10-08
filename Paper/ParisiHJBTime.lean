module

public import Paper.HJBTimeGrid
public import Paper.HJBTimePotentialLimit
public import Paper.ParisiRestartState
public import Paper.ParisiHJBBase

@[expose] public section

/-! Actual attained Parisi control values at every physical time and field.
The controlled process starts afresh at elapsed time zero. Its running
coefficient is exactly the original CDF evaluated at the shifted time.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter
open scoped NNReal Topology
namespace Paper

/-- Generic elapsed-time verification on actual Itô characteristics. -/
theorem parisiTime_control_upper {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (rho μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hshift : ∀ r ∈ Icc (0 : ℝ) (1 - a), parisiCDF rho r = parisiCDF μ (a + r))
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A)) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), d r.toNNReal sample = β ^ 2 * parisiCDF rho r * A r sample)
    (hi0 : Integrable (X 0) P) :
    (∫ sample, Real.log (Real.cosh (X (1 - a).toNNReal sample)) ∂P) -
      hjbExpectedCost P (parisiInstantControlCost β rho A) 0 (1 - a) ≤
        ∫ sample, parisiPotential β μ (a, X 0 sample) ∂P := by
  have hu := tendsto_integral_finiteParisiPotential_time β hβ μ a ha (X 0) hi0
  have he := (tendsto_parisiCDFDistance_grid μ).const_mul ((3 / 2 : ℝ) * β ^ 2)
  have hl := hu.add he
  simp only [mul_zero, add_zero] at hl
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hl (.of_forall fun n =>
    hjbTimeGrid_control_upper hc hβ rho μ μ n a ha hshift A hAm hA hd hi0)

/-- The actual shifted PDE feedback attains the generic elapsed-time value. -/
theorem parisiTime_feedback_value {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (rho μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hshift : ∀ r ∈ Icc (0 : ℝ) (1 - a), parisiCDF rho r = parisiCDF μ (a + r))
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A)) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), d r.toNNReal sample = β ^ 2 * parisiCDF rho r * A r sample)
    (hi0 : Integrable (X 0) P)
    (hoptimal : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), A r sample = parisiGradient β μ (a + r, X r.toNNReal sample)) :
    (∫ sample, Real.log (Real.cosh (X (1 - a).toNNReal sample)) ∂P) -
      hjbExpectedCost P (parisiInstantControlCost β rho A) 0 (1 - a) =
        ∫ sample, parisiPotential β μ (a, X 0 sample) ∂P := by
  apply le_antisymm (parisiTime_control_upper hc hβ rho μ a ha hshift A hAm hA hd hi0)
  have hu := tendsto_integral_finiteParisiPotential_time β hβ μ a ha (X 0) hi0
  have he := (tendsto_parisiCDFDistance_grid μ).const_mul ((3 / 2 : ℝ) * β ^ 2)
  have hg := (((tendsto_parisiHJBGradientError β hβ μ).pow 2).const_mul (β ^ 2 / 2)).mul_const (1 - a)
  have hl := (hu.sub he).sub hg
  simp only [mul_zero, zero_mul, sub_zero, zero_pow (by norm_num : 2 ≠ 0)] at hl
  apply le_of_tendsto hl
  exact .of_forall fun n => (hjbTimeGrid_control_error_bounds hc hβ rho μ μ n a ha hshift A hAm hA hd hi0
    (parisiHJBGradientError_nonneg β μ n) (fun sample r hr => by
      rw [hoptimal sample r hr]
      exact parisiHJBGradientError_bound β μ n (a + r) _)).2

end Paper
