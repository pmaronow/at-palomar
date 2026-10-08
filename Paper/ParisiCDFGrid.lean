module

public import Paper.ParisiCDFIntegral
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Finite atomic approximations of actual Parisi measures

The grid measure is the push-forward by upward rounding to a uniform grid.
Its CDF lies below the original CDF, and the rounding displacement tends to
zero uniformly. These are concrete probability measures, not abstract step
functions assumed to represent measures.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Paper

/-- An equally spaced overlap grid with mesh `1 / (n+1)`. -/
noncomputable def parisiGridPoint (n : ℕ) (i : Fin (n + 2)) : Overlap :=
  ⟨(i : ℝ) / (n + 1 : ℕ), by
    have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    constructor
    · positivity
    · apply (div_le_one hd).mpr
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

/-- The index of the first grid point greater than or equal to `x`. -/
noncomputable def parisiGridIndex (n : ℕ) (x : Overlap) : Fin (n + 2) :=
  ⟨Nat.ceil ((n + 1 : ℕ) * (x : ℝ)), by
    apply Nat.lt_succ_of_le
    apply Nat.ceil_le.mpr
    have hd : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
    simpa using mul_le_mul_of_nonneg_left x.property.2 hd⟩

/-- Upward overlap rounding; endpoint atoms are retained. -/
noncomputable def parisiGridRound (n : ℕ) (x : Overlap) : Overlap :=
  parisiGridPoint n (parisiGridIndex n x)

theorem measurable_parisiGridRound (n : ℕ) : Measurable (parisiGridRound n) := by
  apply Measurable.subtype_mk
  change Measurable (fun x : Overlap =>
    (Nat.ceil ((n + 1 : ℕ) * (x : ℝ)) : ℝ) / (n + 1 : ℕ))
  exact (measurable_from_nat.comp
    (measurable_const.mul measurable_subtype_coe).nat_ceil).div_const _

theorem le_parisiGridRound (n : ℕ) (x : Overlap) :
    (x : ℝ) ≤ (parisiGridRound n x : ℝ) := by
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  change (x : ℝ) ≤ (Nat.ceil ((n + 1 : ℕ) * (x : ℝ)) : ℝ) / (n + 1 : ℕ)
  apply (le_div_iff₀ hd).mpr
  simpa [mul_comm] using Nat.le_ceil ((n + 1 : ℕ) * (x : ℝ))

theorem parisiGridRound_sub_lt_mesh (n : ℕ) (x : Overlap) :
    (parisiGridRound n x : ℝ) - (x : ℝ) < 1 / (n + 1 : ℕ) := by
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg hd.le x.property.1)
  change (Nat.ceil ((n + 1 : ℕ) * (x : ℝ)) : ℝ) / (n + 1 : ℕ) -
    (x : ℝ) < 1 / (n + 1 : ℕ)
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]
  have he : (1 / (n + 1 : ℕ) + (x : ℝ)) * (n + 1 : ℕ) =
      (n + 1 : ℕ) * (x : ℝ) + 1 := by field_simp; ring
  rw [he]
  exact hceil

theorem finite_range_parisiGridRound (n : ℕ) :
    (Set.range (parisiGridRound n)).Finite :=
  (Set.finite_range (parisiGridPoint n)).subset (by
    rintro _ ⟨x, rfl⟩
    exact ⟨parisiGridIndex n x, rfl⟩)

/-- The actual finite atomic grid approximation of an arbitrary Parisi measure. -/
noncomputable def parisiGridMeasure (μ : ParisiMeasure) (n : ℕ) : ParisiMeasure :=
  μ.map (parisiGridRound n)

theorem parisiCDF_grid_le (μ : ParisiMeasure) (n : ℕ) (t : ℝ) :
    parisiCDF (parisiGridMeasure μ n) t ≤ parisiCDF μ t := by
  unfold parisiCDF parisiGridMeasure
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_parisiGridRound n)
      (isClosed_le continuous_subtype_val continuous_const).measurableSet]
  apply ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) _)
  exact measure_mono (fun x hx => (le_parisiGridRound n x).trans hx)

theorem tendsto_parisiGridRound (x : Overlap) :
    Tendsto (fun n : ℕ => parisiGridRound n x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have hz : Tendsto (fun n : ℕ => (parisiGridRound n x : ℝ) - (x : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (le_parisiGridRound n x))
      (fun n => (parisiGridRound_sub_lt_mesh n x).le)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_add_cancel, zero_add] using hz.add_const (x : ℝ)

theorem ae_mem_range_parisiGridRound (μ : ParisiMeasure) (n : ℕ) :
    ∀ᵐ q ∂(parisiGridMeasure μ n : Measure Overlap), q ∈ Set.range (parisiGridRound n) := by
  rw [parisiGridMeasure, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_parisiGridRound n).aemeasurable
    (finite_range_parisiGridRound n).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun q => ⟨q, rfl⟩)

/-- The approximating probability measure has genuinely finite support. -/
theorem finite_support_parisiGridMeasure (μ : ParisiMeasure) (n : ℕ) :
    (parisiGridMeasure μ n : Measure Overlap).support.Finite :=
  (finite_range_parisiGridRound n).subset
    ((parisiGridMeasure μ n : Measure Overlap).support_subset_of_isClosed
      (finite_range_parisiGridRound n).isClosed (ae_mem_range_parisiGridRound μ n))

/-- The L1 distance between the cumulative distribution functions. -/
noncomputable def parisiCDFDistance (μ ν : ParisiMeasure) : ℝ :=
  ∫ t in (0 : ℝ)..1, |parisiCDF μ t - parisiCDF ν t|

theorem parisiCDFDistance_nonneg (μ ν : ParisiMeasure) :
    0 ≤ parisiCDFDistance μ ν :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)

/-- Upward rounding approximates every actual Parisi measure in CDF L1. -/
theorem parisiCDFDistance_grid_le (μ : ParisiMeasure) (n : ℕ) :
    parisiCDFDistance μ (parisiGridMeasure μ n) ≤ 1 / (n + 1 : ℕ) := by
  exact parisiCDF_map_L1_bound μ (parisiGridRound n) (measurable_parisiGridRound n)
    _ (le_parisiGridRound n) (fun q => (parisiGridRound_sub_lt_mesh n q).le)

theorem parisiCDF_grid_norm_integral_le (μ : ParisiMeasure) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖parisiCDF μ t - parisiCDF (parisiGridMeasure μ n) t‖) ≤
      1 / (n + 1 : ℕ) := by
  simpa only [Real.norm_eq_abs, parisiCDFDistance] using parisiCDFDistance_grid_le μ n

theorem tendsto_parisiCDFDistance_grid (μ : ParisiMeasure) :
    Tendsto (fun n : ℕ => parisiCDFDistance μ (parisiGridMeasure μ n))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => parisiCDFDistance_nonneg _ _)
    (fun n => parisiCDFDistance_grid_le μ n)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end Paper
