module

public import Paper.FixedPointUnique
public import Paper.PhysicalSKDisorder
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Identifying the trusted SK backend's canonical Gaussian parameters -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

/-- The paper's positive-field fixed point agrees with the backend's selector.
Uniqueness here is the independently proved Gaussian Stein argument. -/
theorem skBackend_rsQ_eq (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : 0 ≤ q) (hfixed : q = overlapMap β h q) : q = SpinGlass.AT.rsQ β h := by
  apply positive_field_fixedPoint_unique β h q (SpinGlass.AT.rsQ β h)
    hβ hh hq (SpinGlass.AT.rsQ_mem_Icc β h).1 hfixed
  have hp := SpinGlass.AT.rsQ_fixedPoint β h
  simpa [SpinGlass.AT.IsRSFixedPoint, SpinGlass.AT.standardGaussianExpectation,
    overlapMap, gaussianExpectation, gaussianField, add_comm] using hp

/-- The backend's algebraic AT index equals the paper's actual Gaussian sech moment. -/
theorem skBackend_atParameter_eq (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : 0 ≤ q) (hfixed : q = overlapMap β h q) :
    SpinGlass.AT.atParameter β h = atParameter β h q := by
  unfold SpinGlass.AT.atParameter
  rw [SpinGlass.AT.rsA_eq_gaussian_sech_fourth hβ hh,
    ← skBackend_rsQ_eq β h q hβ hh hq hfixed]
  simp [atParameter, sech, gaussianExpectation, SpinGlass.AT.standardGaussianExpectation,
    gaussianField, add_comm]

/-- The backend's RS value is exactly the displayed RS free-energy expression. -/
theorem skBackend_rsFreeEnergy_eq (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : 0 ≤ q) (hfixed : q = overlapMap β h q) :
    SpinGlass.AT.rsFreeEnergy β h = rsFreeEnergy β h q := by
  unfold SpinGlass.AT.rsFreeEnergy SpinGlass.AT.rsPathValue
  rw [← skBackend_rsQ_eq β h q hβ hh hq hfixed]
  simp [rsFreeEnergy, gaussianExpectation, gaussianField,
    SpinGlass.AT.standardGaussianExpectation, add_comm]

/-- A quantitative `M/n` comparison implies the physical free-energy limit. -/
theorem finiteSKFreeEnergy_tendsto_of_error_bound (β h q M : ℝ)
    (hbound : ∀ n : ℕ, 0 < n →
      0 ≤ rsFreeEnergy β h q - finiteSKFreeEnergy β h n ∧
      rsFreeEnergy β h q - finiteSKFreeEnergy β h n ≤ M / (n : ℝ)) :
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q)) := by
  have hzero : Tendsto (fun n : ℕ => M / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat M
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hevent := hzero.eventually (eventually_lt_nhds hε)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hineq := hbound n hnp
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hineq.1])]
  linarith [hineq.2]

end Paper
