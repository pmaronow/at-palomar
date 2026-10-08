module

public import Paper.GaussianDifferentiation
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Existence of the positive-field replica-symmetric fixed point

The actual Gaussian overlap map is continuous by dominated convergence, with
the dominating constant `1`. Its value at `q=0` is positive in positive field,
and its value at `q=1` is strictly less than `1`. The intermediate value theorem
therefore yields a fixed point strictly between zero and one.

This file proves existence. `FixedPointUnique.lean` also proves uniqueness.
-/

open MeasureTheory ProbabilityTheory

namespace Paper

/-- Continuity includes the variance-zero endpoint; no positive-variance
derivative or hidden fixed-point choice is required.
-/
theorem continuous_overlapMap (β h : ℝ) : Continuous (overlapMap β h) := by
  unfold overlapMap gaussianExpectation
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact (integrable_gaussian_tanh_sq β h q).aestronglyMeasurable
  · intro q
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (tanh_sq_lt_one (gaussianField β h q z)).le
  · exact integrable_const 1
  · filter_upwards with z
    have hc : Continuous (fun q : ℝ => gaussianField β h q z) := by
      unfold gaussianField
      fun_prop
    exact (gaussian_continuous_tanh.comp hc).pow 2

/-- The positive-field Gaussian fixed point exists in `(0,1)`.

The proof works for every real inverse-temperature parameter; the physical
positive-temperature specialization is stated separately below.
-/
theorem exists_positive_field_fixedPoint (β h : ℝ) (hh : 0 < h) :
    ∃ q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧ q = overlapMap β h q := by
  let f : ℝ → ℝ := fun q => overlapMap β h q - q
  have hc : Continuous f := (continuous_overlapMap β h).sub continuous_id
  have h0 : 0 < f 0 := by
    dsimp [f]
    rw [overlapMap_zero, sub_zero]
    exact sq_pos_of_pos (tanh_pos hh)
  have h1 : f 1 < 0 := by
    dsimp [f]
    exact sub_neg.mpr (overlapMap_lt_one β h 1)
  obtain ⟨q, hq, he⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨h1.le, h0.le⟩)
  have hfixed : q = overlapMap β h q := by
    dsimp [f] at he
    linarith
  exact ⟨q, ⟨fixedPoint_pos hh hq.1 hfixed, fixedPoint_lt_one hfixed⟩, hfixed⟩

/-- The paper's stated positive-temperature, positive-field existence result. -/
theorem exists_rs_fixedPoint (β h : ℝ) (_hβ : 0 < β) (hh : 0 < h) :
    ∃ q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧ q = overlapMap β h q :=
  exists_positive_field_fixedPoint β h hh

end Paper
