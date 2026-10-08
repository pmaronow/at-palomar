module

public import Paper.HJBEndpoint

@[expose] public section

/-! # Finite telescope of actual expected control costs

The stochastic endpoint terms, absolutely integrable time costs, and
deterministic coefficient errors are all telescoped as genuine integrals.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Paper

def hjbExpectedCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ → Ω → ℝ) (a b : ℝ) : ℝ := ∫ ω, (∫ t in a..b, C t ω) ∂P

theorem sum_hjbExpectedCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ → Ω → ℝ) (T : ℕ → ℝ) (N : ℕ)
    (ht : ∀ ω i, i < N → IntervalIntegrable (fun t => C t ω) volume (T i) (T (i + 1)))
    (hi : ∀ i, i < N → Integrable (fun ω => ∫ t in T i..T (i + 1), C t ω) P) :
    (∑ i ∈ Finset.range N, hjbExpectedCost P C (T i) (T (i + 1))) =
      hjbExpectedCost P C (T 0) (T N) := by
  unfold hjbExpectedCost
  rw [← integral_finset_sum _ (fun i hi0 => hi i (Finset.mem_range.mp hi0))]
  apply integral_congr_ae
  exact .of_forall fun ω => intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi0 => ht ω i hi0)

theorem hjb_expected_cells_telescope_upper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : ℝ → Ω → ℝ) (E : ℝ → ℝ) (T : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℝ)
    (ht : ∀ ω i, i < N → IntervalIntegrable (fun t => C t ω) volume (T i) (T (i + 1)))
    (hi : ∀ i, i < N → Integrable (fun ω => ∫ t in T i..T (i + 1), C t ω) P)
    (hE : ∀ i, i < N → IntervalIntegrable E volume (T i) (T (i + 1)))
    (hcell : ∀ i, i < N → F (i + 1) - hjbExpectedCost P C (T i) (T (i + 1)) ≤
      F i + ∫ t in T i..T (i + 1), E t) :
    F N - hjbExpectedCost P C (T 0) (T N) ≤ F 0 + ∫ t in T 0..T N, E t := by
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun i hi0 => by
    have hh := hcell i (Finset.mem_range.mp hi0)
    show F (i + 1) - F i - hjbExpectedCost P C (T i) (T (i + 1)) ≤
      ∫ t in T i..T (i + 1), E t
    linarith)
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub,
    sum_hjbExpectedCost P C T N ht hi,
    intervalIntegral.sum_integral_adjacent_intervals hE] at hh
  linarith

theorem hjb_expected_cells_telescope_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : ℝ → Ω → ℝ) (E : ℝ → ℝ) (T : ℕ → ℝ)
    (N : ℕ) (F : ℕ → ℝ) (Q : ℝ)
    (ht : ∀ ω i, i < N → IntervalIntegrable (fun t => C t ω) volume (T i) (T (i + 1)))
    (hi : ∀ i, i < N → Integrable (fun ω => ∫ t in T i..T (i + 1), C t ω) P)
    (hE : ∀ i, i < N → IntervalIntegrable E volume (T i) (T (i + 1)))
    (hcell : ∀ i, i < N → F i - (∫ t in T i..T (i + 1), E t) -
      Q * (T (i + 1) - T i) ≤
        F (i + 1) - hjbExpectedCost P C (T i) (T (i + 1))) :
    F 0 - (∫ t in T 0..T N, E t) - Q * (T N - T 0) ≤
      F N - hjbExpectedCost P C (T 0) (T N) := by
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun i hi0 => by
    have hh := hcell i (Finset.mem_range.mp hi0)
    show -(∫ t in T i..T (i + 1), E t) - Q * (T (i + 1) - T i) ≤
      F (i + 1) - F i - hjbExpectedCost P C (T i) (T (i + 1))
    linarith)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub, intervalIntegral.sum_integral_adjacent_intervals hE,
    Finset.sum_sub_distrib, Finset.sum_range_sub,
    sum_hjbExpectedCost P C T N ht hi] at hh
  linarith

end Paper
