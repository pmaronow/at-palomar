module

public import Paper.HJBGridCells

@[expose] public section

/-! # Time meshes starting at an arbitrary physical time

Taking the maximum with the starting time preserves the genuine grid cells.
Zero-width initial cells contribute nothing, while norm estimates telescope
through the remaining cells as actual interval integrals.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace Paper

def parisiGradientMeshTime (n : ℕ) (s : ℝ) (i : ℕ) : ℝ :=
  max s (hjbGridTime n i)

lemma monotone_hjbGridTime (n : ℕ) : Monotone (hjbGridTime n) := by
  intro i j hij
  unfold hjbGridTime
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hij

lemma parisiGradientMeshTime_mono (n : ℕ) (s : ℝ) :
    Monotone (parisiGradientMeshTime n s) :=
  monotone_const.max (monotone_hjbGridTime n)

@[simp] theorem parisiGradientMeshTime_zero (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    parisiGradientMeshTime n s 0 = s := by
  simp only [parisiGradientMeshTime, hjbGridTime, Nat.cast_zero, zero_div, max_eq_left hs]

@[simp] theorem parisiGradientMeshTime_terminal (n : ℕ) {s : ℝ} (hs : s ≤ 1) :
    parisiGradientMeshTime n s (n + 1) = 1 := by
  have he : hjbGridTime n (n + 1) = 1 := by
    unfold hjbGridTime
    exact div_self (by positivity)
  rw [parisiGradientMeshTime, he, max_eq_right hs]

lemma parisiGradientMeshTime_mem (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {i : ℕ} (hi : i ≤ n + 1) : parisiGradientMeshTime n s i ∈ Icc (0 : ℝ) 1 := by
  exact ⟨hs.1.trans (le_max_left _ _), max_le hs.2 (hjbGridTime_le_one n i hi)⟩

/-- A nonempty truncated cell ends at the original right grid boundary. -/
lemma parisiGradientMeshTime_step_lt_terminal (n : ℕ) (s : ℝ) (i : ℕ)
    (hlt : parisiGradientMeshTime n s i < parisiGradientMeshTime n s (i + 1)) :
    parisiGradientMeshTime n s (i + 1) = hjbGridTime n (i + 1) := by
  apply max_eq_right
  by_contra hn
  have hu : hjbGridTime n (i + 1) ≤ s := (lt_of_not_ge hn).le
  simp only [parisiGradientMeshTime, max_eq_left hu] at hlt
  exact (not_lt_of_ge (le_max_left s (hjbGridTime n i))) hlt

/-- Every nonempty truncated cell lies inside its actual Cole--Hopf grid cell. -/
lemma parisiGradientMeshTime_cell_subset (n : ℕ) (s : ℝ) (i : ℕ)
    (hlt : parisiGradientMeshTime n s i < parisiGradientMeshTime n s (i + 1)) :
    Icc (parisiGradientMeshTime n s i) (parisiGradientMeshTime n s (i + 1)) ⊆
      Icc (hjbGridTime n i) (hjbGridTime n (i + 1)) := by
  rw [parisiGradientMeshTime_step_lt_terminal n s i hlt]
  exact Icc_subset_Icc (le_max_right _ _) le_rfl

/-- Consecutive times either form an actual cell or coincide. -/
lemma parisiGradientMeshTime_step_cases (n : ℕ) (s : ℝ) (i : ℕ) :
    parisiGradientMeshTime n s i = parisiGradientMeshTime n s (i + 1) ∨
      parisiGradientMeshTime n s i < parisiGradientMeshTime n s (i + 1) :=
  eq_or_lt_of_le (parisiGradientMeshTime_mono n s (Nat.le_succ i))

/-- The norm of a telescoped expected gradient increment is bounded by the
single genuine error integral. This also accommodates zero-width cells. -/
theorem parisiGradientMesh_norm_telescope {G : Type*} [NormedAddCommGroup G]
    (F : ℕ → G) (E : ℝ → ℝ) (T : ℕ → ℝ) (N : ℕ)
    (hE : ∀ i, i < N → IntervalIntegrable E volume (T i) (T (i + 1)))
    (hcell : ∀ i, i < N → ‖F (i + 1) - F i‖ ≤ ∫ r in T i..T (i + 1), E r) :
    ‖F N - F 0‖ ≤ ∫ r in T 0..T N, E r := by
  have htel : (∑ i ∈ Finset.range N, (F (i + 1) - F i)) = F N - F 0 := Finset.sum_range_sub F N
  rw [← htel]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖F (i + 1) - F i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, ∫ r in T i..T (i + 1), E r :=
      Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals hE

lemma parisiGradientMesh_integral_le_full {E : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hE : IntervalIntegrable E volume (0 : ℝ) 1)
    (hEnon : ∀ r, 0 ≤ E r) :
    (∫ r in s..1, E r) ≤ ∫ r in (0 : ℝ)..1, E r := by
  exact intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
    (.of_forall hEnon) hE

lemma parisiGradientMesh_cdfError_bound (μ ν : ParisiMeasure) (n : ℕ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ r in s..1, ‖parisiCDF μ r - parisiCDF (parisiGridMeasure ν n) r‖) ≤
      parisiCDFDistance μ (parisiGridMeasure ν n) := by
  have hi : IntervalIntegrable (fun r => ‖parisiCDF μ r - parisiCDF (parisiGridMeasure ν n) r‖)
      volume (0 : ℝ) 1 :=
    (((parisiCDF_monotone μ).intervalIntegrable (a := (0 : ℝ)) (b := 1)).sub
      ((parisiCDF_monotone (parisiGridMeasure ν n)).intervalIntegrable (a := (0 : ℝ)) (b := 1))).norm
  simpa only [Real.norm_eq_abs, parisiCDFDistance] using
    parisiGradientMesh_integral_le_full hs hi (fun r => norm_nonneg _)

end Paper
