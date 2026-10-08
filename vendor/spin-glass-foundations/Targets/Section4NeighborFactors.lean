module

public import Targets.Section4USecond
public import Targets.Section4StationarityInterior

@[expose] public section

/-!
# Adjacent physical endpoint factors

At an overlap breakpoint the previous level's zero split variance and the
next level's full split variance describe the same original squared slope
and squared Hessian. The next level's zero outer variance disappears; its
remaining outer means match the previous recursion exactly. The identities
do not require strict gaps, positive masses, stationarity, or regularity.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- At zero variance the actual smoothed Hessian is the input Hessian,
independently of the mass, including mass zero. -/
theorem stepD2_parisiF_zero_variance {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m x : ℝ) :
    stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m 0 x =
      parisiFSecond s β j x := by
  have H := hasDerivAt_parisiStep_spatial_second (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1
    (parisiF_C2_props s β j).2.2 (parisiF_C2_props s β j).1 m 0 x
  have he : stepD1 (parisiF s β j) (parisiFDeriv s β j) m 0 = parisiFDeriv s β j := by
    funext y
    exact stepD1_parisiF_zero_variance s β j m y
  rw [he] at H
  exact H.unique ((parisiF_C2_props s β j).1.2.1 x)

private theorem neighbor_initial_full_Q {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β (r + 1) (s.m r) 0
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y = (parisiFDeriv s β (k + 2 - r) (y 0)) ^ 2 := by
  simp only [section4VarianceQ, Nat.add_sub_cancel, sub_self, pairedSecondMean_zero_variance]
  rw [show k + 2 - (r + 1) = k + 1 - r by omega,
    show k + 2 - r = (k + 1 - r) + 1 by omega, parisiFDeriv,
    show k + 1 - (k + 1 - r) = r by omega,
    show k + 2 - (k + 1 - r) = r + 1 by omega]

private theorem neighbor_initial_full_R {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (x y : Fin 1 → ℝ) :
    section4VarianceR s β (r + 1) (s.m r) 0
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y = (parisiFSecond s β (k + 2 - r) (y 0)) ^ 2 := by
  simp only [section4VarianceR, Nat.add_sub_cancel, sub_self, pairedSecondMean_zero_variance]
  rw [show k + 2 - (r + 1) = k + 1 - r by omega,
    show k + 2 - r = (k + 1 - r) + 1 by omega, parisiFSecond,
    show k + 1 - (k + 1 - r) = r by omega,
    show k + 2 - (k + 1 - r) = r + 1 by omega]

/-- Neighboring baseline squared-slope factors agree after aligning their
outer depths. The extra next-level zero-variance mean has been removed. -/
theorem section4VarianceQ_neighbor_full_eq_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) {j : ℕ} (hj : j ≤ r - 1) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β (r + 1) (s.m r) (j + 1)
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y =
      section4VarianceQ s β r (s.m (r - 1)) j 0 x y := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  have hfull : β ^ 2 * (s.q (r + 1) - s.q r) ∈
      Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q (r + 1 - 1))) := by
    simp only [Nat.add_sub_cancel]
    exact ⟨mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' (r + 1) (by omega) r (by omega))), le_rfl⟩
  induction j generalizing x y with
  | zero =>
    have hG : section4VarianceQ s β (r + 1) (s.m r) 0
        (β ^ 2 * (s.q (r + 1) - s.q r)) =
        fun _ y => (parisiFDeriv s β (k + 2 - r) (y 0)) ^ 2 := by
      funext x y
      exact neighbor_initial_full_Q s β hr0 hr x y
    change section4VarianceQ s β (r + 1) (s.m r) 1 _ x y = _
    conv_lhs => unfold section4VarianceQ
    dsimp only
    rw [hG]
    have hbase := section4Cascade_baseline s β (r := r + 1) (by omega) (by omega)
      hfull (j := 0) (by omega)
    simp only [Nat.add_sub_cancel] at hbase
    rw [hbase]
    simp only [section4VarianceQ, sub_zero, parisiStep_zero_var, stepD1_parisiF_zero_variance,
      Nat.add_zero, show k + 2 - (k + 2 - (r + 1) + 2) = r - 1 by omega,
      show r - 1 + 1 = r by omega, show k + 2 - (r + 1) + 1 = k + 2 - r by omega]
  | succ j ih =>
    have hG : section4VarianceQ s β (r + 1) (s.m r) (j + 1)
        (β ^ 2 * (s.q (r + 1) - s.q r)) = section4VarianceQ s β r (s.m (r - 1)) j 0 := by
      funext x y
      exact ih (by omega) x y
    change section4VarianceQ s β (r + 1) (s.m r) ((j + 1) + 1) _ x y = _
    conv_lhs => rw [section4VarianceQ]
    dsimp only
    rw [hG]
    conv_rhs => rw [section4VarianceQ]
    dsimp only
    have hbase := section4Cascade_baseline s β (r := r + 1) (by omega) (by omega)
      hfull (j := j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hbase
    rw [hbase, section4Cascade_baseline s β hr0 (by omega) hzero (j := j) (by omega),
      show k + 2 - (k + 2 - (r + 1) + 2 + (j + 1)) = k + 2 - (k + 2 - r + 2 + j) by omega,
      show k + 2 - (r + 1) + 1 + (j + 1) = k + 2 - r + 1 + j by omega]

/-- Neighboring baseline squared-Hessian factors obey the same exact
outer-depth alignment, without any analytic regularity hypothesis. -/
theorem section4VarianceR_neighbor_full_eq_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) {j : ℕ} (hj : j ≤ r - 1) (x y : Fin 1 → ℝ) :
    section4VarianceR s β (r + 1) (s.m r) (j + 1)
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y =
      section4VarianceR s β r (s.m (r - 1)) j 0 x y := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  have hfull : β ^ 2 * (s.q (r + 1) - s.q r) ∈
      Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q (r + 1 - 1))) := by
    simp only [Nat.add_sub_cancel]
    exact ⟨mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' (r + 1) (by omega) r (by omega))), le_rfl⟩
  induction j generalizing x y with
  | zero =>
    have hG : section4VarianceR s β (r + 1) (s.m r) 0
        (β ^ 2 * (s.q (r + 1) - s.q r)) =
        fun _ y => (parisiFSecond s β (k + 2 - r) (y 0)) ^ 2 := by
      funext x y
      exact neighbor_initial_full_R s β hr0 hr x y
    change section4VarianceR s β (r + 1) (s.m r) 1 _ x y = _
    conv_lhs => unfold section4VarianceR
    dsimp only
    rw [hG]
    have hbase := section4Cascade_baseline s β (r := r + 1) (by omega) (by omega)
      hfull (j := 0) (by omega)
    simp only [Nat.add_sub_cancel] at hbase
    rw [hbase]
    simp only [section4VarianceR, sub_zero, parisiStep_zero_var, stepD2_parisiF_zero_variance,
      Nat.add_zero, show k + 2 - (k + 2 - (r + 1) + 2) = r - 1 by omega,
      show r - 1 + 1 = r by omega, show k + 2 - (r + 1) + 1 = k + 2 - r by omega]
  | succ j ih =>
    have hG : section4VarianceR s β (r + 1) (s.m r) (j + 1)
        (β ^ 2 * (s.q (r + 1) - s.q r)) = section4VarianceR s β r (s.m (r - 1)) j 0 := by
      funext x y
      exact ih (by omega) x y
    change section4VarianceR s β (r + 1) (s.m r) ((j + 1) + 1) _ x y = _
    conv_lhs => rw [section4VarianceR]
    dsimp only
    rw [hG]
    conv_rhs => rw [section4VarianceR]
    dsimp only
    have hbase := section4Cascade_baseline s β (r := r + 1) (by omega) (by omega)
      hfull (j := j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hbase
    rw [hbase, section4Cascade_baseline s β hr0 (by omega) hzero (j := j) (by omega),
      show k + 2 - (k + 2 - (r + 1) + 2 + (j + 1)) = k + 2 - (k + 2 - r + 2 + j) by omega,
      show k + 2 - (r + 1) + 1 + (j + 1) = k + 2 - r + 1 + j by omega]

/-- The normalized squared-slope factors at neighboring physical endpoints
are equal, including every zero mass, zero gap, and beta zero. -/
theorem section4TVarianceQ_neighbor_full_eq_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) :
    section4TVarianceQ s β h (r + 1) (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r)) =
      section4TVarianceQ s β h r (s.m (r - 1)) 0 := by
  have H := section4VarianceQ_neighbor_full_eq_zero s β hr0 hr (j := r - 1) le_rfl
    (0 : Fin 1 → ℝ) (fun _ => h)
  simpa only [section4TVarianceQ, Nat.add_sub_cancel, show r - 1 + 1 = r by omega] using H

/-- The actual squared-Hessian factors also agree at neighboring physical
endpoints. No stationarity or higher-derivative input is needed. -/
theorem section4THessianSquare_neighbor_full_eq_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) :
    section4THessianSquare s β h (r + 1) (β ^ 2 * (s.q (r + 1) - s.q r)) =
      section4THessianSquare s β h r 0 := by
  have H := section4VarianceR_neighbor_full_eq_zero s β hr0 hr (j := r - 1) le_rfl
    (0 : Fin 1 → ℝ) (fun _ => h)
  simpa only [section4THessianSquare, Nat.add_sub_cancel, show r - 1 + 1 = r by omega] using H

end SpinGlass.Targets
