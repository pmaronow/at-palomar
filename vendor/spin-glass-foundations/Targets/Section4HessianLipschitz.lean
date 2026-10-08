module

public import Targets.Section4HessianRegularity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# No-loss propagation of Hessian-square variance regularity

At the baseline mass the unchanged outer potentials are independent of the
split variance. Their normalized positive averages are contractions for uniform
observable differences. A Lipschitz estimate for the genuine scalar initial
Hessian-square integral therefore reaches the final Section 4 factor with
exactly the same constant, including both variance endpoints and mass zero.

The scalar estimate is an explicit hypothesis, not a conclusion of this file.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A fixed normalized tilt does not enlarge a uniform difference bound.
Integrability is reused from the existing bounded-observable theorem. -/
theorem pairedTiltMean_abs_sub_le {n : ℕ}
    {A G H : (Fin n → ℝ) → ℝ} {B C D m v : ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hH : Measurable H)
    (hGB : ∀ y, |G y| ≤ B) (hHC : ∀ y, |H y| ≤ C)
    (hsub : ∀ y, |G y - H y| ≤ D) (x : Fin n → ℝ) :
    |pairedTiltMean m v A G x - pairedTiltMean m v A H x| ≤ D := by
  have heq : pairedTiltMean m v A G x - pairedTiltMean m v A H x =
      pairedTiltMean m v A (fun y => G y - H y) x := by
    simp only [pairedTiltMean, sub_mul]
    exact (integral_sub (integrable_pairedTiltMean hA hG hGB x)
      (integrable_pairedTiltMean hA hH hHC x)).symm
  rw [heq]
  exact pairedTiltMean_abs_le hA (hG.sub hH) hsub x

private theorem hessianLipschitz_scalar_growth {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) :
    GuerraGrowth (fun y : Fin 1 → ℝ => A (y 0)) := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  refine ⟨hAm.comp (measurable_pi_apply 0), C, D, hD, fun y => ?_⟩
  simpa [l1] using hb (y 0)

/-- Every unchanged outer level preserves exactly the initial factor's
variance-Lipschitz constant, uniformly in both fields. -/
theorem section4VarianceR_baseline_lipschitz_of_initial_factor
    {k : ℕ} (s : RSBScheme k) (β L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y : Fin 1 → ℝ,
        |section4VarianceR s β r (s.m (r - 1)) 0 v x y -
          section4VarianceR s β r (s.m (r - 1)) 0 w x y| ≤ L * |v - w|)
    {j : ℕ} (hj : j ≤ r - 1)
    {v w : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (x y : Fin 1 → ℝ) :
    |section4VarianceR s β r (s.m (r - 1)) j v x y -
      section4VarianceR s β r (s.m (r - 1)) j w x y| ≤ L * |v - w| := by
  have hm : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  induction j generalizing x y with
  | zero => exact hLip v hv w hw x y
  | succ j ih =>
    simp only [section4VarianceR,
      section4Cascade_baseline s β hr0 hr hv (j := j) (by omega),
      section4Cascade_baseline s β hr0 hr hw (j := j) (by omega), pairedSecondMean]
    apply pairedTiltMean_abs_sub_le
      (hessianLipschitz_scalar_growth (parisiF_hasLinearGrowth s β _)
        (parisiF_measurable s β _))
      ((measurable_section4VarianceR s β r _ j v).comp (measurable_const.prodMk measurable_id))
      ((measurable_section4VarianceR s β r _ j w).comp (measurable_const.prodMk measurable_id))
      (B := 1) (C := 1)
    · intro z
      change |section4VarianceR s β r (s.m (r - 1)) j v x z| ≤ 1
      have H := section4VarianceR_mem_Icc s β r hm j v x z
      simpa only [abs_of_nonneg H.1] using H.2
    · intro z
      change |section4VarianceR s β r (s.m (r - 1)) j w x z| ≤ 1
      have H := section4VarianceR_mem_Icc s β r hm j w x z
      simpa only [abs_of_nonneg H.1] using H.2
    · intro z
      exact ih (by omega) x z

/-- The actual final Hessian-square factor inherits the initial estimate with
no dependence on the number of outer levels. -/
theorem section4THessianSquare_lipschitz_of_initial_factor
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y : Fin 1 → ℝ,
        |section4VarianceR s β r (s.m (r - 1)) 0 v x y -
          section4VarianceR s β r (s.m (r - 1)) 0 w x y| ≤ L * |v - w|)
    {v w : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤
      L * |v - w| :=
  section4VarianceR_baseline_lipschitz_of_initial_factor s β L hr0 hr hLip
    le_rfl hv hw 0 (fun _ => h)

/-- The zero-outer-depth Hessian-square observable is exactly its one-dimensional
Gaussian integral, for every mass and variance, including zero. -/
theorem section4VarianceR_initial_eq_scalar_integral {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) (m v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceR s β r m 0 v x y =
      ∫ z, (stepD2 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
        (parisiFSecond s β (k + 2 - r)) m v
          (y 0 + Real.sqrt (β ^ 2 * (s.q r - s.q (r - 1)) - v) * z)) ^ 2 *
        tiltWeight (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
          (parisiStep m v (parisiF s β (k + 2 - r))) (y 0) z ∂(gaussianReal 0 1) := by
  unfold section4VarianceR pairedSecondMean
  exact pairedTiltMean_scalar_integral (measurable_parisiStep (parisiF_measurable s β _) _ _)
    ((measurable_stepD2 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1
      (parisiF_C2_props s β _).2.2 _ _).pow_const 2) _ _ _

/-- Direct scalar-input adapter: a uniform-in-field estimate for the genuine
baseline Gaussian integral yields the final factor's Lipschitz estimate without
any loss in the constant. The scalar estimate is an explicit hypothesis. -/
theorem section4THessianSquare_lipschitz_of_scalar_integral
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hLip : let a := β ^ 2 * (s.q r - s.q (r - 1))
      let m := s.m (r - 1)
      let A := parisiF s β (k + 2 - r)
      let A' := parisiFDeriv s β (k + 2 - r)
      let A'' := parisiFSecond s β (k + 2 - r)
      ∀ v ∈ Set.Icc 0 a, ∀ w ∈ Set.Icc 0 a, ∀ x : ℝ,
        |(∫ z, (stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z)) ^ 2 *
            tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)) -
          (∫ z, (stepD2 A A' A'' m w (x + Real.sqrt (a - w) * z)) ^ 2 *
            tiltWeight m (a - w) (parisiStep m w A) x z ∂(gaussianReal 0 1))| ≤
          L * |v - w|)
    {v w : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤
      L * |v - w| := by
  apply section4THessianSquare_lipschitz_of_initial_factor s β h L hr0 hr
    (fun v hv w hw x y => ?_) hv hw
  simpa only [section4VarianceR_initial_eq_scalar_integral] using hLip v hv w hw (y 0)

/-- The scalar mean value theorem extends an interior derivative bound to a
closed-interval Lipschitz estimate. Only continuity is required at the endpoints;
the interval may degenerate. -/
theorem abs_sub_le_of_derivative_bound_on_open_interval
    {f f' : ℝ → ℝ} {a b L : ℝ} (hc : ContinuousOn f (Set.Icc a b))
    (hd : ∀ z ∈ Set.Ioo a b, HasDerivAt f (f' z) z)
    (hb : ∀ z ∈ Set.Ioo a b, |f' z| ≤ L)
    {v w : ℝ} (hv : v ∈ Set.Icc a b) (hw : w ∈ Set.Icc a b) :
    |f v - f w| ≤ L * |v - w| := by
  wlog hvw : v ≤ w generalizing v w
  · have H := this hw hv (le_of_not_ge hvw)
    simpa only [abs_sub_comm] using H
  rcases eq_or_lt_of_le hvw with heq | hlt
  · simp only [heq, sub_self, abs_zero, mul_zero, le_refl]
  obtain ⟨c, hc', heq⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (hc.mono (Set.Icc_subset_Icc hv.1 hw.2))
    (fun z hz => hd z ⟨hv.1.trans_lt hz.1, hz.2.trans_le hw.2⟩)
  have H := hb c ⟨hv.1.trans_lt hc'.1, hc'.2.trans_le hw.2⟩
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hlt)] at H
  have H' := (div_le_iff₀ (sub_pos.mpr hlt)).mp H
  calc
    |f v - f w| = |f w - f v| := abs_sub_comm _ _
    _ ≤ L * (w - v) := H'
    _ = L * |v - w| := by rw [abs_of_nonpos (sub_nonpos.mpr hvw)]; ring

/-- A uniform fieldwise derivative estimate only in the open initial variance
interval is enough for the final closed-interval factor bound. Endpoint
continuity is reused from the actual baseline recursion, including mass zero. -/
theorem section4THessianSquare_lipschitz_of_initial_derivative
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hderiv : ∀ x y, ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (dR v x y) v)
    (hbound : ∀ x y, ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      |dR v x y| ≤ L)
    {v w : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤
      L * |v - w| := by
  apply section4THessianSquare_lipschitz_of_initial_factor s β h L hr0 hr
    (fun v hv w hw x y => ?_) hv hw
  apply abs_sub_le_of_derivative_bound_on_open_interval
    (section4VarianceR_baseline_continuous_paths s β hr0 hr (j := 0) (by omega)
      (fun _ => x) (fun _ => y) continuousOn_const continuousOn_const)
    (hderiv x y) (hbound x y) hv hw

end SpinGlass.Targets
