module

public import Targets.Section4SquaredSlopeDerivative
public import Targets.Section4UPrime
public import Targets.CoupledReplicaWeights

@[expose] public section

/-!
# The actual second variance derivative of Talagrand's U

At the original mass every unchanged outer potential is independent of the
split variance. The proved normalized-observable rule therefore propagates
(4.16) without a covariance correction. This identifies Q' and U'' as the
negative nested normalized square of the actual inner spatial Hessian.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The scalar one-coordinate form of the actual paired normalized mean. -/
theorem pairedTiltMean_scalar_integral {A G : ℝ → ℝ} (hA : Measurable A) (hG : Measurable G)
    (m v : ℝ) (y : Fin 1 → ℝ) :
    pairedTiltMean m v (fun z => A (z 0)) (fun z => G (z 0)) y =
      ∫ z, G (y 0 + Real.sqrt v * z) * tiltWeight m v A (y 0) z ∂(gaussianReal 0 1) := by
  have hw (z : Fin 1 → ℝ) : tiltWeightPi 1 m v (fun u => A (u 0)) y z =
      tiltWeight m v A (y 0) (z 0) := by
    simp only [tiltWeightPi, tiltWeight]
    by_cases hm : m = 0
    · simp only [hm, if_true]
    · rw [if_neg hm, if_neg hm,
        integral_piGauss_eval (0 : Fin 1) (fun z => Real.exp (m * A (y 0 + Real.sqrt v * z)))
          (((hA.comp (by fun_prop)).const_mul m).exp.aestronglyMeasurable)]
  simp only [pairedTiltMean, hw]
  exact integral_piGauss_eval (0 : Fin 1)
    (fun z => G (y 0 + Real.sqrt v * z) * tiltWeight m v A (y 0) z)
    (((hG.comp (by fun_prop)).mul (measurable_tiltWeight hA (y 0))).aestronglyMeasurable)

/-- The positive normalized squared-Hessian factor in (4.45), before choosing
the baseline mass and the final external field. -/
noncomputable def section4VarianceR {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (m : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun v =>
      pairedSecondMean (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
        (fun _ y => parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
        (fun _ y => (stepD2 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
          (parisiFSecond s β (k + 2 - r)) m v (y 0)) ^ 2)
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 2 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) - s.q (k + 2 - (k + 2 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (y 0))
        (section4VarianceR s β r m j v)

theorem measurable_section4VarianceR {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) (j : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => section4VarianceR s β r m j v p.1 p.2) := by
  induction j with
  | zero =>
    unfold section4VarianceR
    apply measurable_pairedSecondMean
    · exact (measurable_parisiStep (parisiF_measurable s β _) m v).comp ((measurable_pi_apply 0).comp measurable_snd)
    · exact ((measurable_stepD2 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1
        (parisiF_C2_props s β _).2.2 m v).pow_const 2).comp ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    unfold section4VarianceR
    apply measurable_pairedSecondMean
    · exact (scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd)
    · exact ih

private theorem scalar_lift_growth {A : ℝ → ℝ} (hA : HasLinearGrowth A) (hAm : Measurable A) :
    GuerraGrowth (fun y : Fin 1 → ℝ => A (y 0)) := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  refine ⟨hAm.comp (measurable_pi_apply 0), C, D, hD, fun y => ?_⟩
  simpa [l1] using hb (y 0)

private theorem pairedTiltMean_unit_range {n : ℕ} {A G : (Fin n → ℝ) → ℝ}
    (hA : GuerraGrowth A) (hGm : Measurable G) (hG : ∀ y, G y ∈ Set.Icc 0 1)
    (m v : ℝ) (x : Fin n → ℝ) : pairedTiltMean m v A G x ∈ Set.Icc 0 1 := by
  have hb (y : Fin n → ℝ) : |G y| ≤ 1 := by rw [abs_of_nonneg (hG y).1]; exact (hG y).2
  exact ⟨pairedTiltMean_nonneg hA (fun y => (hG y).1) m v x,
    (le_abs_self _).trans (pairedTiltMean_abs_le hA hGm hb x)⟩

/-- The Hessian-square factor remains in [0,1] at every outer depth. -/
theorem section4VarianceR_mem_Icc {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceR s β r m j v x y ∈ Set.Icc 0 1 := by
  induction j generalizing x y with
  | zero =>
    have hAm := parisiF_measurable s β (k + 2 - r)
    have hB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 (parisiF_C2_props s β _).1
      (parisiF_hasLinearGrowth s β _) hAm (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
    apply pairedTiltMean_unit_range
      (scalar_lift_growth (hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm m v)
        (measurable_parisiStep hAm m v))
      (((measurable_stepD2 hAm (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2 m v).pow_const 2).comp
        (measurable_pi_apply 0))
    intro z
    refine ⟨sq_nonneg _, ?_⟩
    dsimp only [Function.comp_apply]
    nlinarith [hB.abs_second_le_one (z 0), sq_abs (stepD2 (parisiF s β (k + 2 - r))
      (parisiFDeriv s β (k + 2 - r)) (parisiFSecond s β (k + 2 - r)) m v (z 0)),
      abs_nonneg (stepD2 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) (parisiFSecond s β (k + 2 - r)) m v (z 0))]
  | succ j ih =>
    exact pairedTiltMean_unit_range
      (scalar_lift_growth (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1)
      ((measurable_section4VarianceR s β r m j v).comp (measurable_const.prodMk measurable_id)) (ih x) _ _ y

private theorem section4VarianceQ_baseline_zero_eq {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β r (s.m (r - 1)) 0 v x y =
      splitBaselineSlopeQ (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
        (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1))) (y 0) v := by
  unfold section4VarianceQ pairedSecondMean splitBaselineSlopeQ
  exact pairedTiltMean_scalar_integral (measurable_parisiStep (parisiF_measurable s β _) _ _)
    ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 _ _).pow_const 2) _ _ _

private theorem section4VarianceR_zero_eq {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceR s β r m 0 v x y =
      ∫ z, (stepD2 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
        (parisiFSecond s β (k + 2 - r)) m v (y 0 + Real.sqrt (β ^ 2 * (s.q r - s.q (r - 1)) - v) * z)) ^ 2 *
        tiltWeight (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
          (parisiStep m v (parisiF s β (k + 2 - r))) (y 0) z ∂(gaussianReal 0 1) := by
  unfold section4VarianceR pairedSecondMean
  exact pairedTiltMean_scalar_integral (measurable_parisiStep (parisiF_measurable s β _) _ _)
    ((measurable_stepD2 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1
      (parisiF_C2_props s β _).2.2 _ _).pow_const 2) _ _ _

/-- Actual Q differentiation through every unchanged outer level. The zero
baseline velocity of each outer potential is reused from the proved (4.11). -/
theorem section4VarianceQ_baseline_deriv_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {j : ℕ} (hj : j ≤ r - 1) :
    CoupledParamDeriv (section4VarianceQ s β r (s.m (r - 1)) j)
      (fun v x y => -section4VarianceR s β r (s.m (r - 1)) j v x y)
      (Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) 1 := by
  have hm : s.m (r - 1) ∈ Set.Icc 0 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hGb (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) : |section4VarianceQ s β r (s.m (r - 1)) j v x y| ≤ 1 := by
    have H := section4VarianceQ_mem_Icc s β r hm j v x y
    rw [abs_of_nonneg H.1]
    exact H.2
  have hRb (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) : |-section4VarianceR s β r (s.m (r - 1)) j v x y| ≤ 1 := by
    have H := section4VarianceR_mem_Icc s β r hm j v x y
    rw [abs_neg, abs_of_nonneg H.1]
    exact H.2
  induction j with
  | zero =>
    refine ⟨?_, fun v _ => measurable_section4VarianceQ s β r _ 0 v,
      fun v _ => (measurable_section4VarianceR s β r _ 0 v).neg,
      ⟨1, 0, le_rfl, fun v _ x y => by simpa using hGb 0 v x y⟩, fun v _ x y => hRb 0 v x y⟩
    intro v hv x y
    simp only [section4VarianceQ_baseline_zero_eq, section4VarianceR_zero_eq]
    exact hasDerivAt_splitBaselineSlopeQ_parisiF s β (k + 2 - r) hm _ (y 0) hv
  | succ j ih =>
    have hp := section4VarianceD_props s β hr0 hr hm le_rfl (j := j) (by omega)
    have he : section4VarianceD s β r (s.m (r - 1)) j = fun _ _ _ => 0 := by
      funext v x y
      simp only [section4VarianceD_eq_massGap_mul, sub_self, zero_div, zero_mul]
    rw [he] at hp
    refine ⟨?_, fun v _ => measurable_section4VarianceQ s β r _ (j + 1) v,
      fun v _ => (measurable_section4VarianceR s β r _ (j + 1) v).neg,
      ⟨1, 0, le_rfl, fun v _ x y => by simpa using hGb (j + 1) v x y⟩,
      fun v _ x y => hRb (j + 1) v x y⟩
    intro v hv x y
    have H := hasDerivAt_pairedSecondMean hp (ih (by omega))
      (fun w _ x y => hGb j w x y) (Ioo_mem_nhds hv.1 hv.2) x y
      (m := s.m (k + 2 - (k + 2 - r + 2 + j)))
      (v := β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) - s.q (k + 2 - (k + 2 - r + 2 + j))))
    simpa only [section4VarianceQ, section4VarianceR, mul_zero, add_zero, pairedSecondMean,
      pairedTiltMean, zero_mul, integral_zero, sub_zero, neg_mul, integral_neg] using! H

/-- The actual nested positive Hessian-square factor at the external field. -/
noncomputable def section4THessianSquare {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (v : ℝ) : ℝ :=
  section4VarianceR s β r (s.m (r - 1)) (r - 1) v 0 (fun _ => h)

theorem section4THessianSquare_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (v : ℝ) : section4THessianSquare s β h r v ∈ Set.Icc 0 1 :=
  section4VarianceR_mem_Icc s β r ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ _ v _ _

/-- Actual full normalized Q derivative, with no omitted outer terms. -/
theorem hasDerivAt_section4TVarianceQ_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4TVarianceQ s β h r (s.m (r - 1))) (-section4THessianSquare s β h r v) v :=
  (section4VarianceQ_baseline_deriv_props s β hr0 hr le_rfl).deriv v hv 0 (fun _ => h)

/-- Talagrand's actual identity (4.45): U'' is the negative normalized square
of the inner spatial Hessian, with all remaining outer tilts retained. -/
theorem hasDerivAt_deriv_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (deriv (section4U s β h r)) (-section4THessianSquare s β h r v) v := by
  apply (hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hv).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
  exact (hasDerivAt_section4U s β h hr0 hr hm hw).deriv

/-- The second derivative lies in [-1,0], uniformly in recursion depth. -/
theorem deriv2_section4U_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (deriv (section4U s β h r)) v ∈ Set.Icc (-1) 0 := by
  rw [(hasDerivAt_deriv_section4U s β h hr0 hr hm hv).deriv]
  have H := section4THessianSquare_mem_Icc s β h hr v
  constructor <;> linarith [H.1, H.2]

end SpinGlass.Targets
