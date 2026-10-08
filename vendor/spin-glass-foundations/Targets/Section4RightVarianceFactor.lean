module

public import Targets.Section4RightMassDerivative
public import Targets.Section4VarianceFactorContinuity
public import Targets.Section4USecond
public import Targets.ParisiThirdUniform

@[expose] public section

/-!
# Normalized squared-slope factor for the actual right insertion

The varying mass is the outer mass of the split. Removing the mass-gap
prefactor from the actual variance derivative defines its normalized factor
without division, including at equal masses. Only fixed-variance mass
continuity is needed for the mixed derivative argument.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The normalized actual right split observable followed by its unchanged
outer levels. The first field is the paired API's dummy coordinate. -/
noncomputable def section4RightVarianceQ {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) : ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun v => pairedSecondMean m v
      (fun _ y => parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
        (parisiF s β (k + 1 - r)) (y 0))
      (fun _ y => (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
        (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (y 0)) ^ 2)
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 1 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 1 - r + 2 + j) + 1) -
          s.q (k + 2 - (k + 1 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v)
          (k + 1 - r + 2 + j) (y 0))
        (section4RightVarianceQ s β r m j v)

/-- Exact factorization at every formal mass and variance, with no division
by the mass gap. -/
theorem section4RightVarianceD_eq_massGap_mul {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4RightVarianceD s β r m j v x y =
      (m - s.m r) / 2 * section4RightVarianceQ s β r m j v x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    simp only [section4RightVarianceD, section4RightVarianceQ, pairedSecondMean,
      pairedTiltMean, ih, mul_assoc, integral_const_mul]

/-- Spatial measurability of the actual normalized factor. -/
theorem measurable_section4RightVarianceQ {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) (j : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      section4RightVarianceQ s β r m j v p.1 p.2) := by
  induction j with
  | zero =>
    unfold section4RightVarianceQ
    apply measurable_pairedSecondMean
    · exact (measurable_parisiStep (parisiF_measurable s β _) _ _).comp
        ((measurable_pi_apply 0).comp measurable_snd)
    · exact ((measurable_stepD1 (parisiF_measurable s β _)
        (parisiF_C2_props s β _).2.1 _ _).pow_const 2).comp
        ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    unfold section4RightVarianceQ
    apply measurable_pairedSecondMean
    · exact (scalarFieldCascade_props _ _ _).1.comp
        ((measurable_pi_apply 0).comp measurable_snd)
    · exact ih

/-- Normalized means preserve the unit interval. The inserted outer mass is
arbitrary; only the fixed original inner mass needs its physical bounds. -/
theorem section4RightVarianceQ_mem_Icc {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m : ℝ) (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4RightVarianceQ s β r m j v x y ∈ Set.Icc 0 1 := by
  induction j generalizing x y with
  | zero =>
    have hAm := parisiF_measurable s β (k + 1 - r)
    have hc := hasParisiC2_parisiStep_nonneg
      (v := β ^ 2 * (s.q (r + 1) - s.q r) - v) (s.m_nonneg hr) (s.m_le_one hr)
      (parisiF_C2_props s β _).1 (parisiF_hasLinearGrowth s β _) hAm
      (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
    apply pairedTiltMean_mem_Icc
      (guerraGrowth_one (hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm _ _)
        (measurable_parisiStep hAm _ _))
      (((measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 _ _).pow_const 2).comp
        (measurable_pi_apply 0))
    intro z
    refine ⟨sq_nonneg _, ?_⟩
    dsimp only [Function.comp_apply]
    nlinarith [hc.abs_first_le_one (z 0), sq_abs
      (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
        (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (z 0)),
      abs_nonneg (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
        (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (z 0))]
  | succ j ih =>
    exact pairedTiltMean_mem_Icc
      (guerraGrowth_one (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1)
      ((measurable_section4RightVarianceQ s β r m j v).comp
        (measurable_const.prodMk measurable_id)) (ih x) _ _ y

/-- The normalized right factor at the root, after exactly `r` outer levels. -/
noncomputable def section4RightTVarianceQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) : ℝ := section4RightVarianceQ s β r m r v 0 (fun _ => h)

theorem section4RightTVarianceD_eq_massGap_mul {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) :
    section4RightTVarianceD s β h r m v =
      (m - s.m r) / 2 * section4RightTVarianceQ s β h r m v :=
  section4RightVarianceD_eq_massGap_mul s β r m r v 0 (fun _ => h)

theorem section4RightTVarianceQ_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m v : ℝ) :
    section4RightTVarianceQ s β h r m v ∈ Set.Icc 0 1 :=
  section4RightVarianceQ_mem_Icc s β hr m r v 0 (fun _ => h)

private theorem right_pairedTiltMean_eq_scalarTiltMean {A G : ℝ → ℝ}
    (hAm : Measurable A) (hGm : Measurable G) (m v : ℝ) (y : Fin 1 → ℝ) :
    pairedTiltMean m v (fun z => A (z 0)) (fun z => G (z 0)) y =
      scalarTiltMean A G m v (y 0) := by
  rw [pairedTiltMean_scalar_integral hAm hGm]
  by_cases hm : m = 0
  · simp [hm, scalarTiltMean, tiltP, tiltE, tiltWeight]
  · simp only [scalarTiltMean, tiltP, tiltE, tiltWeight, if_neg hm,
      ← mul_div_assoc, integral_div]

private theorem right_cascade_mass_continuous_paths {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {r : ℕ} (hr : r ≤ k + 1) {v : ℝ} (hv : 0 ≤ v)
    {j : ℕ} (hj : j ≤ r) :
    CoupledContinuousOn
      (fun m (_ y : Fin 1 → ℝ) => scalarFieldCascade
        (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v)
        (k + 1 - r + 2 + j) (y 0)) (Set.Icc 0 1) := by
  have H := section4RightMassD_props s β hr (V := v) ⟨hv, le_rfl⟩ hj
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2) 2 := by
    intro m hm
    constructor <;> linarith [hm.1, hm.2]
  obtain ⟨C, D, hD, hb⟩ := H.growth
  refine ⟨fun m hm => H.measurable m (hsub hm),
    ⟨C, D, hD, fun m hm => hb m (hsub hm)⟩, ?_⟩
  intro x y _hy hy
  have hc : ContinuousOn (fun p : ℝ × ℝ => scalarFieldCascade
      (fun l => section4Mass s r p.1 (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v)
      (k + 1 - r + 2 + j) p.2) (Set.Icc 0 1 ×ˢ Set.univ) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ 1
    · intro m _
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (scalarFieldCascade_props
          (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v)
          (k + 1 - r + 2 + j)).2.2 a b
    · intro a _ m hm
      exact (H.deriv m (hsub hm) 0 (fun _ => a)).continuousAt.continuousWithinAt
  exact hc.comp
    (continuousOn_id.prodMk ((continuous_apply 0).comp_continuousOn hy))
    (fun m hm => ⟨hm, Set.mem_univ _⟩)

/-- Fixed-variance mass continuity along physical-field paths, propagated
through all actual unchanged outer means. Baseline mass one is included. -/
theorem section4RightVarianceQ_mass_continuous_paths {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {r : ℕ} (hr : r ≤ k + 1) {v : ℝ} (hv : 0 ≤ v)
    {j : ℕ} (hj : j ≤ r) :
    ∀ x y : ℝ → Fin 1 → ℝ, ContinuousOn x (Set.Icc 0 1) →
      ContinuousOn y (Set.Icc 0 1) →
      ContinuousOn (fun m => section4RightVarianceQ s β r m j v (x m) (y m))
        (Set.Icc 0 1) := by
  induction j with
  | zero =>
    intro x y _hx hy
    let a := β ^ 2 * (s.q (r + 1) - s.q r) - v
    let A := parisiF s β (k + 1 - r)
    let B := parisiStep (s.m r) a A
    let G := fun z => (stepD1 A (parisiFDeriv s β (k + 1 - r)) (s.m r) a z) ^ 2
    have hAm := parisiF_measurable s β (k + 1 - r)
    have hC2 := hasParisiC2_parisiStep_nonneg (v := a)
      (s.m_nonneg hr) (s.m_le_one hr) (parisiF_C2_props s β (k + 1 - r)).1
      (parisiF_hasLinearGrowth s β _) hAm
      (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
    have hBc : Continuous B := continuous_iff_continuousAt.mpr fun z =>
      (hC2.1 z).continuousAt
    have hGc : Continuous G := (continuous_iff_continuousAt.mpr
      (fun z => (hC2.2.1 z).continuousAt)).pow 2
    have hGb (z : ℝ) : |G z| ≤ 1 := by
      dsimp [G]
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hC2.abs_first_le_one z,
        sq_abs (stepD1 A (parisiFDeriv s β (k + 1 - r)) (s.m r) a z),
        abs_nonneg (stepD1 A (parisiFDeriv s β (k + 1 - r)) (s.m r) a z)]
    have hmap : ContinuousOn (fun m => (m, v, y m 0)) (Set.Icc 0 1) :=
      continuousOn_id.prodMk (continuousOn_const.prodMk
        ((continuous_apply 0).comp_continuousOn hy))
    have HC := (continuous_scalarTiltMean_joint
      (hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm _ _)
      hBc hGc hGb).comp_continuousOn
        hmap
    convert HC using 1
    funext m
    exact right_pairedTiltMean_eq_scalarTiltMean hBc.measurable hGc.measurable m v (y m)
  | succ j ih =>
    intro x y hx hy
    exact continuousOn_pairedSecondMean_paths
      (right_cascade_mass_continuous_paths s β hr hv (by omega : j ≤ r)) isCompact_Icc
      (fun m _ => measurable_section4RightVarianceQ s β r m j v)
      (fun m _ xx yy => by
        have H := section4RightVarianceQ_mem_Icc s β hr m j v xx yy
        simpa only [abs_of_nonneg H.1] using H.2)
      (ih (by omega)) _ _ continuousOn_const x y hx hy

/-- The actual normalized right factor is mass-continuous at fixed
nonnegative variance, without dividing by its vanishing mass-gap coefficient. -/
theorem continuousOn_section4RightTVarianceQ_mass {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {v : ℝ} (hv : 0 ≤ v) :
    ContinuousOn (fun m => section4RightTVarianceQ s β h r m v) (Set.Icc 0 1) :=
  section4RightVarianceQ_mass_continuous_paths s β hr hv le_rfl
    (fun _ => 0) (fun _ _ => h) continuousOn_const continuousOn_const

end SpinGlass.Targets
