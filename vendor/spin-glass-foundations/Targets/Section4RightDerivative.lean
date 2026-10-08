module

public import Targets.Section4RightVariation
public import Targets.CoupledCascadeDeriv

@[expose] public section

/-!
# The full variance derivative of the dual Section 4 recursion

The checked reflected split derivative is propagated through the actual fixed
outer levels by the existing normalized parameter rule. Its absolute bound is
half the decreased mass gap, with no loss in depth. The derivative is asserted
only at positive interior split variance; endpoint continuity gives the closed
interval Lipschitz estimate. The last overlap interval and zero masses remain
included.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem right_pairedTiltMean_one {A G : ℝ → ℝ}
    (hA : Measurable A) (hG : Measurable G) (m v : ℝ) (y : Fin 1 → ℝ) :
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

/-- The explicit reflected split derivative and its normalized outer means.
The first field is a dummy coordinate for the existing one-coordinate API. -/
noncomputable def section4RightVarianceD {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (m : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun v x y => (m - s.m r) / 2 *
      pairedSecondMean m v
        (fun _ y => parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
          (parisiF s β (k + 1 - r)) (y 0))
        (fun _ y => (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
          (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (y 0)) ^ 2) x y
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 1 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 1 - r + 2 + j) + 1) - s.q (k + 2 - (k + 1 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j) (y 0))
        (section4RightVarianceD s β r m j v)

private theorem section4RightVarianceD_zero_eq {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m v : ℝ) (x y : Fin 1 → ℝ) :
    section4RightVarianceD s β r m 0 v x y = (m - s.m r) / 2 *
      ∫ z, (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
        (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (y 0 + Real.sqrt v * z)) ^ 2 *
          tiltWeight m v (parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
            (parisiF s β (k + 1 - r))) (y 0) z ∂(gaussianReal 0 1) := by
  simp only [section4RightVarianceD, pairedSecondMean]
  rw [right_pairedTiltMean_one
    (measurable_parisiStep (parisiF_measurable s β _) _ _)
    ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 _ _).pow_const 2)]

private theorem section4RightVarianceD_zero_bound {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hmm : m ≤ s.m r)
    (v : ℝ) (x y : Fin 1 → ℝ) :
    |section4RightVarianceD s β r m 0 v x y| ≤ (s.m r - m) / 2 := by
  let A := parisiF s β (k + 1 - r)
  let A' := parisiFDeriv s β (k + 1 - r)
  let w := β ^ 2 * (s.q (r + 1) - s.q r) - v
  let B := parisiStep (s.m r) w A
  let G := fun y => (stepD1 A A' (s.m r) w y) ^ 2
  have hAm := parisiF_measurable s β (k + 1 - r)
  have hB : HasLinearGrowth B := hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm _ _
  have hBm : Measurable B := measurable_parisiStep hAm _ _
  have hGm : Measurable G :=
    (measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 _ _).pow_const 2
  have hB2 := hasParisiC2_parisiStep_nonneg (v := w) (s.m_nonneg hr) (s.m_le_one hr)
    (parisiF_C2_props s β _).1 (parisiF_hasLinearGrowth s β _) hAm
    (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
  have hBG : GuerraGrowth (fun y : Fin 1 → ℝ => B (y 0)) := by
    obtain ⟨C, D, _, hD, hb⟩ := hB
    refine ⟨hBm.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
    intro y
    simpa [l1] using hb (y 0)
  have hGbound (y : Fin 1 → ℝ) : |G (y 0)| ≤ 1 := by
    dsimp [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hB2.abs_first_le_one (y 0), sq_abs (stepD1 A A' (s.m r) w (y 0)),
      abs_nonneg (stepD1 A A' (s.m r) w (y 0))]
  have H := pairedTiltMean_abs_le (m := m) (v := v) hBG
    (hGm.comp (measurable_pi_apply 0)) hGbound y
  simp only [Function.comp_def] at H
  change |(m - s.m r) / 2 * pairedTiltMean m v
    (fun y => B (y 0)) (fun y => G (y 0)) y| ≤ _
  rw [abs_mul, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmm) (by norm_num))]
  nlinarith [div_nonneg (sub_nonneg.mpr hmm) (show (0 : ℝ) ≤ 2 by norm_num)]

/-- All local analytic hypotheses for the actual right split, including a
uniform field-growth bound and a derivative bound independent of depth. -/
theorem section4RightVarianceD_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) :
    CoupledParamDeriv
      (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2) (y 0))
      (section4RightVarianceD s β r m 0)
      (Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) ((s.m r - m) / 2) := by
  let a := β ^ 2 * (s.q (r + 1) - s.q r)
  have hAm := parisiF_measurable s β (k + 1 - r)
  have hc := continuous_split_parisiStep (parisiF_hasLinearGrowth s β (k + 1 - r))
    (parisiF_C2_props s β _).1 (continuous_parisiFSecond s β _)
    ⟨s.m_nonneg hr, s.m_le_one hr⟩ hm a
  have hmap : Continuous (fun v : ℝ => (a - v, (0 : ℝ))) := by fun_prop
  have hc0 : Continuous (fun v : ℝ => parisiStep m v
      (parisiStep (s.m r) (a - v) (parisiF s β (k + 1 - r))) 0) := by
    simpa only [Function.comp_def, sub_sub_cancel] using
      hc.comp hmap
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc0.continuousOn
  refine ⟨?_, ?_, ?_, ⟨C, 1, zero_le_one, ?_⟩,
    fun v _ x y => section4RightVarianceD_zero_bound s β hr hmm v x y⟩
  · intro v hv x y
    simp only [section4RightVarianceD_zero_eq]
    exact hasDerivAt_section4RightCascade_split s β hr m (y 0) hv
  · intro v _
    exact (scalarFieldCascade_props _ _ _).1.comp
      ((measurable_pi_apply 0).comp measurable_snd)
  · intro v _
    apply (measurable_pairedSecondMean
      ((measurable_parisiStep hAm _ _).comp ((measurable_pi_apply 0).comp measurable_snd))
      (((measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 _ _).pow_const 2).comp
        ((measurable_pi_apply 0).comp measurable_snd)) _ _).const_mul
  · intro v hv x y
    have hb0 : |scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2) 0| ≤ C := by
      rw [section4RightCascade_split s β hr]
      simpa only [Real.norm_eq_abs] using! hC v ⟨hv.1.le, hv.2.le⟩
    have hLip := (scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2)).2.2 (y 0) 0
    have htri := abs_sub_le
      (scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2) (y 0))
      (scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2) 0) 0
    simp only [sub_zero] at hLip htri
    simp only [l1, Fin.sum_univ_one, one_mul]
    linarith [abs_nonneg (x 0)]

/-- The fixed outer normalized means preserve the same derivative bound.
There are exactly `r` outer levels in the right construction. -/
theorem section4RightVarianceD_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r)
    {j : ℕ} (hj : j ≤ r) :
    CoupledParamDeriv
      (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j) (y 0))
      (section4RightVarianceD s β r m j)
      (Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) ((s.m r - m) / 2) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using section4RightVarianceD_base_props s β hr hm hmm
  | succ j ih =>
    let p := k + 2 - (k + 1 - r + 2 + j)
    have hp : p < r := by dsimp [p]; omega
    have H := (ih (by omega)).secondStep (m := s.m p)
      (v := β ^ 2 * (s.q (p + 1) - s.q p)) isOpen_Ioo
      (s.m_nonneg (by omega))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega))))
    have he :
        (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + (j + 1)) (y 0)) =
        (fun v (_ : Fin 1 → ℝ) y => parisiStepPi 1 (s.m p)
          (β ^ 2 * (s.q (p + 1) - s.q p))
          (fun z => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
            (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j) (z 0)) y) := by
      funext v x y
      rw [show k + 1 - r + 2 + (j + 1) = (k + 1 - r + 2 + j) + 1 by omega,
        scalarFieldCascade]
      change parisiStep (section4Mass s r m p) (section5RightVariance s β r p v) _ _ = _
      simp only [section4Mass, section5RightVariance, if_pos hp]
      symm
      simpa using parisiStepPi_sum (n := 1) (s.m p) (β ^ 2 * (s.q (p + 1) - s.q p))
        (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1 y
    rw [he]
    exact H

/-- The explicit full-depth right variance derivative. -/
noncomputable def section4RightTVarianceD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) : ℝ := section4RightVarianceD s β r m r v 0 (fun _ => h)

/-- The genuine derivative of the full dual recursion, including the last
interval and zero masses, at interior split variance. -/
theorem hasDerivAt_section4RightT_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (section4RightT s β h r m) (section4RightTVarianceD s β h r m v) v := by
  have H := (section4RightVarianceD_props s β hr hm hmm (j := r) le_rfl).deriv
    v hv 0 (fun _ => h)
  have hi : k + 1 - r + 2 + r = k + 3 := by omega
  simpa only [hi, section4RightT, section4RightTVarianceD] using! H

/-- The full derivative has no loss in the number of outer levels. -/
theorem abs_deriv_section4RightT_variance_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |deriv (section4RightT s β h r m) v| ≤ (s.m r - m) / 2 := by
  rw [(hasDerivAt_section4RightT_variance s β h hr hm hmm hv).deriv]
  exact (section4RightVarianceD_props s β hr hm hmm (j := r) le_rfl).bound
    v hv 0 (fun _ => h)

/-- The actual right derivative is nonpositive, with the sharp mass-gap bound. -/
theorem deriv_section4RightT_variance_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    deriv (section4RightT s β h r m) v ∈ Set.Icc ((m - s.m r) / 2) 0 := by
  refine ⟨?_, ?_⟩
  · have H := abs_deriv_section4RightT_variance_le s β h hr hm hmm hv
    linarith [neg_abs_le (deriv (section4RightT s β h r m) v)]
  · have H := (antitoneOn_section4RightT s β h hr hm hmm).derivWithin_nonpos (x := v)
    rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hv.1 hv.2)] at H

private theorem section4RightT_decrement_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) (hvw : v ≤ w) :
    section4RightT s β h r m v - section4RightT s β h r m w ≤ (s.m r - m) / 2 * (w - v) := by
  have H := (convex_Icc (0 : ℝ) (β ^ 2 * (s.q (r + 1) - s.q r))).mul_sub_le_image_sub_of_le_deriv
    (continuousOn_section4RightT s β h hr hm) (f := section4RightT s β h r m)
    (C := (m - s.m r) / 2) ?_ ?_ v hv w hw hvw
  · linarith
  · intro u hu
    exact (hasDerivAt_section4RightT_variance s β h hr hm hmm
      (by simpa only [interior_Icc] using hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    exact (deriv_section4RightT_variance_mem_Icc s β h hr hm hmm
      (by simpa only [interior_Icc] using hu)).1

/-- Closed-interval Lipschitz control, obtained without endpoint derivatives.
The Lipschitz constant is half the decreased mass gap, independently of depth. -/
theorem section4RightT_variance_dist_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |section4RightT s β h r m v - section4RightT s β h r m w| ≤
      (s.m r - m) / 2 * |v - w| := by
  rcases le_total v w with hvw | hwv
  · rw [abs_of_nonneg (sub_nonneg.mpr (antitoneOn_section4RightT s β h hr hm hmm hv hw hvw)),
      abs_sub_comm v w, abs_of_nonneg (sub_nonneg.mpr hvw)]
    exact section4RightT_decrement_le s β h hr hm hmm hv hw hvw
  · rw [abs_sub_comm (section4RightT s β h r m v) _,
      abs_of_nonneg (sub_nonneg.mpr (antitoneOn_section4RightT s β h hr hm hmm hw hv hwv)),
      abs_of_nonneg (sub_nonneg.mpr hwv)]
    exact section4RightT_decrement_le s β h hr hm hmm hw hv hwv

end SpinGlass.Targets
