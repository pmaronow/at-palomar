module

public import Targets.Section4NestedMonotone
public import Targets.CoupledCascadeDeriv

@[expose] public section

/-!
# The actual variance derivative through every Section 4 outer level

The two-step derivative (4.11) is propagated using the existing
`CoupledParamDeriv.secondStep` theorem at one Gaussian coordinate. The derivative
bound is preserved by the normalized tilted mean, independently of recursion
depth. All local regularity and uniform growth hypotheses are proved for the
actual scalar recursion.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem pairedTiltMean_one {A G : ℝ → ℝ} (hA : Measurable A) (hG : Measurable G)
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

/-- The explicit nested normalized mean giving the variance derivative. The
first field is a dummy coordinate used only to reuse the existing paired API. -/
noncomputable def section4VarianceD {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (m : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun v x y => (m - s.m (r - 1)) / 2 *
      pairedSecondMean (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
        (fun _ y => parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
        (fun _ y => (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
          m v (y 0)) ^ 2) x y
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 2 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) - s.q (k + 2 - (k + 2 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (y 0))
        (section4VarianceD s β r m j v)

private theorem section4VarianceD_zero_eq {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceD s β r m 0 v x y = (m - s.m (r - 1)) / 2 *
      ∫ z, (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
        m v (y 0 + Real.sqrt (β ^ 2 * (s.q r - s.q (r - 1)) - v) * z)) ^ 2 *
          tiltWeight (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
            (parisiStep m v (parisiF s β (k + 2 - r))) (y 0) z ∂(gaussianReal 0 1) := by
  simp only [section4VarianceD, pairedSecondMean]
  rw [pairedTiltMean_one
    (measurable_parisiStep (parisiF_measurable s β _) m v)
    ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 m v).pow_const 2)]

private theorem section4VarianceD_zero_bound {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} {m : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hmm : s.m (r - 1) ≤ m) (v : ℝ) (x y : Fin 1 → ℝ) :
    |section4VarianceD s β r m 0 v x y| ≤ (m - s.m (r - 1)) / 2 := by
  let A := parisiF s β (k + 2 - r)
  let A' := parisiFDeriv s β (k + 2 - r)
  let B := parisiStep m v A
  let G := fun y => (stepD1 A A' m v y) ^ 2
  have hAm := parisiF_measurable s β (k + 2 - r)
  have hB : HasLinearGrowth B := hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm m v
  have hBm : Measurable B := measurable_parisiStep hAm m v
  have hGm : Measurable G :=
    (measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 m v).pow_const 2
  have hB2 := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 (parisiF_C2_props s β _).1
    (parisiF_hasLinearGrowth s β _) hAm (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
  have hBG : GuerraGrowth (fun y : Fin 1 → ℝ => B (y 0)) := by
    obtain ⟨C, D, _, hD, hb⟩ := hB
    refine ⟨hBm.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
    intro y
    simpa [l1] using hb (y 0)
  have hGbound (y : Fin 1 → ℝ) : |G (y 0)| ≤ 1 := by
    dsimp [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hB2.abs_first_le_one (y 0), sq_abs (stepD1 A A' m v (y 0)),
      abs_nonneg (stepD1 A A' m v (y 0))]
  have H := pairedTiltMean_abs_le (m := s.m (r - 1))
    (v := β ^ 2 * (s.q r - s.q (r - 1)) - v) hBG
    (hGm.comp (measurable_pi_apply 0)) hGbound y
  simp only [Function.comp_def] at H
  change |(m - s.m (r - 1)) / 2 * pairedTiltMean (s.m (r - 1))
    (β ^ 2 * (s.q r - s.q (r - 1)) - v)
    (fun y => B (y 0)) (fun y => G (y 0)) y| ≤ _
  rw [abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hmm) (by norm_num))]
  nlinarith [div_nonneg (sub_nonneg.mpr hmm) (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Every analytic hypothesis for the actual split-level variance derivative,
uniformly on the full interior interval. -/
theorem section4VarianceD_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) :
    CoupledParamDeriv
      (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2) (y 0))
      (section4VarianceD s β r m 0)
      (Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) ((m - s.m (r - 1)) / 2) := by
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  have hAm := parisiF_measurable s β (k + 2 - r)
  have hc := continuous_split_parisiStep (parisiF_hasLinearGrowth s β (k + 2 - r))
    (parisiF_C2_props s β _).1 (continuous_parisiFSecond s β _) hm
    (s.m_nonneg (p := r - 1) (by omega)) a
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨?_, ?_, ?_, ⟨C, 1, zero_le_one, ?_⟩,
    fun v _ x y => section4VarianceD_zero_bound s β hm hmm v x y⟩
  · intro v hv x y
    simp only [section4Cascade_split s β hr0 hr, section4VarianceD_zero_eq]
    exact hasDerivAt_split_parisiF s β (k + 2 - r) hm (s.m (r - 1)) a (y 0) hv
  · intro v _
    exact (scalarFieldCascade_props _ _ _).1.comp
      ((measurable_pi_apply 0).comp measurable_snd)
  · intro v _
    apply (measurable_pairedSecondMean
      ((measurable_parisiStep hAm m v).comp ((measurable_pi_apply 0).comp measurable_snd))
      (((measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 m v).pow_const 2).comp
        ((measurable_pi_apply 0).comp measurable_snd)) _ _).const_mul
  · intro v hv x y
    have hb0 : |scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2) 0| ≤ C := by
      rw [section4Cascade_split s β hr0 hr]
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using! hC v ⟨hv.1.le, hv.2.le⟩
    have hLip := (scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2)).2.2 (y 0) 0
    have htri := abs_sub_le
      (scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2) (y 0))
      (scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2) 0) 0
    simp only [sub_zero] at hLip htri
    simp only [l1, Fin.sum_univ_one, one_mul]
    linarith [abs_nonneg (x 0)]

/-- Existing one-field parameter calculus propagates the actual split derivative
and its depth-independent bound through every remaining outer level. -/
theorem section4VarianceD_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {j : ℕ} (hj : j ≤ r - 1) :
    CoupledParamDeriv
      (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (y 0))
      (section4VarianceD s β r m j)
      (Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) ((m - s.m (r - 1)) / 2) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using section4VarianceD_base_props s β hr0 hr hm hmm
  | succ j ih =>
    let p := k + 2 - (k + 2 - r + 2 + j)
    have hp : p < r := by dsimp [p]; omega
    have hpn : p ≠ r := by omega
    have hpn' : ¬r < p := by omega
    have hpn'' : p + 1 ≠ r := by dsimp [p]; omega
    have H := (ih (by omega)).secondStep (m := s.m p)
      (v := β ^ 2 * (s.q (p + 1) - s.q p)) isOpen_Ioo
      (s.m_nonneg (by omega))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega))))
    have he :
        (fun v (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + (j + 1)) (y 0)) =
        (fun v (_ : Fin 1 → ℝ) y => parisiStepPi 1 (s.m p)
          (β ^ 2 * (s.q (p + 1) - s.q p))
          (fun z => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
            (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (z 0)) y) := by
      funext v x y
      rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
        scalarFieldCascade]
      change parisiStep (section4Mass s r m p) (section5Variance s β r p v) _ _ = _
      simp only [section4Mass, section5Variance, if_pos hp, if_neg hpn,
        if_neg hpn', if_neg hpn'']
      symm
      simpa using parisiStepPi_sum (n := 1) (s.m p) (β ^ 2 * (s.q (p + 1) - s.q p))
        (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1 y
    rw [he]
    exact H

/-- The explicit normalized outer cascade of the two-step derivative (4.11). -/
noncomputable def section4TVarianceD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) : ℝ :=
  section4VarianceD s β r m (r - 1) v 0 (fun _ => h)

/-- The variance derivative of the actual full Section 4 function, without
assuming differentiability of any nested integral. -/
theorem hasDerivAt_section4T_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4T s β h r m) (section4TVarianceD s β h r m v) v := by
  have H := (section4VarianceD_props s β hr0 hr hm hmm (j := r - 1) le_rfl).deriv
    v hv 0 (fun _ => h)
  have hi : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  simpa only [hi, section4T, section4TVarianceD] using! H

/-- The actual nested variance derivative has a bound independent of the level
count, including when the original outer mass is zero. -/
theorem abs_deriv_section4T_variance_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |deriv (section4T s β h r m) v| ≤ (m - s.m (r - 1)) / 2 := by
  rw [(hasDerivAt_section4T_variance s β h hr0 hr hm hmm hv).deriv]
  exact (section4VarianceD_props s β hr0 hr hm hmm (j := r - 1) le_rfl).bound
    v hv 0 (fun _ => h)

/-- The full scalar variance derivative is nonnegative and uniformly bounded. -/
theorem deriv_section4T_variance_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    deriv (section4T s β h r m) v ∈ Set.Icc 0 ((m - s.m (r - 1)) / 2) := by
  refine ⟨?_, (le_abs_self _).trans (abs_deriv_section4T_variance_le s β h hr0 hr hm hmm hv)⟩
  have H := (monotoneOn_section4T s β h hr0 hr hm hmm).derivWithin_nonneg (x := v)
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hv.1 hv.2)] at H

private theorem section4T_increment_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    section4T s β h r m w - section4T s β h r m v ≤ (m - s.m (r - 1)) / 2 * (w - v) := by
  apply (convex_Icc (0 : ℝ) (β ^ 2 * (s.q r - s.q (r - 1)))).image_sub_le_mul_sub_of_deriv_le
    (continuousOn_section4T s β h hr0 hr hm.1) ?_ ?_ v hv w hw hvw
  · intro u hu
    exact (hasDerivAt_section4T_variance s β h hr0 hr hm hmm
      (by simpa only [interior_Icc] using hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    exact (deriv_section4T_variance_mem_Icc s β h hr0 hr hm hmm
      (by simpa only [interior_Icc] using hu)).2

/-- Endpoint-safe Lipschitz control in the split variance. The constant is
half the inserted mass gap, independently of the number of outer levels. -/
theorem section4T_variance_dist_le {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4T s β h r m v - section4T s β h r m w| ≤ (m - s.m (r - 1)) / 2 * |v - w| := by
  rcases le_total v w with hvw | hwv
  · rw [abs_sub_comm (section4T s β h r m v) _, abs_sub_comm v w,
      abs_of_nonneg (sub_nonneg.mpr (monotoneOn_section4T s β h hr0 hr hm hmm hv hw hvw)),
      abs_of_nonneg (sub_nonneg.mpr hvw)]
    exact section4T_increment_le s β h hr0 hr hm hmm hv hw hvw
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotoneOn_section4T s β h hr0 hr hm hmm hw hv hwv)),
      abs_of_nonneg (sub_nonneg.mpr hwv)]
    exact section4T_increment_le s β h hr0 hr hm hmm hw hv hwv

end SpinGlass.Targets
