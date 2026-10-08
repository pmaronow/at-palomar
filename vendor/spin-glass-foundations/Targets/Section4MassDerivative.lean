module

public import Targets.ParisiMassLocal

@[expose] public section

/-!
# Actual mass variation through the Section 4 scalar recursion

The genuine inserted mass derivative is propagated through the original outer
levels by the existing normalized parameter-derivative rule. The positive-mass
local bound is uniform in the field, but not claimed uniform as the baseline
mass tends to zero. The zero-baseline branch is treated separately.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- An explicit finite bound on a positive compact mass interval. -/
noncomputable def section4MassLocalBound (a b v : ℝ) : ℝ :=
  (Real.sqrt v * (Real.exp ((b * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (b * Real.sqrt v)) +
    Real.sqrt v * gAbsMoment + b * v / 2) / a

/-- The nested normalized tilted mean of the inserted scalar mass derivative. -/
noncomputable def section4MassD {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (v : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun m _ y => deriv (fun a => parisiStep a v (parisiF s β (k + 2 - r)) (y 0)) m
  | j + 1 => fun m =>
      pairedSecondMean (s.m (k + 2 - (k + 2 - r + 1 + j)))
        (section5Variance s β r (k + 2 - (k + 2 - r + 1 + j)) v)
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j) (y 0))
        (section4MassD s β r v j m)

theorem section4MassD_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    {a b v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
      (section4MassD s β r v 0) (Set.Ioo a b) (section4MassLocalBound a b v) := by
  have hA := parisiF_hasLinearGrowth s β (k + 2 - r)
  have hAm := parisiF_measurable s β (k + 2 - r)
  have hL := parisiF_lipschitz s β (k + 2 - r)
  obtain ⟨C, D, _, hD, hb⟩ := hasLinearGrowth_parisiStep hA hAm 0 v
  refine ⟨?_, ?_, ?_, ⟨C + b * v / 2, D, hD, ?_⟩, ?_⟩
  · intro m _ x y
    exact (differentiable_parisiStep_mass hA hAm v (y 0) m).hasDerivAt
  · intro m _
    exact (measurable_parisiStep hAm m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  · intro m _
    exact (measurable_deriv_parisiStep_mass hA hAm m v).comp
      ((measurable_pi_apply 0).comp measurable_snd)
  · intro m hm x y
    have hd := abs_parisiStep_mass_sub_zero_le hA hAm hL hv.le m (y 0)
    rw [abs_of_pos (ha.trans hm.1)] at hd
    have htri := abs_sub_le (parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
      (parisiStep 0 v (parisiF s β (k + 2 - r)) (y 0)) 0
    simp only [sub_zero] at htri
    simp only [l1, Fin.sum_univ_one]
    nlinarith [hb (y 0), mul_le_mul_of_nonneg_right hm.2.le hv.le,
      mul_nonneg hD (abs_nonneg (x 0))]
  · intro m hm x y
    exact abs_deriv_parisiStep_mass_le hA hAm hL ha ⟨hm.1.le, hm.2.le⟩ hv (y 0)

/-- Local differentiation hypotheses at every actual outer level. -/
theorem section4MassD_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (_hr0 : 1 ≤ r) (hr : r ≤ k + 1) {a b v : ℝ} (ha : 0 < a)
    (hv : v ∈ Set.Ioc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) {j : ℕ} (hj : j ≤ r) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j) (y 0))
      (section4MassD s β r v j) (Set.Ioo a b) (section4MassLocalBound a b v) := by
  induction j with
  | zero =>
    simpa only [Nat.add_zero, section4Cascade_inserted s β (show r ≤ k + 2 by omega)] using!
      section4MassD_base_props s β r ha hv.1
  | succ j ih =>
    let p := k + 2 - (k + 2 - r + 1 + j)
    have hp : p < r := by dsimp [p]; omega
    have H := (ih (by omega)).secondStep (m := s.m p)
      (v := section5Variance s β r p v) isOpen_Ioo (s.m_nonneg (by omega))
      (section5Variance_nonneg s β hr (by dsimp [p]; omega) ⟨hv.1.le, hv.2⟩)
    have he :
        (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + (j + 1)) (y 0)) =
        (fun m (_ : Fin 1 → ℝ) y => parisiStepPi 1 (s.m p) (section5Variance s β r p v)
          (fun z => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
            (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j) (z 0)) y) := by
      funext m x y
      rw [show k + 2 - r + 1 + (j + 1) = (k + 2 - r + 1 + j) + 1 by omega,
        scalarFieldCascade]
      change parisiStep (section4Mass s r m p) (section5Variance s β r p v) _ _ = _
      simp only [section4Mass, if_pos hp]
      symm
      simpa using parisiStepPi_sum (n := 1) (s.m p) (section5Variance s β r p v)
        (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1 y
    rw [he]
    exact H

/-- The explicit full-depth mass derivative candidate. -/
noncomputable def section4TMassD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (v m : ℝ) : ℝ := section4MassD s β r v r m 0 (fun _ => h)

/-- Positive-mass differentiation of the actual full Section 4 function. -/
theorem hasDerivAt_section4T_mass_pos {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 < m)
    (hv : v ∈ Set.Ioc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (fun a => section4T s β h r a v) (section4TMassD s β h r v m) m := by
  have H := (section4MassD_props s β hr0 hr (a := m / 2) (b := 2 * m)
    (by positivity) hv (j := r) le_rfl).deriv m (by constructor <;> linarith) 0 (fun _ => h)
  have hi : k + 2 - r + 1 + r = k + 3 := by omega
  simpa only [hi, section4T, section4TMassD] using! H

/-- If the baseline mass vanishes, every unchanged outer mass vanishes too.
The actual outer recursion is then a single Gaussian expectation. -/
theorem section4T_of_zero_baseline_mass {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hz : s.m (r - 1) = 0) (m : ℝ)
    {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4T s β h r m v =
      parisiStep 0 (β ^ 2 * s.q r - v) (parisiStep m v (parisiF s β (k + 2 - r))) h := by
  have hzero {p : ℕ} (hp : p ≤ r - 1) : s.m p = 0 := by
    apply le_antisymm
    · exact (s.m_mono' (r - 1) (by omega) p hp).trans_eq hz
    · exact s.m_nonneg (by omega)
  have hB := hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β (k + 2 - r))
    (parisiF_measurable s β _) m v
  have hBm := measurable_parisiStep (parisiF_measurable s β (k + 2 - r)) m v
  have he {j : ℕ} (hj : j ≤ r - 1) :
      scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) =
      parisiStep 0 (β ^ 2 * (s.q r - s.q (r - 1 - j)) - v)
        (parisiStep m v (parisiF s β (k + 2 - r))) := by
    induction j with
    | zero =>
      simpa only [Nat.add_zero, Nat.sub_zero, hz] using section4Cascade_split s β hr0 hr m v
    | succ j ih =>
      let p := k + 2 - (k + 2 - r + 2 + j)
      have hp : p < r := by dsimp [p]; omega
      have hpn : p ≠ r := by omega
      have hpn' : ¬r < p := by omega
      have hpn'' : p + 1 ≠ r := by dsimp [p]; omega
      have hi : r - 1 - (j + 1) = p := by dsimp [p]; omega
      have hi' : r - 1 - j = p + 1 := by dsimp [p]; omega
      rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
        scalarFieldCascade, ih (by omega), hi, hi']
      change parisiStep (section4Mass s r m p) (section5Variance s β r p v) _ = _
      simp only [section4Mass, section5Variance, if_pos hp, if_neg hpn,
        if_neg hpn', if_neg hpn'', hzero (show p ≤ r - 1 by omega)]
      have hv1 : 0 ≤ β ^ 2 * (s.q (p + 1) - s.q p) :=
        mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
      have hv2 : 0 ≤ β ^ 2 * (s.q r - s.q (p + 1)) - v := by
        have hq := s.q_mono' (r - 1) (by omega) (p + 1) (by dsimp [p]; omega)
        nlinarith [hv.2, mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq)]
      refine (parisiStep_add 0 _ _ hv1 hv2 hB hBm).symm.trans ?_
      congr 1
      ring
  have hi : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  simpa only [section4T, hi, Nat.sub_self, s.q_zero, sub_zero] using congrFun (he (j := r - 1) le_rfl) h

/-- Genuine mass-zero differentiation at any zero-baseline level, including
the first interval. All nested zero-mass outer expectations are discharged. -/
theorem hasDerivAt_section4T_mass_zero {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hz : s.m (r - 1) = 0)
    {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (fun m => section4T s β h r m v)
      (∫ z, deriv (fun m => parisiStep m v (parisiF s β (k + 2 - r))
        (h + Real.sqrt (β ^ 2 * s.q r - v) * z)) 0 ∂(gaussianReal 0 1)) 0 := by
  simp_rw [section4T_of_zero_baseline_mass s β h hr0 hr hz _ hv]
  exact hasDerivAt_mass_zero_outer_expectation (parisiF_hasLinearGrowth s β (k + 2 - r))
    (parisiF_measurable s β _) (parisiF_lipschitz s β _) hv.1 _ h

/-- Differentiability in the inserted mass at the actual baseline, with both
variance endpoints and the zero-mass baseline included. -/
theorem differentiableAt_section4T_mass_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    DifferentiableAt ℝ (fun m => section4T s β h r m v) (s.m (r - 1)) := by
  rcases eq_or_lt_of_le hv.1 with hzero | hvpos
  · subst v
    simpa only [section4T_zero_variance s β h hr0 hr] using
      (differentiableAt_const (parisiF s β (k + 2) h))
  · rcases eq_or_lt_of_le (s.m_nonneg (p := r - 1) (by omega)) with hz | hm
    · rw [← hz]
      exact (hasDerivAt_section4T_mass_zero s β h hr0 hr hz.symm hv).differentiableAt
    · exact (hasDerivAt_section4T_mass_pos s β h hr0 hr hm ⟨hvpos, hv.2⟩).differentiableAt

/-- Talagrand's actual `U(v) = 2 ∂m T(v,m)` at the original mass. Its derivative
is justified by `differentiableAt_section4T_mass_baseline`, including mass zero. -/
noncomputable def section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (v : ℝ) : ℝ :=
  2 * deriv (fun m => section4T s β h r m v) (s.m (r - 1))

theorem hasDerivAt_section4T_mass_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (fun m => section4T s β h r m v) (section4U s β h r v / 2) (s.m (r - 1)) := by
  simpa only [section4U, mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using!
    (differentiableAt_section4T_mass_baseline s β h hr0 hr hv).hasDerivAt

/-- At zero baseline mass, `U` is the actual outer Gaussian average of the
centered second moment at the inserted level. -/
theorem section4U_zero_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hz : s.m (r - 1) = 0)
    {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4U s β h r v = ∫ z, ∫ z',
      (parisiF s β (k + 2 - r)
        (h + Real.sqrt (β ^ 2 * s.q r - v) * z + Real.sqrt v * z') -
        parisiStep 0 v (parisiF s β (k + 2 - r))
          (h + Real.sqrt (β ^ 2 * s.q r - v) * z)) ^ 2
        ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) := by
  rw [section4U, hz, (hasDerivAt_section4T_mass_zero s β h hr0 hr hz hv).deriv]
  simp_rw [(hasDerivAt_parisiStep_mass_zero (parisiF_hasLinearGrowth s β (k + 2 - r))
    (parisiF_measurable s β _) v _).deriv]
  rw [integral_div]
  ring

/-- The inserted zero variance does not depend on its mass, so `U(0)=0`. -/
theorem section4U_zero_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) : section4U s β h r 0 = 0 := by
  simp only [section4U, section4T_zero_variance s β h hr0 hr, deriv_const, mul_zero]

end SpinGlass.Targets
