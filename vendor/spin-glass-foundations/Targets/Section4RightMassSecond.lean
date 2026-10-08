module

public import Targets.Section4RightMassDerivative
public import Targets.Section4MassTaylor

@[expose] public section

/-!
# Uniform second mass derivative and Taylor bound for the right insertion

The scalar cumulant bounds apply to the old-mass inner transform, which remains
one-Lipschitz. The existing second-derivative-plus-square invariant is then
transported through the unchanged outer levels. Its constant is the same as
for the left insertion, with no dependence on the depth or the mass gap.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem rightInner_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (v : ℝ) :
    let B := parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
      (parisiF s β (k + 1 - r))
    HasLinearGrowth B ∧ Measurable B ∧ ∀ x y, |B x - B y| ≤ |x-y| := by
  refine ⟨hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _) _ _,
    measurable_parisiStep (parisiF_measurable s β _) _ _, ?_⟩
  intro x y
  simpa only [one_mul] using parisiStep_lipschitz (L := 1)
    (by simpa only [one_mul] using parisiF_lipschitz s β (k + 1 - r))
    (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _) x y

/-- The right first mass observable is measurable in its fields. -/
theorem measurable_section4RightMassD {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) (v m : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      section4RightMassD s β r v j m p.1 p.2) := by
  induction j with
  | zero =>
    exact (measurable_deriv_parisiStep_mass (rightInner_props s β r v).1
      (rightInner_props s β r v).2.1 m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    unfold section4RightMassD
    exact measurable_pairedSecondMean
      ((scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd)) ih _ _

/-- Normalized outer means preserve the physical first mass bound. -/
theorem section4RightMassD_abs_le_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V)
    (x y : Fin 1 → ℝ) :
    |section4RightMassD s β r v j m x y| ≤ parisiMassFirstBound V := by
  induction j generalizing x y with
  | zero =>
    exact (parisiStep_mass_derivatives_uniform (rightInner_props s β r v).1
      (rightInner_props s β r v).2.1 (rightInner_props s β r v).2.2 hm hv (y 0)).1
  | succ j ih =>
    obtain ⟨C, D, _, hD, hb⟩ := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j)).2.1
    apply pairedTiltMean_abs_le
    · refine ⟨(scalarFieldCascade_props _ _ _).1.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
      intro z
      simpa only [l1, Fin.sum_univ_one] using hb (z 0)
    · exact (measurable_section4RightMassD s β r j v m).comp (measurable_const.prodMk measurable_id)
    · exact ih x

/-- The actual second mass observable, propagated by the normalized covariance
rule, not merely a formal second derivative. -/
noncomputable def section4RightMassE {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (v : ℝ) : ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun m _ y => iteratedDeriv 2 (fun a => parisiStep a v
      (parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
        (parisiF s β (k + 1 - r))) (y 0)) m
  | j + 1 => fun m =>
      pairedSecondCovariance (s.m (k + 2 - (k + 1 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 1 - r + 2 + j) + 1) -
          s.q (k + 2 - (k + 1 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v)
          (k + 1 - r + 2 + j) (y 0))
        (section4RightMassD s β r v j m) (section4RightMassD s β r v j m)
        (section4RightMassE s β r v j m)

theorem measurable_section4RightMassE {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) (v m : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      section4RightMassE s β r v j m p.1 p.2) := by
  induction j with
  | zero =>
    exact (measurable_second_deriv_parisiStep_mass (rightInner_props s β r v).1
      (rightInner_props s β r v).2.1 m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    have hA := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j)).1
    have hD := measurable_section4RightMassD s β r j v m
    unfold section4RightMassE pairedSecondCovariance
    exact (measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd))
      (ih.add ((hD.const_mul _).mul hD)) _ _).sub
      (((measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd)) hD _ _).const_mul _).mul
        (measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd)) hD _ _))

/-- The existing second-plus-square invariant gives the same depth-uniform
constant as the left mass derivative, including masses zero and one. -/
theorem section4RightMassE_invariant {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r j : ℕ} (_hr : r ≤ k + 1) (hj : j ≤ r) {m v V : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x y : Fin 1 → ℝ) :
    |section4RightMassE s β r v j m x y| + section4RightMassD s β r v j m x y ^ 2 ≤
      section4MassSecondBound V := by
  induction j generalizing x y with
  | zero =>
    have H := parisiStep_mass_derivatives_uniform (rightInner_props s β r v).1
      (rightInner_props s β r v).2.1 (rightInner_props s β r v).2.2 hm hv (y 0)
    have Hsq := pow_le_pow_left₀ (abs_nonneg _) H.1 2
    rw [sq_abs] at Hsq
    exact add_le_add H.2 Hsq
  | succ j ih =>
    obtain ⟨C, L, _, hL, hb⟩ := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j)).2.1
    apply pairedSecondCovariance_mass_invariant
    · refine ⟨(scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd),
        C, L, hL, ?_⟩
      intro x y
      simp only [l1, Fin.sum_univ_one]
      nlinarith [hb (y 0), mul_nonneg hL (abs_nonneg (x 0))]
    · exact measurable_section4RightMassD s β r j v m
    · exact measurable_section4RightMassE s β r j v m
    · exact section4RightMassD_abs_le_uniform s β r j hm hv
    · exact ih (by omega)
    · exact ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩

private theorem rightMassE_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    {v V : ℝ} (hv : v ∈ Set.Icc 0 V) :
    CoupledParamDeriv (section4RightMassD s β r v 0) (section4RightMassE s β r v 0)
      (Set.Ioo (-2) 2) (parisiMassSecondBound (4 * V)) := by
  obtain ⟨hA, hAm, hLip⟩ := rightInner_props s β r v
  refine ⟨?_, fun m _ => measurable_section4RightMassD s β r 0 v m,
    fun m _ => measurable_section4RightMassE s β r 0 v m,
    ⟨parisiMassFirstBound (4 * V), 0, le_rfl, ?_⟩, ?_⟩
  · intro m _ x y
    simpa only [section4RightMassD, section4RightMassE, iteratedDeriv_succ, iteratedDeriv_zero] using
      (analyticAt_parisiStep_mass hA hAm v (y 0) m).deriv.differentiableAt.hasDerivAt
  · intro m hm x y
    simpa only [section4RightMassD, zero_mul, add_zero] using
      (parisiStep_mass_derivatives_local_uniform hA hAm hLip
        (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).1
  · intro m hm x y
    exact (parisiStep_mass_derivatives_local_uniform hA hAm hLip
      (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).2

/-- Genuine second differentiation on an open neighborhood of the physical
mass interval. The local domination may grow with depth; the physical bound
is separately supplied by the invariant above. -/
theorem section4RightMassE_deriv_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v V : ℝ} (hv : v ∈ Set.Icc 0 V)
    {j : ℕ} (hj : j ≤ r) :
    CoupledParamDeriv (section4RightMassD s β r v j) (section4RightMassE s β r v j)
      (Set.Ioo (-2) 2)
      (parisiMassSecondBound (4 * V) + 2 * j * parisiMassFirstBound (4 * V) ^ 2) := by
  induction j with
  | zero =>
    simpa only [Nat.cast_zero, mul_zero, zero_mul, add_zero] using rightMassE_base_props s β r hv
  | succ j ih =>
    have hA := section4RightMassD_props s β hr hv (j := j) (by omega)
    let p := k + 2 - (k + 1 - r + 2 + j)
    have H := (hA.tiltSecond (ih (by omega)) hA.bound isOpen_Ioo (m := s.m p)
      (v := β ^ 2 * (s.q (p + 1) - s.q p))).1
    refine ⟨H.deriv, H.measurable, H.measurable_deriv, H.growth, ?_⟩
    intro m hm x y
    refine (H.bound m hm x y).trans ?_
    rw [abs_of_nonneg (s.m_nonneg (show p ≤ k + 1 by dsimp [p]; omega)), Nat.cast_add, Nat.cast_one]
    have Hm := s.m_le_one (show p ≤ k + 1 by dsimp [p]; omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr Hm) (sq_nonneg (parisiMassFirstBound (4 * V)))]

/-- The second derivative is the explicit transported covariance observable. -/
theorem hasDerivAt_deriv_section4RightT_mass {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Ioo (-2) 2) (hv : 0 ≤ v) :
    HasDerivAt (fun a => deriv (fun b => section4RightT s β h r b v) a)
      (section4RightMassE s β r v r m 0 (fun _ => h)) m := by
  have H := (section4RightMassE_deriv_props s β hr (V := v) ⟨hv, le_rfl⟩
    (j := r) le_rfl).deriv m hm 0 (fun _ => h)
  apply H.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hm] with a ha
  exact (hasDerivAt_section4RightT_mass s β h hr ha hv).deriv

/-- The actual second mass derivative has the same beta-only bound as for
the left insertion, at both mass and variance endpoints. -/
theorem abs_second_deriv_section4RightT_mass_le_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |deriv (deriv (fun a => section4RightT s β h r a v)) m| ≤
      section4MassSecondBound (β ^ 2) := by
  rw [(hasDerivAt_deriv_section4RightT_mass s β h hr
    ⟨by linarith [hm.1], by linarith [hm.2]⟩ hv.1).deriv]
  have hv' : v ∈ Set.Icc 0 (β ^ 2) := by
    refine ⟨hv.1, hv.2.trans ?_⟩
    nlinarith [mul_nonneg (sq_nonneg β) (s.q_nonneg (p := r) (by omega)),
      mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_le_one (p := r + 1) (by omega)))]
  have H := section4RightMassE_invariant s β hr le_rfl hm hv' 0 (fun _ => h)
  nlinarith [sq_nonneg (section4RightMassD s β r v r m 0 (fun _ => h))]

/-- The actual full right transform has a depth-uniform quadratic mass
remainder on the entire physical mass interval. -/
theorem section4RightT_mass_taylor_bound {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {a b v : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |section4RightT s β h r b v - section4RightT s β h r a v -
      deriv (fun m => section4RightT s β h r m v) a * (b-a)| ≤
      section4MassSecondBound (β ^ 2) * (b-a)^2 := by
  apply quadratic_remainder_of_second_bound (section4MassSecondBound_nonneg _)
    (fun x hx => (hasDerivAt_section4RightT_mass s β h hr
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ hv.1).differentiableAt)
    (fun x hx => (hasDerivAt_deriv_section4RightT_mass s β h hr
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ hv.1).differentiableAt)
    (fun x hx => abs_second_deriv_section4RightT_mass_le_uniform s β h hr hx hv) ha hb

end SpinGlass.Targets
