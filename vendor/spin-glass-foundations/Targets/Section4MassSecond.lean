module

public import Targets.Section4MassUniform
public import Targets.Section4MassSecondInvariant
public import Targets.Section4MassSecondLocal

@[expose] public section

/-!
# Second mass differentiation through the actual Section 4 recursion

The second observable is differentiated through the same normalized outer
levels as the first one. Its bound keeps the first-derivative square, so the
constant is independent of the number of RSB levels.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Spatial measurability of the genuine second mass derivative, including zero. -/
theorem measurable_second_deriv_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m v : ℝ) :
    Measurable (fun x => iteratedDeriv 2 (fun a => parisiStep a v A x) m) := by
  apply measurable_of_tendsto_metrizable' (𝓝[≠] (0 : ℝ))
    (f := fun t x => t⁻¹ * (deriv (fun a => parisiStep a v A x) (m + t) -
      deriv (fun a => parisiStep a v A x) m))
  · intro t
    exact ((measurable_deriv_parisiStep_mass hA hAm (m + t) v).sub
      (measurable_deriv_parisiStep_mass hA hAm m v)).const_mul _
  · apply tendsto_pi_nhds.mpr
    intro x
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul] using
      (analyticAt_parisiStep_mass hA hAm v x m).deriv.differentiableAt.hasDerivAt.tendsto_slope_zero

/-- The actual covariance expression for the nested second mass derivative. -/
noncomputable def section4MassE {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (v : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun m _ y => iteratedDeriv 2 (fun a => parisiStep a v (parisiF s β (k + 2 - r)) (y 0)) m
  | j + 1 => fun m =>
      pairedSecondCovariance (s.m (k + 2 - (k + 2 - r + 1 + j)))
        (section5Variance s β r (k + 2 - (k + 2 - r + 1 + j)) v)
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j) (y 0))
        (section4MassD s β r v j m) (section4MassD s β r v j m) (section4MassE s β r v j m)

theorem measurable_section4MassE {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) (v m : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => section4MassE s β r v j m p.1 p.2) := by
  induction j with
  | zero =>
    exact (measurable_second_deriv_parisiStep_mass (parisiF_hasLinearGrowth s β _)
      (parisiF_measurable s β _) m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    have hA := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j)).1
    have hD := measurable_section4MassD s β r j v m
    unfold section4MassE pairedSecondCovariance
    exact (measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd))
      (ih.add ((hD.const_mul _).mul hD)) _ _).sub
      (((measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd)) hD _ _).const_mul _).mul
        (measurable_pairedSecondMean (hA.comp ((measurable_pi_apply 0).comp measurable_snd)) hD _ _))

/-- The field/depth-independent constant for the full nested second derivative. -/
noncomputable def section4MassSecondBound (V : ℝ) : ℝ :=
  parisiMassSecondBound V + parisiMassFirstBound V ^ 2

theorem section4MassSecondBound_nonneg (V : ℝ) : 0 ≤ section4MassSecondBound V :=
  add_nonneg (parisiMassSecondBound_nonneg V) (sq_nonneg _)

/-- The proposed invariant is valid for the actual second-observable recursion,
including both mass endpoints and all nonnegative physical variance endpoints. -/
theorem section4MassE_invariant {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r j : ℕ} (_hr : r ≤ k + 1) (hj : j ≤ r) {m v V : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x y : Fin 1 → ℝ) :
    |section4MassE s β r v j m x y| + section4MassD s β r v j m x y ^ 2 ≤
      section4MassSecondBound V := by
  induction j generalizing x y with
  | zero =>
    have H := parisiStep_parisiF_mass_derivatives_uniform s β (k + 2 - r) hm hv (y 0)
    have Hsq : (deriv (fun a => parisiStep a v (parisiF s β (k + 2 - r)) (y 0)) m) ^ 2 ≤
        parisiMassFirstBound V ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) H.1 2
    exact add_le_add H.2 Hsq
  | succ j ih =>
    obtain ⟨C, L, _, hL, hb⟩ := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j)).2.1
    apply pairedSecondCovariance_mass_invariant
    · refine ⟨(scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd),
        C, L, hL, ?_⟩
      intro x y
      simp only [l1, Fin.sum_univ_one]
      nlinarith [hb (y 0), mul_nonneg hL (abs_nonneg (x 0))]
    · exact measurable_section4MassD s β r j v m
    · exact measurable_section4MassE s β r j v m
    · exact section4MassD_abs_le_uniform s β r j hm hv
    · exact ih (by omega)
    · exact ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩

theorem section4MassE_abs_le_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r j : ℕ} (hr : r ≤ k + 1) (hj : j ≤ r) {m v V : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x y : Fin 1 → ℝ) :
    |section4MassE s β r v j m x y| ≤ section4MassSecondBound V := by
  have H := section4MassE_invariant s β hr hj hm hv x y
  nlinarith [sq_nonneg (section4MassD s β r v j m x y)]

private theorem mass_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    {v V : ℝ} (hv : v ∈ Set.Icc 0 V) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
      (section4MassD s β r v 0) (Set.Ioo (-2) 2) (parisiMassFirstBound (4 * V)) ∧
    CoupledParamDeriv (section4MassD s β r v 0) (section4MassE s β r v 0)
      (Set.Ioo (-2) 2) (parisiMassSecondBound (4 * V)) := by
  have hA := parisiF_hasLinearGrowth s β (k + 2 - r)
  have hAm := parisiF_measurable s β (k + 2 - r)
  have hL := parisiF_lipschitz s β (k + 2 - r)
  obtain ⟨C, L, _, hL0, hb⟩ := hasLinearGrowth_parisiStep hA hAm 0 v
  constructor
  · refine ⟨?_, ?_, ?_, ⟨C + v, L, hL0, ?_⟩, ?_⟩
    · intro m _ x y
      exact (differentiable_parisiStep_mass hA hAm v (y 0) m).hasDerivAt
    · intro m _
      exact (measurable_parisiStep hAm m v).comp ((measurable_pi_apply 0).comp measurable_snd)
    · intro m _
      exact measurable_section4MassD s β r 0 v m
    · intro m hm x y
      have H := abs_parisiStep_mass_sub_zero_le hA hAm hL hv.1 m (y 0)
      have Htri := abs_sub_le (parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
        (parisiStep 0 v (parisiF s β (k + 2 - r)) (y 0)) 0
      have hmabs : |m| ≤ 2 := abs_le.mpr ⟨hm.1.le, hm.2.le⟩
      simp only [sub_zero] at Htri
      simp only [l1, Fin.sum_univ_one]
      nlinarith [hb (y 0), mul_le_mul_of_nonneg_right hmabs hv.1,
        mul_nonneg hL0 (abs_nonneg (x 0))]
    · intro m hm x y
      exact (parisiStep_mass_derivatives_local_uniform hA hAm hL
        (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).1
  · refine ⟨?_, fun m _ => measurable_section4MassD s β r 0 v m,
      fun m _ => measurable_section4MassE s β r 0 v m,
      ⟨parisiMassFirstBound (4 * V), 0, le_rfl, ?_⟩, ?_⟩
    · intro m _ x y
      simpa only [section4MassD, section4MassE, iteratedDeriv_succ, iteratedDeriv_zero] using
        (analyticAt_parisiStep_mass hA hAm v (y 0) m).deriv.differentiableAt.hasDerivAt
    · intro m hm x y
      simpa only [section4MassD, zero_mul, add_zero] using
        (parisiStep_mass_derivatives_local_uniform hA hAm hL
          (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).1
    · intro m hm x y
      exact (parisiStep_mass_derivatives_local_uniform hA hAm hL
        (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).2

/-- Both genuine derivatives propagate on an open neighborhood of all physical
masses. This auxiliary domination bound may depend on depth; the physical
second-derivative bound comes separately from the sharper invariant. -/
theorem section4MassE_deriv_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v V : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hV : v ≤ V)
    {j : ℕ} (hj : j ≤ r) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j) (y 0))
      (section4MassD s β r v j) (Set.Ioo (-2) 2) (parisiMassFirstBound (4 * V)) ∧
    CoupledParamDeriv (section4MassD s β r v j) (section4MassE s β r v j)
      (Set.Ioo (-2) 2)
      (parisiMassSecondBound (4 * V) + 2 * j * parisiMassFirstBound (4 * V) ^ 2) := by
  induction j with
  | zero =>
    simpa only [Nat.add_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero,
      section4Cascade_inserted s β (show r ≤ k + 2 by omega)] using!
      mass_base_props s β r ⟨hv.1, hV⟩
  | succ j ih =>
    obtain ⟨hA, hD⟩ := ih (by omega)
    let p := k + 2 - (k + 2 - r + 1 + j)
    have hp : p < r := by dsimp [p]; omega
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
    constructor
    · rw [he]
      exact hA.secondStep isOpen_Ioo (s.m_nonneg (by omega))
        (section5Variance_nonneg s β hr (by dsimp [p]; omega) hv)
    · have H := (hA.tiltSecond hD hA.bound isOpen_Ioo (m := s.m p)
        (v := section5Variance s β r p v)).1
      refine ⟨H.deriv, H.measurable, H.measurable_deriv, H.growth, ?_⟩
      intro m hm x y
      refine (H.bound m hm x y).trans ?_
      rw [abs_of_nonneg (s.m_nonneg (show p ≤ k + 1 by dsimp [p]; omega)), Nat.cast_add, Nat.cast_one]
      have Hm := s.m_le_one (show p ≤ k + 1 by dsimp [p]; omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr Hm) (sq_nonneg (parisiMassFirstBound (4 * V)))]

/-- The full second mass derivative of `T` is the actual nested covariance
observable, not an assumed formal derivative. -/
theorem hasDerivAt_section4TMassD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Ioo (-2) 2)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (fun a => section4TMassD s β h r v a) (section4MassE s β r v r m 0 (fun _ => h)) m :=
  (section4MassE_deriv_props s β hr hv (V := v) le_rfl (j := r) le_rfl).2.deriv m hm 0 (fun _ => h)

theorem hasDerivAt_deriv_section4T_mass {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Ioo (-2) 2)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (fun a => deriv (fun b => section4T s β h r b v) a)
      (section4MassE s β r v r m 0 (fun _ => h)) m := by
  apply (hasDerivAt_section4TMassD s β h hr hm hv).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hm] with a ha
  have H := (section4MassE_deriv_props s β hr hv (V := v) le_rfl (j := r) le_rfl).1.deriv a ha 0 (fun _ => h)
  have hi : k + 2 - r + 1 + r = k + 3 := by omega
  simpa only [section4T, section4TMassD, hi] using H.deriv

/-- Uniform second mass bound for the actual full transform, including masses
zero and one and both physical variance endpoints. -/
theorem section4T_second_mass_derivative_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ∃ e : ℝ, HasDerivAt (fun a => deriv (fun b => section4T s β h r b v) a) e m ∧
      |e| ≤ section4MassSecondBound (β ^ 2) := by
  refine ⟨_, hasDerivAt_deriv_section4T_mass s β h hr ⟨by linarith [hm.1], by linarith [hm.2]⟩ hv, ?_⟩
  have hv' : v ∈ Set.Icc 0 (β ^ 2) := by
    refine ⟨hv.1, hv.2.trans ?_⟩
    have hq0 := s.q_nonneg (p := r - 1) (by omega)
    have hq1 := s.q_le_one (p := r) (by omega)
    nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hq0,
      mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq1)]
  exact section4MassE_abs_le_uniform s β hr le_rfl hm hv' 0 (fun _ => h)

theorem abs_second_deriv_section4T_mass_le_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |iteratedDeriv 2 (fun a => section4T s β h r a v) m| ≤ section4MassSecondBound (β ^ 2) := by
  obtain ⟨e, he, hb⟩ := section4T_second_mass_derivative_uniform s β h hr hm hv
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, he.deriv] using hb

/-- The inserted functional has the same second mass derivative as `T`:
its deterministic correction is affine in the inserted mass. This completes
the nested second-mass bound, including both mass and overlap endpoints. -/
theorem section4Phi_second_mass_derivative_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m u : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    ∃ e : ℝ, HasDerivAt (fun a => deriv (fun b => section4Phi s β h r b u) a) e m ∧
      |e| ≤ section4MassSecondBound (β ^ 2) := by
  have hv := section5SplitVariance_mem s β (t := 1) ⟨by norm_num, le_rfl⟩ hu
  simp only [one_mul] at hv
  let v := β ^ 2 * (s.q r - u)
  let c := β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2)
  obtain ⟨e, he, hb⟩ := section4T_second_mass_derivative_uniform s β h hr hm hv
  refine ⟨e, ?_, hb⟩
  apply (he.sub_const c).congr_of_eventuallyEq
  have hm' : m ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  filter_upwards [isOpen_Ioo.mem_nhds hm'] with a ha
  have hT := (section4MassE_deriv_props s β hr hv (V := v) le_rfl (j := r) le_rfl).1.deriv a ha 0 (fun _ => h)
  have hi : k + 2 - r + 1 + r = k + 3 := by omega
  have hTa : HasDerivAt (fun b => section4T s β h r b v) (section4TMassD s β h r v a) a := by
    simpa only [hi, section4T, section4TMassD] using hT
  have HC := ((hasDerivAt_id a).const_sub (s.m (r - 1))).mul_const c
  have HP : HasDerivAt (fun b => section4Phi s β h r b u) (section4TMassD s β h r v a - c) a := by
    simpa only [section4Phi, c, v, id_eq, neg_mul, one_mul, sub_eq_add_neg] using!
      ((hTa.const_add (Real.log 2)).sub_const (parisiCorrection s β)).add HC
  rw [HP.deriv, hTa.deriv]

theorem abs_second_deriv_section4Phi_mass_le_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m u : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |iteratedDeriv 2 (fun a => section4Phi s β h r a u) m| ≤ section4MassSecondBound (β ^ 2) := by
  obtain ⟨e, he, hb⟩ := section4Phi_second_mass_derivative_uniform s β h hr hm hu
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, he.deriv] using hb

end SpinGlass.Targets
