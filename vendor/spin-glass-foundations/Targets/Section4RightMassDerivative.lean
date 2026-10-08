module

public import Targets.Section4RightDerivative
public import Targets.Section4MassSecondLocal

@[expose] public section

/-!
# Genuine mass differentiation of the right insertion

The old inner mass is fixed; the newly inserted outer mass varies. The scalar
mass derivative and its local domination are reused on this actual inner
function, then transported through the unchanged outer levels. A two-sided
mass neighborhood includes zero and one, and nonnegative split variances
include both physical endpoints. No variable-mass reflection is used.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The existing scalar mass bounds give the parameter-differentiation data
for any measurable, linearly growing, one-Lipschitz input. -/
theorem scalarMass_coupledParamDeriv {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {v V : ℝ} (hv : v ∈ Set.Icc 0 V) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => parisiStep m v A (y 0))
      (fun m (_ : Fin 1 → ℝ) y => deriv (fun a => parisiStep a v A (y 0)) m)
      (Set.Ioo (-2) 2) (parisiMassFirstBound (4 * V)) := by
  obtain ⟨C, L, _, hL0, hb⟩ := hasLinearGrowth_parisiStep hA hAm 0 v
  refine ⟨?_, ?_, ?_, ⟨C + v, L, hL0, ?_⟩, ?_⟩
  · intro m _ x y
    exact (differentiable_parisiStep_mass hA hAm v (y 0) m).hasDerivAt
  · intro m _
    exact (measurable_parisiStep hAm m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  · intro m _
    exact (measurable_deriv_parisiStep_mass hA hAm m v).comp
      ((measurable_pi_apply 0).comp measurable_snd)
  · intro m hm x y
    have H := abs_parisiStep_mass_sub_zero_le hA hAm hLip hv.1 m (y 0)
    have Htri := abs_sub_le (parisiStep m v A (y 0)) (parisiStep 0 v A (y 0)) 0
    have hmabs : |m| ≤ 2 := abs_le.mpr ⟨hm.1.le, hm.2.le⟩
    simp only [sub_zero] at Htri
    simp only [l1, Fin.sum_univ_one]
    nlinarith [hb (y 0), mul_le_mul_of_nonneg_right hmabs hv.1,
      mul_nonneg hL0 (abs_nonneg (x 0))]
  · intro m hm x y
    exact (parisiStep_mass_derivatives_local_uniform hA hAm hLip
      (abs_le.mpr ⟨hm.1.le, hm.2.le⟩) hv (y 0)).1

/-- The genuine local derivative in the inserted outer mass, followed by the
actual fixed outer normalized means. -/
noncomputable def section4RightMassD {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (v : ℝ) : ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun m _ y => deriv (fun a => parisiStep a v
      (parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
        (parisiF s β (k + 1 - r))) (y 0)) m
  | j + 1 => fun m =>
      pairedSecondMean (s.m (k + 2 - (k + 1 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 1 - r + 2 + j) + 1) -
          s.q (k + 2 - (k + 1 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v)
          (k + 1 - r + 2 + j) (y 0))
        (section4RightMassD s β r v j m)

/-- Uniform local mass differentiation of the actual two-step right split.
The inner old mass does not vary with the new outer mass. -/
theorem section4RightMassD_base_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v V : ℝ} (hv : v ∈ Set.Icc 0 V) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade
        (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v)
        (k + 1 - r + 2) (y 0))
      (section4RightMassD s β r v 0) (Set.Ioo (-2) 2)
      (parisiMassFirstBound (4 * V)) := by
  let A := parisiF s β (k + 1 - r)
  let w := β ^ 2 * (s.q (r + 1) - s.q r) - v
  have hA := parisiF_hasLinearGrowth s β (k + 1 - r)
  have hAm := parisiF_measurable s β (k + 1 - r)
  have hLip : ∀ x y, |parisiStep (s.m r) w A x - parisiStep (s.m r) w A y| ≤ |x-y| := by
    intro x y
    simpa only [one_mul] using parisiStep_lipschitz (m := s.m r) (v := w) (L := 1)
      (by simpa only [one_mul] using parisiF_lipschitz s β (k + 1 - r)) hA hAm x y
  simpa only [section4RightCascade_split s β hr, section4RightMassD] using!
    scalarMass_coupledParamDeriv (hasLinearGrowth_parisiStep hA hAm (s.m r) w)
      (measurable_parisiStep hAm (s.m r) w) hLip hv

/-- All unchanged outer levels preserve the local mass bound without depth
loss. Only nonnegativity of the inserted variance is needed here. -/
theorem section4RightMassD_props {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v V : ℝ} (hv : v ∈ Set.Icc 0 V)
    {j : ℕ} (hj : j ≤ r) :
    CoupledParamDeriv
      (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade
        (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) v)
        (k + 1 - r + 2 + j) (y 0))
      (section4RightMassD s β r v j) (Set.Ioo (-2) 2)
      (parisiMassFirstBound (4 * V)) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using section4RightMassD_base_props s β hr hv
  | succ j ih =>
    let p := k + 2 - (k + 1 - r + 2 + j)
    have hp : p < r := by dsimp [p]; omega
    have H := (ih (by omega)).secondStep (m := s.m p)
      (v := β ^ 2 * (s.q (p + 1) - s.q p)) isOpen_Ioo
      (s.m_nonneg (by omega))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega))))
    have he :
        (fun m (_ : Fin 1 → ℝ) y => scalarFieldCascade
          (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5RightVariance s β r (k + 2 - l) v)
          (k + 1 - r + 2 + (j + 1)) (y 0)) =
        (fun m (_ : Fin 1 → ℝ) y => parisiStepPi 1 (s.m p)
          (β ^ 2 * (s.q (p + 1) - s.q p))
          (fun z => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
            (fun l => section5RightVariance s β r (k + 2 - l) v)
            (k + 1 - r + 2 + j) (z 0)) y) := by
      funext m x y
      rw [show k + 1 - r + 2 + (j + 1) = (k + 1 - r + 2 + j) + 1 by omega,
        scalarFieldCascade]
      change parisiStep (section4Mass s r m p) (section5RightVariance s β r p v) _ _ = _
      simp only [section4Mass, section5RightVariance, if_pos hp]
      symm
      simpa using parisiStepPi_sum (n := 1) (s.m p) (β ^ 2 * (s.q (p + 1) - s.q p))
        (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1 y
    rw [he]
    exact H

/-- The explicit full-depth derivative in the new outer mass. -/
noncomputable def section4RightTMassD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (v m : ℝ) : ℝ := section4RightMassD s β r v r m 0 (fun _ => h)

/-- Genuine mass differentiation on an open neighborhood of every physical
mass, including zero and one. -/
theorem hasDerivAt_section4RightT_mass {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Ioo (-2) 2) (hv : 0 ≤ v) :
    HasDerivAt (fun a => section4RightT s β h r a v)
      (section4RightTMassD s β h r v m) m := by
  have H := (section4RightMassD_props s β hr (V := v) ⟨hv, le_rfl⟩
    (j := r) le_rfl).deriv m hm 0 (fun _ => h)
  have hi : k + 1 - r + 2 + r = k + 3 := by omega
  simpa only [hi, section4RightT, section4RightTMassD] using! H

/-- Twice the actual baseline derivative in the new outer mass. -/
noncomputable def section4RightU {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (v : ℝ) : ℝ :=
  2 * deriv (fun m => section4RightT s β h r m v) (s.m r)

/-- The actual baseline derivative, including both physical variance endpoints
and baseline mass zero. -/
theorem hasDerivAt_section4RightT_mass_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt (fun m => section4RightT s β h r m v)
      (section4RightU s β h r v / 2) (s.m r) := by
  have H := hasDerivAt_section4RightT_mass s β h hr
    (m := s.m r) ⟨by linarith [s.m_nonneg hr], by linarith [s.m_le_one hr]⟩ hv
  simpa only [section4RightU, mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)]
    using! H.differentiableAt.hasDerivAt

/-- A zero-variance inserted transform is independent of its mass. -/
theorem section4RightU_zero_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) : section4RightU s β h r 0 = 0 := by
  simp only [section4RightU, section4RightT_zero_variance s β h hr, deriv_const, mul_zero]

end SpinGlass.Targets
