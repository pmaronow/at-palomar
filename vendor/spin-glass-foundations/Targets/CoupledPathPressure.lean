module

public import Targets.CoupledJointInterpolation

@[expose] public section

/-!
# Gaussian averaging of the simultaneous cascade derivative

The joint derivative is already proved for each fixed disorder. Here an
anchored bound on one common time neighborhood is affine in the disorder norm,
so it is integrable under the actual Gaussian law. Difference quotients give
measurability of the actual derivative, including locally constant zero faces.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- The actual time component of the proved joint derivative. -/
noncomputable def constrainedFieldCascadePathD (U : ℝ → EnergySpace n) (u : ℝ)
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (d j : ℕ) (x y : Fin n → ℝ) (w : ℝ) : ℝ :=
  (fderiv ℝ (fun q : CoupledJointField n => coupledFieldCascade n m (fun l => v l q.1) d
    (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y)) (1, 0, 0)

/-- A single time neighborhood works for every disorder and both replica fields.
The constant is affine in the disorder norm, not uniform in system size. -/
theorem constrainedFieldCascade_amplitude_path_anchored_bound
    (a : ℝ → ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (ha : DifferentiableAt ℝ a w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ᶠ z in 𝓝 w,
      ∀ (U : EnergySpace n) (x y : Fin n → ℝ),
      |coupledFieldCascade n m (fun l => v l z) d
          (constrainedPairFieldBase n (a z • U) u) j x y -
        coupledFieldCascade n m (fun l => v l w) d
          (constrainedPairFieldBase n (a w • U) u) j x y| ≤
        (A + B * ‖U‖) * |z - w| := by
  classical
  obtain ⟨Ca, hCa, hba⟩ := ha.isBigO_sub.exists_pos
  have hvl (l : Fin j) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z in 𝓝 w, |v l z - v l w| ≤ C * |z - w| := by
    obtain ⟨C, hC, hb⟩ := (hv l l.isLt).isBigO_sub.exists_pos
    exact ⟨C, hC, by simpa only [Real.norm_eq_abs] using hb.bound⟩
  choose Cv hCv hbv using hvl
  have hf (l : Fin j) : ∀ᶠ z in 𝓝 w,
      v l w = v l z ∨ (0 < v l w ∧ 0 < v l z) := by
    rcases hface l l.isLt with hp | hz
    · filter_upwards [(hv l l.isLt).continuousAt.eventually (lt_mem_nhds hp)] with z h
      exact Or.inr ⟨hp, h⟩
    · filter_upwards [hz] with z h
      exact Or.inl (hz.self_of_nhds.trans h.symm)
  let A := ∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l
  let B := 2 * Fintype.card (Config n) * Ca
  refine ⟨A, B, Finset.sum_nonneg (fun l _ =>
    mul_nonneg (constrainedLevelHeatBound_nonneg n m d l) (hCv l).le), by positivity, ?_⟩
  filter_upwards [hba.bound, Filter.eventually_all.mpr hbv,
    Filter.eventually_all.mpr hf, hnonneg] with z haz hvz hfz hnz
  intro U x y
  have H := constrainedFieldCascade_joint_dist_le (a w • U) (a z • U) u m
    (fun l => v l w) (fun l => v l z) hm hnonneg.self_of_nhds hnz d j
    (fun l hl => hfz ⟨l, hl⟩) x y x y
  simp only [sub_self, l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at H
  rw [← Fin.sum_univ_eq_sum_range, ← sub_smul, norm_smul, Real.norm_eq_abs] at H
  have hsum : (∑ l : Fin j, constrainedLevelHeatBound n m d l * |v l z - v l w|) ≤
      A * |z - w| := by
    change _ ≤ (∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l) * |z - w|
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hvz l)
        (constrainedLevelHeatBound_nonneg n m d l)
  have ha' : |a z - a w| ≤ Ca * |z - w| := by simpa only [Real.norm_eq_abs] using haz
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ha' (norm_nonneg U))
    (show 0 ≤ 2 * (Fintype.card (Config n) : ℝ) by positivity)
  dsimp only [B]
  nlinarith

/-- Disorder measurability of the actual simultaneous path derivative. -/
theorem measurable_constrainedFieldCascadePathD (a : ℝ → ℝ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (ha : DifferentiableAt ℝ a w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    Measurable (fun U : EnergySpace n =>
      constrainedFieldCascadePathD (fun z => a z • U) u m v d j x y w) := by
  let F := fun z (U : EnergySpace n) => coupledFieldCascade n m (fun l => max (v l z) 0) d
    (constrainedPairFieldBase n (a z • U) u) j x y
  have hFm (z : ℝ) : Measurable (F z) :=
    (continuous_constrainedPairFieldCascade_disorder u m (fun l => max (v l z) 0) hm
      (fun _ => le_max_right _ _) d j x y).measurable.comp (by fun_prop)
  apply measurable_of_tendsto_metrizable' (𝓝[>] (0 : ℝ))
    (f := fun t U => t⁻¹ * (F (w + t) U - F w U))
    (fun t => ((hFm (w + t)).sub (hFm w)).const_mul t⁻¹)
  rw [tendsto_pi_nhds]
  intro U
  have H := hasDerivAt_constrainedFieldCascade_path_fderiv (fun z => a z • U) u m v hm d j
    (ha.smul_const U) hv hnonneg hface x y
  have H' : HasDerivAt (fun z => F z U)
      (constrainedFieldCascadePathD (fun z => a z • U) u m v d j x y w) w := by
    apply H.congr_of_eventuallyEq
    filter_upwards [hnonneg] with z hz
    simp only [F, max_eq_left (hz _)]
  simpa only [smul_eq_mul] using H'.tendsto_slope_zero_right


section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The simultaneous derivative may be passed through the actual outer Gaussian
average. Its integrability and all local domination hypotheses are proved.
No independent-parameter partial derivative or replica formula is assumed. -/
theorem constrainedPairGaussian_path_derivative {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ → ℝ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (ha : DifferentiableAt ℝ a w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    Integrable (fun ω => constrainedFieldCascadePathD
      (fun z => a z • Z ω) u m v d j x y w) ℙ ∧
    HasDerivAt (fun z => ∫ ω, coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (a z • Z ω) u) j x y ∂ℙ)
      (∫ ω, constrainedFieldCascadePathD (fun z => a z • Z ω) u m v d j x y w ∂ℙ) w := by
  obtain ⟨A, B, hA, hB, hb⟩ :=
    constrainedFieldCascade_amplitude_path_anchored_bound (n := n) a u m v hm d j ha hv hnonneg hface
  let S := {z : ℝ | (∀ l, 0 ≤ v l z) ∧
    ∀ (U : EnergySpace n) (x y : Fin n → ℝ),
      |coupledFieldCascade n m (fun l => v l z) d
          (constrainedPairFieldBase n (a z • U) u) j x y -
        coupledFieldCascade n m (fun l => v l w) d
          (constrainedPairFieldBase n (a w • U) u) j x y| ≤
        (A + B * ‖U‖) * |z - w|}
  have hS : S ∈ 𝓝 w := hnonneg.and hb
  let D := fun ω => constrainedFieldCascadePathD (fun z => a z • Z ω) u m v d j x y w
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have he (z : ℝ) : L z 1 = z := by simp [L]
  have hDm : AEStronglyMeasurable D ℙ :=
    ((measurable_constrainedFieldCascadePathD a u m v hm d j ha hv hnonneg hface x y).comp
      hZ.repr_measurable).aestronglyMeasurable
  have HD (ω : Ω) : HasDerivAt (fun z => coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (a z • Z ω) u) j x y) (D ω) w :=
    hasDerivAt_constrainedFieldCascade_path_fderiv (fun z => a z • Z ω) u m v hm d j
      (ha.smul_const (Z ω)) hv hnonneg hface x y
  have H := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := (ℙ : Measure Ω)) (F := fun z ω => coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (a z • Z ω) u) j x y)
    (F' := fun ω => L (D ω)) hS
    (fun z hz => ((continuous_constrainedPairFieldCascade_disorder u m (fun l => v l z) hm
      hz.1 d j x y).measurable.comp (hZ.repr_measurable.const_smul (a z))).aestronglyMeasurable)
    (integrable_constrainedPairFieldCascade_amplitude hZ (a w) u m (fun l => v l w) hm
      hnonneg.self_of_nhds d j x y)
    (L.continuous.comp_aestronglyMeasurable hDm)
    (bound := fun ω => A + B * ‖Z ω‖)
    (Eventually.of_forall fun ω z hz => by
      simpa only [Real.norm_eq_abs] using hz.2 (Z ω) x y)
    ((integrable_const A).add ((integrable_norm_of_gaussian hZ).const_mul B))
    (Eventually.of_forall fun ω => (HD ω).hasFDerivAt)
  have hi : Integrable D ℙ := by
    simpa only [he] using H.1.apply_continuousLinearMap 1
  have hd := H.2.hasDerivAt
  rw [ContinuousLinearMap.integral_apply H.1] at hd
  exact ⟨hi, by simpa only [he] using hd⟩

theorem hasDerivAt_constrainedPairGaussian_path {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ → ℝ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {w : ℝ}
    (ha : DifferentiableAt ℝ a w)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasDerivAt (fun z => ∫ ω, coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (a z • Z ω) u) j x y ∂ℙ)
      (∫ ω, constrainedFieldCascadePathD (fun z => a z • Z ω) u m v d j x y w ∂ℙ) w :=
  (constrainedPairGaussian_path_derivative hZ a u m v hm d j ha hv hnonneg hface x y).2

end GaussianDisorder


end SpinGlass.Targets
