module

public import Targets.ConstrainedPathContinuity
public import Targets.CoupledDisorderInterpolation
public import Targets.Section5InterpolationPath

@[expose] public section

/-!
# Endpoint continuity of the actual second interpolation

Joint compact-parameter continuity of the constrained cascade and its proved
disorder Lipschitz bound justify the outer Gaussian limit. Both neighbor
constructions are covered with all variances moving, including zero faces.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The actual Gaussian average is continuous when its disorder amplitude,
every variance, and both fields move continuously on a compact parameter set. -/
theorem continuousOn_constrainedPairGaussian_path {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    {S : Set P} (hS : IsCompact S) (a : P → ℝ) (ha : ContinuousOn a S)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hvc : ∀ j, ContinuousOn (v j) S) (hv : ∀ j z, z ∈ S → 0 ≤ v j z)
    (d j : ℕ) (x y : P → Fin n → ℝ) (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun z => ∫ ω, coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (a z • Z ω) u) j (x z) (y z) ∂ℙ) S := by
  let F := fun (U : EnergySpace n) z => coupledFieldCascade n m (fun l => v l z) d
    (constrainedPairFieldBase n (a z • U) u) j (x z) (y z)
  have hF (U : EnergySpace n) : ContinuousOn (F U) S := by
    exact ((coupledContinuousOn_constrainedPairFieldBase u hS
      (ha.smul continuousOn_const)).fieldCascade hS m v hm hvc hv d j).continuous x y hx hy
  obtain ⟨C, hC⟩ := hS.bddAbove_image (hF 0).abs
  obtain ⟨A, hA⟩ := hS.bddAbove_image ha.abs
  apply continuousOn_of_dominated
    (bound := fun ω => C + (2 * |A| * Fintype.card (Config n)) * ‖Z ω‖)
  · intro z hz
    exact ((continuous_constrainedPairFieldCascade_disorder u m (fun l => v l z) hm
      (fun l => hv l z hz) d j (x z) (y z)).measurable.comp
        (hZ.repr_measurable.const_smul (a z))).aestronglyMeasurable
  · intro z hz
    filter_upwards with ω
    have H := constrainedPairFieldCascade_disorder_dist_le (a z • Z ω) 0 u m
      (fun l => v l z) hm (fun l => hv l z hz) d j (x z) (y z)
    simp only [sub_zero] at H
    have HN := uAbs_le_card_mul_norm n (a z • Z ω)
    rw [norm_smul, Real.norm_eq_abs] at HN
    have HA : |a z| ≤ |A| := (hA (Set.mem_image_of_mem _ hz)).trans (le_abs_self _)
    have H0 : |F 0 z| ≤ C := hC (Set.mem_image_of_mem _ hz)
    have HT := abs_sub_le (F (Z ω) z) (F 0 z) 0
    simp only [sub_zero] at HT
    have HD : |F (Z ω) z - F 0 z| ≤ 2 * uAbs n (a z • Z ω) := by
      simpa only [F, smul_zero] using H
    rw [Real.norm_eq_abs]
    change |F (Z ω) z| ≤ _
    nlinarith [mul_le_mul_of_nonneg_right HA (norm_nonneg (Z ω)),
      mul_nonneg (show 0 ≤ (Fintype.card (Config n) : ℝ) by positivity)
        (show 0 ≤ (|A| - |a z|) * ‖Z ω‖ from mul_nonneg (sub_nonneg.mpr HA) (norm_nonneg _))]
  · exact (integrable_const C).add ((integrable_norm_of_gaussian hZ).const_mul _)
  · exact Eventually.of_forall fun ω => hF (Z ω)

/-- Closed-interval continuity of Talagrand's actual left second interpolation. -/
theorem continuousOn_section5Interpolation {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (section5Interpolation n s β h Z r m t u) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => by unfold section5InterpolationVariance; fun_prop)
    (fun j w hw => section5InterpolationVariance_nonneg s β hr (by omega) ht hu hw)
    (k + 3 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

/-- The actual dual right interpolation is continuous at both endpoints too. -/
theorem continuousOn_section5RightInterpolation {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (section5RightInterpolation n s β h Z r m t u) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => by unfold section5RightInterpolationVariance; fun_prop)
    (fun j w hw => section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu hw)
    (k + 2 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

end SpinGlass.Targets
