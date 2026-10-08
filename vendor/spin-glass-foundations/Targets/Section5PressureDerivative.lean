module

public import Targets.CoupledPathPressureFormula
public import Targets.Section5InterpolationContinuity

@[expose] public section

/-!
# The actual second-interpolation pressure derivatives

Both physical paths are differentiated through all field levels and the outer
Gaussian disorder average. The results retain the genuine joint derivative and
identify its Gaussian trace and finite heat contributions. Replica-overlap
identification is a separate step.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Genuine derivative of the Gaussian-averaged left interpolation. -/
theorem hasDerivAt_section5Interpolation
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5Interpolation n s β h Z r m t u)
      ((1 / (n : ℝ)) * ∫ ω, constrainedFieldCascadePathD
        (fun z => Real.sqrt (z * t) • Z ω) u
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance s β t u r (k + 2 - j))
        (k + 3 - r) (k + 3) (fun _ => h) (fun _ => h) w ∂ℙ) w := by
  have H := hasDerivAt_constrainedPairGaussian_path hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega)) (k + 3 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1).differentiableAt
    (fun j _ => (hasDerivAt_section5InterpolationVariance s β t u r (k + 2 - j) w).differentiableAt)
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5InterpolationVariance s β t u r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5InterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5InterpolationVariance s β t u r (k + 2 - j) w ∨
      (section5InterpolationVariance s β t u r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5InterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
        hr (by omega) ht hu hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  exact H.const_mul (1 / (n : ℝ))

/-- Differentiability of the actual left pressure throughout the open interval. -/
theorem differentiableOn_section5Interpolation
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    DifferentiableOn ℝ (section5Interpolation n s β h Z r m t u) (Set.Ioo 0 1) :=
  fun _ hw => (hasDerivAt_section5Interpolation s β h hZ hr hm ht hu hw).differentiableAt.differentiableWithinAt

/-- Genuine derivative of the Gaussian-averaged right interpolation. -/
theorem hasDerivAt_section5RightInterpolation
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5RightInterpolation n s β h Z r m t u)
      ((1 / (n : ℝ)) * ∫ ω, constrainedFieldCascadePathD
        (fun z => Real.sqrt (z * t) • Z ω) u
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j))
        (k + 2 - r) (k + 3) (fun _ => h) (fun _ => h) w ∂ℙ) w := by
  have H := hasDerivAt_constrainedPairGaussian_path hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega)) (k + 2 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1).differentiableAt
    (fun j _ => (hasDerivAt_section5RightInterpolationVariance s β t u r (k + 2 - j) w).differentiableAt)
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5RightInterpolationVariance s β t u r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5RightInterpolationVariance s β t u r (k + 2 - j) w ∨
      (section5RightInterpolationVariance s β t u r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5RightInterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
        hr (by omega) ht hu hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  exact H.const_mul (1 / (n : ℝ))

/-- Differentiability of the actual right pressure throughout the open interval. -/
theorem differentiableOn_section5RightInterpolation
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    DifferentiableOn ℝ (section5RightInterpolation n s β h Z r m t u) (Set.Ioo 0 1) :=
  fun _ hw => (hasDerivAt_section5RightInterpolation s β h hZ hr hm ht hu hw).differentiableAt.differentiableWithinAt


private theorem sqrt_time_derivative_mul {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

/-- Explicit trace-plus-heat formula for the actual left pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_section5Interpolation_trace
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5Interpolation n s β h Z r m t u)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5Mass s r m (k + 2 - j))
          (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w)
          (k + 3 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * β ^ 2 * (section5Rho s r u (k + 2 - l + 1) -
            section5Rho s r u (k + 2 - l)))) *
          (if 0 < section5InterpolationVariance s β t u r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5Mass s r m (k + 2 - j))
              (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w)
              (k + 3 - r) l (k + 3 - (l + 1))
              (section5InterpolationVariance s β t u r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega)) (k + 3 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5InterpolationVariance s β t u r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5InterpolationVariance s β t u r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5InterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5InterpolationVariance s β t u r (k + 2 - j) w ∨
      (section5InterpolationVariance s β t u r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5InterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
        hr (by omega) ht hu hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [section5Interpolation, sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))

/-- Explicit trace-plus-heat formula for the actual right pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_section5RightInterpolation_trace
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5RightInterpolation n s β h Z r m t u)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5RightMass s r m (k + 2 - j))
          (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w)
          (k + 2 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * β ^ 2 * (section5RightRho s r u (k + 2 - l + 1) -
            section5RightRho s r u (k + 2 - l)))) *
          (if 0 < section5RightInterpolationVariance s β t u r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5RightMass s r m (k + 2 - j))
              (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w)
              (k + 2 - r) l (k + 3 - (l + 1))
              (section5RightInterpolationVariance s β t u r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega)) (k + 2 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5RightInterpolationVariance s β t u r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5RightInterpolationVariance s β t u r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5RightInterpolationVariance_nonneg s β hr (by omega) ht hu ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5RightInterpolationVariance s β t u r (k + 2 - j) w ∨
      (section5RightInterpolationVariance s β t u r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5RightInterpolationVariance_pos_or_eq_zero s β (p := k + 2 - j)
        hr (by omega) ht hu hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [section5RightInterpolation, sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))


end SpinGlass.Targets
