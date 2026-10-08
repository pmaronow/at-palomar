module

public import Targets.MixedNestedVariance
public import Targets.MixedDisorderInterpolation
public import Targets.MixedPathPressure
public import Targets.CoupledVariancePressure

@[expose] public section

/-!
# Gaussian averaging of the actual mixed variance derivative

Measurable forward difference quotients identify the actual propagated heat
derivative as a measurable disorder observable. Its checked uniform bound
then supplies Gaussian integrability, without additional joint regularity of
the nested heat expression.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem measurable_mixedLevelVarianceD_disorder (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    Measurable (fun U : EnergySpace n => mixedLevelVarianceD U u mode m v ℓ j w x y) := by
  let F := fun (z : ℝ) (U : EnergySpace n) =>
    mixedVectorCascade n mode m (Function.update v ℓ z) (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y
  have hFm {z : ℝ} (hz : 0 ≤ z) : Measurable (F z) :=
    (continuous_mixedConstrainedCascade_disorder u mode m (Function.update v ℓ z) hm
      (nonneg_update_variance hv ℓ hz) (ℓ + 1 + j) x y).measurable
  apply measurable_of_tendsto_metrizable' (𝓝[>] (0 : ℝ))
    (f := fun t U => t⁻¹ * (F (w + max t 0) U - F w U))
    (fun t => ((hFm (by positivity)).sub (hFm hw.le)).const_mul t⁻¹)
  rw [tendsto_pi_nhds]
  intro U
  have H := (hasDerivAt_mixedConstrainedCascade_variance U u mode m v hm hv ℓ j x y hw).tendsto_slope_zero_right
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [F, max_eq_left (show 0 ≤ t from le_of_lt ht), smul_eq_mul]

section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The genuine propagated mixed variance derivative is bounded and
integrable under the original Gaussian disorder law. -/
theorem integrable_mixedLevelVarianceD {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (fun ω => mixedLevelVarianceD (a • Z ω) u mode m v ℓ j w x y) ℙ := by
  apply (integrable_const (mixedLevelHeatBound n mode m ℓ)).mono'
    (((measurable_mixedLevelVarianceD_disorder u mode m v hm hv ℓ j x y hw).comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (mixedLevelVarianceD_props (a • Z ω) u mode m v hm hv ℓ j (w + 1)).bound
    w ⟨hw, by linarith⟩ x y

/-- The actual Gaussian-averaged partial derivative in one original variance,
with the disorder amplitude and all other mixed levels fixed. -/
theorem hasDerivAt_mixedConstrainedGaussian_variance {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z => ∫ ω, mixedVectorCascade n mode m (Function.update v ℓ z)
      (constrainedPairFieldBase n (a • Z ω) u) (ℓ + 1 + j) x y ∂ℙ)
      (∫ ω, mixedLevelVarianceD (a • Z ω) u mode m v ℓ j w x y ∂ℙ) w := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
    (F := fun z ω => mixedVectorCascade n mode m (Function.update v ℓ z)
      (constrainedPairFieldBase n (a • Z ω) u) (ℓ + 1 + j) x y)
    (F' := fun z ω => mixedLevelVarianceD (a • Z ω) u mode m v ℓ j z x y)
    (s := Set.Ioi 0) (isOpen_Ioi.mem_nhds hw)
    (bound := fun _ => mixedLevelHeatBound n mode m ℓ) ?_
    (integrable_mixedConstrainedCascade_amplitude hZ a u mode m (Function.update v ℓ w) hm
      (nonneg_update_variance hv ℓ hw.le) (ℓ + 1 + j) x y)
    (((measurable_mixedLevelVarianceD_disorder u mode m v hm hv ℓ j x y hw).comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · filter_upwards [isOpen_Ioi.mem_nhds hw] with z hz
    exact ((continuous_mixedConstrainedCascade_disorder u mode m (Function.update v ℓ z) hm
      (nonneg_update_variance hv ℓ hz.le) (ℓ + 1 + j) x y).measurable.comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable
  · filter_upwards with ω z hz
    rw [Real.norm_eq_abs]
    exact (mixedLevelVarianceD_props (a • Z ω) u mode m v hm hv ℓ j (z + 1)).bound
      z ⟨hz, by linarith⟩ x y
  · filter_upwards with ω z hz
    exact hasDerivAt_mixedConstrainedCascade_variance (a • Z ω) u mode m v hm hv ℓ j x y hz

end GaussianDisorder

end SpinGlass.Targets
