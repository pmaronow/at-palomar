module

/-
# The outer Gaussian average of an individual cascade-variance derivative

Measurability follows from actual difference quotients and the proved disorder
continuity. The uniform derivative bound justifies differentiation under the
Gaussian expectation. No simultaneous multi-variance chain rule is asserted.
-/
public import Targets.CoupledNestedVariance
public import Targets.CoupledDisorderInterpolation

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem nonneg_update_variance {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i)
    (ℓ : ℕ) {w : ℝ} (hw : 0 ≤ w) : ∀ i, 0 ≤ Function.update v ℓ w i := by
  intro i
  by_cases hi : i = ℓ
  · subst i; simpa only [Function.update_self] using hw
  · simpa only [Function.update_of_ne hi] using hv i

/-- Actual disorder measurability of the propagated variance derivative.
The proof uses measurable forward difference quotients, not a postulated joint
regularity theorem for the nested heat expression. -/
theorem measurable_constrainedLevelVarianceD_disorder (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    Measurable (fun U : EnergySpace n => constrainedLevelVarianceD U u m v d ℓ j w x y) := by
  let F := fun (z : ℝ) (U : EnergySpace n) =>
    coupledFieldCascade n m (Function.update v ℓ z) d (constrainedPairFieldBase n U u) (ℓ + 1 + j) x y
  have hFm {z : ℝ} (hz : 0 ≤ z) : Measurable (F z) :=
    (continuous_constrainedPairFieldCascade_disorder u m (Function.update v ℓ z) hm
      (nonneg_update_variance hv ℓ hz) d (ℓ + 1 + j) x y).measurable
  apply measurable_of_tendsto_metrizable' (𝓝[>] (0 : ℝ))
    (f := fun t U => t⁻¹ * (F (w + max t 0) U - F w U))
    (fun t => ((hFm (by positivity)).sub (hFm hw.le)).const_mul t⁻¹)
  rw [tendsto_pi_nhds]
  intro U
  have H := (hasDerivAt_constrainedFieldCascade_variance U u m v hm hv d ℓ j x y hw).tendsto_slope_zero_right
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [F, max_eq_left (show 0 ≤ t from le_of_lt ht), smul_eq_mul]

section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The propagated variance derivative is bounded and integrable under the
actual Gaussian disorder law, at every fixed disorder amplitude. -/
theorem integrable_constrainedLevelVarianceD {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (fun ω => constrainedLevelVarianceD (a • Z ω) u m v d ℓ j w x y) ℙ := by
  apply (integrable_const (constrainedLevelHeatBound n m d ℓ)).mono'
    (((measurable_constrainedLevelVarianceD_disorder u m v hm hv d ℓ j x y hw).comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (constrainedLevelVarianceD_props (a • Z ω) u m v hm hv d ℓ j (w + 1)).bound
    w ⟨hw, by linarith⟩ x y

/-- The true Gaussian-averaged partial derivative in one original field
variance, with all unchanged variances and the disorder amplitude fixed. -/
theorem hasDerivAt_constrainedPairGaussian_variance {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z => ∫ ω, coupledFieldCascade n m (Function.update v ℓ z) d
      (constrainedPairFieldBase n (a • Z ω) u) (ℓ + 1 + j) x y ∂ℙ)
      (∫ ω, constrainedLevelVarianceD (a • Z ω) u m v d ℓ j w x y ∂ℙ) w := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
    (F := fun z ω => coupledFieldCascade n m (Function.update v ℓ z) d
      (constrainedPairFieldBase n (a • Z ω) u) (ℓ + 1 + j) x y)
    (F' := fun z ω => constrainedLevelVarianceD (a • Z ω) u m v d ℓ j z x y)
    (s := Set.Ioi 0) (isOpen_Ioi.mem_nhds hw)
    (bound := fun _ => constrainedLevelHeatBound n m d ℓ) ?_
    (integrable_constrainedPairFieldCascade_amplitude hZ a u m (Function.update v ℓ w) hm
      (nonneg_update_variance hv ℓ hw.le) d (ℓ + 1 + j) x y)
    (((measurable_constrainedLevelVarianceD_disorder u m v hm hv d ℓ j x y hw).comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · filter_upwards [isOpen_Ioi.mem_nhds hw] with z hz
    exact ((continuous_constrainedPairFieldCascade_disorder u m (Function.update v ℓ z) hm
      (nonneg_update_variance hv ℓ hz.le) d (ℓ + 1 + j) x y).measurable.comp
      (hZ.repr_measurable.const_smul a)).aestronglyMeasurable
  · filter_upwards with ω z hz
    rw [Real.norm_eq_abs]
    exact (constrainedLevelVarianceD_props (a • Z ω) u m v hm hv d ℓ j (z + 1)).bound
      z ⟨hz, by linarith⟩ x y
  · filter_upwards with ω z hz
    exact hasDerivAt_constrainedFieldCascade_variance (a • Z ω) u m v hm hv d ℓ j x y hz

/-- The same partial derivative for the actual site-normalized pressure. -/
theorem hasDerivAt_constrainedDisorderPressure_variance {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) (t : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z => constrainedDisorderPressure Z u m (Function.update v ℓ z) d (ℓ + 1 + j) x y t)
      ((1 / (n : ℝ)) * ∫ ω, constrainedLevelVarianceD (Real.sqrt t • Z ω) u m v d ℓ j w x y ∂ℙ) w := by
  exact (hasDerivAt_constrainedPairGaussian_variance hZ (Real.sqrt t) u m v hm hv d ℓ j x y hw).const_mul _

/-- Site normalization removes the factor N from the partial-derivative bound.
The estimate is uniform in fields, disorder amplitude and unchanged outer depth. -/
theorem constrainedDisorderPressure_variance_deriv_abs_le {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (hn : 0 < n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j)
    (d ℓ j : ℕ) (x y : Fin n → ℝ) (t : ℝ) {w : ℝ} (hw : 0 < w) :
    |deriv (fun z => constrainedDisorderPressure Z u m (Function.update v ℓ z) d (ℓ + 1 + j) x y t) w| ≤
      (if ℓ < d then 1 else 2) * (2 + 4 * ∑ l ∈ Finset.range ℓ, |m l| + |m ℓ|) := by
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hint := integrable_constrainedLevelVarianceD hZ (Real.sqrt t) u m v hm hv d ℓ j x y hw
  have hb (ω : Ω) : |constrainedLevelVarianceD (Real.sqrt t • Z ω) u m v d ℓ j w x y| ≤
      constrainedLevelHeatBound n m d ℓ :=
    (constrainedLevelVarianceD_props (Real.sqrt t • Z ω) u m v hm hv d ℓ j (w + 1)).bound
      w ⟨hw, by linarith⟩ x y
  have hI : |∫ ω, constrainedLevelVarianceD (Real.sqrt t • Z ω) u m v d ℓ j w x y ∂ℙ| ≤
      constrainedLevelHeatBound n m d ℓ := by
    calc
      _ ≤ ∫ ω, |constrainedLevelVarianceD (Real.sqrt t • Z ω) u m v d ℓ j w x y| ∂ℙ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, constrainedLevelHeatBound n m d ℓ ∂ℙ :=
        integral_mono hint.abs (integrable_const _) hb
      _ = _ := by simp
  rw [(hasDerivAt_constrainedDisorderPressure_variance hZ u m v hm hv d ℓ j x y t hw).deriv,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
  refine (mul_le_mul_of_nonneg_left hI (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))).trans_eq ?_
  rw [constrainedLevelHeatBound_eq]
  field_simp

end GaussianDisorder

end SpinGlass.Targets
