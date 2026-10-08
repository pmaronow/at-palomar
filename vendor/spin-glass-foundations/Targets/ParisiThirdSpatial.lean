module

public import Targets.ParisiSlopeVariance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The actual third spatial derivative after positive Gaussian smoothing

Only the proved C2 invariant is required of the input. Differentiating the
spatial FTC identity in variance proves the needed mixed derivative; the heat
equation then identifies the third spatial derivative. No commutation of
unproved partial derivatives or input third derivative is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The derivative of the finite spatial integral of B' may be passed through
the integral using the already proved common interior variance bound. -/
theorem hasDerivAt_integral_stepD1_variance {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (a b : ℝ) :
    HasDerivAt (fun w => ∫ y in a..b, stepD1 A A' m w y)
      (∫ y in a..b, stepD1Variance A A' A'' m v y) v := by
  have hcB := (continuous_parisiStep_variance_spatial hC2 hcA'' hm.1).2.1
  have hcV : Continuous (stepD1Variance A A' A'' m v) :=
    (continuousOn_stepD1Variance hA hC2 hcA'' m).comp_continuous
      (by fun_prop : Continuous (fun y : ℝ => (v, y))) (fun _ => ⟨hv, Set.mem_univ _⟩)
  let K := 3 * (Real.exp (Real.sqrt (v + 1) * gAbsMoment) * gAbsExpMoment (Real.sqrt (v + 1))) /
    (2 * Real.sqrt (v / 2))
  have hset : Set.Ioo (v / 2) (v + 1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have H (c d : ℝ) : HasDerivAt
      (fun w => ∫ y in Set.Ioc c d, stepD1 A A' m w y)
      (∫ y in Set.Ioc c d, stepD1Variance A A' A'' m v y) v := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc c d)) (F := fun w y => stepD1 A A' m w y)
      (F' := fun w y => stepD1Variance A A' A'' m w y) (bound := fun _ => K) hset
      ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · filter_upwards with w
      exact (hcB.comp (by fun_prop : Continuous (fun y : ℝ => (w, y)))).measurable.aestronglyMeasurable
    · exact ((hcB.comp (by fun_prop : Continuous (fun y : ℝ => (v, y)))).intervalIntegrable c d).1
    · exact hcV.measurable.aestronglyMeasurable
    · filter_upwards with y w hw
      simpa only [Real.norm_eq_abs, K] using abs_stepD1Variance_le_on_Icc hA hC2 hcA''.measurable
        hm (show 0 < v / 2 by positivity) ⟨hw.1.le, hw.2.le⟩ y
    · filter_upwards with y w hw
      exact hasDerivAt_stepD1_variance hA hC2 hcA''.measurable m y (by linarith [hw.1])
  exact (H a b).sub (H b a)

/-- Spatial increments of the actual heat velocity are integrals of the proved
variance derivative of B'. This is the justified mixed-derivative identity. -/
theorem parisiStep_heatVelocity_sub_eq_integral {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    (stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2) / 2 -
      (stepD2 A A' A'' m v 0 + m * (stepD1 A A' m v 0) ^ 2) / 2 =
      ∫ y in (0 : ℝ)..x, stepD1Variance A A' A'' m v y := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hFTC (w : ℝ) : (∫ y in (0 : ℝ)..x, stepD1 A A' m w y) =
      parisiStep m w A x - parisiStep m w A 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_parisiStep_spatial hA hcA.measurable hcA'.measurable hC2.1
        hC2.abs_first_le_one m w y)
      (((continuous_parisiStep_variance_spatial hC2 hcA'' hm.1).2.1.comp
        (by fun_prop : Continuous (fun y : ℝ => (w, y)))).intervalIntegrable 0 x)
  have H := hasDerivAt_integral_stepD1_variance hA hC2 hcA'' hm hv 0 x
  simp only [hFTC] at H
  exact ((hasDerivAt_parisiStep_variance hA hC2 hcA.measurable hcA'.measurable hcA''.measurable m x hv).sub
    (hasDerivAt_parisiStep_variance hA hC2 hcA.measurable hcA'.measurable hcA''.measurable m 0 hv)).unique H

/-- The spatial derivative of the actual heat velocity is the already proved
variance derivative of B'. -/
theorem hasDerivAt_parisiStep_heatVelocity_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (fun y => (stepD2 A A' A'' m v y + m * (stepD1 A A' m v y) ^ 2) / 2)
      (stepD1Variance A A' A'' m v x) x := by
  have hc : Continuous (stepD1Variance A A' A'' m v) :=
    (continuousOn_stepD1Variance hA hC2 hcA'' m).comp_continuous
      (by fun_prop : Continuous (fun y : ℝ => (v, y))) (fun _ => ⟨hv, Set.mem_univ _⟩)
  have H := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const
      ((stepD2 A A' A'' m v 0 + m * (stepD1 A A' m v 0) ^ 2) / 2)
  have he (y : ℝ) : (∫ z in (0 : ℝ)..y, stepD1Variance A A' A'' m v z) +
      (stepD2 A A' A'' m v 0 + m * (stepD1 A A' m v 0) ^ 2) / 2 =
      (stepD2 A A' A'' m v y + m * (stepD1 A A' m v y) ^ 2) / 2 := by
    rw [← parisiStep_heatVelocity_sub_eq_integral hA hC2 hcA'' hm hv y]
    ring
  simpa only [he] using H

/-- The actual third spatial derivative after positive Gaussian smoothing.
It is derived from the proved slope variance rule rather than postulated. -/
noncomputable def stepD3 (A A' A'' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  2 * stepD1Variance A A' A'' m v x -
    2 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x

theorem hasDerivAt_stepD2_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (stepD2 A A' A'' m v) (stepD3 A A' A'' m v x) x := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have H := (hasDerivAt_parisiStep_heatVelocity_spatial hA hC2 hcA'' hm hv x).const_mul 2
  have HS := (hasDerivAt_parisiStep_spatial_second hA hcA.measurable hcA'.measurable
    hcA''.measurable hC2 m v x).pow 2 |>.const_mul m
  convert! H.sub HS using 1
  · funext y
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  · dsimp only [stepD3]
    ring

theorem continuous_stepD3_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) {v : ℝ} (hv : 0 < v) :
    Continuous (stepD3 A A' A'' m v) := by
  have hcV : Continuous (stepD1Variance A A' A'' m v) :=
    (continuousOn_stepD1Variance hA hC2 hcA'' m).comp_continuous
      (by fun_prop : Continuous (fun y : ℝ => (v, y))) (fun _ => ⟨hv, Set.mem_univ _⟩)
  have hc := continuous_parisiStep_variance_spatial hC2 hcA'' hm
  have hmap : Continuous (fun y : ℝ => (v, y)) := by fun_prop
  exact (hcV.const_mul 2).sub (((hc.2.1.comp hmap).const_mul (2 * m)).mul (hc.2.2.comp hmap))

/-- The third derivative's bound is independent of the field and input depth;
the positive-variance restriction is explicit. -/
theorem abs_stepD3_le {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    |stepD3 A A' A'' m v x| ≤
      2 * ((1 + 2 * m) * (Real.exp ((m * Real.sqrt v) * gAbsMoment) *
        gAbsExpMoment (m * Real.sqrt v)) / (2 * Real.sqrt v)) + 2 := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hb := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  have hprod : |stepD1 A A' m v x| * |stepD2 A A' A'' m v x| ≤ 1 :=
    mul_le_one₀ (hb.abs_first_le_one x) (abs_nonneg _) (hb.abs_second_le_one x)
  have hh := abs_sub (2 * stepD1Variance A A' A'' m v x)
    (2 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x)
  simp only [abs_mul, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hp := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm.1)
  dsimp only [stepD3]
  nlinarith [abs_stepD1Variance_le hA hC2 hcA''.measurable hm hv x, hm.2]

/-- Actual Parisi inputs satisfy every hypothesis of the new third derivative. -/
theorem hasDerivAt_stepD2_parisiF_spatial {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v)
      (stepD3 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v x) x :=
  hasDerivAt_stepD2_spatial (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm hv x

end SpinGlass.Targets
