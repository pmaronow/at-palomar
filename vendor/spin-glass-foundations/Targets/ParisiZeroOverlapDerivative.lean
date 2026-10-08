module

public import Targets.ParisiSlopeVariance
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# The squared-slope derivative when the outer variance starts at zero

At a zero scalar slope, rescaling the outer Gaussian amplitude by its square
root gives a genuine first-order limit. Existing scalar joint differentiation
and local variance bounds provide both the pointwise limit and an integrable
Gaussian quadratic bound. No variance-zero derivative is assigned by default.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The squared scalar slope with zero outer mass and complementary inner
variance. This is the initial-overlap competitor's actual normalized factor. -/
noncomputable def zeroOuterSquaredSlope (A A' : ℝ → ℝ) (m a h u : ℝ) : ℝ :=
  ∫ z, (stepD1 A A' m (a - u) (h + Real.sqrt u * z)) ^ 2 ∂(gaussianReal 0 1)

/-- At zero outer variance the observable is scalar evaluation. -/
theorem zeroOuterSquaredSlope_zero (A A' : ℝ → ℝ) (m a h : ℝ) :
    zeroOuterSquaredSlope A A' m a h 0 = (stepD1 A A' m a h) ^ 2 := by
  simp [zeroOuterSquaredSlope]

private theorem zeroOuter_rescaled_slope_tendsto {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 < a)
    (hzero : stepD1 A A' m a h = 0) (z : ℝ) :
    Tendsto (fun u => stepD1 A A' m (a - u) (h + Real.sqrt u * z) / Real.sqrt u)
      (𝓝[>] 0) (𝓝 (stepD2 A A' A'' m a h * z)) := by
  have hdV : HasDerivAt (fun θ : ℝ => a - θ ^ 2) 0 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub a using 1
    norm_num
  have hdX : HasDerivAt (fun θ : ℝ => h + θ * z) z 0 := by
    simpa only [one_mul, id_eq] using! ((hasDerivAt_id (0 : ℝ)).mul_const z).const_add h
  have hd := hasDerivAt_stepD1_variance_curve hA hC2 hcA'' hm hdV hdX
    (by simpa using ha)
  have ht := hd.tendsto_slope_zero_right
  simp only [zero_add, zero_pow (by norm_num : 2 ≠ 0), sub_zero, zero_mul, add_zero,
    hzero, smul_eq_mul] at ht
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact Real.sqrt_pos.mpr hu
  have H := ht.comp hsqrt
  rw [mul_comm z] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [Function.comp_def, Real.sq_sqrt hu.le, div_eq_mul_inv]
  ring

private theorem zeroOuter_rescaled_slope_bound {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m a h : ℝ} (hm : m ∈ Set.Icc 0 1) (ha : 0 < a)
    (hzero : stepD1 A A' m a h = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Set.Ioo 0 (min (a / 2) 1), ∀ z : ℝ,
      |stepD1 A A' m (a - u) (h + Real.sqrt u * z) / Real.sqrt u| ≤ |z| + K := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  let K := 3 * (Real.exp (Real.sqrt a * gAbsMoment) * gAbsExpMoment (Real.sqrt a)) /
    (2 * Real.sqrt (a / 2))
  have hb (w : ℝ) (hw : w ∈ Set.Icc (a / 2) a) (y : ℝ) :
      |stepD1Variance A A' A'' m w y| ≤ K :=
    abs_stepD1Variance_le_on_Icc hA hC2 hcA''.measurable hm (by positivity) hw y
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb a ⟨by linarith, le_rfl⟩ h)
  refine ⟨K, hK, ?_⟩
  intro u hu z
  have hua : u < a / 2 := hu.2.trans_le (min_le_left _ _)
  have hu1 : u ≤ 1 := hu.2.le.trans (min_le_right _ _)
  have hw : a - u ∈ Set.Icc (a / 2) a := ⟨by linarith, by linarith [hu.1]⟩
  have hV : |stepD1 A A' m (a - u) h - stepD1 A A' m a h| ≤ K * u := by
    have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => stepD1 A A' m w h) (f' := fun w => stepD1Variance A A' A'' m w h)
      (s := Set.Icc (a / 2) a) (C := K)
      (fun w hw => (hasDerivAt_stepD1_variance hA hC2 hcA''.measurable m h
        (lt_of_lt_of_le (by positivity : (0 : ℝ) < a / 2) hw.1)).hasDerivWithinAt)
      (fun w hw => by simpa only [Real.norm_eq_abs] using hb w hw h)
      (convex_Icc _ _) ⟨by linarith, le_rfl⟩ hw
    simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg, abs_of_pos hu.1] using H
  have hB := hasParisiC2_parisiStep_nonneg (v := a - u) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hcA''.measurable
  have hS : |stepD1 A A' m (a - u) (h + Real.sqrt u * z) - stepD1 A A' m (a - u) h| ≤
      Real.sqrt u * |z| := by
    have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := stepD1 A A' m (a - u)) (f' := stepD2 A A' A'' m (a - u))
      (s := Set.univ) (C := 1) (fun y _ => (hB.2.1 y).hasDerivWithinAt)
      (fun y _ => by simpa only [Real.norm_eq_abs] using hB.abs_second_le_one y)
      convex_univ (Set.mem_univ h) (Set.mem_univ (h + Real.sqrt u * z))
    simpa only [Real.norm_eq_abs, one_mul, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg u)] using H
  have hh := abs_sub_le (stepD1 A A' m (a - u) (h + Real.sqrt u * z))
    (stepD1 A A' m (a - u) h) 0
  rw [hzero, sub_zero] at hV
  simp only [sub_zero] at hh
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu.1
  have hs1 : Real.sqrt u ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hu1
  rw [abs_div, abs_of_pos hsu, div_le_iff₀ hsu]
  have hprod := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hK hsu.le)
  rw [mul_assoc, ← pow_two, Real.sq_sqrt hu.1.le, mul_one] at hprod
  nlinarith only [hh, hV, hS, hprod]

/-- At a vanishing scalar slope the actual zero-outer-mass mean has inward
variance derivative equal to the squared Hessian. This proves the endpoint
limit with Gaussian domination, retaining arbitrary masses in `[0,1]`. -/
theorem hasDerivWithinAt_zeroOuterSquaredSlope_zero {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m a h : ℝ} (hm : m ∈ Set.Icc 0 1) (ha : 0 < a)
    (hzero : stepD1 A A' m a h = 0) :
    HasDerivWithinAt (zeroOuterSquaredSlope A A' m a h)
      ((stepD2 A A' A'' m a h) ^ 2) (Set.Icc 0 a) 0 := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  obtain ⟨K, hK, hb⟩ := zeroOuter_rescaled_slope_bound hA hC2 hcA'' hm ha hzero
  let F := fun u z => (stepD1 A A' m (a - u) (h + Real.sqrt u * z) / Real.sqrt u) ^ 2
  have hbi : Integrable (fun z : ℝ => 2 * K ^ 2 + 2 * z ^ 2) (gaussianReal 0 1) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq).const_mul 2)
  have hint := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 1) (l := 𝓝[>] (0 : ℝ)) (F := F)
    (f := fun z => (stepD2 A A' A'' m a h * z) ^ 2)
    (fun z => 2 * K ^ 2 + 2 * z ^ 2) ?_ ?_ hbi ?_
  · have hmoment : (∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1)) = 1 := by
      have H := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_eq_integral measurable_id'.aemeasurable] at H
      simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using H
    have heq : (∫ z, (stepD2 A A' A'' m a h * z) ^ 2 ∂(gaussianReal 0 1)) =
        (stepD2 A A' A'' m a h) ^ 2 := by
      simp only [mul_pow, integral_const_mul, hmoment, mul_one]
    rw [heq] at hint
    apply hasDerivWithinAt_iff_tendsto_slope.mpr
    have hfilter : 𝓝[Set.Icc 0 a \ {(0 : ℝ)}] 0 ≤ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_mono _ (by
        intro u hu
        have hne : u ≠ 0 := by simpa only [Set.mem_singleton_iff] using hu.2
        exact lt_of_le_of_ne hu.1.1 (Ne.symm hne))
    apply (hint.mono_left hfilter).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hup : 0 < u := by
      have hne : u ≠ 0 := by simpa only [Set.mem_singleton_iff] using hu.2
      exact lt_of_le_of_ne hu.1.1 (Ne.symm hne)
    simp only [slope_def_field, sub_zero, F, div_pow, Real.sq_sqrt hup.le,
      integral_div, zeroOuterSquaredSlope, Real.sqrt_zero, zero_mul, add_zero,
      hzero, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
  · filter_upwards with u
    exact ((((measurable_stepD1 hcA.measurable hcA'.measurable m (a - u)).comp
      (measurable_tilt_shift u h)).div_const (Real.sqrt u)).pow_const 2).aestronglyMeasurable
  · have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u ∈ Set.Ioo 0 (min (a / 2) 1) := by
      have hlt : ∀ᶠ u : ℝ in 𝓝 0, u < min (a / 2) 1 :=
        Iio_mem_nhds (by positivity)
      filter_upwards [self_mem_nhdsWithin, hlt.filter_mono nhdsWithin_le_nhds] with u hu hu'
      exact ⟨hu, hu'⟩
    filter_upwards [hsmall] with u hu
    filter_upwards with z
    have H := hb u hu z
    have Hsquare := mul_self_le_mul_self (abs_nonneg _) H
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    nlinarith only [Hsquare, sq_abs z, sq_abs (stepD1 A A' m (a - u) (h + Real.sqrt u * z) / Real.sqrt u),
      sq_nonneg (|z| - K)]
  · filter_upwards with z
    exact (zeroOuter_rescaled_slope_tendsto hA hC2 hcA'' hm.1 ha hzero z).pow 2

/-- Specialization to every actual Parisi-recursion input. -/
theorem hasDerivWithinAt_zeroOuterSquaredSlope_parisiF_zero {k : ℕ}
    (s : RSBScheme k) (β : ℝ) (j : ℕ) {m a h : ℝ}
    (hm : m ∈ Set.Icc 0 1) (ha : 0 < a)
    (hzero : stepD1 (parisiF s β j) (parisiFDeriv s β j) m a h = 0) :
    HasDerivWithinAt
      (zeroOuterSquaredSlope (parisiF s β j) (parisiFDeriv s β j) m a h)
      ((stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m a h) ^ 2)
      (Set.Icc 0 a) 0 :=
  hasDerivWithinAt_zeroOuterSquaredSlope_zero (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (continuous_parisiFSecond s β j) hm ha hzero

end SpinGlass.Targets
