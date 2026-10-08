module

public import Targets.ParisiThirdSpatial

@[expose] public section

/-!
# The baseline squared-slope identity in Section 4

The two equal-mass steps have constant total potential. Their normalized
squared-slope observable is differentiated on the physical open split interval.
The actual third spatial derivative supplies the Gaussian Stein cancellation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem scalar_C2_lipschitz' {A A' A'' : ℝ → ℝ} (hC2 : HasParisiC2 A A' A'')
    (x y : ℝ) : |A x - A y| ≤ 1 * |x - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := A') (s := Set.univ) (C := 1)
    (fun z _ => (hC2.1 z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

private theorem tiltWeight_eq_exp_sub {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m v x z : ℝ) :
    tiltWeight m v A x z = Real.exp (m * (A (x + Real.sqrt v * z) - parisiStep m v A x)) := by
  by_cases hm : m = 0
  · simp [hm, tiltWeight]
  · rw [tiltWeight, if_neg hm, parisiStep, if_neg hm, mul_sub, Real.exp_sub]
    rw [show m * (1 / m * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1))) =
      Real.log (∫ z, Real.exp (m * A (x + Real.sqrt v * z)) ∂(gaussianReal 0 1)) by field_simp]
    rw [Real.exp_log (smoothing_integral_pos hA hAm x)]

/-- The equal-mass outer weight has a genuinely constant baseline potential. -/
theorem splitBaselineWeight_eq {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m a x z : ℝ) {v : ℝ}
    (hv : v ∈ Set.Icc 0 a) :
    tiltWeight m (a - v) (parisiStep m v A) x z =
      Real.exp (m * (parisiStep m v A (x + Real.sqrt (a - v) * z) - parisiStep m a A x)) := by
  rw [tiltWeight_eq_exp_sub (hasLinearGrowth_parisiStep hA hAm m v) (measurable_parisiStep hAm m v)]
  have H := congrFun (parisiStep_add m (a - v) v (sub_nonneg.mpr hv.2) hv.1 hA hAm) x
  rw [sub_add_cancel] at H
  rw [← H]

/-- The actual equal-mass squared-slope mean in (4.16), before unchanged
outer levels are applied. -/
noncomputable def splitBaselineSlopeQ (A A' : ℝ → ℝ) (m a x v : ℝ) : ℝ :=
  ∫ z, (stepD1 A A' m v (x + Real.sqrt (a - v) * z)) ^ 2 *
    tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)

private theorem tilted_bounded_integrable {F G : ℝ → ℝ} {B m v : ℝ}
    (hF : HasLinearGrowth F) (hFm : Measurable F)
    (hLip : ∀ x y, |F x - F y| ≤ 1 * |x - y|)
    (hGm : Measurable G) (hG : ∀ x, |G x| ≤ B) (x : ℝ) :
    Integrable (fun z => G (x + Real.sqrt v * z) * tiltWeight m v F x z) (gaussianReal 0 1) :=
  integrable_mul_tiltWeight_of_bound zero_le_one hLip hF hFm x
    (hGm.comp (measurable_tilt_shift v x)) (b := 0) le_rfl (a := B) (by simpa using fun z => hG (x + Real.sqrt v * z))

/-- Scalar Gaussian Stein with a general bounded C1 observable under the
actual normalized tilt. Both mass-zero and variance-zero weights are retained. -/
theorem integral_gaussian_mul_tilted_observable {F F' G G' : ℝ → ℝ} {B C : ℝ}
    (hF : HasLinearGrowth F) (hFm : Measurable F) (hF'm : Measurable F')
    (hFd : ∀ x, HasDerivAt F (F' x) x) (hFb : ∀ x, |F' x| ≤ 1)
    (hGd : ∀ x, HasDerivAt G (G' x) x) (hG'm : Measurable G')
    (hGb : ∀ x, |G x| ≤ B) (hG'b : ∀ x, |G' x| ≤ C) (m v x : ℝ) :
    (∫ z, z * (G (x + Real.sqrt v * z) * tiltWeight m v F x z) ∂(gaussianReal 0 1)) =
      Real.sqrt v * ∫ z, (G' (x + Real.sqrt v * z) + m * G (x + Real.sqrt v * z) * F' (x + Real.sqrt v * z)) *
        tiltWeight m v F x z ∂(gaussianReal 0 1) := by
  have hLip (y z : ℝ) : |F y - F z| ≤ 1 * |y - z| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := F) (f' := F') (s := Set.univ) (C := 1) (fun t _ => (hFd t).hasDerivWithinAt)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hFb t) convex_univ (Set.mem_univ z) (Set.mem_univ y)
  have hGm : Measurable G := (continuous_iff_continuousAt.mpr fun y => (hGd y).continuousAt).measurable
  have hB : 0 ≤ B := (abs_nonneg (G 0)).trans (hGb 0)
  have hgi := tilted_bounded_integrable hF hFm hLip hGm hGb (m := m) (v := v) x
  have hxgi : Integrable (fun z => z * (G (x + Real.sqrt v * z) * tiltWeight m v F x z)) (gaussianReal 0 1) := by
    have H := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one hLip hF hFm x
      (measurable_id.mul (hGm.comp (measurable_tilt_shift v x))) (b := B) hB (a := 0)
      (fun z => by simpa only [zero_add, abs_mul, mul_comm, Pi.mul_apply, Function.comp_def, id_eq] using
        mul_le_mul_of_nonneg_left (hGb (x + Real.sqrt v * z)) (abs_nonneg z))
    simpa only [mul_assoc, Pi.mul_apply, Function.comp_def, id_eq] using H
  have hgb (y : ℝ) : |G' y + m * G y * F' y| ≤ C + |m| * B := by
    have hp := mul_le_mul (hGb y) (hFb y) (abs_nonneg _) hB
    have hh := abs_add_le (G' y) (m * G y * F' y)
    simp only [abs_mul] at hh
    nlinarith [hG'b y, mul_le_mul_of_nonneg_left hp (abs_nonneg m)]
  have hg'i := tilted_bounded_integrable hF hFm hLip
    (hG'm.add ((hGm.const_mul m).mul hF'm)) hgb (m := m) (v := v) x
  have hW (z : ℝ) : HasDerivAt (fun z => tiltWeight m v F x z)
      (Real.sqrt v * m * F' (x + Real.sqrt v * z) * tiltWeight m v F x z) z := by
    simp_rw [tiltWeight_eq_exp_sub hF hFm]
    have H := (((hFd _).comp z (((hasDerivAt_id z).const_mul (Real.sqrt v)).const_add x)).sub_const
      (parisiStep m v F x)).const_mul m |>.exp
    convert! H using 1
    simp only [Function.comp_def, id_eq, mul_one]
    ring
  have H := gaussianReal_stein_of_hasDerivAt
    (fun z => G (x + Real.sqrt v * z) * tiltWeight m v F x z)
    (fun z => Real.sqrt v * ((G' (x + Real.sqrt v * z) + m * G (x + Real.sqrt v * z) * F' (x + Real.sqrt v * z)) *
      tiltWeight m v F x z)) (fun z => ?_) hgi hxgi (hg'i.const_mul (Real.sqrt v))
  · simpa only [integral_const_mul] using H
  · have hd := ((hGd _).comp z (((hasDerivAt_id z).const_mul (Real.sqrt v)).const_add x)).mul (hW z)
    convert! hd using 1
    simp only [Function.comp_def, id_eq, mul_one]
    ring

/-- The explicit derivative before normalized averaging and Stein cancellation. -/
noncomputable def splitBaselineSlopeVelocity (A A' A'' : ℝ → ℝ) (m a x v z : ℝ) : ℝ :=
  let y := x + Real.sqrt (a - v) * z
  2 * stepD1 A A' m v y *
      (stepD1Variance A A' A'' m v y - z / (2 * Real.sqrt (a - v)) * stepD2 A A' A'' m v y) +
    m * (stepD1 A A' m v y) ^ 2 * splitVarianceVelocity A A' A'' m a x v z

private theorem baseline_weight_le {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (x z : ℝ) :
    tiltWeight m (a - v) (parisiStep m v A) x z ≤
      Real.exp (Real.sqrt a * gAbsMoment) * Real.exp (Real.sqrt a * |z|) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  have H := tiltWeight_le (m := m) (v := a - v) zero_le_one (scalar_C2_lipschitz' hB)
    (hasLinearGrowth_parisiStep hA hcA.measurable m v) (measurable_parisiStep hcA.measurable m v) x z
  simp only [mul_one, abs_of_nonneg hm.1] at H
  have hcoef : m * Real.sqrt (a - v) ≤ Real.sqrt a := by
    have h := mul_le_mul_of_nonneg_right hm.2 (Real.sqrt_nonneg (a - v))
    simp only [one_mul] at h
    exact h.trans (Real.sqrt_le_sqrt (by linarith [hv.1]))
  exact H.trans (mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcoef gAbsMoment_nonneg))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcoef (abs_nonneg z)))
    (Real.exp_pos _).le (Real.exp_pos _).le)

private theorem baseline_slope_velocity_bound {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {a lo hi w : ℝ}
    (hlo : 0 < lo) (hhi : hi < a) (hw : w ∈ Set.Icc lo hi) (x z : ℝ) :
    |splitBaselineSlopeVelocity A A' A'' m a x w z| ≤
      2 * (3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) /
        (2 * Real.sqrt lo)) + 1 / 2 + 3 * (1 / (2 * Real.sqrt (a - hi))) * |z| := by
  let y := x + Real.sqrt (a - w) * z
  let K := 3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) /
    (2 * Real.sqrt lo)
  let L := 1 / (2 * Real.sqrt (a - hi))
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  have hv : w ∈ Set.Ioo 0 a := ⟨hlo.trans_le hw.1, hw.2.trans_lt hhi⟩
  have hK := abs_stepD1Variance_le_on_Icc hA hC2 hcA''.measurable hm hlo hw y
  change |stepD1Variance A A' A'' m w y| ≤ K at hK
  have hKn : 0 ≤ K := (abs_nonneg _).trans hK
  have hLn : 0 ≤ L := by dsimp [L]; positivity
  have hc : |z / (2 * Real.sqrt (a - w))| ≤ L * |z| := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (sub_pos.mpr hv.2)))]
    have h : 1 / (2 * Real.sqrt (a - w)) ≤ L :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) (Real.sqrt_pos.mpr (sub_pos.mpr hhi)))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hw.2])) (by norm_num))
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_left h (abs_nonneg z)
  have hS := hB.abs_first_le_one y
  have hD := hB.abs_second_le_one y
  have hS2 : (stepD1 A A' m w y) ^ 2 ≤ 1 := by nlinarith [sq_abs (stepD1 A A' m w y), abs_nonneg (stepD1 A A' m w y)]
  have hSV : |stepD1Variance A A' A'' m w y - z / (2 * Real.sqrt (a - w)) * stepD2 A A' A'' m w y| ≤
      K + L * |z| := by
    have hh := abs_sub (stepD1Variance A A' A'' m w y)
      (z / (2 * Real.sqrt (a - w)) * stepD2 A A' A'' m w y)
    rw [abs_mul] at hh
    nlinarith [mul_le_mul hc hD (abs_nonneg _) (mul_nonneg hLn (abs_nonneg z))]
  have hHV : (stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2 ∈ Set.Icc 0 (1 / 2) := by
    have H := deriv_parisiStep_variance_mem_Icc hA hC2 hcA.measurable hcA'.measurable hcA''.measurable hm y hv.1
    rwa [(hasDerivAt_parisiStep_variance hA hC2 hcA.measurable hcA'.measurable hcA''.measurable m y hv.1).deriv] at H
  have hBV : |splitVarianceVelocity A A' A'' m a x w z| ≤ 1 / 2 + L * |z| := by
    have hh := abs_sub ((stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2)
      (z / (2 * Real.sqrt (a - w)) * stepD1 A A' m w y)
    rw [abs_of_nonneg hHV.1, abs_mul] at hh
    change |_ - _| ≤ _
    nlinarith [mul_le_mul hc hS (abs_nonneg _) (mul_nonneg hLn (abs_nonneg z)), hHV.2]
  have h1 := mul_le_mul hS hSV (abs_nonneg _) zero_le_one
  have h2 := mul_le_mul hS2 hBV (abs_nonneg _) zero_le_one
  have h3 := mul_le_mul_of_nonneg_left h2 hm.1
  have h4 := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 1 / 2 + L * |z|)
  have hh := abs_add_le
    (2 * stepD1 A A' m w y * (stepD1Variance A A' A'' m w y - z / (2 * Real.sqrt (a - w)) * stepD2 A A' A'' m w y))
    (m * (stepD1 A A' m w y) ^ 2 * splitVarianceVelocity A A' A'' m a x w z)
  simp only [abs_mul, abs_of_nonneg hm.1, abs_pow, sq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  change |_ + _| ≤ _
  change _ ≤ 2 * K + 1 / 2 + 3 * L * |z|
  nlinarith

/-- Actual differentiation of the two-step normalized squared-slope mean,
before Gaussian Stein cancellation. Local domination is proved, not assumed. -/
theorem hasDerivAt_splitBaselineSlopeQ_before_ibp {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (splitBaselineSlopeQ A A' m a x)
      (∫ z, splitBaselineSlopeVelocity A A' A'' m a x v z *
        tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  let lo := v / 2
  let hi := (a + v) / 2
  let J := Set.Icc lo hi
  let K := 3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) / (2 * Real.sqrt lo)
  let L := 1 / (2 * Real.sqrt (a - hi))
  let C := Real.exp (Real.sqrt a * gAbsMoment)
  have hlo : 0 < lo := div_pos hv.1 (by norm_num)
  have hhi : hi < a := by dsimp [hi]; linarith [hv.2]
  have hJ : J ∈ 𝓝 v := Icc_mem_nhds (by dsimp [lo]; linarith [hv.1]) (by dsimp [hi]; linarith [hv.2])
  have hJ' (w : ℝ) (hw : w ∈ J) : w ∈ Set.Ioo 0 a := ⟨hlo.trans_le hw.1, hw.2.trans_lt hhi⟩
  let F := fun w z => (stepD1 A A' m w (x + Real.sqrt (a - w) * z)) ^ 2 *
    tiltWeight m (a - w) (parisiStep m w A) x z
  let D := fun w z => splitBaselineSlopeVelocity A A' A'' m a x w z *
    tiltWeight m (a - w) (parisiStep m w A) x z
  have hWm (w : ℝ) := measurable_tiltWeight (measurable_parisiStep hcA.measurable m w) x (m := m) (v := a - w)
  have hSm (w : ℝ) := (measurable_stepD1 hcA.measurable hcA'.measurable m w).comp (measurable_tilt_shift (a - w) x)
  have hDm : Measurable (D v) := by
    have hcV := (continuousOn_stepD1Variance hA hC2 hcA'' m).comp_continuous
      (by fun_prop : Continuous (fun z : ℝ => (v, x + Real.sqrt (a - v) * z)))
      (fun _ => ⟨hv.1, Set.mem_univ _⟩)
    have hDD := (measurable_stepD2 hcA.measurable hcA'.measurable hcA''.measurable m v).comp (measurable_tilt_shift (a - v) x)
    dsimp only [D, splitBaselineSlopeVelocity, splitVarianceVelocity]
    exact (((hSm v).const_mul 2).mul (hcV.measurable.sub ((measurable_id.div_const _).mul hDD)) |>.add
      (((hSm v).pow_const 2).const_mul m |>.mul ((hDD.add (((hSm v).pow_const 2).const_mul m)).div_const 2 |>.sub
        ((measurable_id.div_const _).mul (hSm v))))).mul (hWm v)
  have hd (w : ℝ) (hw : w ∈ Set.Ioo 0 a) (z : ℝ) : HasDerivAt (fun w => F w z) (D w z) w := by
    have hS := (hasDerivAt_stepD1_split_field hA hC2 hcA'' hm.1 a x z hw).pow 2
    have hBv := hasDerivAt_parisiStep_split_field hA hC2 hcA'' hm.1 a x z hw
    have hW : HasDerivAt (fun w => tiltWeight m (a - w) (parisiStep m w A) x z)
        (m * splitVarianceVelocity A A' A'' m a x w z * tiltWeight m (a - w) (parisiStep m w A) x z) w := by
      have H := ((hBv.sub_const (parisiStep m a A x)).const_mul m).exp
      have he : (fun t => Real.exp (m * (parisiStep m t A (x + Real.sqrt (a - t) * z) - parisiStep m a A x))) =ᶠ[𝓝 w]
          (fun t => tiltWeight m (a - t) (parisiStep m t A) x z) := by
        filter_upwards [Ioo_mem_nhds hw.1 hw.2] with t ht
        exact (splitBaselineWeight_eq hA hcA.measurable m a x z ⟨ht.1.le, ht.2.le⟩).symm
      apply (H.congr_of_eventuallyEq he.symm).congr_deriv
      rw [splitBaselineWeight_eq hA hcA.measurable m a x z ⟨hw.1.le, hw.2.le⟩]
      dsimp only [splitVarianceVelocity]
      ring
    convert! hS.mul hW using 1
    dsimp only [D, splitBaselineSlopeVelocity, Pi.pow_apply]
    ring
  have hbound (w : ℝ) (hw : w ∈ J) (z : ℝ) :
      ‖D w z‖ ≤ C * ((2 * K + 1 / 2 + 3 * L * |z|) * Real.exp (Real.sqrt a * |z|)) := by
    have hb := baseline_slope_velocity_bound hA hC2 hcA'' hm hlo hhi hw x z
    change |splitBaselineSlopeVelocity A A' A'' m a x w z| ≤ 2 * K + 1 / 2 + 3 * L * |z| at hb
    have hbb : 0 ≤ 2 * K + 1 / 2 + 3 * L * |z| := (abs_nonneg _).trans hb
    have hW := baseline_weight_le hA hC2 hcA'' hm ⟨(hJ' w hw).1.le, (hJ' w hw).2.le⟩ x z
    have hWn := tiltWeight_nonneg (hasLinearGrowth_parisiStep hA hcA.measurable m w)
      (measurable_parisiStep hcA.measurable m w) x z (m := m) (v := a - w)
    dsimp only [D]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWn]
    exact (mul_le_mul hb hW hWn hbb).trans_eq (by dsimp only [C]; ring)
  have hFi : Integrable (F v) (gaussianReal 0 1) := by
    apply tilted_bounded_integrable (hasLinearGrowth_parisiStep hA hcA.measurable m v)
      (measurable_parisiStep hcA.measurable m v) (scalar_C2_lipschitz' (hB v))
      ((measurable_stepD1 hcA.measurable hcA'.measurable m v).pow_const 2) (B := 1) (fun y => ?_) x
    simp only [abs_pow, sq_abs]
    nlinarith [(hB v).abs_first_le_one y, sq_abs (stepD1 A A' m v y), abs_nonneg (stepD1 A A' m v y)]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ
    (Eventually.of_forall fun w => (((hSm w).pow_const 2).mul (hWm w)).aestronglyMeasurable)
    hFi hDm.aestronglyMeasurable (Eventually.of_forall fun z w hw => hbound w hw z)
    ((integrable_poly_mul_exp_abs (2 * K + 1 / 2) (3 * L) (Real.sqrt a)).const_mul C)
    (Eventually.of_forall fun z w hw => hd w (hJ' w hw) z)).2

/-- Talagrand's (4.16): the genuine equal-mass normalized squared-slope
mean has derivative the negative normalized square of B''. All derivatives
and domination are proved for the actual transform, including mass zero. -/
theorem hasDerivAt_splitBaselineSlopeQ {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (splitBaselineSlopeQ A A' m a x)
      (-(∫ z, (stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z)) ^ 2 *
        tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1))) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  let B := parisiStep m v A
  let S := stepD1 A A' m v
  let T := stepD2 A A' A'' m v
  let E := stepD3 A A' A'' m v
  let G := fun y => 2 * S y * T y + m * (S y) ^ 3
  let G' := fun y => 2 * (T y) ^ 2 + 2 * S y * E y + 3 * m * (S y) ^ 2 * T y
  let K := 2 * ((1 + 2 * m) * (Real.exp ((m * Real.sqrt v) * gAbsMoment) *
    gAbsExpMoment (m * Real.sqrt v)) / (2 * Real.sqrt v)) + 2
  let W := tiltWeight m (a - v) B x
  let Y := fun z => x + Real.sqrt (a - v) * z
  have hB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  have hE (y : ℝ) : HasDerivAt T (E y) y := hasDerivAt_stepD2_spatial hA hC2 hcA'' hm hv.1 y
  have hEb (y : ℝ) : |E y| ≤ K := abs_stepD3_le hA hC2 hcA'' hm hv.1 y
  have hKn : 0 ≤ K := (abs_nonneg (E 0)).trans (hEb 0)
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun y => (hB.2.1 y).continuousAt
  have hTc : Continuous T := continuous_iff_continuousAt.mpr fun y => (hE y).continuousAt
  have hEc : Continuous E := continuous_stepD3_spatial hA hC2 hcA'' hm.1 hv.1
  have hGd (y : ℝ) : HasDerivAt G (G' y) y := by
    have H := (((hB.2.1 y).const_mul 2).mul (hE y)).add (((hB.2.1 y).pow 3).const_mul m)
    convert! H using 1
    dsimp only [G']
    ring
  have hGm : Measurable G := ((hSc.const_mul 2).mul hTc |>.add ((hSc.pow 3).const_mul m)).measurable
  have hG'm : Measurable G' :=
    (((hTc.pow 2).const_mul 2).add ((hSc.const_mul 2).mul hEc) |>.add
      (((hSc.pow 2).const_mul (3 * m)).mul hTc)).measurable
  have hSb (y : ℝ) := hB.abs_first_le_one y
  have hTb (y : ℝ) := hB.abs_second_le_one y
  have hS2 (y : ℝ) : |S y| ^ 2 ≤ 1 := by nlinarith [hSb y, abs_nonneg (S y)]
  have hS3 (y : ℝ) : |S y| ^ 3 ≤ 1 := by
    have H := mul_le_mul (hS2 y) (hSb y) (abs_nonneg _) zero_le_one
    nlinarith
  have hGb (y : ℝ) : |G y| ≤ 3 := by
    have hh := abs_add_le (2 * S y * T y) (m * (S y) ^ 3)
    simp only [abs_mul, abs_pow, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    have h1 := mul_le_mul (hSb y) (hTb y) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul_of_nonneg_left (hS3 y) hm.1
    dsimp only [G]
    nlinarith [hm.2]
  have hG'b (y : ℝ) : |G' y| ≤ 5 + 2 * K := by
    have ht2 : (T y) ^ 2 ≤ 1 := by nlinarith [hTb y, sq_abs (T y), abs_nonneg (T y)]
    have h1 := mul_le_mul (hSb y) (hEb y) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hS2 y) (hTb y) (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul_of_nonneg_left h2 hm.1
    have hh := abs_add_le (2 * T y ^ 2 + 2 * S y * E y) (3 * m * S y ^ 2 * T y)
    have hh' := abs_add_le (2 * T y ^ 2) (2 * S y * E y)
    simp only [abs_mul, abs_pow, sq_abs, abs_of_nonneg hm.1,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hh hh'
    dsimp only [G']
    rw [sq_abs] at h2 h3
    nlinarith [hm.2]
  have hBg : HasLinearGrowth B := hasLinearGrowth_parisiStep hA hcA.measurable m v
  have hBm : Measurable B := measurable_parisiStep hcA.measurable m v
  have hLip := scalar_C2_lipschitz' hB
  have hstein := integral_gaussian_mul_tilted_observable hBg hBm hSc.measurable hB.1 (hSb)
    hGd hG'm hGb hG'b m (a - v) x
  let J := fun y => G' y + m * G y * S y
  have hJm : Measurable J := hG'm.add ((hGm.const_mul m).mul hSc.measurable)
  have hJb (y : ℝ) : |J y| ≤ (5 + 2 * K) + 3 := by
    have hp := mul_le_mul (hGb y) (hSb y) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    have hh := abs_add_le (G' y) (m * G y * S y)
    simp only [abs_mul, abs_of_nonneg hm.1] at hh
    have hmhp := mul_le_mul_of_nonneg_left hp hm.1
    dsimp only [J]
    nlinarith [hG'b y, hm.2]
  have hJi := tilted_bounded_integrable hBg hBm hLip hJm hJb (m := m) (v := a - v) x
  have hTi := tilted_bounded_integrable hBg hBm hLip (hTc.measurable.pow_const 2)
    (B := 1) (fun y => by simpa only [abs_pow, sq_abs] using
      (show (T y) ^ 2 ≤ 1 by nlinarith [hTb y, sq_abs (T y), abs_nonneg (T y)]))
    (m := m) (v := a - v) x
  have hxi : Integrable (fun z => z * (G (Y z) * W z)) (gaussianReal 0 1) := by
    have H := integrable_mul_tiltWeight_of_bound (m := m) (v := a - v) zero_le_one hLip hBg hBm x
      (measurable_id.mul (hGm.comp (measurable_tilt_shift (a - v) x))) (a := 0) (b := 3) (by norm_num)
      (fun z => by simpa only [Pi.mul_apply, Function.comp_def, id_eq, abs_mul, zero_add, mul_comm, Y] using
        mul_le_mul_of_nonneg_left (hGb (Y z)) (abs_nonneg z))
    simpa only [Pi.mul_apply, Function.comp_def, id_eq, mul_assoc, Y, W] using H
  apply (hasDerivAt_splitBaselineSlopeQ_before_ibp hA hC2 hcA'' hm a x hv).congr_deriv
  calc
    (∫ z, splitBaselineSlopeVelocity A A' A'' m a x v z * W z ∂(gaussianReal 0 1)) =
        ∫ z, ((J (Y z) * W z) / 2 - (T (Y z)) ^ 2 * W z) -
          (1 / (2 * Real.sqrt (a - v))) * (z * (G (Y z) * W z)) ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [splitBaselineSlopeVelocity, splitVarianceVelocity, J, G', G, Y, S, T, E, stepD3]
      ring
    _ = (∫ z, J (Y z) * W z ∂(gaussianReal 0 1)) / 2 -
        (∫ z, (T (Y z)) ^ 2 * W z ∂(gaussianReal 0 1)) -
          (1 / (2 * Real.sqrt (a - v))) * (∫ z, z * (G (Y z) * W z) ∂(gaussianReal 0 1)) := by
      have hsub : Integrable (fun z => J (Y z) * W z / 2 - (T (Y z)) ^ 2 * W z) (gaussianReal 0 1) := by
        simpa only [Pi.sub_apply, Y, W] using! (hJi.div_const 2).sub hTi
      rw [integral_sub hsub (hxi.const_mul _),
        integral_sub (hJi.div_const 2) hTi, integral_div, integral_const_mul]
    _ = -(∫ z, (T (Y z)) ^ 2 * W z ∂(gaussianReal 0 1)) := by
      change _ - _ - _ * (∫ z, z * (G (x + Real.sqrt (a - v) * z) * tiltWeight m (a - v) B x z) ∂(gaussianReal 0 1)) = _
      rw [hstein]
      dsimp only [J, Y, W]
      field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hv.2)).ne']
      ring

/-- The two-step form of (4.16) on every genuine Parisi-recursion input. -/
theorem hasDerivAt_splitBaselineSlopeQ_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (splitBaselineSlopeQ (parisiF s β j) (parisiFDeriv s β j) m a x)
      (-(∫ z, (stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
        m v (x + Real.sqrt (a - v) * z)) ^ 2 *
        tiltWeight m (a - v) (parisiStep m v (parisiF s β j)) x z ∂(gaussianReal 0 1))) v :=
  hasDerivAt_splitBaselineSlopeQ (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm a x hv

end SpinGlass.Targets
