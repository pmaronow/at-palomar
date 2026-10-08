module

public import Targets.ParisiMassZero
public import Targets.Section4NestedDerivative

@[expose] public section

/-!
# Local bounds for the actual scalar mass derivative

The positive-mass estimates reuse the existing tilted Gaussian first-moment
bound and the step-minus-input estimate. These bounds are uniform in the spatial
field and provide the hypotheses needed by the existing outer recursion rule.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Spatial measurability of the genuine mass derivative, including mass zero. -/
theorem measurable_deriv_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (m v : ℝ) :
    Measurable (fun x => deriv (fun a => parisiStep a v A x) m) := by
  have ha : Measurable (fun p : ℝ × ℝ => A (p.1 + Real.sqrt v * p.2)) :=
    hmeas.comp (by fun_prop)
  have hB := measurable_parisiStep hmeas m v
  by_cases hm : m = 0
  · subst m
    simp_rw [(hasDerivAt_parisiStep_mass_zero hA hmeas v _).deriv]
    have hh := (ha.sub ((measurable_parisiStep hmeas 0 v).comp measurable_fst)).pow_const 2
    exact (hh.stronglyMeasurable.integral_prod_right'.measurable).div_const 2
  · simp_rw [(hasDerivAt_parisiStep_mass hA hmeas hm v _).deriv]
    have hI : Measurable (fun x => ∫ z, A (x + Real.sqrt v * z) *
        tiltWeight m v A x z ∂(gaussianReal 0 1)) := by
      simp only [tiltWeight, if_neg hm, ← mul_div_assoc, integral_div]
      exact ((ha.mul (ha.const_mul m).exp).stronglyMeasurable.integral_prod_right'.measurable).div
        ((ha.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable)
    exact (hI.sub hB).div_const m

private theorem gAbsExpMoment_mono {a b : ℝ} (hab : a ≤ b) :
    gAbsExpMoment a ≤ gAbsExpMoment b := by
  unfold gAbsExpMoment
  exact integral_mono (integrable_abs_mul_exp_abs_stdGaussian a) (integrable_abs_mul_exp_abs_stdGaussian b)
    (fun z => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hab (abs_nonneg z))) (abs_nonneg z))

/-- The centered tilted first moment is controlled independently of the field. -/
theorem abs_tilted_self_sub_le {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|) (m v x : ℝ) :
    |(∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)) - A x| ≤
      Real.sqrt v * (Real.exp ((|m| * Real.sqrt v) * gAbsMoment) *
        gAbsExpMoment (|m| * Real.sqrt v)) := by
  have hL : ∀ y z, |A y - A z| ≤ 1 * |y - z| := by simpa only [one_mul] using hLip
  have hI := integrable_self_mul_tiltWeight_mass hA hmeas m v x
  have hW := integrable_tiltWeight_mass hA hmeas m v x
  have hJ : Integrable (fun z => |z| * tiltWeight m v A x z) (gaussianReal 0 1) :=
    integrable_mul_tiltWeight_of_bound zero_le_one hL hA hmeas x measurable_id.abs
      (a := 0) (b := 1) zero_le_one (fun z => by simp)
  have hcen : (∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)) - A x =
      ∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z - A x * tiltWeight m v A x z
        ∂(gaussianReal 0 1) := by
    rw [integral_sub hI (hW.const_mul _), integral_const_mul,
      tiltWeight_integral_one hA hmeas, mul_one]
  rw [hcen]
  calc
    _ ≤ ∫ z, |A (x + Real.sqrt v * z) * tiltWeight m v A x z - A x * tiltWeight m v A x z|
        ∂(gaussianReal 0 1) := abs_integral_le_integral_abs
    _ ≤ ∫ z, Real.sqrt v * (|z| * tiltWeight m v A x z) ∂(gaussianReal 0 1) := by
      apply integral_mono (hI.sub (hW.const_mul _)).abs (hJ.const_mul _)
      intro z
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (tiltWeight_nonneg hA hmeas x z)]
      have hh := hLip (x + Real.sqrt v * z) x
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (tiltWeight_nonneg (m := m) (v := v) hA hmeas x z)]
    _ ≤ Real.sqrt v * (Real.exp ((|m| * Real.sqrt v) * gAbsMoment) *
        gAbsExpMoment (|m| * Real.sqrt v)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mul_one] using (integral_abs_mul_tiltWeight_le (m := m) (v := v)
          zero_le_one hL hA hmeas x)) (Real.sqrt_nonneg _)

/-- A finite local bound for positive mass derivatives, uniform in the field. -/
theorem abs_deriv_parisiStep_mass_le {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|) {a b m v : ℝ}
    (ha : 0 < a) (hm : m ∈ Set.Icc a b) (hv : 0 < v) (x : ℝ) :
    |deriv (fun u => parisiStep u v A x) m| ≤
      (Real.sqrt v * (Real.exp ((b * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (b * Real.sqrt v)) +
        Real.sqrt v * gAbsMoment + b * v / 2) / a := by
  have hmpos : 0 < m := ha.trans_le hm.1
  have hL : ∀ y z, |A y - A z| ≤ 1 * |y - z| := by simpa only [one_mul] using hLip
  have h1 := abs_tilted_self_sub_le hA hmeas hLip m v x
  have h2 := abs_parisiStep_sub_self_le (L := 1) zero_lt_one hv hmpos.ne' hL hA hmeas x
  simp only [one_mul, one_pow] at h2
  change |parisiStep m v A x - A x| ≤ Real.sqrt v * gAbsMoment + |m| * v / 2 at h2
  rw [abs_of_pos hmpos] at h1 h2
  have he : Real.exp ((m * Real.sqrt v) * gAbsMoment) ≤ Real.exp ((b * Real.sqrt v) * gAbsMoment) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm.2 (Real.sqrt_nonneg _)) gAbsMoment_nonneg)
  have hg := gAbsExpMoment_mono (mul_le_mul_of_nonneg_right hm.2 (Real.sqrt_nonneg v))
  have hprod := mul_le_mul he hg (gAbsExpMoment_nonneg _) (Real.exp_pos _).le
  have hn : |(∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z ∂(gaussianReal 0 1)) -
      parisiStep m v A x| ≤
      Real.sqrt v * (Real.exp ((b * Real.sqrt v) * gAbsMoment) * gAbsExpMoment (b * Real.sqrt v)) +
        Real.sqrt v * gAbsMoment + b * v / 2 := by
    have htri := abs_sub_le (∫ z, A (x + Real.sqrt v * z) * tiltWeight m v A x z
      ∂(gaussianReal 0 1)) (A x) (parisiStep m v A x)
    rw [abs_sub_comm (A x)] at htri
    nlinarith [mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg v),
      mul_le_mul_of_nonneg_right hm.2 hv.le]
  rw [(hasDerivAt_parisiStep_mass hA hmeas hmpos.ne' v x).deriv, abs_div, abs_of_pos hmpos]
  exact div_le_div₀ ((abs_nonneg _).trans hn) hn ha hm.1

/-- Negating the input reflects the mass, including its actual zero branch. -/
theorem parisiStep_neg_input (A : ℝ → ℝ) (m v x : ℝ) :
    parisiStep m v (fun y => -A y) x = -parisiStep (-m) v A x := by
  by_cases hm : m = 0
  · simp [parisiStep, hm, integral_neg]
  · simp only [parisiStep, if_neg hm, if_neg (neg_ne_zero.mpr hm),
      mul_neg, neg_mul, one_div, inv_neg]
    ring

/-- The Herbst estimate gives a two-sided, field-uniform bound around zero
mass; this is the domination needed for the genuine zero-mass derivative. -/
theorem abs_parisiStep_mass_sub_zero_le {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|) {v : ℝ} (hv : 0 ≤ v) (m x : ℝ) :
    |parisiStep m v A x - parisiStep 0 v A x| ≤ |m| * v / 2 := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hAn : HasLinearGrowth (fun y => -A y) := by
      obtain ⟨C, D, hC, hD, hb⟩ := hA
      exact ⟨C, D, hC, hD, fun y => by simpa only [abs_neg] using hb y⟩
    have hLn : ∀ y z, |-A y - -A z| ≤ |y - z| := by
      intro y z
      simpa only [neg_sub_neg, abs_sub_comm] using hLip y z
    have H := parisiStep_zero_sandwich (neg_pos.mpr hm) hv hLn hAn hmeas.neg x
    rw [parisiStep_neg_input A, parisiStep_neg_input A] at H
    simp only [neg_zero, neg_neg] at H
    rw [abs_of_nonpos (sub_nonpos.mpr (by linarith [H.1])), abs_of_neg hm]
    linarith [H.2]
  · simp [hm]
  · have H := parisiStep_zero_sandwich hm hv hLip hA hmeas x
    rw [abs_of_nonneg (sub_nonneg.mpr H.1), abs_of_pos hm]
    linarith [H.2]

/-- Scalar specialization of Mathlib's anchored dominated derivative theorem.
Unlike the neighborhood-Lipschitz version, only a bound relative to the point
being differentiated is required. -/
theorem hasDerivAt_integral_of_anchored_bound {F : ℝ → ℝ → ℝ} {D bound : ℝ → ℝ}
    {μ : Measure ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hmeas : ∀ u ∈ s, AEStronglyMeasurable (F u) μ) (hint : Integrable (F t) μ)
    (hD : AEStronglyMeasurable D μ)
    (hb : ∀ᵐ z ∂μ, ∀ u ∈ s, |F u z - F t z| ≤ bound z * |u - t|)
    (hbi : Integrable bound μ) (hd : ∀ᵐ z ∂μ, HasDerivAt (fun u => F u z) (D z) t) :
    HasDerivAt (fun u => ∫ z, F u z ∂μ) (∫ z, D z ∂μ) t := by
  let L : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hDm : AEStronglyMeasurable (L ∘ D) μ := L.continuous.comp_aestronglyMeasurable hD
  have H := hasFDerivAt_integral_of_dominated_loc_of_lip' hs hmeas hint hDm
    (by simpa only [Real.norm_eq_abs] using hb) hbi
    (hd.mono fun z hz => hz.hasFDerivAt)
  have HH := H.2.hasDerivAt
  rw [ContinuousLinearMap.integral_apply H.1] at HH
  simpa [L, Function.comp_def] using! HH

/-- The actual inner mass derivative at zero may be passed through a Gaussian
expectation. The domination is the proved two-sided Herbst estimate. -/
theorem hasDerivAt_mass_zero_outer_expectation {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|) {v : ℝ} (hv : 0 ≤ v) (w x : ℝ) :
    HasDerivAt (fun m => parisiStep 0 w (parisiStep m v A) x)
      (∫ z, deriv (fun m => parisiStep m v A (x + Real.sqrt w * z)) 0 ∂(gaussianReal 0 1)) 0 := by
  have H := hasDerivAt_integral_of_anchored_bound (s := Set.univ)
    (F := fun m z => parisiStep m v A (x + Real.sqrt w * z))
    (D := fun z => deriv (fun m => parisiStep m v A (x + Real.sqrt w * z)) 0)
    (bound := fun _ => v / 2) Filter.univ_mem
    (fun m _ => ((measurable_parisiStep hmeas m v).comp (by fun_prop)).aestronglyMeasurable)
    (integrable_of_hasLinearGrowth (hasLinearGrowth_parisiStep hA hmeas 0 v)
      (measurable_parisiStep hmeas 0 v) x w)
    (((measurable_deriv_parisiStep_mass hA hmeas 0 v).comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun z m _ => by
      simpa only [sub_zero, mul_div_assoc, mul_comm (v / 2)] using
        abs_parisiStep_mass_sub_zero_le hA hmeas hLip hv m (x + Real.sqrt w * z))
    (integrable_const _) (Eventually.of_forall fun z =>
      (differentiable_parisiStep_mass hA hmeas v (x + Real.sqrt w * z) 0).hasDerivAt)
  simpa only [parisiStep, if_true] using! H

end SpinGlass.Targets
