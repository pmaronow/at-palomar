module

public import Targets.ParisiStepSemigroup
public import Targets.CascadeDeriv
public import ParisiFormula.GaussianStein

@[expose] public section

/-!
# Variance differentiation of the actual scalar Parisi step

The heat-generator calculation needed for Talagrand's (4.4). We reuse scalar
Gaussian Stein and the existing spatial derivative formulas. Differentiation
under Gaussian integrals is justified by exponential-growth domination.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem exp_growth_affine_bound {f : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hb : ∀ y, |f y| ≤ C * Real.exp (c * |y|))
    (x z a M : ℝ) (ha : |a| ≤ M) :
    |f (x + a * z)| ≤ C * Real.exp (c * |x|) * Real.exp ((c * M) * |z|) := by
  calc
    |f (x + a * z)| ≤ C * Real.exp (c * |x + a * z|) := hb _
    _ ≤ C * Real.exp (c * (|x| + M * |z|)) := by
      gcongr
      exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
    _ = C * Real.exp (c * |x|) * Real.exp ((c * M) * |z|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem integrable_exp_growth_affine {f : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ C * Real.exp (c * |y|)) (x a : ℝ) :
    Integrable (fun z => f (x + a * z)) (gaussianReal 0 1) := by
  refine ((integrable_exp_abs_mul_stdGaussian (c * |a|)).const_mul
    (C * Real.exp (c * |x|))).mono'
      (hf.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  exact exp_growth_affine_bound hC hc hb x z a |a| le_rfl

theorem hasDerivAt_integral_gaussian_amplitude {f f' : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf'm : Measurable f')
    (hfb : ∀ y, |f y| ≤ C * Real.exp (c * |y|))
    (hf'b : ∀ y, |f' y| ≤ C * Real.exp (c * |y|)) (x a : ℝ) :
    HasDerivAt (fun b => ∫ z, f (x + b * z) ∂(gaussianReal 0 1))
      (∫ z, f' (x + a * z) * z ∂(gaussianReal 0 1)) a := by
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt).measurable
  have hbound : Integrable (fun z : ℝ =>
      (C * Real.exp (c * |x|)) * (|z| * Real.exp ((c * (|a| + 1)) * |z|)))
      (gaussianReal 0 1) :=
    (integrable_abs_mul_exp_abs_stdGaussian (c * (|a| + 1))).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b z => f (x + b * z))
    (F' := fun b z => f' (x + b * z) * z)
    (s := Metric.ball a 1) (Metric.ball_mem_nhds a one_pos)
    (bound := fun z => (C * Real.exp (c * |x|)) *
      (|z| * Real.exp ((c * (|a| + 1)) * |z|))) ?_ ?_ ?_ ?_ hbound ?_).2
  · filter_upwards with b
    exact (hfm.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_exp_growth_affine hC hc hfm hfb x a
  · exact ((hf'm.comp (by fun_prop)).mul measurable_id).aestronglyMeasurable
  · filter_upwards with z b hb
    have hba : |b - a| < 1 := by simpa [Real.dist_eq] using hb
    have hb' : |b| ≤ |a| + 1 := by linarith [abs_sub_abs_le_abs_sub b a]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |f' (x + b * z)| * |z| ≤
          (C * Real.exp (c * |x|) * Real.exp ((c * (|a| + 1)) * |z|)) * |z| :=
        mul_le_mul_of_nonneg_right (exp_growth_affine_bound hC hc hf'b x z b (|a| + 1) hb')
          (abs_nonneg z)
      _ = _ := by ring
  · filter_upwards with z b _
    simpa only [Function.comp_apply, mul_one, one_mul, id_eq] using!
      (hf (x + b * z)).comp b (((hasDerivAt_id b).mul_const z).const_add x)

/-- Gaussian heat generator at positive variance, with exponential-growth inputs. -/
theorem hasDerivAt_integral_gaussian_variance {f f' f'' : ℝ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (hf''m : Measurable f'')
    (hfb : ∀ y, |f y| ≤ C * Real.exp (c * |y|))
    (hf'b : ∀ y, |f' y| ≤ C * Real.exp (c * |y|))
    (hf''b : ∀ y, |f'' y| ≤ C * Real.exp (c * |y|))
    (x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => ∫ z, f (x + Real.sqrt w * z) ∂(gaussianReal 0 1))
      ((∫ z, f'' (x + Real.sqrt v * z) ∂(gaussianReal 0 1)) / 2) v := by
  have hf'm : Measurable f' :=
    (continuous_iff_continuousAt.mpr fun y => (hf' y).continuousAt).measurable
  have hd := (hasDerivAt_integral_gaussian_amplitude hC hc hf hf'm hfb hf'b x (Real.sqrt v)).comp v
    (Real.hasDerivAt_sqrt hv.ne')
  have hstein : (∫ z, z * f' (x + Real.sqrt v * z) ∂(gaussianReal 0 1)) =
      ∫ z, Real.sqrt v * f'' (x + Real.sqrt v * z) ∂(gaussianReal 0 1) := by
    let K := (1 + Real.sqrt v) * C * Real.exp (c * |x|)
    refine gaussianReal_stein_of_bound _ _ ?_
      (((hf''m.comp (by fun_prop)).const_mul (Real.sqrt v))) (C := K) (c := c * Real.sqrt v) ?_ ?_
    · intro z
      simpa only [Function.comp_def, mul_one, one_mul, id_eq, mul_comm] using!
        (hf' _).comp z (((hasDerivAt_id z).const_mul (Real.sqrt v)).const_add x)
    · intro z
      have hb := exp_growth_affine_bound hC hc hf'b x z (Real.sqrt v) (Real.sqrt v)
        (by rw [abs_of_nonneg (Real.sqrt_nonneg v)])
      refine hb.trans ?_
      dsimp [K]
      gcongr
      nlinarith [Real.sqrt_nonneg v, hC]
    · intro z
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)]
      have hb := exp_growth_affine_bound hC hc hf''b x z (Real.sqrt v) (Real.sqrt v)
        (by rw [abs_of_nonneg (Real.sqrt_nonneg v)])
      calc
        Real.sqrt v * |f'' (x + Real.sqrt v * z)| ≤ Real.sqrt v *
            (C * Real.exp (c * |x|) * Real.exp ((c * Real.sqrt v) * |z|)) :=
          mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg v)
        _ ≤ K * Real.exp ((c * Real.sqrt v) * |z|) := by
          dsimp [K]
          nlinarith [mul_nonneg hC (Real.exp_pos (c * |x|)).le,
            Real.exp_pos ((c * Real.sqrt v) * |z|)]
  apply hd.congr_deriv
  rw [show (∫ z, f' (x + Real.sqrt v * z) * z ∂(gaussianReal 0 1)) =
      ∫ z, z * f' (x + Real.sqrt v * z) ∂(gaussianReal 0 1) by simp only [mul_comm],
    hstein, integral_const_mul]
  field_simp

private theorem parisi_exponential_heat_bounds {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hb' : ∀ y, |A' y| ≤ 1) (hb'' : ∀ y, |A'' y| ≤ 1) (m : ℝ) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 ≤ c ∧
      (∀ y, |Real.exp (m * A y)| ≤ K * Real.exp (c * |y|)) ∧
      (∀ y, |m * A' y * Real.exp (m * A y)| ≤ K * Real.exp (c * |y|)) ∧
      (∀ y, |(m * A'' y + m ^ 2 * (A' y) ^ 2) * Real.exp (m * A y)| ≤
        K * Real.exp (c * |y|)) := by
  obtain ⟨C, D, hC, hD, hb⟩ := hA
  let K := (1 + |m| + m ^ 2) * Real.exp (|m| * C)
  let c := |m| * D
  have he (y : ℝ) : Real.exp (m * A y) ≤
      Real.exp (|m| * C) * Real.exp (c * |y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := le_abs_self (m * A y)
    rw [abs_mul] at h
    have h' := mul_le_mul_of_nonneg_left (hb y) (abs_nonneg m)
    dsimp [c]
    nlinarith
  have hbcoef (y b : ℝ) (hbb : |b| ≤ 1 + |m| + m ^ 2) :
      |b * Real.exp (m * A y)| ≤ K * Real.exp (c * |y|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |b| * Real.exp (m * A y) ≤
          (1 + |m| + m ^ 2) * (Real.exp (|m| * C) * Real.exp (c * |y|)) :=
        mul_le_mul hbb (he y) (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [K]; ring
  refine ⟨K, c, by dsimp [K]; positivity, by dsimp [c]; positivity, ?_, ?_, ?_⟩
  · intro y
    simpa only [one_mul] using hbcoef y 1
      (by rw [abs_one]; nlinarith [abs_nonneg m, sq_nonneg m])
  · intro y
    apply hbcoef
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (hb' y) (abs_nonneg m)
    nlinarith [sq_nonneg m]
  · intro y
    apply hbcoef
    have hsq : (A' y) ^ 2 ≤ 1 := by nlinarith [sq_abs (A' y), hb' y, abs_nonneg (A' y)]
    have h1 := mul_le_mul_of_nonneg_left (hb'' y) (abs_nonneg m)
    have h2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg m)
    have hh := abs_add_le (m * A'' y) (m ^ 2 * (A' y) ^ 2)
    rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg m) (sq_nonneg (A' y)))] at hh
    nlinarith

/-- The actual scalar Parisi heat equation, written with its existing spatial derivatives.
The mass may be zero; only the differentiated variance is required to be positive. -/
theorem hasDerivAt_parisiStep_variance {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hmeas : Measurable A) (hmeas' : Measurable A') (hmeas'' : Measurable A'')
    (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => parisiStep m w A x)
      ((stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2) / 2) v := by
  have hb' := hC2.abs_first_le_one
  have hb'' := hC2.abs_second_le_one
  by_cases hm : m = 0
  · subst m
    obtain ⟨C, D, hC, hD, hb⟩ := hA
    have hexp (y : ℝ) : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
    have hlin (y : ℝ) : |A y| ≤ (C + D + 1) * Real.exp |y| := by
      have hh := Real.add_one_le_exp |y|
      calc
        |A y| ≤ C + D * |y| := hb y
        _ ≤ C * Real.exp |y| + D * Real.exp |y| := by
          have h1 := mul_le_mul_of_nonneg_left (hexp y) hC
          have h2 := mul_le_mul_of_nonneg_left (show |y| ≤ Real.exp |y| by linarith) hD
          nlinarith
        _ ≤ (C + D + 1) * Real.exp |y| := by nlinarith [Real.exp_pos |y|]
    have hb1 (y : ℝ) : 1 ≤ (C + D + 1) * Real.exp |y| := by
      nlinarith [hexp y, Real.exp_pos |y|]
    have hd := hasDerivAt_integral_gaussian_variance (show 0 ≤ C + D + 1 by positivity)
      zero_le_one hC2.1 hC2.2.1 hmeas''
      (by simpa only [one_mul] using hlin)
      (fun y => by simpa only [one_mul] using (hb' y).trans (hb1 y))
      (fun y => by simpa only [one_mul] using (hb'' y).trans (hb1 y)) x hv
    simpa [parisiStep, stepD2, tiltQ, tiltE] using! hd
  · obtain ⟨K, c, hK, hc, hf, hf', hf''⟩ := parisi_exponential_heat_bounds hA hb' hb'' m
    have hd (y : ℝ) : HasDerivAt (fun y => Real.exp (m * A y))
        (m * A' y * Real.exp (m * A y)) y := by
      apply ((hC2.1 y).const_mul m).exp.congr_deriv
      ring
    have hd' (y : ℝ) : HasDerivAt (fun y => m * A' y * Real.exp (m * A y))
        ((m * A'' y + m ^ 2 * (A' y) ^ 2) * Real.exp (m * A y)) y := by
      apply (((hC2.2.1 y).const_mul m).mul (hd y)).congr_deriv
      ring
    have hfm : Measurable (fun y => (m * A'' y + m ^ 2 * (A' y) ^ 2) * Real.exp (m * A y)) :=
      ((hmeas''.const_mul m).add ((hmeas'.pow_const 2).const_mul (m ^ 2))).mul
        ((hmeas.const_mul m).exp)
    have hheat := hasDerivAt_integral_gaussian_variance hK hc hd hd' hfm hf hf' hf'' x hv
    have hpos := smoothing_integral_pos hA hmeas (m := m) (v := v) x
    have hfin := (hheat.log hpos.ne').const_mul (1 / m)
    have heq : (fun w => parisiStep m w A x) = fun w =>
        (1 / m) * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1)) := by
      funext w
      rw [parisiStep, if_neg hm]
    rw [heq]
    apply hfin.congr_deriv
    rw [integral_second_expand hb' hb'' hA hmeas hmeas' hmeas'' x]
    simp only [stepD2, stepD1, tiltE]
    field_simp [hm, hpos.ne']
    ring

end SpinGlass.Targets
