module

public import Paper.HeatGradient

@[expose] public section

/-! Positive-variance Gaussian smoothing of bounded measurable data is
jointly continuous in its mean and variance. The density, rather than the
observable, is differentiated or varied. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace Paper

theorem gaussianPDFReal_joint_neighborhood_bound (v₀ : ℝ) (hv₀ : 0 < v₀)
    (v : ℝ≥0) (hvlo : v₀ / 2 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ 2 * v₀)
    (x₀ x y : ℝ) (hx : |x - x₀| ≤ 1) :
    gaussianPDFReal x v y ≤
      (Real.sqrt (2 * Real.pi * (v₀ / 2)))⁻¹ * Real.exp (1 / v₀) *
        Real.exp (-(1 / (8 * v₀)) * (y - x₀) ^ 2) := by
  have hv : 0 < (v : ℝ) := lt_of_lt_of_le (by positivity) hvlo
  have hx2 : (x - x₀) ^ 2 ≤ 1 := by nlinarith [sq_abs (x - x₀), abs_nonneg (x - x₀)]
  have hquad : (y - x) ^ 2 ≥ (y - x₀) ^ 2 / 2 - 1 := by
    nlinarith [sq_nonneg ((y - x₀) - 2 * (x - x₀))]
  have hfirst : -(y - x) ^ 2 / (2 * (v : ℝ)) ≤
      -(y - x₀) ^ 2 / (4 * (v : ℝ)) + 1 / (2 * (v : ℝ)) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))).mpr
    field_simp
    nlinarith
  have hconst : 1 / (2 * (v : ℝ)) ≤ 1 / v₀ := by
    apply one_div_le_one_div_of_le hv₀
    linarith
  have hneg : -(y - x₀) ^ 2 / (4 * (v : ℝ)) ≤
      -(y - x₀) ^ 2 / (8 * v₀) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (v : ℝ)) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hvhi (sq_nonneg (y - x₀))]
  have hexp : -(y - x) ^ 2 / (2 * (v : ℝ)) ≤
      1 / v₀ + -(1 / (8 * v₀)) * (y - x₀) ^ 2 := by
    calc
      _ ≤ -(y - x₀) ^ 2 / (4 * (v : ℝ)) + 1 / (2 * (v : ℝ)) := hfirst
      _ ≤ -(y - x₀) ^ 2 / (8 * v₀) + 1 / v₀ := add_le_add hneg hconst
      _ = _ := by ring
  have hpref : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≤
      (Real.sqrt (2 * Real.pi * (v₀ / 2)))⁻¹ := by
    apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvlo (by positivity))
  unfold gaussianPDFReal
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * (v₀ / 2)))⁻¹ *
        Real.exp (1 / v₀ + -(1 / (8 * v₀)) * (y - x₀) ^ 2) :=
      mul_le_mul hpref (Real.exp_le_exp.mpr hexp) (by positivity) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem continuousAt_gaussianPDFReal_parameters (p : ℝ × ℝ) (hv : 0 < p.2) (y : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => gaussianPDFReal q.1 q.2.toNNReal y) p := by
  unfold gaussianPDFReal
  have hp : 0 < (p.2.toNNReal : ℝ) := by simpa [Real.coe_toNNReal _ hv.le] using hv
  fun_prop (disch := positivity)

theorem heatSemigroup_eq_integral_gaussianPDFReal (f : ℝ → ℝ) (hf : Measurable f)
    (x v : ℝ) (hv : 0 < v) :
    heatSemigroup v f x = ∫ y, gaussianPDFReal x v.toNNReal y * f y := by
  unfold heatSemigroup
  rw [gaussianExpectation_shift_eq_integral x v hv.le f hf]
  have hvn : v.toNNReal ≠ 0 := by simpa using hv
  simpa only [smul_eq_mul] using integral_gaussianReal_eq_integral_smul (f := f) hvn

theorem continuousAt_heatSemigroup_of_bounded (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => heatSemigroup q.2 f q.1) p := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let C := (Real.sqrt (2 * Real.pi * (p.2 / 2)))⁻¹ * Real.exp (1 / p.2)
  let bound := fun y => (C * M) * Real.exp (-(1 / (8 * p.2)) * (y - p.1) ^ 2)
  have hi : Integrable bound :=
    ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (8 * p.2))).comp_sub_right p.1).const_mul _
  have hbound : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ∀ᵐ y : ℝ,
      ‖gaussianPDFReal q.1 q.2.toNNReal y * f y‖ ≤ bound y := by
    have heps : 0 < min 1 (p.2 / 2) := by positivity
    filter_upwards [Metric.ball_mem_nhds p heps] with q hq
    have hd : max |q.1 - p.1| |q.2 - p.2| < min 1 (p.2 / 2) := by
      simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using hq
    have hx : |q.1 - p.1| ≤ 1 := ((max_lt_iff.mp hd).1.trans_le (min_le_left _ _)).le
    have hvlo : p.2 / 2 ≤ q.2 := by
      have hh := (max_lt_iff.mp hd).2.trans_le (min_le_right _ _)
      have := neg_le_abs (q.2 - p.2)
      linarith
    have hvhi : q.2 ≤ 2 * p.2 := by
      have hh := (max_lt_iff.mp hd).2.trans_le (min_le_right _ _)
      have := le_abs_self (q.2 - p.2)
      linarith
    filter_upwards with y
    have hbpdf := gaussianPDFReal_joint_neighborhood_bound p.2 hp q.2.toNNReal
      (by simpa [Real.coe_toNNReal _ (by linarith : 0 ≤ q.2)] using hvlo)
      (by simpa [Real.coe_toNNReal _ (by linarith : 0 ≤ q.2)] using hvhi) p.1 q.1 y hx
    rw [norm_mul, Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact (mul_le_mul hbpdf (hb y) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [bound, C]; ring)
  have hc : ContinuousAt (fun q : ℝ × ℝ => ∫ y, gaussianPDFReal q.1 q.2.toNNReal y * f y) p := by
    apply continuousAt_of_dominated
      (.of_forall fun q => ((measurable_gaussianPDFReal _ _).mul hf).aestronglyMeasurable)
      hbound hi
    exact .of_forall (fun y => (continuousAt_gaussianPDFReal_parameters p hp y).mul_const (f y))
  apply hc.congr_of_eventuallyEq
  have hev : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 0 < q.2 :=
    (continuous_snd.continuousAt.eventually (Ioi_mem_nhds hp))
  filter_upwards [hev] with q hq
  exact heatSemigroup_eq_integral_gaussianPDFReal f hf q.1 q.2 hq

theorem heatGradient_eq_integral_gaussianPDFReal (f : ℝ → ℝ) (hf : Measurable f)
    (x v : ℝ) (hv : 0 < v) :
    heatGradient v f x =
      ∫ y, ((y - x) / v * gaussianPDFReal x v.toNNReal y) * f y := by
  have hvn : 0 < (v.toNNReal : ℝ) := by simpa [Real.coe_toNNReal _ hv.le] using hv
  simpa only [Real.coe_toNNReal _ hv.le] using
    (gaussian_spatial_derivative_eq_heatGradient v.toNNReal hvn f hf x).symm

set_option maxHeartbeats 800000 in
theorem continuousAt_heatGradient_of_bounded (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => heatGradient q.2 f q.1) p := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let C := (Real.sqrt (2 * Real.pi * (p.2 / 2)))⁻¹ * Real.exp (1 / p.2)
  let bound := fun y => (C * M * (2 / p.2)) *
    ((|y - p.1| + 1) * Real.exp (-(1 / (8 * p.2)) * (y - p.1) ^ 2))
  have hk : (0 : ℝ) < 1 / (8 * p.2) := by positivity
  have hpoly : Integrable (fun z : ℝ => (|z| + 1) * Real.exp (-(1 / (8 * p.2)) * z ^ 2)) := by
    have hi : Integrable (fun z : ℝ => |z| * Real.exp (-(1 / (8 * p.2)) * z ^ 2)) := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
        (integrable_mul_exp_neg_mul_sq hk).norm
    convert hi.add (integrable_exp_neg_mul_sq hk) using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  have hi : Integrable bound := (hpoly.comp_sub_right p.1).const_mul _
  have hbound : ∀ᶠ q : ℝ × ℝ in 𝓝 p, ∀ᵐ y : ℝ,
      ‖((y - q.1) / q.2 * gaussianPDFReal q.1 q.2.toNNReal y) * f y‖ ≤ bound y := by
    have heps : 0 < min 1 (p.2 / 2) := by positivity
    filter_upwards [Metric.ball_mem_nhds p heps] with q hq
    have hd : max |q.1 - p.1| |q.2 - p.2| < min 1 (p.2 / 2) := by
      simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using hq
    have hx : |q.1 - p.1| ≤ 1 := ((max_lt_iff.mp hd).1.trans_le (min_le_left _ _)).le
    have hvlo : p.2 / 2 ≤ q.2 := by
      have hh := (max_lt_iff.mp hd).2.trans_le (min_le_right _ _)
      have := neg_le_abs (q.2 - p.2)
      linarith
    have hvhi : q.2 ≤ 2 * p.2 := by
      have hh := (max_lt_iff.mp hd).2.trans_le (min_le_right _ _)
      have := le_abs_self (q.2 - p.2)
      linarith
    have hqpos : 0 < q.2 := by linarith
    have hinv : q.2⁻¹ ≤ 2 / p.2 := by
      have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < p.2 / 2) hvlo
      convert hh using 1 <;> field_simp
    filter_upwards with y
    have htri : |y - q.1| ≤ |y - p.1| + 1 := by
      calc
        _ = |(y - p.1) - (q.1 - p.1)| := by congr 1; ring
        _ ≤ |y - p.1| + |q.1 - p.1| := abs_sub _ _
        _ ≤ _ := by linarith
    have hbpdf := gaussianPDFReal_joint_neighborhood_bound p.2 hp q.2.toNNReal
      (by simpa [Real.coe_toNNReal _ hqpos.le] using hvlo)
      (by simpa [Real.coe_toNNReal _ hqpos.le] using hvhi) p.1 q.1 y hx
    have hcoeff : |y - q.1| / q.2 ≤ (|y - p.1| + 1) * (2 / p.2) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul htri hinv (by positivity) (by positivity)
    simp only [norm_mul, Real.norm_eq_abs, abs_div, abs_of_pos hqpos,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact (mul_le_mul (mul_le_mul hcoeff hbpdf (gaussianPDFReal_nonneg _ _ _) (by positivity))
      (hb y) (by positivity) (by positivity)).trans_eq (by dsimp [bound, C]; ring)
  have hc : ContinuousAt (fun q : ℝ × ℝ =>
      ∫ y, ((y - q.1) / q.2 * gaussianPDFReal q.1 q.2.toNNReal y) * f y) p := by
    apply continuousAt_of_dominated (μ := volume)
      (F := fun (q : ℝ × ℝ) (y : ℝ) =>
        ((y - q.1) / q.2 * gaussianPDFReal q.1 q.2.toNNReal y) * f y)
      (bound := bound)
    · exact .of_forall (fun q => (((measurable_id.sub measurable_const).div_const q.2).mul
        (measurable_gaussianPDFReal q.1 q.2.toNNReal)).mul hf |>.aestronglyMeasurable)
    · exact hbound
    · exact hi
    · exact .of_forall (fun y =>
      ((show ContinuousAt (fun q : ℝ × ℝ => (y - q.1) / q.2) p by
        fun_prop (disch := positivity)).mul
          (continuousAt_gaussianPDFReal_parameters p hp y)).mul_const (f y))
  apply hc.congr_of_eventuallyEq
  have hev : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 0 < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hp)
  filter_upwards [hev] with q hq
  exact heatGradient_eq_integral_gaussianPDFReal f hf q.1 q.2 hq

end Paper
