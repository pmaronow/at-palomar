module

public import Targets.ParisiHessianVariance
public import Targets.Section4SquaredSlopeDerivative

@[expose] public section

/-!
# The scalar Hessian-square flow

The actual equal-mass split observable is differentiated before applying
Gaussian Stein. Uniform bounds on the actual third and fourth spatial
derivatives and the actual Hessian variance derivative yield a bound without
an inverse split variance. These input bounds are explicit, not conclusions.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem flow_C2_lipschitz {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (x y : ℝ) : |A x - A y| ≤ 1 * |x - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := A') (s := Set.univ) (C := 1)
    (fun z _ => (hC2.1 z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

private theorem flow_tilted_integrable {F G : ℝ → ℝ} {B m v : ℝ}
    (hF : HasLinearGrowth F) (hFm : Measurable F)
    (hLip : ∀ x y, |F x - F y| ≤ 1 * |x - y|)
    (hGm : Measurable G) (hG : ∀ x, |G x| ≤ B) (x : ℝ) :
    Integrable (fun z => G (x + Real.sqrt v * z) * tiltWeight m v F x z)
      (gaussianReal 0 1) :=
  integrable_mul_tiltWeight_of_bound zero_le_one hLip hF hFm x
    (hGm.comp (measurable_tilt_shift v x)) (b := 0) le_rfl (a := B)
    (by simpa using fun z => hG (x + Real.sqrt v * z))

/-- The actual scalar Hessian-square observable before unchanged outer levels. -/
noncomputable def splitBaselineHessianSquare (A A' A'' : ℝ → ℝ) (m a x v : ℝ) : ℝ :=
  ∫ z, (stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z)) ^ 2 *
    tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)

/-- The derivative integrand before Gaussian Stein. -/
noncomputable def splitBaselineHessianVelocity (A A' A'' A''' : ℝ → ℝ)
    (m a x v z : ℝ) : ℝ :=
  let y := x + Real.sqrt (a - v) * z
  2 * stepD2 A A' A'' m v y *
      (stepD2Variance A A' A'' A''' m v y -
        z / (2 * Real.sqrt (a - v)) * stepD3 A A' A'' m v y) +
    m * (stepD2 A A' A'' m v y) ^ 2 * splitVarianceVelocity A A' A'' m a x v z

private theorem flow_weight_le {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (x z : ℝ) :
    tiltWeight m (a - v) (parisiStep m v A) x z ≤
      Real.exp (Real.sqrt a * gAbsMoment) * Real.exp (Real.sqrt a * |z|) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hcA''.measurable
  have H := tiltWeight_le (m := m) (v := a - v) zero_le_one (flow_C2_lipschitz hB)
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

private theorem flow_velocity_bound {A A' A'' A''' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {a lo hi w K2 K3 : ℝ}
    (hlo : 0 < lo) (hhi : hi < a) (hw : w ∈ Set.Icc lo hi)
    (hJ2 : ∀ y, |stepD2Variance A A' A'' A''' m w y| ≤ K2)
    (hE : ∀ y, |stepD3 A A' A'' m w y| ≤ K3) (x z : ℝ) :
    |splitBaselineHessianVelocity A A' A'' A''' m a x w z| ≤
      2 * K2 + 1 / 2 + (2 * K3 + 1) * (1 / (2 * Real.sqrt (a - hi))) * |z| := by
  let y := x + Real.sqrt (a - w) * z
  let L := 1 / (2 * Real.sqrt (a - hi))
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hcA''.measurable
  have hv : w ∈ Set.Ioo 0 a := ⟨hlo.trans_le hw.1, hw.2.trans_lt hhi⟩
  have hLn : 0 ≤ L := by dsimp [L]; positivity
  have hc : |z / (2 * Real.sqrt (a - w))| ≤ L * |z| := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (sub_pos.mpr hv.2)))]
    have h : 1 / (2 * Real.sqrt (a - w)) ≤ L :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) (Real.sqrt_pos.mpr (sub_pos.mpr hhi)))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hw.2])) (by norm_num))
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_left h (abs_nonneg z)
  have hS := hB.abs_first_le_one y
  have hT := hB.abs_second_le_one y
  have hT2 : (stepD2 A A' A'' m w y) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (stepD2 A A' A'' m w y), abs_nonneg (stepD2 A A' A'' m w y)]
  have hTV : |stepD2Variance A A' A'' A''' m w y -
      z / (2 * Real.sqrt (a - w)) * stepD3 A A' A'' m w y| ≤ K2 + L * |z| * K3 := by
    have hh := abs_sub (stepD2Variance A A' A'' A''' m w y)
      (z / (2 * Real.sqrt (a - w)) * stepD3 A A' A'' m w y)
    rw [abs_mul] at hh
    nlinarith [hJ2 y, mul_le_mul hc (hE y) (abs_nonneg _) (mul_nonneg hLn (abs_nonneg z))]
  have hHV : (stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2 ∈ Set.Icc 0 (1 / 2) := by
    have H := deriv_parisiStep_variance_mem_Icc hA hC2 hcA.measurable hcA'.measurable hcA''.measurable hm y hv.1
    rwa [(hasDerivAt_parisiStep_variance hA hC2 hcA.measurable hcA'.measurable hcA''.measurable m y hv.1).deriv] at H
  have hBV : |splitVarianceVelocity A A' A'' m a x w z| ≤ 1 / 2 + L * |z| := by
    have hh := abs_sub ((stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2)
      (z / (2 * Real.sqrt (a - w)) * stepD1 A A' m w y)
    rw [abs_of_nonneg hHV.1, abs_mul] at hh
    change |_ - _| ≤ _
    nlinarith [mul_le_mul hc hS (abs_nonneg _) (mul_nonneg hLn (abs_nonneg z)), hHV.2]
  have h1 := mul_le_mul hT hTV (abs_nonneg _) zero_le_one
  have h2 := mul_le_mul hT2 hBV (abs_nonneg _) zero_le_one
  have h3 := mul_le_mul_of_nonneg_left h2 hm.1
  have h4 := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 1 / 2 + L * |z|)
  have hh := abs_add_le
    (2 * stepD2 A A' A'' m w y * (stepD2Variance A A' A'' A''' m w y -
      z / (2 * Real.sqrt (a - w)) * stepD3 A A' A'' m w y))
    (m * (stepD2 A A' A'' m w y) ^ 2 * splitVarianceVelocity A A' A'' m a x w z)
  simp only [abs_mul, abs_of_nonneg hm.1, abs_pow, sq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  change |_ + _| ≤ _
  change _ ≤ 2 * K2 + 1 / 2 + (2 * K3 + 1) * L * |z|
  nlinarith

/-- Differentiation of the actual squared-Hessian integral. Domination is
derived locally from uniform bounds on the actual variance and spatial rules. -/
theorem hasDerivAt_splitBaselineHessianSquare_before_ibp {A A' A'' A''' : ℝ → ℝ}
    {K K2 K3 : ℝ} (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA3d : ∀ y, HasDerivAt A'' (A''' y) y) (hcA3 : Continuous A''')
    (hA3b : ∀ y, |A''' y| ≤ K) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (a x : ℝ)
    (hJ2 : ∀ w ∈ Set.Ioo 0 a, ∀ y, |stepD2Variance A A' A'' A''' m w y| ≤ K2)
    (hE : ∀ w ∈ Set.Ioo 0 a, ∀ y, |stepD3 A A' A'' m w y| ≤ K3)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (splitBaselineHessianSquare A A' A'' m a x)
      (∫ z, splitBaselineHessianVelocity A A' A'' A''' m a x v z *
        tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hcA'' : Continuous A'' := continuous_iff_continuousAt.mpr fun y => (hA3d y).continuousAt
  have hB (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hcA''.measurable
  let lo := v / 2
  let hi := (a + v) / 2
  let J := Set.Icc lo hi
  let L := 1 / (2 * Real.sqrt (a - hi))
  let C := Real.exp (Real.sqrt a * gAbsMoment)
  have hlo : 0 < lo := div_pos hv.1 (by norm_num)
  have hhi : hi < a := by dsimp [hi]; linarith [hv.2]
  have hJ : J ∈ 𝓝 v := Icc_mem_nhds (by dsimp [lo]; linarith [hv.1]) (by dsimp [hi]; linarith [hv.2])
  have hJ' (w : ℝ) (hw : w ∈ J) : w ∈ Set.Ioo 0 a := ⟨hlo.trans_le hw.1, hw.2.trans_lt hhi⟩
  let F := fun w z => (stepD2 A A' A'' m w (x + Real.sqrt (a - w) * z)) ^ 2 *
    tiltWeight m (a - w) (parisiStep m w A) x z
  let D := fun w z => splitBaselineHessianVelocity A A' A'' A''' m a x w z *
    tiltWeight m (a - w) (parisiStep m w A) x z
  have hWm (w : ℝ) := measurable_tiltWeight (measurable_parisiStep hcA.measurable m w) x (m := m) (v := a - w)
  have hSm (w : ℝ) := (measurable_stepD1 hcA.measurable hcA'.measurable m w).comp (measurable_tilt_shift (a - w) x)
  have hTm (w : ℝ) := (measurable_stepD2 hcA.measurable hcA'.measurable hcA''.measurable m w).comp
    (measurable_tilt_shift (a - w) x)
  have hDm : Measurable (D v) := by
    have hcV := (continuousOn_stepD2Variance hA hC2 hA3d hcA3 hA3b m).comp_continuous
      (by fun_prop : Continuous (fun z : ℝ => (v, x + Real.sqrt (a - v) * z)))
      (fun _ => ⟨hv.1, Set.mem_univ _⟩)
    have hEm := (continuous_stepD3_spatial hA hC2 hcA'' hm.1 hv.1).measurable.comp
      (measurable_tilt_shift (a - v) x)
    dsimp only [D, splitBaselineHessianVelocity, splitVarianceVelocity]
    exact (((hTm v).const_mul 2).mul (hcV.measurable.sub ((measurable_id.div_const _).mul hEm)) |>.add
      (((hTm v).pow_const 2).const_mul m |>.mul (((hTm v).add (((hSm v).pow_const 2).const_mul m)).div_const 2 |>.sub
        ((measurable_id.div_const _).mul (hSm v))))).mul (hWm v)
  have hd (w : ℝ) (hw : w ∈ Set.Ioo 0 a) (z : ℝ) : HasDerivAt (fun w => F w z) (D w z) w := by
    have hX := (((Real.hasDerivAt_sqrt (sub_pos.mpr hw.2).ne').comp w
      ((hasDerivAt_id w).const_sub a)).mul_const z).const_add x
    have hT := (hasDerivAt_stepD2_variance_curve hA hC2 hA3d hcA3 hA3b hm
      (hasDerivAt_id w) hX hw.1).pow 2
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
    convert! hT.mul hW using 1
    dsimp only [D, splitBaselineHessianVelocity, Pi.pow_apply, id_eq, Function.comp_def]
    ring
  have hbound (w : ℝ) (hw : w ∈ J) (z : ℝ) :
      ‖D w z‖ ≤ C * ((2 * K2 + 1 / 2 + ((2 * K3 + 1) * L) * |z|) * Real.exp (Real.sqrt a * |z|)) := by
    have hb := flow_velocity_bound hA hC2 hcA'' hm hlo hhi hw (hJ2 w (hJ' w hw)) (hE w (hJ' w hw)) x z
    change |splitBaselineHessianVelocity A A' A'' A''' m a x w z| ≤ 2 * K2 + 1 / 2 + (2 * K3 + 1) * L * |z| at hb
    have hbb : 0 ≤ 2 * K2 + 1 / 2 + (2 * K3 + 1) * L * |z| := (abs_nonneg _).trans hb
    have hW := flow_weight_le hA hC2 hcA'' hm ⟨(hJ' w hw).1.le, (hJ' w hw).2.le⟩ x z
    have hWn := tiltWeight_nonneg (hasLinearGrowth_parisiStep hA hcA.measurable m w)
      (measurable_parisiStep hcA.measurable m w) x z (m := m) (v := a - w)
    dsimp only [D]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWn]
    exact (mul_le_mul hb hW hWn hbb).trans_eq (by dsimp only [C]; ring)
  have hFi : Integrable (F v) (gaussianReal 0 1) := by
    apply flow_tilted_integrable (hasLinearGrowth_parisiStep hA hcA.measurable m v)
      (measurable_parisiStep hcA.measurable m v) (flow_C2_lipschitz (hB v))
      ((measurable_stepD2 hcA.measurable hcA'.measurable hcA''.measurable m v).pow_const 2)
      (B := 1) (fun y => ?_) x
    simp only [abs_pow, sq_abs]
    nlinarith [(hB v).abs_second_le_one y, sq_abs (stepD2 A A' A'' m v y), abs_nonneg (stepD2 A A' A'' m v y)]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ
    (Eventually.of_forall fun w => (((hTm w).pow_const 2).mul (hWm w)).aestronglyMeasurable)
    hFi hDm.aestronglyMeasurable (Eventually.of_forall fun z w hw => hbound w hw z)
    ((integrable_poly_mul_exp_abs (2 * K2 + 1 / 2) ((2 * K3 + 1) * L) (Real.sqrt a)).const_mul C)
    (Eventually.of_forall fun z w hw => hd w (hJ' w hw) z)).2

/-- The explicit, measurable scalar variance derivative used by outer transport. -/
noncomputable def splitBaselineHessianDerivative (A A' A'' A''' : ℝ → ℝ)
    (m a x v : ℝ) : ℝ :=
  ∫ z, splitBaselineHessianVelocity A A' A'' A''' m a x v z *
    tiltWeight m (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)

/-- Field measurability of the actual derivative coefficient. -/
theorem measurable_splitBaselineHessianDerivative {A A' A'' A''' : ℝ → ℝ}
    {K : ℝ} (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA3d : ∀ y, HasDerivAt A'' (A''' y) y) (hcA3 : Continuous A''')
    (hA3b : ∀ y, |A''' y| ≤ K) {m a v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Ioo 0 a) :
    Measurable (fun x => splitBaselineHessianDerivative A A' A'' A''' m a x v) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hcA'' : Continuous A'' := continuous_iff_continuousAt.mpr fun y => (hA3d y).continuousAt
  have hS : Measurable (fun p : ℝ × ℝ => stepD1 A A' m v (p.1 + Real.sqrt (a - v) * p.2)) :=
    (measurable_stepD1 hcA.measurable hcA'.measurable m v).comp (by fun_prop)
  have hT : Measurable (fun p : ℝ × ℝ => stepD2 A A' A'' m v (p.1 + Real.sqrt (a - v) * p.2)) :=
    (measurable_stepD2 hcA.measurable hcA'.measurable hcA''.measurable m v).comp (by fun_prop)
  have hE : Measurable (fun p : ℝ × ℝ => stepD3 A A' A'' m v (p.1 + Real.sqrt (a - v) * p.2)) :=
    (continuous_stepD3_spatial hA hC2 hcA'' hm.1 hv.1).measurable.comp (by fun_prop)
  have hJ := ((continuousOn_stepD2Variance hA hC2 hA3d hcA3 hA3b m).comp_continuous
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (v, p.1 + Real.sqrt (a - v) * p.2)))
    (fun _ => ⟨hv.1, Set.mem_univ _⟩)).measurable
  have hW : Measurable (fun p : ℝ × ℝ => tiltWeight m (a - v) (parisiStep m v A) p.1 p.2) := by
    simp_rw [splitBaselineWeight_eq hA hcA.measurable m a _ _ ⟨hv.1.le, hv.2.le⟩]
    exact ((((measurable_parisiStep hcA.measurable m v).comp (by fun_prop)).sub
      ((measurable_parisiStep hcA.measurable m a).comp measurable_fst)).const_mul m).exp
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  dsimp only [splitBaselineHessianVelocity, splitVarianceVelocity]
  exact (((hT.const_mul 2).mul (hJ.sub ((measurable_snd.div_const _).mul hE))).add
    (((hT.pow_const 2).const_mul m).mul (((hT.add ((hS.pow_const 2).const_mul m)).div_const 2).sub
      ((measurable_snd.div_const _).mul hS)))).mul hW

/-- Gaussian Stein eliminates the inverse outer split variance. The bound
is independent of field, total variance and recursion depth once the explicit
actual derivative bounds are uniform. Mass zero is included. -/
theorem abs_splitBaselineHessianDerivative_le {A A' A'' A''' D4 : ℝ → ℝ}
    {K K2 K3 K4 : ℝ} (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA3d : ∀ y, HasDerivAt A'' (A''' y) y) (hcA3 : Continuous A''')
    (hA3b : ∀ y, |A''' y| ≤ K) {m a v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Ioo 0 a)
    (hJ2 : ∀ y, |stepD2Variance A A' A'' A''' m v y| ≤ K2)
    (hEb : ∀ y, |stepD3 A A' A'' m v y| ≤ K3)
    (hD4 : ∀ y, HasDerivAt (stepD3 A A' A'' m v) (D4 y) y)
    (hD4m : Measurable D4) (hD4b : ∀ y, |D4 y| ≤ K4) (x : ℝ) :
    |splitBaselineHessianDerivative A A' A'' A''' m a x v| ≤
      2 * K2 + K3 ^ 2 + K4 + 2 * K3 + 2 := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hcA'' : Continuous A'' := continuous_iff_continuousAt.mpr fun y => (hA3d y).continuousAt
  let B := parisiStep m v A
  let S := stepD1 A A' m v
  let T := stepD2 A A' A'' m v
  let E := stepD3 A A' A'' m v
  let J2 := stepD2Variance A A' A'' A''' m v
  let H := fun y => (T y + m * S y ^ 2) / 2
  let P := fun y => 2 * T y * J2 y + m * T y ^ 2 * H y
  let G := fun y => 2 * T y * E y + m * T y ^ 2 * S y
  let G' := fun y => 2 * E y ^ 2 + 2 * T y * D4 y + m * (2 * T y * E y * S y + T y ^ 3)
  let J := fun y => G' y + m * G y * S y
  let W := tiltWeight m (a - v) B x
  let Y := fun z => x + Real.sqrt (a - v) * z
  have hB := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA
    hcA.measurable hcA'.measurable hcA''.measurable
  have hTd (y : ℝ) : HasDerivAt T (E y) y := hasDerivAt_stepD2_spatial hA hC2 hcA'' hm hv.1 y
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun y => (hB.2.1 y).continuousAt
  have hTc : Continuous T := continuous_iff_continuousAt.mpr fun y => (hTd y).continuousAt
  have hEc : Continuous E := continuous_stepD3_spatial hA hC2 hcA'' hm.1 hv.1
  have hJ2m : Measurable J2 := ((continuousOn_stepD2Variance hA hC2 hA3d hcA3 hA3b m).comp_continuous
    (by fun_prop : Continuous (fun y : ℝ => (v, y))) (fun _ => ⟨hv.1, Set.mem_univ _⟩)).measurable
  have hSb (y : ℝ) := hB.abs_first_le_one y
  have hTb (y : ℝ) := hB.abs_second_le_one y
  have hK2 : 0 ≤ K2 := (abs_nonneg _).trans (hJ2 0)
  have hK3 : 0 ≤ K3 := (abs_nonneg _).trans (hEb 0)
  have hK4 : 0 ≤ K4 := (abs_nonneg _).trans (hD4b 0)
  have hT2 (y : ℝ) : |T y| ^ 2 ≤ 1 := by nlinarith [hTb y, abs_nonneg (T y)]
  have hT3 (y : ℝ) : |T y| ^ 3 ≤ 1 := by
    have hh := mul_le_mul (hT2 y) (hTb y) (abs_nonneg _) zero_le_one
    nlinarith
  have hHb (y : ℝ) : |H y| ≤ 1 / 2 := by
    have hh := deriv_parisiStep_variance_mem_Icc hA hC2 hcA.measurable hcA'.measurable hcA''.measurable hm y hv.1
    rw [(hasDerivAt_parisiStep_variance hA hC2 hcA.measurable hcA'.measurable hcA''.measurable m y hv.1).deriv] at hh
    exact (abs_of_nonneg hh.1).trans_le hh.2
  have hPm : Measurable P := ((hTc.measurable.const_mul 2).mul hJ2m).add
    (((hTc.measurable.pow_const 2).const_mul m).mul
      ((hTc.measurable.add ((hSc.measurable.pow_const 2).const_mul m)).div_const 2))
  have hPb (y : ℝ) : |P y| ≤ 2 * K2 + 1 / 2 := by
    have h1 := mul_le_mul (hTb y) (hJ2 y) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hT2 y) (hHb y) (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul_of_nonneg_left h2 hm.1
    have hh := abs_add_le (2 * T y * J2 y) (m * T y ^ 2 * H y)
    simp only [abs_mul, abs_pow, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    change |_ + _| ≤ _
    nlinarith [hm.2]
  have hGd (y : ℝ) : HasDerivAt G (G' y) y := by
    have hh := (((hTd y).const_mul 2).mul (hD4 y)).add
      ((((hTd y).pow 2).const_mul m).mul (hB.2.1 y))
    convert! hh using 1
    dsimp only [G', E, S, T, Pi.pow_apply]
    ring
  have hGm : Measurable G := ((hTc.measurable.const_mul 2).mul hEc.measurable).add
    (((hTc.measurable.pow_const 2).const_mul m).mul hSc.measurable)
  have hG'm : Measurable G' := ((hEc.measurable.pow_const 2).const_mul 2).add
    ((hTc.measurable.const_mul 2).mul hD4m) |>.add
      ((((hTc.measurable.const_mul 2).mul hEc.measurable).mul hSc.measurable).add
        (hTc.measurable.pow_const 3) |>.const_mul m)
  have hGb (y : ℝ) : |G y| ≤ 2 * K3 + 1 := by
    have h1 := mul_le_mul (hTb y) (hEb y) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hT2 y) (hSb y) (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul_of_nonneg_left h2 hm.1
    have hh := abs_add_le (2 * T y * E y) (m * T y ^ 2 * S y)
    simp only [abs_mul, abs_pow, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    change |_ + _| ≤ _
    nlinarith [hm.2]
  have hG'b (y : ℝ) : |G' y| ≤ 2 * K3 ^ 2 + 2 * K4 + 2 * K3 + 1 := by
    have hE2 : E y ^ 2 ≤ K3 ^ 2 := by nlinarith [hEb y, sq_abs (E y), abs_nonneg (E y)]
    have h1 := mul_le_mul (hTb y) (hD4b y) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hTb y) (hEb y) (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul h2 (hSb y) (abs_nonneg _) (by simpa only [one_mul] using hK3)
    have h4 := mul_le_mul_of_nonneg_left (show 2 * |T y| * |E y| * |S y| + |T y| ^ 3 ≤ 2 * K3 + 1 by
      nlinarith [hT3 y]) hm.1
    have h5 := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 2 * K3 + 1)
    have hh := abs_add_le (2 * E y ^ 2 + 2 * T y * D4 y) (m * (2 * T y * E y * S y + T y ^ 3))
    have hh1 := abs_add_le (2 * E y ^ 2) (2 * T y * D4 y)
    have hh2 := abs_add_le (2 * T y * E y * S y) (T y ^ 3)
    simp only [abs_mul, abs_pow, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh hh1 hh2
    rw [sq_abs] at hh1
    have hh3 := mul_le_mul_of_nonneg_left hh2 hm.1
    change |_ + _| ≤ _
    nlinarith
  have hJm : Measurable J := hG'm.add ((hGm.const_mul m).mul hSc.measurable)
  have hJb (y : ℝ) : |J y| ≤ 2 * K3 ^ 2 + 2 * K4 + 4 * K3 + 2 := by
    have hp := mul_le_mul (hGb y) (hSb y) (abs_nonneg _) (by positivity : 0 ≤ 2 * K3 + 1)
    have hh := abs_add_le (G' y) (m * G y * S y)
    simp only [abs_mul, abs_of_nonneg hm.1] at hh
    have h1 := mul_le_mul_of_nonneg_left hp hm.1
    have h2 := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 2 * K3 + 1)
    change |_ + _| ≤ _
    nlinarith [hG'b y]
  have hBg : HasLinearGrowth B := hasLinearGrowth_parisiStep hA hcA.measurable m v
  have hBm : Measurable B := measurable_parisiStep hcA.measurable m v
  have hLip := flow_C2_lipschitz hB
  have hstein := integral_gaussian_mul_tilted_observable hBg hBm hSc.measurable hB.1 hSb
    hGd hG'm hGb hG'b m (a - v) x
  have hPi := flow_tilted_integrable hBg hBm hLip hPm hPb (m := m) (v := a - v) x
  have hJi := flow_tilted_integrable hBg hBm hLip hJm hJb (m := m) (v := a - v) x
  have hxi : Integrable (fun z => z * (G (Y z) * W z)) (gaussianReal 0 1) := by
    have hh := integrable_mul_tiltWeight_of_bound (m := m) (v := a - v) zero_le_one hLip hBg hBm x
      (measurable_id.mul (hGm.comp (measurable_tilt_shift (a - v) x)))
      (a := 0) (b := 2 * K3 + 1) (by positivity)
      (fun z => by simpa only [Pi.mul_apply, Function.comp_def, id_eq, abs_mul, zero_add, mul_comm, Y] using
        mul_le_mul_of_nonneg_left (hGb (Y z)) (abs_nonneg z))
    simpa only [Pi.mul_apply, Function.comp_def, id_eq, mul_assoc, Y, W] using hh
  have heq : splitBaselineHessianDerivative A A' A'' A''' m a x v =
      ∫ z, (P (Y z) - J (Y z) / 2) * W z ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ z, P (Y z) * W z - (1 / (2 * Real.sqrt (a - v))) *
          (z * (G (Y z) * W z)) ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp only [splitBaselineHessianVelocity, splitVarianceVelocity, P, G, H, Y, T, S, E, J2]
        ring
      _ = (∫ z, P (Y z) * W z ∂(gaussianReal 0 1)) -
          (1 / (2 * Real.sqrt (a - v))) * ∫ z, z * (G (Y z) * W z) ∂(gaussianReal 0 1) := by
        rw [integral_sub hPi (hxi.const_mul _), integral_const_mul]
      _ = (∫ z, P (Y z) * W z ∂(gaussianReal 0 1)) -
          (∫ z, J (Y z) * W z ∂(gaussianReal 0 1)) / 2 := by
        rw [hstein]
        dsimp only [J, Y, W]
        field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hv.2)).ne']
      _ = _ := by
        rw [← integral_div, ← integral_sub hPi (hJi.div_const 2)]
        apply integral_congr_ae
        filter_upwards with z
        ring
  have hbound (y : ℝ) : |P y - J y / 2| ≤ 2 * K2 + K3 ^ 2 + K4 + 2 * K3 + 2 := by
    have hh := abs_sub (P y) (J y / 2)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    nlinarith [hPb y, hJb y]
  rw [heq]
  simpa only [zero_mul, add_zero, mul_zero, zero_add, Pi.sub_apply, Y, W, B] using!
    abs_integral_mul_tiltWeight_le (m := m) (v := a - v) zero_le_one hLip hBg hBm
      (hPm.sub (hJm.div_const 2)) (D' := 0) le_rfl
      (by simpa only [zero_mul, add_zero, Pi.sub_apply] using! hbound) x

/-- The actual scalar flow is differentiable with the uniform Stein bound. -/
theorem abs_deriv_splitBaselineHessianSquare_le {A A' A'' A''' D4 : ℝ → ℝ}
    {K K2 K3 K4 : ℝ} (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA3d : ∀ y, HasDerivAt A'' (A''' y) y) (hcA3 : Continuous A''')
    (hA3b : ∀ y, |A''' y| ≤ K) {m a v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hJ2 : ∀ w ∈ Set.Ioo 0 a, ∀ y, |stepD2Variance A A' A'' A''' m w y| ≤ K2)
    (hE : ∀ w ∈ Set.Ioo 0 a, ∀ y, |stepD3 A A' A'' m w y| ≤ K3)
    (hv : v ∈ Set.Ioo 0 a)
    (hD4 : ∀ y, HasDerivAt (stepD3 A A' A'' m v) (D4 y) y)
    (hD4m : Measurable D4) (hD4b : ∀ y, |D4 y| ≤ K4) (x : ℝ) :
    |deriv (splitBaselineHessianSquare A A' A'' m a x) v| ≤
      2 * K2 + K3 ^ 2 + K4 + 2 * K3 + 2 := by
  rw [(hasDerivAt_splitBaselineHessianSquare_before_ibp hA hC2 hA3d hcA3 hA3b hm a x hJ2 hE hv).deriv]
  exact abs_splitBaselineHessianDerivative_le hA hC2 hA3d hcA3 hA3b hm hv
    (hJ2 v hv) (hE v hv) hD4 hD4m hD4b x

end SpinGlass.Targets
