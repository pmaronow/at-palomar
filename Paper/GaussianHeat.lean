module

public import Paper.GaussianDifferentiation
public import Paper.GaussianIBP
public import Paper.GaussianPositivity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Gaussian heat derivatives and joint continuity

The variance derivative is proved by dominated differentiation in the Gaussian
scale, followed by the actual standard-Gaussian Stein identity. The square-root
chain rule is used only at strictly positive variance.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem integrable_standardGaussian_id : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  apply integrable_of_mem_interior_integrableExpSet (X := fun z : ℝ => z)
  simp [integrableExpSet_fun_id_gaussianReal]

/-- Differentiation in the affine Gaussian scale. The dominating function is
`M * |Z|`, whose Gaussian integrability is proved from exponential moments. -/
theorem hasDerivAt_gaussian_scale (f df : ℝ → ℝ) (h a M : ℝ)
    (hf : Continuous f) (hdf : Continuous df)
    (hi : Integrable (fun z => f (h + a * z)) (gaussianReal 0 1))
    (hd : ∀ x, HasDerivAt f (df x) x) (hb : ∀ x, ‖df x‖ ≤ M) :
    HasDerivAt (fun b => gaussianExpectation (fun z => f (h + b * z)))
      (gaussianExpectation (fun z => df (h + a * z) * z)) a := by
  have hc (b : ℝ) : Continuous (fun z : ℝ => h + b * z) := by fun_prop
  have hmeas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (fun z => f (h + b * z)) (gaussianReal 0 1) :=
    .of_forall fun b => (hf.comp (hc b)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun z => df (h + a * z) * z) (gaussianReal 0 1) :=
    ((hdf.comp (hc a)).mul continuous_id).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      ‖df (h + b * z) * z‖ ≤ M * ‖z‖ := by
    filter_upwards with z b _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  have hdiff : ∀ᵐ z ∂gaussianReal 0 1, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun x => f (h + x * z)) (df (h + b * z) * z) b := by
    filter_upwards with z b _
    have hinner : HasDerivAt (fun x : ℝ => h + x * z) z b := by
      simpa using ((hasDerivAt_id b).mul_const z).const_add h
    exact (hd (h + b * z)).comp b hinner
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b z => f (h + b * z)) (F' := fun b z => df (h + b * z) * z)
    (bound := fun z => M * ‖z‖) (s := Set.univ) (by simp)
    hmeas hi hmeas' hbound (integrable_standardGaussian_id.norm.const_mul M) hdiff).2

/-- The Gaussian heat equation for a twice differentiable observable with
bounded first and second derivatives. Its proof includes derivative exchange
and Gaussian integration by parts. -/
theorem hasDerivAt_gaussian_variance (f df ddf : ℝ → ℝ) (h t M K : ℝ)
    (ht : 0 < t) (hf : Continuous f) (hdf : Continuous df) (hddf : Continuous ddf)
    (hi : Integrable (fun z => f (h + Real.sqrt t * z)) (gaussianReal 0 1))
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖df x‖ ≤ M) (hdb : ∀ x, ‖ddf x‖ ≤ K) :
    HasDerivAt (fun b => gaussianExpectation (fun z => f (h + Real.sqrt b * z)))
      ((1 / 2 : ℝ) * gaussianExpectation (fun z => ddf (h + Real.sqrt t * z))) t := by
  let a := Real.sqrt t
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have hc : Continuous (fun z : ℝ => h + a * z) := by fun_prop
  have hstein := gaussian_stein_of_bounded
    (fun z => df (h + a * z)) (fun z => ddf (h + a * z) * a) M (K * ‖a‖)
    (hdf.comp hc) ((hddf.comp hc).mul continuous_const)
    (fun z => by
      have hinner : HasDerivAt (fun y : ℝ => h + a * y) a z := by
        simpa using ((hasDerivAt_id z).const_mul a).const_add h
      exact (hdd (h + a * z)).comp z hinner)
    (fun z => hb _) (fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hdb _) (norm_nonneg _))
  have hscale : gaussianExpectation (fun z => df (h + a * z) * z) =
      a * gaussianExpectation (fun z => ddf (h + a * z)) := by
    calc
      _ = gaussianExpectation (fun z => z * df (h + a * z)) := by
        congr 1
        ext z
        ring
      _ = gaussianExpectation (fun z => ddf (h + a * z) * a) := hstein
      _ = _ := by
        unfold gaussianExpectation
        rw [integral_mul_const]
        ring
  have hdscale := hasDerivAt_gaussian_scale f df h a M hf hdf hi hd hb
  rw [hscale] at hdscale
  convert hdscale.comp t (Real.hasDerivAt_sqrt (ne_of_gt ht)) using 1
  · rfl
  · dsimp [a]
    field_simp

theorem continuous_gaussian_sech_pow_joint (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => gaussianExpectation
      (fun z => sech (p.1 + Real.sqrt p.2 * z) ^ n)) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro p
    have hc : Continuous (fun z : ℝ => p.1 + Real.sqrt p.2 * z) := by fun_prop
    exact ((gaussian_continuous_sech.comp hc).pow n).aestronglyMeasurable
  · intro p
    filter_upwards with z
    rw [Real.norm_of_nonneg (pow_nonneg (sech_pos _).le n)]
    exact pow_le_one₀ (sech_pos _).le (sech_le_one _)
  · exact integrable_const 1
  · filter_upwards with z
    have hc : Continuous (fun p : ℝ × ℝ => p.1 + Real.sqrt p.2 * z) := by fun_prop
    exact (gaussian_continuous_sech.comp hc).pow n

theorem continuous_gaussianA_joint : Continuous (fun p : ℝ × ℝ => gaussianA p.1 p.2) :=
  continuous_gaussian_sech_pow_joint 2

theorem continuous_gaussianC_joint : Continuous (fun p : ℝ × ℝ => gaussianC p.1 p.2) :=
  continuous_gaussian_sech_pow_joint 4

theorem continuous_atZeroFunction_joint : Continuous (fun p : ℝ × ℝ => atZeroFunction p.1 p.2) :=
  (continuous_snd.mul continuous_gaussianC_joint).add continuous_gaussianA_joint |>.sub continuous_const

noncomputable def gaussianD (h t : ℝ) : ℝ :=
  gaussianExpectation (fun z => sech (h + Real.sqrt t * z) ^ 6)

theorem sech_sq_second_derivative_bound (x : ℝ) :
    ‖4 * sech x ^ 2 - 6 * sech x ^ 4‖ ≤ 10 := by
  calc
    _ ≤ ‖4 * sech x ^ 2‖ + ‖6 * sech x ^ 4‖ := norm_sub_le _ _
    _ ≤ 10 := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg (sech x)),
        Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 4)]
      norm_num
      nlinarith [sech_sq_le_one x, sech_fourth_le_one x]

theorem sech_fourth_second_derivative_bound (x : ℝ) :
    ‖16 * sech x ^ 4 - 20 * sech x ^ 6‖ ≤ 36 := by
  calc
    _ ≤ ‖16 * sech x ^ 4‖ + ‖20 * sech x ^ 6‖ := norm_sub_le _ _
    _ ≤ 36 := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 4),
        Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 6)]
      norm_num
      nlinarith [sech_fourth_le_one x,
        pow_le_one₀ (sech_pos x).le (sech_le_one x) (n := 6)]

/-- The actual Gaussian heat identity `A_t = 2A - 3C`. -/
theorem hasDerivAt_gaussianA_variance (h : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianA h) (2 * gaussianA h t - 3 * gaussianC h t) t := by
  have hdd (x : ℝ) : HasDerivAt (fun y => -2 * Real.tanh y * sech y ^ 2)
      (4 * sech x ^ 2 - 6 * sech x ^ 4) x := by
    convert (hasDerivAt_tanh_mul_sech_sq x).const_mul (-2) using 1
    · ext y
      ring
    · ring
  have hv := hasDerivAt_gaussian_variance (fun x => sech x ^ 2)
    (fun x => -2 * Real.tanh x * sech x ^ 2)
    (fun x => 4 * sech x ^ 2 - 6 * sech x ^ 4) h t 2 10 ht
    (gaussian_continuous_sech.pow 2)
    ((continuous_const.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 2))
    ((continuous_const.mul (gaussian_continuous_sech.pow 2)).sub
      (continuous_const.mul (gaussian_continuous_sech.pow 4)))
    (integrable_gaussian_sech_pow h (Real.sqrt t) 2)
    hasDerivAt_sech_sq hdd sech_sq_derivative_bound sech_sq_second_derivative_bound
  have he : gaussianExpectation (fun z => 4 * sech (h + Real.sqrt t * z) ^ 2 -
      6 * sech (h + Real.sqrt t * z) ^ 4) = 4 * gaussianA h t - 6 * gaussianC h t := by
    simp only [gaussianA, gaussianC, gaussianExpectation]
    rw [integral_sub ((integrable_gaussian_sech_pow h (Real.sqrt t) 2).const_mul 4)
      ((integrable_gaussian_sech_pow h (Real.sqrt t) 4).const_mul 6)]
    rw [integral_const_mul, integral_const_mul]
  rw [he] at hv
  convert hv using 1
  · rfl
  · ring

/-- The actual Gaussian heat identity `C_t = 8C - 10 E[sech⁶]`. -/
theorem hasDerivAt_gaussianC_variance (h : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianC h) (8 * gaussianC h t - 10 * gaussianD h t) t := by
  have hdd (x : ℝ) : HasDerivAt (fun y => -4 * Real.tanh y * sech y ^ 4)
      (16 * sech x ^ 4 - 20 * sech x ^ 6) x := by
    convert (hasDerivAt_tanh_mul_sech_fourth x).const_mul (-4) using 1
    · ext y
      ring
    · ring
  have hv := hasDerivAt_gaussian_variance (fun x => sech x ^ 4)
    (fun x => -4 * Real.tanh x * sech x ^ 4)
    (fun x => 16 * sech x ^ 4 - 20 * sech x ^ 6) h t 4 36 ht
    (gaussian_continuous_sech.pow 4)
    ((continuous_const.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 4))
    ((continuous_const.mul (gaussian_continuous_sech.pow 4)).sub
      (continuous_const.mul (gaussian_continuous_sech.pow 6)))
    (integrable_gaussian_sech_pow h (Real.sqrt t) 4)
    hasDerivAt_sech_fourth hdd sech_fourth_derivative_bound sech_fourth_second_derivative_bound
  have he : gaussianExpectation (fun z => 16 * sech (h + Real.sqrt t * z) ^ 4 -
      20 * sech (h + Real.sqrt t * z) ^ 6) = 16 * gaussianC h t - 20 * gaussianD h t := by
    simp only [gaussianC, gaussianD, gaussianExpectation]
    rw [integral_sub ((integrable_gaussian_sech_pow h (Real.sqrt t) 4).const_mul 16)
      ((integrable_gaussian_sech_pow h (Real.sqrt t) 6).const_mul 20)]
    rw [integral_const_mul, integral_const_mul]
  rw [he] at hv
  convert hv using 1
  · rfl
  · ring

/-- Joint continuity at every mean and variance, including variance zero, for
any bounded continuous observable. -/
theorem continuous_gaussian_affine_joint (f : ℝ → ℝ) (C : ℝ)
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun p : ℝ × ℝ => gaussianExpectation
      (fun z => f (p.1 + Real.sqrt p.2 * z))) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p
    have hc : Continuous (fun z : ℝ => p.1 + Real.sqrt p.2 * z) := by fun_prop
    exact (hf.comp hc).aestronglyMeasurable
  · intro p
    exact .of_forall fun z => hb _
  · exact integrable_const C
  · filter_upwards with z
    have hc : Continuous (fun p : ℝ × ℝ => p.1 + Real.sqrt p.2 * z) := by fun_prop
    exact hf.comp hc

theorem continuous_gaussianU_joint : Continuous (fun p : ℝ × ℝ => gaussianU p.1 p.2) :=
  continuous_gaussian_affine_joint (fun y => Real.tanh y * sech y ^ 2) 1
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 2))
    (fun y => norm_tanh_mul_sech_pow_le_one y 2)

theorem continuous_gaussianV_joint : Continuous (fun p : ℝ × ℝ => gaussianV p.1 p.2) :=
  continuous_gaussian_affine_joint (fun y => Real.tanh y * sech y ^ 4) 1
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4))
    (fun y => norm_tanh_mul_sech_pow_le_one y 4)

theorem continuous_gaussianD_joint : Continuous (fun p : ℝ × ℝ => gaussianD p.1 p.2) :=
  continuous_gaussian_sech_pow_joint 6

theorem tanh_mul_sech_fourth_derivative_bound (x : ℝ) :
    ‖5 * sech x ^ 6 - 4 * sech x ^ 4‖ ≤ 9 := by
  calc
    _ ≤ ‖5 * sech x ^ 6‖ + ‖4 * sech x ^ 4‖ := norm_sub_le _ _
    _ ≤ 9 := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 6),
        Real.norm_of_nonneg (pow_nonneg (sech_pos x).le 4)]
      norm_num
      nlinarith [sech_fourth_le_one x,
        pow_le_one₀ (sech_pos x).le (sech_le_one x) (n := 6)]

/-- Gaussian integration by parts for the exact appendix moments. -/
theorem gaussianC_variance_stein_relation (h t : ℝ) (ht : 0 ≤ t) :
    gaussianT h t - h * gaussianV h t = t * (5 * gaussianD h t - 4 * gaussianC h t) := by
  have hs := gaussian_variance_stein (fun y => Real.tanh y * sech y ^ 4)
    (fun y => 5 * sech y ^ 6 - 4 * sech y ^ 4) h t 1 9 ht
    (gaussian_continuous_tanh.mul (gaussian_continuous_sech.pow 4))
    ((continuous_const.mul (gaussian_continuous_sech.pow 6)).sub
      (continuous_const.mul (gaussian_continuous_sech.pow 4)))
    hasDerivAt_tanh_mul_sech_fourth (fun y => norm_tanh_mul_sech_pow_le_one y 4)
    tanh_mul_sech_fourth_derivative_bound
  have hleft : gaussianExpectation (fun z => ((h + Real.sqrt t * z) - h) *
      (Real.tanh (h + Real.sqrt t * z) * sech (h + Real.sqrt t * z) ^ 4)) =
      gaussianT h t - h * gaussianV h t := by
    simp only [gaussianT, gaussianV, gaussianExpectation]
    rw [← integral_const_mul, ← integral_sub (integrable_gaussianT_integrand h t)
      ((integrable_gaussianV_integrand h t).const_mul h)]
    apply integral_congr_ae
    filter_upwards with z
    ring
  have hright : gaussianExpectation (fun z => 5 * sech (h + Real.sqrt t * z) ^ 6 -
      4 * sech (h + Real.sqrt t * z) ^ 4) = 5 * gaussianD h t - 4 * gaussianC h t := by
    simp only [gaussianD, gaussianC, gaussianExpectation]
    rw [integral_sub ((integrable_gaussian_sech_pow h (Real.sqrt t) 6).const_mul 5)
      ((integrable_gaussian_sech_pow h (Real.sqrt t) 4).const_mul 4),
      integral_const_mul, integral_const_mul]
  rw [hleft, hright] at hs
  exact hs

/-- Appendix identity `C_t = 2(hv - T)/t`, including the heat-derivative
exchange and the actual Gaussian integration-by-parts proof. -/
theorem hasDerivAt_gaussianC_variance_stein (h : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianC h) (2 * (h * gaussianV h t - gaussianT h t) / t) t := by
  have hs := gaussianC_variance_stein_relation h t ht.le
  have he : 8 * gaussianC h t - 10 * gaussianD h t =
      2 * (h * gaussianV h t - gaussianT h t) / t := by
    field_simp
    nlinarith [hs]
  rw [← he]
  exact hasDerivAt_gaussianC_variance h ht

/-- Appendix identity `F_t = 2(B - T + hv)` for the actual Gaussian function. -/
theorem hasDerivAt_atZeroFunction_variance (h : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (atZeroFunction h)
      (2 * (gaussianB h t - gaussianT h t + h * gaussianV h t)) t := by
  convert (((hasDerivAt_id t).mul (hasDerivAt_gaussianC_variance_stein h ht)).add
    (hasDerivAt_gaussianA_variance h ht)).sub_const 1 using 1
  · ext b
    simp only [atZeroFunction, Pi.mul_apply, Pi.add_apply, id_eq]
  · dsimp [gaussianB]
    field_simp
    ring

theorem atZeroFunction_variance_derivative_pos (h : ℝ) {t : ℝ}
    (hh : 0 ≤ h) (ht : 0 < t) : 0 < deriv (atZeroFunction h) t := by
  rw [(hasDerivAt_atZeroFunction_variance h ht).deriv]
  have hv : 0 ≤ h * gaussianV h t := by
    by_cases hh0 : h = 0
    · simp [hh0]
    · exact (mul_pos (lt_of_le_of_ne hh (Ne.symm hh0)) (gaussianV_pos h t
        (lt_of_le_of_ne hh (Ne.symm hh0)) ht)).le
  nlinarith [gaussianB_sub_gaussianT_pos h t ht]

theorem atZeroFunction_strictMonoOn_variance (h : ℝ) (hh : 0 ≤ h) :
    StrictMonoOn (atZeroFunction h) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact (continuous_atZeroFunction_joint.comp
      (continuous_const.prodMk continuous_id)).continuousOn
  · intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    exact atZeroFunction_variance_derivative_pos h hh ht

/-- The appendix's strict positivity `F(0,t)>0` follows from the actual heat
derivative and continuity through variance zero. -/
theorem atZeroFunction_zero_mean_pos {t : ℝ} (ht : 0 < t) : 0 < atZeroFunction 0 t := by
  have hm := atZeroFunction_strictMonoOn_variance 0 (by norm_num)
    (show (0 : ℝ) ∈ Set.Ici 0 by simp) ht.le ht
  simpa [atZeroFunction, gaussianA_zero_time, gaussianC_zero_time] using hm

theorem atZeroFunction_field_derivative_neg {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    deriv (fun b => atZeroFunction b t) h < 0 := by
  rw [(hasDerivAt_atZeroFunction_field h t).deriv]
  have hu := gaussianU_pos h t hh ht
  have hv := gaussianV_pos h t hh ht
  nlinarith

theorem atZeroFunction_strictAntiOn_field {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun h => atZeroFunction h t) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact (continuous_atZeroFunction_joint.comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro h hh
    rw [interior_Ici, Set.mem_Ioi] at hh
    exact atZeroFunction_field_derivative_neg hh ht

theorem continuous_gaussianT_joint : Continuous (fun p : ℝ × ℝ => gaussianT p.1 p.2) :=
  continuous_gaussian_affine_joint (fun y => y * Real.tanh y * sech y ^ 4) 1
    ((continuous_id.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 4))
    norm_y_tanh_sech_fourth_le_one

theorem tendsto_sech_atTop_zero : Tendsto sech atTop (𝓝 0) := by
  have hc : Tendsto Real.cosh atTop atTop := by
    convert (Real.tendsto_exp_atTop.atTop_add
      Real.tendsto_exp_neg_atTop_nhds_zero).atTop_div_const
        (by norm_num : (0 : ℝ) < 2) using 1
    ext x
    exact Real.cosh_eq x
  convert tendsto_inv_atTop_zero.comp hc using 1
  ext x
  simp [sech]

/-- Dominated convergence proves the large-field limit of every positive
sech moment. -/
theorem tendsto_gaussian_sech_pow_field (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun h => gaussianExpectation (fun z => sech (h + Real.sqrt t * z) ^ n))
      atTop (𝓝 0) := by
  have hm : ∀ᶠ h in atTop, AEStronglyMeasurable
      (fun z => sech (h + Real.sqrt t * z) ^ n) (gaussianReal 0 1) := by
    apply Eventually.of_forall
    intro h
    have hc : Continuous (fun z : ℝ => h + Real.sqrt t * z) := by fun_prop
    exact ((gaussian_continuous_sech.comp hc).pow n).aestronglyMeasurable
  have hb : ∀ᶠ h in atTop, ∀ᵐ z ∂gaussianReal 0 1,
      ‖sech (h + Real.sqrt t * z) ^ n‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro h
    filter_upwards with z
    rw [Real.norm_of_nonneg (pow_nonneg (sech_pos _).le n)]
    exact pow_le_one₀ (sech_pos _).le (sech_le_one _)
  have hl : ∀ᵐ z ∂gaussianReal 0 1,
      Tendsto (fun h => sech (h + Real.sqrt t * z) ^ n) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with z
    have hshift : Tendsto (fun h : ℝ => h + Real.sqrt t * z) atTop atTop :=
      tendsto_id.atTop_add tendsto_const_nhds
    simpa only [Function.comp_def, zero_pow hn] using (tendsto_sech_atTop_zero.comp hshift).pow n
  simpa only [gaussianExpectation, integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) hm hb
      (integrable_const 1) hl

theorem tendsto_gaussianA_field (t : ℝ) : Tendsto (fun h => gaussianA h t) atTop (𝓝 0) :=
  tendsto_gaussian_sech_pow_field t 2 (by norm_num)

theorem tendsto_gaussianC_field (t : ℝ) : Tendsto (fun h => gaussianC h t) atTop (𝓝 0) :=
  tendsto_gaussian_sech_pow_field t 4 (by norm_num)

theorem tendsto_atZeroFunction_field (t : ℝ) :
    Tendsto (fun h => atZeroFunction h t) atTop (𝓝 (-1 : ℝ)) := by
  simpa only [atZeroFunction, mul_zero, zero_add, zero_sub] using
    ((tendsto_const_nhds.mul (tendsto_gaussianC_field t)).add
      (tendsto_gaussianA_field t)).sub (tendsto_const_nhds (x := (1 : ℝ)))

end Paper
