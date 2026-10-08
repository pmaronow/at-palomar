module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Lemmas.SpinGlass.GaussianIntegrationByParts

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal
open scoped Topology

set_option autoImplicit false

namespace SpinGlass.AT

private lemma integral_eq_integral_Ioi_add_neg {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x, f x = ∫ x in Set.Ioi (0 : ℝ), (f x + f (-x)) := by
  have hsplit := setIntegral_union (f := f)
    (Set.Iic_disjoint_Ioi (a := (0 : ℝ)) (b := 0) le_rfl)
    measurableSet_Ioi hf.integrableOn hf.integrableOn
  rw [Set.Iic_union_Ioi, setIntegral_univ] at hsplit
  have hneg : ∫ x in Set.Ioi (0 : ℝ), f (-x) = ∫ x in Set.Iic 0, f x := by
    simpa using integral_comp_neg_Ioi (0 : ℝ) f
  calc
    ∫ x, f x = (∫ x in Set.Iic 0, f x) + ∫ x in Set.Ioi 0, f x := hsplit
    _ = (∫ x in Set.Ioi 0, f (-x)) + ∫ x in Set.Ioi 0, f x := by rw [hneg]
    _ = ∫ x in Set.Ioi 0, (f (-x) + f x) :=
      (integral_add hf.comp_neg.integrableOn hf.integrableOn).symm
    _ = ∫ x in Set.Ioi 0, (f x + f (-x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

private lemma standard_affine_integral_eq_gaussian
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ z, f (x + Real.sqrt r * z) ∂gaussianReal 0 1) =
      ∫ y, f y ∂gaussianReal x ⟨r, hr⟩ := by
  let v : ℝ≥0 := ⟨r, hr⟩
  have hmul : Measure.map (fun z : ℝ => Real.sqrt r * z) (gaussianReal 0 1) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one]
    exact Real.sq_sqrt hr
  have hadd : Measure.map (fun y : ℝ => x + y) (gaussianReal 0 v) =
      gaussianReal x v := by
    simpa using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := v) x
  have hmap : Measure.map (fun z : ℝ => x + Real.sqrt r * z)
      (gaussianReal 0 1) = gaussianReal x v := by
    calc
      Measure.map (fun z : ℝ => x + Real.sqrt r * z) (gaussianReal 0 1) =
          Measure.map (fun y : ℝ => x + y)
            (Measure.map (fun z : ℝ => Real.sqrt r * z) (gaussianReal 0 1)) := by
              simpa [Function.comp_def] using
                (Measure.map_map (μ := gaussianReal 0 1)
                  (g := fun y : ℝ => x + y)
                  (f := fun z : ℝ => Real.sqrt r * z)
                  (by fun_prop) (by fun_prop)).symm
      _ = Measure.map (fun y : ℝ => x + y) (gaussianReal 0 v) := by rw [hmul]
      _ = gaussianReal x v := hadd
  calc
    (∫ z, f (x + Real.sqrt r * z) ∂gaussianReal 0 1) =
        ∫ y, f y ∂Measure.map (fun z : ℝ => x + Real.sqrt r * z)
          (gaussianReal 0 1) := by
            rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ y, f y ∂gaussianReal x ⟨r, hr⟩ := by rw [hmap]

/-- The standard real Gaussian is invariant under reflection. -/
theorem standardGaussian_integral_comp_neg (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z, f (-z) ∂gaussianReal 0 1) = ∫ z, f z ∂gaussianReal 0 1 := by
  have hmap : Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) =
      gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  calc
    (∫ z, f (-z) ∂gaussianReal 0 1) =
        ∫ z, f z ∂Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) := by
          rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    _ = ∫ z, f z ∂gaussianReal 0 1 := by rw [hmap]

/-!
# The Latała--Guerra monotonicity lemma

This module contains the analytic input behind uniqueness of the
replica-symmetric fixed point. It is kept separate from the definition of the
fixed point so that the latter remains a small public API.
-/

private noncomputable def lgSech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

private lemma lgSech_pos (x : ℝ) : 0 < lgSech x :=
  inv_pos.mpr (Real.cosh_pos x)

private lemma lgSech_le_one (x : ℝ) : lgSech x ≤ 1 :=
  inv_le_one_of_one_le₀ (Real.one_le_cosh x)

private lemma lgContinuous_sech : Continuous lgSech := by
  unfold lgSech
  exact Real.continuous_cosh.inv₀ fun x => (Real.cosh_pos x).ne'

private lemma lgTanh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh y) (lgSech x ^ 2) x := by
  rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y]
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  apply h.congr_deriv
  unfold lgSech
  rw [show Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x =
    Real.cosh x ^ 2 - Real.sinh x ^ 2 by ring]
  rw [Real.cosh_sq_sub_sinh_sq]
  field_simp

private lemma lgContinuous_tanh : Continuous (fun x : ℝ => Real.tanh x) := by
  exact continuous_iff_continuousAt.2 fun x => (lgTanh_hasDerivAt x).continuousAt

private lemma lgTanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos ((Real.sinh_pos_iff).2 hx) (Real.cosh_pos x)

private lemma lgTanh_ne_zero {x : ℝ} (hx : x ≠ 0) : Real.tanh x ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_ne_zero (Real.sinh_ne_zero.mpr hx) (Real.cosh_pos x).ne'

private lemma lgTanh_monotone : Monotone Real.tanh := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (lgTanh_hasDerivAt x).differentiableAt
  · intro x
    rw [(lgTanh_hasDerivAt x).deriv]
    positivity

private lemma lgTanh_mul_sechSq_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.tanh x * lgSech x ^ 2 := by
  exact mul_nonneg (by simpa using lgTanh_monotone hx) (sq_nonneg _)

private lemma lgTanh_mul_sechSq_odd (x : ℝ) :
    Real.tanh (-x) * lgSech (-x) ^ 2 =
      -(Real.tanh x * lgSech x ^ 2) := by
  rw [Real.tanh_neg]
  unfold lgSech
  rw [Real.cosh_neg]
  ring

private lemma lgTanh_mul_sechSq_abs_le_one (x : ℝ) :
    |Real.tanh x * lgSech x ^ 2| ≤ 1 := by
  rw [abs_mul, abs_pow]
  calc
    |Real.tanh x| * |lgSech x| ^ 2 ≤ 1 * 1 ^ 2 := by
      gcongr
      · exact (Real.abs_tanh_lt_one x).le
      · rw [abs_of_pos (lgSech_pos x)]
        exact lgSech_le_one x
    _ = 1 := by norm_num

private lemma lgTanh_sq_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh y ^ 2)
      (2 * (Real.tanh x * lgSech x ^ 2)) x := by
  have h := (lgTanh_hasDerivAt x).mul (lgTanh_hasDerivAt x)
  rw [show (fun y : ℝ => Real.tanh y ^ 2) =
      fun y => Real.tanh y * Real.tanh y by funext y; ring]
  exact h.congr_deriv (by ring)

private lemma lgTanh_sq_abs_le_one (x : ℝ) : |Real.tanh x ^ 2| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one x).le

private lemma lgContinuous_tanh_sq :
    Continuous (fun x : ℝ => Real.tanh x ^ 2) := by
  exact continuous_iff_continuousAt.2 fun x =>
    (lgTanh_sq_hasDerivAt x).continuousAt

noncomputable def latalaGuerraNumerator (h x : ℝ) : ℝ :=
  ∫ z, Real.tanh (h + Real.sqrt x * z) ^ 2 ∂gaussianReal 0 1

private lemma latalaGuerraNumerator_hasDerivAt {h x : ℝ} (hx : 0 < x) :
    HasDerivAt (latalaGuerraNumerator h)
      (∫ z, (Real.tanh (h + Real.sqrt x * z) *
          lgSech (h + Real.sqrt x * z) ^ 2) * z / Real.sqrt x
        ∂gaussianReal 0 1) x := by
  let F : ℝ → ℝ → ℝ := fun t z => Real.tanh (h + Real.sqrt t * z) ^ 2
  let F' : ℝ → ℝ → ℝ := fun t z =>
    (Real.tanh (h + Real.sqrt t * z) *
      lgSech (h + Real.sqrt t * z) ^ 2) * z / Real.sqrt t
  let c : ℝ := (Real.sqrt (x / 2))⁻¹
  let bound : ℝ → ℝ := fun z => c * |z|
  have hregion : Set.Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  have hsqrtLower : ∀ t ∈ Set.Ioi (x / 2), Real.sqrt (x / 2) ≤ Real.sqrt t :=
    fun t ht => Real.sqrt_le_sqrt ht.le
  have hboundInt : Integrable bound (gaussianReal 0 1) := by
    have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact hz.const_mul c
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := F) (F' := F') (x₀ := x)
    (s := Set.Ioi (x / 2)) (bound := bound) hregion
    (Filter.Eventually.of_forall fun t =>
      (lgContinuous_tanh_sq.comp (by fun_prop)).aestronglyMeasurable)
    (by
      apply Integrable.of_bound (C := 1)
      · exact (lgContinuous_tanh_sq.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards [] with z
        simpa [F, Real.norm_eq_abs] using
          lgTanh_sq_abs_le_one (h + Real.sqrt x * z))
    (by
      apply Continuous.aestronglyMeasurable
      dsimp [F']
      exact (((lgContinuous_tanh.comp (by fun_prop)).mul
        ((lgContinuous_sech.comp (by fun_prop)).pow 2)).mul
          continuous_id).div_const _)
    (by
      filter_upwards [] with z
      intro t ht
      have ht0 : 0 < t := lt_trans (half_pos hx) ht
      have hsqrt0 : 0 < Real.sqrt (x / 2) := Real.sqrt_pos.2 (half_pos hx)
      have hsqrtt0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
      have hinv : (Real.sqrt t)⁻¹ ≤ c := by
        exact (inv_le_inv₀ hsqrtt0 hsqrt0).2 (hsqrtLower t ht)
      rw [Real.norm_eq_abs]
      dsimp [F', bound]
      rw [abs_div, abs_mul]
      have hg := lgTanh_mul_sechSq_abs_le_one
        (h + Real.sqrt t * z)
      rw [abs_of_pos hsqrtt0]
      calc
        |Real.tanh (h + Real.sqrt t * z) *
              lgSech (h + Real.sqrt t * z) ^ 2| * |z| / Real.sqrt t =
            (Real.sqrt t)⁻¹ *
              (|Real.tanh (h + Real.sqrt t * z) *
                lgSech (h + Real.sqrt t * z) ^ 2| * |z|) := by
                  field_simp
        _ ≤ c * (1 * |z|) := by gcongr
        _ = c * |z| := by ring)
    hboundInt
    (by
      filter_upwards [] with z
      intro t ht
      have ht0 : 0 < t := lt_trans (half_pos hx) ht
      have harg : HasDerivAt (fun u : ℝ => h + Real.sqrt u * z)
          (z / (2 * Real.sqrt t)) t := by
        have ha := ((Real.hasDerivAt_sqrt ht0.ne').mul_const z).const_add h
        have hcoef : z / (2 * Real.sqrt t) = 1 / (2 * Real.sqrt t) * z := by ring
        rw [hcoef]
        simpa only [add_comm] using ha
      have htanh := (lgTanh_hasDerivAt (h + Real.sqrt t * z)).comp t harg
      change HasDerivAt (fun u => Real.tanh (h + Real.sqrt u * z) ^ 2)
        ((Real.tanh (h + Real.sqrt t * z) *
          lgSech (h + Real.sqrt t * z) ^ 2) * z / Real.sqrt t) t
      have hout : HasDerivAt
          ((fun u => Real.tanh (h + Real.sqrt u * z)) *
            (fun u => Real.tanh (h + Real.sqrt u * z)))
          ((Real.tanh (h + Real.sqrt t * z) *
            lgSech (h + Real.sqrt t * z) ^ 2) * z / Real.sqrt t) t := by
        apply (htanh.mul htanh).congr_deriv
        simp only [Function.comp_apply]
        field_simp [(Real.sqrt_pos.2 ht0).ne']
        ring
      convert hout using 1
      funext u
      simp only [Pi.mul_apply, pow_two])
  dsimp only [F, F'] at hdiff
  exact hdiff.2

noncomputable def latalaGuerraRatio (h x : ℝ) : ℝ :=
  latalaGuerraNumerator h x / x

private noncomputable def lgCore (y : ℝ) : ℝ :=
  Real.tanh y * (y * lgSech y ^ 2 - Real.tanh y)

private lemma lgCore_neg {y : ℝ} (hy : y ≠ 0) : lgCore y < 0 := by
  have hpos : ∀ {u : ℝ}, 0 < u → u * lgSech u ^ 2 < Real.tanh u := by
    intro u hu
    have hs : 2 * u < Real.sinh (2 * u) :=
      Real.self_lt_sinh_iff.mpr (by linarith)
    rw [Real.sinh_two_mul] at hs
    rw [Real.tanh_eq_sinh_div_cosh]
    unfold lgSech
    have hc := Real.cosh_pos u
    field_simp [hc.ne']
    nlinarith
  by_cases hypos : 0 < y
  · unfold lgCore
    exact mul_neg_of_pos_of_neg (lgTanh_pos hypos)
      (sub_neg.mpr (hpos hypos))
  · have hny : 0 < -y := by
      have : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
      linarith
    have hkneg : lgCore (-y) < 0 := by
      unfold lgCore
      exact mul_neg_of_pos_of_neg (lgTanh_pos hny)
        (sub_neg.mpr (hpos hny))
    unfold lgCore at hkneg ⊢
    rw [Real.tanh_neg] at hkneg
    unfold lgSech at hkneg ⊢
    rw [Real.cosh_neg] at hkneg
    nlinarith

private lemma lgCore_nonpos (y : ℝ) : lgCore y ≤ 0 := by
  by_cases hy : y = 0
  · simp [hy, lgCore]
  · exact (lgCore_neg hy).le

private lemma lgCore_abs_le (y : ℝ) : |lgCore y| ≤ |y| + 1 := by
  unfold lgCore
  rw [abs_mul]
  calc
    |Real.tanh y| * |y * lgSech y ^ 2 - Real.tanh y| ≤
        1 * (|y * lgSech y ^ 2| + |Real.tanh y|) := by
          gcongr
          · exact (Real.abs_tanh_lt_one y).le
          · exact abs_sub _ _
    _ ≤ 1 * (|y| * 1 + 1) := by
      gcongr
      · rw [abs_mul, abs_pow]
        gcongr
        rw [abs_of_pos (lgSech_pos y)]
        nlinarith [lgSech_pos y, lgSech_le_one y]
      · exact (Real.abs_tanh_lt_one y).le
    _ = |y| + 1 := by ring

private lemma integrable_lgCore_affine (h x : ℝ) :
    Integrable (fun z => lgCore (h + Real.sqrt x * z))
      (gaussianReal 0 1) := by
  have hz : Integrable (fun z : ℝ => |h| + Real.sqrt x * |z| + 1)
      (gaussianReal 0 1) := by
    have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    exact ((integrable_const |h|).add (habs.const_mul (Real.sqrt x))).add
      (integrable_const 1)
  apply Integrable.mono' hz
  · apply Continuous.aestronglyMeasurable
    unfold lgCore lgSech
    exact (lgContinuous_tanh.mul
      ((continuous_id.mul (lgContinuous_sech.pow 2)).sub
        lgContinuous_tanh)).comp (by fun_prop)
  · filter_upwards [] with z
    rw [Real.norm_eq_abs]
    calc
      |lgCore (h + Real.sqrt x * z)| ≤ |h + Real.sqrt x * z| + 1 :=
        lgCore_abs_le _
      _ ≤ |h| + Real.sqrt x * |z| + 1 := by
        calc
          |h + Real.sqrt x * z| + 1 ≤ |h| + |Real.sqrt x * z| + 1 := by
            linarith [abs_add_le h (Real.sqrt x * z)]
          _ = |h| + Real.sqrt x * |z| + 1 := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]

private lemma integral_lgCore_affine_neg {h x : ℝ} (hh : 0 < h) (_hx : 0 < x) :
    (∫ z, lgCore (h + Real.sqrt x * z) ∂gaussianReal 0 1) < 0 := by
  have hnonneg : 0 ≤ fun z => -lgCore (h + Real.sqrt x * z) :=
    fun z => neg_nonneg.mpr (lgCore_nonpos _)
  have hint := (integrable_lgCore_affine h x).neg
  rw [← neg_pos, ← integral_neg]
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0))
      |>.isOpenPosMeasure
  apply integral_pos_of_integrable_nonneg_nonzero
    (f := fun z => -lgCore (h + Real.sqrt x * z))
    (x := 0)
  · unfold lgCore lgSech
    exact (lgContinuous_tanh.mul
      ((continuous_id.mul (lgContinuous_sech.pow 2)).sub
        lgContinuous_tanh)).comp (by fun_prop) |>.neg
  · exact hint
  · exact hnonneg
  · simp only [mul_zero, add_zero, neg_ne_zero]
    exact (lgCore_neg hh.ne').ne

private lemma integral_tanh_mul_sechSq_affine_nonneg {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    0 ≤ ∫ z, Real.tanh (h + Real.sqrt x * z) *
      lgSech (h + Real.sqrt x * z) ^ 2 ∂gaussianReal 0 1 := by
  -- Pairing `y` with `-y` in the Gaussian density proves the sign.
  let v : ℝ≥0 := ⟨x, hx.le⟩
  let g : ℝ → ℝ := fun y => Real.tanh y * lgSech y ^ 2
  have hvpos : 0 < v := by exact hx
  have hv : v ≠ 0 := hvpos.ne'
  have hshift :
      (∫ z, g (h + Real.sqrt x * z) ∂gaussianReal 0 1) =
        ∫ y, g y ∂gaussianReal h v := by
    simpa [v, g] using standard_affine_integral_eq_gaussian hx.le h
      (lgContinuous_tanh.mul
        (lgContinuous_sech.pow 2))
  rw [show (fun z => Real.tanh (h + Real.sqrt x * z) *
      lgSech (h + Real.sqrt x * z) ^ 2) =
      fun z => g (h + Real.sqrt x * z) by rfl, hshift]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hvol : Integrable (fun y => gaussianPDFReal h v y * g y) := by
    apply Integrable.mono' (integrable_gaussianPDFReal h v)
    · exact ((measurable_gaussianPDFReal h v).mul
        ((lgContinuous_tanh.mul
          (lgContinuous_sech.pow 2)).measurable))
          |>.aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul]
      have hp := gaussianPDFReal_nonneg h v y
      rw [abs_of_nonneg hp]
      exact mul_le_of_le_one_right hp (by
        change |Real.tanh y * lgSech y ^ 2| ≤ 1
        exact lgTanh_mul_sechSq_abs_le_one y)
  rw [integral_eq_integral_Ioi_add_neg hvol]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0 ≤ gaussianPDFReal h v y * g y + gaussianPDFReal h v (-y) * g (-y)
  have hy0 : 0 ≤ y := hy.le
  have hp : gaussianPDFReal h v (-y) ≤ gaussianPDFReal h v y := by
    rw [gaussianPDFReal, gaussianPDFReal]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * (v : ℝ))
    nlinarith [sq_nonneg (y - h), sq_nonneg (y + h)]
  have hg : 0 ≤ g y := by simpa [g] using lgTanh_mul_sechSq_nonneg hy0
  have hodd : g (-y) = -g y := by simpa [g] using lgTanh_mul_sechSq_odd y
  rw [hodd]
  calc
    gaussianPDFReal h v y * g y + gaussianPDFReal h v (-y) * -g y =
        (gaussianPDFReal h v y - gaussianPDFReal h v (-y)) * g y := by ring
    _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hp) hg

private lemma latalaGuerraRatio_deriv_neg {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    deriv (latalaGuerraRatio h) x < 0 := by
  have hnum := latalaGuerraNumerator_hasDerivAt (h := h) hx
  have hratio := hnum.div (hasDerivAt_id x) hx.ne'
  have hcore := integral_lgCore_affine_neg hh hx
  have hodd := integral_tanh_mul_sechSq_affine_nonneg hh.le hx
  have hsqrt : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hgInt : Integrable (fun z => Real.tanh (h + Real.sqrt x * z) *
      lgSech (h + Real.sqrt x * z) ^ 2) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact ((lgContinuous_tanh.mul
        (lgContinuous_sech.pow 2)).comp
          (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact lgTanh_mul_sechSq_abs_le_one _
  have hzInt : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
      simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
    apply Integrable.mono' habs continuous_id.aestronglyMeasurable
    filter_upwards [] with z
    simp [Real.norm_eq_abs]
  have hderivInt : Integrable (fun z =>
      (Real.tanh (h + Real.sqrt x * z) *
        lgSech (h + Real.sqrt x * z) ^ 2) * z / Real.sqrt x)
      (gaussianReal 0 1) := by
    have habs : Integrable (fun z : ℝ => |z| / Real.sqrt x)
        (gaussianReal 0 1) := by
      have : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
        simpa using integrable_abs_pow_gaussianReal_centered (1 : ℝ≥0) 1
      exact this.div_const _
    apply Integrable.mono' habs
    · exact (((lgContinuous_tanh.mul (lgContinuous_sech.pow 2)).comp
        (by fun_prop)).mul continuous_id).div_const _ |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.2 hx)]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (abs_nonneg z)
          (lgTanh_mul_sechSq_abs_le_one _)) (Real.sqrt_nonneg x)
  have htanhSqInt : Integrable (fun z =>
      Real.tanh (h + Real.sqrt x * z) ^ 2) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (lgContinuous_tanh_sq.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs]
      exact lgTanh_sq_abs_le_one _
  have hrearrange :
      x * (∫ z, (Real.tanh (h + Real.sqrt x * z) *
          lgSech (h + Real.sqrt x * z) ^ 2) * z / Real.sqrt x
        ∂gaussianReal 0 1) - latalaGuerraNumerator h x =
      (∫ z, lgCore (h + Real.sqrt x * z) ∂gaussianReal 0 1) -
        h * (∫ z, Real.tanh (h + Real.sqrt x * z) *
          lgSech (h + Real.sqrt x * z) ^ 2 ∂gaussianReal 0 1) := by
    unfold latalaGuerraNumerator
    rw [← integral_const_mul]
    rw [← integral_sub (hderivInt.const_mul x) htanhSqInt]
    rw [← integral_const_mul]
    rw [← integral_sub (integrable_lgCore_affine h x)
      (hgInt.const_mul h)]
    apply integral_congr_ae
    filter_upwards [] with z
    unfold lgCore
    nth_rw 1 [show x = Real.sqrt x * Real.sqrt x by
      rw [mul_self_sqrt hx.le]]
    field_simp [hsqrt]
    ring
  change deriv (latalaGuerraNumerator h / id) x < 0
  rw [hratio.deriv]
  simp only [id_eq, mul_one]
  rw [mul_comm _ x, hrearrange]
  have hnegative :
      (∫ z, lgCore (h + Real.sqrt x * z) ∂gaussianReal 0 1) -
        h * (∫ z, Real.tanh (h + Real.sqrt x * z) *
          lgSech (h + Real.sqrt x * z) ^ 2 ∂gaussianReal 0 1) < 0 := by
    nlinarith [mul_nonneg hh.le hodd]
  exact div_neg_of_neg_of_pos hnegative (sq_pos_of_pos hx)

/-- Latała--Guerra monotonicity: for a positive external field, the Gaussian
`tanh²` expectation divided by its variance is strictly decreasing. -/
theorem latalaGuerraRatio_strictAnti {h : ℝ} (hh : 0 < h) :
    StrictAntiOn (latalaGuerraRatio h) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact ((latalaGuerraNumerator_hasDerivAt (h := h) hx).div
      (hasDerivAt_id x) hx.ne').continuousAt.continuousWithinAt
  · intro x hx
    exact latalaGuerraRatio_deriv_neg hh (by simpa using hx)

end SpinGlass.AT
