module

public import Paper.ParisiMixTerminalDifferentiation

@[expose] public section

/-! # Exponential weights for the actual Gaussian Volterra linearization

The square-root time kernel becomes arbitrarily small after multiplication
by a backward exponential weight. All estimates concern actual interval
integrals and the actual polarized Gaussian Duhamel operator.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

namespace Paper

set_option maxHeartbeats 2000000

noncomputable def parisiDecayWeight (ell t s : ℝ) : ℝ := Real.exp (-ell * max (s - t) 0)

theorem parisiDecayWeight_nonneg (ell t s : ℝ) : 0 ≤ parisiDecayWeight ell t s :=
  (Real.exp_pos _).le

theorem parisiDecayWeight_le_one (ell : ℝ) (hell : 0 ≤ ell) (t s : ℝ) :
    parisiDecayWeight ell t s ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell) (le_max_right _ _)

theorem parisiDecayWeight_intervalIntegrable (ell t a b : ℝ) :
    IntervalIntegrable (parisiDecayWeight ell t) volume a b :=
  (show Continuous (parisiDecayWeight ell t) by unfold parisiDecayWeight; fun_prop).intervalIntegrable _ _

theorem integral_parisiDecayWeight_le_inv (ell : ℝ) (hell : 0 < ell)
    (t b : ℝ) (htb : t ≤ b) :
    (∫ s in t..b, parisiDecayWeight ell t s) ≤ ell⁻¹ := by
  have hi : IntervalIntegrable (fun s => Real.exp (-ell * (s - t))) volume t b :=
    (show Continuous (fun s : ℝ => Real.exp (-ell * (s - t))) by fun_prop).intervalIntegrable _ _
  have hd : ∀ s ∈ uIcc t b,
      HasDerivAt (fun y => -ell⁻¹ * Real.exp (-ell * (y - t))) (Real.exp (-ell * (s - t))) s := by
    intro s _
    convert! ((((hasDerivAt_id s).sub_const t).const_mul (-ell)).exp).const_mul (-ell⁻¹) using 1
    simp only [id_eq]
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hcongr : (∫ s in t..b, parisiDecayWeight ell t s) =
      ∫ s in t..b, Real.exp (-ell * (s - t)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    rw [uIoo_of_le htb] at hs
    simp only [parisiDecayWeight, max_eq_left (sub_nonneg.mpr hs.1.le)]
  rw [hcongr, he]
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
  have hp := Real.exp_pos (-ell * (b - t))
  have hn : 0 ≤ ell⁻¹ := inv_nonneg.mpr hell.le
  nlinarith

/-- The exponentially weighted square-root kernel tends to zero with its explicit rate. -/
theorem integral_parisiDecayWeight_inv_sqrt_le (ell : ℝ) (hell : 0 < ell)
    (t b : ℝ) (htb : t ≤ b) :
    (∫ s in t..b, parisiDecayWeight ell t s * (Real.sqrt (s - t))⁻¹) ≤
      3 * Real.sqrt ell⁻¹ := by
  have h := integral_bdd_mul_inv_sqrt_sub_le (parisiDecayWeight ell t)
    (show Measurable (parisiDecayWeight ell t) by unfold parisiDecayWeight; fun_prop)
    (parisiDecayWeight_nonneg ell t) (parisiDecayWeight_le_one ell hell.le t)
    t b ell⁻¹ htb (inv_pos.mpr hell)
  have hi := integral_parisiDecayWeight_le_inv ell hell t b htb
  have hs : (Real.sqrt ell⁻¹) ^ 2 = ell⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hell.le)
  have hsne : Real.sqrt ell⁻¹ ≠ 0 := (Real.sqrt_pos.mpr (inv_pos.mpr hell)).ne'
  have hc : ell⁻¹ * (Real.sqrt ell⁻¹)⁻¹ = Real.sqrt ell⁻¹ := by
    conv_lhs => lhs; rw [← hs]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hsne, mul_one]
  have hp := mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr (Real.sqrt_nonneg ell⁻¹))
  rw [hc] at hp
  linarith

noncomputable def parisiTimeWeight (ell : ℝ) : ParisiSlabGradient 0 1 :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => Real.exp (ell * p.1))
    (by fun_prop) (Real.exp |ell|) (fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        ell * (p.1 : ℝ) ≤ |ell| * (p.1 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self ell) p.1.property.1
        _ ≤ |ell| := by simpa using mul_le_mul_of_nonneg_left p.1.property.2 (abs_nonneg ell))

@[simp] theorem parisiTimeWeight_apply (ell : ℝ) (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiTimeWeight ell p = Real.exp (ell * p.1) := rfl

theorem norm_parisiTimeWeight_le (ell : ℝ) : ‖parisiTimeWeight ell‖ ≤ Real.exp |ell| :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (Real.exp_pos _).le _

noncomputable def parisiTimeWeightOperator (ell : ℝ) :
    ParisiSlabGradient 0 1 →L[ℝ] ParisiSlabGradient 0 1 :=
  LinearMap.mkContinuous
    { toFun := fun v => parisiTimeWeight ell * v
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun c v => mul_smul_comm c _ v }
    (Real.exp |ell|) (fun v => (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_parisiTimeWeight_le ell) (norm_nonneg v)))

@[simp] theorem parisiTimeWeightOperator_apply (ell : ℝ) (v : ParisiSlabGradient 0 1)
    (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiTimeWeightOperator ell v p = Real.exp (ell * p.1) * v p := rfl

theorem parisiTimeWeightOperator_neg_cancel (ell : ℝ) (v : ParisiSlabGradient 0 1) :
    parisiTimeWeightOperator ell (parisiTimeWeightOperator (-ell) v) = v := by
  ext p
  simp only [parisiTimeWeightOperator_apply]
  rw [← mul_assoc, ← Real.exp_add]
  simp

noncomputable def parisiWeightedLinearizedOperator (ell β : ℝ) (μ : ParisiMeasure)
    (v : ParisiSlabGradient 0 1) : ParisiSlabGradient 0 1 →L[ℝ] ParisiSlabGradient 0 1 :=
  (parisiTimeWeightOperator ell).comp
    ((parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v).comp
      (parisiTimeWeightOperator (-ell)))

private theorem norm_parisiWeightedLinearSource_le (ell β : ℝ) (μ : ParisiMeasure)
    (v w : ParisiSlabGradient 0 1) (hv : ‖v‖ ≤ 1) (t x s : ℝ)
    (ht : 0 ≤ t) (hs : s ∈ Icc t 1) :
    ‖β ^ 2 * Real.exp (ell * t) *
      parisiLinearGradientSource β μ
        (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
          (v * parisiTimeWeightOperator (-ell) w)) t x s‖ ≤
      (|β| * gaussianAbsMoment * ‖w‖) *
        (parisiDecayWeight ell t s * (Real.sqrt (s - t))⁻¹) := by
  by_cases hβ : β = 0
  · subst β
    simp
  have hs0 : s ∈ Icc (0 : ℝ) 1 := ⟨ht.trans hs.1, hs.2⟩
  have hf : ∀ y, ‖parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
      (v * parisiTimeWeightOperator (-ell) w) (s, y)‖ ≤ Real.exp (-ell * s) * ‖w‖ := by
    intro y
    unfold parisiSlabExtend
    rw [projIcc_of_mem _ hs0]
    change ‖v (⟨s, hs0⟩, y) * (parisiTimeWeightOperator (-ell) w (⟨s, hs0⟩, y))‖ ≤ _
    rw [parisiTimeWeightOperator_apply, norm_mul, norm_mul]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hvp := (v.norm_coe_le_norm (⟨s, hs0⟩, y)).trans hv
    have hwp := w.norm_coe_le_norm (⟨s, hs0⟩, y)
    calc
      _ ≤ 1 * (Real.exp (-ell * s) * ‖w‖) :=
        mul_le_mul hvp (mul_le_mul_of_nonneg_left hwp (Real.exp_pos _).le)
          (by positivity) (by norm_num)
      _ = _ := one_mul _
  have hg := norm_heatGradient_le (β ^ 2 * (s - t))
    (fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
      (v * parisiTimeWeightOperator (-ell) w) (s, y)) (Real.exp (-ell * s) * ‖w‖) hf x
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  have hsource := mul_le_mul hm hg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hexp : Real.exp (ell * t) * Real.exp (-ell * s) = Real.exp (-ell * (s - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg β),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold parisiLinearGradientSource
  rw [norm_mul]
  calc
    _ ≤ β ^ 2 * Real.exp (ell * t) *
        (1 * ((Real.sqrt (β ^ 2 * (s - t)))⁻¹ * gaussianAbsMoment *
          (Real.exp (-ell * s) * ‖w‖))) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (β ^ 2 * |β|⁻¹) * gaussianAbsMoment * ‖w‖ *
        (Real.exp (ell * t) * Real.exp (-ell * s)) * (Real.sqrt (s - t))⁻¹ := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
      ring
    _ = (|β| * gaussianAbsMoment * ‖w‖) *
        (parisiDecayWeight ell t s * (Real.sqrt (s - t))⁻¹) := by
      rw [hexp, ← sq_abs β]
      unfold parisiDecayWeight
      rw [max_eq_left (sub_nonneg.mpr hs.1)]
      have ha : |β| ≠ 0 := abs_ne_zero.mpr hβ
      field_simp

/-- The actual globally weighted Gaussian linearization has an arbitrarily small norm. -/
theorem norm_parisiWeightedLinearizedOperator_apply_le (ell β : ℝ) (μ : ParisiMeasure)
    (hell : 0 < ell) (v w : ParisiSlabGradient 0 1) (hv : ‖v‖ ≤ 1) :
    ‖parisiWeightedLinearizedOperator ell β μ v w‖ ≤
      (3 * |β| * gaussianAbsMoment * Real.sqrt ell⁻¹) * ‖w‖ := by
  have hc : 0 ≤ |β| * gaussianAbsMoment * ‖w‖ := by
    have := gaussianAbsMoment_nonneg
    positivity
  apply (BoundedContinuousFunction.norm_le (by
    have := gaussianAbsMoment_nonneg
    positivity)).mpr
  intro p
  change ‖Real.exp (ell * p.1) * ((2 : ℝ) *
    parisiSlabLinearValue β μ (by norm_num : (0 : ℝ) ≤ 1)
      (v * parisiTimeWeightOperator (-ell) w) p)‖ ≤ _
  rw [parisiSlabLinearValue_apply_physical]
  have he : Real.exp (ell * (p.1 : ℝ)) * ((2 : ℝ) * (β ^ 2 / 2 *
      ∫ s in (p.1 : ℝ)..1, parisiLinearGradientSource β μ
        (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
          (v * parisiTimeWeightOperator (-ell) w)) p.1 p.2 s)) =
      ∫ s in (p.1 : ℝ)..1, β ^ 2 * Real.exp (ell * p.1) *
        parisiLinearGradientSource β μ
          (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
            (v * parisiTimeWeightOperator (-ell) w)) p.1 p.2 s := by
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [he]
  have hi := intervalIntegrable_bdd_mul_inv_sqrt_sub (parisiDecayWeight ell p.1)
    (show Measurable (parisiDecayWeight ell p.1) by unfold parisiDecayWeight; fun_prop)
    (parisiDecayWeight_nonneg ell p.1) (parisiDecayWeight_le_one ell hell.le p.1)
    p.1 1 p.1.property.2
  have hn := intervalIntegral.norm_integral_le_of_norm_le p.1.property.2
    (.of_forall fun s hs => norm_parisiWeightedLinearSource_le ell β μ v w hv p.1 p.2 s
      p.1.property.1 ⟨hs.1.le, hs.2⟩) (hi.const_mul (|β| * gaussianAbsMoment * ‖w‖))
  conv_rhs at hn => rw [intervalIntegral.integral_const_mul]
  have hk := integral_parisiDecayWeight_inv_sqrt_le ell hell p.1 1 p.1.property.2
  exact hn.trans ((mul_le_mul_of_nonneg_left hk hc).trans_eq (by ring))

theorem parisiTimeWeightOperator_isInvertible (ell : ℝ) :
    (parisiTimeWeightOperator ell).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := parisiTimeWeightOperator (-ell))
  · apply ContinuousLinearMap.ext
    intro v
    exact parisiTimeWeightOperator_neg_cancel ell v
  · apply ContinuousLinearMap.ext
    intro v
    change parisiTimeWeightOperator (-ell) (parisiTimeWeightOperator ell v) = v
    simpa only [neg_neg] using parisiTimeWeightOperator_neg_cancel (-ell) v

/-- The genuine global Gaussian Volterra linearization has an invertible residual,
for every inverse temperature and every bounded coefficient gradient. -/
theorem parisiSlabLinearizedOperator_residual_isInvertible (β : ℝ) (μ : ParisiMeasure)
    (v : ParisiSlabGradient 0 1) (hv : ‖v‖ ≤ 1) :
    (1 - parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v).IsInvertible := by
  let c := |β| * gaussianAbsMoment
  have hc : 0 ≤ c := mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  have hlim : Tendsto (fun ell : ℝ => 3 * c * Real.sqrt ell⁻¹) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun ell : ℝ => ell⁻¹) atTop (𝓝 0)).sqrt.const_mul (3 * c)
  obtain ⟨ell, hell, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))).exists
  let W := parisiWeightedLinearizedOperator ell β μ v
  have hnorm : ‖W‖ ≤ 3 * c * Real.sqrt ell⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound W (by positivity)
    intro w
    simpa only [W, c, mul_assoc] using norm_parisiWeightedLinearizedOperator_apply_le ell β μ hell v w hv
  have hinv : (1 - W).IsInvertible := one_sub_clm_isInvertible W (hnorm.trans_lt hsmall)
  have hcomp := ((parisiTimeWeightOperator_isInvertible (-ell)).comp hinv).comp
    (parisiTimeWeightOperator_isInvertible ell)
  have heq : ((parisiTimeWeightOperator (-ell)).comp (1 - W)).comp
      (parisiTimeWeightOperator ell) =
      1 - parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v := by
    ext w
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      one_apply_eq_self, map_sub]
    dsimp only [W, parisiWeightedLinearizedOperator]
    simp only [ContinuousLinearMap.comp_apply]
    rw [show parisiTimeWeightOperator (-ell) (parisiTimeWeightOperator ell w) = w by
      simpa only [neg_neg] using parisiTimeWeightOperator_neg_cancel (-ell) w]
    rw [show parisiTimeWeightOperator (-ell)
        (parisiTimeWeightOperator ell
          (parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v w)) =
        parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v w by
      simpa only [neg_neg] using parisiTimeWeightOperator_neg_cancel (-ell)
        (parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1) v w)]
  exact heq ▸ hcomp

private theorem symmetric_bilinear_linearization_eq {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B : X →L[𝕜] X →L[𝕜] X) (hB : ∀ v w, B v w = B w v) (v : X) :
    B v + B.flip v = (2 : 𝕜) • B v := by
  apply ContinuousLinearMap.ext
  intro w
  change B v w + B w v = (2 : 𝕜) • B v w
  rw [hB w v, two_smul 𝕜]

/-- The same actual global inverse in the symmetric-bilinear API used by the Banach IFT. -/
theorem parisiSlabBilinearOperator_global_residual_isInvertible (β : ℝ) (μ : ParisiMeasure)
    (v : ParisiSlabGradient 0 1) (hv : ‖v‖ ≤ 1) :
    quadraticLinearizationIsInvertible
      (parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1)) v := by
  unfold quadraticLinearizationIsInvertible
  have heq := symmetric_bilinear_linearization_eq
    (parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1))
    (parisiSlabBilinearOperator_symm β μ (by norm_num : (0 : ℝ) ≤ 1)) v
  rw [heq]
  exact parisiSlabLinearizedOperator_residual_isInvertible β μ v hv

end Paper



