module

public import Paper.ParisiLocal
public import Paper.JTVariational

@[expose] public section

/-!
# Stability of the actual Parisi Duhamel map under measure variation

Every estimate below concerns the genuine Gaussian integral operator and the
CDFs of probability measures on `[0,1]`. In particular, a probability mixing
variation changes the operator by at most its mixing parameter. The local
bounded-gradient fixed points inherit a proved quantitative measure estimate.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction Topology

namespace Paper

/-- Two actual probability CDFs differ by at most one. -/
theorem norm_parisiCDF_sub_le_one (μ ν : ParisiMeasure) (s : ℝ) :
    ‖parisiCDF μ s - parisiCDF ν s‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [parisiCDF_nonneg μ s, parisiCDF_nonneg ν s,
    parisiCDF_le_one μ s, parisiCDF_le_one ν s]

/-- The actual probability-mixing variation has a uniform CDF error at most `t`. -/
theorem norm_parisiCDF_mix_sub_le (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    ‖parisiCDF (parisiMix μ ν t) s - parisiCDF μ s‖ ≤ t := by
  rw [parisiCDF_mix μ ν t s ht,
    show (1 - t) * parisiCDF μ s + t * parisiCDF ν s - parisiCDF μ s =
      t * (parisiCDF ν s - parisiCDF μ s) by ring, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_left (norm_parisiCDF_sub_le_one ν μ s) ht.1).trans_eq
    (mul_one t)

theorem norm_parisiHeatSource_measure_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R D : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) (t x s : ℝ) :
    ‖parisiHeatSource β μ v t x s - parisiHeatSource β ν v t x s‖ ≤ D * R ^ 2 := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  have hDp : 0 ≤ D := (norm_nonneg _).trans (hD s)
  unfold parisiHeatSource
  rw [← sub_mul, norm_mul]
  exact mul_le_mul (hD s) (norm_heatSemigroup_le _ _ _ hsq _) (norm_nonneg _) hDp

/-- The nonlinear potential correction is quantitatively stable in the measure CDF. -/
theorem norm_parisiDuhamelCorrection_measure_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R D : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiDuhamelCorrection β μ v b t x - parisiDuhamelCorrection β ν v b t x‖ ≤
      β ^ 2 / 2 * D * R ^ 2 * (b - t) := by
  have hi := parisiHeatSource_intervalIntegrable β μ v hv R hb t x t b
  have hj := parisiHeatSource_intervalIntegrable β ν v hv R hb t x t b
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := b) (fun s _ => norm_parisiHeatSource_measure_sub_le β μ ν v R D hb hD t x s)
  rw [abs_of_nonneg (sub_nonneg.mpr htb)] at h
  unfold parisiDuhamelCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem norm_parisiGradientSource_measure_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R D : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) (t x s : ℝ) :
    ‖parisiGradientSource β μ v t x s - parisiGradientSource β ν v t x s‖ ≤
      (D * |β|⁻¹ * gaussianAbsMoment * R ^ 2) * (Real.sqrt (s - t))⁻¹ := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  have hDp : 0 ≤ D := (norm_nonneg _).trans (hD s)
  unfold parisiGradientSource
  rw [← sub_mul, norm_mul]
  calc
    _ ≤ D * ((Real.sqrt (β ^ 2 * (s - t)))⁻¹ * gaussianAbsMoment * R ^ 2) :=
      mul_le_mul (hD s) (norm_heatGradient_le _ _ _ hsq _) (norm_nonneg _) hDp
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
      ring

/-- The actual Gaussian gradient correction is stable even at its integrable
square-root time singularity. -/
theorem norm_parisiGradientCorrection_measure_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R D : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiGradientCorrection β μ v b t x - parisiGradientCorrection β ν v b t x‖ ≤
      |β| * gaussianAbsMoment * R ^ 2 * D * Real.sqrt (b - t) := by
  have hi := parisiGradientSource_intervalIntegrable β μ v hv R hb t x b htb
  have hj := parisiGradientSource_intervalIntegrable β ν v hv R hb t x b htb
  have h := intervalIntegral.norm_integral_le_of_norm_le htb
    (Filter.Eventually.of_forall fun s _ =>
      norm_parisiGradientSource_measure_sub_le β μ ν v R D hb hD t x s)
    ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
      (D * |β|⁻¹ * gaussianAbsMoment * R ^ 2))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t b htb] at h
  unfold parisiGradientCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [← sq_abs β]
    field_simp

/-- Multiplication by a bounded measurable coefficient preserves the actual
integrable square-root time kernel. -/
theorem intervalIntegrable_bdd_mul_inv_sqrt_sub (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1) (t b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (fun s => f s * (Real.sqrt (s - t))⁻¹) volume t b := by
  apply (intervalIntegrable_inv_sqrt_sub t b htb).mono_fun'
  · exact (hf.mul (show Measurable (fun s : ℝ => (Real.sqrt (s - t))⁻¹) by fun_prop)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 s) (by positivity))]
    simpa using mul_le_mul_of_nonneg_right (hf1 s)
      (show 0 ≤ (Real.sqrt (s - t))⁻¹ by positivity)

/-- Splitting time near its square-root singularity gives an actual weighted
`L¹` estimate, uniform in the initial time. -/
theorem integral_bdd_mul_inv_sqrt_sub_le (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (t b ε : ℝ) (htb : t ≤ b) (hε : 0 < ε) :
    (∫ s in t..b, f s * (Real.sqrt (s - t))⁻¹) ≤
      2 * Real.sqrt ε + (∫ s in t..b, f s) * (Real.sqrt ε)⁻¹ := by
  have hfi (a c : ℝ) : IntervalIntegrable f volume a c := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ => (1 : ℝ)) volume a c).mono_fun'
    · exact hf.aestronglyMeasurable
    · filter_upwards with s
      simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 s)] using hf1 s
  have hw := intervalIntegrable_bdd_mul_inv_sqrt_sub f hf hf0 hf1 t b htb
  have hk := intervalIntegrable_inv_sqrt_sub t b htb
  have hfull0 : 0 ≤ (∫ s in t..b, f s) :=
    intervalIntegral.integral_nonneg_of_forall htb hf0
  by_cases hb : b ≤ t + ε
  · have hnear := intervalIntegral.integral_mono_on htb hw hk (fun s hs => by
      have hp : 0 ≤ (Real.sqrt (s - t))⁻¹ := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf1 s) hp)
    rw [integral_inv_sqrt_sub t b htb] at hnear
    have hs : Real.sqrt (b - t) ≤ Real.sqrt ε := Real.sqrt_le_sqrt (by linarith)
    have hp : 0 ≤ (∫ s in t..b, f s) * (Real.sqrt ε)⁻¹ := mul_nonneg hfull0 (by positivity)
    linarith
  · have hcb : t + ε ≤ b := (lt_of_not_ge hb).le
    have htc : t ≤ t + ε := by linarith
    have hwnear := intervalIntegrable_bdd_mul_inv_sqrt_sub f hf hf0 hf1 t (t + ε) htc
    have hknear := intervalIntegrable_inv_sqrt_sub t (t + ε) htc
    have hwfar := hw.mono_set (by
      rw [uIcc_of_le hcb, uIcc_of_le htb]
      exact Icc_subset_Icc htc le_rfl)
    have hnear := intervalIntegral.integral_mono_on htc hwnear hknear (fun s hs => by
      have hp : 0 ≤ (Real.sqrt (s - t))⁻¹ := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf1 s) hp)
    rw [integral_inv_sqrt_sub t (t + ε) htc, show t + ε - t = ε by ring] at hnear
    have hfar := intervalIntegral.integral_mono_on hcb hwfar
      ((hfi (t + ε) b).const_mul (Real.sqrt ε)⁻¹) (fun s hs => by
        have hse : ε ≤ s - t := by linarith [hs.1]
        have hsp : 0 < Real.sqrt (s - t) := Real.sqrt_pos.mpr (hε.trans_le hse)
        have hep : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
        have hinv : (Real.sqrt (s - t))⁻¹ ≤ (Real.sqrt ε)⁻¹ :=
          (inv_le_inv₀ hsp hep).mpr (Real.sqrt_le_sqrt hse)
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hinv (hf0 s))
    rw [intervalIntegral.integral_const_mul] at hfar
    have hpart := intervalIntegral.integral_mono_interval htc hcb le_rfl
      (Filter.Eventually.of_forall hf0) (hfi t b)
    have hscaled := mul_le_mul_of_nonneg_left hpart
      (show 0 ≤ (Real.sqrt ε)⁻¹ by positivity)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hwnear hwfar
    linarith

/-- The CDF difference has a genuine finite Lebesgue time integral. -/
theorem parisiCDF_difference_intervalIntegrable (μ ν : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (fun s => ‖parisiCDF μ s - parisiCDF ν s‖) volume a b :=
  ((parisiCDF_monotone μ).intervalIntegrable.sub
    (parisiCDF_monotone ν).intervalIntegrable).norm

/-- Weighted CDF convergence controls the singular Gaussian-gradient kernel.
The unweighted integral is over the fixed physical time interval `[0,1]`. -/
theorem integral_parisiCDF_difference_inv_sqrt_le (μ ν : ParisiMeasure)
    (t b ε : ℝ) (ht : 0 ≤ t) (htb : t ≤ b) (hb : b ≤ 1) (hε : 0 < ε) :
    (∫ s in t..b, ‖parisiCDF μ s - parisiCDF ν s‖ * (Real.sqrt (s - t))⁻¹) ≤
      2 * Real.sqrt ε +
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt ε)⁻¹ := by
  have hf : Measurable (fun s => ‖parisiCDF μ s - parisiCDF ν s‖) :=
    ((parisiCDF_measurable μ).sub (parisiCDF_measurable ν)).norm
  have hweighted := integral_bdd_mul_inv_sqrt_sub_le _ hf (fun s => norm_nonneg _)
    (norm_parisiCDF_sub_le_one μ ν) t b ε htb hε
  have hpart := intervalIntegral.integral_mono_interval ht htb hb
    (Filter.Eventually.of_forall (fun s => norm_nonneg (parisiCDF μ s - parisiCDF ν s)))
    (parisiCDF_difference_intervalIntegrable μ ν 0 1)
  have hscaled := mul_le_mul_of_nonneg_right hpart
    (show 0 ≤ (Real.sqrt ε)⁻¹ by positivity)
  linarith

/-- Pointwise CDF difference estimate for the actual gradient source. -/
theorem norm_parisiGradientSource_measure_pointwise_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (t x s : ℝ) :
    ‖parisiGradientSource β μ v t x s - parisiGradientSource β ν v t x s‖ ≤
      (|β|⁻¹ * gaussianAbsMoment * R ^ 2) *
        (‖parisiCDF μ s - parisiCDF ν s‖ * (Real.sqrt (s - t))⁻¹) := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  unfold parisiGradientSource
  rw [← sub_mul, norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_heatGradient_le _ _ _ hsq _)
    (norm_nonneg _)).trans_eq ?_
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
  ring

/-- Genuine `L¹` CDF convergence implies a uniform measure estimate for the
Gaussian gradient correction. The split parameter can be chosen independently
of the initial time. -/
theorem norm_parisiGradientCorrection_measure_L1_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R)
    (b t x ε : ℝ) (ht : 0 ≤ t) (htb : t ≤ b) (hb : b ≤ 1) (hε : 0 < ε) :
    ‖parisiGradientCorrection β μ v b t x - parisiGradientCorrection β ν v b t x‖ ≤
      |β| * gaussianAbsMoment * R ^ 2 / 2 *
        (2 * Real.sqrt ε +
          (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt ε)⁻¹) := by
  have hi := parisiGradientSource_intervalIntegrable β μ v hv R hvb t x b htb
  have hj := parisiGradientSource_intervalIntegrable β ν v hv R hvb t x b htb
  have hcf : Measurable (fun s => ‖parisiCDF μ s - parisiCDF ν s‖) :=
    ((parisiCDF_measurable μ).sub (parisiCDF_measurable ν)).norm
  have hci := intervalIntegrable_bdd_mul_inv_sqrt_sub _ hcf
    (fun s => norm_nonneg _) (norm_parisiCDF_sub_le_one μ ν) t b htb
  have h := intervalIntegral.norm_integral_le_of_norm_le htb
    (Filter.Eventually.of_forall fun s _ =>
      norm_parisiGradientSource_measure_pointwise_le β μ ν v R hvb t x s)
    (hci.const_mul (|β|⁻¹ * gaussianAbsMoment * R ^ 2))
  rw [intervalIntegral.integral_const_mul] at h
  have hweighted := integral_parisiCDF_difference_inv_sqrt_le μ ν t b ε ht htb hb hε
  have hp : 0 ≤ |β|⁻¹ * gaussianAbsMoment * R ^ 2 := by
    have := gaussianAbsMoment_nonneg
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hweighted hp
  unfold parisiGradientCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  refine (mul_le_mul_of_nonneg_left (h.trans hscaled) (by positivity)).trans_eq ?_
  by_cases hβ : β = 0
  · simp [hβ]
  · rw [← sq_abs β]
    field_simp

/-- The local bounded-continuous operator inherits the uniform weighted `L¹`
CDF estimate, with no regularity assumptions on the probability measures. -/
theorem norm_parisiSlabGradientOperator_measure_L1_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) (ε : ℝ) (hε : 0 < ε) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb v -
      parisiSlabGradientOperator β ν hab g hg hgb v‖ ≤
      |β| * gaussianAbsMoment * ‖v‖ ^ 2 / 2 *
        (2 * Real.sqrt ε +
          (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt ε)⁻¹) := by
  have hcdf0 : 0 ≤ (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun s => norm_nonneg _)
  apply (BoundedContinuousFunction.norm_le (by
    have := gaussianAbsMoment_nonneg
    positivity)).mpr
  intro p
  change ‖parisiSlabGradientValue β μ hab g v p -
    parisiSlabGradientValue β ν hab g v p‖ ≤ _
  unfold parisiSlabGradientValue
  rw [add_sub_add_left_eq_sub,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2,
    parisiNormalizedGradientCorrection_eq β ν _ b p.1 p.2 p.1.property.2]
  exact norm_parisiGradientCorrection_measure_L1_sub_le β μ ν (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v).measurable ‖v‖ (norm_parisiSlabExtend_le hab v)
    b p.1 p.2 ε (ha.trans p.1.property.1) p.1.property.2 hb hε

/-- The genuine local bounded-gradient fixed points inherit quantitative
stability from the measure-dependent operator and the proved contraction. -/
theorem localParisiGradient_measure_L1_stability (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v w : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hwnorm : ‖w‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hw : parisiSlabGradientOperator β ν hab g hg hgb w = w)
    (ε : ℝ) (hε : 0 < ε) :
    ‖v - w‖ ≤ 4 * |β| * gaussianAbsMoment *
      (2 * Real.sqrt ε +
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt ε)⁻¹) := by
  let B := 2 * Real.sqrt ε +
    (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt ε)⁻¹
  let J := |β| * gaussianAbsMoment * B
  have hcdf0 : 0 ≤ (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun s => norm_nonneg _)
  have hJ : 0 ≤ J := by
    dsimp [J, B]
    have := gaussianAbsMoment_nonneg
    positivity
  have hwpow : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
  have hm : ‖parisiSlabGradientOperator β μ hab g hg hgb w -
      parisiSlabGradientOperator β ν hab g hg hgb w‖ ≤ 2 * J := by
    calc
      _ ≤ |β| * gaussianAbsMoment * ‖w‖ ^ 2 / 2 * B :=
        norm_parisiSlabGradientOperator_measure_L1_sub_le β μ ν hab ha hb g hg hgb w ε hε
      _ = J / 2 * ‖w‖ ^ 2 := by dsimp [J]; ring
      _ ≤ J / 2 * 4 := mul_le_mul_of_nonneg_left hwpow (by positivity)
      _ = 2 * J := by ring
  have hd : ‖v - w‖ ≤ 4 * parisiSlabContractionConstant β a b * ‖v - w‖ + 2 * J := by
    calc
      _ = ‖parisiSlabGradientOperator β μ hab g hg hgb v -
          parisiSlabGradientOperator β ν hab g hg hgb w‖ := by rw [hv, hw]
      _ ≤ ‖parisiSlabGradientOperator β μ hab g hg hgb v -
          parisiSlabGradientOperator β μ hab g hg hgb w‖ +
          ‖parisiSlabGradientOperator β μ hab g hg hgb w -
            parisiSlabGradientOperator β ν hab g hg hgb w‖ := by
        rw [show parisiSlabGradientOperator β μ hab g hg hgb v -
            parisiSlabGradientOperator β ν hab g hg hgb w =
          (parisiSlabGradientOperator β μ hab g hg hgb v -
            parisiSlabGradientOperator β μ hab g hg hgb w) +
          (parisiSlabGradientOperator β μ hab g hg hgb w -
            parisiSlabGradientOperator β ν hab g hg hgb w) by abel]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add
        (norm_parisiSlabGradientOperator_sub_le β μ hab g hg hgb v w hvnorm hwnorm) hm
  have hs := mul_le_mul_of_nonneg_right hshort (norm_nonneg (v - w))
  have hfinal : ‖v - w‖ ≤ 4 * J := by linarith
  simpa only [J, B, mul_assoc] using hfinal

/-- A CDF approximation with `L¹` error at most its mesh converges uniformly
at the concrete local bounded-gradient fixed points, at square-root rate. -/
theorem localParisiGradient_measure_mesh_stability (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v w : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hwnorm : ‖w‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hw : parisiSlabGradientOperator β ν hab g hg hgb w = w)
    (δ : ℝ) (hδ : 0 < δ)
    (hCDF : (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) ≤ δ) :
    ‖v - w‖ ≤ 12 * |β| * gaussianAbsMoment * Real.sqrt δ := by
  have hbase := localParisiGradient_measure_L1_stability β μ ν hab ha hb g hg hgb
    hshort v w hvnorm hwnorm hv hw δ hδ
  have hsqrt : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have heq : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
    conv_lhs => arg 1; rw [← Real.sq_sqrt hδ.le]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hsqrt, mul_one]
  have hscaled := mul_le_mul_of_nonneg_right hCDF
    (show 0 ≤ (Real.sqrt δ)⁻¹ by positivity)
  rw [heq] at hscaled
  have hcoeff : 0 ≤ 4 * |β| * gaussianAbsMoment := by
    have := gaussianAbsMoment_nonneg
    positivity
  have hup := mul_le_mul_of_nonneg_left
    (show 2 * Real.sqrt δ + (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) *
      (Real.sqrt δ)⁻¹ ≤ 3 * Real.sqrt δ by linarith) hcoeff
  exact (hbase.trans hup).trans_eq (by ring)

/-- Atomic solutions whose genuine CDF mesh tends to zero transfer the sharp
unit gradient bound to the unique actual local fixed point. -/
theorem localParisiGradient_norm_le_one_of_mesh_approximants (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (ν : ℕ → ParisiMeasure) (w : ℕ → ParisiSlabGradient a b)
    (hwunit : ∀ n, ‖w n‖ ≤ 1)
    (hw : ∀ n, parisiSlabGradientOperator β (ν n) hab g hg hgb (w n) = w n)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (hδzero : Tendsto δ atTop (𝓝 0))
    (hCDF : ∀ n, (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF (ν n) s‖) ≤ δ n) :
    ‖v‖ ≤ 1 := by
  have herr : Tendsto (fun n => 12 * |β| * gaussianAbsMoment * Real.sqrt (δ n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds.mul hδzero.sqrt)
  have hlim : Tendsto (fun n => 1 + 12 * |β| * gaussianAbsMoment * Real.sqrt (δ n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖v‖ ≤ 1 + 12 * |β| * gaussianAbsMoment * Real.sqrt (δ n) :=
    Filter.Eventually.of_forall fun n => by
      have hdist := localParisiGradient_measure_mesh_stability β μ (ν n) hab ha hb g hg hgb
        hshort v (w n) hvnorm ((hwunit n).trans (by norm_num)) hv (hw n) (δ n) (hδpos n) (hCDF n)
      have htriangle := norm_add_le (v - w n) (w n)
      rw [sub_add_cancel] at htriangle
      linarith [hwunit n]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- Uniform CDF error gives the sharper linear local operator estimate. -/
theorem norm_parisiSlabGradientOperator_measure_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) (D : ℝ)
    (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb v -
      parisiSlabGradientOperator β ν hab g hg hgb v‖ ≤
      parisiSlabContractionConstant β a b * ‖v‖ ^ 2 * D := by
  have hDp : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  apply (BoundedContinuousFunction.norm_le (by
    have := parisiSlabContractionConstant_nonneg β a b
    positivity)).mpr
  intro p
  change ‖parisiSlabGradientValue β μ hab g v p -
    parisiSlabGradientValue β ν hab g v p‖ ≤ _
  unfold parisiSlabGradientValue
  rw [add_sub_add_left_eq_sub,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2,
    parisiNormalizedGradientCorrection_eq β ν _ b p.1 p.2 p.1.property.2]
  have hc := norm_parisiGradientCorrection_measure_sub_le β μ ν (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v).measurable ‖v‖ D (norm_parisiSlabExtend_le hab v)
    hD b p.1 p.2 p.1.property.2
  have hs : Real.sqrt (b - (p.1 : ℝ)) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (sub_le_sub_left p.1.property.1 b)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ |β| * gaussianAbsMoment * ‖v‖ ^ 2 * D by
      have := gaussianAbsMoment_nonneg
      positivity)
  exact (hc.trans hm).trans_eq (by unfold parisiSlabContractionConstant; ring)

/-- Uniform CDF perturbations give linear stability of the actual local fixed points. -/
theorem localParisiGradient_measure_stability (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v w : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hwnorm : ‖w‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hw : parisiSlabGradientOperator β ν hab g hg hgb w = w)
    (D : ℝ) (hD : ∀ s, ‖parisiCDF μ s - parisiCDF ν s‖ ≤ D) :
    ‖v - w‖ ≤ 8 * parisiSlabContractionConstant β a b * D := by
  let C := parisiSlabContractionConstant β a b
  have hC : 0 ≤ C := parisiSlabContractionConstant_nonneg β a b
  have hDp : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hwpow : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
  have hm : ‖parisiSlabGradientOperator β μ hab g hg hgb w -
      parisiSlabGradientOperator β ν hab g hg hgb w‖ ≤ 4 * C * D := by
    calc
      _ ≤ C * ‖w‖ ^ 2 * D := norm_parisiSlabGradientOperator_measure_sub_le β μ ν hab g hg hgb w D hD
      _ = (C * D) * ‖w‖ ^ 2 := by ring
      _ ≤ (C * D) * 4 := mul_le_mul_of_nonneg_left hwpow (mul_nonneg hC hDp)
      _ = _ := by ring
  have hd : ‖v - w‖ ≤ 4 * C * ‖v - w‖ + 4 * C * D := by
    calc
      _ = ‖parisiSlabGradientOperator β μ hab g hg hgb v -
          parisiSlabGradientOperator β ν hab g hg hgb w‖ := by rw [hv, hw]
      _ ≤ ‖parisiSlabGradientOperator β μ hab g hg hgb v -
          parisiSlabGradientOperator β μ hab g hg hgb w‖ +
          ‖parisiSlabGradientOperator β μ hab g hg hgb w -
            parisiSlabGradientOperator β ν hab g hg hgb w‖ := by
        rw [show parisiSlabGradientOperator β μ hab g hg hgb v -
            parisiSlabGradientOperator β ν hab g hg hgb w =
          (parisiSlabGradientOperator β μ hab g hg hgb v -
            parisiSlabGradientOperator β μ hab g hg hgb w) +
          (parisiSlabGradientOperator β μ hab g hg hgb w -
            parisiSlabGradientOperator β ν hab g hg hgb w) by abel]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add
        (norm_parisiSlabGradientOperator_sub_le β μ hab g hg hgb v w hvnorm hwnorm) hm
  have hs := mul_le_mul_of_nonneg_right hshort (norm_nonneg (v - w))
  change ‖v - w‖ ≤ 8 * C * D
  linarith

/-- The actual local gradient responds linearly to a genuine probability mixing path. -/
theorem localParisiGradient_mix_stability (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v w : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hwnorm : ‖w‖ ≤ 2)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hw : parisiSlabGradientOperator β (parisiMix μ ν t) hab g hg hgb w = w) :
    ‖v - w‖ ≤ 8 * parisiSlabContractionConstant β a b * t := by
  apply localParisiGradient_measure_stability β μ (parisiMix μ ν t) hab g hg hgb
    hshort v w hvnorm hwnorm hv hw t
  intro s
  rw [norm_sub_rev]
  exact norm_parisiCDF_mix_sub_le μ ν t ht s

end Paper
