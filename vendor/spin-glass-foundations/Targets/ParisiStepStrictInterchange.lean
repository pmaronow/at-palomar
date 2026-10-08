module

public import Targets.ParisiStepInterchange
public import Targets.ParisiStrictConvexity
public import Targets.ParisiStrictVariance
public import Targets.Section4SplitDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-!
# Strict Gaussian operator interchange

The small-variance commutator is differentiated at the genuine zero-variance
face. Its coefficient is a strictly positive tilted slope variance. The
semigroup and non-strict interchange then transport the strict inequality to
arbitrary positive variances. In particular, the lower mass may be zero.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem interchange_lipschitz {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (x y : ℝ) : |A x - A y| ≤ |x - y| := by
  simpa only [Real.norm_eq_abs, one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := A') (s := Set.univ) (C := 1)
      (fun t _ => (hC2.1 t).hasDerivWithinAt)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one t)
      convex_univ (Set.mem_univ y) (Set.mem_univ x)

private theorem interchange_family_growth {F : ℝ → ℝ → ℝ}
    (hLip : ∀ w x y, |F w x - F w y| ≤ |x - y|) (w : ℝ) :
    HasLinearGrowth (F w) := by
  refine ⟨|F w 0|, 1, abs_nonneg _, zero_le_one, fun x => ?_⟩
  have H := abs_sub_le (F w x) (F w 0) 0
  have H' := hLip w x 0
  simp only [sub_zero] at H H'
  linarith

private theorem interchange_family_envelope {F : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hLip : ∀ w x y, |F w x - F w y| ≤ |x - y|) (v b x : ℝ) :
    ∀ᶠ w in 𝓝 v, ∀ z,
      |F w (x + Real.sqrt b * z)| ≤ |F v 0| + 1 + |x| + Real.sqrt b * |z| := by
  have H : ∀ᶠ w in 𝓝 v, |F w 0| < |F v 0| + 1 :=
    ((hc.comp (continuous_id.prodMk continuous_const)).abs.continuousAt).eventually
      (Iio_mem_nhds (by dsimp; linarith))
  filter_upwards [H] with w hw z
  have H1 := hLip w (x + Real.sqrt b * z) 0
  have H2 := abs_sub_le (F w (x + Real.sqrt b * z)) (F w 0) 0
  have H3 := abs_add_le x (Real.sqrt b * z)
  simp only [sub_zero] at H1 H2
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at H3
  linarith

private theorem continuous_interchange_weighted_family {F G : ℝ → ℝ → ℝ}
    (hcF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    (hLip : ∀ w x y, |F w x - F w y| ≤ |x - y|)
    (hG : ∀ w y, |G w y| ≤ 1) (m b x : ℝ) :
    Continuous (fun w => ∫ z, G w (x + Real.sqrt b * z) *
      Real.exp (m * F w (x + Real.sqrt b * z)) ∂gaussianReal 0 1) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  let C := |F v 0| + 1 + |x|
  let D := Real.sqrt b
  let B := fun z : ℝ => Real.exp (|m| * C) * Real.exp ((|m| * D) * |z|)
  have hF (w : ℝ) : Continuous (fun z => F w (x + Real.sqrt b * z)) :=
    hcF.comp (continuous_const.prodMk (by fun_prop))
  have hG' (w : ℝ) : Continuous (fun z => G w (x + Real.sqrt b * z)) :=
    hcG.comp (continuous_const.prodMk (by fun_prop))
  apply continuousAt_of_dominated (bound := B)
  · exact Eventually.of_forall fun w => ((hG' w).mul
      (Real.continuous_exp.comp ((hF w).const_mul m))).measurable.aestronglyMeasurable
  · filter_upwards [interchange_family_envelope hcF hLip v b x] with w hw
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_of_le_one_left (Real.exp_pos _).le (hG w _)).trans ?_
      dsimp [B]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have H := le_abs_self (m * F w (x + Real.sqrt b * z))
      rw [abs_mul] at H
      have H' := mul_le_mul_of_nonneg_left (hw z) (abs_nonneg m)
      dsimp [C, D]
      nlinarith
  · exact (integrable_exp_abs_mul_stdGaussian (|m| * D)).const_mul _
  · exact Eventually.of_forall fun z =>
      (((hcG.comp (continuous_id.prodMk continuous_const)).mul
        (Real.continuous_exp.comp ((hcF.comp
          (continuous_id.prodMk continuous_const)).const_mul m))).continuousAt)

private theorem continuous_interchange_step_family {F : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hLip : ∀ w x y, |F w x - F w y| ≤ |x - y|) (m b x : ℝ) :
    Continuous (fun w => parisiStep m b (F w) x) := by
  have hFm (w : ℝ) : Measurable (F w) :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  by_cases hm : m = 0
  · subst m
    simp only [parisiStep, if_true]
    apply continuous_iff_continuousAt.mpr
    intro v
    apply continuousAt_of_dominated
      (bound := fun z : ℝ => |F v 0| + 1 + |x| + Real.sqrt b * |z|)
    · exact Eventually.of_forall fun w =>
        ((hFm w).comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [interchange_family_envelope hc hLip v b x] with w hw
      exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hw z
    · simpa only [Real.norm_eq_abs, id_eq, Pi.add_apply] using!
        (integrable_const _).add ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm.const_mul _)
    · exact Eventually.of_forall fun z =>
        (hc.comp (continuous_id.prodMk continuous_const)).continuousAt
  · have H := continuous_interchange_weighted_family hc (G := fun _ _ => 1)
      continuous_const hLip (by simp) m b x
    simp only [one_mul] at H
    have Hp (w : ℝ) : (∫ z, Real.exp (m * F w (x + Real.sqrt b * z)) ∂gaussianReal 0 1) ≠ 0 :=
      (smoothing_integral_pos (interchange_family_growth hLip w) (hFm w) x).ne'
    simpa only [parisiStep, if_neg hm] using (H.log Hp).const_mul (1 / m)

/-- The heat velocity of a scalar smoothing, defined without a variance
denominator and therefore meaningful at zero variance. -/
noncomputable def interchangeHeat (A A' A'' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  (stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2) / 2

private theorem interchangeHeat_continuous {A A' A'' : ℝ → ℝ}
    (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'') {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun p : ℝ × ℝ => interchangeHeat A A' A'' m p.1 p.2) := by
  have H := continuous_parisiStep_variance_spatial hC2 hc'' hm
  exact (H.2.2.add ((H.2.1.pow 2).const_mul m)).div_const 2

private theorem interchangeHeat_abs_le {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    |interchangeHeat A A' A'' m v x| ≤ 1 := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have H := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  unfold interchangeHeat
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hm.1, abs_pow, sq_abs]
  have Hsq := (sq_le_one_iff_abs_le_one _).mpr (H.abs_first_le_one x)
  nlinarith [H.abs_second_le_one x, mul_le_mul_of_nonneg_left Hsq hm.1, hm.2]

private theorem continuous_interchange_mean_family {F G : ℝ → ℝ → ℝ}
    (hcF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hcG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    (hLip : ∀ w x y, |F w x - F w y| ≤ |x - y|)
    (hG : ∀ w y, |G w y| ≤ 1) (m b x : ℝ) :
    Continuous (fun w => ∫ z, G w (x + Real.sqrt b * z) *
      tiltWeight m b (F w) x z ∂gaussianReal 0 1) := by
  have H := continuous_interchange_weighted_family hcF hcG hLip hG m b x
  have He := continuous_interchange_weighted_family hcF (G := fun _ _ => 1)
    continuous_const hLip (by simp) m b x
  simp only [one_mul] at He
  have Hp (w : ℝ) : (∫ z, Real.exp (m * F w (x + Real.sqrt b * z)) ∂gaussianReal 0 1) ≠ 0 :=
    (smoothing_integral_pos (interchange_family_growth hLip w)
      (hcF.comp (continuous_const.prodMk continuous_id)).measurable x).ne'
  have Hdiv := H.div He Hp
  change Continuous (fun w =>
    (∫ z, G w (x + Real.sqrt b * z) * Real.exp (m * F w (x + Real.sqrt b * z)) ∂gaussianReal 0 1) /
    (∫ z, Real.exp (m * F w (x + Real.sqrt b * z)) ∂gaussianReal 0 1)) at Hdiv
  by_cases hm : m = 0
  · simpa only [Pi.div_apply, hm, tiltWeight, if_true, zero_mul, Real.exp_zero, mul_one,
      integral_const, probReal_univ, smul_eq_mul, one_mul, div_one] using Hdiv
  · simpa only [Pi.div_apply, tiltWeight, if_neg hm, ← mul_div_assoc, integral_div] using Hdiv

/-- Differentiation of a fixed outer scalar transform through an actual
inner variance. This is a proved parameter chain rule, not a PDE premise. -/
theorem hasDerivAt_nested_parisiStep_variance {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (l b x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => parisiStep l b (parisiStep m w A) x)
      (∫ z, interchangeHeat A A' A'' m v (x + Real.sqrt b * z) *
        tiltWeight l b (parisiStep m v A) x z ∂gaussianReal 0 1) v := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hj := continuous_parisiStep_variance_spatial hC2 hc'' hm.1
  have hB2 (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  let K := Set.Icc (v / 2) (v + 1)
  have hvK : K ∈ 𝓝 v := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (show IsCompact K from isCompact_Icc).exists_bound_of_continuousOn
    (hj.1.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hb (w : ℝ) (hw : w ∈ K) (z : ℝ) :
      |parisiStep m w A (x + Real.sqrt b * z)| ≤ C + |x| + Real.sqrt b * |z| := by
    have H0 : |parisiStep m w A 0| ≤ C := by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using! hC w hw
    have H1 := interchange_lipschitz (hB2 w) (x + Real.sqrt b * z) 0
    have H2 := abs_sub_le (parisiStep m w A (x + Real.sqrt b * z)) (parisiStep m w A 0) 0
    have H3 := abs_add_le x (Real.sqrt b * z)
    simp only [sub_zero] at H1 H2
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at H3
    linarith
  have H := hasDerivAt_parisiStep_param_local (m := l)
    (F := fun w z => parisiStep m w A (x + Real.sqrt b * z))
    (F' := fun w z => interchangeHeat A A' A'' m w (x + Real.sqrt b * z))
    (C := C + |x|) (D := Real.sqrt b) (C' := 1) (D' := 0)
    hvK (Real.sqrt_nonneg b) le_rfl
    (fun w hw z => hasDerivAt_parisiStep_variance hA hC2 hc.measurable
      hc'.measurable hc''.measurable m _ (by have := hw.1; linarith))
    (fun w _ => (hj.1.comp (continuous_const.prodMk (by fun_prop))).measurable)
    (fun w _ => ((interchangeHeat_continuous hC2 hc'' hm.1).comp
      (continuous_const.prodMk (by fun_prop))).measurable)
    hb (fun w _ z => by simpa using interchangeHeat_abs_le hA hC2 hc'' hm w (x + Real.sqrt b * z))
  simpa only [parisiStep, tiltWeight, Real.sqrt_one, one_mul, zero_add] using! H

/-- The nested variance derivative extends genuinely inward to variance zero.
The smaller outer mass can be zero. -/
theorem hasDerivWithinAt_nested_parisiStep_variance_zero {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (l b x : ℝ) :
    HasDerivWithinAt (fun w => parisiStep l b (parisiStep m w A) x)
      (∫ z, interchangeHeat A A' A'' m 0 (x + Real.sqrt b * z) *
        tiltWeight l b (parisiStep m 0 A) x z ∂gaussianReal 0 1) (Set.Ici 0) 0 := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hj := continuous_parisiStep_variance_spatial hC2 hc'' hm.1
  have hLip (w : ℝ) := interchange_lipschitz
    (hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
      hc.measurable hc'.measurable hc''.measurable)
  have Hc := continuous_interchange_step_family hj.1 hLip l b x
  have Hd := continuous_interchange_mean_family hj.1 (interchangeHeat_continuous hC2 hc'' hm.1)
    hLip (interchangeHeat_abs_le hA hC2 hc'' hm) l b x
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (fun w hw => (hasDerivAt_nested_parisiStep_variance hA hC2 hc'' hm l b x hw).differentiableAt.differentiableWithinAt)
    Hc.continuousWithinAt self_mem_nhdsWithin
  apply Hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (hasDerivAt_nested_parisiStep_variance hA hC2 hc'' hm l b x hw).deriv.symm

private theorem interchangeHeat_zero (A A' A'' : ℝ → ℝ) (m x : ℝ) :
    interchangeHeat A A' A'' m 0 x = (A'' x + m * A' x ^ 2) / 2 := by
  simp [interchangeHeat, stepD1, stepD2, tiltE, tiltP, tiltQ, tiltR,
    Real.exp_ne_zero]

/-- The scalar heat equation extends inward to variance zero, with its
actual spatial derivatives at that face. -/
theorem hasDerivWithinAt_parisiStep_variance_zero {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) :
    HasDerivWithinAt (fun w => parisiStep m w A x)
      ((A'' x + m * A' x ^ 2) / 2) (Set.Ici 0) 0 := by
  have H := hasDerivWithinAt_nested_parisiStep_variance_zero hA hC2 hc'' hm 0 0 x
  simpa only [parisiStep_zero_var, tiltWeight, if_true, Real.sqrt_zero, zero_mul,
    add_zero, mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul,
    interchangeHeat_zero] using H

private theorem interchange_heat_mean {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    (m l b x : ℝ) :
    (∫ z, interchangeHeat A A' A'' m 0 (x + Real.sqrt b * z) *
      tiltWeight l b (parisiStep m 0 A) x z ∂gaussianReal 0 1) =
    (tiltQ A A'' l b x + m * tiltR A A' l b x) / (2 * tiltE A l b x) := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have he : parisiStep m 0 A = A := funext (parisiStep_zero_var m A)
  have hw (z : ℝ) : tiltWeight l b A x z =
      Real.exp (l * A (x + Real.sqrt b * z)) / tiltE A l b x := by
    by_cases hl : l = 0
    · simp [tiltWeight, tiltE, hl]
    · simp only [tiltWeight, if_neg hl, tiltE]
  rw [he]
  simp_rw [interchangeHeat_zero, hw]
  have hf (z : ℝ) :
      (A'' (x + Real.sqrt b * z) + m * A' (x + Real.sqrt b * z) ^ 2) / 2 *
        (Real.exp (l * A (x + Real.sqrt b * z)) / tiltE A l b x) =
      (A'' (x + Real.sqrt b * z) * Real.exp (l * A (x + Real.sqrt b * z)) +
        m * (A' (x + Real.sqrt b * z) ^ 2 * Real.exp (l * A (x + Real.sqrt b * z)))) /
        (2 * tiltE A l b x) := by ring
  simp_rw [hf]
  rw [integral_div, integral_add
    (integrable_tiltQ hC2.abs_second_le_one hA hc.measurable hc''.measurable x)
    ((integrable_tiltR hC2.abs_first_le_one hA hc.measurable hc'.measurable x).const_mul m),
    integral_const_mul]
  rfl

/-- The genuine small-variance commutator has the tilted slope variance as
its first coefficient. No comparison, stationarity, or equality is assumed.
The zero lower-mass face is included. -/
theorem hasDerivWithinAt_parisiStep_commutator_zero {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m l : ℝ} (hm : m ∈ Set.Icc 0 1) (hl : l ∈ Set.Icc 0 1) (b x : ℝ) :
    HasDerivWithinAt
      (fun w => parisiStep m w (parisiStep l b A) x - parisiStep l b (parisiStep m w A) x)
      (-(m - l) / 2 * (tiltR A A' l b x / tiltE A l b x -
        (tiltP A A' l b x / tiltE A l b x) ^ 2)) (Set.Ici 0) 0 := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB2 := hasParisiC2_parisiStep_nonneg (v := b) hl.1 hl.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hB'' : Continuous (stepD2 A A' A'' l b) :=
    (continuous_parisiStep_variance_spatial hC2 hc'' hl.1).2.2.comp
      (continuous_const.prodMk continuous_id)
  have H1 := hasDerivWithinAt_parisiStep_variance_zero
    (hasLinearGrowth_parisiStep hA hc.measurable l b) hB2 hB'' hm x
  have H2 := hasDerivWithinAt_nested_parisiStep_variance_zero hA hC2 hc'' hm l b x
  apply (H1.sub H2).congr_deriv
  rw [interchange_heat_mean hA hC2 hc'' m l b x]
  unfold stepD1 stepD2
  ring

/-- Every positive upper variance contains a genuinely strict small swap.
Only a single field is needed for the later positive-variance propagation. -/
theorem exists_small_strict_parisiStep_interchange {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    (hpos : ∀ y, 0 < A'' y) {m l a b : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hl : 0 ≤ l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (x : ℝ) :
    ∃ v ∈ Set.Ioo 0 a, parisiStep m v (parisiStep l b A) x <
      parisiStep l b (parisiStep m v A) x := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hvar := tilt_variance_pos_of_strictMono hA hc hc' hC2.abs_first_le_one
    (strictMono_of_hasDerivAt_pos hC2.2.1 hpos) l hb x
  have Hd := hasDerivWithinAt_parisiStep_commutator_zero hA hC2 hc'' hm
    ⟨hl, hlm.le.trans hm.2⟩ b x
  have hneg : -(m - l) / 2 * (tiltR A A' l b x / tiltE A l b x -
      (tiltP A A' l b x / tiltE A l b x) ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hvar
  have He := Hd.Ioi_of_Ici.limsup_slope_le' (by simp) hneg
  have Ha : ∀ᶠ v : ℝ in 𝓝[>] 0, v < a :=
    nhdsWithin_le_nhds (Iio_mem_nhds ha)
  have Hp : ∀ᶠ v : ℝ in 𝓝[>] 0, 0 < v := self_mem_nhdsWithin
  obtain ⟨v, hv, hva, hvneg⟩ := (Hp.and (Ha.and He)).exists
  refine ⟨v, ⟨hv, hva⟩, ?_⟩
  have he : parisiStep m 0 A = A := funext (parisiStep_zero_var m A)
  simpa only [slope_def_field, parisiStep_zero_var, he, sub_self, sub_zero,
    div_lt_iff₀ hv, zero_mul, sub_lt_zero] using hvneg

/-- Strict Talagrand Gaussian operator interchange for the actual scalar
regularity class. Both variances are positive and the masses differ; the
smaller mass is explicitly allowed to vanish. Strict convexity is expressed
by the positive, continuous actual Hessian. -/
theorem parisiStep_interchange_strict {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    (hpos : ∀ y, 0 < A'' y) {m l a b : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hl : 0 ≤ l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (x : ℝ) :
    parisiStep m a (parisiStep l b A) x < parisiStep l b (parisiStep m a A) x := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  obtain ⟨v, hv, hswap⟩ := exists_small_strict_parisiStep_interchange
    hA hC2 hc'' hpos hm hl hlm ha hb 0
  have hgap : 0 < a - v := sub_pos.mpr hv.2
  let B := parisiStep l b A
  let C := parisiStep m v A
  have hBg : HasLinearGrowth B := hasLinearGrowth_parisiStep hA hc.measurable l b
  have hBm : Measurable B := measurable_parisiStep hc.measurable l b
  have hCg : HasLinearGrowth C := hasLinearGrowth_parisiStep hA hc.measurable m v
  have hCm : Measurable C := measurable_parisiStep hc.measurable m v
  have hB2 := hasParisiC2_parisiStep_nonneg (v := b) hl (hlm.le.trans hm.2) hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hC2' := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hB'' : Continuous (stepD2 A A' A'' l b) :=
    (continuous_parisiStep_variance_spatial hC2 hc'' hl).2.2.comp
      (continuous_const.prodMk continuous_id)
  have hC'' : Continuous (stepD2 A A' A'' m v) :=
    (continuous_parisiStep_variance_spatial hC2 hc'' hm.1).2.2.comp
      (continuous_const.prodMk continuous_id)
  have hLc : Continuous (parisiStep m v B) :=
    (continuous_parisiStep_variance_spatial hB2 hB'' hm.1).1.comp
      (continuous_const.prodMk continuous_id)
  have hRc : Continuous (parisiStep l b C) :=
    (continuous_parisiStep_variance_spatial hC2' hC'' hl).1.comp
      (continuous_const.prodMk continuous_id)
  have Hstrict := parisiStep_lt_of_continuous_le hm.1 hgap
    (hasLinearGrowth_parisiStep hBg hBm m v)
    (hasLinearGrowth_parisiStep hCg hCm l b) hLc hRc
    (fun y => parisiStep_interchange hA hc.measurable hl hlm.le hv.1.le hb.le y) hswap x
  have Hle := parisiStep_interchange hCg hCm hl hlm.le hgap.le hb.le x
  have hleft := congrFun (parisiStep_add m (a - v) v hgap.le hv.1.le hBg hBm) x
  have hright := parisiStep_add m (a - v) v hgap.le hv.1.le hA hc.measurable
  have he : a - v + v = a := sub_add_cancel a v
  rw [he] at hleft hright
  calc
    parisiStep m a (parisiStep l b A) x = parisiStep m (a - v) (parisiStep m v B) x := hleft
    _ < parisiStep m (a - v) (parisiStep l b C) x := Hstrict
    _ ≤ parisiStep l b (parisiStep m (a - v) C) x := Hle
    _ = parisiStep l b (parisiStep m a A) x := by rw [hright]

/-- Strict interchange specialized to every genuine Parisi recursion level;
no extra analytic or nondegeneracy condition is left on the input profile. -/
theorem parisiStep_interchange_parisiF_strict {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m l a b : ℝ} (hm : m ∈ Set.Icc 0 1) (hl : 0 ≤ l) (hlm : l < m)
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    parisiStep m a (parisiStep l b (parisiF s β j)) x <
      parisiStep l b (parisiStep m a (parisiF s β j)) x :=
  parisiStep_interchange_strict (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) (parisiFSecond_pos s β j) hm hl hlm ha hb x

/-- The Hessian of an arbitrary admissible scalar cascade is continuous;
the masses need not be sorted and the variances may vanish. -/
theorem continuous_scalarFieldCascadeSecond (M V : ℕ → ℝ)
    (hM : ∀ j, M j ∈ Set.Icc 0 1) (j : ℕ) :
    Continuous (scalarFieldCascadeSecond M V j) := by
  induction j with
  | zero =>
    exact continuous_const.sub ((Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')).pow 2)
  | succ j ih =>
    exact (continuous_parisiStep_variance_spatial (scalarFieldCascade_C2_pos M V hM j).1
      ih (hM j).1).2.2.comp (continuous_const.prodMk continuous_id)

/-- Strict interchange on any unsorted scalar suffix of the actual tagged
interleaving construction. All analytic properties are discharged internally. -/
theorem parisiStep_interchange_scalarFieldCascade_strict (M V : ℕ → ℝ)
    (hM : ∀ j, M j ∈ Set.Icc 0 1) (j : ℕ)
    {m l a b : ℝ} (hm : m ∈ Set.Icc 0 1) (hl : 0 ≤ l) (hlm : l < m)
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    parisiStep m a (parisiStep l b (scalarFieldCascade M V j)) x <
      parisiStep l b (parisiStep m a (scalarFieldCascade M V j)) x :=
  parisiStep_interchange_strict (scalarFieldCascade_props M V j).2.1
    (scalarFieldCascade_C2_pos M V hM j).1
    (continuous_scalarFieldCascadeSecond M V hM j) (scalarFieldCascade_C2_pos M V hM j).2.2.2
    hm hl hlm ha hb x

end SpinGlass.Targets
