module

public import Paper.ParisiMixDifferentiation
public import Paper.ParisiMildDerivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-! # Differentiating the actual local Parisi potential

The potential correction is the quadratic form of a genuine bounded
Gaussian time-integral functional. This identifies its derivative along
probability mixtures from the already constructed local gradient derivative.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction NNReal

namespace Paper

noncomputable def parisiSlabPotentialLinearSource (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (t x s : ℝ) : ℝ :=
  parisiCDF μ s * heatSemigroup (β ^ 2 * (s - t))
    (fun y => parisiSlabExtend hab v (s, y)) x

theorem parisiSlabPotentialLinearSource_measurable (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (t x : ℝ) :
    Measurable (parisiSlabPotentialLinearSource β μ hab v t x) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      parisiSlabExtend hab v (p.1, x + Real.sqrt (β ^ 2 * (p.1 - t)) * p.2)) :=
    (continuous_parisiSlabExtend hab v).measurable.comp (by fun_prop)
  exact (parisiCDF_measurable μ).mul
    (hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable

theorem norm_parisiSlabPotentialLinearSource_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (t x s : ℝ) :
    ‖parisiSlabPotentialLinearSource β μ hab v t x s‖ ≤ ‖v‖ := by
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  rw [parisiSlabPotentialLinearSource, norm_mul]
  exact (mul_le_mul hm (norm_heatSemigroup_le _ _ ‖v‖
    (fun y => norm_parisiSlabExtend_le hab v (s, y)) x) (norm_nonneg _) (by norm_num))
    |>.trans_eq (one_mul _)

theorem parisiSlabPotentialLinearSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (t x c d : ℝ) :
    IntervalIntegrable (parisiSlabPotentialLinearSource β μ hab v t x) volume c d :=
  (intervalIntegrable_const : IntervalIntegrable (fun _ => ‖v‖) volume c d).mono_fun'
    (parisiSlabPotentialLinearSource_measurable β μ hab v t x).aestronglyMeasurable
    (.of_forall (norm_parisiSlabPotentialLinearSource_le β μ hab v t x))

noncomputable def parisiSlabPotentialLinearValue (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (v : ParisiSlabGradient a b) : ℝ :=
  β ^ 2 / 2 * ∫ s in t..b, parisiSlabPotentialLinearSource β μ hab v t x s

theorem norm_parisiSlabPotentialLinearValue_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (htb : t ≤ b) (v : ParisiSlabGradient a b) :
    ‖parisiSlabPotentialLinearValue β μ hab t x v‖ ≤ β ^ 2 / 2 * (b - t) * ‖v‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := b)
    (fun s _ => norm_parisiSlabPotentialLinearSource_le β μ hab v t x s)
  rw [abs_of_nonneg (sub_nonneg.mpr htb)] at h
  rw [parisiSlabPotentialLinearValue, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem parisiSlabPotentialLinearSource_add (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) (t x s : ℝ) :
    parisiSlabPotentialLinearSource β μ hab (v + w) t x s =
      parisiSlabPotentialLinearSource β μ hab v t x s +
        parisiSlabPotentialLinearSource β μ hab w t x s := by
  have hi := integrable_heatSemigroup_integrand (β ^ 2 * (s - t))
    (fun y => parisiSlabExtend hab v (s, y))
    ((continuous_parisiSlabExtend hab v).measurable.comp (by fun_prop)) ‖v‖
    (fun y => norm_parisiSlabExtend_le hab v (s, y)) x
  have hj := integrable_heatSemigroup_integrand (β ^ 2 * (s - t))
    (fun y => parisiSlabExtend hab w (s, y))
    ((continuous_parisiSlabExtend hab w).measurable.comp (by fun_prop)) ‖w‖
    (fun y => norm_parisiSlabExtend_le hab w (s, y)) x
  unfold parisiSlabPotentialLinearSource heatSemigroup gaussianExpectation
  change _ * (∫ z, (parisiSlabExtend hab v (s, x + _ * z) +
    parisiSlabExtend hab w (s, x + _ * z)) ∂gaussianReal 0 1) = _
  rw [integral_add hi hj, mul_add]

theorem parisiSlabPotentialLinearSource_smul (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (c t x s : ℝ) :
    parisiSlabPotentialLinearSource β μ hab (c • v) t x s =
      c * parisiSlabPotentialLinearSource β μ hab v t x s := by
  unfold parisiSlabPotentialLinearSource heatSemigroup gaussianExpectation
  change _ * (∫ z, c * parisiSlabExtend hab v (s, x + _ * z) ∂gaussianReal 0 1) = _
  rw [integral_const_mul]
  ring

noncomputable def parisiSlabPotentialLinearOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (htb : t ≤ b) :
    ParisiSlabGradient a b →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := parisiSlabPotentialLinearValue β μ hab t x
      map_add' := fun v w => by
        unfold parisiSlabPotentialLinearValue
        simp_rw [parisiSlabPotentialLinearSource_add]
        rw [intervalIntegral.integral_add
          (parisiSlabPotentialLinearSource_intervalIntegrable β μ hab v t x t b)
          (parisiSlabPotentialLinearSource_intervalIntegrable β μ hab w t x t b), mul_add]
      map_smul' := fun c v => by
        unfold parisiSlabPotentialLinearValue
        simp_rw [parisiSlabPotentialLinearSource_smul]
        rw [intervalIntegral.integral_const_mul]
        change _ = c * _
        ring }
    (β ^ 2 / 2 * (b - t)) (norm_parisiSlabPotentialLinearValue_le β μ hab t x htb)

@[simp] theorem parisiSlabPotentialLinearOperator_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (htb : t ≤ b) (v : ParisiSlabGradient a b) :
    parisiSlabPotentialLinearOperator β μ hab t x htb v =
      parisiSlabPotentialLinearValue β μ hab t x v := rfl

theorem parisiDuhamelCorrection_eq_potentialLinearOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (t x : ℝ) (htb : t ≤ b) :
    parisiDuhamelCorrection β μ (parisiSlabExtend hab v) b t x =
      parisiSlabPotentialLinearOperator β μ hab t x htb (v * v) := by
  simp only [parisiSlabPotentialLinearOperator_apply, parisiSlabPotentialLinearValue,
    parisiDuhamelCorrection, parisiSlabPotentialLinearSource, parisiHeatSource,
    parisiSlabExtend, pow_two]
  rfl

theorem parisiSlabPotentialLinearOperator_mix_apply (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (htb : t ≤ b) (v : ParisiSlabGradient a b)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) :
    parisiSlabPotentialLinearOperator β (parisiMix μ ν ε) hab t x htb v =
      (1 - ε) * parisiSlabPotentialLinearOperator β μ hab t x htb v +
        ε * parisiSlabPotentialLinearOperator β ν hab t x htb v := by
  simp only [parisiSlabPotentialLinearOperator_apply, parisiSlabPotentialLinearValue]
  have he : parisiSlabPotentialLinearSource β (parisiMix μ ν ε) hab v t x =
      fun s => (1 - ε) * parisiSlabPotentialLinearSource β μ hab v t x s +
        ε * parisiSlabPotentialLinearSource β ν hab v t x s := by
    funext s
    unfold parisiSlabPotentialLinearSource
    rw [parisiCDF_mix μ ν ε s hε]
    ring
  rw [he, intervalIntegral.integral_add
    ((parisiSlabPotentialLinearSource_intervalIntegrable β μ hab v t x t b).const_mul _)
    ((parisiSlabPotentialLinearSource_intervalIntegrable β ν hab v t x t b).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The potential's actual mixture derivative, for any differentiated bounded gradient family. -/
theorem hasDerivWithinAt_parisiDuhamelCorrection_mix (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (t x : ℝ) (htb : t ≤ b)
    (v : ℝ → ParisiSlabGradient a b) (w : ParisiSlabGradient a b)
    (hv : HasDerivWithinAt v w (Icc (0 : ℝ) 1) 0) :
    HasDerivWithinAt (fun ε => parisiDuhamelCorrection β (parisiMix μ ν ε)
      (parisiSlabExtend hab (v ε)) b t x)
      (parisiDuhamelCorrection β ν (parisiSlabExtend hab (v 0)) b t x -
        parisiDuhamelCorrection β μ (parisiSlabExtend hab (v 0)) b t x +
          2 * parisiSlabPotentialLinearOperator β μ hab t x htb (v 0 * w))
      (Icc (0 : ℝ) 1) 0 := by
  let A := parisiSlabPotentialLinearOperator β μ hab t x htb
  let B := parisiSlabPotentialLinearOperator β ν hab t x htb
  have hA := A.hasFDerivAt.comp_hasDerivWithinAt 0 (hv.mul hv)
  have hB := B.hasFDerivAt.comp_hasDerivWithinAt 0 (hv.mul hv)
  have hId := (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have hOne := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  have h := ((hOne.sub hId).mul hA).add (hId.mul hB)
  have hmul : w * v 0 + v 0 * w = (2 : ℝ) • (v 0 * w) := by
    simp only [two_smul ℝ]
    rw [mul_comm w (v 0)]
  have hd : (-1) * A (v 0 * v 0) + (1 - 0) * A (w * v 0 + v 0 * w) +
      (1 * B (v 0 * v 0) + 0 * B (w * v 0 + v 0 * w)) =
      parisiDuhamelCorrection β ν (parisiSlabExtend hab (v 0)) b t x -
        parisiDuhamelCorrection β μ (parisiSlabExtend hab (v 0)) b t x +
          2 * A (v 0 * w) := by
    rw [parisiDuhamelCorrection_eq_potentialLinearOperator,
      parisiDuhamelCorrection_eq_potentialLinearOperator, hmul, map_smul]
    change _ = B (v 0 * v 0) - A (v 0 * v 0) + 2 * A (v 0 * w)
    simp only [smul_eq_mul]
    ring
  have h' : HasDerivWithinAt
      (fun ε => (1 - ε) * A (v ε * v ε) + ε * B (v ε * v ε))
      ((-1) * A (v 0 * v 0) + (1 - 0) * A (w * v 0 + v 0 * w) +
        (1 * B (v 0 * v 0) + 0 * B (w * v 0 + v 0 * w)))
      (Icc (0 : ℝ) 1) 0 := by
    convert! h using 1
    simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply,
        id_eq, zero_sub]
  apply (h'.congr_deriv hd).congr
  · intro ε hε
    rw [parisiDuhamelCorrection_eq_potentialLinearOperator β (parisiMix μ ν ε)
      hab (v ε) t x htb,
      parisiSlabPotentialLinearOperator_mix_apply β μ ν hab t x htb (v ε * v ε) ε hε]
  · rw [parisiDuhamelCorrection_eq_potentialLinearOperator β (parisiMix μ ν 0)
      hab (v 0) t x htb, parisiMix_zero]
    change A (v 0 * v 0) = (1 - 0) * A (v 0 * v 0) + 0 * B (v 0 * v 0)
    ring

/-- The actual local potential varies differentiably with the probability measure. -/
theorem hasDerivWithinAt_chosenLocalParisiPotential_mix (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (t x : ℝ) (htb : t ≤ b) :
    HasDerivWithinAt
      (fun ε => parisiDuhamelCorrection β (parisiMix μ ν ε)
        (parisiSlabExtend hab
          (chosenLocalParisiGradient β (parisiMix μ ν ε) hab g hg hgb hshort)) b t x)
      (parisiDuhamelCorrection β ν
        (parisiSlabExtend hab (chosenLocalParisiGradient β μ hab g hg hgb hshort)) b t x -
      parisiDuhamelCorrection β μ
        (parisiSlabExtend hab (chosenLocalParisiGradient β μ hab g hg hgb hshort)) b t x +
      2 * parisiSlabPotentialLinearOperator β μ hab t x htb
        (chosenLocalParisiGradient β μ hab g hg hgb hshort *
          localParisiMixDerivative β μ ν hab
            (chosenLocalParisiGradient β μ hab g hg hgb hshort)
            (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).1 hshort))
      (Icc (0 : ℝ) 1) 0 := by
  simpa only [parisiMix_zero] using hasDerivWithinAt_parisiDuhamelCorrection_mix β μ ν hab t x htb
    (fun ε => chosenLocalParisiGradient β (parisiMix μ ν ε) hab g hg hgb hshort)
    (localParisiMixDerivative β μ ν hab
      (chosenLocalParisiGradient β μ hab g hg hgb hshort)
      (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).1 hshort)
    (hasDerivWithinAt_chosenLocalParisiGradient_mix β μ ν hab g hg hgb hshort)

end Paper
