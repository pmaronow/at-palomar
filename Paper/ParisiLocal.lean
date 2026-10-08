module

public import Paper.ParisiMild
public import Paper.PDEFixedPoint
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! # A concrete local bounded-gradient solution

The gradient Duhamel map acts on bounded continuous functions on a time
slab. Clamping time extends such functions to the full plane without
increasing their norm. The normalized Gaussian correction handles jumps
of the measure's distribution function and the terminal time.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Paper

abbrev ParisiSlabGradient (a b : ℝ) := BoundedContinuousFunction (Icc a b × ℝ) ℝ

noncomputable def parisiSlabExtend {a b : ℝ} (hab : a ≤ b)
    (v : ParisiSlabGradient a b) (p : ℝ × ℝ) : ℝ :=
  v (projIcc a b hab p.1, p.2)

theorem continuous_parisiSlabExtend {a b : ℝ} (hab : a ≤ b)
    (v : ParisiSlabGradient a b) : Continuous (parisiSlabExtend hab v) := by
  exact v.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)

theorem norm_parisiSlabExtend_le {a b : ℝ} (hab : a ≤ b)
    (v : ParisiSlabGradient a b) (p : ℝ × ℝ) : ‖parisiSlabExtend hab v p‖ ≤ ‖v‖ :=
  v.norm_coe_le_norm _

theorem norm_parisiSlabExtend_sub_le {a b : ℝ} (hab : a ≤ b)
    (v w : ParisiSlabGradient a b) (p : ℝ × ℝ) :
    ‖parisiSlabExtend hab v p - parisiSlabExtend hab w p‖ ≤ ‖v - w‖ :=
  (v - w).norm_coe_le_norm _

noncomputable def parisiSlabContractionConstant (β a b : ℝ) : ℝ :=
  |β| * gaussianAbsMoment * Real.sqrt (b - a)

theorem parisiSlabContractionConstant_nonneg (β a b : ℝ) :
    0 ≤ parisiSlabContractionConstant β a b :=
  mul_nonneg (mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg) (Real.sqrt_nonneg _)

noncomputable def parisiSlabGradientValue (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (v : ParisiSlabGradient a b)
    (p : Icc a b × ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * (b - p.1)) g p.2 +
    parisiNormalizedGradientCorrection β μ (parisiSlabExtend hab v) b p.1 p.2

theorem continuous_parisiSlabGradientValue (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (v : ParisiSlabGradient a b) :
    Continuous (parisiSlabGradientValue β μ hab g v) := by
  have hh := (continuous_gaussian_affine_joint g 1 hg hgb).comp
    (show Continuous (fun p : Icc a b × ℝ => (p.2, β ^ 2 * (b - p.1))) by fun_prop)
  have hc := (continuous_parisiNormalizedGradientCorrection β μ (parisiSlabExtend hab v)
    (continuous_parisiSlabExtend hab v) ‖v‖ (norm_parisiSlabExtend_le hab v) b).comp
    (show Continuous (fun p : Icc a b × ℝ => ((p.1 : ℝ), p.2)) by fun_prop)
  exact hh.add hc

theorem norm_parisiSlabGradientValue_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) (p : Icc a b × ℝ) :
    ‖parisiSlabGradientValue β μ hab g v p‖ ≤
      1 + parisiSlabContractionConstant β a b * ‖v‖ ^ 2 := by
  have hh := norm_heatSemigroup_le (β ^ 2 * (b - p.1)) g 1 hgb p.2
  have hc := norm_parisiNormalizedGradientCorrection_le β μ (parisiSlabExtend hab v)
    ‖v‖ (norm_parisiSlabExtend_le hab v) b p.1 p.2
  have hs : Real.sqrt (b - (p.1 : ℝ)) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (sub_le_sub_left p.1.property.1 b)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ |β| * gaussianAbsMoment * ‖v‖ ^ 2 by
      have := gaussianAbsMoment_nonneg
      positivity)
  have hn := norm_add_le (heatSemigroup (β ^ 2 * (b - p.1)) g p.2)
    (parisiNormalizedGradientCorrection β μ (parisiSlabExtend hab v) b p.1 p.2)
  unfold parisiSlabGradientValue parisiSlabContractionConstant
  nlinarith

noncomputable def parisiSlabGradientOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) : ParisiSlabGradient a b :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (parisiSlabGradientValue β μ hab g v) (continuous_parisiSlabGradientValue β μ hab g hg hgb v)
    (1 + parisiSlabContractionConstant β a b * ‖v‖ ^ 2)
    (norm_parisiSlabGradientValue_le β μ hab g hgb v)

theorem norm_parisiSlabGradientOperator_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb v‖ ≤
      1 + parisiSlabContractionConstant β a b * ‖v‖ ^ 2 := by
  apply (BoundedContinuousFunction.norm_le (by
    have := parisiSlabContractionConstant_nonneg β a b
    positivity)).mpr
  exact norm_parisiSlabGradientValue_le β μ hab g hgb v

theorem norm_parisiSlabGradientOperator_sub_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v w : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2) (hw : ‖w‖ ≤ 2) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb v -
      parisiSlabGradientOperator β μ hab g hg hgb w‖ ≤
      4 * parisiSlabContractionConstant β a b * ‖v - w‖ := by
  apply (BoundedContinuousFunction.norm_le (by
    have := parisiSlabContractionConstant_nonneg β a b
    positivity)).mpr
  intro p
  change ‖parisiSlabGradientValue β μ hab g v p -
    parisiSlabGradientValue β μ hab g w p‖ ≤ _
  unfold parisiSlabGradientValue
  rw [add_sub_add_left_eq_sub,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2,
    parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2]
  have hc := norm_parisiGradientCorrection_sub_le β μ (parisiSlabExtend hab v)
    (parisiSlabExtend hab w) (continuous_parisiSlabExtend hab v).measurable
    (continuous_parisiSlabExtend hab w).measurable 2 ‖v - w‖
    (fun q => (norm_parisiSlabExtend_le hab v q).trans hv)
    (fun q => (norm_parisiSlabExtend_le hab w q).trans hw)
    (norm_parisiSlabExtend_sub_le hab v w) b p.1 p.2 p.1.property.2
  have hs : Real.sqrt (b - (p.1 : ℝ)) ≤ Real.sqrt (b - a) :=
    Real.sqrt_le_sqrt (sub_le_sub_left p.1.property.1 b)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * |β| * gaussianAbsMoment * 2 * ‖v - w‖ by
      have := gaussianAbsMoment_nonneg
      positivity)
  unfold parisiSlabContractionConstant
  nlinarith

theorem exists_unique_localParisiGradient (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    ∃! v : ParisiSlabGradient a b, ‖v‖ ≤ 2 ∧
      parisiSlabGradientOperator β μ hab g hg hgb v = v := by
  exact boundedGradient_fixedPoint (parisiSlabGradientOperator β μ hab g hg hgb)
    (parisiSlabContractionConstant β a b) (parisiSlabContractionConstant_nonneg β a b)
    hshort (norm_parisiSlabGradientOperator_le β μ hab g hg hgb)
    (norm_parisiSlabGradientOperator_sub_le β μ hab g hg hgb)

/-- The fixed point satisfies the original physical-time integral equation. -/
theorem localParisiGradient_equation (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v) (p : Icc a b × ℝ) :
    v p = heatSemigroup (β ^ 2 * (b - p.1)) g p.2 +
      parisiGradientCorrection β μ (parisiSlabExtend hab v) b p.1 p.2 := by
  have he := congrArg (fun w : ParisiSlabGradient a b => w p) hv
  change parisiSlabGradientValue β μ hab g v p = v p at he
  rw [← he]
  unfold parisiSlabGradientValue
  rw [parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2]

theorem localParisiGradient_terminal (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v) (x : ℝ) :
    v (⟨b, ⟨hab, le_rfl⟩⟩, x) = g x := by
  rw [localParisiGradient_equation β μ hab g hg hgb v hv]
  simp [parisiGradientCorrection, heatSemigroup, gaussianExpectation]

end Paper
