module

public import Paper.ParisiVariation
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-! # Actual local Parisi derivatives along probability mixtures

The local gradient is the unique bounded solution of its actual Gaussian
Duhamel equation. Its mixture derivative is constructed from the linearized
Gaussian equation, rather than included as a hypothesis.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction NNReal

namespace Paper

noncomputable def chosenLocalParisiGradient (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    ParisiSlabGradient a b :=
  Classical.choose (exists_unique_localParisiGradient β μ hab g hg hgb hshort).exists

theorem chosenLocalParisiGradient_spec (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    ‖chosenLocalParisiGradient β μ hab g hg hgb hshort‖ ≤ 2 ∧
      parisiSlabGradientOperator β μ hab g hg hgb
        (chosenLocalParisiGradient β μ hab g hg hgb hshort) =
          chosenLocalParisiGradient β μ hab g hg hgb hshort :=
  Classical.choose_spec (exists_unique_localParisiGradient β μ hab g hg hgb hshort).exists

noncomputable def parisiSlabLinearizedOperator (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) :
    ParisiSlabGradient a b →L[ℝ] ParisiSlabGradient a b :=
  (2 : ℝ) • parisiSlabBilinearOperator β μ hab v

@[simp] theorem parisiSlabLinearizedOperator_apply (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) :
    parisiSlabLinearizedOperator β μ hab v w =
      (2 : ℝ) • parisiSlabBilinearOperator β μ hab v w := rfl

theorem norm_parisiSlabLinearizedOperator_apply_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    ‖parisiSlabLinearizedOperator β μ hab v w‖ ≤ (1 / 2 : ℝ) * ‖w‖ := by
  rw [parisiSlabLinearizedOperator_apply, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := norm_parisiSlabBilinearOperator_apply_le β μ hab v w
  have hC := parisiSlabContractionConstant_nonneg β a b
  have hn := norm_nonneg w
  have hCv : parisiSlabContractionConstant β a b * ‖v‖ ≤ 1 / 4 := by
    calc
      _ ≤ parisiSlabContractionConstant β a b * 2 :=
        mul_le_mul_of_nonneg_left hv hC
      _ ≤ 1 / 4 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hCv hn]

noncomputable def parisiSlabVariationMap (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v w : ParisiSlabGradient a b) : ParisiSlabGradient a b :=
  (parisiSlabQuadraticOperator β ν hab v - parisiSlabQuadraticOperator β μ hab v) +
    parisiSlabLinearizedOperator β μ hab v w

theorem parisiSlabVariationMap_contracting (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    ContractingWith (1 / 2 : ℝ≥0) (parisiSlabVariationMap β μ ν hab v) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  unfold parisiSlabVariationMap
  rw [add_sub_add_left_eq_sub, ← map_sub]
  exact norm_parisiSlabLinearizedOperator_apply_le β μ hab v (w - z) hv hshort

noncomputable def localParisiMixDerivative (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) : ParisiSlabGradient a b :=
  ContractingWith.fixedPoint (parisiSlabVariationMap β μ ν hab v)
    (parisiSlabVariationMap_contracting β μ ν hab v hv hshort)

theorem localParisiMixDerivative_equation (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (v : ParisiSlabGradient a b) (hv : ‖v‖ ≤ 2)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    localParisiMixDerivative β μ ν hab v hv hshort =
      (parisiSlabQuadraticOperator β ν hab v - parisiSlabQuadraticOperator β μ hab v) +
        parisiSlabLinearizedOperator β μ hab v
          (localParisiMixDerivative β μ ν hab v hv hshort) :=
  (parisiSlabVariationMap_contracting β μ ν hab v hv hshort).fixedPoint_isFixedPt.eq.symm

theorem parisiSlabGradientOperator_sub_eq_quadratic (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (v w : ParisiSlabGradient a b) :
    parisiSlabGradientOperator β μ hab g hg hgb v -
      parisiSlabGradientOperator β ν hab g hg hgb w =
        parisiSlabQuadraticOperator β μ hab v - parisiSlabQuadraticOperator β ν hab w := by
  ext p
  change (heatSemigroup _ g _ + _) - (heatSemigroup _ g _ + _) = _
  rw [BoundedContinuousFunction.sub_apply, parisiSlabQuadraticOperator_apply,
    parisiSlabQuadraticOperator_apply]
  ring

private theorem quadratic_linear_remainder
    {X : Type*} [NormedCommRing X] [NormedAlgebra ℝ X]
    (A B : X →L[ℝ] X) (x y w : X) (ε : ℝ)
    (hy : y - x = A (y * y) - A (x * x) + ε • (B (y * y) - A (y * y)))
    (hw : w = B (x * x) - A (x * x) + (2 : ℝ) • A (x * w)) :
    (y - x - ε • w) - (2 : ℝ) • A (x * (y - x - ε • w)) =
      A ((y - x) * (y - x)) +
        ε • ((B (y * y) - A (y * y)) - (B (x * x) - A (x * x))) := by
  have hA : A (y * y) - A (x * x) =
      (2 : ℝ) • A (x * (y - x)) + A ((y - x) * (y - x)) := by
    rw [← map_smul, ← map_add, ← map_sub]
    congr 1
    simp only [two_smul ℝ]
    ring
  have hL : (2 : ℝ) • A (x * (y - x - ε • w)) =
      (2 : ℝ) • A (x * (y - x)) - ε • ((2 : ℝ) • A (x * w)) := by
    rw [mul_sub, map_sub, mul_smul_comm, map_smul]
    module
  have hres : (y - x) - (2 : ℝ) • A (x * (y - x)) =
      A ((y - x) * (y - x)) + ε • (B (y * y) - A (y * y)) := by
    calc
      _ = (A (y * y) - A (x * x) + ε • (B (y * y) - A (y * y))) -
          (2 : ℝ) • A (x * (y - x)) := congrArg (fun z => z - (2 : ℝ) • A (x * (y - x))) hy
      _ = _ := by rw [hA]; module
  have hws : w - (2 : ℝ) • A (x * w) = B (x * x) - A (x * x) := by
    calc
      _ = (B (x * x) - A (x * x) + (2 : ℝ) • A (x * w)) -
          (2 : ℝ) • A (x * w) := congrArg (fun z => z - (2 : ℝ) • A (x * w)) hw
      _ = _ := by module
  calc
    _ = ((y - x) - (2 : ℝ) • A (x * (y - x))) -
        ε • (w - (2 : ℝ) • A (x * w)) := by rw [hL]; module
    _ = (A ((y - x) * (y - x)) + ε • (B (y * y) - A (y * y))) -
        ε • (B (x * x) - A (x * x)) := by rw [hres, hws]
    _ = _ := by module

/-- The actual mixture fixed point has a quadratic Taylor remainder. -/
theorem localParisiMix_quadratic_remainder (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v y : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hynorm : ‖y‖ ≤ 2)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hy : parisiSlabGradientOperator β (parisiMix μ ν ε) hab g hg hgb y = y) :
    ‖y - v - ε • localParisiMixDerivative β μ ν hab v hvnorm hshort‖ ≤ 4 * ε ^ 2 := by
  let C := parisiSlabContractionConstant β a b
  let A := parisiSlabLinearOperator β μ hab
  let B := parisiSlabLinearOperator β ν hab
  let w := localParisiMixDerivative β μ ν hab v hvnorm hshort
  let r := y - v - ε • w
  have hC : 0 ≤ C := parisiSlabContractionConstant_nonneg β a b
  have hCs : C ≤ 1 / 8 := hshort
  have hδ : ‖y - v‖ ≤ ε := by
    have h := localParisiGradient_mix_stability β μ ν hab g hg hgb hshort v y
      hvnorm hynorm ε hε hv hy
    rw [norm_sub_rev] at h
    have hc := mul_le_mul_of_nonneg_right hCs hε.1
    change ‖y - v‖ ≤ ε
    linarith
  have hvar : y - v = A (y * y) - A (v * v) + ε • (B (y * y) - A (y * y)) := by
    calc
      _ = parisiSlabGradientOperator β (parisiMix μ ν ε) hab g hg hgb y -
          parisiSlabGradientOperator β μ hab g hg hgb v := by rw [hv, hy]
      _ = parisiSlabQuadraticOperator β (parisiMix μ ν ε) hab y -
          parisiSlabQuadraticOperator β μ hab v :=
        parisiSlabGradientOperator_sub_eq_quadratic β (parisiMix μ ν ε) μ hab g hg hgb y v
      _ = _ := by
        rw [parisiSlabQuadraticOperator_eq_bilinear, parisiSlabBilinearOperator_mix_apply β μ ν hab ε hε]
        rw [parisiSlabQuadraticOperator_eq_bilinear]
        change (1 - ε) • A (y * y) + ε • B (y * y) - A (v * v) = _
        module
  have hw : w = B (v * v) - A (v * v) + (2 : ℝ) • A (v * w) := by
    exact localParisiMixDerivative_equation β μ ν hab v hvnorm hshort
      |>.trans (by simp only [parisiSlabQuadraticOperator_eq_bilinear,
        parisiSlabBilinearOperator_apply, parisiSlabLinearizedOperator_apply]; rfl)
  have hr : r - parisiSlabLinearizedOperator β μ hab v r =
      A ((y - v) * (y - v)) +
        ε • ((B (y * y) - A (y * y)) - (B (v * v) - A (v * v))) :=
    quadratic_linear_remainder A B v y w ε hvar hw
  have hquadratic : ‖A ((y - v) * (y - v))‖ ≤ ε ^ 2 := by
    have h := norm_parisiSlabBilinearOperator_apply_le β μ hab (y - v) (y - v)
    change ‖A ((y - v) * (y - v))‖ ≤ C * ‖y - v‖ * ‖y - v‖ at h
    have hp : ‖y - v‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hδ 2
    have hCp := mul_le_mul_of_nonneg_right (show C ≤ 1 by linarith) (sq_nonneg ‖y - v‖)
    nlinarith
  have hdiff : ‖(B (y * y) - A (y * y)) - (B (v * v) - A (v * v))‖ ≤ ε := by
    have hμ := norm_parisiSlabGradientOperator_sub_le β μ hab (fun _ => 0)
      continuous_const (by simp) y v hynorm hvnorm
    have hν := norm_parisiSlabGradientOperator_sub_le β ν hab (fun _ => 0)
      continuous_const (by simp) y v hynorm hvnorm
    change ‖parisiSlabQuadraticOperator β μ hab y - parisiSlabQuadraticOperator β μ hab v‖ ≤
      4 * C * ‖y - v‖ at hμ
    change ‖parisiSlabQuadraticOperator β ν hab y - parisiSlabQuadraticOperator β ν hab v‖ ≤
      4 * C * ‖y - v‖ at hν
    rw [parisiSlabQuadraticOperator_eq_bilinear, parisiSlabQuadraticOperator_eq_bilinear] at hμ hν
    change ‖A (y * y) - A (v * v)‖ ≤ 4 * C * ‖y - v‖ at hμ
    change ‖B (y * y) - B (v * v)‖ ≤ 4 * C * ‖y - v‖ at hν
    have ht := norm_sub_le (B (y * y) - B (v * v)) (A (y * y) - A (v * v))
    rw [show (B (y * y) - B (v * v)) - (A (y * y) - A (v * v)) =
      (B (y * y) - A (y * y)) - (B (v * v) - A (v * v)) by abel] at ht
    have hc := mul_le_mul_of_nonneg_right hCs (norm_nonneg (y - v))
    linarith
  have hres : ‖r - parisiSlabLinearizedOperator β μ hab v r‖ ≤ 2 * ε ^ 2 := by
    rw [hr]
    have hn := norm_add_le (A ((y - v) * (y - v)))
      (ε • ((B (y * y) - A (y * y)) - (B (v * v) - A (v * v))))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.1] at hn
    have hd := mul_le_mul_of_nonneg_left hdiff hε.1
    nlinarith
  have hn := norm_add_le (r - parisiSlabLinearizedOperator β μ hab v r)
    (parisiSlabLinearizedOperator β μ hab v r)
  rw [sub_add_cancel] at hn
  have hl := norm_parisiSlabLinearizedOperator_apply_le β μ hab v r hvnorm hshort
  change ‖r‖ ≤ 4 * ε ^ 2
  linarith

/-- Genuine one-sided Gateaux differentiability of the actual local gradient. -/
theorem hasDerivWithinAt_chosenLocalParisiGradient_mix (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x, ‖g x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8) :
    HasDerivWithinAt
      (fun ε => chosenLocalParisiGradient β (parisiMix μ ν ε) hab g hg hgb hshort)
      (localParisiMixDerivative β μ ν hab
        (chosenLocalParisiGradient β μ hab g hg hgb hshort)
        (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).1 hshort)
      (Icc (0 : ℝ) 1) 0 := by
  let v := chosenLocalParisiGradient β μ hab g hg hgb hshort
  let w := localParisiMixDerivative β μ ν hab v
    (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).1 hshort
  rw [hasDerivWithinAt_iff_tendsto]
  simp only [parisiMix_zero, sub_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun ε => by positivity)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have h := localParisiMix_quadratic_remainder β μ ν hab g hg hgb hshort v
      (chosenLocalParisiGradient β (parisiMix μ ν ε) hab g hg hgb hshort)
      (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).1
      (chosenLocalParisiGradient_spec β (parisiMix μ ν ε) hab g hg hgb hshort).1 ε hε
      (chosenLocalParisiGradient_spec β μ hab g hg hgb hshort).2
      (chosenLocalParisiGradient_spec β (parisiMix μ ν ε) hab g hg hgb hshort).2
    change ‖ε‖⁻¹ * ‖chosenLocalParisiGradient β (parisiMix μ ν ε) hab g hg hgb hshort -
      v - ε • w‖ ≤ 4 * ε
    rw [Real.norm_eq_abs, abs_of_nonneg hε.1]
    calc
      _ ≤ ε⁻¹ * (4 * ε ^ 2) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hε.1)
      _ = 4 * ε := by
        by_cases he : ε = 0
        · simp [he]
        · field_simp
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (4 : ℝ))
      (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 4)).mul nhdsWithin_le_nhds)

end Paper
