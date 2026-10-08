module

public import Paper.ParisiMeasureStability

@[expose] public section

/-! # Joint stability in the terminal gradient and the probability measure -/

open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Paper

theorem norm_parisiSlabGradientOperator_terminal_sub_le (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g k : ℝ → ℝ)
    (hg : Continuous g) (hk : Continuous k)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hkb : ∀ x, ‖k x‖ ≤ 1)
    (v : ParisiSlabGradient a b) (D : ℝ) (hd : ∀ x, ‖g x - k x‖ ≤ D) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb v -
      parisiSlabGradientOperator β μ hab k hk hkb v‖ ≤ D := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hd 0)
  apply (BoundedContinuousFunction.norm_le hD).mpr
  intro p
  change ‖parisiSlabGradientValue β μ hab g v p -
    parisiSlabGradientValue β μ hab k v p‖ ≤ D
  unfold parisiSlabGradientValue
  rw [add_sub_add_right_eq_sub, ← heatSemigroup_sub
    (β ^ 2 * (b - p.1)) g k hg.measurable hk.measurable 1 1 hgb hkb]
  exact norm_heatSemigroup_le _ _ D hd _

/-- The estimate allows independently varying terminal data. This is the
stability needed to continue finite-grid approximations across slabs. -/
theorem localParisiGradient_terminal_measure_mesh_stability
    (β : ℝ) (μ ν : ParisiMeasure) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g k : ℝ → ℝ) (hg : Continuous g) (hk : Continuous k)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hkb : ∀ x, ‖k x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v w : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hwnorm : ‖w‖ ≤ 2)
    (hv : parisiSlabGradientOperator β μ hab g hg hgb v = v)
    (hw : parisiSlabGradientOperator β ν hab k hk hkb w = w)
    (D : ℝ) (hd : ∀ x, ‖g x - k x‖ ≤ D)
    (δ : ℝ) (hδ : 0 < δ)
    (hCDF : (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) ≤ δ) :
    ‖v - w‖ ≤ 2 * D + 12 * |β| * gaussianAbsMoment * Real.sqrt δ := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hd 0)
  let c : ℝ := |β| * gaussianAbsMoment
  have hc : 0 ≤ c := mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  have hmeasure : ‖parisiSlabGradientOperator β μ hab k hk hkb w -
      parisiSlabGradientOperator β ν hab k hk hkb w‖ ≤ 6 * c * Real.sqrt δ := by
    have hbase := norm_parisiSlabGradientOperator_measure_L1_sub_le β μ ν hab ha hb
      k hk hkb w δ hδ
    have hsqrt := Real.sq_sqrt hδ.le
    have hsqrtne : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
    have heq : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
      conv_lhs => arg 1; rw [← hsqrt]
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hsqrtne, mul_one]
    have hscaled := mul_le_mul_of_nonneg_right hCDF
      (inv_nonneg.mpr (Real.sqrt_nonneg δ))
    rw [heq] at hscaled
    have hwpow : ‖w‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg w]
    have hbound : 2 * Real.sqrt δ +
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) *
          (Real.sqrt δ)⁻¹ ≤ 3 * Real.sqrt δ := by linarith
    have hnonneg : 0 ≤ 2 * Real.sqrt δ +
        (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) *
          (Real.sqrt δ)⁻¹ := by
      have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume)
        (by norm_num : (0 : ℝ) ≤ 1) (fun s => norm_nonneg (parisiCDF μ s - parisiCDF ν s))
      positivity
    calc
      _ ≤ c * ‖w‖ ^ 2 / 2 *
          (2 * Real.sqrt δ +
            (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) *
              (Real.sqrt δ)⁻¹) := hbase
      _ ≤ c * 4 / 2 * (3 * Real.sqrt δ) := by gcongr
      _ = _ := by ring
  have hlip := norm_parisiSlabGradientOperator_sub_le β μ hab g hg hgb v w hvnorm hwnorm
  have hterminal := norm_parisiSlabGradientOperator_terminal_sub_le β μ hab g k
    hg hk hgb hkb w D hd
  have htriangle : ‖v - w‖ ≤
      ‖parisiSlabGradientOperator β μ hab g hg hgb v -
        parisiSlabGradientOperator β μ hab g hg hgb w‖ +
      (‖parisiSlabGradientOperator β μ hab g hg hgb w -
          parisiSlabGradientOperator β μ hab k hk hkb w‖ +
        ‖parisiSlabGradientOperator β μ hab k hk hkb w -
          parisiSlabGradientOperator β ν hab k hk hkb w‖) := by
    calc
      _ = ‖parisiSlabGradientOperator β μ hab g hg hgb v -
          parisiSlabGradientOperator β ν hab k hk hkb w‖ := by rw [hv, hw]
      _ ≤ _ := by
        have he : parisiSlabGradientOperator β μ hab g hg hgb v -
            parisiSlabGradientOperator β ν hab k hk hkb w =
            (parisiSlabGradientOperator β μ hab g hg hgb v -
              parisiSlabGradientOperator β μ hab g hg hgb w) +
            ((parisiSlabGradientOperator β μ hab g hg hgb w -
              parisiSlabGradientOperator β μ hab k hk hkb w) +
              (parisiSlabGradientOperator β μ hab k hk hkb w -
                parisiSlabGradientOperator β ν hab k hk hkb w)) := by abel
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_add_le _ _))
  have hs := mul_le_mul_of_nonneg_right hshort (norm_nonneg (v - w))
  have hfinal : ‖v - w‖ ≤ 2 * D + 12 * c * Real.sqrt δ := by linarith
  simpa only [c, mul_assoc] using hfinal

end Paper
