module

public import Paper.ParisiSolution

@[expose] public section

/-! # Every time-slab equation for the constructed general-measure gradient

The genuine finite Cole--Hopf gradients satisfy every slab equation. Their
proved uniform limit retains these equations, including the changing
terminal gradient at each slab endpoint.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

namespace Paper

theorem norm_parisiGlobalRestrict_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (V W : ParisiSlabGradient 0 1) :
    ‖parisiGlobalRestrict ha hb V - parisiGlobalRestrict ha hb W‖ ≤ ‖V - W‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (V - W))).mpr
  intro p
  exact (V - W).norm_coe_le_norm _

/-- Actual uniform grid limits retain the local equations at every terminal time. -/
theorem isParisiMildOnEverySlab_of_grid_limit (β : ℝ) (μ : ParisiMeasure)
    (W : ℕ → ParisiSlabGradient 0 1) (hW : ∀ n, ‖W n‖ ≤ 1)
    (hmild : ∀ n, IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (W n))
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1) (hlim : Tendsto W atTop (𝓝 V)) :
    IsParisiMildOnEverySlab β μ V := by
  intro b hb t ht x
  let RV := parisiGlobalRestrict (le_refl (0 : ℝ)) hb.2 V
  let RW := fun n => parisiGlobalRestrict (le_refl (0 : ℝ)) hb.2 (W n)
  let g := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (b, y)
  let k := fun n y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (b, y)
  have hg : Continuous g := (continuous_parisiSlabExtend (by norm_num) V).comp (by fun_prop)
  have hk : ∀ n, Continuous (k n) := fun n =>
    (continuous_parisiSlabExtend (by norm_num) (W n)).comp (by fun_prop)
  have hgb : ∀ y, ‖g y‖ ≤ 1 := fun y =>
    (norm_parisiSlabExtend_le (by norm_num) V (b, y)).trans hV
  have hkb : ∀ n y, ‖k n y‖ ≤ 1 := fun n y =>
    (norm_parisiSlabExtend_le (by norm_num) (W n) (b, y)).trans (hW n)
  let G := parisiSlabGradientOperator β μ hb.1 g hg hgb
  have hRV : ‖RV‖ ≤ 2 := (norm_parisiGlobalRestrict_le _ _ V).trans (hV.trans (by norm_num))
  have hRW : ∀ n, ‖RW n‖ ≤ 2 := fun n =>
    (norm_parisiGlobalRestrict_le _ _ (W n)).trans ((hW n).trans (by norm_num))
  have hnormlim : Tendsto (fun n => ‖V - W n‖) atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun n => V - W n) atTop (𝓝 (V - V)) := tendsto_const_nhds.sub hlim
    simpa using hh.norm
  have hmeshlim : Tendsto (fun n : ℕ => Real.sqrt (1 / (n + 1 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  have herrlim : Tendsto (fun n =>
      (4 * parisiSlabContractionConstant β 0 b + 2) * ‖V - W n‖ +
      6 * |β| * gaussianAbsMoment * Real.sqrt (1 / (n + 1 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hnormlim).add (tendsto_const_nhds.mul hmeshlim)
  have hbound (n : ℕ) : ‖G RV - RV‖ ≤
      (4 * parisiSlabContractionConstant β 0 b + 2) * ‖V - W n‖ +
      6 * |β| * gaussianAbsMoment * Real.sqrt (1 / (n + 1 : ℕ)) := by
    have hn := globalParisiRestriction_fixedPoint β (parisiGridMeasure μ n)
      (W n) (hW n) (hmild n) hb.1 (le_refl 0) hb.2
    have hmeasure := norm_parisiSlabGradientOperator_measure_mesh_sub_le β μ (parisiGridMeasure μ n)
      hb.1 (le_refl 0) hb.2 (k n) (hk n) (hkb n) (RW n) (hRW n)
      (1 / (n + 1 : ℕ)) (by positivity) (parisiCDF_grid_norm_integral_le μ n)
    rw [hn] at hmeasure
    have hterminal := norm_parisiSlabGradientOperator_terminal_sub_le β μ hb.1 g (k n)
      hg (hk n) hgb (hkb n) (RW n) ‖V - W n‖
      (fun y => norm_parisiSlabExtend_sub_le (by norm_num) V (W n) (b, y))
    have hlip := norm_parisiSlabGradientOperator_sub_le β μ hb.1 g hg hgb RV (RW n) hRV (hRW n)
    have hrestrict := norm_parisiGlobalRestrict_sub_le (le_refl (0 : ℝ)) hb.2 V (W n)
    have hC := parisiSlabContractionConstant_nonneg β 0 b
    have hscaled := mul_le_mul_of_nonneg_left hrestrict (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
    have htriangle : ‖G RV - RV‖ ≤ ‖G RV - G (RW n)‖ +
        (‖G (RW n) - parisiSlabGradientOperator β μ hb.1 (k n) (hk n) (hkb n) (RW n)‖ +
        (‖parisiSlabGradientOperator β μ hb.1 (k n) (hk n) (hkb n) (RW n) - RW n‖ +
          ‖RW n - RV‖)) := by
      calc
        _ ≤ ‖G RV - G (RW n)‖ + ‖G (RW n) - RV‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖G RV - G (RW n)‖ +
            (‖G (RW n) - parisiSlabGradientOperator β μ hb.1 (k n) (hk n) (hkb n) (RW n)‖ +
              ‖parisiSlabGradientOperator β μ hb.1 (k n) (hk n) (hkb n) (RW n) - RV‖) :=
          add_le_add (le_refl _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
        _ ≤ _ := add_le_add (le_refl _)
          (add_le_add (le_refl _) (norm_sub_le_norm_sub_add_norm_sub _ _ _))
    rw [norm_sub_rev (RW n) RV] at htriangle
    change ‖RV - RW n‖ ≤ ‖V - W n‖ at hrestrict
    linarith
  have hz : ‖G RV - RV‖ ≤ 0 := ge_of_tendsto herrlim (.of_forall hbound)
  have hfix : G RV = RV := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))
  have heq := localParisiGradient_equation β μ hb.1 g hg hgb RV hfix (⟨t, ht⟩, x)
  rw [parisiGlobalRestrict_apply] at heq
  rw [parisiGradientCorrection_congr β μ (parisiSlabExtend hb.1 RV)
    (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V) b t x ht.2] at heq
  · exact heq
  · intro s hs y
    unfold parisiSlabExtend
    have hs' : s ∈ Icc (0 : ℝ) b := ⟨ht.1.trans hs.1, hs.2⟩
    rw [projIcc_of_mem hb.1 hs']
    exact parisiGlobalRestrict_apply _ _ V (⟨s, hs'⟩, y)

theorem parisiGradientBCF_mildOnEverySlab (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    IsParisiMildOnEverySlab β μ (parisiGradientBCF β μ) :=
  isParisiMildOnEverySlab_of_grid_limit β μ (parisiGridGradientApproximation β μ)
    (norm_parisiGridGradientApproximation_le_one β μ) (parisiGridGradientApproximation_mild β hβ μ)
    (parisiGradientBCF β μ) (norm_parisiGradientBCF_le_one β μ) (tendsto_parisiGridGradient β hβ μ)

theorem parisiGradientBCF_zero_apply (μ : ParisiMeasure) (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiGradientBCF 0 μ p = Real.tanh p.2 := by
  have h := congrArg (fun v : ParisiSlabGradient 0 1 => v p) (parisiGradientBCF_fixedPoint 0 μ)
  change parisiSlabGradientValue 0 μ (by norm_num : (0 : ℝ) ≤ 1)
    Real.tanh (parisiGradientBCF 0 μ) p = _ at h
  simpa [parisiSlabGradientValue, parisiNormalizedGradientCorrection,
    heatSemigroup, gaussianExpectation] using h.symm

/-- The constructed gradient obeys every slab equation, including zero inverse temperature. -/
theorem parisiGradientBCF_mildOnEverySlab_all (β : ℝ) (μ : ParisiMeasure) :
    IsParisiMildOnEverySlab β μ (parisiGradientBCF β μ) := by
  by_cases hβ : β = 0
  · subst β
    intro b hb t ht x
    simp [parisiSlabExtend, parisiGradientBCF_zero_apply, parisiGradientCorrection,
      heatSemigroup, gaussianExpectation]
  · exact parisiGradientBCF_mildOnEverySlab β hβ μ

/-- The actual constructed global solution is the local fixed point on any time slab. -/
theorem parisiGradientBCF_restriction_fixedPoint (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    parisiSlabGradientOperator β μ hab
      (fun y => parisiGradient β μ (b, y))
      ((continuous_parisiGradient β μ).comp (by fun_prop))
      (fun y => norm_parisiGradient_le_one β μ (b, y))
      (parisiGlobalRestrict ha hb (parisiGradientBCF β μ)) =
        parisiGlobalRestrict ha hb (parisiGradientBCF β μ) :=
  globalParisiRestriction_fixedPoint β μ (parisiGradientBCF β μ)
    (norm_parisiGradientBCF_le_one β μ) (parisiGradientBCF_mildOnEverySlab_all β μ) hab ha hb

end Paper

