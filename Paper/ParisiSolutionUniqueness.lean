module

public import Paper.ParisiSolution
public import Paper.ParisiMildUnique

@[expose] public section

/-! # Uniqueness of the constructed bounded continuous mild solution -/

open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Paper

/-- The whole-strip concrete gradient operator has exactly the constructed
bounded continuous fixed point, without a smallness condition on beta. -/
theorem parisiGradientBCF_unique (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1)
    (hfix : parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
      gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le) V = V) :
    V = parisiGradientBCF β μ := by
  let v := parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V
  have hv : Continuous v := continuous_parisiSlabExtend (by norm_num) V
  have hvb : ∀ p, ‖v p‖ ≤ ‖V‖ + 1 := fun p =>
    (norm_parisiSlabExtend_le (by norm_num) V p).trans (by linarith)
  have hwb : ∀ p, ‖parisiGradient β μ p‖ ≤ ‖V‖ + 1 := fun p =>
    (norm_parisiGradient_le_one β μ p).trans (by linarith [norm_nonneg V])
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
        parisiGradientCorrection β μ v 1 t x := by
    intro t ht x
    have h := localParisiGradient_equation β μ (by norm_num : (0 : ℝ) ≤ 1)
      Real.tanh gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      V hfix (⟨t, ht⟩, x)
    simpa only [v, parisiSlabExtend, projIcc_of_mem _ ht] using h
  have he := parisiMildGradient_unique β μ Real.tanh v (parisiGradient β μ)
    hv (continuous_parisiGradient β μ) (‖V‖ + 1) hvb hwb heq
    (fun t ht x => parisiGradient_equation β μ t x ht)
  apply BoundedContinuousFunction.ext
  intro p
  have hp := he p.1 p.1.property p.2
  simpa only [v, parisiGradient, parisiSlabExtend, projIcc_of_mem _ p.1.property] using hp

theorem parisiGradientBCF_eq_of_everySlab (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1)
    (hmild : IsParisiMildOnEverySlab β μ V)
    (hterminal : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (1, x) = Real.tanh x) :
    V = parisiGradientBCF β μ :=
  parisiGradientBCF_unique β μ V
    (globalParisi_fixedPoint_of_everySlab β μ V hV hmild hterminal)

end Paper
