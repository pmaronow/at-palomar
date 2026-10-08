module

public import Paper.ParisiMixDifferentiation
public import Paper.ParisiTerminalStability
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-! # The actual bounded terminal heat operator on a Parisi slab -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

namespace Paper

noncomputable def parisiSlabTerminalHeatValue (β : ℝ)
    {a b : ℝ} (_hab : a ≤ b) (g : ℝ →ᵇ ℝ) : ParisiSlabGradient a b :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => heatSemigroup (β ^ 2 * (b - p.1)) g p.2)
    ((continuous_gaussian_affine_joint g ‖g‖ g.continuous g.norm_coe_le_norm).comp
      (show Continuous (fun p : Icc a b × ℝ => (p.2, β ^ 2 * (b - p.1))) by fun_prop))
    ‖g‖ (fun p => norm_heatSemigroup_le _ g ‖g‖ g.norm_coe_le_norm p.2)

theorem norm_parisiSlabTerminalHeatValue_le (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ →ᵇ ℝ) : ‖parisiSlabTerminalHeatValue β hab g‖ ≤ ‖g‖ := by
  exact (BoundedContinuousFunction.norm_le (norm_nonneg g)).mpr
    (fun p => norm_heatSemigroup_le _ g ‖g‖ g.norm_coe_le_norm p.2)

theorem parisiSlabTerminalHeatValue_add (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) (g k : ℝ →ᵇ ℝ) :
    parisiSlabTerminalHeatValue β hab (g + k) =
      parisiSlabTerminalHeatValue β hab g + parisiSlabTerminalHeatValue β hab k := by
  ext p
  change heatSemigroup _ (g + k) p.2 = heatSemigroup _ g p.2 + heatSemigroup _ k p.2
  exact integral_add
    (integrable_heatSemigroup_integrand _ g g.continuous.measurable ‖g‖ g.norm_coe_le_norm p.2)
    (integrable_heatSemigroup_integrand _ k k.continuous.measurable ‖k‖ k.norm_coe_le_norm p.2)

theorem parisiSlabTerminalHeatValue_smul (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) (g : ℝ →ᵇ ℝ) :
    parisiSlabTerminalHeatValue β hab (c • g) = c • parisiSlabTerminalHeatValue β hab g := by
  ext p
  change heatSemigroup _ (c • g) p.2 = c * heatSemigroup _ g p.2
  exact integral_const_mul _ _

/-- Gaussian heat evolution from bounded terminal data, as an actual bounded linear map. -/
noncomputable def parisiSlabTerminalHeatOperator (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) : (ℝ →ᵇ ℝ) →L[ℝ] ParisiSlabGradient a b :=
  LinearMap.mkContinuous
    { toFun := parisiSlabTerminalHeatValue β hab
      map_add' := parisiSlabTerminalHeatValue_add β hab
      map_smul' := parisiSlabTerminalHeatValue_smul β hab }
    1 (fun g => by simpa using norm_parisiSlabTerminalHeatValue_le β hab g)

@[simp] theorem parisiSlabTerminalHeatOperator_apply (β : ℝ)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ →ᵇ ℝ) (p : Icc a b × ℝ) :
    parisiSlabTerminalHeatOperator β hab g p =
      heatSemigroup (β ^ 2 * (b - p.1)) g p.2 := rfl

theorem parisiSlabGradientOperator_eq_terminalHeat_add_quadratic (β : ℝ) (μ : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ →ᵇ ℝ) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (v : ParisiSlabGradient a b) :
    parisiSlabGradientOperator β μ hab g g.continuous hgb v =
      parisiSlabTerminalHeatOperator β hab g + parisiSlabQuadraticOperator β μ hab v := by
  ext p
  rw [BoundedContinuousFunction.add_apply, parisiSlabTerminalHeatOperator_apply,
    parisiSlabQuadraticOperator_apply]
  rfl

/-- Joint local stability along a genuine probability mixture and varying bounded terminal data. -/
theorem localParisiGradient_terminal_mix_stability (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (g k : ℝ →ᵇ ℝ)
    (hgb : ∀ x, ‖g x‖ ≤ 1) (hkb : ∀ x, ‖k x‖ ≤ 1)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (v y : ParisiSlabGradient a b) (hvnorm : ‖v‖ ≤ 2) (hynorm : ‖y‖ ≤ 2)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hv : parisiSlabGradientOperator β μ hab g g.continuous hgb v = v)
    (hy : parisiSlabGradientOperator β (parisiMix μ ν ε) hab k k.continuous hkb y = y) :
    ‖v - y‖ ≤ 2 * ‖g - k‖ + 8 * parisiSlabContractionConstant β a b * ε := by
  have ht := norm_parisiSlabGradientOperator_terminal_sub_le β μ hab g k
    g.continuous k.continuous hgb hkb y ‖g - k‖ (fun x => (g - k).norm_coe_le_norm x)
  have hl := norm_parisiSlabGradientOperator_sub_le β μ hab g g.continuous hgb
    v y hvnorm hynorm
  have hm := norm_parisiSlabGradientOperator_measure_sub_le β μ (parisiMix μ ν ε) hab
    k k.continuous hkb y ε (fun s => by
      rw [norm_sub_rev]
      exact norm_parisiCDF_mix_sub_le μ ν ε hε s)
  have hsquare : ‖y‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg y]
  have hC := parisiSlabContractionConstant_nonneg β a b
  have hc := mul_le_mul_of_nonneg_right hshort (norm_nonneg (v - y))
  have hparam := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hC hε.1)
  have hn : ‖v - y‖ ≤
      ‖parisiSlabGradientOperator β μ hab g g.continuous hgb v -
        parisiSlabGradientOperator β μ hab g g.continuous hgb y‖ +
      ‖parisiSlabGradientOperator β μ hab g g.continuous hgb y -
        parisiSlabGradientOperator β μ hab k k.continuous hkb y‖ +
      ‖parisiSlabGradientOperator β μ hab k k.continuous hkb y -
        parisiSlabGradientOperator β (parisiMix μ ν ε) hab k k.continuous hkb y‖ := by
    conv_lhs => rw [← hv, ← hy]
    rw [show parisiSlabGradientOperator β μ hab g g.continuous hgb v -
        parisiSlabGradientOperator β (parisiMix μ ν ε) hab k k.continuous hkb y =
      (parisiSlabGradientOperator β μ hab g g.continuous hgb v -
        parisiSlabGradientOperator β μ hab g g.continuous hgb y) +
      ((parisiSlabGradientOperator β μ hab g g.continuous hgb y -
        parisiSlabGradientOperator β μ hab k k.continuous hkb y) +
      (parisiSlabGradientOperator β μ hab k k.continuous hkb y -
        parisiSlabGradientOperator β (parisiMix μ ν ε) hab k k.continuous hkb y)) by abel]
    simpa only [add_assoc] using (norm_add_le
      (parisiSlabGradientOperator β μ hab g g.continuous hgb v -
        parisiSlabGradientOperator β μ hab g g.continuous hgb y)
      ((parisiSlabGradientOperator β μ hab g g.continuous hgb y -
        parisiSlabGradientOperator β μ hab k k.continuous hkb y) +
        (parisiSlabGradientOperator β μ hab k k.continuous hkb y -
          parisiSlabGradientOperator β (parisiMix μ ν ε) hab k k.continuous hkb y)))
      |>.trans (add_le_add_right (norm_add_le _ _) _)
  nlinarith

end Paper
