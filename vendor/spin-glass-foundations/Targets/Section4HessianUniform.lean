module

public import Targets.ParisiFourthUniform
public import Targets.ParisiHessianVarianceBound
public import Targets.Section4HessianLipschitz
public import Targets.Section4HessianDerivative
public import Targets.ParisiHessianSquareFlow
public import Targets.Section4ThirdVariation

@[expose] public section

/-!
# Uniform regularity of the actual Hessian-square factor

The actual scalar input has third and fourth spatial derivatives bounded by
6 and 43. One extra scalar step has third and fourth derivatives bounded by
14 and 143; its Hessian variance derivative is bounded by 83. These constants
are independent of depth, field, temperature and split variance.
Gaussian Stein bounds the actual initial Hessian-square derivative by 535;
the fixed outer averages preserve this constant. Endpoint continuity gives
the full closed-interval Lipschitz bound, with no regularity assumption left.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The variance derivative of the actual smoothed Hessian stays bounded as
positive variance tends to zero, with no depth or temperature loss. -/
theorem abs_stepD2Variance_parisiF_le {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    |stepD2Variance (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
      (parisiFThird s β j) m v x| ≤ 83 := by
  convert abs_stepD2Variance_le_of_C4 (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (hasDerivAt_parisiFSecond s β j)
    (hasDerivAt_parisiFThird s β j) (continuous_parisiFFourth s β j).measurable
    (abs_parisiFThird_le_six s β j) (abs_parisiFFourth_le_43 s β j) hm x hv using 1
  norm_num

/-- The old positive-variance third-derivative expression has the genuine
endpoint-safe fourth derivative constructed by the uniform scalar recursion. -/
theorem hasDerivAt_stepD3_parisiF_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (stepD3 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v)
      (stepD4Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
        (parisiFThird s β j) (parisiFFourth s β j) m v x) x := by
  have heq : stepD3 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v =
      stepD3Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
        (parisiFThird s β j) m v := by
    funext y
    exact stepD3_eq_stepD3Uniform (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
      (continuous_parisiFSecond s β j) (continuous_parisiFThird s β j).measurable
      (hasDerivAt_parisiFSecond s β j) (abs_parisiFThird_le_six s β j) hm hv y
  rw [heq]
  exact hasDerivAt_stepD3Uniform_parisiF s β j hm v x

/-- The explicit initial derivative coefficient, prior to the unchanged
outer averages. It is a genuine scalar Gaussian integral, not a free input. -/
noncomputable def section4HessianInitialDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) (v : ℝ) (_x y : Fin 1 → ℝ) : ℝ :=
  splitBaselineHessianDerivative (parisiF s β (k + 2 - r))
    (parisiFDeriv s β (k + 2 - r)) (parisiFSecond s β (k + 2 - r))
    (parisiFThird s β (k + 2 - r)) (s.m (r - 1))
    (β ^ 2 * (s.q r - s.q (r - 1))) (y 0) v

/-- The actual initial Hessian-square derivative is measurable in the fields
and bounded by 535 on the open physical variance interval. All scalar
derivatives and bounds are supplied by the actual Parisi recursion. -/
theorem section4HessianInitialDerivative_props {k : ℕ} (s : RSBScheme k)
    (β : ℝ) {r : ℕ} (hr : r ≤ k + 1) :
    (∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (section4HessianInitialDerivative s β r v x y) v) ∧
    (∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        section4HessianInitialDerivative s β r v p.1 p.2)) ∧
    (∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      |section4HessianInitialDerivative s β r v x y| ≤ 535) := by
  have hm : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  let j := k + 2 - r
  have hA := parisiF_hasLinearGrowth s β j
  have hC2 := (parisiF_C2_props s β j).1
  have hd3 := hasDerivAt_parisiFSecond s β j
  have hc3 := continuous_parisiFThird s β j
  have hb3 := abs_parisiFThird_le_six s β j
  constructor
  · intro v hv x y
    have H := hasDerivAt_splitBaselineHessianSquare_before_ibp hA hC2 hd3 hc3 hb3 hm
      (β ^ 2 * (s.q r - s.q (r - 1))) (y 0)
      (fun w hw z => abs_stepD2Variance_parisiF_le s β j hm z hw.1)
      (fun w hw z => abs_stepD3_parisiF_le_uniform s β j hm hw.1 z) hv
    simpa only [section4VarianceR_initial_eq_scalar_integral, splitBaselineHessianSquare,
      section4HessianInitialDerivative, splitBaselineHessianDerivative, j] using! H
  constructor
  · intro v hv
    exact (measurable_splitBaselineHessianDerivative hA hC2 hd3 hc3 hb3 hm hv).comp
      ((measurable_pi_apply 0).comp measurable_snd)
  · intro v hv x y
    have hD4m := ((continuous_stepD4Uniform_variance_spatial hA hC2
      (continuous_parisiFSecond s β j) hc3 (continuous_parisiFFourth s β j)
      hb3 (abs_parisiFFourth_le_43 s β j) hm).comp
      (by fun_prop : Continuous (fun z : ℝ => (v, z)))).measurable
    have H := abs_splitBaselineHessianDerivative_le hA hC2 hd3 hc3 hb3 hm hv
      (fun z => abs_stepD2Variance_parisiF_le s β j hm z hv.1)
      (abs_stepD3_parisiF_le_uniform s β j hm hv.1)
      (hasDerivAt_stepD3_parisiF_uniform s β j hm hv.1) hD4m
      (abs_stepD4Uniform_parisiF_le s β j hm v) (y 0)
    norm_num only at H
    exact H

/-- The actual final Hessian-square factor is differentiable at every
interior physical variance, with no assumed regularity input. -/
theorem hasDerivAt_section4THessianSquare_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4THessianSquare s β h r)
      (deriv (section4THessianSquare s β h r) v) v := by
  have H := section4HessianInitialDerivative_props s β hr
  exact (hasDerivAt_section4THessianSquare_of_initial_derivative s β h 535 hr0 hr
    (section4HessianInitialDerivative s β r) H.1 H.2.1 H.2.2 hv).differentiableAt.hasDerivAt

/-- Depth-uniform interior bound for the actual Hessian-square derivative. -/
theorem abs_deriv_section4THessianSquare_le_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |deriv (section4THessianSquare s β h r) v| ≤ 535 := by
  have H := section4HessianInitialDerivative_props s β hr
  exact abs_deriv_section4THessianSquare_le_of_initial_derivative s β h 535 hr0 hr
    (section4HessianInitialDerivative s β r) H.1 H.2.1 H.2.2 hv

/-- The actual factor has a universal Lipschitz constant on the full closed
physical variance interval. Both endpoints, zero masses and degenerate
intervals are included; no number of levels occurs in the bound. -/
theorem section4THessianSquare_lipschitz_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤
      535 * |v - w| := by
  have H := section4HessianInitialDerivative_props s β hr
  exact section4THessianSquare_lipschitz_of_initial_derivative s β h 535 hr0 hr
    (section4HessianInitialDerivative s β r) (fun x y v hv => H.1 v hv x y)
    (fun x y v hv => H.2.2 v hv x y) hv hw

/-- Lemma 4.9 on the open physical overlap interval: the genuine third
derivative is bounded by a beta-only constant. At the endpoints the checked
closed-interval Hessian Lipschitz estimate supplies the needed Taylor control. -/
theorem abs_deriv3_section4FirstVariation_le_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) {u : ℝ} (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r)) :
    |deriv (deriv (deriv (section4FirstVariation s β h r))) u| ≤ β ^ 6 * 535 / 2 := by
  have H := section4HessianInitialDerivative_props s β hr
  exact abs_deriv3_section4FirstVariation_le_of_initial_derivative s β h 535 hr0 hr hm
    (section4HessianInitialDerivative s β r) H.1 H.2.1 H.2.2 hu

end SpinGlass.Targets
