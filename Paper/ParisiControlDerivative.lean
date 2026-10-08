module

public import Paper.ParisiControlConvexity
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! # Genuine measure derivatives of the expected fixed-control payoff

An affine extension outside the probability-mixing interval allows ordinary
dominated differentiation. The actual probability variation agrees with this
extension on [0,1], giving its one-sided derivative at zero.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

def parisiAffineControlPayoff {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) : ℝ :=
  Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω +
    t * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω))) -
    (parisiControlCost β μ A ω +
      t * (parisiControlCost β ν A ω - parisiControlCost β μ A ω))

def parisiAffineControlDerivative {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) : ℝ :=
  Real.tanh (h + β * B ω + parisiControlDrift β μ A ω +
    t * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω)) *
      (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω) -
    (parisiControlCost β ν A ω - parisiControlCost β μ A ω)

theorem parisiAffineControlPayoff_hasDerivAt {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) :
    HasDerivAt (fun r => parisiAffineControlPayoff β h B A μ ν r ω)
      (parisiAffineControlDerivative β h B A μ ν t ω) t := by
  let d := parisiControlDrift β ν A ω - parisiControlDrift β μ A ω
  let e := parisiControlCost β ν A ω - parisiControlCost β μ A ω
  have hin : HasDerivAt (fun r => h + β * B ω + parisiControlDrift β μ A ω + r * d) d t := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const d).const_add (h + β * B ω + parisiControlDrift β μ A ω)
  have hc : HasDerivAt (fun r => parisiControlCost β μ A ω + r * e) e t := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const e).const_add (parisiControlCost β μ A ω)
  exact ((hasDerivAt_log_cosh _).comp t hin).sub hc

theorem parisiAffineControlDerivative_norm_le {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) (ω : Ω) :
    ‖parisiAffineControlDerivative β h B A μ ν t ω‖ ≤ 3 * β ^ 2 := by
  have hd : ‖parisiControlDrift β ν A ω - parisiControlDrift β μ A ω‖ ≤ 2 * β ^ 2 := by
    exact (norm_sub_le _ _).trans (by
      have hi := parisiControlDrift_norm_le β μ A hb ω
      have hj := parisiControlDrift_norm_le β ν A hb ω
      linarith)
  have hc : ‖parisiControlCost β ν A ω - parisiControlCost β μ A ω‖ ≤ β ^ 2 := by
    exact (norm_sub_le _ _).trans (by
      have hi := parisiControlCost_norm_le β μ A hb ω
      have hj := parisiControlCost_norm_le β ν A hb ω
      linarith)
  unfold parisiAffineControlDerivative
  calc
    _ ≤ ‖Real.tanh _ * (parisiControlDrift β ν A ω - parisiControlDrift β μ A ω)‖ +
      ‖parisiControlCost β ν A ω - parisiControlCost β μ A ω‖ := norm_sub_le _ _
    _ ≤ 1 * (2 * β ^ 2) + β ^ 2 := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (by simpa only [Real.norm_eq_abs] using
        (Real.abs_tanh_lt_one _).le) hd (norm_nonneg _) zero_le_one) hc
    _ = _ := by ring

theorem parisiAffineControlPayoff_eq_mix {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    parisiAffineControlPayoff β h B A μ ν t ω =
      parisiControlPayoff β h B A (parisiMix μ ν t) ω := by
  unfold parisiAffineControlPayoff parisiControlPayoff
  rw [parisiControlDrift_mix β μ ν A hA hb t ht ω,
    parisiControlCost_mix β μ ν A hA hb t ht ω]
  congr 1
  · congr 1
    congr 1
    ring
  · ring

theorem measurable_parisiAffineControlPayoff {Ω : Type*} [MeasurableSpace Ω]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (μ ν : ParisiMeasure) (t : ℝ) :
    Measurable (parisiAffineControlPayoff β h B A μ ν t) := by
  have hdμ := measurable_parisiControlDrift β μ A hA
  have hdν := measurable_parisiControlDrift β ν A hA
  have hcμ := measurable_parisiControlCost β μ A hA
  have hcν := measurable_parisiControlCost β ν A hA
  exact (((Real.continuous_cosh).log (fun x => (Real.cosh_pos x).ne')).measurable.comp
    (((measurable_const.add (hB.const_mul β)).add hdμ).add
      ((hdν.sub hdμ).const_mul t))).sub
    (hcμ.add ((hcν.sub hcμ).const_mul t))

theorem measurable_parisiAffineControlDerivative {Ω : Type*} [MeasurableSpace Ω]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (μ ν : ParisiMeasure) (t : ℝ) :
    Measurable (parisiAffineControlDerivative β h B A μ ν t) := by
  have hdμ := measurable_parisiControlDrift β μ A hA
  have hdν := measurable_parisiControlDrift β ν A hA
  have hcμ := measurable_parisiControlCost β μ A hA
  have hcν := measurable_parisiControlCost β ν A hA
  exact ((gaussian_continuous_tanh.measurable.comp
    (((measurable_const.add (hB.const_mul β)).add hdμ).add
      ((hdν.sub hdμ).const_mul t))).mul (hdν.sub hdμ)).sub (hcν.sub hcμ)

/-- The exact expected fixed-control probability-mixing derivative. All
dominated-differentiation and absolute-integrability premises are proved. -/
theorem parisiControlObjective_hasDerivWithinAt_mix
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β h : ℝ) (B : Ω → ℝ) (hBm : Measurable B) (hBi : Integrable B P)
    (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun t => parisiControlObjective P β h B A (parisiMix μ ν t))
      (∫ ω, parisiAffineControlDerivative β h B A μ ν 0 ω ∂P) (Icc (0 : ℝ) 1) 0 := by
  have hi : Integrable (parisiAffineControlPayoff β h B A μ ν 0) P := by
    have he : parisiAffineControlPayoff β h B A μ ν 0 = parisiControlPayoff β h B A μ := by
      funext ω
      simp [parisiAffineControlPayoff, parisiControlPayoff]
    rw [he]
    exact integrable_parisiControlPayoff P β h B hBm hBi A hA hb μ
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t ω => parisiAffineControlPayoff β h B A μ ν t ω)
    (F' := fun t ω => parisiAffineControlDerivative β h B A μ ν t ω)
    (bound := fun _ => 3 * β ^ 2) (s := (univ : Set ℝ)) (by simp)
    (.of_forall fun t => (measurable_parisiAffineControlPayoff β h B hBm A hA μ ν t).aestronglyMeasurable)
    hi (measurable_parisiAffineControlDerivative β h B hBm A hA μ ν 0).aestronglyMeasurable
    (.of_forall fun ω t _ => parisiAffineControlDerivative_norm_le β h B A hb μ ν t ω)
    (integrable_const (3 * β ^ 2))
    (.of_forall fun ω t _ => parisiAffineControlPayoff_hasDerivAt β h B A μ ν t ω)).2
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro t ht
    unfold parisiControlObjective
    apply integral_congr_ae
    exact .of_forall fun ω => (parisiAffineControlPayoff_eq_mix β h B A
      (fun ω => hA.comp (measurable_id.prodMk measurable_const)) hb μ ν t ht ω).symm
  · exact ⟨le_rfl, zero_le_one⟩

end Paper
