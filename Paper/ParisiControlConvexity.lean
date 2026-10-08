module

public import Paper.JTVariational
public import Paper.RSContinuity
public import Paper.ParisiMildDerivative
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! # Convexity of the concrete fixed-control Parisi objective

The drift and quadratic cost are affine in the probability measure.  The
strictly convex terminal `log cosh` therefore gives the control comparison
used by the Hamilton--Jacobi verification argument.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace Paper

theorem strictConvexOn_logCosh : StrictConvexOn ℝ univ (fun x : ℝ => Real.log (Real.cosh x)) := by
  apply StrictMono.strictConvexOn_univ_of_deriv
    ((Real.continuous_cosh).log (fun x => (Real.cosh_pos x).ne'))
  have he : deriv (fun x : ℝ => Real.log (Real.cosh x)) = Real.tanh := by
    funext x
    exact (hasDerivAt_log_cosh x).deriv
  rw [he]
  exact tanh_strictMono

def parisiControlDrift {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  β ^ 2 * ∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω

def parisiControlCost {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω ^ 2

def parisiControlPayoff {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (μ : ParisiMeasure) (ω : Ω) : ℝ :=
  Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω)) -
    parisiControlCost β μ A ω

def parisiControlObjective {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (β h : ℝ) (B : Ω → ℝ) (A : ℝ → Ω → ℝ) (μ : ParisiMeasure) : ℝ :=
  ∫ ω, parisiControlPayoff β h B A μ ω ∂P

theorem parisiControl_intervalIntegrable {Ω : Type*} (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    IntervalIntegrable (fun s => parisiCDF μ s * A s ω) volume (0 : ℝ) 1 ∧
      IntervalIntegrable (fun s => parisiCDF μ s * A s ω ^ 2) volume (0 : ℝ) 1 := by
  have hm := parisiCDF_measurable μ
  have hCDF (s : ℝ) : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  constructor
  · exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
      (hm.mul (hA ω)).aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
        change ‖parisiCDF μ s * A s ω‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ (hCDF s) (norm_nonneg _) (hb s ω))
  · exact (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
      (hm.mul ((hA ω).pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        change ‖parisiCDF μ s * A s ω ^ 2‖ ≤ 1
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (hCDF s) (pow_nonneg (norm_nonneg _) 2)
          (pow_le_one₀ (norm_nonneg _) (hb s ω)))

theorem parisiControlDrift_mix {Ω : Type*} (β : ℝ) (μ ν : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    parisiControlDrift β (parisiMix μ ν t) A ω =
      (1 - t) * parisiControlDrift β μ A ω + t * parisiControlDrift β ν A ω := by
  have hi := (parisiControl_intervalIntegrable μ A hA hb ω).1
  have hj := (parisiControl_intervalIntegrable ν A hA hb ω).1
  unfold parisiControlDrift
  simp_rw [parisiCDF_mix μ ν t _ ht]
  calc
    _ = β ^ 2 * ∫ s in (0 : ℝ)..1,
        (1 - t) * (parisiCDF μ s * A s ω) + t * (parisiCDF ν s * A s ω) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring

theorem parisiControlCost_mix {Ω : Type*} (β : ℝ) (μ ν : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    parisiControlCost β (parisiMix μ ν t) A ω =
      (1 - t) * parisiControlCost β μ A ω + t * parisiControlCost β ν A ω := by
  have hi := (parisiControl_intervalIntegrable μ A hA hb ω).2
  have hj := (parisiControl_intervalIntegrable ν A hA hb ω).2
  unfold parisiControlCost
  simp_rw [parisiCDF_mix μ ν t _ ht]
  calc
    _ = β ^ 2 / 2 * ∫ s in (0 : ℝ)..1,
        (1 - t) * (parisiCDF μ s * A s ω ^ 2) + t * (parisiCDF ν s * A s ω ^ 2) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring

/-- Pointwise convexity is proved for the concrete terminal payoff. -/
theorem parisiControlPayoff_mix_le {Ω : Type*} (β h : ℝ) (B : Ω → ℝ)
    (A : ℝ → Ω → ℝ) (hA : ∀ ω, Measurable (fun s => A s ω))
    (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (μ ν : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    parisiControlPayoff β h B A (parisiMix μ ν t) ω ≤
      (1 - t) * parisiControlPayoff β h B A μ ω + t * parisiControlPayoff β h B A ν ω := by
  have hc := strictConvexOn_logCosh.convexOn.2
    (mem_univ (h + β * B ω + parisiControlDrift β μ A ω))
    (mem_univ (h + β * B ω + parisiControlDrift β ν A ω))
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hc
  unfold parisiControlPayoff
  rw [parisiControlDrift_mix β μ ν A hA hb t ht ω,
    parisiControlCost_mix β μ ν A hA hb t ht ω]
  have he : h + β * B ω + ((1 - t) * parisiControlDrift β μ A ω +
      t * parisiControlDrift β ν A ω) =
      (1 - t) * (h + β * B ω + parisiControlDrift β μ A ω) +
        t * (h + β * B ω + parisiControlDrift β ν A ω) := by ring
  rw [he]
  linarith

/-- Genuine expected-objective convexity, with absolute integrability
explicit for each payoff before the integral comparison. -/
theorem parisiControlObjective_mix_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (β h : ℝ) (B : Ω → ℝ) (A : ℝ → Ω → ℝ)
    (hA : ∀ ω, Measurable (fun s => A s ω)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hiμ : Integrable (parisiControlPayoff β h B A μ) P)
    (hiν : Integrable (parisiControlPayoff β h B A ν) P)
    (himix : Integrable (parisiControlPayoff β h B A (parisiMix μ ν t)) P) :
    parisiControlObjective P β h B A (parisiMix μ ν t) ≤
      (1 - t) * parisiControlObjective P β h B A μ + t * parisiControlObjective P β h B A ν := by
  unfold parisiControlObjective
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hiμ.const_mul _) (hiν.const_mul _)]
  exact integral_mono himix ((hiμ.const_mul _).add (hiν.const_mul _))
    (parisiControlPayoff_mix_le β h B A hA hb μ ν t ht)

theorem parisiControlDrift_norm_le {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlDrift β μ A ω‖ ≤ β ^ 2 := by
  have hi : ‖∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω‖ ≤ 1 := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 1) (C := 1) (f := fun s => parisiCDF μ s * A s ω) (fun s _ => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
        exact mul_le_one₀ (parisiCDF_le_one μ s) (norm_nonneg _) (hb s ω))
    simpa using hi
  unfold parisiControlDrift
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg β)]
  simpa using mul_le_mul_of_nonneg_left hi (sq_nonneg β)

theorem parisiControlCost_norm_le {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → Ω → ℝ) (hb : ∀ s ω, ‖A s ω‖ ≤ 1) (ω : Ω) :
    ‖parisiControlCost β μ A ω‖ ≤ β ^ 2 / 2 := by
  have hi : ‖∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω ^ 2‖ ≤ 1 := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 1) (C := 1) (f := fun s => parisiCDF μ s * A s ω ^ 2) (fun s _ => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s), norm_pow]
        exact mul_le_one₀ (parisiCDF_le_one μ s) (pow_nonneg (norm_nonneg _) 2)
          (pow_le_one₀ (norm_nonneg _) (hb s ω)))
    simpa using hi
  unfold parisiControlCost
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  simpa using mul_le_mul_of_nonneg_left hi
    (div_nonneg (sq_nonneg β) (by norm_num : (0 : ℝ) ≤ 2))

theorem measurable_parisiControlDrift {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) : Measurable (parisiControlDrift β μ A) := by
  have hm : Measurable (fun p : ℝ × Ω => parisiCDF μ p.1 * A p.1 p.2) :=
    ((parisiCDF_measurable μ).comp measurable_fst).mul hA
  have hi := hm.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
  have hh := hi.measurable.const_mul (β ^ 2)
  unfold parisiControlDrift
  simpa only [parisiControlDrift, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    using hh

theorem measurable_parisiControlCost {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) : Measurable (parisiControlCost β μ A) := by
  have hm : Measurable (fun p : ℝ × Ω => parisiCDF μ p.1 * A p.1 p.2 ^ 2) :=
    ((parisiCDF_measurable μ).comp measurable_fst).mul (hA.pow_const 2)
  have hi := hm.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
  have hh := hi.measurable.const_mul (β ^ 2 / 2)
  unfold parisiControlCost
  simpa only [parisiControlCost, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    using hh

/-- Bounded measurable controls and an integrable Brownian endpoint give
absolute integrability of the actual terminal objective. -/
theorem integrable_parisiControlPayoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hBm : Measurable B) (hBi : Integrable B P) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ : ParisiMeasure) : Integrable (parisiControlPayoff β h B A μ) P := by
  have hm : Measurable (parisiControlPayoff β h B A μ) := by
    exact (((Real.continuous_cosh).log (fun x => (Real.cosh_pos x).ne')).measurable.comp
      ((measurable_const.add (measurable_const.mul hBm)).add
        (measurable_parisiControlDrift β μ A hA))).sub
      (measurable_parisiControlCost β μ A hA)
  have hi : Integrable (fun ω => |h| + |β| * ‖B ω‖ + β ^ 2 + β ^ 2 / 2) P :=
    (((integrable_const |h|).add (hBi.norm.const_mul |β|)).add
      (integrable_const (β ^ 2))).add (integrable_const (β ^ 2 / 2))
  apply hi.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    calc
      ‖parisiControlPayoff β h B A μ ω‖ ≤
          ‖Real.log (Real.cosh (h + β * B ω + parisiControlDrift β μ A ω))‖ +
            ‖parisiControlCost β μ A ω‖ := norm_sub_le _ _
      _ ≤ ‖h + β * B ω + parisiControlDrift β μ A ω‖ + β ^ 2 / 2 :=
        add_le_add (by simpa only [Real.norm_eq_abs] using
          (norm_logcosh_le_abs (h + β * B ω + parisiControlDrift β μ A ω)))
          (parisiControlCost_norm_le β μ A hb ω)
      _ ≤ ‖h + β * B ω‖ + β ^ 2 + β ^ 2 / 2 :=
        add_le_add ((norm_add_le (h + β * B ω) (parisiControlDrift β μ A ω)).trans
          (add_le_add (le_refl _) (parisiControlDrift_norm_le β μ A hb ω))) (le_refl _)
      _ ≤ |h| + |β| * ‖B ω‖ + β ^ 2 + β ^ 2 / 2 := by
        gcongr
        simpa only [norm_mul, Real.norm_eq_abs] using norm_add_le h (β * B ω)

/-- Convexity for the physical fixed-control objective, with all integral
premises discharged from the control bounds. -/
theorem parisiControlObjective_mix_le_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (β h : ℝ) (B : Ω → ℝ)
    (hBm : Measurable B) (hBi : Integrable B P) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s ω, ‖A s ω‖ ≤ 1)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiControlObjective P β h B A (parisiMix μ ν t) ≤
      (1 - t) * parisiControlObjective P β h B A μ +
        t * parisiControlObjective P β h B A ν := by
  exact parisiControlObjective_mix_le P β h B A
    (fun ω => hA.comp (measurable_id.prodMk measurable_const)) hb μ ν t ht
    (integrable_parisiControlPayoff P β h B hBm hBi A hA hb μ)
    (integrable_parisiControlPayoff P β h B hBm hBi A hA hb ν)
    (integrable_parisiControlPayoff P β h B hBm hBi A hA hb (parisiMix μ ν t))

end Paper
