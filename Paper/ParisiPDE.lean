module

public import Paper.GaussianHeat
public import Paper.RSFunctional
public import Paper.GaussianConvolution
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The weak Parisi equation and its concrete Duhamel operator

The potential has linear growth and is not required to be bounded.  The
weak spatial gradient is separately represented and essentially bounded.
Tests for the terminal equation have compact support away from time zero;
their support is allowed to meet time one, so the terminal trace is retained.

The Gaussian operators below are actual integrals, not abstract kernels.
The estimates are the preliminary bounds for a bounded-gradient fixed point.
No existence or uniqueness of the general weak PDE is asserted in this file.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace Paper

/-- Lebesgue measure on the time strip used by the distributional equation. -/
noncomputable def parisiSpaceTime : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod volume

/-- Spatial and time derivatives of a smooth test on the full plane. -/
noncomputable def parisiTestX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => φ (p.1, x)) p.2

noncomputable def parisiTestXX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => parisiTestX φ (p.1, x)) p.2

noncomputable def parisiTestT (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => φ (t, p.2)) p.1

/-- Distributional spatial derivative on the open time strip.
Integrability is explicit so that an undefined Bochner integral cannot
trivially satisfy the distributional identity. -/
def IsParisiWeakGradient (u v : ℝ × ℝ → ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} →
    Integrable (fun p => u p * parisiTestX φ p + v p * φ p) parisiSpaceTime ∧
      (∫ p, u p * parisiTestX φ p + v p * φ p ∂parisiSpaceTime) = 0

/-- The weak terminal-value problem in Jagannath--Tobasco's solution class.
The smooth compactly supported tests are supported in positive times, but
need not vanish at the terminal boundary. -/
structure IsParisiWeakSolution (β : ℝ) (μ : ParisiMeasure)
    (u v : ℝ × ℝ → ℝ) : Prop where
  continuous_potential : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ)
  measurable_gradient : AEStronglyMeasurable v parisiSpaceTime
  bounded_gradient : ∃ M : ℝ, ∀ᵐ p ∂parisiSpaceTime, ‖v p‖ ≤ M
  weak_gradient : IsParisiWeakGradient u v
  terminal : ∀ x : ℝ, u (1, x) = Real.log (Real.cosh x)
  equation : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1} →
    Integrable (fun p => -u p * parisiTestT φ p + β ^ 2 / 2 *
      (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)) parisiSpaceTime ∧
    Integrable (fun x => φ (1, x) * Real.log (Real.cosh x)) ∧
    (∫ p, -u p * parisiTestT φ p + β ^ 2 / 2 *
      (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)
      ∂parisiSpaceTime) +
      (∫ x, φ (1, x) * Real.log (Real.cosh x)) = 0

theorem parisiCDF_measurable (μ : ParisiMeasure) : Measurable (parisiCDF μ) :=
  (parisiCDF_monotone μ).measurable

/-- Uniform bounds survive genuine Gaussian averaging. -/
theorem norm_heatSemigroup_le (ell : ℝ) (f : ℝ → ℝ) (M : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) : ‖heatSemigroup ell f x‖ ≤ M := by
  unfold heatSemigroup gaussianExpectation
  simpa using norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1) (Filter.Eventually.of_forall
    (fun z : ℝ => hb (x + Real.sqrt ell * z)))

theorem integrable_heatSemigroup_integrand (ell : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Integrable (fun z : ℝ => f (x + Real.sqrt ell * z)) (gaussianReal 0 1) :=
  (integrable_const M).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hb _))

theorem heatSemigroup_sub (ell : ℝ) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (M N : ℝ)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) (x : ℝ) :
    heatSemigroup ell (fun y => f y - g y) x =
      heatSemigroup ell f x - heatSemigroup ell g x := by
  exact integral_sub (integrable_heatSemigroup_integrand ell f hf M hfb x)
    (integrable_heatSemigroup_integrand ell g hg N hgb x)

theorem norm_square_sub_le {a b R D : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hab : ‖a - b‖ ≤ D) : ‖a ^ 2 - b ^ 2‖ ≤ 2 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have hD : 0 ≤ D := (norm_nonneg (a - b)).trans hab
  calc
    ‖a ^ 2 - b ^ 2‖ = ‖a - b‖ * ‖a + b‖ := by
      rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, norm_mul]
    _ ≤ D * (2 * R) := mul_le_mul hab ((norm_add_le a b).trans (by linarith))
      (norm_nonneg _) hD
    _ = 2 * R * D := by ring

/-- The nonlinear source in the backward mild equation, before integration
in time. -/
noncomputable def parisiHeatSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x s : ℝ) : ℝ :=
  parisiCDF μ s * heatSemigroup (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x

theorem parisiHeatSource_measurable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (t x : ℝ) :
    Measurable (parisiHeatSource β μ v t x) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      v (p.1, x + Real.sqrt (β ^ 2 * (p.1 - t)) * p.2) ^ 2) := by
    exact (hv.comp (by fun_prop)).pow_const 2
  exact (parisiCDF_measurable μ).mul
    (hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable

theorem norm_parisiHeatSource_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (t x s : ℝ) :
    ‖parisiHeatSource β μ v t x s‖ ≤ R ^ 2 := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := by
    intro y
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  calc
    ‖parisiHeatSource β μ v t x s‖ = ‖parisiCDF μ s‖ *
      ‖heatSemigroup (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x‖ := norm_mul _ _
    _ ≤ 1 * R ^ 2 := mul_le_mul hm (norm_heatSemigroup_le _ _ _ hsq _)
      (norm_nonneg _) (by norm_num)
    _ = R ^ 2 := one_mul _

theorem parisiHeatSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ)
    (hb : ∀ p, ‖v p‖ ≤ R) (t x a b : ℝ) :
    IntervalIntegrable (parisiHeatSource β μ v t x) volume a b :=
  (intervalIntegrable_const : IntervalIntegrable (fun _ => R ^ 2) volume a b).mono_fun'
    (parisiHeatSource_measurable β μ v hv t x).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_parisiHeatSource_le β μ v R hb t x))

/-- The nonlinear correction to the heat evolution of the terminal value. -/
noncomputable def parisiDuhamelCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) : ℝ :=
  β ^ 2 / 2 * ∫ s in t..b, parisiHeatSource β μ v t x s

/-- The actual backward Duhamel formula with the paper's terminal data. -/
noncomputable def parisiDuhamelPotential (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x : ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * (1 - t)) (fun y => Real.log (Real.cosh y)) x +
    parisiDuhamelCorrection β μ v 1 t x

theorem norm_parisiDuhamelCorrection_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiDuhamelCorrection β μ v b t x‖ ≤ β ^ 2 / 2 * (b - t) * R ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := b) (fun s _ => norm_parisiHeatSource_le β μ v R hb t x s)
  rw [abs_of_nonneg (sub_nonneg.mpr htb)] at h
  unfold parisiDuhamelCorrection
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  calc
    β ^ 2 / 2 * ‖∫ s in t..b, parisiHeatSource β μ v t x s‖ ≤
      β ^ 2 / 2 * (R ^ 2 * (b - t)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = β ^ 2 / 2 * (b - t) * R ^ 2 := by ring

theorem norm_parisiHeatSource_sub_le (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R D : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (hd : ∀ p, ‖v p - w p‖ ≤ D) (t x s : ℝ) :
    ‖parisiHeatSource β μ v t x s - parisiHeatSource β μ w t x s‖ ≤ 2 * R * D := by
  have hsqv : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvb _) 2
  have hsqw : ∀ y, ‖w (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwb _) 2
  have hsqdiff : ∀ y, ‖v (s, y) ^ 2 - w (s, y) ^ 2‖ ≤ 2 * R * D :=
    fun y => norm_square_sub_le (hvb _) (hwb _) (hd _)
  have hheat : ‖heatSemigroup (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x -
      heatSemigroup (β ^ 2 * (s - t)) (fun y => w (s, y) ^ 2) x‖ ≤ 2 * R * D := by
    rw [← heatSemigroup_sub (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2)
      (fun y => w (s, y) ^ 2) ((hv.comp (by fun_prop)).pow_const 2)
      ((hw.comp (by fun_prop)).pow_const 2) (R ^ 2) (R ^ 2) hsqv hsqw]
    exact norm_heatSemigroup_le _ _ _ hsqdiff _
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  unfold parisiHeatSource
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul hm hheat (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The nonlinear potential correction is locally Lipschitz in the bounded
gradient, with an explicit time-length factor. -/
theorem norm_parisiDuhamelCorrection_sub_le (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R D : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (hd : ∀ p, ‖v p - w p‖ ≤ D) (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiDuhamelCorrection β μ v b t x -
      parisiDuhamelCorrection β μ w b t x‖ ≤ β ^ 2 * (b - t) * R * D := by
  have hi := parisiHeatSource_intervalIntegrable β μ v hv R hvb t x t b
  have hj := parisiHeatSource_intervalIntegrable β μ w hw R hwb t x t b
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := b) (fun s _ => norm_parisiHeatSource_sub_le β μ v w hv hw
      R D hvb hwb hd t x s)
  rw [abs_of_nonneg (sub_nonneg.mpr htb)] at h
  unfold parisiDuhamelCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  calc
    β ^ 2 / 2 * ‖∫ s in t..b, parisiHeatSource β μ v t x s -
      parisiHeatSource β μ w t x s‖ ≤ β ^ 2 / 2 * ((2 * R * D) * (b - t)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = β ^ 2 * (b - t) * R * D := by ring

/-- The finite first absolute moment that controls Gaussian smoothing. -/
noncomputable def gaussianAbsMoment : ℝ := gaussianExpectation (fun z => ‖z‖)

theorem gaussianAbsMoment_nonneg : 0 ≤ gaussianAbsMoment :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The concrete spatial heat-gradient integral.  Its identification with a
derivative of Gaussian smoothing is a separate analytic theorem. -/
noncomputable def heatGradient (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt ell)⁻¹ * gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))

theorem integrable_heatGradient_integrand (ell : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    Integrable (fun z : ℝ => z * f (x + Real.sqrt ell * z)) (gaussianReal 0 1) :=
  integrable_standardGaussian_id.mul_bdd (hf.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hb _))

theorem norm_heatGradient_le (ell : ℝ) (f : ℝ → ℝ) (M : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    ‖heatGradient ell f x‖ ≤ (Real.sqrt ell)⁻¹ * gaussianAbsMoment * M := by
  have h : ‖gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))‖ ≤
      M * gaussianAbsMoment := by
    have hb' : ∀ᵐ z ∂gaussianReal 0 1,
        ‖z * f (x + Real.sqrt ell * z)‖ ≤ M * ‖z‖ :=
      Filter.Eventually.of_forall fun z => by
        rw [norm_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg z)
    have hi := norm_integral_le_of_norm_le
      (integrable_standardGaussian_id.norm.const_mul M) hb'
    simpa [gaussianExpectation, gaussianAbsMoment, integral_const_mul] using hi
  unfold heatGradient
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    (Real.sqrt ell)⁻¹ * ‖gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))‖ ≤
      (Real.sqrt ell)⁻¹ * (M * gaussianAbsMoment) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Real.sqrt ell)⁻¹ * gaussianAbsMoment * M := by ring

theorem heatGradient_sub (ell : ℝ) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (M N : ℝ)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) (x : ℝ) :
    heatGradient ell (fun y => f y - g y) x =
      heatGradient ell f x - heatGradient ell g x := by
  unfold heatGradient gaussianExpectation
  simp_rw [mul_sub]
  rw [integral_sub (integrable_heatGradient_integrand ell f hf M hfb x)
    (integrable_heatGradient_integrand ell g hg N hgb x), mul_sub]

theorem intervalIntegrable_inv_sqrt_sub (t b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (fun s => (Real.sqrt (s - t))⁻¹) volume t b := by
  have heq : EqOn (fun s => (Real.sqrt (s - t))⁻¹)
      (fun s => (s - t) ^ (-(1 / 2 : ℝ))) (uIoo t b) := by
    intro s hs
    rw [uIoo_of_le htb] at hs
    dsimp only
    rw [Real.rpow_neg (sub_nonneg.mpr hs.1.le), ← Real.sqrt_eq_rpow]
  apply (intervalIntegrable_congr_uIoo heq).mpr
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b - t)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_right t
  simpa using hi

/-- The heat-gradient singularity has a finite and explicit time integral. -/
theorem integral_inv_sqrt_sub (t b : ℝ) (htb : t ≤ b) :
    (∫ s in t..b, (Real.sqrt (s - t))⁻¹) = 2 * Real.sqrt (b - t) := by
  have heq : EqOn (fun s => (Real.sqrt (s - t))⁻¹)
      (fun s => (s - t) ^ (-(1 / 2 : ℝ))) (uIoo t b) := by
    intro s hs
    rw [uIoo_of_le htb] at hs
    dsimp only
    rw [Real.rpow_neg (sub_nonneg.mpr hs.1.le), ← Real.sqrt_eq_rpow]
  rw [intervalIntegral.integral_congr_uIoo heq,
    intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) t]
  simp only [sub_self]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

/-- Source term for the bounded-gradient Duhamel fixed point. -/
noncomputable def parisiGradientSource (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (t x s : ℝ) : ℝ :=
  parisiCDF μ s * heatGradient (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x

theorem parisiGradientSource_measurable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (t x : ℝ) :
    Measurable (parisiGradientSource β μ v t x) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      p.2 * v (p.1, x + Real.sqrt (β ^ 2 * (p.1 - t)) * p.2) ^ 2) := by
    exact measurable_snd.mul ((hv.comp (by fun_prop)).pow_const 2)
  have hi := (hm.stronglyMeasurable.integral_prod_right'
    (ν := gaussianReal 0 1)).measurable
  have hs : Measurable (fun s : ℝ => (Real.sqrt (β ^ 2 * (s - t)))⁻¹) := by fun_prop
  exact (parisiCDF_measurable μ).mul (hs.mul hi)

theorem norm_parisiGradientSource_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) (t x s : ℝ) :
    ‖parisiGradientSource β μ v t x s‖ ≤
      (|β|⁻¹ * gaussianAbsMoment * R ^ 2) * (Real.sqrt (s - t))⁻¹ := by
  have hsq : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 2
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  unfold parisiGradientSource
  rw [norm_mul]
  calc
    ‖parisiCDF μ s‖ * ‖heatGradient (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x‖ ≤
      1 * ((Real.sqrt (β ^ 2 * (s - t)))⁻¹ * gaussianAbsMoment * R ^ 2) :=
        mul_le_mul hm (norm_heatGradient_le _ _ _ hsq _) (norm_nonneg _) (by norm_num)
    _ = (|β|⁻¹ * gaussianAbsMoment * R ^ 2) * (Real.sqrt (s - t))⁻¹ := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
      ring

theorem parisiGradientSource_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (R : ℝ)
    (hb : ∀ p, ‖v p‖ ≤ R) (t x b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (parisiGradientSource β μ v t x) volume t b :=
  ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
    (|β|⁻¹ * gaussianAbsMoment * R ^ 2)).mono_fun'
      (parisiGradientSource_measurable β μ v hv t x).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_parisiGradientSource_le β μ v R hb t x))

noncomputable def parisiGradientCorrection (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (b t x : ℝ) : ℝ :=
  β ^ 2 / 2 * ∫ s in t..b, parisiGradientSource β μ v t x s

/-- The local gradient correction has size proportional to the square root
of the time interval, including the degenerate value `β = 0`. -/
theorem norm_parisiGradientCorrection_le (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiGradientCorrection β μ v b t x‖ ≤
      |β| * gaussianAbsMoment * R ^ 2 * Real.sqrt (b - t) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le htb
    (Filter.Eventually.of_forall fun s _ => norm_parisiGradientSource_le β μ v R hb t x s)
    ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
      (|β|⁻¹ * gaussianAbsMoment * R ^ 2))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t b htb] at h
  unfold parisiGradientCorrection
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  calc
    β ^ 2 / 2 * ‖∫ s in t..b, parisiGradientSource β μ v t x s‖ ≤
      β ^ 2 / 2 * ((|β|⁻¹ * gaussianAbsMoment * R ^ 2) * (2 * Real.sqrt (b - t))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = |β| * gaussianAbsMoment * R ^ 2 * Real.sqrt (b - t) := by
      by_cases hβ : β = 0
      · simp [hβ]
      · have habs : |β| ≠ 0 := abs_ne_zero.mpr hβ
        rw [← sq_abs β]
        field_simp

theorem norm_parisiGradientSource_sub_le (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R D : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (hd : ∀ p, ‖v p - w p‖ ≤ D) (t x s : ℝ) :
    ‖parisiGradientSource β μ v t x s - parisiGradientSource β μ w t x s‖ ≤
      (|β|⁻¹ * gaussianAbsMoment * (2 * R * D)) * (Real.sqrt (s - t))⁻¹ := by
  have hsqv : ∀ y, ‖v (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvb _) 2
  have hsqw : ∀ y, ‖w (s, y) ^ 2‖ ≤ R ^ 2 := fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwb _) 2
  have hsqdiff : ∀ y, ‖v (s, y) ^ 2 - w (s, y) ^ 2‖ ≤ 2 * R * D :=
    fun y => norm_square_sub_le (hvb _) (hwb _) (hd _)
  have hheat : ‖heatGradient (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x -
      heatGradient (β ^ 2 * (s - t)) (fun y => w (s, y) ^ 2) x‖ ≤
        (Real.sqrt (β ^ 2 * (s - t)))⁻¹ * gaussianAbsMoment * (2 * R * D) := by
    rw [← heatGradient_sub (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2)
      (fun y => w (s, y) ^ 2) ((hv.comp (by fun_prop)).pow_const 2)
      ((hw.comp (by fun_prop)).pow_const 2) (R ^ 2) (R ^ 2) hsqv hsqw]
    exact norm_heatGradient_le _ _ _ hsqdiff _
  have hm : ‖parisiCDF μ s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ s)]
    exact parisiCDF_le_one μ s
  unfold parisiGradientSource
  rw [← mul_sub, norm_mul]
  calc
    ‖parisiCDF μ s‖ * ‖heatGradient (β ^ 2 * (s - t)) (fun y => v (s, y) ^ 2) x -
      heatGradient (β ^ 2 * (s - t)) (fun y => w (s, y) ^ 2) x‖ ≤
        1 * ((Real.sqrt (β ^ 2 * (s - t)))⁻¹ * gaussianAbsMoment * (2 * R * D)) :=
          mul_le_mul hm hheat (norm_nonneg _) (by norm_num)
    _ = (|β|⁻¹ * gaussianAbsMoment * (2 * R * D)) * (Real.sqrt (s - t))⁻¹ := by
      rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
      ring

/-- The bounded-gradient Duhamel correction has the square-root-time
Lipschitz constant used in the short-time fixed-point construction. -/
theorem norm_parisiGradientCorrection_sub_le (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R D : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (hd : ∀ p, ‖v p - w p‖ ≤ D) (b t x : ℝ) (htb : t ≤ b) :
    ‖parisiGradientCorrection β μ v b t x - parisiGradientCorrection β μ w b t x‖ ≤
      2 * |β| * gaussianAbsMoment * R * D * Real.sqrt (b - t) := by
  have hi := parisiGradientSource_intervalIntegrable β μ v hv R hvb t x b htb
  have hj := parisiGradientSource_intervalIntegrable β μ w hw R hwb t x b htb
  have h := intervalIntegral.norm_integral_le_of_norm_le htb
    (Filter.Eventually.of_forall fun s _ =>
      norm_parisiGradientSource_sub_le β μ v w hv hw R D hvb hwb hd t x s)
    ((intervalIntegrable_inv_sqrt_sub t b htb).const_mul
      (|β|⁻¹ * gaussianAbsMoment * (2 * R * D)))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t b htb] at h
  unfold parisiGradientCorrection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  calc
    β ^ 2 / 2 * ‖∫ s in t..b, parisiGradientSource β μ v t x s -
      parisiGradientSource β μ w t x s‖ ≤ β ^ 2 / 2 *
        ((|β|⁻¹ * gaussianAbsMoment * (2 * R * D)) * (2 * Real.sqrt (b - t))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * |β| * gaussianAbsMoment * R * D * Real.sqrt (b - t) := by
      by_cases hβ : β = 0
      · simp [hβ]
      · have habs : |β| ≠ 0 := abs_ne_zero.mpr hβ
        rw [← sq_abs β]
        field_simp

@[simp] theorem parisiDuhamelPotential_terminal (β : ℝ) (μ : ParisiMeasure)
    (v : ℝ × ℝ → ℝ) (x : ℝ) :
    parisiDuhamelPotential β μ v 1 x = Real.log (Real.cosh x) := by
  simp [parisiDuhamelPotential, parisiDuhamelCorrection, heatSemigroup, gaussianExpectation]

end Paper
