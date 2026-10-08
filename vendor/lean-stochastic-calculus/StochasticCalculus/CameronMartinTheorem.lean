/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.CameronMartin
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# The Cameron--Martin theorem

Translation of a Gaussian measure by a Cameron--Martin vector preserves its measure class.
More precisely, if `h` belongs to the Cameron--Martin space, then the translated law has density

`exp (h(x) - ‖h‖² / 2)`

with respect to the original Gaussian measure.  Here `h(x)` means the canonical `L²(μ)`
representative supplied by the first-chaos construction in `StochasticCalculus.CameronMartin`.

The analytic shift-versus-tilt step is `translated_eq_tilted`: both the translated and the
tilted measure give every continuous linear functional `L` the Gaussian law with mean
`L (mean μ) + ⟪ofDual μ L, h⟫` and variance `‖ofDual μ L‖²` (`map_translated_dual`,
`map_tilted_dual`, the latter through the moment generating function `mgf_tilted_dual`), so
they coincide by uniqueness of characteristic functions.  This file proves that the closed
first chaos is Gaussian and derives the normalized density formula from that step, then proves
its measure-theoretic consequences: mutual absolute continuity, the Radon--Nikodym derivative,
and the almost-everywhere logarithmic density formula used by the closability rung.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

noncomputable section

universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8














































































namespace StochasticCalculus.CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

private theorem map_eq_gaussianReal_of_mgf_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {X : Ω → ℝ} (hX : AEMeasurable X ν) (m : ℝ) (v : ℝ≥0)
    (hmgf : mgf X ν = mgf id (gaussianReal m v)) :
    ν.map X = gaussianReal m v := by
  have heqOn := eqOn_complexMGF_of_mgf hmgf.symm
  have hcomplex : complexMGF id (gaussianReal m v) = complexMGF X ν := by
    funext z
    apply heqOn
    simp only [integrableExpSet_id_gaussianReal, interior_univ, Set.mem_univ, Set.ofPred_true]
  have hmap := Measure.ext_of_complexMGF_eq aemeasurable_id hX hcomplex
  simpa only [Measure.map_id] using hmap.symm

private theorem measure_eq_of_forall_map_dual_eq
    {μ ν : Measure W} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hproj : ∀ L : StrongDual ℝ W, μ.map L = ν.map L) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hproj L]

/-- The exponent in the Cameron--Martin density. -/
def densityExponent (h : Space μ) (x : W) : ℝ :=
  (h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2

/-- The real-valued, strictly positive Cameron--Martin density. -/
def realDensity (h : Space μ) (x : W) : ℝ :=
  Real.exp (densityExponent μ h x)

/-- The Cameron--Martin density, as an `ℝ≥0∞`-valued function suitable for `withDensity`. -/
def density (h : Space μ) (x : W) : ℝ≥0∞ :=
  ENNReal.ofReal (realDensity μ h x)

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The canonical representative of the density exponent is measurable. -/
theorem measurable_densityExponent (h : Space μ) :
    Measurable (densityExponent μ h) := by
  exact (Lp.stronglyMeasurable (h : Lp ℝ 2 μ)).measurable.sub_const _

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued Cameron--Martin density is measurable. -/
theorem measurable_realDensity (h : Space μ) : Measurable (realDensity μ h) := by
  exact (measurable_densityExponent μ h).exp

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued density is strongly measurable, hence also strongly measurable almost
everywhere for every reference measure on `W`. -/
theorem aestronglyMeasurable_realDensity (h : Space μ) :
    AEStronglyMeasurable (realDensity μ h) μ := by
  exact ⟨realDensity μ h, (measurable_realDensity μ h).stronglyMeasurable,
    Filter.EventuallyEq.rfl⟩

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The Cameron--Martin density is measurable. -/
theorem measurable_density (h : Space μ) : Measurable (density μ h) := by
  exact (measurable_realDensity μ h).ennreal_ofReal

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued Cameron--Martin density is everywhere strictly positive. -/
theorem realDensity_pos (h : Space μ) (x : W) : 0 < realDensity μ h x :=
  Real.exp_pos _

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A Cameron--Martin density is everywhere strictly positive. -/
theorem density_ne_zero (h : Space μ) (x : W) : density μ h x ≠ 0 := by
  rw [density, ENNReal.ofReal_ne_zero_iff]
  exact realDensity_pos μ h x

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A Cameron--Martin density is finite everywhere. -/
theorem density_ne_top (h : Space μ) (x : W) : density μ h x ≠ ∞ :=
  ENNReal.ofReal_ne_top

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Converting the extended nonnegative density back to `ℝ` recovers `realDensity`. -/
@[simp]
theorem density_toReal (h : Space μ) (x : W) :
    (density μ h x).toReal = realDensity μ h x := by
  exact ENNReal.toReal_ofReal (realDensity_pos μ h x).le

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the density exponent vanishes pointwise. -/
@[simp]
theorem densityExponent_zero (x : W) :
    densityExponent μ (0 : Space μ) x = 0 := by
  simp only [densityExponent, ZeroMemClass.coe_zero, AEEqFun.coeFn_zero_eq, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_self]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the real-valued density is one. -/
@[simp]
theorem realDensity_zero (x : W) : realDensity μ (0 : Space μ) x = 1 := by
  simp only [realDensity, densityExponent_zero, Real.exp_zero]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the extended nonnegative density is one. -/
@[simp]
theorem density_zero (x : W) : density μ (0 : Space μ) x = 1 := by
  simp only [density, realDensity_zero, ENNReal.ofReal_one]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The density exponent at the negative Cameron--Martin vector, almost everywhere. -/
theorem densityExponent_neg_ae (h : Space μ) :
    densityExponent μ (-h) =ᵐ[μ]
      fun x ↦ -(h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2 := by
  filter_upwards [Lp.coeFn_neg (h : Lp ℝ 2 μ)] with x hx
  change (((-h : Space μ) : Lp ℝ 2 μ) : W → ℝ) x =
    -((h : Lp ℝ 2 μ) : W → ℝ) x at hx
  simp only [densityExponent, norm_neg]
  rw [hx]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The product of the real densities at opposite shifts is constant almost everywhere. -/
theorem realDensity_mul_neg_ae (h : Space μ) :
    (fun x ↦ realDensity μ h x * realDensity μ (-h) x) =ᵐ[μ]
      fun _ ↦ Real.exp (-‖h‖ ^ 2) := by
  filter_upwards [densityExponent_neg_ae μ h] with x hx
  simp only [realDensity]
  rw [hx, ← Real.exp_add]
  congr 1
  simp only [densityExponent]
  ring

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The product of the extended densities at opposite shifts is constant almost everywhere. -/
theorem density_mul_neg_ae (h : Space μ) :
    (fun x ↦ density μ h x * density μ (-h) x) =ᵐ[μ]
      fun _ ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) := by
  filter_upwards [realDensity_mul_neg_ae μ h] with x hx
  simp only [density]
  rw [← ENNReal.ofReal_mul (realDensity_pos μ h x).le, hx]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real density of the opposite shift is a reciprocal density, almost everywhere. -/
theorem realDensity_neg_eq_div_ae (h : Space μ) :
    realDensity μ (-h) =ᵐ[μ]
      fun x ↦ Real.exp (-‖h‖ ^ 2) / realDensity μ h x := by
  filter_upwards [realDensity_mul_neg_ae μ h] with x hx
  apply (eq_div_iff (realDensity_pos μ h x).ne').2
  simpa only [mul_comm] using hx

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The extended density of the opposite shift is a reciprocal density, almost everywhere. -/
theorem density_neg_eq_div_ae (h : Space μ) :
    density μ (-h) =ᵐ[μ]
      fun x ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) / density μ h x := by
  filter_upwards [density_mul_neg_ae μ h] with x hx
  apply (ENNReal.eq_div_iff (density_ne_zero μ h x)
    (density_ne_top μ h x)).2
  exact hx

/-- Translation by the zero Cameron--Martin vector leaves the measure unchanged. -/
@[simp]
theorem translated_zero : translated μ (0 : Space μ) = μ := by
  simp only [translated, inclusion_apply, ZeroMemClass.coe_zero, AEEqFun.coeFn_zero_eq, zero_smul,
    integral_zero, translatedMeasure_zero]

/-- The Cameron--Martin formula holds at the zero vector without any analytic input. -/
theorem translated_eq_withDensity_zero :
    translated μ (0 : Space μ) = μ.withDensity (density μ (0 : Space μ)) := by
  rw [translated_zero, funext (density_zero μ)]
  exact withDensity_one.symm

/-! ### Centering and variance of the first chaos -/

/-- Expectation as a continuous linear functional on scalar `L²(μ)`. -/
noncomputable def expectationMap : Lp ℝ 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2).flip (Lp.const 2 μ 1)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `expectationMap` agrees with the Bochner integral of the canonical `L²` representative. -/
@[simp]
theorem expectationMap_apply (f : Lp ℝ 2 μ) :
    expectationMap μ f = ∫ x, f x ∂μ := by
  rw [expectationMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [Lp.const_val, AEEqFun.coeFn_const_eq, ContinuousLinearMap.mul_apply', mul_one]

/-- Centered continuous linear functionals have expectation zero. -/
theorem expectationMap_centeredDual (L : StrongDual ℝ W) :
    expectationMap μ (centeredDualToLp μ L) = 0 := by
  rw [expectationMap_apply]
  rw [integral_congr_ae (centeredDualToLp_ae_eq μ L)]
  rw [integral_sub (by fun_prop) (by fun_prop)]
  rw [IsGaussian.integral_dual]
  simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- Every element of the closed first chaos has expectation zero. -/
theorem expectationMap_firstChaos (h : Space μ) :
    expectationMap μ (h : Lp ℝ 2 μ) = 0 := by
  have hle : firstChaos μ ≤ (expectationMap μ).ker := by
    unfold firstChaos
    apply Submodule.topologicalClosure_minimal
    · rintro f ⟨L, rfl⟩
      exact expectationMap_centeredDual μ L
    · exact (expectationMap μ).isClosed_ker
  exact hle h.property

/-- The canonical representative of every first-chaos element is centered. -/
theorem integral_coe_eq_zero (h : Space μ) :
    ∫ x, (h : Lp ℝ 2 μ) x ∂μ = 0 := by
  rw [← expectationMap_apply]
  exact expectationMap_firstChaos μ h

/-- The variance of a first-chaos element is the square of its Hilbert norm. -/
theorem variance_coe_eq_norm_sq (h : Space μ) :
    Var[fun x ↦ (h : Lp ℝ 2 μ) x; μ] = ‖h‖ ^ 2 := by
  rw [variance_of_integral_eq_zero
    (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable
    (integral_coe_eq_zero μ h)]
  calc
    ∫ x, (h : Lp ℝ 2 μ) x ^ 2 ∂μ =
        @inner ℝ _ _ (h : Lp ℝ 2 μ) (h : Lp ℝ 2 μ) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs,
        RCLike.ofReal_real_eq_id, id_eq, abs_mul_abs_self]
    _ = ‖(h : Lp ℝ 2 μ)‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖h‖ ^ 2 := by rfl

/-! ### Gaussianity of the closed first chaos -/

/-- A centered real Gaussian law, bundled as a probability measure. -/
private noncomputable def centeredGaussianPM (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 v, inferInstance⟩

/-- Centered real Gaussian laws vary continuously with their variance. -/
private lemma tendsto_centeredGaussianPM {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ centeredGaussianPM (v n)) atTop (𝓝 (centeredGaussianPM v₀)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [centeredGaussianPM, ProbabilityMeasure.coe_mk,
    charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  have hvR : Tendsto (fun n ↦ (v n : ℝ)) atTop (𝓝 (v₀ : ℝ)) :=
    NNReal.tendsto_coe.mpr hv
  exact (((hvR.ofReal.mul_const ((t : ℂ) ^ 2)).div_const 2).neg).cexp

/-- The law of a real random variable, bundled as a probability measure. -/
private noncomputable def lawPM {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) : ProbabilityMeasure ℝ :=
  ⟨μ.map f, (Measure.isProbabilityMeasure_map_iff hf).mpr inferInstance⟩

private theorem variance_coe_L2_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    Var[(f : Ω → ℝ); μ] = ‖f‖ ^ 2 := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable, hf₀]
  simp only [sub_zero]
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  congr 1
  funext x
  simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
    abs_mul_abs_self]

/-- A centered Gaussian element of `L²(μ)` has law `N(0, ‖f‖²)`. -/
lemma law_eq_centeredGaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ)
    (hfG : HasGaussianLaw (f : Ω → ℝ) μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    μ.map (f : Ω → ℝ) = gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [hfG.map_eq_gaussianReal, hf₀, variance_coe_L2_eq_norm_sq μ f hf₀]
  congr 1
  apply NNReal.eq
  simp only [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_pow, coe_nnnorm]

/-- A limit in `L²` of centered Gaussian random variables is Gaussian. -/
lemma hasGaussianLaw_L2_limit_of_centered
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g))
    (hfG : ∀ n, HasGaussianLaw (f n : Ω → ℝ) μ)
    (hf₀ : ∀ n, ∫ x, f n x ∂μ = 0) : HasGaussianLaw (g : Ω → ℝ) μ := by
  have hdist := (tendstoInMeasure_of_tendsto_Lp hfg).tendstoInDistribution
    (fun n ↦ (Lp.aestronglyMeasurable (f n)).aemeasurable)
  have hlaw : Tendsto
      (fun n ↦ lawPM μ (f n : Ω → ℝ)
        (Lp.aestronglyMeasurable (f n)).aemeasurable) atTop
      (𝓝 (lawPM μ (g : Ω → ℝ) (Lp.aestronglyMeasurable g).aemeasurable)) :=
    hdist.tendsto
  have hv : Tendsto (fun n ↦ ‖f n‖₊ ^ 2) atTop (𝓝 (‖g‖₊ ^ 2)) :=
    hfg.nnnorm.pow 2
  have hgauss := tendsto_centeredGaussianPM hv
  have heq : (fun n ↦ lawPM μ (f n : Ω → ℝ)
      (Lp.aestronglyMeasurable (f n)).aemeasurable) =
      fun n ↦ centeredGaussianPM (‖f n‖₊ ^ 2) := by
    funext n
    apply Subtype.ext
    exact law_eq_centeredGaussian μ (f n) (hfG n) (hf₀ n)
  rw [heq] at hlaw
  have hprobEq := tendsto_nhds_unique hlaw hgauss
  have hmeasureEq : μ.map (g : Ω → ℝ) = gaussianReal 0 (‖g‖₊ ^ 2) :=
    congrArg Subtype.val hprobEq
  refine ⟨(Lp.aestronglyMeasurable g).aemeasurable, ?_⟩
  rw [hmeasureEq]
  infer_instance

private theorem hasGaussianLaw_centeredDualToLp (L : StrongDual ℝ W) :
    HasGaussianLaw ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) μ := by
  apply HasGaussianLaw.congr (Y :=
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ)) ?_
    (centeredDualToLp_ae_eq μ L).symm
  refine ⟨(L.measurable.sub_const _).aemeasurable, ?_⟩
  have h_eq :
      μ.map (fun x ↦ L x - L (mean μ)) =
        (μ.map L).map (fun y ↦ y - L (mean μ)) := by
    calc
      μ.map (fun x ↦ L x - L (mean μ)) =
          μ.map ((fun y ↦ y - L (mean μ)) ∘ L) := rfl
      _ = (μ.map L).map (fun y ↦ y - L (mean μ)) :=
        (Measure.map_map (measurable_id.sub_const _) L.measurable).symm
  rw [h_eq]
  infer_instance

private theorem integral_centeredDualToLp_eq_zero (L : StrongDual ℝ W) :
    ∫ x, (centeredDualToLp μ L : Lp ℝ 2 μ) x ∂μ = 0 := by
  rw [integral_congr_ae (centeredDualToLp_ae_eq μ L)]
  have hL : Integrable L μ :=
    memLp_one_iff_integrable.mp (IsGaussian.memLp_dual μ L 1 (by norm_num))
  rw [integral_sub hL (integrable_const (L (mean μ)))]
  rw [IsGaussian.integral_dual L]
  simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- Every Cameron--Martin-space representative belongs to the closed Gaussian first chaos. -/
theorem space_hasGaussianLaw (h : Space μ) :
    HasGaussianLaw ((h : Lp ℝ 2 μ) : W → ℝ) μ := by
  rcases mem_closure_iff_seq_limit.mp h.property with ⟨f, hf_range, hf_tendsto⟩
  choose L hL using hf_range
  apply hasGaussianLaw_L2_limit_of_centered μ hf_tendsto
  · intro n
    rw [← hL n]
    exact hasGaussianLaw_centeredDualToLp μ (L n)
  · intro n
    rw [← hL n]
    exact integral_centeredDualToLp_eq_zero μ (L n)

/-- The law of a first-chaos representative is the centered real Gaussian whose variance is its
squared `L²` norm. -/
theorem map_coe_eq_gaussianReal (h : Space μ) :
    μ.map ((h : Lp ℝ 2 μ) : W → ℝ) = gaussianReal 0 (‖h‖₊ ^ 2) := by
  calc
    μ.map ((h : Lp ℝ 2 μ) : W → ℝ) =
        gaussianReal 0 (‖(h : Lp ℝ 2 μ)‖₊ ^ 2) :=
      law_eq_centeredGaussian μ (h : Lp ℝ 2 μ)
        (space_hasGaussianLaw μ h) (integral_coe_eq_zero μ h)
    _ = gaussianReal 0 (‖h‖₊ ^ 2) := by rfl

/-- The exponential moment of a first-chaos representative is its Gaussian normalizer. -/
theorem integral_exp_coe (h : Space μ) :
    ∫ x, Real.exp ((h : Lp ℝ 2 μ) x) ∂μ = Real.exp (‖h‖ ^ 2 / 2) := by
  have hG := space_hasGaussianLaw μ h
  have hmgf := mgf_gaussianReal ⟨hG.aemeasurable, hG.map_eq_gaussianReal⟩ 1
  rw [integral_coe_eq_zero μ h, Real.coe_toNNReal _
    (variance_nonneg (fun x ↦ (h : Lp ℝ 2 μ) x) μ),
    variance_coe_eq_norm_sq μ h] at hmgf
  simpa [mgf] using hmgf

/-- The exponential of a first-chaos representative is integrable. -/
theorem integrable_exp_coe (h : Space μ) :
    Integrable (fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x)) μ := by
  have hi : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (gaussianReal 0 (‖h‖₊ ^ 2)) := integrable_exp_mul_gaussianReal 1
  have himap : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (μ.map ((h : Lp ℝ 2 μ) : W → ℝ)) := by
    rw [map_coe_eq_gaussianReal μ h]
    exact hi
  change Integrable ((fun y : ℝ ↦ Real.exp y) ∘
    ((h : Lp ℝ 2 μ) : W → ℝ)) μ
  simpa only [one_mul] using
    himap.comp_aemeasurable (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable

/-- The real-valued Cameron--Martin density is integrable. -/
theorem integrable_realDensity (h : Space μ) : Integrable (realDensity μ h) μ := by
  have hi := (integrable_exp_coe μ h).div_const
    (Real.exp (‖h‖ ^ 2 / 2))
  apply hi.congr
  filter_upwards with x
  simp only [realDensity, densityExponent, Real.exp_sub]

/-- The real-valued Cameron--Martin density has expectation one. -/
theorem integral_realDensity (h : Space μ) : ∫ x, realDensity μ h x ∂μ = 1 := by
  rw [show realDensity μ h = fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x) /
      Real.exp (‖h‖ ^ 2 / 2) by
        funext x
        simp only [realDensity, densityExponent, Real.exp_sub]]
  rw [integral_div, integral_exp_coe μ h]
  exact div_self (Real.exp_ne_zero _)

/-- The Cameron--Martin density integrates to one. -/
theorem lintegral_density (h : Space μ) : ∫⁻ x, density μ h x ∂μ = 1 := by
  change (∫⁻ x, ENNReal.ofReal (realDensity μ h x) ∂μ) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_realDensity μ h)
    (Filter.Eventually.of_forall fun x ↦ (realDensity_pos μ h x).le)]
  rw [integral_realDensity μ h]
  simp only [ENNReal.ofReal_one]

/-- Reduction of the Cameron--Martin density formula to the shift-versus-tilt identity.  Gaussian
closure of the first chaos and its MGF supply the normalizing factor. -/
theorem translated_eq_withDensity_of_eq_tilted (h : Space μ)
    (hshift : translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :
    translated μ h = μ.withDensity (density μ h) := by
  rw [hshift, Measure.tilted]
  congr with x
  rw [integral_exp_coe μ h]
  simp only [density, realDensity, densityExponent]
  rw [Real.exp_sub]

/-- The law of a continuous linear functional under the translated Gaussian measure: the
Gaussian with mean shifted by `L (inclusion μ h)` and unchanged variance `‖ofDual μ L‖²`. -/
theorem map_translated_dual (h : Space μ) (L : StrongDual ℝ W) :
    (translated μ h).map L =
      gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
  have hcoe : Measurable ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  calc (translated μ h).map L
      = μ.map (L ∘ translate (inclusion μ h)) := by
        unfold translated translatedMeasure
        rw [Measure.map_map L.continuous.measurable (measurable_translate _)]
    _ = μ.map ((fun y ↦ y + (L (mean μ) + L (inclusion μ h))) ∘
          ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)) := by
        apply Measure.map_congr
        filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
        simp only [Function.comp_apply, translate, map_add, coe_ofDual, hx]
        ring
    _ = (μ.map ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)).map
          (fun y ↦ y + (L (mean μ) + L (inclusion μ h))) := by
        rw [Measure.map_map (by fun_prop) hcoe]
    _ = gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
        rw [map_coe_eq_gaussianReal μ (ofDual μ L), gaussianReal_map_add_const, zero_add]

/-- The moment generating function of a continuous linear functional under the exponential
tilt by a first-chaos element: Gaussian with mean `L (mean μ) + ⟪ofDual μ L, h⟫` and variance
`‖ofDual μ L‖²`. -/
theorem mgf_tilted_dual (h : Space μ) (L : StrongDual ℝ W) (t : ℝ) :
    mgf L (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) t =
      Real.exp ((L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) * t +
        ((‖ofDual μ L‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
  set g : Space μ := ofDual μ L with hg
  have hnum : ∫ x, Real.exp (((fun x ↦ (h : Lp ℝ 2 μ) x) + fun x ↦ t * L x) x) ∂μ =
      Real.exp (t * L (mean μ)) * Real.exp (‖h + t • g‖ ^ 2 / 2) := by
    rw [← integral_exp_coe μ (h + t • g), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [centeredDualToLp_ae_eq μ L,
      Lp.coeFn_add (h : Lp ℝ 2 μ) ((t • g : Space μ) : Lp ℝ 2 μ),
      Lp.coeFn_smul t (g : Lp ℝ 2 μ)] with x hx hadd hsmul
    simp only [Pi.add_apply]
    rw [← Real.exp_add, Submodule.coe_add, hadd, Pi.add_apply, Submodule.coe_smul, hsmul,
      Pi.smul_apply, hg, coe_ofDual, hx, smul_eq_mul]
    ring_nf
  have hsq : ‖h + t • g‖ ^ 2 = ‖h‖ ^ 2 + 2 * t * @inner ℝ _ _ g h + t ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_add_sq_real, Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right,
      ← Submodule.coe_inner, real_inner_comm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  unfold mgf
  rw [integral_exp_tilted, hnum, integral_exp_coe μ h, hsq]
  simp only [coe_nnnorm, NNReal.coe_pow]
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-- The law of a continuous linear functional under the exponential tilt by a first-chaos
element. -/
theorem map_tilted_dual (h : Space μ) (L : StrongDual ℝ W) :
    (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)).map L =
      gaussianReal (L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) (‖ofDual μ L‖₊ ^ 2) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  apply map_eq_gaussianReal_of_mgf_eq L.continuous.measurable.aemeasurable
  funext t
  rw [mgf_tilted_dual, mgf_gaussianReal HasLaw.id t]

/-- The analytic core of the Cameron--Martin theorem: translating by the covariance image of `h`
is the same as exponentially tilting by its first-chaos representative.  Both measures give
every continuous linear functional `L` the Gaussian law with mean `L (mean μ) + ⟪ofDual μ L, h⟫`
and variance `‖ofDual μ L‖²`, so they agree by `Measure.ext_of_charFunDual`. -/
theorem translated_eq_tilted (h : Space μ) :
    translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  have : IsProbabilityMeasure (translated μ h) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_translate _).aemeasurable).mpr inferInstance
  apply measure_eq_of_forall_map_dual_eq
  intro L
  rw [map_translated_dual, map_tilted_dual, apply_inclusion]

/-- The Cameron--Martin translation formula. -/
theorem translated_eq_withDensity (h : Space μ) :
    translated μ h = μ.withDensity (density μ h) := by
  exact translated_eq_withDensity_of_eq_tilted μ h (translated_eq_tilted μ h)

/-- The translated Gaussian law is absolutely continuous with respect to the original law. -/
theorem translated_absolutelyContinuous (h : Space μ) : translated μ h ≪ μ := by
  rw [translated_eq_withDensity]
  exact withDensity_absolutelyContinuous μ (density μ h)

/-- The original Gaussian law is absolutely continuous with respect to its Cameron--Martin
translation. -/
theorem absolutelyContinuous_translated (h : Space μ) : μ ≪ translated μ h := by
  rw [translated_eq_withDensity]
  exact withDensity_absolutelyContinuous' (measurable_density μ h).aemeasurable
    (Filter.Eventually.of_forall (density_ne_zero μ h))

/-- Translation by the ambient image of a Cameron--Martin vector preserves the measure class. -/
theorem isQuasiInvariantShift_inclusion (h : Space μ) :
    IsQuasiInvariantShift μ (inclusion μ h) := by
  exact ⟨translated_absolutelyContinuous μ h, absolutelyContinuous_translated μ h⟩

/-- The Radon--Nikodym derivative of the translated law is the Cameron--Martin density. -/
theorem rnDeriv_translated (h : Space μ) :
    (translated μ h).rnDeriv μ =ᵐ[μ] density μ h := by
  rw [translated_eq_withDensity]
  exact Measure.rnDeriv_withDensity μ (measurable_density μ h)

/-- The logarithmic Radon--Nikodym derivative is the first-chaos random variable minus half its
squared Cameron--Martin norm. -/
theorem logDensity_ae_eq (h : Space μ) :
    logDensity μ h =ᵐ[μ] densityExponent μ h := by
  unfold logDensity llr
  filter_upwards [rnDeriv_translated μ h] with x hx
  rw [hx]
  simp only [density_toReal, realDensity, Real.log_exp]

/-- Exponential moments of scalar multiples of a first-chaos representative. -/
theorem integrable_exp_mul_coe (h : Space μ) (c : ℝ) :
    Integrable (fun x ↦ Real.exp (c * (h : Lp ℝ 2 μ) x)) μ := by
  refine (integrable_exp_coe μ (c • h)).congr ?_
  filter_upwards [Lp.coeFn_smul c (h : Lp ℝ 2 μ)] with x hx
  rw [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]

/-- **The Cameron--Martin translation formula for Bochner integrals**: for a continuous `F` and a
Cameron--Martin vector `h`, `∫ F (x + inclusion μ h) dμ = ∫ F x · exp (h x - ‖h‖² / 2) dμ`.
Without an integrability hypothesis this remains a formal Bochner-integral identity; Lean defines
the integral to be zero in a nonintegrable case. -/
theorem integral_add_inclusion {F : W → ℝ} (hF : Continuous F) (h : Space μ) :
    ∫ x, F (x + inclusion μ h) ∂μ =
      ∫ x, F x * Real.exp ((h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2) ∂μ := by
  have h1 : ∫ x, F (x + inclusion μ h) ∂μ = ∫ x, F x ∂(translated μ h) := by
    unfold translated translatedMeasure
    rw [integral_map (measurable_translate _).aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [h1, translated_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (measurable_density μ h) (Filter.Eventually.of_forall fun x ↦ (density_ne_top μ h x).lt_top)]
  congr 1
  funext x
  rw [density_toReal, smul_eq_mul, mul_comm]
  rfl

end StochasticCalculus.CameronMartin
