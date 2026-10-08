module

public import Targets.ParisiMassZero
public import Targets.ParisiStepSemigroup
public import Targets.Section4NestedMonotone
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-!
# Interchanging scalar Gaussian Parisi operators

The non-strict comparison in Talagrand's Lemma 5.12 follows from integral
Minkowski. We obtain its integral-parameter form from Mathlib's Hölder
inequality and Tonelli, without postulating an interchange inequality.
No equality characterization for arbitrary nonconstant functions is asserted:
affine functions also give equality.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

namespace SpinGlass.Targets

/-- Integral Minkowski, in the finite-left-norm case needed for Gaussian
exponential profiles. The right norm is permitted to be infinite. -/
theorem lintegral_minkowski_of_finite
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {F : X × Y → ℝ≥0∞} (hF : Measurable F) {p : ℝ} (hp : 1 < p)
    (hfinite : (∫⁻ x, (∫⁻ y, F (x, y) ∂ν) ^ p ∂μ) ≠ ∞) :
    (∫⁻ x, (∫⁻ y, F (x, y) ∂ν) ^ p ∂μ) ^ (1 / p) ≤
      ∫⁻ y, (∫⁻ x, F (x, y) ^ p ∂μ) ^ (1 / p) ∂ν := by
  let S : X → ℝ≥0∞ := fun x => ∫⁻ y, F (x, y) ∂ν
  let I : ℝ≥0∞ := ∫⁻ x, S x ^ p ∂μ
  let B : ℝ≥0∞ := ∫⁻ y, (∫⁻ x, F (x, y) ^ p ∂μ) ^ (1 / p) ∂ν
  have hS : Measurable S := hF.lintegral_prod_right'
  have hpq := Real.HolderConjugate.conjExponent hp
  have hI : I ≠ ∞ := hfinite
  by_cases hzero : I = 0
  · change I ^ (1 / p) ≤ B
    rw [hzero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr (lt_trans zero_lt_one hp))]
    exact zero_le
  have he (x : X) : S x ^ p = S x * S x ^ (p - 1) := by
    nth_rw 2 [← ENNReal.rpow_one (S x)]
    rw [← ENNReal.rpow_add_of_nonneg _ _
      (by norm_num : (0 : ℝ) ≤ 1) (sub_nonneg.mpr hp.le)]
    congr 1
    ring
  have hholder (y : Y) :
      (∫⁻ x, F (x, y) * S x ^ (p - 1) ∂μ) ≤
        (∫⁻ x, F (x, y) ^ p ∂μ) ^ (1 / p) * I ^ (1 / p.conjExponent) := by
    have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun x => F (x, y))
      (hF.comp measurable_prodMk_right).aemeasurable (hS.pow_const (p - 1)).aemeasurable
    simpa only [Pi.mul_apply, ← ENNReal.rpow_mul, hpq.sub_one_mul_conj] using H
  have H : I ≤ B * I ^ (1 / p.conjExponent) := by
    calc
      I = ∫⁻ x, ∫⁻ y, F (x, y) * S x ^ (p - 1) ∂ν ∂μ := by
        apply lintegral_congr
        intro x
        rw [lintegral_mul_const _ (show Measurable (fun y => F (x, y)) from
          hF.comp measurable_prodMk_left)]
        exact he x
      _ = ∫⁻ y, ∫⁻ x, F (x, y) * S x ^ (p - 1) ∂μ ∂ν :=
        lintegral_lintegral_swap (hF.mul ((hS.comp measurable_fst).pow_const _)).aemeasurable
      _ ≤ ∫⁻ y, (∫⁻ x, F (x, y) ^ p ∂μ) ^ (1 / p) * I ^ (1 / p.conjExponent) ∂ν :=
        lintegral_mono hholder
      _ = B * I ^ (1 / p.conjExponent) := by
        rw [lintegral_mul_const _ ((hF.pow_const p).lintegral_prod_left.pow_const _)]
  have hpow : I ^ (1 / p.conjExponent) ≠ 0 := by simp [hzero, hI]
  have hpowtop : I ^ (1 / p.conjExponent) ≠ ∞ := by simp [hzero, hI]
  have hsplit : I ^ (1 / p) * I ^ (1 / p.conjExponent) = I := by
    rw [← ENNReal.rpow_add _ _ hzero hI]
    simpa only [one_div, ENNReal.rpow_one] using congrArg (fun z : ℝ => I ^ z) hpq.inv_add_inv_eq_one
  change I ^ (1 / p) ≤ B
  apply (ENNReal.mul_le_mul_iff_left hpow hpowtop).mp
  rwa [hsplit]

private theorem ofReal_exp_rpow (a p : ℝ) :
    (ENNReal.ofReal (Real.exp a)) ^ p = ENNReal.ofReal (Real.exp (a * p)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos a),
    Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]

private theorem ofReal_exp_parisiStep {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmA : Measurable A) {m : ℝ} (hm : m ≠ 0)
    (a x : ℝ) :
    ENNReal.ofReal (Real.exp (m * parisiStep m a A x)) =
      ∫⁻ z, ENNReal.ofReal (Real.exp (m * A (x + Real.sqrt a * z)))
        ∂(gaussianReal 0 1) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_of_hasLinearGrowth hA hmA m x a)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  rw [parisiStep, if_neg hm]
  have he : m * (1 / m * Real.log (∫ z, Real.exp (m * A (x + Real.sqrt a * z))
      ∂(gaussianReal 0 1))) =
      Real.log (∫ z, Real.exp (m * A (x + Real.sqrt a * z)) ∂(gaussianReal 0 1)) := by
    field_simp
  rw [he, Real.exp_log (smoothing_integral_pos hA hmA x)]

/-- Talagrand's operator comparison for strictly ordered positive masses.
Only measurable linear growth is required of the input. -/
theorem parisiStep_interchange_of_pos_lt {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) {m' m : ℝ}
    (hm' : 0 < m') (hmm : m' < m) (a a' x : ℝ) :
    parisiStep m a (parisiStep m' a' Q) x ≤
      parisiStep m' a' (parisiStep m a Q) x := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (m' * Q (x + Real.sqrt a * z.1 + Real.sqrt a' * z.2)))
  let L := parisiStep m a (parisiStep m' a' Q) x
  let R := parisiStep m' a' (parisiStep m a Q) x
  have hm : 0 < m := hm'.trans hmm
  have hp : 1 < m / m' := (one_lt_div hm').mpr hmm
  have hF : Measurable F := by
    exact (((hmQ.comp (by fun_prop)).const_mul m').exp).ennreal_ofReal
  have hin (z : ℝ) : (∫⁻ z', F (z, z') ∂(gaussianReal 0 1)) =
      ENNReal.ofReal (Real.exp (m' * parisiStep m' a' Q (x + Real.sqrt a * z))) :=
    (ofReal_exp_parisiStep hQ hmQ hm'.ne' a' (x + Real.sqrt a * z)).symm
  have hI : (∫⁻ z, (∫⁻ z', F (z, z') ∂(gaussianReal 0 1)) ^ (m / m')
      ∂(gaussianReal 0 1)) = ENNReal.ofReal (Real.exp (m * L)) := by
    simp_rw [hin, ofReal_exp_rpow]
    have he (z : ℝ) : m' * parisiStep m' a' Q (x + Real.sqrt a * z) * (m / m') =
        m * parisiStep m' a' Q (x + Real.sqrt a * z) := by field_simp
    simp_rw [he]
    exact (ofReal_exp_parisiStep (hasLinearGrowth_parisiStep hQ hmQ m' a')
      (measurable_parisiStep hmQ m' a') hm.ne' a x).symm
  have hout (z' : ℝ) :
      (∫⁻ z, F (z, z') ^ (m / m') ∂(gaussianReal 0 1)) ^ (1 / (m / m')) =
      ENNReal.ofReal (Real.exp (m' * parisiStep m a Q (x + Real.sqrt a' * z'))) := by
    have hpow (z : ℝ) : F (z, z') ^ (m / m') =
        ENNReal.ofReal (Real.exp (m * Q (x + Real.sqrt a' * z' + Real.sqrt a * z))) := by
      change (ENNReal.ofReal (Real.exp (m' * Q (x + Real.sqrt a * z + Real.sqrt a' * z')))) ^
        (m / m') = _
      rw [ofReal_exp_rpow]
      congr 2
      rw [show x + Real.sqrt a * z + Real.sqrt a' * z' =
        x + Real.sqrt a' * z' + Real.sqrt a * z by ring]
      field_simp
    simp_rw [hpow]
    rw [← ofReal_exp_parisiStep hQ hmQ hm.ne', ofReal_exp_rpow]
    congr 2
    field_simp
  have H := lintegral_minkowski_of_finite (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    hF hp (by rw [hI]; exact ENNReal.ofReal_ne_top)
  rw [hI, ofReal_exp_rpow] at H
  simp_rw [hout] at H
  rw [← ofReal_exp_parisiStep (hasLinearGrowth_parisiStep hQ hmQ m a)
    (measurable_parisiStep hmQ m a) hm'.ne' a' x] at H
  have he : m * L * (1 / (m / m')) = m' * L := by field_simp
  rw [he] at H
  have hreal : Real.exp (m' * L) ≤ Real.exp (m' * R) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp H
  exact (mul_le_mul_iff_right₀ hm').mp (Real.exp_le_exp.mp hreal)

/-- The lower mass may be zero. Monotonicity compares its inner expectation
with positive masses; analyticity of the fixed outer-input transform then
passes the proved comparison to zero without a singular quotient limit. -/
theorem parisiStep_interchange_zero {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) {m : ℝ}
    (hm : 0 < m) (a a' x : ℝ) :
    parisiStep m a (parisiStep 0 a' Q) x ≤
      parisiStep 0 a' (parisiStep m a Q) x := by
  have hB := hasLinearGrowth_parisiStep hQ hmQ m a
  have hmB := measurable_parisiStep hmQ m a
  have hlim := ((analyticAt_parisiStep_mass hB hmB a' x 0).continuousAt.tendsto).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hm)] with l hl hlm
  have hinner : ∀ y, parisiStep 0 a' Q y ≤ parisiStep l a' Q y :=
    fun y => monotone_parisiStep_mass hQ hmQ a' y hl.le
  exact (parisiStep_mono_of_growth hm.le
    (hasLinearGrowth_parisiStep hQ hmQ 0 a') (measurable_parisiStep hmQ 0 a')
    (hasLinearGrowth_parisiStep hQ hmQ l a') (measurable_parisiStep hmQ l a') hinner x).trans
      (parisiStep_interchange_of_pos_lt hQ hmQ hl hlm a a' x)

/-- The non-strict scalar interchange of Talagrand's Lemma 5.12, including
both zero masses and both zero variances, on measurable linear-growth inputs. -/
theorem parisiStep_interchange {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) {m' m a a' : ℝ}
    (hm' : 0 ≤ m') (hmm : m' ≤ m) (ha : 0 ≤ a) (ha' : 0 ≤ a') (x : ℝ) :
    parisiStep m a (parisiStep m' a' Q) x ≤
      parisiStep m' a' (parisiStep m a Q) x := by
  rcases hmm.eq_or_lt with heq | hlt
  · subst m
    have H₁ := congrFun (parisiStep_add m' a a' ha ha' hQ hmQ) x
    have H₂ := congrFun (parisiStep_add m' a' a ha' ha hQ hmQ) x
    rw [← H₁, ← H₂, add_comm a a']
  · rcases hm'.eq_or_lt with hz | hpos
    · subst m'
      exact parisiStep_interchange_zero hQ hmQ hlt a a' x
    · exact parisiStep_interchange_of_pos_lt hQ hmQ hpos hlt a a' x

/-- In particular the interchange applies to every actual scalar Parisi
input, without any boundedness assumption on log-cosh or its descendants. -/
theorem parisiStep_interchange_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m' m a a' : ℝ} (hm' : 0 ≤ m') (hmm : m' ≤ m)
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (x : ℝ) :
    parisiStep m a (parisiStep m' a' (parisiF s β j)) x ≤
      parisiStep m' a' (parisiStep m a (parisiF s β j)) x :=
  parisiStep_interchange (parisiF_hasLinearGrowth s β j) (parisiF_measurable s β j)
    hm' hmm ha ha' x

end SpinGlass.Targets
