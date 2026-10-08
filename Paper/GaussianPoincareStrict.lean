module

public import Paper.GaussianPoincare

@[expose] public section

/-!
# Strict Gaussian Poincaré for nonconstant derivatives

The Young-inequality deficit is the expectation of the squared difference of
the derivatives at two Gaussian rotations. Full support makes this deficit
positive when the derivative is nonconstant, yielding strictness in the
rotation interpolation proof. No equality-case theorem is assumed.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace Paper

private instance strict_standardGaussian_openPos : Measure.IsOpenPosMeasure (gaussianReal 0 1) where
  open_pos U hU hne hzero :=
    hU.measure_ne_zero volume hne ((gaussianReal_absolutelyContinuous' 0 (by norm_num)) hzero)

/-- The derivative correlation is strictly below its square moment whenever
one point has unequal derivative values under the rotation. -/
theorem gaussian_rotation_derivative_product_lt
    (df : ℝ → ℝ) (h a θ C : ℝ) (hdf : Continuous df) (hC : 0 ≤ C)
    (hdb : ∀ x, ‖df x‖ ≤ C) (ha : 0 ≤ a)
    (hw : ∃ p : ℝ × ℝ, df (h + a * p.1) ≠
      df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))) :
    (∫ p, df (h + a * p.1) * df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
      ∂standardGaussianPair) < gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
  letI : Measure.IsOpenPosMeasure standardGaussianPair := by unfold standardGaussianPair; infer_instance
  let U : ℝ × ℝ → ℝ := fun p => df (h + a * p.1)
  let V : ℝ × ℝ → ℝ := fun p => df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
  have hcU : Continuous U := by dsimp [U]; fun_prop
  have hcV : Continuous V := by dsimp [V]; fun_prop
  have hb2 : ∀ x, ‖df x ^ 2‖ ≤ C ^ 2 := by
    intro x
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hdb x) 2
  have hiU := integrable_gaussian_pair_bounded (fun p => U p ^ 2) (C ^ 2)
    (hcU.pow 2) (fun p => hb2 _)
  have hiV := integrable_gaussian_pair_bounded (fun p => V p ^ 2) (C ^ 2)
    (hcV.pow 2) (fun p => hb2 _)
  have hiP := integrable_gaussian_pair_bounded (fun p => U p * V p) (C ^ 2)
    (hcU.mul hcV) (fun p => by
      rw [norm_mul]
      nlinarith [mul_le_mul (hdb (h + a * p.1))
        (hdb (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))) (norm_nonneg _) hC])
  have hiGap := integrable_gaussian_pair_bounded (fun p => (U p - V p) ^ 2) ((2 * C) ^ 2)
    ((hcU.sub hcV).pow 2) (fun p => by
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      have hu := hdb (h + a * p.1)
      have hv := hdb (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2))
      exact (norm_sub_le _ _).trans (by simpa only [U, V, two_mul] using add_le_add hu hv))
  obtain ⟨p, hp⟩ := hw
  have hgap : 0 < ∫ p, (U p - V p) ^ 2 ∂standardGaussianPair :=
    integral_pos_of_integrable_nonneg_nonzero ((hcU.sub hcV).pow 2) hiGap
      (fun p => sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.mpr hp))
  have hidentity : (∫ p, (U p - V p) ^ 2 ∂standardGaussianPair) =
      (∫ p, U p ^ 2 ∂standardGaussianPair) + (∫ p, V p ^ 2 ∂standardGaussianPair) -
      2 * (∫ p, U p * V p ∂standardGaussianPair) := by
    calc
      _ = ∫ p, (U p ^ 2 + V p ^ 2) - 2 * (U p * V p) ∂standardGaussianPair := by
        apply integral_congr_ae
        filter_upwards [] with p
        ring
      _ = _ := by
        have hsub := integral_sub (hiU.add hiV) (hiP.const_mul 2)
        simp only [Pi.sub_apply, Pi.add_apply, integral_const_mul] at hsub
        have hadd : (∫ p, U p ^ 2 + V p ^ 2 ∂standardGaussianPair) =
            (∫ p, U p ^ 2 ∂standardGaussianPair) + (∫ p, V p ^ 2 ∂standardGaussianPair) := by
          simpa only [Pi.add_apply] using integral_add hiU hiV
        rw [hadd] at hsub
        exact hsub

  have hfirst : (∫ p, U p ^ 2 ∂standardGaussianPair) =
      gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
    simp only [standardGaussianPair, U]
    rw [integral_prod _ hiU]
    dsimp only [U]
    simp [gaussianExpectation]
  have hrot := gaussian_pair_rotated_integral (fun x => df x ^ 2) h a θ (C ^ 2)
    (hdf.pow 2) hb2 ha
  change (∫ p, V p ^ 2 ∂standardGaussianPair) = _ at hrot
  rw [hidentity, hfirst, hrot] at hgap
  change (∫ p, U p * V p ∂standardGaussianPair) < _
  linarith

/-- A genuine two-coordinate witness can realize any pair of derivative
values whenever the rotation angle has positive sine and the scale is positive. -/
theorem gaussian_rotation_derivative_witness (df : ℝ → ℝ) (h a θ : ℝ)
    (ha : 0 < a) (hθ : 0 < Real.sin θ) (hw : ∃ u v, df u ≠ df v) :
    ∃ p : ℝ × ℝ, df (h + a * p.1) ≠
      df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) := by
  obtain ⟨u, v, huv⟩ := hw
  let x := (u - h) / a
  let y := (v - h - a * Real.cos θ * x) / (a * Real.sin θ)
  refine ⟨(x, y), ?_⟩
  have hx : h + a * x = u := by dsimp [x]; field_simp; ring
  have hy : h + a * (Real.cos θ * x + Real.sin θ * y) = v := by
    dsimp [y]
    field_simp
    ring
  simpa only [hx, hy] using huv

theorem gaussian_poincare_bounded_C2_strict (f df ddf : ℝ → ℝ) (h a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hf : Continuous f) (hdf : Continuous df) (hddf : Continuous ddf)
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖df x‖ ≤ C) (hddb : ∀ x, ‖ddf x‖ ≤ C)
    (hdf_nonconstant : ∃ u v, df u ≠ df v) :
    gaussianExpectation (fun z => f (h + a * z) ^ 2) -
      gaussianExpectation (fun z => f (h + a * z)) ^ 2 <
        a ^ 2 * gaussianExpectation (fun z => df (h + a * z) ^ 2) := by
  let B := gaussianExpectation (fun z => df (h + a * z) ^ 2)
  let g : ℝ → ℝ := fun θ => gaussianRotationCovariance f h a θ - a ^ 2 * Real.cos θ * B
  have hgD (θ : ℝ) : HasDerivAt g
      (a ^ 2 * Real.sin θ * (B - ∫ p, df (h + a * p.1) *
        df (h + a * (Real.cos θ * p.1 + Real.sin θ * p.2)) ∂standardGaussianPair)) θ := by
    have hCov := hasDerivAt_gaussianRotationCovariance f df ddf h a θ C
      hf hdf hddf hC hd hdd hb hdb hddb
    convert hCov.sub (((Real.hasDerivAt_cos θ).const_mul (a ^ 2)).mul_const B) using 1
    ring
  have hgC : Continuous g := continuous_iff_continuousAt.mpr (fun θ => (hgD θ).continuousAt)
  have hmono : StrictMonoOn g (Icc (0 : ℝ) (Real.pi / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hgC.continuousOn
    intro θ hθ
    rw [interior_Icc] at hθ
    rw [(hgD θ).deriv]
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos])
    exact mul_pos (mul_pos (sq_pos_of_pos ha) hsin)
      (sub_pos.mpr (gaussian_rotation_derivative_product_lt df h a θ C hdf hC hdb ha.le
        (gaussian_rotation_derivative_witness df h a θ ha hsin hdf_nonconstant)))
  have hm := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 2 ∈ Icc (0 : ℝ) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  have hcov0 : gaussianRotationCovariance f h a 0 =
      gaussianExpectation (fun z => f (h + a * z) ^ 2) := by
    have hi := integrable_gaussian_pair_bounded (fun p : ℝ × ℝ => f (h + a * p.1) ^ 2)
      (C ^ 2) (by fun_prop) (fun p => by
        simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb (h + a * p.1)) 2)
    simp only [gaussianRotationCovariance, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    simp_rw [← pow_two]
    simp only [standardGaussianPair]
    rw [integral_prod _ hi]
    simp [gaussianExpectation]
  have hcovPi : gaussianRotationCovariance f h a (Real.pi / 2) =
      gaussianExpectation (fun z => f (h + a * z)) ^ 2 := by
    simp only [gaussianRotationCovariance, Real.cos_pi_div_two, Real.sin_pi_div_two,
      one_mul, zero_mul, zero_add]
    simp only [standardGaussianPair]
    rw [integral_prod_mul (fun z : ℝ => f (h + a * z)) (fun z : ℝ => f (h + a * z))]
    simp only [gaussianExpectation]
    ring
  dsimp [g] at hm
  rw [hcov0, hcovPi, Real.cos_zero, Real.cos_pi_div_two] at hm
  dsimp [B] at hm
  linarith

/-- The strict Gaussian Poincaré inequality needed at the AT boundary. -/
theorem gaussian_poincare_tanh_strict (x a : ℝ) (ha : 0 < a) :
    gaussianExpectation (fun z => Real.tanh (x + a * z) ^ 2) -
      gaussianExpectation (fun z => Real.tanh (x + a * z)) ^ 2 <
        a ^ 2 * gaussianExpectation (fun z => sech (x + a * z) ^ 4) := by
  have hnonconstant : ∃ u v : ℝ, sech u ^ 2 ≠ sech v ^ 2 := by
    refine ⟨0, 1, ?_⟩
    have hc : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
    have hs : sech 1 < 1 := by
      unfold sech
      simpa only [one_div] using (inv_lt_one₀ (Real.cosh_pos 1)).mpr hc
    have hs2 : sech 1 ^ 2 < 1 := by nlinarith [sech_pos 1]
    simpa [sech] using ne_of_gt hs2
  have hp := gaussian_poincare_bounded_C2_strict Real.tanh (fun y => sech y ^ 2)
    (fun y => -2 * Real.tanh y * sech y ^ 2) x a 2 ha (by norm_num)
    gaussian_continuous_tanh (gaussian_continuous_sech.pow 2)
    ((continuous_const.mul gaussian_continuous_tanh).mul (gaussian_continuous_sech.pow 2))
    hasDerivAt_tanh hasDerivAt_sech_sq
    (fun y => by rw [Real.norm_eq_abs]; exact (Real.abs_tanh_lt_one y).le.trans (by norm_num))
    (fun y => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact (sech_sq_le_one y).trans (by norm_num))
    sech_sq_derivative_bound hnonconstant
  simpa only [← pow_mul, Nat.reduceMul] using hp

end Paper
