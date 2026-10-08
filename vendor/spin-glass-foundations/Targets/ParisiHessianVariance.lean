module

public import Targets.ParisiThirdSpatial

@[expose] public section

/-!
# Variance differentiation of the actual scalar Hessian

The existing Gaussian-amplitude theorem differentiates the exponential moments
in `stepD2`. A bounded third spatial derivative of the input is sufficient;
no fourth derivative or commutation of unproved partial derivatives is assumed.
The variance derivative below is genuine on positive variance and includes
mass zero. A uniform bound at variance zero is a separate obligation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem weighted_exp_bounds {A A' G G' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hA' : ∀ x, |A' x| ≤ 1)
    (hG : ∀ x, |G x| ≤ B) (hG' : ∀ x, |G' x| ≤ C) (m : ℝ) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 ≤ c ∧
      (∀ x, |G x * Real.exp (m * A x)| ≤ K * Real.exp (c * |x|)) ∧
      (∀ x, |(G' x + m * G x * A' x) * Real.exp (m * A x)| ≤
        K * Real.exp (c * |x|)) := by
  obtain ⟨a, b, ha, hb, hAb⟩ := hA
  have hB : 0 ≤ B := (abs_nonneg (G 0)).trans (hG 0)
  have hC : 0 ≤ C := (abs_nonneg (G' 0)).trans (hG' 0)
  let D := B + C + |m| * B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he (x : ℝ) : Real.exp (m * A x) ≤
      Real.exp (|m| * a) * Real.exp ((|m| * b) * |x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have H := le_abs_self (m * A x)
    rw [abs_mul] at H
    nlinarith [mul_le_mul_of_nonneg_left (hAb x) (abs_nonneg m)]
  have hcoef (x d : ℝ) (hd : |d| ≤ D) :
      |d * Real.exp (m * A x)| ≤
        (D * Real.exp (|m| * a)) * Real.exp ((|m| * b) * |x|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hd (he x) (Real.exp_pos _).le hD).trans_eq (by ring)
  refine ⟨D * Real.exp (|m| * a), |m| * b, by positivity, by positivity,
    fun x => hcoef x _ ((hG x).trans (by dsimp [D]; nlinarith [mul_nonneg (abs_nonneg m) hB])), ?_⟩
  intro x
  apply hcoef
  have H := abs_add_le (G' x) (m * G x * A' x)
  simp only [abs_mul] at H
  have hp := mul_le_mul (hG x) (hA' x) (abs_nonneg _) hB
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg m)
  dsimp [D]
  nlinarith [hG' x]

/-- Differentiate a bounded C1 observable's unnormalized exponential moment
in positive Gaussian variance. The formula has no division by the mass. -/
theorem hasDerivAt_gaussian_weighted_exp_variance {A A' G G' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hAd : ∀ x, HasDerivAt A (A' x) x)
    (hA'm : Measurable A') (hA'b : ∀ x, |A' x| ≤ 1)
    (hGd : ∀ x, HasDerivAt G (G' x) x) (hG'm : Measurable G')
    (hGb : ∀ x, |G x| ≤ B) (hG'b : ∀ x, |G' x| ≤ C)
    (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => ∫ z, G (x + Real.sqrt w * z) *
      Real.exp (m * A (x + Real.sqrt w * z)) ∂(gaussianReal 0 1))
      ((∫ z, (G' (x + Real.sqrt v * z) +
        m * G (x + Real.sqrt v * z) * A' (x + Real.sqrt v * z)) *
        Real.exp (m * A (x + Real.sqrt v * z)) * z ∂(gaussianReal 0 1)) *
        (1 / (2 * Real.sqrt v))) v := by
  have hAm := (continuous_iff_continuousAt.mpr fun y => (hAd y).continuousAt).measurable
  have hGm := (continuous_iff_continuousAt.mpr fun y => (hGd y).continuousAt).measurable
  obtain ⟨K, c, hK, hc, hb, hb'⟩ := weighted_exp_bounds hA hA'b hGb hG'b m
  have hd (y : ℝ) : HasDerivAt (fun y => G y * Real.exp (m * A y))
      ((G' y + m * G y * A' y) * Real.exp (m * A y)) y := by
    convert! (hGd y).mul (((hAd y).const_mul m).exp) using 1
    ring
  exact (hasDerivAt_integral_gaussian_amplitude hK hc hd
    ((hG'm.add ((hGm.const_mul m).mul hA'm)).mul (hAm.const_mul m).exp)
    hb hb' x (Real.sqrt v)).comp v (Real.hasDerivAt_sqrt hv.ne')

/-- The explicit positive-variance derivative of the actual Hessian. The
quotients retain the expectation branch when the mass is zero. -/
noncomputable def stepD2Variance (A A' A'' A''' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  let E := tiltE A m v x
  let Q := tiltQ A A'' m v x
  let R := tiltR A A' m v x
  let E' := (∫ z, (m * A' (x + Real.sqrt v * z)) *
    Real.exp (m * A (x + Real.sqrt v * z)) * z ∂(gaussianReal 0 1)) /
    (2 * Real.sqrt v)
  let Q' := (∫ z, (A''' (x + Real.sqrt v * z) +
    m * A'' (x + Real.sqrt v * z) * A' (x + Real.sqrt v * z)) *
    Real.exp (m * A (x + Real.sqrt v * z)) * z ∂(gaussianReal 0 1)) /
    (2 * Real.sqrt v)
  let R' := (∫ z, (2 * A' (x + Real.sqrt v * z) * A'' (x + Real.sqrt v * z) +
    m * (A' (x + Real.sqrt v * z)) ^ 3) *
    Real.exp (m * A (x + Real.sqrt v * z)) * z ∂(gaussianReal 0 1)) /
    (2 * Real.sqrt v)
  (Q' * E - Q * E') / E ^ 2 +
    m * ((R' * E - R * E') / E ^ 2 -
      2 * stepD1 A A' m v x * stepD1Variance A A' A'' m v x)

/-- Genuine Hessian variance differentiation from bounded C3 input. The
variance-zero singularity in this explicit representation is not ignored. -/
theorem hasDerivAt_stepD2_variance {A A' A'' A''' : ℝ → ℝ} {K : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hA'''m : Measurable A''')
    (hA'''b : ∀ x, |A''' x| ≤ K) (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => stepD2 A A' A'' m w x)
      (stepD2Variance A A' A'' A''' m v x) v := by
  have hA'm := (continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt).measurable
  have hA''m := (continuous_iff_continuousAt.mpr fun y => (hA'''d y).continuousAt).measurable
  have hE := hasDerivAt_gaussian_weighted_exp_variance hA hC2.1 hA'm
    hC2.abs_first_le_one (G := fun _ => 1) (G' := fun _ => 0) (B := 1) (C := 0)
    (fun y => hasDerivAt_const y 1) measurable_const (by simp) (by simp) m x hv
  simp only [one_mul, zero_add, mul_one] at hE
  have hQ := hasDerivAt_gaussian_weighted_exp_variance hA hC2.1 hA'm
    hC2.abs_first_le_one hA'''d hA'''m hC2.abs_second_le_one hA'''b m x hv
  have hR := hasDerivAt_gaussian_weighted_exp_variance hA hC2.1 hA'm
    hC2.abs_first_le_one (G := fun y => (A' y) ^ 2)
    (G' := fun y => 2 * A' y * A'' y)
    (fun y => by convert! (hC2.2.1 y).pow 2 using 1; ring)
    ((hA'm.const_mul 2).mul hA''m)
    (B := 1) (fun y => by
      rw [abs_pow, sq_abs]
      nlinarith [hC2.2.2.1 y, hC2.2.2.2 y])
    (C := 2) (fun y => by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [mul_le_mul (hC2.abs_first_le_one y) (hC2.abs_second_le_one y)
        (abs_nonneg _) zero_le_one]) m x hv
  have hEn := (tiltE_pos (m := m) (v := v) hA
    (continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt).measurable x).ne'
  have hS := hasDerivAt_stepD1_variance hA hC2 hA''m m x hv
  simp_rw [show ∀ y, m * (A' y) ^ 2 * A' y = m * (A' y) ^ 3 from fun _ => by ring] at hR
  have H := (hQ.div hE hEn).add (((hR.div hE hEn).sub (hS.pow 2)).const_mul m)
  convert! H using 1
  simp only [stepD2Variance, tiltE, tiltQ, tiltR, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    div_eq_mul_inv, one_mul]

private theorem continuous_weighted_exp_velocity {A A' G G' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hcA : Continuous A) (hcA' : Continuous A')
    (hcG : Continuous G) (hcG' : Continuous G') (hA'b : ∀ x, |A' x| ≤ 1)
    (hGb : ∀ x, |G x| ≤ B) (hG'b : ∀ x, |G' x| ≤ C) (m : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ z,
      (G' (p.2 + Real.sqrt p.1 * z) + m * G (p.2 + Real.sqrt p.1 * z) *
        A' (p.2 + Real.sqrt p.1 * z)) *
      Real.exp (m * A (p.2 + Real.sqrt p.1 * z)) * z ∂(gaussianReal 0 1)) := by
  obtain ⟨K, c, hK, hc, _, hb⟩ := weighted_exp_bounds hA hA'b hGb hG'b m
  exact continuous_gaussian_firstMoment_variance_spatial hK hc
    ((hcG'.add ((hcG.const_mul m).mul hcA')).mul (Real.continuous_exp.comp (hcA.const_mul m))) hb

/-- Joint continuity of the genuine Hessian variance velocity on positive
variance, from bounded continuous third input derivative. -/
theorem continuousOn_stepD2Variance {A A' A'' A''' : ℝ → ℝ} {K : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hcA''' : Continuous A''')
    (hA'''b : ∀ x, |A''' x| ≤ K) (m : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => stepD2Variance A A' A'' A''' m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun x => (hC2.1 x).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun x => (hC2.2.1 x).continuousAt
  have hcA'' : Continuous A'' := continuous_iff_continuousAt.mpr fun x => (hA'''d x).continuousAt
  have hmap : Continuous (fun p : ℝ × ℝ => (m, p)) := by fun_prop
  have hE := (continuous_tiltE_mass_variance_spatial hA hcA).comp hmap
  have hQ := (continuous_gaussian_weighted_exp_joint hA hcA hcA'' hC2.abs_second_le_one).comp hmap
  have hR := (continuous_gaussian_weighted_exp_joint hA hcA (hcA'.pow 2)
    (fun x => by change |(A' x) ^ 2| ≤ 1; rw [abs_pow, sq_abs]; nlinarith [hC2.2.2.1 x, hC2.2.2.2 x])).comp hmap
  have hE' := continuous_weighted_exp_velocity hA hcA hcA' (G := fun _ => 1)
    (G' := fun _ => 0) continuous_const continuous_const hC2.abs_first_le_one
    (B := 1) (by simp) (C := 0) (by simp) m
  simp only [zero_add, mul_one] at hE'
  have hQ' := continuous_weighted_exp_velocity hA hcA hcA' hcA'' hcA'''
    hC2.abs_first_le_one hC2.abs_second_le_one hA'''b m
  have hR' := continuous_weighted_exp_velocity hA hcA hcA' (hcA'.pow 2)
    ((hcA'.const_mul 2).mul hcA'') hC2.abs_first_le_one
    (B := 1) (fun x => by change |(A' x) ^ 2| ≤ 1; rw [abs_pow, sq_abs]; nlinarith [hC2.2.2.1 x, hC2.2.2.2 x])
    (C := 2) (fun x => by
      change |2 * A' x * A'' x| ≤ 2
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [mul_le_mul (hC2.abs_first_le_one x) (hC2.abs_second_le_one x)
        (abs_nonneg _) zero_le_one]) m
  simp only [Pi.mul_apply, Pi.pow_apply] at hR'
  simp_rw [show ∀ y, m * (A' y) ^ 2 * A' y = m * (A' y) ^ 3 from fun _ => by ring] at hR'
  have hden : ContinuousOn (fun p : ℝ × ℝ => 2 * Real.sqrt p.1)
      (Set.Ioi 0 ×ˢ Set.univ) := (Real.continuous_sqrt.comp continuous_fst).const_mul 2 |>.continuousOn
  have hden0 (p : ℝ × ℝ) (hp : p ∈ Set.Ioi 0 ×ˢ Set.univ) :
      2 * Real.sqrt p.1 ≠ 0 := mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hp.1).ne'
  have hE0 (p : ℝ × ℝ) (_ : p ∈ Set.Ioi 0 ×ˢ Set.univ) :
      (tiltE A m p.1 p.2) ^ 2 ≠ 0 := pow_ne_zero 2 (tiltE_pos hA hcA.measurable p.2).ne'
  have hEv := hE'.continuousOn.div hden hden0
  have hQv := hQ'.continuousOn.div hden hden0
  have hRv := hR'.continuousOn.div hden hden0
  have hS := ((continuous_gaussian_weighted_exp_joint hA hcA hcA' hC2.abs_first_le_one).comp hmap).div
    hE (fun p => (tiltE_pos hA hcA.measurable p.2).ne')
  have hV := continuousOn_stepD1Variance hA hC2 hcA'' m
  exact ((hQv.mul hE.continuousOn).sub (hQ.continuousOn.mul hEv)).div
    (hE.pow 2).continuousOn hE0 |>.add
    (((((hRv.mul hE.continuousOn).sub (hR.continuousOn.mul hEv)).div
      (hE.pow 2).continuousOn hE0).sub ((hS.continuousOn.const_mul 2).mul hV)).const_mul m)

/-- The existing positive-smoothing third derivative is jointly continuous,
not merely continuous at fixed variance. -/
theorem continuousOn_stepD3_variance_spatial {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {m : ℝ} (hm : 0 ≤ m) :
    ContinuousOn (fun p : ℝ × ℝ => stepD3 A A' A'' m p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hc := continuous_parisiStep_variance_spatial hC2 hcA'' hm
  exact ((continuousOn_stepD1Variance hA hC2 hcA'' m).const_mul 2).sub
    (((hc.2.1.continuousOn.const_mul (2 * m)).mul hc.2.2.continuousOn))

/-- Actual joint derivative of the scalar Hessian on positive variance. -/
theorem hasFDerivAt_stepD2_variance_spatial {A A' A'' A''' : ℝ → ℝ} {K : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hcA''' : Continuous A''')
    (hA'''b : ∀ x, |A''' x| ≤ K) {m : ℝ} (hm : m ∈ Set.Icc 0 1)
    {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => stepD2 A A' A'' m p.1 p.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (stepD2Variance A A' A'' A''' m v x)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD3 A A' A'' m v x))) (v, x) := by
  have hcA'' : Continuous A'' := continuous_iff_continuousAt.mpr fun y => (hA'''d y).continuousAt
  have hn : Set.Ioi 0 ×ˢ Set.univ ∈ 𝓝 (v, x) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hv, Set.mem_univ x⟩
  have hdv : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x),
      HasFDerivAt (fun w => stepD2 A A' A'' m w p.2)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD2Variance A A' A'' A''' m p.1 p.2)) p.1 := by
    filter_upwards [hn] with p hp
    exact (hasDerivAt_stepD2_variance hA hC2 hA'''d hcA'''.measurable hA'''b m p.2 hp.1).hasFDerivAt
  have hdx : ∀ᶠ p : ℝ × ℝ in 𝓝 (v, x),
      HasFDerivAt (stepD2 A A' A'' m p.1)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (stepD3 A A' A'' m p.1 p.2)) p.2 := by
    filter_upwards [hn] with p hp
    exact (hasDerivAt_stepD2_spatial hA hC2 hcA'' hm hp.1 p.2).hasFDerivAt
  apply (hasStrictFDerivAt_uncurry_coprod (u := (v, x))
    (f := fun v x => stepD2 A A' A'' m v x)
    (f₁ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight (stepD2Variance A A' A'' A''' m v x))
    (f₂ := fun v x => (1 : ℝ →L[ℝ] ℝ).smulRight (stepD3 A A' A'' m v x))
    hdv hdx ?_ ?_).hasFDerivAt
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp
      ((continuousOn_stepD2Variance hA hC2 hA'''d hcA''' hA'''b m
        (v, x) ⟨hv, Set.mem_univ x⟩).continuousAt hn)
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp
      ((continuousOn_stepD3_variance_spatial hA hC2 hcA'' hm.1
        (v, x) ⟨hv, Set.mem_univ x⟩).continuousAt hn)

/-- Chain rule for the actual Hessian along simultaneous variance and field
paths. It is the moving-Hessian input for differentiating its squared mean. -/
theorem hasDerivAt_stepD2_variance_curve {A A' A'' A''' : ℝ → ℝ} {K : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hcA''' : Continuous A''')
    (hA'''b : ∀ x, |A''' x| ≤ K) {m : ℝ} (hm : m ∈ Set.Icc 0 1)
    {V X : ℝ → ℝ} {v' x' t : ℝ}
    (hV : HasDerivAt V v' t) (hX : HasDerivAt X x' t) (hv : 0 < V t) :
    HasDerivAt (fun a => stepD2 A A' A'' m (V a) (X a))
      (v' * stepD2Variance A A' A'' A''' m (V t) (X t) +
        x' * stepD3 A A' A'' m (V t) (X t)) t := by
  have H := (hasFDerivAt_stepD2_variance_spatial hA hC2 hA'''d hcA''' hA'''b hm hv (X t)).comp_hasDerivAt t
    (hV.prodMk hX)
  simpa only [Function.comp_def, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] using! H

end SpinGlass.Targets
