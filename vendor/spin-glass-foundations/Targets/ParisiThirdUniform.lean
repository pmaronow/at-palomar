module

public import Targets.ParisiThirdSpatial
public import Targets.ParisiJointMassContinuity
public import Targets.CascadeSecondPi
public import Targets.CascadeEndpoint

@[expose] public section

/-!
# Uniform spatial third derivatives through the actual Parisi recursion

The normalized exponential third-derivative polynomial is preserved by a
step at the same mass. Changing the mass costs only its decrement, so the
monotone mass sequence gives a depth-independent bound, including variance
zero. This avoids the singular positive-smoothing estimate.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- A scalar normalized Gaussian observable, also at mass zero. -/
noncomputable def scalarTiltMean (A G : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  tiltP A G m v x / tiltE A m v x

/-- Spatial differentiation of an unnormalized bounded observable. The
existing finite-coordinate dominated-differentiation theorem is used at n=1. -/
theorem hasDerivAt_tiltP_spatial {A A' G G' : ℝ → ℝ} {B B' : ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (hA'm : Measurable A')
    (hGm : Measurable G) (hG'm : Measurable G')
    (hAd : ∀ x, HasDerivAt A (A' x) x) (hGd : ∀ x, HasDerivAt G (G' x) x)
    (hAb : ∀ x, |A' x| ≤ 1) (hGb : ∀ x, |G x| ≤ B) (hG'b : ∀ x, |G' x| ≤ B')
    (m v x : ℝ) :
    HasDerivAt (tiltP A G m v) (tiltP A (fun y => G' y + m * G y * A' y) m v x) x := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  have hshiftm (J : ℝ → ℝ) (hJ : Measurable J) (u : ℝ) :
      Measurable (fun y : Fin 1 → ℝ => J (u + y 0)) :=
    hJ.comp (measurable_const.add (measurable_pi_apply 0))
  have heval (J : ℝ → ℝ) (hJ : Measurable J) (u : ℝ) :
      (∫ z : Fin 1 → ℝ, J (u + Real.sqrt v * z 0) *
        Real.exp (m * A (u + Real.sqrt v * z 0)) ∂piGauss 1) = tiltP A J m v u :=
    integral_piGauss_eval 0 _ (((hJ.comp (measurable_tilt_shift v u)).mul
      ((hAm.comp (measurable_tilt_shift v u)).const_mul m).exp).aestronglyMeasurable)
  have H := hasDerivAt_integral_mul_exp_param_pi
    (A := fun u y => A (u + y 0)) (A' := fun u y => A' (u + y 0))
    (G := fun u y => G (u + y 0)) (G' := fun u y => G' (u + y 0))
    (m := m) (v := v) (C := C + D * (|x| + 1)) (D := D)
    (BA := 1) (BG := B) (BG' := B') (0 : Fin 1 → ℝ)
    (r := x) (s := Set.Ioo (x - 1) (x + 1)) (Ioo_mem_nhds (by linarith) (by linarith)) hD
    (fun u _ y => by simpa only [Function.comp_def, id_eq, mul_one] using
      (hAd (u + y 0)).comp u ((hasDerivAt_id u).add_const (y 0)))
    (fun u _ y => by simpa only [Function.comp_def, id_eq, mul_one] using
      (hGd (u + y 0)).comp u ((hasDerivAt_id u).add_const (y 0)))
    (fun u _ => hshiftm A hAm u) (fun u _ => hshiftm A' hA'm u)
    (fun u _ => hshiftm G hGm u) (fun u _ => hshiftm G' hG'm u)
    (fun u hu y => by
      have hu' : |u| ≤ |x| + 1 := by
        have H : |u - x| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have := abs_sub_le u x 0
        simp only [sub_zero] at this
        linarith
      have H := hb (u + y 0)
      simp only [l1, Fin.sum_univ_one]
      nlinarith [mul_le_mul_of_nonneg_left (abs_add_le u (y 0)) hD,
        mul_le_mul_of_nonneg_left hu' hD])
    (fun u _ y => hAb (u + y 0)) (fun u _ y => hGb (u + y 0))
    (fun u _ y => hG'b (u + y 0))
  simp only [Pi.zero_apply, zero_add] at H
  simp_rw [heval G hGm] at H
  rw [heval (fun y => G' y + m * G y * A' y)
    (hG'm.add ((hGm.const_mul m).mul hA'm)) x] at H
  exact H

/-- The scalar normalized-observable spatial rule, valid at every mass and
variance, including zero. It can be reused at higher derivative orders. -/
theorem hasDerivAt_scalarTiltMean_spatial {A A' G G' : ℝ → ℝ} {B B' : ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (hA'm : Measurable A')
    (hGm : Measurable G) (hG'm : Measurable G')
    (hAd : ∀ x, HasDerivAt A (A' x) x) (hGd : ∀ x, HasDerivAt G (G' x) x)
    (hAb : ∀ x, |A' x| ≤ 1) (hGb : ∀ x, |G x| ≤ B) (hG'b : ∀ x, |G' x| ≤ B')
    (m v x : ℝ) :
    HasDerivAt (scalarTiltMean A G m v)
      (scalarTiltMean A (fun y => G' y + m * G y * A' y) m v x -
        m * scalarTiltMean A G m v x * stepD1 A A' m v x) x := by
  have Hn := hasDerivAt_tiltP_spatial hA hAm hA'm hGm hG'm hAd hGd hAb hGb hG'b m v x
  have Hd := hasDerivAt_integral_exp_mul (m := m) (v := v) hAd hAb hA hAm hA'm x
  rw [integral_mul_deriv_eq hAb hA hAm hA'm x] at Hd
  change HasDerivAt (tiltE A m v) (m * tiltP A A' m v x) x at Hd
  convert! Hn.div Hd (tiltE_pos hA hAm x).ne' using 1
  unfold scalarTiltMean stepD1
  field_simp

/-- The third derivative of an exponential, divided by its mass and value. -/
def parisiThirdPolynomial (p q z m : ℝ) : ℝ := z + 3 * m * p * q + m ^ 2 * p ^ 3

/-- Endpoint-safe candidate for the actual third spatial derivative. -/
noncomputable def stepD3Uniform (A A' A'' A''' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  scalarTiltMean A (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) m v x -
    3 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x - m ^ 2 * (stepD1 A A' m v x) ^ 3

private theorem scalarTiltMean_second_eq {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (hA'm : Measurable A')
    (hA''m : Measurable A'') (hAb : ∀ x, |A' x| ≤ 1) (hA''b : ∀ x, |A'' x| ≤ 1)
    (m v x : ℝ) :
    scalarTiltMean A (fun y => A'' y + m * A' y ^ 2) m v x =
      stepD2 A A' A'' m v x + m * (stepD1 A A' m v x) ^ 2 := by
  have H : tiltP A (fun y => A'' y + m * A' y ^ 2) m v x =
      tiltQ A A'' m v x + m * tiltR A A' m v x := by
    unfold tiltP tiltQ tiltR
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (integrable_tiltQ hA''b hA hAm hA''m x)
      ((integrable_tiltR hAb hA hAm hA'm x).const_mul m), integral_const_mul]
  unfold scalarTiltMean stepD2 stepD1
  rw [H, add_div, mul_div_assoc]
  ring

/-- The normalized Bell-polynomial formula gives the genuine third spatial
derivative without requiring positive smoothing variance. -/
theorem hasDerivAt_stepD2_uniform {A A' A'' A''' : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'') (hA'''m : Measurable A''')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hA'''b : ∀ x, |A''' x| ≤ B)
    (m v x : ℝ) :
    HasDerivAt (stepD2 A A' A'' m v) (stepD3Uniform A A' A'' A''' m v x) x := by
  have hAm : Measurable A := (continuous_iff_continuousAt.mpr
    fun x => (hC2.1 x).continuousAt).measurable
  have hA'm : Measurable A' := (continuous_iff_continuousAt.mpr
    fun x => (hC2.2.1 x).continuousAt).measurable
  have hGd (y : ℝ) : HasDerivAt (fun y => A'' y + m * A' y ^ 2)
      (A''' y + 2 * m * A' y * A'' y) y := by
    convert! (hA'''d y).add (((hC2.2.1 y).pow 2).const_mul m) using 1
    ring
  have hGb (y : ℝ) : |A'' y + m * A' y ^ 2| ≤ 1 + |m| := by
    have H := abs_add_le (A'' y) (m * A' y ^ 2)
    simp only [abs_mul, abs_pow, sq_abs] at H
    nlinarith [hC2.abs_second_le_one y,
      mul_le_mul_of_nonneg_left ((sq_le_one_iff_abs_le_one _).mpr (hC2.abs_first_le_one y)) (abs_nonneg m)]
  have hG'b (y : ℝ) : |A''' y + 2 * m * A' y * A'' y| ≤ B + 2 * |m| := by
    have H := abs_add_le (A''' y) (2 * m * A' y * A'' y)
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    have Hp := mul_le_one₀ (hC2.abs_first_le_one y) (abs_nonneg _) (hC2.abs_second_le_one y)
    nlinarith [hA'''b y, mul_le_mul_of_nonneg_left Hp (by positivity : 0 ≤ 2 * |m|)]
  have H := hasDerivAt_scalarTiltMean_spatial hA hAm hA'm
    (hA''m.add ((hA'm.pow_const 2).const_mul m))
    (hA'''m.add (((hA'm.const_mul (2 * m)).mul hA''m)))
    hC2.1 hGd hC2.abs_first_le_one hGb hG'b m v x
  have he (y : ℝ) : (A''' y + 2 * m * A' y * A'' y) +
      m * (A'' y + m * A' y ^ 2) * A' y = parisiThirdPolynomial (A' y) (A'' y) (A''' y) m := by
    unfold parisiThirdPolynomial
    ring
  simp only [Pi.add_apply, Pi.mul_apply, he] at H
  change HasDerivAt (fun y => scalarTiltMean A (fun z => A'' z + m * A' z ^ 2) m v y)
    (scalarTiltMean A (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) m v x -
      m * scalarTiltMean A (fun z => A'' z + m * A' z ^ 2) m v x * stepD1 A A' m v x) x at H
  simp_rw [scalarTiltMean_second_eq hA hAm hA'm hA''m hC2.abs_first_le_one
    hC2.abs_second_le_one] at H
  have HD := ((hasDerivAt_parisiStep_spatial_second hA hAm hA'm hA''m hC2 m v x).pow 2).const_mul m
  convert! H.sub HD using 1
  · funext y
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  · unfold stepD3Uniform
    ring

/-- A normalized mean contracts any uniform absolute bound. -/
theorem scalarTiltMean_abs_le {A G : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (hG : ∀ x, |G x| ≤ B)
    (m v x : ℝ) : |scalarTiltMean A G m v x| ≤ B := by
  have H := norm_integral_le_of_norm_le
    (f := fun z : ℝ => G (x + Real.sqrt v * z) * Real.exp (m * A (x + Real.sqrt v * z)))
    ((integrable_exp_mul_of_hasLinearGrowth hA hAm m x v).const_mul B)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hG _) (Real.exp_pos _).le)
  rw [integral_const_mul] at H
  change |tiltP A G m v x| ≤ B * tiltE A m v x at H
  rw [scalarTiltMean, abs_div, abs_of_pos (tiltE_pos hA hAm x), div_le_iff₀ (tiltE_pos hA hAm x)]
  exact H

/-- Joint continuity of a bounded normalized scalar observable. The constant
bound need not be one; scaling reuses the existing joint Gaussian theorem. -/
theorem continuous_scalarTiltMean_joint {A G : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hcA : Continuous A) (hcG : Continuous G)
    (hG : ∀ x, |G x| ≤ B) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => scalarTiltMean A G p.1 p.2.1 p.2.2) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0)
  have hB1 : 0 < B + 1 := by linarith
  have hs (x : ℝ) : |G x / (B + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hB1, div_le_iff₀ hB1]
    linarith [hG x]
  have H := (continuous_gaussian_weighted_exp_joint hA hcA (hcG.div_const (B + 1)) hs).const_mul (B + 1)
  have he (p : ℝ × (ℝ × ℝ)) :
      (B + 1) * (∫ z, (G (p.2.2 + Real.sqrt p.2.1 * z) / (B + 1)) *
        Real.exp (p.1 * A (p.2.2 + Real.sqrt p.2.1 * z)) ∂(gaussianReal 0 1)) =
      tiltP A G p.1 p.2.1 p.2.2 := by
    simp only [div_mul_eq_mul_div, integral_div]
    unfold tiltP
    field_simp
  simp only [he] at H
  exact H.div (continuous_tiltE_mass_variance_spatial hA hcA)
    (fun p => (tiltE_pos hA hcA.measurable p.2.2).ne')

/-- Changing a mass costs at most five times its decrement in the raw third
polynomial. This cost telescopes, rather than accumulating once per level. -/
theorem parisiThirdPolynomial_mass_change {p q z m n : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1) :
    |parisiThirdPolynomial p q z m - parisiThirdPolynomial p q z n| ≤ 5 * (n - m) := by
  have hgap : 0 ≤ n - m := sub_nonneg.mpr hmn
  have hsq : m ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hm hmn 2
  have hpq : |p * q| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hp (abs_nonneg _) hq
  have hp3 : |p ^ 3| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hp
  calc
    _ = |3 * (m - n) * (p * q) + (m ^ 2 - n ^ 2) * p ^ 3| := by
      congr 1
      unfold parisiThirdPolynomial
      ring
    _ ≤ |3 * (m - n) * (p * q)| + |(m ^ 2 - n ^ 2) * p ^ 3| := abs_add_le _ _
    _ = 3 * (n - m) * |p * q| + (n ^ 2 - m ^ 2) * |p ^ 3| := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_nonpos (sub_nonpos.mpr hmn), abs_of_nonpos (sub_nonpos.mpr hsq)]
      ring
    _ ≤ 3 * (n - m) + (n ^ 2 - m ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hpq (by positivity : 0 ≤ 3 * (n - m)),
        mul_le_mul_of_nonneg_left hp3 (sub_nonneg.mpr hsq)]
    _ ≤ 5 * (n - m) := by nlinarith [mul_nonneg hgap (show 0 ≤ 2 - n - m by linarith)]

theorem parisiThirdPolynomial_lower_mass_bound {p q z m n : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1)
    (hpoly : |parisiThirdPolynomial p q z n| ≤ 6 - 5 * n) :
    |parisiThirdPolynomial p q z m| ≤ 6 - 5 * m := by
  have H := abs_sub_le (parisiThirdPolynomial p q z m) (parisiThirdPolynomial p q z n) 0
  simp only [sub_zero] at H
  linarith [parisiThirdPolynomial_mass_change (z := z) hp hq hm hmn hn]

/-- Exact preservation of the raw third polynomial at the smoothing mass. -/
theorem parisiThirdPolynomial_stepD3Uniform (A A' A'' A''' : ℝ → ℝ) (m v x : ℝ) :
    parisiThirdPolynomial (stepD1 A A' m v x) (stepD2 A A' A'' m v x)
      (stepD3Uniform A A' A'' A''' m v x) m =
      scalarTiltMean A (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) m v x := by
  unfold stepD3Uniform
  simp only [parisiThirdPolynomial]
  ring

/-- The actual third spatial derivative, with the zero-variance step included. -/
noncomputable def parisiFThird {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => -2 * parisiFDeriv s β 0 x * parisiFSecond s β 0 x
  | j + 1 => stepD3Uniform (parisiF s β j) (parisiFDeriv s β j)
      (parisiFSecond s β j) (parisiFThird s β j)
      (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))

/-- Simultaneous spatial C3 regularity and the telescoping mass invariant.
The bound is independent of beta, field, all variances and recursion depth. -/
theorem parisiFThird_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    (∀ x, HasDerivAt (parisiFSecond s β j) (parisiFThird s β j x) x) ∧
      Continuous (parisiFThird s β j) ∧
      (∀ m ∈ Set.Icc 0 (s.m (k + 1 - j)), ∀ x,
        |parisiThirdPolynomial (parisiFDeriv s β j x) (parisiFSecond s β j x)
          (parisiFThird s β j x) m| ≤ 6 - 5 * m) := by
  induction j with
  | zero =>
    have hcP : Continuous (parisiFDeriv s β 0) := continuous_iff_continuousAt.mpr
      fun x => ((parisiF_C2_props s β 0).1.2.1 x).continuousAt
    refine ⟨?_, (hcP.const_mul (-2)).mul (continuous_parisiFSecond s β 0), ?_⟩
    · intro x
      convert! (((parisiF_C2_props s β 0).1.2.1 x).pow 2).const_sub 1 using 1
      simp only [parisiFThird, parisiFSecond, parisiFDeriv]
      ring
    · intro m hm x
      have hp := (parisiF_C2_props s β 0).1.abs_first_le_one x
      apply parisiThirdPolynomial_lower_mass_bound hp
        ((parisiF_C2_props s β 0).1.abs_second_le_one x) hm.1
        (by simpa only [Nat.sub_zero, s.m_top] using hm.2) le_rfl
      have he : parisiThirdPolynomial (parisiFDeriv s β 0 x) (parisiFSecond s β 0 x)
          (parisiFThird s β 0 x) 1 = parisiFDeriv s β 0 x := by
        unfold parisiThirdPolynomial parisiFThird parisiFSecond parisiFDeriv
        ring
      rw [he]
      norm_num
      exact hp
  | succ j ih =>
    have hA := parisiF_hasLinearGrowth s β j
    have hC2 := (parisiF_C2_props s β j).1
    have hAm := parisiF_measurable s β j
    have hA''m := (parisiF_C2_props s β j).2.2
    have hm0 := s.m_nonneg (p := k + 1 - j) (by omega)
    have hm1 := s.m_le_one (p := k + 1 - j) (by omega)
    have hB (x : ℝ) : |parisiFThird s β j x| ≤ 6 := by
      simpa only [parisiThirdPolynomial, mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
        add_zero, sub_zero] using ih.2.2 0 ⟨le_rfl, hm0⟩ x
    have hpoly := ih.2.2 (s.m (k + 1 - j)) ⟨hm0, le_rfl⟩
    constructor
    · exact hasDerivAt_stepD2_uniform hA hC2 hA''m ih.2.1.measurable ih.1 hB _ _
    constructor
    · have hcA : Continuous (parisiF s β j) := continuous_iff_continuousAt.mpr
        fun x => (hC2.1 x).continuousAt
      have hcA' : Continuous (parisiFDeriv s β j) := continuous_iff_continuousAt.mpr
        fun x => (hC2.2.1 x).continuousAt
      have hcA'' := continuous_parisiFSecond s β j
      have hcA''' := ih.2.1
      have hcJ : Continuous (fun x => parisiThirdPolynomial (parisiFDeriv s β j x)
          (parisiFSecond s β j x) (parisiFThird s β j x) (s.m (k + 1 - j))) := by
        unfold parisiThirdPolynomial
        fun_prop
      have hcM := (continuous_scalarTiltMean_joint hA hcA hcJ hpoly).comp
        (by fun_prop : Continuous (fun x : ℝ => (s.m (k + 1 - j),
          (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)), x))))
      have hc := continuous_parisiStep_variance_spatial hC2 hcA'' hm0
      have hcpath : Continuous (fun x : ℝ =>
          (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)), x)) := by fun_prop
      unfold parisiFThird stepD3Uniform
      exact (hcM.sub ((((hc.2.1.comp hcpath).const_mul
        (3 * s.m (k + 1 - j))).mul (hc.2.2.comp hcpath)))).sub
          (((hc.2.1.comp hcpath).pow 3).const_mul (s.m (k + 1 - j) ^ 2))
    · intro m hm x
      have hmle : m ≤ s.m (k + 1 - j) := hm.2.trans
        (s.m_mono' (k + 1 - j) (by omega) (k + 1 - (j + 1)) (by omega))
      apply parisiThirdPolynomial_lower_mass_bound
        ((parisiF_C2_props s β (j + 1)).1.abs_first_le_one x)
        ((parisiF_C2_props s β (j + 1)).1.abs_second_le_one x) hm.1 hmle hm1
      change |parisiThirdPolynomial (stepD1 _ _ _ _ x) (stepD2 _ _ _ _ _ x)
        (stepD3Uniform _ _ _ _ _ _ x) (s.m (k + 1 - j))| ≤ _
      rw [parisiThirdPolynomial_stepD3Uniform]
      exact scalarTiltMean_abs_le hA hAm hpoly _ _ x

theorem hasDerivAt_parisiFSecond {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (parisiFSecond s β j) (parisiFThird s β j x) x :=
  (parisiFThird_props s β j).1 x

theorem continuous_parisiFThird {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Continuous (parisiFThird s β j) := (parisiFThird_props s β j).2.1

/-- Uniform C3 bound for every actual finite Parisi input, including every
zero-variance and zero-mass step. No depth-dependent constant is introduced. -/
theorem abs_parisiFThird_le_six {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    |parisiFThird s β j x| ≤ 6 := by
  simpa only [parisiThirdPolynomial, mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    add_zero, sub_zero] using (parisiFThird_props s β j).2.2 0
      ⟨le_rfl, s.m_nonneg (p := k + 1 - j) (by omega)⟩ x

/-- A fixed scalar input's raw third polynomial has a simple uniform bound
at every physical mass. This bound is not iterated in the recursion. -/
theorem abs_parisiThirdPolynomial_le {p q z m B : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hz : |z| ≤ B) (hm : m ∈ Set.Icc 0 1) :
    |parisiThirdPolynomial p q z m| ≤ B + 4 := by
  have hpq : |p| * |q| ≤ 1 := mul_le_one₀ hp (abs_nonneg _) hq
  have hp3 : |p| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hp
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm.1 hm.2
  have H₁ := abs_add_le z (3 * m * p * q)
  have H₂ := abs_add_le (z + 3 * m * p * q) (m ^ 2 * p ^ 3)
  simp only [abs_mul, abs_pow, abs_of_nonneg hm.1,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)] at H₁ H₂
  unfold parisiThirdPolynomial
  nlinarith [mul_le_mul_of_nonneg_left hpq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hm.1),
    mul_le_mul_of_nonneg_left hp3 (sq_nonneg m)]

/-- A bounded C3 scalar input gives a bounded output at every physical mass,
including zero variance. Only the separate telescoping invariant is used for
the actual recursion's depth-independent bound. -/
theorem abs_stepD3Uniform_le {A A' A'' A''' : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'') (hA'''b : ∀ x, |A''' x| ≤ B)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    |stepD3Uniform A A' A'' A''' m v x| ≤ B + 8 := by
  have hAm : Measurable A := (continuous_iff_continuousAt.mpr
    fun y => (hC2.1 y).continuousAt).measurable
  have hA'm : Measurable A' := (continuous_iff_continuousAt.mpr
    fun y => (hC2.2.1 y).continuousAt).measurable
  have hpoly (y : ℝ) := abs_parisiThirdPolynomial_le (hC2.abs_first_le_one y)
    (hC2.abs_second_le_one y) (hA'''b y) hm
  have hout := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hAm hA'm hA''m
  have hpq := mul_le_one₀ (hout.abs_first_le_one x) (abs_nonneg _)
    (hout.abs_second_le_one x)
  have hp3 : |stepD1 A A' m v x| ^ 3 ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (hout.abs_first_le_one x)
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm.1 hm.2
  have H₁ := abs_sub (scalarTiltMean A
    (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) m v x)
    (3 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x)
  have H₂ := abs_sub (scalarTiltMean A
    (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) m v x -
      3 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x)
    (m ^ 2 * stepD1 A A' m v x ^ 3)
  simp only [abs_mul, abs_pow, abs_of_nonneg hm.1,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)] at H₁ H₂
  unfold stepD3Uniform
  nlinarith [scalarTiltMean_abs_le hA hAm hpoly m v x,
    mul_le_mul_of_nonneg_left hpq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hm.1),
    mul_le_mul_of_nonneg_left hp3 (sq_nonneg m)]

/-- Joint variance/spatial continuity of the actual third-derivative formula,
including zero variance. -/
theorem continuous_stepD3Uniform_variance_spatial {A A' A'' A''' : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hcA'' : Continuous A'') (hcA''' : Continuous A''')
    (hA'''b : ∀ x, |A''' x| ≤ B) {m : ℝ} (hm : m ∈ Set.Icc 0 1) :
    Continuous (fun p : ℝ × ℝ => stepD3Uniform A A' A'' A''' m p.1 p.2) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr
    fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr
    fun y => (hC2.2.1 y).continuousAt
  have hcJ : Continuous (fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m) := by
    unfold parisiThirdPolynomial
    fun_prop
  have hJ (y : ℝ) := abs_parisiThirdPolynomial_le (hC2.abs_first_le_one y)
    (hC2.abs_second_le_one y) (hA'''b y) hm
  have hcM := (continuous_scalarTiltMean_joint hA hcA hcJ hJ).comp
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (m, p)))
  have hc := continuous_parisiStep_variance_spatial hC2 hcA'' hm.1
  exact (hcM.sub (((hc.2.1.const_mul (3 * m)).mul hc.2.2))).sub
    ((hc.2.1.pow 3).const_mul (m ^ 2))

/-- Genuine C3 regularity for a scalar step on an actual Parisi input,
without any positive-variance hypothesis. -/
theorem hasDerivAt_stepD2_parisiF_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (m v x : ℝ) :
    HasDerivAt (stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v)
      (stepD3Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
        (parisiFThird s β j) m v x) x :=
  hasDerivAt_stepD2_uniform (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (parisiF_C2_props s β j).2.2 (continuous_parisiFThird s β j).measurable
    (hasDerivAt_parisiFSecond s β j) (abs_parisiFThird_le_six s β j) m v x

/-- Uniform bound for an additional scalar step of any physical mass; the
constant does not depend on the input scheme's depth or on its variances. -/
theorem abs_stepD3Uniform_parisiF_le {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    |stepD3Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
      (parisiFThird s β j) m v x| ≤ 14 := by
  convert abs_stepD3Uniform_le (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_C2_props s β j).2.2
    (abs_parisiFThird_le_six s β j) hm v x using 1
  norm_num

/-- The earlier positive-smoothing third derivative is exactly the new
endpoint-safe expression, by uniqueness of the genuine spatial derivative. -/
theorem stepD3_eq_stepD3Uniform {A A' A'' A''' : ℝ → ℝ} {B : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hcA'' : Continuous A'') (hA'''m : Measurable A''')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x) (hA'''b : ∀ x, |A''' x| ≤ B)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    stepD3 A A' A'' m v x = stepD3Uniform A A' A'' A''' m v x :=
  (hasDerivAt_stepD2_spatial hA hC2 hcA'' hm hv x).unique
    (hasDerivAt_stepD2_uniform hA hC2 hcA''.measurable hA'''m hA'''d hA'''b m v x)

/-- The singular positive-smoothing estimate can now be replaced, for actual
Parisi inputs, by a constant independent of variance and recursion depth. -/
theorem abs_stepD3_parisiF_le_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    |stepD3 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) m v x| ≤ 14 := by
  rw [(hasDerivAt_stepD2_parisiF_spatial s β j hm hv x).unique
    (hasDerivAt_stepD2_parisiF_uniform s β j m v x)]
  exact abs_stepD3Uniform_parisiF_le s β j hm v x

end SpinGlass.Targets
