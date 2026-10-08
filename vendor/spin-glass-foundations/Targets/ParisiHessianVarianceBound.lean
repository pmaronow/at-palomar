module

public import Targets.ParisiHessianVariance
public import Targets.ParisiThirdUniform

@[expose] public section

/-!
# Zero-inclusive constants for positive-variance Hessian derivatives

Gaussian heat differentiation of bounded C2 observables gives constants with
no inverse variance. Applied to the moments defining the scalar Hessian, this
requires bounded fourth spatial input derivatives. The resulting estimate is
uniform over every positive variance, including arbitrarily close to zero.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The unnormalized heat-generator polynomial for a scalar observable. -/
def scalarObservableHeat (A' A'' G G' G'' : ℝ → ℝ) (m x : ℝ) : ℝ :=
  G'' x + 2 * m * G' x * A' x + m * G x * A'' x + m ^ 2 * G x * (A' x) ^ 2

theorem scalarObservableHeat_abs_le {A A' A'' G G' G'' : ℝ → ℝ} {B C D m : ℝ}
    (hC2 : HasParisiC2 A A' A'') (hm : m ∈ Set.Icc 0 1)
    (hG : ∀ x, |G x| ≤ B) (hG' : ∀ x, |G' x| ≤ C) (hG'' : ∀ x, |G'' x| ≤ D)
    (x : ℝ) : |scalarObservableHeat A' A'' G G' G'' m x| ≤ D + 2 * C + 2 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG x)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hG' x)
  have hp : (A' x) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hC2.abs_first_le_one x)
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm.1 hm.2
  have h1 : |2 * m * G' x * A' x| ≤ 2 * C := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * 1 * C * 1 := by gcongr; exact hm.2; exact hG' x; exact hC2.abs_first_le_one x
      _ = _ := by ring
  have h2 : |m * G x * A'' x| ≤ B := by
    rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
    calc
      _ ≤ 1 * B * 1 := by gcongr; exact hm.2; exact hG x; exact hC2.abs_second_le_one x
      _ = _ := by ring
  have h3 : |m ^ 2 * G x * (A' x) ^ 2| ≤ B := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow, sq_abs, sq_abs]
    calc
      _ ≤ 1 * B * 1 := by gcongr; exact hG x
      _ = _ := by ring
  have H1 := abs_add_le (G'' x) (2 * m * G' x * A' x)
  have H2 := abs_add_le (G'' x + 2 * m * G' x * A' x) (m * G x * A'' x)
  have H3 := abs_add_le (G'' x + 2 * m * G' x * A' x + m * G x * A'' x)
    (m ^ 2 * G x * (A' x) ^ 2)
  unfold scalarObservableHeat
  linarith [hG'' x]

/-- Heat differentiation of a bounded C2 observable's exponential moment.
This uses the existing Gaussian heat generator, not a new heat-kernel proof. -/
theorem hasDerivAt_tiltP_variance_heat {A A' A'' G G' G'' : ℝ → ℝ} {B C D : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'')
    (hGd : ∀ x, HasDerivAt G (G' x) x) (hG'd : ∀ x, HasDerivAt G' (G'' x) x)
    (hG''m : Measurable G'')
    (hG : ∀ x, |G x| ≤ B) (hG' : ∀ x, |G' x| ≤ C) (hG'' : ∀ x, |G'' x| ≤ D)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => tiltP A G m w x)
      (tiltP A (scalarObservableHeat A' A'' G G' G'' m) m v x / 2) v := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hG' 0)
  have hD : 0 ≤ D := (abs_nonneg _).trans (hG'' 0)
  have hAm := (continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt).measurable
  have hA'm := (continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt).measurable
  have hGm := (continuous_iff_continuousAt.mpr fun y => (hGd y).continuousAt).measurable
  have hG'm := (continuous_iff_continuousAt.mpr fun y => (hG'd y).continuousAt).measurable
  obtain ⟨a, b, ha, hb, hAb⟩ := hA
  let M := D + 2 * C + 2 * B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have he (y : ℝ) : Real.exp (m * A y) ≤
      Real.exp (m * a) * Real.exp ((m * b) * |y|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ((le_abs_self (A y)).trans (hAb y)) hm.1]
  have hcoef (F : ℝ → ℝ) (hF : ∀ y, |F y| ≤ M) (y : ℝ) :
      |F y * Real.exp (m * A y)| ≤ (M * Real.exp (m * a)) * Real.exp ((m * b) * |y|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul (hF y) (he y) (Real.exp_pos _).le hM).trans_eq (by ring)
  have hg1 (y : ℝ) : |G' y + m * G y * A' y| ≤ M := by
    have H := abs_add_le (G' y) (m * G y * A' y)
    have hp : |m * G y * A' y| ≤ B := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
      calc
        _ ≤ 1 * B * 1 := by gcongr; exact hm.2; exact hG y; exact hC2.abs_first_le_one y
        _ = _ := by ring
    dsimp [M]
    linarith [hG' y]
  have hd (y : ℝ) : HasDerivAt (fun y => G y * Real.exp (m * A y))
      ((G' y + m * G y * A' y) * Real.exp (m * A y)) y := by
    convert! (hGd y).mul (((hC2.1 y).const_mul m).exp) using 1
    ring
  have hd' (y : ℝ) : HasDerivAt
      (fun y => (G' y + m * G y * A' y) * Real.exp (m * A y))
      (scalarObservableHeat A' A'' G G' G'' m y * Real.exp (m * A y)) y := by
    convert! ((hG'd y).add (((hGd y).const_mul m).mul (hC2.2.1 y))).mul
      (((hC2.1 y).const_mul m).exp) using 1
    simp only [Pi.add_apply, Pi.mul_apply]
    unfold scalarObservableHeat
    ring
  apply hasDerivAt_integral_gaussian_variance (by positivity : 0 ≤ M * Real.exp (m * a))
    (mul_nonneg hm.1 hb) hd hd'
    (by unfold scalarObservableHeat; fun_prop)
    (hcoef G (fun y => (hG y).trans (by dsimp [M]; linarith)))
    (hcoef _ hg1) (hcoef _ (scalarObservableHeat_abs_le hC2 hm hG hG' hG'')) x hv

/-- A bounded C2 observable has a variance derivative with a constant that
does not blow up near zero variance. -/
theorem scalarTiltMean_variance_derivative_bound {A A' A'' G G' G'' : ℝ → ℝ}
    {B C D : ℝ} (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'')
    (hGd : ∀ x, HasDerivAt G (G' x) x) (hG'd : ∀ x, HasDerivAt G' (G'' x) x)
    (hG''m : Measurable G'')
    (hG : ∀ x, |G x| ≤ B) (hG' : ∀ x, |G' x| ≤ C) (hG'' : ∀ x, |G'' x| ≤ D)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    ∃ d, HasDerivAt (fun w => scalarTiltMean A G m w x) d v ∧
      |d| ≤ D / 2 + C + 2 * B := by
  have hAm := (continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt).measurable
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0)
  let H := scalarObservableHeat A' A'' G G' G'' m
  let E := scalarObservableHeat A' A'' (fun _ => 1) (fun _ => 0) (fun _ => 0) m
  have hdN := hasDerivAt_tiltP_variance_heat hA hC2 hA''m hGd hG'd hG''m hG hG' hG'' hm x hv
  have hdE := hasDerivAt_tiltP_variance_heat hA hC2 hA''m
    (G := fun _ => 1) (G' := fun _ => 0) (G'' := fun _ => 0)
    (fun y => hasDerivAt_const y 1) (fun y => hasDerivAt_const y 0) measurable_const
    (B := 1) (by simp) (C := 0) (by simp) (D := 0) (by simp) hm x hv
  change HasDerivAt (fun w => tiltP A G m w x) (tiltP A H m v x / 2) v at hdN
  have he (w : ℝ) : tiltP A (fun _ => 1) m w x = tiltE A m w x := by simp [tiltP, tiltE]
  simp only [he] at hdE
  change HasDerivAt (fun w => tiltE A m w x) (tiltP A E m v x / 2) v at hdE
  let d := scalarTiltMean A H m v x / 2 - scalarTiltMean A G m v x * scalarTiltMean A E m v x / 2
  refine ⟨d, ?_, ?_⟩
  · convert! hdN.div hdE (tiltE_pos hA hAm x).ne' using 1
    unfold d scalarTiltMean
    field_simp
  · have hH := scalarTiltMean_abs_le hA hAm (scalarObservableHeat_abs_le hC2 hm hG hG' hG'') m v x
    have hG0 := scalarTiltMean_abs_le hA hAm hG m v x
    have hE0 := scalarTiltMean_abs_le hA hAm
      (scalarObservableHeat_abs_le hC2 hm (G := fun _ => 1) (G' := fun _ => 0) (G'' := fun _ => 0)
        (B := 1) (by simp) (C := 0) (by simp) (D := 0) (by simp)) m v x
    change |scalarTiltMean A H m v x| ≤ D + 2 * C + 2 * B at hH
    change |scalarTiltMean A E m v x| ≤ 0 + 2 * 0 + 2 * 1 at hE0
    norm_num at hE0
    have hp := mul_le_mul hG0 hE0 (abs_nonneg _) hB
    have hh := abs_sub (scalarTiltMean A H m v x / 2)
      (scalarTiltMean A G m v x * scalarTiltMean A E m v x / 2)
    simp only [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    dsimp [d]
    linarith

/-- The actual Hessian variance derivative has a bound uniform down to zero
variance whenever the input has bounded third and fourth spatial derivatives.
This assertion is about every positive variance, not a derivative at zero. -/
theorem abs_stepD2Variance_le_of_C4 {A A' A'' A''' A'''' : ℝ → ℝ} {K3 K4 : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA3d : ∀ x, HasDerivAt A'' (A''' x) x) (hA4d : ∀ x, HasDerivAt A''' (A'''' x) x)
    (hA4m : Measurable A'''') (hA3b : ∀ x, |A''' x| ≤ K3) (hA4b : ∀ x, |A'''' x| ≤ K4)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (x : ℝ) {v : ℝ} (hv : 0 < v) :
    |stepD2Variance A A' A'' A''' m v x| ≤ K4 + 4 * K3 + 16 := by
  have h3 : 0 ≤ K3 := (abs_nonneg _).trans (hA3b 0)
  have h4 : 0 ≤ K4 := (abs_nonneg _).trans (hA4b 0)
  have hA1m := (continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt).measurable
  have hA2m := (continuous_iff_continuousAt.mpr fun y => (hA3d y).continuousAt).measurable
  have hA3m := (continuous_iff_continuousAt.mpr fun y => (hA4d y).continuousAt).measurable
  obtain ⟨dQ, hdQ, hbQ⟩ := scalarTiltMean_variance_derivative_bound hA hC2 hA2m
    hA3d hA4d hA4m hC2.abs_second_le_one hA3b hA4b hm x hv
  obtain ⟨dS, hdS, hbS⟩ := scalarTiltMean_variance_derivative_bound hA hC2 hA2m
    hC2.2.1 hA3d hA3m hC2.abs_first_le_one hC2.abs_second_le_one hA3b hm x hv
  have hg1 (y : ℝ) : HasDerivAt (fun y => (A' y) ^ 2) (2 * A' y * A'' y) y := by
    convert! (hC2.2.1 y).pow 2 using 1
    ring
  have hg2 (y : ℝ) : HasDerivAt (fun y => 2 * A' y * A'' y)
      (2 * (A'' y) ^ 2 + 2 * A' y * A''' y) y := by
    convert! ((hC2.2.1 y).const_mul 2).mul (hA3d y) using 1
    ring
  have hg0b (y : ℝ) : |(A' y) ^ 2| ≤ 1 := by
    rw [abs_pow, sq_abs]
    exact (sq_le_one_iff_abs_le_one _).mpr (hC2.abs_first_le_one y)
  have hg1b (y : ℝ) : |2 * A' y * A'' y| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul (hC2.abs_first_le_one y) (hC2.abs_second_le_one y)
      (abs_nonneg _) zero_le_one]
  have hg2b (y : ℝ) : |2 * (A'' y) ^ 2 + 2 * A' y * A''' y| ≤ 2 + 2 * K3 := by
    have H := abs_add_le (2 * (A'' y) ^ 2) (2 * A' y * A''' y)
    simp only [abs_mul, abs_pow, sq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith [mul_le_mul (hC2.abs_first_le_one y) (hA3b y) (abs_nonneg _) zero_le_one,
      (sq_le_one_iff_abs_le_one _).mpr (hC2.abs_second_le_one y)]
  obtain ⟨dR, hdR, hbR⟩ := scalarTiltMean_variance_derivative_bound hA hC2 hA2m
    hg1 hg2 (((hA2m.pow_const 2).const_mul 2).add ((hA1m.const_mul 2).mul hA3m))
    hg0b hg1b hg2b hm x hv
  have H : HasDerivAt (fun w => stepD2 A A' A'' m w x)
      (dQ + m * (dR - 2 * stepD1 A A' m v x * dS)) v := by
    convert! hdQ.add ((hdR.sub (hdS.pow 2)).const_mul m) using 1
    norm_num [scalarTiltMean, stepD1]
  rw [(hasDerivAt_stepD2_variance hA hC2 hA3d hA3m hA3b m x hv).unique H]
  have hS := scalarTiltMean_abs_le hA
    (continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt).measurable
    hC2.abs_first_le_one m v x
  change |stepD1 A A' m v x| ≤ 1 at hS
  have hp := mul_le_mul hS hbS (abs_nonneg dS) zero_le_one
  have hi := abs_sub dR (2 * stepD1 A A' m v x * dS)
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  have hib : |dR - 2 * stepD1 A A' m v x * dS| ≤ 2 * K3 + 11 := by
    nlinarith
  have hmB := mul_le_mul hm.2 hib (abs_nonneg _) zero_le_one
  have hh := abs_add_le dQ (m * (dR - 2 * stepD1 A A' m v x * dS))
  rw [abs_mul, abs_of_nonneg hm.1] at hh
  nlinarith

end SpinGlass.Targets
