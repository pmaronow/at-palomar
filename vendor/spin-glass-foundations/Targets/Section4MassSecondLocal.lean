module

public import Targets.ParisiMassUniform

@[expose] public section

/-!
# Two-sided local scalar mass bounds

Reflection and a dilation of the field reuse the checked scalar cumulant
bounds. They provide an open mass neighborhood of the entire physical interval
`[0,1]`, needed for genuine second derivatives at its endpoints.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem scalar_mass_bounds_abs_one {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {m v V : ℝ} (hm : |m| ≤ 1) (hv : v ∈ Set.Icc 0 V) (x : ℝ) :
    |deriv (fun a => parisiStep a v A x) m| ≤ parisiMassFirstBound V ∧
      |iteratedDeriv 2 (fun a => parisiStep a v A x) m| ≤ parisiMassSecondBound V := by
  by_cases hm0 : 0 ≤ m
  · exact parisiStep_mass_derivatives_uniform hA hAm hLip ⟨hm0, (le_abs_self m).trans hm⟩ hv x
  have hAn : HasLinearGrowth (fun y => -A y) := by
    obtain ⟨C, L, hC, hL, hb⟩ := hA
    exact ⟨C, L, hC, hL, fun y => by simpa only [abs_neg] using hb y⟩
  have hLn : ∀ y z, |-A y - -A z| ≤ |y - z| := by
    intro y z
    simpa only [neg_sub_neg, abs_sub_comm] using hLip y z
  let G := fun a => parisiStep a v (fun y => -A y) x
  have hG (a : ℝ) : AnalyticAt ℝ G a := analyticAt_parisiStep_mass hAn hAm.neg v x a
  have he (a : ℝ) : -G (-a) = parisiStep a v A x := by
    simp only [G, parisiStep_neg_input, neg_neg]
  have hD (a : ℝ) : HasDerivAt (fun a => parisiStep a v A x) (deriv G (-a)) a := by
    have H := (((hG (-a)).differentiableAt.hasDerivAt.comp a (hasDerivAt_id a).neg).neg)
    convert! H using 1
    · funext b; exact (he b).symm
    · ring
  have hd : (fun a => deriv (fun b => parisiStep b v A x) a) = fun a => deriv G (-a) := by
    funext a; exact (hD a).deriv
  have hDD : iteratedDeriv 2 (fun a => parisiStep a v A x) m = -iteratedDeriv 2 G (-m) := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [show deriv (fun a => parisiStep a v A x) = (fun a => deriv G (-a)) from hd]
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (((hG (-m)).deriv.differentiableAt.hasDerivAt).comp m (hasDerivAt_id m).neg).deriv
  have H := parisiStep_mass_derivatives_uniform hAn hAm.neg hLn
    (m := -m) ⟨by linarith, by simpa only [abs_of_neg (lt_of_not_ge hm0)] using hm⟩ hv x
  rw [(hD m).deriv, hDD, abs_neg]
  exact H

private theorem scalar_mass_dilation (A : ℝ → ℝ) (m x : ℝ) {v : ℝ} (_hv : 0 ≤ v) :
    parisiStep m v A x = parisiStep (m / 2) (4 * v) (fun y => 2 * A (y / 2)) (2 * x) / 2 := by
  have hs : Real.sqrt (4 * v) = 2 * Real.sqrt v := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hx (z : ℝ) : (2 * x + Real.sqrt (4 * v) * z) / 2 = x + Real.sqrt v * z := by rw [hs]; ring
  by_cases hm : m = 0
  · simp only [hm, zero_div, parisiStep, if_true, hx, integral_const_mul]
    ring
  · have hm' : m / 2 ≠ 0 := div_ne_zero hm (by norm_num)
    simp only [parisiStep, if_neg hm, if_neg hm', hx]
    have hmul (z : ℝ) : m / 2 * (2 * A (x + Real.sqrt v * z)) = m * A (x + Real.sqrt v * z) := by ring
    simp_rw [hmul]
    field_simp

/-- A uniform bound on an open neighborhood of all physical masses.
The looser constants here are used only to justify differentiation; the final
physical-interval bound retains the sharper original constants. -/
theorem parisiStep_mass_derivatives_local_uniform {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {m v V : ℝ} (hm : |m| ≤ 2) (hv : v ∈ Set.Icc 0 V) (x : ℝ) :
    |deriv (fun a => parisiStep a v A x) m| ≤ parisiMassFirstBound (4 * V) ∧
      |iteratedDeriv 2 (fun a => parisiStep a v A x) m| ≤ parisiMassSecondBound (4 * V) := by
  let B := fun y => 2 * A (y / 2)
  have hB : HasLinearGrowth B := by
    obtain ⟨C, L, hC, hL, hb⟩ := hA
    refine ⟨2 * C, L, by positivity, hL, fun y => ?_⟩
    have H := hb (y / 2)
    dsimp only [B]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    nlinarith
  have hBm : Measurable B := (hAm.comp (measurable_id.div_const 2)).const_mul 2
  have hBL : ∀ y z, |B y - B z| ≤ |y - z| := by
    intro y z
    have H := hLip (y / 2) (z / 2)
    dsimp only [B]
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    linarith
  let G := fun a => parisiStep a (4 * v) B (2 * x)
  have hG (a : ℝ) : AnalyticAt ℝ G a := analyticAt_parisiStep_mass hB hBm _ _ _
  have hD (a : ℝ) : HasDerivAt (fun a => parisiStep a v A x) (deriv G (a / 2) / 4) a := by
    have H := (((hG (a / 2)).differentiableAt.hasDerivAt).comp a
      ((hasDerivAt_id a).div_const 2)).div_const 2
    convert! H using 1
    · funext b
      exact scalar_mass_dilation A b x hv.1
    · ring
  have hd : deriv (fun a => parisiStep a v A x) = fun a => deriv G (a / 2) / 4 := by
    funext a; exact (hD a).deriv
  have hDD : iteratedDeriv 2 (fun a => parisiStep a v A x) m = iteratedDeriv 2 G (m / 2) / 8 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [hd]
    have H := (((hG (m / 2)).deriv.differentiableAt.hasDerivAt).comp m
      ((hasDerivAt_id m).div_const 2)).div_const 4
    convert! H.deriv using 1
    ring
  have H := scalar_mass_bounds_abs_one hB hBm hBL (m := m / 2)
    (by rw [abs_div]; norm_num; linarith) (v := 4 * v) (V := 4 * V)
    ⟨mul_nonneg (by norm_num) hv.1, by linarith [hv.2]⟩ (2 * x)
  rw [(hD m).deriv, hDD]
  rw [abs_div, abs_div]
  norm_num only [show |(4 : ℝ)| = 4 from by norm_num, show |(8 : ℝ)| = 8 from by norm_num]
  constructor
  · change |deriv G (m / 2)| / 4 ≤ _
    nlinarith [H.1, parisiMassFirstBound_nonneg (4 * V)]
  · change |iteratedDeriv 2 G (m / 2)| / 8 ≤ _
    nlinarith [H.2, parisiMassSecondBound_nonneg (4 * V)]

end SpinGlass.Targets
