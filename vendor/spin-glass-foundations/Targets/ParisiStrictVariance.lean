module

public import Targets.GaussianCauchySchwarzEquality
public import Targets.Section5PairScalarComparison

@[expose] public section

/-!
# Strict positivity under the actual Gaussian tilted law

These results supply the nondegeneracy needed for the strict scalar
interchange. Positive variance is essential; the mass is allowed to vanish.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace SpinGlass.Targets

/-- A continuous strictly increasing bounded profile has positive variance
under the actual exponential Gaussian tilt. No equality case is assumed. -/
theorem tilt_variance_pos_of_strictMono {A A' : ℝ → ℝ} (hA : HasLinearGrowth A)
    (hc : Continuous A) (hc' : Continuous A') (hbd : ∀ y, |A' y| ≤ 1)
    (hmono : StrictMono A') (m : ℝ) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    0 < tiltR A A' m v x / tiltE A m v x -
      (tiltP A A' m v x / tiltE A m v x) ^ 2 := by
  let g := fun z => Real.exp (m / 2 * A (x + Real.sqrt v * z))
  let f := fun z => A' (x + Real.sqrt v * z) * g z
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hgpos (z : ℝ) : 0 < g z := Real.exp_pos _
  have hgg (z : ℝ) : g z ^ 2 = Real.exp (m * A (x + Real.sqrt v * z)) := by
    dsimp [g]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hff (z : ℝ) : f z ^ 2 = A' (x + Real.sqrt v * z) ^ 2 *
      Real.exp (m * A (x + Real.sqrt v * z)) := by
    dsimp only [f]
    rw [mul_pow, hgg]
  have hfg (z : ℝ) : f z * g z = A' (x + Real.sqrt v * z) *
      Real.exp (m * A (x + Real.sqrt v * z)) := by
    dsimp only [f]
    rw [mul_assoc, ← sq, hgg]
  have hffi : Integrable (fun z => f z ^ 2) (gaussianReal 0 1) := by
    simp_rw [hff]
    exact integrable_tiltR hbd hA hc.measurable hc'.measurable x
  have hggi : Integrable (fun z => g z ^ 2) (gaussianReal 0 1) := by
    simp_rw [hgg]
    exact integrable_exp_mul_of_hasLinearGrowth hA hc.measurable m x v
  have hfgi : Integrable (fun z => f z * g z) (gaussianReal 0 1) := by
    simp_rw [hfg]
    exact integrable_tiltP hbd hA hc.measurable hc'.measurable x
  have hE : 0 < tiltE A m v x := tiltE_pos hA hc.measurable x
  have hCS := sq_integral_mul_le hbd hA hc.measurable hc'.measurable (m := m) (v := v) x
  have hstrict : tiltP A A' m v x ^ 2 < tiltR A A' m v x * tiltE A m v x := by
    apply lt_of_le_of_ne hCS
    intro he
    have he' : (∫ z, f z * g z ∂gaussianReal 0 1) ^ 2 =
        (∫ z, f z ^ 2 ∂gaussianReal 0 1) * (∫ z, g z ^ 2 ∂gaussianReal 0 1) := by
      simp_rw [hfg, hff, hgg]
      exact he
    obtain ⟨c, hprop⟩ := eq_mul_of_gaussian_cauchySchwarz_eq hf hg hgpos hffi hggi hfgi he'
    have hcst (z : ℝ) : A' (x + Real.sqrt v * z) = c :=
      mul_right_cancel₀ (hgpos z).ne' (hprop z)
    have hh := hmono (show x + Real.sqrt v * 0 < x + Real.sqrt v * 1 by
      nlinarith [Real.sqrt_pos.mpr hv])
    rw [hcst, hcst] at hh
    exact (lt_irrefl c) hh
  rw [sub_pos, div_pow, div_lt_div_iff₀ (sq_pos_of_pos hE) hE]
  nlinarith

/-- Strict integral order from continuous order and one strict point. Gaussian
absolute continuity turns an integral equality into equality everywhere. -/
theorem integral_gaussian_lt_of_continuous_le {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable f (gaussianReal 0 1)) (hgi : Integrable g (gaussianReal 0 1))
    (hle : ∀ z, f z ≤ g z) {z : ℝ} (hlt : f z < g z) :
    (∫ y, f y ∂gaussianReal 0 1) < ∫ y, g y ∂gaussianReal 0 1 := by
  apply lt_of_le_of_ne (integral_mono hfi hgi hle)
  intro he
  have hae := (integral_eq_iff_of_ae_le hfi hgi (Eventually.of_forall hle)).mp he
  have hv : f =ᵐ[volume] g :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).ae_eq hae
  exact hlt.ne (congrFun (MeasureTheory.Measure.eq_of_ae_eq hv hf hg) z)

/-- One strict point between continuous profiles makes every positive-variance
Gaussian step strict, including the zero-mass expectation. -/
theorem parisiStep_lt_of_continuous_le {A B : ℝ → ℝ} {m v : ℝ}
    (hm : 0 ≤ m) (hv : 0 < v) (hA : HasLinearGrowth A) (hB : HasLinearGrowth B)
    (hcA : Continuous A) (hcB : Continuous B) (hle : ∀ z, A z ≤ B z)
    {z : ℝ} (hlt : A z < B z) (x : ℝ) :
    parisiStep m v A x < parisiStep m v B x := by
  have hs : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hex : x + Real.sqrt v * ((z - x) / Real.sqrt v) = z := by field_simp; ring
  have hlt' : A (x + Real.sqrt v * ((z - x) / Real.sqrt v)) <
      B (x + Real.sqrt v * ((z - x) / Real.sqrt v)) := by simpa only [hex] using hlt
  have hcA' : Continuous (fun y => A (x + Real.sqrt v * y)) := by fun_prop
  have hcB' : Continuous (fun y => B (x + Real.sqrt v * y)) := by fun_prop
  by_cases hm0 : m = 0
  · simpa only [parisiStep, if_pos hm0] using integral_gaussian_lt_of_continuous_le
      hcA' hcB' (integrable_of_hasLinearGrowth hA hcA.measurable x v)
      (integrable_of_hasLinearGrowth hB hcB.measurable x v) (fun y => hle _) hlt'
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  simp only [parisiStep, if_neg hm0]
  apply mul_lt_mul_of_pos_left _ (one_div_pos.mpr hmpos)
  apply Real.log_lt_log (smoothing_integral_pos hA hcA.measurable x)
  exact integral_gaussian_lt_of_continuous_le (Real.continuous_exp.comp (hcA'.const_mul m))
    (Real.continuous_exp.comp (hcB'.const_mul m))
    (integrable_exp_mul_of_hasLinearGrowth hA hcA.measurable m x v)
    (integrable_exp_mul_of_hasLinearGrowth hB hcB.measurable m x v)
    (fun y => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hle _) hm))
    (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hlt' hmpos))

end SpinGlass.Targets
