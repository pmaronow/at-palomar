module

/-
# Gaussian integration by parts in a cascade field

For one Gaussian increment, differentiate both the observable and its tilted
weight.  The resulting identity is needed at each level of Talagrand's
interpolation.  All integrability obligations are included.
-/
public import Targets.CascadeSecondPi
public import ParisiFormula.PiStein

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {n : ℕ}

/-- The exponential quotient also describes the zero-mass weight. -/
theorem tiltWeightPi_eq_exp_div (m v : ℝ) (A : (Fin n → ℝ) → ℝ)
    (x z : Fin n → ℝ) :
    tiltWeightPi n m v A x z = Real.exp (m * A (fun i => x i + Real.sqrt v * z i)) /
      ∫ w, Real.exp (m * A (fun i => x i + Real.sqrt v * w i)) ∂piGauss n := by
  by_cases hm : m = 0
  · simp [tiltWeightPi, hm]
  · simp only [tiltWeightPi, if_neg hm]

/-- Passing a coordinate line through the Gaussian shift contributes `√v`. -/
theorem hasDerivAt_gaussianShift_coord {G G' : (Fin n → ℝ) → ℝ}
    (i : Fin n) (v : ℝ) (x z : Fin n → ℝ) (r : ℝ)
    (hG : ∀ (y : Fin n → ℝ) (u : ℝ), HasDerivAt (fun w => G (y + w • Pi.single i 1))
      (G' (y + u • Pi.single i 1)) u) :
    HasDerivAt (fun u : ℝ => G (fun l => x l + Real.sqrt v * ((z + u • Pi.single i 1) : Fin n → ℝ) l))
      (Real.sqrt v * G' (fun l => x l + Real.sqrt v * ((z + r • Pi.single i 1) : Fin n → ℝ) l)) r := by
  have hshift : ∀ u : ℝ, (fun l => x l + Real.sqrt v * ((z + u • Pi.single i 1) : Fin n → ℝ) l) =
      (fun l => x l + Real.sqrt v * z l) + (u * Real.sqrt v) • Pi.single i 1 := by
    intro u
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hshift]
  refine ((hG (fun l => x l + Real.sqrt v * z l) (r * Real.sqrt v)).comp r
    ((hasDerivAt_id r).mul_const (Real.sqrt v))).congr_deriv ?_
  ring

/-- A Gaussian coordinate times a bounded observable is integrable under the tilt. -/
theorem integrable_coord_mul_tiltWeightPi {A G : (Fin n → ℝ) → ℝ}
    {m v C D L B : ℝ} (i : Fin n) (x : Fin n → ℝ)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hAm : Measurable A) (hGm : Measurable G)
    (hA : ∀ y, |A y| ≤ C + D * l1 y)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y')) (hG : ∀ y, |G y| ≤ B) :
    Integrable (fun z => z i * (G (fun l => x l + Real.sqrt v * z l) *
      tiltWeightPi n m v A x z)) (piGauss n) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0)
  have hbound : ∀ z : Fin n → ℝ,
      |z i * G (fun l => x l + Real.sqrt v * z l)| ≤ 0 + B * l1 z := by
    intro z
    rw [abs_mul, zero_add]
    calc
      _ ≤ l1 z * B := mul_le_mul
        (Finset.single_le_sum (fun l _ => abs_nonneg (z l)) (Finset.mem_univ i))
        (hG _) (abs_nonneg _) (l1_nonneg z)
      _ = _ := mul_comm _ _
  have hi := integrable_mul_tiltWeightPi_of_bound (m := m) (v := v)
    hL hD hLip hA hAm x ((measurable_pi_apply i).mul (hGm.comp (measurable_shift v x)))
    hB hbound
  simpa only [Pi.mul_apply, Function.comp_apply, mul_assoc] using hi

/-- Stein for a tilted cascade increment:
`E[zᵢ G(x+√v z) W] = √v E[(∂ᵢG + m G ∂ᵢA)(x+√v z) W]`.
The normalizing denominator is constant in the integration variable. -/
theorem stein_tiltWeightPi {A A' G G' : (Fin n → ℝ) → ℝ}
    {m v C D L BA BG BG' : ℝ} (i : Fin n) (x : Fin n → ℝ)
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hAm : Measurable A) (hA'm : Measurable A')
    (hGm : Measurable G) (hG'm : Measurable G')
    (hA : ∀ y, |A y| ≤ C + D * l1 y)
    (hLip : ∀ y y', |A y - A y'| ≤ L * l1 (y - y'))
    (hA' : ∀ y, |A' y| ≤ BA) (hG : ∀ y, |G y| ≤ BG) (hG' : ∀ y, |G' y| ≤ BG')
    (hAd : ∀ (y : Fin n → ℝ) (u : ℝ), HasDerivAt (fun w => A (y + w • Pi.single i 1))
      (A' (y + u • Pi.single i 1)) u)
    (hGd : ∀ (y : Fin n → ℝ) (u : ℝ), HasDerivAt (fun w => G (y + w • Pi.single i 1))
      (G' (y + u • Pi.single i 1)) u) :
    (∫ z, z i * (G (fun l => x l + Real.sqrt v * z l) * tiltWeightPi n m v A x z)
      ∂piGauss n) =
      Real.sqrt v * ∫ z, (G' (fun l => x l + Real.sqrt v * z l) +
        m * G (fun l => x l + Real.sqrt v * z l) * A' (fun l => x l + Real.sqrt v * z l)) *
        tiltWeightPi n m v A x z ∂piGauss n := by
  let S := fun z : Fin n → ℝ => fun l => x l + Real.sqrt v * z l
  let F := fun z => G (S z) * tiltWeightPi n m v A x z
  let H := fun y => G' y + m * G y * A' y
  let F' := fun z => Real.sqrt v * (H (S z) * tiltWeightPi n m v A x z)
  have hBG : 0 ≤ BG := (abs_nonneg _).trans (hG 0)
  have hBA : 0 ≤ BA := (abs_nonneg _).trans (hA' 0)
  have hBG' : 0 ≤ BG' := (abs_nonneg _).trans (hG' 0)
  have hHm : Measurable H := hG'm.add ((hGm.const_mul m).mul hA'm)
  have hHb : ∀ y, |H y| ≤ BG' + |m| * BG * BA := by
    intro y
    refine (abs_add_le _ _).trans (add_le_add (hG' y) ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hG y) (abs_nonneg _))
      (hA' y) (abs_nonneg _) (by positivity)
  have hFm : Measurable F := (hGm.comp (measurable_shift v x)).mul
    (measurable_tiltWeightPi hAm x)
  have hF'm : Measurable F' := measurable_const.mul
    ((hHm.comp (measurable_shift v x)).mul (measurable_tiltWeightPi hAm x))
  have hFi : Integrable F (piGauss n) := integrable_mul_tiltWeightPi_of_bound
    hL hD hLip hA hAm x (hGm.comp (measurable_shift v x)) (a := BG) (b := 0) le_rfl
    (fun z => by simpa using hG (S z))
  have hzFi : Integrable (fun z => z i * F z) (piGauss n) :=
    integrable_coord_mul_tiltWeightPi i x hD hL hAm hGm hA hLip hG
  have hF'i : Integrable F' (piGauss n) :=
    (integrable_mul_tiltWeightPi_of_bound hL hD hLip hA hAm x
      (hHm.comp (measurable_shift v x)) (a := BG' + |m| * BG * BA) (b := 0) le_rfl
      (fun z => by simpa using hHb (S z))).const_mul (Real.sqrt v)
  have hd : ∀ (z : Fin n → ℝ) (r : ℝ), HasDerivAt (fun u => F (z + u • Pi.single i 1))
      (F' (z + r • Pi.single i 1)) r := by
    intro z r
    have hgd := hasDerivAt_gaussianShift_coord i v x z r hGd
    have had := hasDerivAt_gaussianShift_coord i v x z r hAd
    simp only [F, F', H, S, tiltWeightPi_eq_exp_div, ← mul_div_assoc]
    exact (((hgd.mul ((had.const_mul m).exp)).div_const
      (∫ w, Real.exp (m * A (S w)) ∂piGauss n))).congr_deriv (by ring)
  have hs := stein_pi_of_hasDerivAt i hd hFm hF'm hFi hzFi hF'i
  simpa only [F', integral_const_mul] using hs

end SpinGlass.Targets
