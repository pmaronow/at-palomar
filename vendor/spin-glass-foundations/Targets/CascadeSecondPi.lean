module

/-
# Differentiating tilted averages in Talagrand's N-site cascade

The derivative of a normalized tilted average is the tilted average of the
observable's derivative plus a covariance term.  This is the second-order
chain rule needed for the disorder integration by parts in Theorem 2.1.
-/
public import Targets.CascadeDerivPi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {n : ℕ}

/-- A bounded observable times the exponential cascade kernel is integrable. -/
theorem integrable_bounded_mul_exp_shift_pi {A G : (Fin n → ℝ) → ℝ}
    {m v C D B : ℝ} (hD : 0 ≤ D) (hA : ∀ y, |A y| ≤ C + D * l1 y)
    (hAm : Measurable A) (hGm : Measurable G) (hG : ∀ y, |G y| ≤ B)
    (x : Fin n → ℝ) :
    Integrable (fun z => G (fun i => x i + Real.sqrt v * z i) *
      Real.exp (m * A (fun i => x i + Real.sqrt v * z i))) (piGauss n) := by
  refine ((integrable_exp_shift_pi (m := m) (v := v) hD hA hAm x).const_mul B).mono' ?_ ?_
  · exact ((hGm.comp (measurable_shift v x)).mul
      (Real.measurable_exp.comp ((hAm.comp (measurable_shift v x)).const_mul m))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hG _) (Real.exp_pos _).le

/-- Differentiate the unnormalized numerator of a tilted average.  The observable
and both first derivatives are bounded uniformly on a neighborhood. -/
theorem hasDerivAt_integral_mul_exp_param_pi
    {A A' G G' : ℝ → (Fin n → ℝ) → ℝ} {m v C D BA BG BG' : ℝ}
    (x : Fin n → ℝ) {r : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 r) (hD : 0 ≤ D)
    (hAd : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hGd : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => G u' y) (G' u y) u)
    (hAm : ∀ u ∈ s, Measurable (A u)) (hA'm : ∀ u ∈ s, Measurable (A' u))
    (hGm : ∀ u ∈ s, Measurable (G u)) (hG'm : ∀ u ∈ s, Measurable (G' u))
    (hA : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hA' : ∀ u ∈ s, ∀ y, |A' u y| ≤ BA)
    (hG : ∀ u ∈ s, ∀ y, |G u y| ≤ BG)
    (hG' : ∀ u ∈ s, ∀ y, |G' u y| ≤ BG') :
    HasDerivAt (fun u => ∫ z, G u (fun i => x i + Real.sqrt v * z i) *
        Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂piGauss n)
      (∫ z, (G' r (fun i => x i + Real.sqrt v * z i) +
        m * G r (fun i => x i + Real.sqrt v * z i) *
          A' r (fun i => x i + Real.sqrt v * z i)) *
        Real.exp (m * A r (fun i => x i + Real.sqrt v * z i)) ∂piGauss n) r := by
  have hr : r ∈ s := mem_of_mem_nhds hs
  have hBA : 0 ≤ BA := (abs_nonneg _).trans (hA' r hr 0)
  have hBG : 0 ≤ BG := (abs_nonneg _).trans (hG r hr 0)
  have hBG' : 0 ≤ BG' := (abs_nonneg _).trans (hG' r hr 0)
  let K := Real.exp (|m| * (C + D * l1 x))
  let c := |m| * D * Real.sqrt v
  have hexp : ∀ u ∈ s, ∀ z,
      Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ≤
        K * Real.exp (c * l1 z) := by
    intro u hu z
    dsimp [K, c]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := (hA u hu _).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (l1_shift_le v x z) hD) C)
    have habs : m * A u (fun i => x i + Real.sqrt v * z i) ≤
        |m| * |A u (fun i => x i + Real.sqrt v * z i)| := by
      rw [← abs_mul]; exact le_abs_self _
    calc
      m * A u (fun i => x i + Real.sqrt v * z i) ≤
          |m| * |A u (fun i => x i + Real.sqrt v * z i)| := habs
      _ ≤ |m| * (C + D * (l1 x + Real.sqrt v * l1 z)) :=
        mul_le_mul_of_nonneg_left ha (abs_nonneg m)
      _ = _ := by ring
  have hprod : ∀ u ∈ s, ∀ y, |G' u y + m * G u y * A' u y| ≤
      BG' + |m| * BG * BA := by
    intro u hu y
    calc
      |G' u y + m * G u y * A' u y| ≤ |G' u y| + |m * G u y * A' u y| := abs_add_le _ _
      _ ≤ BG' + |m| * BG * BA := by
        rw [abs_mul, abs_mul]
        exact add_le_add (hG' u hu y)
          (mul_le_mul (mul_le_mul_of_nonneg_left (hG u hu y) (abs_nonneg m))
            (hA' u hu y) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBG))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => G u (fun i => x i + Real.sqrt v * z i) *
      Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
    (F' := fun u z => (G' u (fun i => x i + Real.sqrt v * z i) +
      m * G u (fun i => x i + Real.sqrt v * z i) * A' u (fun i => x i + Real.sqrt v * z i)) *
      Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)))
    (bound := fun z => ((BG' + |m| * BG * BA) * K) * Real.exp (c * l1 z))
    (s := s) hs ?_ (integrable_bounded_mul_exp_shift_pi hD (hA r hr)
      (hAm r hr) (hGm r hr) (hG r hr) x) ?_ ?_
    ((integrable_exp_l1 c).const_mul _) ?_).2
  · filter_upwards [hs] with u hu
    exact (((hGm u hu).comp (measurable_shift v x)).mul
      (Real.measurable_exp.comp (((hAm u hu).comp (measurable_shift v x)).const_mul m))).aestronglyMeasurable
  · exact ((((hG'm r hr).add (((hGm r hr).const_mul m).mul (hA'm r hr))).comp
      (measurable_shift v x)).mul (Real.measurable_exp.comp
        (((hAm r hr).comp (measurable_shift v x)).const_mul m))).aestronglyMeasurable
  · filter_upwards with z u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (BG' + |m| * BG * BA) * (K * Real.exp (c * l1 z)) :=
        mul_le_mul (hprod u hu _) (hexp u hu z) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  · filter_upwards with z u hu
    exact ((hGd u hu _).mul (((hAd u hu _).const_mul m).exp)).congr_deriv (by ring)

/-- The tilted-average chain rule, including the zero-mass branch:
`d ⟨G⟩ = ⟨G' + m G A'⟩ - m ⟨G⟩ ⟨A'⟩`.
It is the mixed second derivative rule when `G` is a first derivative of `A`. -/
theorem hasDerivAt_tiltAvg_param_pi
    {A A' G G' : ℝ → (Fin n → ℝ) → ℝ} {m v C D BA BG BG' : ℝ}
    (x : Fin n → ℝ) {r : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 r) (hD : 0 ≤ D)
    (hAd : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => A u' y) (A' u y) u)
    (hGd : ∀ u ∈ s, ∀ y, HasDerivAt (fun u' => G u' y) (G' u y) u)
    (hAm : ∀ u ∈ s, Measurable (A u)) (hA'm : ∀ u ∈ s, Measurable (A' u))
    (hGm : ∀ u ∈ s, Measurable (G u)) (hG'm : ∀ u ∈ s, Measurable (G' u))
    (hA : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hA' : ∀ u ∈ s, ∀ y, |A' u y| ≤ BA)
    (hG : ∀ u ∈ s, ∀ y, |G u y| ≤ BG)
    (hG' : ∀ u ∈ s, ∀ y, |G' u y| ≤ BG') :
    HasDerivAt (fun u => ∫ z, G u (fun i => x i + Real.sqrt v * z i) *
        tiltWeightPi n m v (A u) x z ∂piGauss n)
      ((∫ z, (G' r (fun i => x i + Real.sqrt v * z i) +
          m * G r (fun i => x i + Real.sqrt v * z i) *
            A' r (fun i => x i + Real.sqrt v * z i)) *
          tiltWeightPi n m v (A r) x z ∂piGauss n) -
        m * (∫ z, G r (fun i => x i + Real.sqrt v * z i) *
          tiltWeightPi n m v (A r) x z ∂piGauss n) *
        (∫ z, A' r (fun i => x i + Real.sqrt v * z i) *
          tiltWeightPi n m v (A r) x z ∂piGauss n)) r := by
  have hr : r ∈ s := mem_of_mem_nhds hs
  by_cases hm : m = 0
  · simp only [hm, tiltWeightPi, ↓reduceIte, mul_one, zero_mul, add_zero, sub_zero]
    exact hasDerivAt_integral_param_pi (A := G) (A' := G') (v := v) (C := BG) (D := 0)
      (C' := BG') (D' := 0) x hs le_rfl le_rfl hGd hGm hG'm
      (by simpa using hG) (by simpa using hG')
  · have hden := hasDerivAt_integral_exp_param_pi (A := A) (A' := A')
      (m := m) (v := v) (C := C) (D := D) (C' := BA) (D' := 0)
      x hs hD le_rfl hAd hAm hA'm hA (by simpa using hA')
    have hnum := hasDerivAt_integral_mul_exp_param_pi (m := m) (v := v) x hs hD
      hAd hGd hAm hA'm hGm hG'm hA hA' hG hG'
    have hpos := integral_exp_shift_pi_pos (m := m) (v := v) hD (hA r hr) (hAm r hr) x
    simp only [tiltWeightPi, if_neg hm, ← mul_div_assoc, integral_div]
    refine (hnum.div hden hpos.ne').congr_deriv ?_
    rw [integral_const_mul]
    field_simp

end SpinGlass.Targets
