module

/-
# The one-step comparison in Talagrand's Lemma 2.6

An event probability bounded by `exp (p * (B - A))` remains bounded by the
corresponding pressure difference after a log-Laplace step of mass `m ≤ p`.
The assumptions `B ≤ A` and `m > 0` are essential. Integrability of the tilted
observable is proved by domination, not assumed or bypassed by totalized integrals.
-/
public import Targets.CoupledGrowth

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

theorem tilted_event_exp_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {A B F : Z → ℝ} {m p : ℝ} (hm : 0 < m) (hmp : m ≤ p)
    (hA : Integrable (fun z => Real.exp (m * A z)) μ)
    (hB : Integrable (fun z => Real.exp (m * B z)) μ) (hF : Measurable F)
    (hBA : ∀ z, B z ≤ A z) (hF0 : ∀ z, 0 ≤ F z)
    (hbound : ∀ z, F z ≤ Real.exp (p * (B z - A z))) :
    (∫ z, F z * (Real.exp (m * A z) / ∫ w, Real.exp (m * A w) ∂μ) ∂μ) ≤
      Real.exp (m * ((1 / m) * Real.log (∫ z, Real.exp (m * B z) ∂μ) -
        (1 / m) * Real.log (∫ z, Real.exp (m * A z) ∂μ))) := by
  let I := ∫ z, Real.exp (m * A z) ∂μ
  let J := ∫ z, Real.exp (m * B z) ∂μ
  have hI : 0 < I := integral_exp_pos hA
  have hJ : 0 < J := integral_exp_pos hB
  have hpt : ∀ z, F z * (Real.exp (m * A z) / I) ≤ Real.exp (m * B z) / I := by
    intro z
    have hh : F z ≤ Real.exp (m * (B z - A z)) := (hbound z).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hmp (sub_nonpos.mpr (hBA z))))
    calc
      _ ≤ Real.exp (m * (B z - A z)) * (Real.exp (m * A z) / I) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = Real.exp (m * B z) / I := by
        rw [← mul_div_assoc, ← Real.exp_add]
        congr 2
        ring
  have hnonneg : ∀ z, 0 ≤ F z * (Real.exp (m * A z) / I) := fun z =>
    mul_nonneg (hF0 z) (by positivity)
  have hInt : Integrable (fun z => F z * (Real.exp (m * A z) / I)) μ := by
    apply (hB.div_const I).mono
      (hF.aestronglyMeasurable.mul (hA.div_const I).aestronglyMeasurable)
    filter_upwards with z
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (hnonneg z),
      abs_of_pos (div_pos (Real.exp_pos _) hI)] using hpt z
  have hi := integral_mono hInt (hB.div_const I) hpt
  rw [integral_div] at hi
  have he : m * ((1 / m) * Real.log J - (1 / m) * Real.log I) = Real.log J - Real.log I := by
    field_simp
  change _ ≤ Real.exp (m * ((1 / m) * Real.log J - (1 / m) * Real.log I))
  rw [he, Real.exp_sub, Real.exp_log hJ, Real.exp_log hI]
  exact hi

theorem independentTiltAvg_le_exp_gap {n : ℕ} {m p v : ℝ} (hm : 0 < m) (hmp : m ≤ p)
    {A B F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hBA : ∀ x y, B x y ≤ A x y) (hF0 : ∀ x y, 0 ≤ F x y)
    (hbound : ∀ x y, F x y ≤ Real.exp (p * (B x y - A x y))) (x y : Fin n → ℝ) :
    independentTiltAvg n m v A F x y ≤
      Real.exp (m * (independentStepPi n m v B x y - independentStepPi n m v A x y)) := by
  have hFm := hF.comp (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ((fun i => x i + Real.sqrt v * z.1 i), (fun i => y i + Real.sqrt v * z.2 i))) (by fun_prop)
  simpa only [independentTiltAvg, independentTiltWeightPi, independentStepPi, if_neg hm.ne',
    Function.comp_def] using
    tilted_event_exp_bound ((piGauss n).prod (piGauss n)) hm hmp
      (hA.integrable_exp_shift m v x y) (hB.integrable_exp_shift m v x y) hFm
      (fun _ => hBA _ _) (fun _ => hF0 _ _) (fun _ => hbound _ _)

theorem sharedTiltAvg_le_exp_gap {n : ℕ} {m p v : ℝ} (hm : 0 < m / 2) (hmp : m / 2 ≤ p)
    {A B F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hBA : ∀ x y, B x y ≤ A x y) (hF0 : ∀ x y, 0 ≤ F x y)
    (hbound : ∀ x y, F x y ≤ Real.exp (p * (B x y - A x y))) (x y : Fin n → ℝ) :
    sharedTiltAvg n m v A F x y ≤
      Real.exp ((m / 2) * (sharedStepPi n m v B x y - sharedStepPi n m v A x y)) := by
  obtain ⟨C, D, hD, hb⟩ := (hA.shared_shift x y).bound
  obtain ⟨C', D', hD', hb'⟩ := (hB.shared_shift x y).bound
  have hiA := integrable_exp_shift_pi (m := m / 2) (v := v) hD hb (hA.shared_shift x y).measurable 0
  have hiB := integrable_exp_shift_pi (m := m / 2) (v := v) hD' hb' (hB.shared_shift x y).measurable 0
  simp only [Pi.zero_apply, zero_add, Pi.add_def] at hiA hiB
  have hFm := hF.comp (f := fun z : Fin n → ℝ =>
    ((fun i => x i + Real.sqrt v * z i), (fun i => y i + Real.sqrt v * z i))) (by fun_prop)
  simpa only [sharedTiltAvg, sharedTiltWeightPi, sharedStepPi, tiltWeightPi, parisiStepPi,
    if_neg hm.ne', Pi.zero_apply, zero_add, Pi.add_def, Function.comp_def] using
    tilted_event_exp_bound (piGauss n) hm hmp hiA hiB hFm
      (fun _ => hBA _ _) (fun _ => hF0 _ _) (fun _ => hbound _ _)

theorem measurable_independentTiltAvg {n : ℕ} (m v : ℝ)
    {A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => A z.1 z.2))
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2)) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => independentTiltAvg n m v A F z.1 z.2) := by
  let S := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
    ((fun i => p.1.1 i + Real.sqrt v * p.2.1 i), (fun i => p.1.2 i + Real.sqrt v * p.2.2 i))
  have hmS : Measurable S := by dsimp [S]; fun_prop
  have hmA := hA.comp hmS
  have hmF := hF.comp hmS
  unfold independentTiltAvg independentTiltWeightPi
  by_cases hm : m = 0
  · simp only [if_pos hm, mul_one]
    exact hmF.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [if_neg hm]
    simp_rw [← mul_div_assoc, integral_div]
    exact ((hmF.mul (hmA.const_mul m).exp).stronglyMeasurable.integral_prod_right'.measurable).div
      ((hmA.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable)

theorem measurable_sharedTiltAvg {n : ℕ} (m v : ℝ)
    {A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => A z.1 z.2))
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2)) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => sharedTiltAvg n m v A F z.1 z.2) := by
  let S := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
    ((fun i => p.1.1 i + Real.sqrt v * p.2 i), (fun i => p.1.2 i + Real.sqrt v * p.2 i))
  have hmS : Measurable S := by dsimp [S]; fun_prop
  have hmA := hA.comp hmS
  have hmF := hF.comp hmS
  unfold sharedTiltAvg sharedTiltWeightPi tiltWeightPi
  simp only [Pi.zero_apply, zero_add, Pi.add_def]
  by_cases hm : m / 2 = 0
  · simp only [if_pos hm, mul_one]
    exact hmF.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [if_neg hm]
    simp_rw [← mul_div_assoc, integral_div]
    exact ((hmF.mul (hmA.const_mul (m / 2)).exp).stronglyMeasurable.integral_prod_right'.measurable).div
      ((hmA.const_mul (m / 2)).exp.stronglyMeasurable.integral_prod_right'.measurable)

theorem independentTiltAvg_nonneg {n : ℕ} (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : ∀ x y, 0 ≤ F x y) (x y : Fin n → ℝ) : 0 ≤ independentTiltAvg n m v A F x y := by
  apply integral_nonneg
  intro z
  apply mul_nonneg (hF _ _)
  unfold independentTiltWeightPi
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem sharedTiltAvg_nonneg {n : ℕ} (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : ∀ x y, 0 ≤ F x y) (x y : Fin n → ℝ) : 0 ≤ sharedTiltAvg n m v A F x y := by
  apply integral_nonneg
  intro z
  apply mul_nonneg (hF _ _)
  unfold sharedTiltWeightPi tiltWeightPi
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))

/-- Positive bounded observables have a positive integral under a positive integrable density. -/
theorem integral_mul_pos_of_bounded {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {F G : Z → ℝ} (hF : Measurable F) (hG : Integrable G μ)
    (hF0 : ∀ z, 0 < F z) (hF1 : ∀ z, F z ≤ 1) (hG0 : ∀ z, 0 < G z) :
    0 < ∫ z, F z * G z ∂μ := by
  have hp : ∀ z, 0 < F z * G z := fun z => mul_pos (hF0 z) (hG0 z)
  have hi : Integrable (fun z => F z * G z) μ := by
    apply hG.mono (hF.aestronglyMeasurable.mul hG.aestronglyMeasurable)
    filter_upwards with z
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_of_pos (hp z), abs_of_pos (hG0 z)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hF1 z) (hG0 z).le
  rw [integral_pos_iff_support_of_nonneg (fun z => (hp z).le) hi]
  have hs : Function.support (fun z => F z * G z) = Set.univ := by
    ext z
    simp only [Function.mem_support, ne_eq, (hp z).ne', not_false_eq_true, Set.mem_univ]
  simp [hs]

theorem independentTiltAvg_pos {n : ℕ} (m v : ℝ)
    {A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hF0 : ∀ x y, 0 < F x y) (hF1 : ∀ x y, F x y ≤ 1) (x y : Fin n → ℝ) :
    0 < independentTiltAvg n m v A F x y := by
  have hFm := hF.comp (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ((fun i => x i + Real.sqrt v * z.1 i), (fun i => y i + Real.sqrt v * z.2 i))) (by fun_prop)
  unfold independentTiltAvg independentTiltWeightPi
  by_cases hm : m = 0
  · simp only [if_pos hm]
    exact integral_mul_pos_of_bounded _ hFm (integrable_const 1)
      (fun _ => hF0 _ _) (fun _ => hF1 _ _) (fun _ => zero_lt_one)
  · simp only [if_neg hm]
    exact integral_mul_pos_of_bounded _ hFm ((hA.integrable_exp_shift m v x y).div_const _)
      (fun _ => hF0 _ _) (fun _ => hF1 _ _)
      (fun _ => div_pos (Real.exp_pos _) (hA.integral_exp_shift_pos m v x y))

theorem sharedTiltAvg_pos {n : ℕ} (m v : ℝ)
    {A F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (hF : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hF0 : ∀ x y, 0 < F x y) (hF1 : ∀ x y, F x y ≤ 1) (x y : Fin n → ℝ) :
    0 < sharedTiltAvg n m v A F x y := by
  have hFm := hF.comp (f := fun z : Fin n → ℝ =>
    ((fun i => x i + Real.sqrt v * z i), (fun i => y i + Real.sqrt v * z i))) (by fun_prop)
  obtain ⟨C, D, hD, hb⟩ := (hA.shared_shift x y).bound
  have hi := integrable_exp_shift_pi (m := m / 2) (v := v) hD hb (hA.shared_shift x y).measurable 0
  have hp := integral_exp_shift_pi_pos (m := m / 2) (v := v) hD hb (hA.shared_shift x y).measurable 0
  simp only [Pi.zero_apply, zero_add, Pi.add_def] at hi hp
  unfold sharedTiltAvg sharedTiltWeightPi tiltWeightPi
  simp only [Pi.zero_apply, zero_add, Pi.add_def]
  by_cases hm : m / 2 = 0
  · simp only [if_pos hm]
    exact integral_mul_pos_of_bounded _ hFm (integrable_const 1)
      (fun _ => hF0 _ _) (fun _ => hF1 _ _) (fun _ => zero_lt_one)
  · simp only [if_neg hm]
    exact integral_mul_pos_of_bounded _ hFm (hi.div_const _)
      (fun _ => hF0 _ _) (fun _ => hF1 _ _) (fun _ => div_pos (Real.exp_pos _) hp)

end SpinGlass.Targets
