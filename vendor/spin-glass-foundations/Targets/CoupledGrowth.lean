module

/-
# Analytic bounds for constrained coupled cascades

Unlike the unrestricted cascade, an overlap-constrained partition function does
not factor between replicas. These lemmas justify its Gaussian integrals and
propagate affine field growth without assuming factorisation.
-/
public import Targets.CoupledCascade

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- Joint measurability and affine growth in both replica fields. -/
structure CoupledGrowth {n : ℕ} (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop where
  measurable : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 p.2)
  bound : ∃ C D : ℝ, 0 ≤ D ∧ ∀ x y, |A x y| ≤ C + D * (l1 x + l1 y)

theorem CoupledGrowth.section_right {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (x : Fin n → ℝ) : GuerraGrowth (A x) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨hA.measurable.comp (measurable_const.prodMk measurable_id),
    C + D * l1 x, D, hD, fun y => ?_⟩
  nlinarith [hb x y]

theorem CoupledGrowth.shared_shift {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    GuerraGrowth (fun z => A (x + z) (y + z)) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨hA.measurable.comp (f := fun z => (x + z, y + z)) (by fun_prop),
    C + D * (l1 x + l1 y), 2 * D, by positivity, fun z => ?_⟩
  have hx := l1_add_le x z
  have hy := l1_add_le y z
  nlinarith [hb (x + z) (y + z)]

theorem CoupledGrowth.integrable_shift {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (v : ℝ) (x y : Fin n → ℝ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      A (fun i => x i + Real.sqrt v * z.1 i) (fun i => y i + Real.sqrt v * z.2 i))
      ((piGauss n).prod (piGauss n)) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  let B : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun z =>
    C + D * (l1 x + l1 y) + (D * Real.sqrt v) * (l1 z.1 + l1 z.2)
  have hi : Integrable B ((piGauss n).prod (piGauss n)) :=
    (integrable_const _).add (((integrable_l1.comp_fst (piGauss n)).add
      (integrable_l1.comp_snd (piGauss n))).const_mul _)
  refine hi.mono ((hA.measurable.comp (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ((fun i => x i + Real.sqrt v * z.1 i), (fun i => y i + Real.sqrt v * z.2 i)))
    (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine (hb _ _).trans ((show C + D * (l1 (fun i => x i + Real.sqrt v * z.1 i) +
      l1 (fun i => y i + Real.sqrt v * z.2 i)) ≤ B z from ?_).trans (le_abs_self _))
  dsimp [B]
  nlinarith [l1_shift_le v x z.1, l1_shift_le v y z.2]

theorem CoupledGrowth.integrable_exp_shift {n : ℕ}
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (m v : ℝ)
    (x y : Fin n → ℝ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Real.exp
      (m * A (fun i => x i + Real.sqrt v * z.1 i) (fun i => y i + Real.sqrt v * z.2 i)))
      ((piGauss n).prod (piGauss n)) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  let c := |m| * D * Real.sqrt v
  have hi := ((integrable_exp_l1 (n := n) c).mul_prod (integrable_exp_l1 (n := n) c)).const_mul
    (Real.exp (|m| * (C + D * (l1 x + l1 y))))
  refine hi.mono (((hA.measurable.comp (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    ((fun i => x i + Real.sqrt v * z.1 i), (fun i => y i + Real.sqrt v * z.2 i)))
    (by fun_prop)).const_mul m).exp.aestronglyMeasurable) ?_
  filter_upwards with z
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hshift : |A (fun i => x i + Real.sqrt v * z.1 i)
      (fun i => y i + Real.sqrt v * z.2 i)| ≤
      C + D * (l1 x + l1 y) + D * Real.sqrt v * (l1 z.1 + l1 z.2) := by
    nlinarith [hb (fun i => x i + Real.sqrt v * z.1 i) (fun i => y i + Real.sqrt v * z.2 i),
      l1_shift_le v x z.1, l1_shift_le v y z.2]
  have ha := le_abs_self (m * A (fun i => x i + Real.sqrt v * z.1 i)
    (fun i => y i + Real.sqrt v * z.2 i))
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hshift (abs_nonneg m)
  dsimp [c]
  nlinarith

theorem CoupledGrowth.integral_exp_shift_pos {n : ℕ}
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (m v : ℝ)
    (x y : Fin n → ℝ) :
    0 < ∫ z : (Fin n → ℝ) × (Fin n → ℝ), Real.exp
      (m * A (fun i => x i + Real.sqrt v * z.1 i) (fun i => y i + Real.sqrt v * z.2 i))
      ∂(piGauss n).prod (piGauss n) :=
  integral_exp_pos (hA.integrable_exp_shift m v x y)

/-- Joint measurability of smoothing in the second field only. -/
theorem measurable_secondStepPi {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 p.2)) (m v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => parisiStepPi n m v (A p.1) p.2) := by
  have hj : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      A p.1.1 (fun i => p.1.2 i + Real.sqrt v * p.2 i)) :=
    hA.comp (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (p.1.1, fun i => p.1.2 i + Real.sqrt v * p.2 i)) (by fun_prop)
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]
    exact hj.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [parisiStepPi, if_neg hm]
    exact (((hj.const_mul m).exp.stronglyMeasurable.integral_prod_right').measurable.log).const_mul _

/-- Fubini for a genuine interacting two-field log-Laplace step. -/
theorem independentStepPi_eq_nested {n : ℕ} (m v : ℝ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    independentStepPi n m v A x y =
      parisiStepPi n m v (fun w => parisiStepPi n m v (A w) y) x := by
  by_cases hm : m = 0
  · simp only [independentStepPi, parisiStepPi, if_pos hm]
    exact integral_prod _ (hA.integrable_shift v x y)
  · simp only [independentStepPi, parisiStepPi, if_neg hm]
    have he : ∀ w : Fin n → ℝ,
        Real.exp (m * ((1 / m) * Real.log (∫ z, Real.exp
          (m * A w (fun i => y i + Real.sqrt v * z i)) ∂piGauss n))) =
        ∫ z, Real.exp (m * A w (fun i => y i + Real.sqrt v * z i)) ∂piGauss n := by
      intro w
      obtain ⟨C, D, hD, hb⟩ := (hA.section_right w).bound
      rw [show ∀ a : ℝ, m * ((1 / m) * a) = a by intro a; field_simp]
      exact Real.exp_log (integral_exp_shift_pi_pos hD hb (hA.section_right w).measurable y)
    simp_rw [he]
    rw [integral_prod _ (hA.integrable_exp_shift m v x y)]

theorem CoupledGrowth.independentStep {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledGrowth (independentStepPi n m v A) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  have hmB := measurable_secondStepPi hA.measurable m v
  have hi : ∀ x y, |parisiStepPi n m v (A x) y| ≤
      (C + D * l1 x + stepK n m v D) + D * l1 y := by
    intro x y
    exact parisiStepPi_abs_le (C := C + D * l1 x) hm hv hD (fun z => by nlinarith [hb x z])
      (hA.section_right x).measurable y
  have hmC : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      parisiStepPi n m v (fun w => parisiStepPi n m v (A w) p.2) p.1) := by
    have H := measurable_secondStepPi (A := fun y x => parisiStepPi n m v (A x) y)
      (hmB.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.2, p.1)) measurable_swap) m v
    exact H.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.2, p.1)) measurable_swap
  refine ⟨?_, C + 2 * stepK n m v D, D, hD, fun x y => ?_⟩
  · simpa only [independentStepPi_eq_nested m v hA] using hmC
  · rw [independentStepPi_eq_nested m v hA]
    have hmF : Measurable (fun w => parisiStepPi n m v (A w) y) :=
      hmB.comp (f := fun w : Fin n → ℝ => (w, y)) (measurable_id.prodMk measurable_const)
    have H := parisiStepPi_abs_le hm hv hD (A := fun w => parisiStepPi n m v (A w) y)
      (C := C + stepK n m v D + D * l1 y) (fun w => by nlinarith [hi w y]) hmF x
    nlinarith

theorem CoupledGrowth.sharedStep {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledGrowth (sharedStepPi n m v A) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  have hj : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      A (fun i => p.1.1 i + Real.sqrt v * p.2 i)
        (fun i => p.1.2 i + Real.sqrt v * p.2 i)) :=
    hA.measurable.comp (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      ((fun i => p.1.1 i + Real.sqrt v * p.2 i),
       (fun i => p.1.2 i + Real.sqrt v * p.2 i))) (by fun_prop)
  refine ⟨?_, C + stepK n (m / 2) v (2 * D), D, hD, fun x y => ?_⟩
  · unfold sharedStepPi parisiStepPi
    simp only [Pi.zero_apply, zero_add, Pi.add_def]
    split_ifs
    · exact hj.stronglyMeasurable.integral_prod_right'.measurable
    · exact (((hj.const_mul (m / 2)).exp.stronglyMeasurable.integral_prod_right').measurable.log).const_mul _
  · have hshift : ∀ z, |A (x + z) (y + z)| ≤
        (C + D * (l1 x + l1 y)) + (2 * D) * l1 z := by
      intro z
      nlinarith [hb (x + z) (y + z), l1_add_le x z, l1_add_le y z]
    have H := parisiStepPi_abs_le (m := m / 2) (div_nonneg hm (by norm_num)) hv
      (show 0 ≤ 2 * D by positivity) hshift (hA.shared_shift x y).measurable 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at H
    change |parisiStepPi n (m / 2) v (fun z => A (x + z) (y + z)) 0| ≤ _
    simpa only [l1, add_assoc, add_left_comm, add_comm] using H

/-- Every level of the constrained cascade is measurable and has affine field growth. -/
theorem CoupledGrowth.cascade {n k : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (s : RSBScheme k) (β : ℝ) (d j : ℕ) :
    CoupledGrowth (coupledCascade n s β d A j) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    simp only [coupledCascade]
    split_ifs
    · exact ih.independentStep (s.m_nonneg (by omega)) (levelVar_nonneg s β j)
    · exact ih.sharedStep (s.m_nonneg (by omega)) (levelVar_nonneg s β j)

/-- Order is preserved even when the two-replica function does not factor. -/
theorem independentStepPi_mono {n : ℕ} {m v : ℝ} (hm : 0 ≤ m)
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, A x y ≤ B x y) (x y : Fin n → ℝ) :
    independentStepPi n m v A x y ≤ independentStepPi n m v B x y := by
  by_cases hm0 : m = 0
  · simp only [independentStepPi, if_pos hm0]
    exact integral_mono (hA.integrable_shift v x y) (hB.integrable_shift v x y) (fun _ => hAB _ _)
  · simp only [independentStepPi, if_neg hm0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (hA.integral_exp_shift_pos m v x y)
      (integral_mono (hA.integrable_exp_shift m v x y) (hB.integrable_exp_shift m v x y)
        (fun _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hAB _ _) hm)))

theorem parisiStepPi_mono_growth {n : ℕ} {m v : ℝ} (hm : 0 ≤ m)
    {A B : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (hB : GuerraGrowth B)
    (hAB : ∀ x, A x ≤ B x) (x : Fin n → ℝ) :
    parisiStepPi n m v A x ≤ parisiStepPi n m v B x := by
  obtain ⟨C, D, hD, hAb⟩ := hA.bound
  obtain ⟨C', D', hD', hBb⟩ := hB.bound
  by_cases hm0 : m = 0
  · simp only [parisiStepPi, if_pos hm0]
    exact integral_mono (integrable_shift_pi hD hAb hA.measurable x)
      (integrable_shift_pi hD' hBb hB.measurable x) (fun _ => hAB _)
  · simp only [parisiStepPi, if_neg hm0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (integral_exp_shift_pi_pos hD hAb hA.measurable x)
      (integral_mono (integrable_exp_shift_pi hD hAb hA.measurable x)
        (integrable_exp_shift_pi hD' hBb hB.measurable x)
        (fun _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hAB _) hm)))

theorem sharedStepPi_mono {n : ℕ} {m v : ℝ} (hm : 0 ≤ m)
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, A x y ≤ B x y) (x y : Fin n → ℝ) :
    sharedStepPi n m v A x y ≤ sharedStepPi n m v B x y :=
  parisiStepPi_mono_growth (div_nonneg hm (by norm_num))
    (hA.shared_shift x y) (hB.shared_shift x y) (fun _ => hAB _ _) 0

theorem coupledCascade_mono {n k : ℕ} (s : RSBScheme k) (β : ℝ) (d j : ℕ)
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, A x y ≤ B x y) (x y : Fin n → ℝ) :
    coupledCascade n s β d A j x y ≤ coupledCascade n s β d B j x y := by
  induction j generalizing x y with
  | zero => exact hAB x y
  | succ j ih =>
    simp only [coupledCascade]
    split_ifs
    · exact independentStepPi_mono (s.m_nonneg (by omega))
        (hA.cascade s β d j) (hB.cascade s β d j) ih x y
    · exact sharedStepPi_mono (s.m_nonneg (by omega))
        (hA.cascade s β d j) (hB.cascade s β d j) ih x y

theorem coupledBase_growth (n : ℕ) (U : EnergySpace n) (h : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : CoupledGrowth (coupledBase n U h t) := by
  have hG : GuerraGrowth (guerraBase n U h t) :=
    ⟨measurable_guerraBase n U h t,
      Real.log (Fintype.card (Config n)) + uAbs n U + Fintype.card (Config n) * (n * |h|),
      Fintype.card (Config n), by positivity, abs_guerraBase_le n U h ht.1 ht.2⟩
  obtain ⟨C, D, hD, hb⟩ := hG.bound
  refine ⟨?_, 2 * C, D, hD, fun x y => ?_⟩
  · simp only [coupledBase_eq]
    exact (hG.measurable.comp measurable_fst).add (hG.measurable.comp measurable_snd)
  · rw [coupledBase_eq]
    nlinarith [abs_add_le (guerraBase n U h t x) (guerraBase n U h t y), hb x, hb y]

end SpinGlass.Targets
