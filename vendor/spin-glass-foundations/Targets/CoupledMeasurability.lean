module

/- Joint measurability in the disorder and the two replica fields. -/
public import Targets.ConstrainedCascade

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {n : ℕ}

abbrev Input (n : ℕ) := EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ))

private noncomputable def independentShift (v : ℝ)
    (p : Input n × ((Fin n → ℝ) × (Fin n → ℝ))) : Input n :=
  (p.1.1, (fun i => p.1.2.1 i + Real.sqrt v * p.2.1 i,
    fun i => p.1.2.2 i + Real.sqrt v * p.2.2 i))

private noncomputable def sharedShift (v : ℝ) (p : Input n × (Fin n → ℝ)) : Input n :=
  (p.1.1, (fun i => p.1.2.1 i + Real.sqrt v * p.2 i,
    fun i => p.1.2.2 i + Real.sqrt v * p.2 i))

private theorem measurable_independentShift (v : ℝ) : Measurable (independentShift (n := n) v) := by
  unfold independentShift
  fun_prop

private theorem measurable_sharedShift (v : ℝ) : Measurable (sharedShift (n := n) v) := by
  unfold sharedShift
  fun_prop

theorem measurable_independentStepPi_joint (m v : ℝ)
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : Input n => A p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Input n => independentStepPi n m v (A p.1) p.2.1 p.2.2) := by
  have H := hA.comp (measurable_independentShift v)
  unfold independentStepPi
  split_ifs
  · exact H.stronglyMeasurable.integral_prod_right'.measurable
  · exact ((H.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable.log).const_mul _

theorem measurable_sharedStepPi_joint (m v : ℝ)
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : Input n => A p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Input n => sharedStepPi n m v (A p.1) p.2.1 p.2.2) := by
  have H := hA.comp (measurable_sharedShift v)
  unfold sharedStepPi parisiStepPi
  simp only [Pi.zero_apply, zero_add, Pi.add_def]
  split_ifs
  · exact H.stronglyMeasurable.integral_prod_right'.measurable
  · exact ((H.const_mul (m / 2)).exp.stronglyMeasurable.integral_prod_right'.measurable.log).const_mul _

theorem measurable_coupledCascade_joint {k : ℕ} (s : RSBScheme k) (β : ℝ) (d j : ℕ)
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : Input n => A p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Input n => coupledCascade n s β d (A p.1) j p.2.1 p.2.2) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    simp only [coupledCascade]
    split_ifs
    · exact measurable_independentStepPi_joint _ _ (A := fun U => coupledCascade n s β d (A U) j) ih
    · exact measurable_sharedStepPi_joint _ _ (A := fun U => coupledCascade n s β d (A U) j) ih

theorem measurable_independentTiltAvg_joint (m v : ℝ)
    {A F : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : Input n => A p.1 p.2.1 p.2.2))
    (hF : Measurable (fun p : Input n => F p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Input n => independentTiltAvg n m v (A p.1) (F p.1) p.2.1 p.2.2) := by
  have hmA := hA.comp (measurable_independentShift v)
  have hmF := hF.comp (measurable_independentShift v)
  unfold independentTiltAvg independentTiltWeightPi
  split_ifs
  · simp only [mul_one]
    exact hmF.stronglyMeasurable.integral_prod_right'.measurable
  · simp_rw [← mul_div_assoc, integral_div]
    exact ((hmF.mul (hmA.const_mul m).exp).stronglyMeasurable.integral_prod_right'.measurable).div
      ((hmA.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable)

theorem measurable_sharedTiltAvg_joint (m v : ℝ)
    {A F : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : Input n => A p.1 p.2.1 p.2.2))
    (hF : Measurable (fun p : Input n => F p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Input n => sharedTiltAvg n m v (A p.1) (F p.1) p.2.1 p.2.2) := by
  have hmA := hA.comp (measurable_sharedShift v)
  have hmF := hF.comp (measurable_sharedShift v)
  unfold sharedTiltAvg sharedTiltWeightPi tiltWeightPi
  simp only [Pi.zero_apply, zero_add, Pi.add_def]
  split_ifs
  · simp only [mul_one]
    exact hmF.stronglyMeasurable.integral_prod_right'.measurable
  · simp_rw [← mul_div_assoc, integral_div]
    exact ((hmF.mul (hmA.const_mul (m / 2)).exp).stronglyMeasurable.integral_prod_right'.measurable).div
      ((hmA.const_mul (m / 2)).exp.stronglyMeasurable.integral_prod_right'.measurable)

theorem measurable_coupledBase_joint (h t : ℝ) :
    Measurable (fun p : Input n => coupledBase n p.1 h t p.2.1 p.2.2) := by
  unfold coupledBase guerraH
  fun_prop

theorem measurable_constrainedBase_joint (h t u : ℝ) :
    Measurable (fun p : Input n => constrainedBase n p.1 h t u p.2.1 p.2.2) := by
  unfold constrainedBase constrainedZ guerraH
  apply Measurable.log
  apply Finset.measurable_sum
  intro σ _
  apply Finset.measurable_sum
  intro τ _
  by_cases hu : overlap n σ τ = u
  · simp only [if_pos hu]
    fun_prop
  · simp only [if_neg hu]
    exact measurable_const

/-- Every weighted observable is measurable jointly with its disorder. -/
theorem measurable_coupledObservable_joint {k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (d : ℕ) (K : Config n → Config n → ℝ) (j : ℕ) :
    Measurable (fun p : Input n => coupledObservable n s β p.1 h t d K j p.2.1 p.2.2) := by
  induction j with
  | zero =>
    unfold coupledObservable coupledGibbsAvg guerraH
    fun_prop
  | succ j ih =>
    have hA := measurable_coupledCascade_joint s β d j (A := fun U => coupledBase n U h t)
      (measurable_coupledBase_joint h t)
    simp only [coupledObservable]
    split_ifs
    · exact measurable_independentTiltAvg_joint _ _
        (A := fun U => coupledCascade n s β d (coupledBase n U h t) j)
        (F := fun U => coupledObservable n s β U h t d K j) hA ih
    · exact measurable_sharedTiltAvg_joint _ _
        (A := fun U => coupledCascade n s β d (coupledBase n U h t) j)
        (F := fun U => coupledObservable n s β U h t d K j) hA ih

end SpinGlass.Targets
