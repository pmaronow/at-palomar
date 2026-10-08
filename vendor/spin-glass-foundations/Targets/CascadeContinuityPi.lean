module

/-
# Continuity of the N-site cascade in an external parameter

Uniform affine growth gives the Gaussian domination needed at interpolation
endpoints, where the square-root derivatives need not be bounded.
-/
public import Targets.CascadeDerivPi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- A cascade smoothing step preserves parameter continuity under uniform
affine growth, including the zero-mass branch. -/
theorem continuousOn_parisiStepPi_param {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] {n : ℕ} {A : P → (Fin n → ℝ) → ℝ}
    {s : Set P} {m v C D : ℝ} (hD : 0 ≤ D)
    (hAm : ∀ u ∈ s, Measurable (A u))
    (hA : ∀ u ∈ s, ∀ y, |A u y| ≤ C + D * l1 y)
    (hcont : ∀ y, ContinuousOn (fun u => A u y) s) (x : Fin n → ℝ) :
    ContinuousOn (fun u => parisiStepPi n m v (A u) x) s := by
  have hshift : ∀ u ∈ s, ∀ z : Fin n → ℝ,
      |A u (fun i => x i + Real.sqrt v * z i)| ≤
        C + D * (l1 x + Real.sqrt v * l1 z) := by
    intro u hu z
    exact (hA u hu _).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (l1_shift_le v x z) hD) C)
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]
    apply continuousOn_of_dominated
      (bound := fun z : Fin n → ℝ => C + D * (l1 x + Real.sqrt v * l1 z))
    · intro u hu
      exact ((hAm u hu).comp (measurable_shift v x)).aestronglyMeasurable
    · intro u hu
      exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hshift u hu z)
    · exact (integrable_const C).add (((integrable_const (l1 x)).add
        (integrable_l1.const_mul (Real.sqrt v))).const_mul D)
    · exact Filter.Eventually.of_forall (fun z => hcont _)
  · have hI : ContinuousOn (fun u => ∫ z,
        Real.exp (m * A u (fun i => x i + Real.sqrt v * z i)) ∂piGauss n) s := by
      apply continuousOn_of_dominated
        (bound := fun z : Fin n → ℝ => Real.exp (|m| * (C + D * l1 x)) *
          Real.exp ((|m| * D * Real.sqrt v) * l1 z))
      · intro u hu
        exact (Real.measurable_exp.comp (((hAm u hu).comp
          (measurable_shift v x)).const_mul m)).aestronglyMeasurable
      · intro u hu
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have ha : m * A u (fun i => x i + Real.sqrt v * z i) ≤
            |m| * |A u (fun i => x i + Real.sqrt v * z i)| := by
          rw [← abs_mul]; exact le_abs_self _
        have hb := mul_le_mul_of_nonneg_left (hshift u hu z) (abs_nonneg m)
        nlinarith
      · exact (integrable_exp_l1 (|m| * D * Real.sqrt v)).const_mul _
      · exact Filter.Eventually.of_forall (fun z =>
          Real.continuous_exp.comp_continuousOn ((hcont _).const_mul m))
    simp only [parisiStepPi, if_neg hm]
    refine (hI.log ?_).const_mul (1 / m)
    intro u hu
    exact (integral_exp_shift_pi_pos hD (hA u hu) (hAm u hu) x).ne'

end SpinGlass.Targets
