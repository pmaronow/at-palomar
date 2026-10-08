module

public import Lemmas.GuerraTalagrand.Flatness.Core

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SpinGlass.AT

/-! ### Endpoint `|v| = 1` -/

/-- The multiplier derivative at either endpoint of the overlap interval. -/
lemma flatness_deriv_gtFunctional_zero_abs_v_eq_one
    (β h q s v : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    deriv (fun l => gtFunctional β h q s l v) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₀ =>
        gtHalfStepEndpoint (gtIncrementScale β s q 1)
          (gtIncrementScale β s 1 1) (gtPathSign v)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₀)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtPathSign v * gtIncrementScale β s 0 q * z₀))) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun y : ℝ => y - v)
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_abs_v_eq_one β q s v _ _ hq hq1 hv

end SpinGlass.AT
