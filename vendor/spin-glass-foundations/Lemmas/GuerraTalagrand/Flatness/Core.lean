module

/- Compatibility adaptation: apply matrix evaluation lemmas before unfolding matrix definitions. -/
-- Canonical implementation module for the shared GT-flatness theory.
public import Lemmas.AT.PsiContinuity
public import Lemmas.AT.Definitions
public import Lemmas.GuerraTalagrand.Gaussian
public import Lemmas.AT.Interpolation
public import Lemmas.AT.PropertyOfG
public import Lemmas.Price.Price
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SpinGlass.AT

/-!
## Branchwise formulas for the GT functional

These formulas mirror the four overlap regimes established in `GTGauss`.
-/

/-! ### The degenerate smart-path endpoint `s = 0` -/

/-- When `s = 0`, every covariance increment in the finite GT recursion
vanishes, so the semigroup solution is just the terminal function. -/
private lemma flatness_gtSemigroupSolution_s_zero
    (β q lam v u x₁ x₂ : ℝ) :
    gtSemigroupSolution β q 0 lam v u x₁ x₂ =
      gtTerminal lam x₁ x₂ := by
  simp [gtSemigroupSolution, gtIncrementScale,
    gtDiagonalStep, gtRankOneStep, standardGaussianExpectation]

/-- At `s = 0` and `lam = 0`, the GT functional is exactly twice the
replica-symmetric path value. -/
lemma flatness_gtFunctional_s_zero_lam_zero
    (β h q v : ℝ) :
    gtFunctional β h q 0 0 v =
      2 * rsPathValue β h q 0 := by
  rw [gtFunctional]
  simp only [sub_zero, one_mul, zero_mul]
  rw [show gtCorrection β q 0 = 0 by simp [gtCorrection]]
  simp only [sub_zero]

  simp_rw [flatness_gtSemigroupSolution_s_zero]
  simp_rw [gtTerminal_zero]

  rw [rsPathValue]
  simp only [zero_mul, zero_div, add_zero]

  have hE :
      standardGaussianExpectation (fun z =>
        Real.log (Real.cosh
          (h + β * Real.sqrt q * z)) +
        Real.log (Real.cosh
          (h + β * Real.sqrt q * z))) =
      2 * standardGaussianExpectation (fun z =>
        Real.log (Real.cosh
          (h + β * Real.sqrt q * z))) := by
    unfold standardGaussianExpectation
    rw [show
      (fun z : ℝ =>
        Real.log (Real.cosh
          (h + β * Real.sqrt q * z)) +
        Real.log (Real.cosh
          (h + β * Real.sqrt q * z))) =
      (fun z : ℝ =>
        2 * Real.log (Real.cosh
          (h + β * Real.sqrt q * z))) by
      funext z
      ring]
    rw [integral_const_mul]

  rw [hE]
  ring

/-- At `s = 0`, the multiplier derivative at `lam = 0` is `q - v`
whenever `q` satisfies the replica-symmetric fixed-point equation. -/
lemma flatness_deriv_gtFunctional_s_zero_lam_zero
    (β h q v : ℝ)
    (hfixed : IsRSFixedPoint β h q) :
    deriv (fun lam => gtFunctional β h q 0 lam v) 0 =
      q - v := by
  rw [deriv_gtFunctional_eq]
  simp only [sub_zero, one_mul]

  have hE :
      standardGaussianExpectation (fun z =>
        deriv (fun lam =>
          gtSemigroupSolution β q 0 lam v 0
            (h + β * Real.sqrt q * z)
            (h + β * Real.sqrt q * z)) 0) =
      q := by
    calc
      standardGaussianExpectation (fun z =>
        deriv (fun lam =>
          gtSemigroupSolution β q 0 lam v 0
            (h + β * Real.sqrt q * z)
            (h + β * Real.sqrt q * z)) 0)
          =
        standardGaussianExpectation (fun z =>
          Real.tanh (h + β * Real.sqrt q * z) ^ 2) := by
            apply congrArg standardGaussianExpectation
            funext z
            let x := h + β * Real.sqrt q * z
            have hfun :
                (fun lam =>
                  gtSemigroupSolution β q 0 lam v 0 x x) =
                (fun lam => gtTerminal lam x x) := by
              funext lam
              exact flatness_gtSemigroupSolution_s_zero
                β q lam v 0 x x
            rw [hfun, deriv_gtTerminal_zero]
            ring
      _ = q := by
        exact hfixed.symm

  rw [hE]

/-- The canonical-overlap specialization of
`flatness_deriv_gtFunctional_s_zero_lam_zero`. -/
lemma flatness_deriv_gtFunctional_s_zero_lam_zero_rsQ
    (β h v : ℝ) :
    deriv
      (fun lam =>
        gtFunctional β h (rsQ β h) 0 lam v) 0 =
      rsQ β h - v := by
  exact flatness_deriv_gtFunctional_s_zero_lam_zero
    β h (rsQ β h) v (rsQ_fixedPoint β h)

/-!
The following helper isolates the routine passage from a pointwise formula
for the GT semigroup solution to the corresponding multiplier derivative of
the GT functional.
-/

private lemma flatness_deriv_gtFunctional_of_solution
    (β h q s lam v : ℝ) (U : ℝ → GTTwoField)
    (hU : ∀ l x₁ x₂,
      gtSemigroupSolution β q s l v 0 x₁ x₂ = U l x₁ x₂) :
    deriv (fun l => gtFunctional β h q s l v) lam =
      standardGaussianExpectation (fun z =>
        deriv (fun l => U l
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun x : ℝ => x - v)
  apply congrArg standardGaussianExpectation
  funext z
  congr 1
  funext l
  exact hU l _ _

/-! ### Case `|v| = 0` -/

lemma flatness_gtFunctional_formula_abs_v_eq_zero
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hv : |v| = 0) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal lam))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - gtCorrection β q s := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  simp [gtFunctional, gtSemigroupSolution, hq0]


lemma flatness_deriv_gtFunctional_formula_abs_v_eq_zero
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hv : |v| = 0) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal l))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  simpa using
    flatness_deriv_gtFunctional_of_solution β h q s lam 0
      (fun l =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal l)))
      (by
        intro l x₁ x₂
        simp [gtSemigroupSolution, hq0])


/-! ### Case `0 < |v| < q` -/

lemma flatness_gtFunctional_formula_abs_v_lt_q
    (β h q s lam v : ℝ)
    (hv0 : 0 < |v|) (hvq : |v| < q) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hqr : ¬ q ≤ |v| := not_le.mpr hvq
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hv0
  have hqpos : 0 < q := lt_trans hv0 hvq
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hqpos
  simp [gtFunctional, gtSemigroupSolution, hqr, hr0, hq0]


lemma flatness_deriv_gtFunctional_formula_abs_v_lt_q
    (β h q s lam v : ℝ)
    (hv0 : 0 < |v|) (hvq : |v| < q) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  have hqr : ¬ q ≤ |v| := not_le.mpr hvq
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hv0
  have hqpos : 0 < q := lt_trans hv0 hvq
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hqpos
  exact
    flatness_deriv_gtFunctional_of_solution β h q s lam v
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal l))))
      (by
        intro l x₁ x₂
        simp [gtSemigroupSolution, hqr, hr0, hq0])


/-! ### Case `q ≤ |v| < 1` -/

lemma flatness_gtFunctional_formula_q_le_abs_v_lt_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hqv : q ≤ |v|) (_hv1 : |v| < 1) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hrpos : 0 < |v| := lt_of_lt_of_le hq hqv
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  simp [gtFunctional, gtSemigroupSolution, hqv, hr0, hq0]


lemma flatness_deriv_gtFunctional_formula_q_le_abs_v_lt_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hqv : q ≤ |v|) (_hv1 : |v| < 1) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hrpos : 0 < |v| := lt_of_lt_of_le hq hqv
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  exact
    flatness_deriv_gtFunctional_of_solution β h q s lam v
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal l))))
      (by
        intro l x₁ x₂
        simp [gtSemigroupSolution, hqv, hr0, hq0])


/-! ### Case `|v| = 1` -/

lemma flatness_gtFunctional_formula_abs_v_eq_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num
  simp [gtFunctional, gtSemigroupSolution, hv, hq1, hq0, h10]


lemma flatness_deriv_gtFunctional_formula_abs_v_eq_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  exact
    flatness_deriv_gtFunctional_of_solution β h q s lam v
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal l))))
      (by
        intro l x₁ x₂
        simp [gtSemigroupSolution, hv, hq1, hq0])


/-! ### Explicit formulas for ∂_λ U_s^{λ,v}|_{λ=0} -/

private abbrev flatnessGauss : Measure ℝ := gaussianReal 0 1

private lemma flatness_fLbaseD_zero (x₁ x₂ : ℝ) :
    GTFrame.fLbaseD 0 (x₁, x₂) = Real.tanh x₁ * Real.tanh x₂ := by
  have h := (GTFrame.hasDerivAt_fLbase 0 (x₁, x₂)).deriv
  change deriv (fun l => gtTerminal l x₁ x₂) 0 = _ at h
  rw [deriv_gtTerminal_zero] at h
  exact h.symm

private lemma flatness_upper_goodFam (b : ℝ) :
    GTFrame.GoodFam
      (fun (_ : Unit) l (x : ℝ × ℝ) => GTFrame.fLbase l x + b ^ 2)
      (fun (_ : Unit) l (x : ℝ × ℝ) => GTFrame.fLbaseD l x) := by
  refine
    { contF := (GTFrame.continuous_fLbase.comp (by fun_prop)).add continuous_const
      contD := GTFrame.continuous_fLbaseD.comp (by fun_prop)
      hasDeriv := fun _ l x => (GTFrame.hasDerivAt_fLbase l x).add_const _
      lipx := ?_
      bddD := fun _ l x => GTFrame.fLbaseD_bdd l x }
  intro _ l x y
  simpa using GTFrame.fLbase_lipx l x y

/-- A final level-one diagonal step does not change the multiplier derivative
of the terminal condition. -/
lemma deriv_gtDiagonalStep_one_gtTerminal_zero (scale x₁ x₂ : ℝ) :
    deriv (fun l => gtDiagonalStep 1 scale (gtTerminal l) x₁ x₂) 0 =
      Real.tanh x₁ * Real.tanh x₂ := by
  have hfun :
      (fun l => gtDiagonalStep 1 scale (gtTerminal l) x₁ x₂) =
      (fun l => gtTerminal l x₁ x₂ + scale ^ 2) := by
    funext l
    exact gtDiagonalStep_one_terminal scale l x₁ x₂
  rw [hfun, ((hasDerivAt_gtTerminal 0 x₁ x₂).add_const (scale ^ 2)).deriv]
  change GTFrame.fLbaseD 0 (x₁, x₂) = _
  exact flatness_fLbaseD_zero x₁ x₂

/-- Propagation through a zero-mass independent diagonal step. -/
lemma deriv_gtDiagonalStep_zero_one_terminal_zero (a b x₁ x₂ : ℝ) :
    deriv (fun l => gtDiagonalStep 0 a
      (gtDiagonalStep 1 b (gtTerminal l)) x₁ x₂) 0 =
    standardGaussianExpectation (fun z₁ =>
      standardGaussianExpectation (fun z₂ =>
        Real.tanh (x₁ + a * z₁) * Real.tanh (x₂ + a * z₂))) := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbase l x + b ^ 2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  have hF : GTFrame.GoodFam F D := flatness_upper_goodFam b
  let F₂ := GTFrame.step0 flatnessGauss (fun _ : Unit => 0) (fun _ => a) F
  let D₂ := GTFrame.step0 flatnessGauss (fun _ : Unit => 0) (fun _ => a) D
  have hF₂ : GTFrame.GoodFam F₂ D₂ :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hF
      continuous_const continuous_const
  let F₃ := GTFrame.step0 flatnessGauss (fun _ : Unit => a) (fun _ => 0) F₂
  let D₃ := GTFrame.step0 flatnessGauss (fun _ : Unit => a) (fun _ => 0) D₂
  have hF₃ : GTFrame.GoodFam F₃ D₃ :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hF₂
      continuous_const continuous_const
  have hd := (hF₃.hasDeriv () 0 (x₁, x₂)).deriv
  change deriv (fun l => F₃ () l (x₁, x₂)) 0 = D₃ () 0 (x₁, x₂) at hd
  have hfun :
      (fun l => gtDiagonalStep 0 a
        (gtDiagonalStep 1 b (gtTerminal l)) x₁ x₂) =
      (fun l => F₃ () l (x₁, x₂)) := by
    funext l
    have hu : gtDiagonalStep 1 b (gtTerminal l) =
        fun y₁ y₂ => gtTerminal l y₁ y₂ + b ^ 2 := by
      funext y₁ y₂
      exact gtDiagonalStep_one_terminal b l y₁ y₂
    rw [hu]
    simp [F₃, F₂, F, GTFrame.step0, flatnessGauss,
      standardGaussianExpectation, gtDiagonalStep]
  rw [hfun, hd]
  simp [D₃, D₂, D, GTFrame.step0, flatnessGauss,
    standardGaussianExpectation, flatness_fLbaseD_zero]

/-- Propagation through a zero-mass rank-one step followed by a zero-mass
independent diagonal step. -/
lemma deriv_gtRankOneStep_zero_diagonal_zero_at_zero
    (r sign a b x₁ x₂ : ℝ) :
    deriv (fun l => gtRankOneStep 0 r sign
      (gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal l))) x₁ x₂) 0 =
    standardGaussianExpectation (fun z₀ =>
      standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          Real.tanh (x₁ + r * z₀ + a * z₁) *
            Real.tanh (x₂ + sign * r * z₀ + a * z₂)))) := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbase l x + b ^ 2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  have hF : GTFrame.GoodFam F D := flatness_upper_goodFam b
  let F₂ := GTFrame.step0 flatnessGauss (fun _ : Unit => 0) (fun _ => a) F
  let D₂ := GTFrame.step0 flatnessGauss (fun _ : Unit => 0) (fun _ => a) D
  have hF₂ : GTFrame.GoodFam F₂ D₂ :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hF
      continuous_const continuous_const
  let F₃ := GTFrame.step0 flatnessGauss (fun _ : Unit => a) (fun _ => 0) F₂
  let D₃ := GTFrame.step0 flatnessGauss (fun _ : Unit => a) (fun _ => 0) D₂
  have hF₃ : GTFrame.GoodFam F₃ D₃ :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hF₂
      continuous_const continuous_const
  let F₄ := GTFrame.step0 flatnessGauss (fun _ : Unit => r) (fun _ => sign * r) F₃
  let D₄ := GTFrame.step0 flatnessGauss (fun _ : Unit => r) (fun _ => sign * r) D₃
  have hF₄ : GTFrame.GoodFam F₄ D₄ :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hF₃
      continuous_const continuous_const
  have hd := (hF₄.hasDeriv () 0 (x₁, x₂)).deriv
  change deriv (fun l => F₄ () l (x₁, x₂)) 0 = D₄ () 0 (x₁, x₂) at hd
  have hfun :
      (fun l => gtRankOneStep 0 r sign
        (gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal l))) x₁ x₂) =
      (fun l => F₄ () l (x₁, x₂)) := by
    funext l
    have hu : gtDiagonalStep 1 b (gtTerminal l) =
        fun y₁ y₂ => gtTerminal l y₁ y₂ + b ^ 2 := by
      funext y₁ y₂
      exact gtDiagonalStep_one_terminal b l y₁ y₂
    rw [hu]
    simp [F₄, F₃, F₂, F, GTFrame.step0, flatnessGauss,
      standardGaussianExpectation, gtRankOneStep, gtDiagonalStep]
  rw [hfun, hd]
  simp [D₄, D₃, D₂, D, GTFrame.step0, flatnessGauss,
    standardGaussianExpectation, flatness_fLbaseD_zero]

/-- The explicit tilted quotient produced by a mass-`1/2` rank-one step at
`lam = 0`.  The `upperScale` term records the harmless constant contributed
by the final level-one diagonal step. -/
noncomputable def gtHalfStepEndpoint
    (scale upperScale sign x₁ x₂ : ℝ) : ℝ :=
  standardGaussianExpectation (fun z =>
      (Real.tanh (x₁ + scale * z) *
        Real.tanh (x₂ + sign * scale * z)) *
      Real.exp ((1 / 2) *
        (gtTerminal 0 (x₁ + scale * z) (x₂ + sign * scale * z) +
          upperScale ^ 2))) /
    standardGaussianExpectation (fun z =>
      Real.exp ((1 / 2) *
        (gtTerminal 0 (x₁ + scale * z) (x₂ + sign * scale * z) +
          upperScale ^ 2)))

/-- On the diagonal and with positive path sign, the half-step endpoint is the
usual `tanh² cosh` tilted quotient. -/
lemma gtHalfStepEndpoint_diagonal (scale upperScale x : ℝ) :
    gtHalfStepEndpoint scale upperScale 1 x x =
      standardGaussianExpectation (fun z =>
        Real.tanh (x + scale * z) ^ 2 * Real.cosh (x + scale * z)) /
      standardGaussianExpectation (fun z => Real.cosh (x + scale * z)) := by
  have hw (y : ℝ) :
      Real.exp ((1 / 2) * (gtTerminal 0 y y + upperScale ^ 2)) =
        Real.exp (upperScale ^ 2 / 2) * Real.cosh y := by
    rw [gtTerminal_zero]
    rw [show (1 / 2 : ℝ) *
      (Real.log (Real.cosh y) + Real.log (Real.cosh y) + upperScale ^ 2) =
        upperScale ^ 2 / 2 + Real.log (Real.cosh y) by ring]
    rw [Real.exp_add, Real.exp_log (Real.cosh_pos y)]
  unfold gtHalfStepEndpoint
  simp only [one_mul]
  simp_rw [hw]
  have hn : (fun z =>
      (Real.tanh (x + scale * z) * Real.tanh (x + scale * z)) *
        (Real.exp (upperScale ^ 2 / 2) * Real.cosh (x + scale * z))) =
      fun z => Real.exp (upperScale ^ 2 / 2) *
        (Real.tanh (x + scale * z) ^ 2 * Real.cosh (x + scale * z)) := by
    funext z
    ring
  rw [hn]
  unfold standardGaussianExpectation
  rw [integral_const_mul, integral_const_mul]
  field_simp [Real.exp_ne_zero (upperScale ^ 2 / 2)]

/-- Gaussian expectation of a shifted hyperbolic cosine. -/
lemma standardGaussianExpectation_cosh_shift (scale x : ℝ) :
    standardGaussianExpectation (fun z => Real.cosh (x + scale * z)) =
      Real.exp (scale ^ 2 / 2) * Real.cosh x := by
  have hmgf (t : ℝ) :
      standardGaussianExpectation (fun z => Real.exp (t * z)) =
        Real.exp (t ^ 2 / 2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
    simpa [mgf, standardGaussianExpectation] using h
  have hi₁ : Integrable (fun z : ℝ => Real.exp x * Real.exp (scale * z))
      (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal scale).const_mul _
  have hi₂ : Integrable (fun z : ℝ => Real.exp (-x) * Real.exp ((-scale) * z))
      (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal (-scale)).const_mul _
  have hfun : (fun z : ℝ => Real.cosh (x + scale * z)) =
      fun z => (Real.exp x * Real.exp (scale * z) +
        Real.exp (-x) * Real.exp ((-scale) * z)) / 2 := by
    funext z
    rw [Real.cosh_eq, Real.exp_add]
    congr 1
    rw [show -(x + scale * z) = -x + (-scale) * z by ring, Real.exp_add]
  rw [hfun]
  unfold standardGaussianExpectation
  rw [integral_div, integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
  change (Real.exp x * standardGaussianExpectation (fun z => Real.exp (scale * z)) +
      Real.exp (-x) * standardGaussianExpectation (fun z => Real.exp ((-scale) * z))) / 2 = _
  rw [hmgf scale, hmgf (-scale), Real.cosh_eq]
  ring_nf

/-- The diagonal half-step quotient is exactly the tilted heat semigroup.
This includes the degenerate case `scale = 0`. -/
lemma gtHalfStepEndpoint_diagonal_eq_tilted
    (scale upperScale x : ℝ) (hscale : 0 ≤ scale) :
    gtHalfStepEndpoint scale upperScale 1 x x =
      tiltedHeatSemigroup (scale ^ 2) (fun y => Real.tanh y ^ 2) x := by
  rw [gtHalfStepEndpoint_diagonal, standardGaussianExpectation_cosh_shift]
  unfold tiltedHeatSemigroup heatSemigroup
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hscale]
  field_simp [Real.exp_ne_zero (scale ^ 2 / 2), ne_of_gt (Real.cosh_pos x)]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf
  simp

/-- Common endpoint derivative formula for a zero-mass rank-one step followed
by the mass-`1/2` step. -/
lemma deriv_gtRankOneStep_zero_half_at_zero
    (r a b sign x₁ x₂ : ℝ) :
    deriv (fun l => gtRankOneStep 0 r sign
      (gtRankOneStep (1 / 2) a sign
        (gtDiagonalStep 1 b (gtTerminal l))) x₁ x₂) 0 =
    standardGaussianExpectation (fun z₀ =>
      gtHalfStepEndpoint a b sign
        (x₁ + r * z₀) (x₂ + sign * r * z₀)) := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbase l x + b ^ 2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  have hF : GTFrame.GoodFam F D := flatness_upper_goodFam b
  let FH := GTFrame.stepM flatnessGauss (1 / 2)
    (fun _ : Unit => a) (fun _ => sign * a) F
  let DH := GTFrame.stepMD flatnessGauss (1 / 2)
    (fun _ : Unit => a) (fun _ => sign * a) F D
  have hFH : GTFrame.GoodFam FH DH :=
    GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) hF
      (by norm_num) continuous_const continuous_const
  let FO := GTFrame.step0 flatnessGauss
    (fun _ : Unit => r) (fun _ => sign * r) FH
  let DO := GTFrame.step0 flatnessGauss
    (fun _ : Unit => r) (fun _ => sign * r) DH
  have hFO : GTFrame.GoodFam FO DO :=
    GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) hFH
      continuous_const continuous_const
  have hd := (hFO.hasDeriv () 0 (x₁, x₂)).deriv
  change deriv (fun l => FO () l (x₁, x₂)) 0 = DO () 0 (x₁, x₂) at hd
  have hfun :
      (fun l => gtRankOneStep 0 r sign
        (gtRankOneStep (1 / 2) a sign
          (gtDiagonalStep 1 b (gtTerminal l))) x₁ x₂) =
      (fun l => FO () l (x₁, x₂)) := by
    funext l
    have hu : gtDiagonalStep 1 b (gtTerminal l) =
        fun y₁ y₂ => gtTerminal l y₁ y₂ + b ^ 2 := by
      funext y₁ y₂
      exact gtDiagonalStep_one_terminal b l y₁ y₂
    rw [hu]
    simp [FO, FH, F, GTFrame.step0, GTFrame.stepM, flatnessGauss,
      standardGaussianExpectation, gtRankOneStep]
  rw [hfun, hd]
  simp [DO, DH, F, D, GTFrame.step0, GTFrame.stepMD, flatnessGauss,
    standardGaussianExpectation, flatness_fLbaseD_zero, gtHalfStepEndpoint]

/-! #### Branchwise endpoint formulas for `U` -/

/-- Endpoint formula in the branch `|v| = 0`; the zero-length rank-one
increment has disappeared. -/
lemma flatness_deriv_U_abs_v_eq_zero
    (β q s v x₁ x₂ : ℝ) (hq : 0 < q) (hv : |v| = 0) :
    deriv (fun lam => gtSemigroupSolution β q s lam v 0 x₁ x₂) 0 =
    standardGaussianExpectation (fun z₁ =>
      standardGaussianExpectation (fun z₂ =>
        Real.tanh (x₁ + gtIncrementScale β s 0 q * z₁) *
          Real.tanh (x₂ + gtIncrementScale β s 0 q * z₂))) := by
  rw [deriv_gtSemigroupSolution_zero_abs_v_eq_zero β q s v x₁ x₂ hq hv]
  exact deriv_gtDiagonalStep_zero_one_terminal_zero _ _ _ _

/-- Endpoint formula in the branch `0 < |v| < q`. -/
lemma flatness_deriv_U_abs_v_lt_q
    (β q s v x₁ x₂ : ℝ) (hv0 : 0 < |v|) (hvq : |v| < q) :
    deriv (fun lam => gtSemigroupSolution β q s lam v 0 x₁ x₂) 0 =
    standardGaussianExpectation (fun z₀ =>
      standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          Real.tanh (x₁ + gtIncrementScale β s 0 |v| * z₀ +
            gtIncrementScale β s |v| q * z₁) *
          Real.tanh (x₂ + gtPathSign v * gtIncrementScale β s 0 |v| * z₀ +
            gtIncrementScale β s |v| q * z₂)))) := by
  rw [deriv_gtSemigroupSolution_zero_abs_v_lt_q β q s v x₁ x₂ hv0 hvq]
  exact deriv_gtRankOneStep_zero_diagonal_zero_at_zero _ _ _ _ _ _

/-- General endpoint formula in the branch `q ≤ |v| < 1`.  In particular,
the signed path factor is retained for negative overlaps. -/
lemma flatness_deriv_U_q_le_abs_v_lt_one
    (β q s v x₁ x₂ : ℝ) (hq : 0 < q) (hqv : q ≤ |v|) (hv1 : |v| < 1) :
    deriv (fun lam => gtSemigroupSolution β q s lam v 0 x₁ x₂) 0 =
    standardGaussianExpectation (fun z₀ =>
      gtHalfStepEndpoint (gtIncrementScale β s q |v|)
        (gtIncrementScale β s |v| 1) (gtPathSign v)
        (x₁ + gtIncrementScale β s 0 q * z₀)
        (x₂ + gtPathSign v * gtIncrementScale β s 0 q * z₀)) := by
  rw [deriv_gtSemigroupSolution_zero_q_le_abs_v_lt_one
    β q s v x₁ x₂ hq hqv hv1]
  exact deriv_gtRankOneStep_zero_half_at_zero _ _ _ _ _ _

/-- Endpoint formula at `|v| = 1`, obtained from the same half-step lemma as
the preceding branch. -/
lemma flatness_deriv_U_abs_v_eq_one
    (β q s v x₁ x₂ : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    deriv (fun lam => gtSemigroupSolution β q s lam v 0 x₁ x₂) 0 =
    standardGaussianExpectation (fun z₀ =>
      gtHalfStepEndpoint (gtIncrementScale β s q 1)
        (gtIncrementScale β s 1 1) (gtPathSign v)
        (x₁ + gtIncrementScale β s 0 q * z₀)
        (x₂ + gtPathSign v * gtIncrementScale β s 0 q * z₀)) := by
  rw [deriv_gtSemigroupSolution_zero_abs_v_eq_one
    β q s v x₁ x₂ hq hq1 hv]
  exact deriv_gtRankOneStep_zero_half_at_zero _ _ _ _ _ _

private lemma gtIncrementScale_sq_of_nonneg
    (β s lower upper : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hlu : lower ≤ upper) :
    gtIncrementScale β s lower upper ^ 2 =
      s * β ^ 2 * (upper - lower) := by
  unfold gtIncrementScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hs, Real.sq_sqrt (sub_nonneg.mpr hlu)]
  ring

private lemma gtIncrementScale_nonneg
    (β s lower upper : ℝ) (hβ : 0 ≤ β) :
    0 ≤ gtIncrementScale β s lower upper := by
  unfold gtIncrementScale
  exact mul_nonneg (mul_nonneg hβ (Real.sqrt_nonneg s))
    (Real.sqrt_nonneg (upper - lower))

/-- Positive-overlap diagonal specialization for `q ≤ v < 1`.  The initial
zero-mass step is an ordinary Gaussian expectation of the existing tilted heat
semigroup. -/
lemma flatness_deriv_U_q_le_v_lt_one_diagonal
    (β q s v x : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hq : 0 < q) (hqv : q ≤ v) (hv1 : v < 1) :
    deriv (fun lam => gtSemigroupSolution β q s lam v 0 x x) 0 =
    standardGaussianExpectation (fun z =>
      tiltedHeatSemigroup (s * β ^ 2 * (v - q))
        (fun y => Real.tanh y ^ 2)
        (x + gtIncrementScale β s 0 q * z)) := by
  have hv0 : 0 ≤ v := le_trans hq.le hqv
  have hsign : gtPathSign v = 1 := by simp [gtPathSign, hv0]
  rw [flatness_deriv_U_q_le_abs_v_lt_one β q s v x x hq]
  · simp only [abs_of_nonneg hv0, hsign, one_mul]
    apply congrArg standardGaussianExpectation
    funext z
    rw [gtHalfStepEndpoint_diagonal_eq_tilted]
    · rw [gtIncrementScale_sq_of_nonneg β s q v hβ hs hqv]
    · exact gtIncrementScale_nonneg β s q v hβ
  · simpa [abs_of_nonneg hv0] using hqv
  · simpa [abs_of_nonneg hv0] using hv1

/-- Positive endpoint specialization at `v = 1`. -/
lemma flatness_deriv_U_v_eq_one_diagonal
    (β q s x : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    deriv (fun lam => gtSemigroupSolution β q s lam 1 0 x x) 0 =
    standardGaussianExpectation (fun z =>
      tiltedHeatSemigroup (s * β ^ 2 * (1 - q))
        (fun y => Real.tanh y ^ 2)
        (x + gtIncrementScale β s 0 q * z)) := by
  rw [flatness_deriv_U_abs_v_eq_one β q s 1 x x hq hq1 (by norm_num)]
  simp only [gtPathSign, if_pos (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  apply congrArg standardGaussianExpectation
  funext z
  rw [gtHalfStepEndpoint_diagonal_eq_tilted]
  · rw [gtIncrementScale_sq_of_nonneg β s q 1 hβ hs hq1]
  · exact gtIncrementScale_nonneg β s q 1 hβ

/-! #### Immediate endpoint formulas for the GT functional -/

lemma flatness_deriv_gtFunctional_zero_abs_v_eq_zero
    (β h q s v : ℝ) (hq : 0 < q) (hv : |v| = 0) :
    deriv (fun l => gtFunctional β h q s l v) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          Real.tanh (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₁) *
          Real.tanh (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₂)))) := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  rw [deriv_gtFunctional_eq]
  rw [sub_zero]
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_abs_v_eq_zero β q s 0 _ _ hq (abs_zero)

lemma flatness_deriv_gtFunctional_zero_abs_v_lt_q
    (β h q s v : ℝ) (hv0 : 0 < |v|) (hvq : |v| < q) :
    deriv (fun l => gtFunctional β h q s l v) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₀ =>
        standardGaussianExpectation (fun z₁ =>
          standardGaussianExpectation (fun z₂ =>
            Real.tanh (h + β * Real.sqrt ((1 - s) * q) * z +
              gtIncrementScale β s 0 |v| * z₀ +
              gtIncrementScale β s |v| q * z₁) *
            Real.tanh (h + β * Real.sqrt ((1 - s) * q) * z +
              gtPathSign v * gtIncrementScale β s 0 |v| * z₀ +
              gtIncrementScale β s |v| q * z₂))))) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun y : ℝ => y - v)
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_abs_v_lt_q β q s v _ _ hv0 hvq

lemma flatness_deriv_gtFunctional_zero_q_le_abs_v_lt_one
    (β h q s v : ℝ) (hq : 0 < q) (hqv : q ≤ |v|) (hv1 : |v| < 1) :
    deriv (fun l => gtFunctional β h q s l v) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₀ =>
        gtHalfStepEndpoint (gtIncrementScale β s q |v|)
          (gtIncrementScale β s |v| 1) (gtPathSign v)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₀)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtPathSign v * gtIncrementScale β s 0 q * z₀))) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun y : ℝ => y - v)
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_q_le_abs_v_lt_one β q s v _ _ hq hqv hv1

/-! #### Identification with `tilde g_s` on negative overlaps -/

/--
For `|v| ≤ q`, the Gaussian correlation
`tilde g_s(v) = E[tanh(Y₁(v)) tanh(Y₂(v))]`.

The four independent standard Gaussians below give both coordinates
variance `β² q`; their covariance is
`β² ((1-s) q + s v)`.
-/
noncomputable def flatnessTildeG
    (β h q s v : ℝ) : ℝ :=
  standardGaussianExpectation (fun z =>
    standardGaussianExpectation (fun z₀ =>
      standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          Real.tanh
              (h + β * Real.sqrt ((1 - s) * q) * z
                + gtIncrementScale β s 0 |v| * z₀
                + gtIncrementScale β s |v| q * z₁) *
            Real.tanh
              (h + β * Real.sqrt ((1 - s) * q) * z
                + gtPathSign v *
                    gtIncrementScale β s 0 |v| * z₀
                + gtIncrementScale β s |v| q * z₂)))))

/--
A zero-length mass-`1/2` step does not change the endpoint
multiplier derivative.
-/
@[simp] lemma flatness_gtHalfStepEndpoint_zero_scale
    (upperScale sign x₁ x₂ : ℝ) :
    gtHalfStepEndpoint 0 upperScale sign x₁ x₂ =
      Real.tanh x₁ * Real.tanh x₂ := by
  unfold gtHalfStepEndpoint
  simp [standardGaussianExpectation, Real.exp_ne_zero]

/-- Positive-overlap functional endpoint formula in tilted-semigroup form. -/
lemma flatness_deriv_gtFunctional_zero_q_le_v_lt_one
    (β h q s v : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hq : 0 < q) (hqv : q ≤ v) (hv1 : v < 1) :
    deriv (fun l => gtFunctional β h q s l v) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₀ =>
        tiltedHeatSemigroup (s * β ^ 2 * (v - q))
          (fun y => Real.tanh y ^ 2)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₀))) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun y : ℝ => y - v)
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_q_le_v_lt_one_diagonal β q s v _ hβ hs hq hqv hv1

/-- Functional endpoint formula at the positive endpoint `v = 1`. -/
lemma flatness_deriv_gtFunctional_zero_v_eq_one
    (β h q s : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    deriv (fun l => gtFunctional β h q s l 1) 0 =
    standardGaussianExpectation (fun z =>
      standardGaussianExpectation (fun z₀ =>
        tiltedHeatSemigroup (s * β ^ 2 * (1 - q))
          (fun y => Real.tanh y ^ 2)
          (h + β * Real.sqrt ((1 - s) * q) * z +
            gtIncrementScale β s 0 q * z₀))) - 1 := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun y : ℝ => y - 1)
  apply congrArg standardGaussianExpectation
  funext z
  exact flatness_deriv_U_v_eq_one_diagonal β q s _ hβ hs hq hq1

private lemma flatness_tiltedHeatSemigroup_zero (f : ℝ → ℝ) (x : ℝ) :
    tiltedHeatSemigroup 0 f x = f x := by
  unfold tiltedHeatSemigroup heatSemigroup standardGaussianExpectation
  simp [ne_of_gt (Real.cosh_pos x)]

private lemma flatness_gaussian_convolution_tanh_sq (h a b c : ℝ)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    standardGaussianExpectation (fun x =>
      standardGaussianExpectation (fun y => Real.tanh (h + a * x + b * y) ^ 2)) =
    standardGaussianExpectation (fun z => Real.tanh (h + c * z) ^ 2) := by
  let va : NNReal := NNReal.mk (a ^ 2) (sq_nonneg a) * 1
  let vb : NNReal := NNReal.mk (b ^ 2) (sq_nonneg b) * 1
  let vc : NNReal := NNReal.mk (c ^ 2) (sq_nonneg c) * 1
  have htanh : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div₀ Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')
  have hma : Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1) =
      gaussianReal 0 va := by
    simpa [va] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal)) a)
  have hmb : Measure.map (fun x : ℝ => b * x) (gaussianReal 0 1) =
      gaussianReal 0 vb := by
    simpa [vb] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal)) b)
  have hmc : Measure.map (fun x : ℝ => c * x) (gaussianReal 0 1) =
      gaussianReal 0 vc := by
    simpa [vc] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal)) c)
  have hv : va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]
  have hf : Integrable (fun z : ℝ => Real.tanh (h + z) ^ 2)
      (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    apply Integrable.of_bound (C := 1)
    · exact ((htanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (Real.tanh_sq_lt_one _).le
  have hprod : Integrable (fun p : ℝ × ℝ => Real.tanh (h + (p.1 + p.2)) ^ 2)
      ((gaussianReal 0 va).prod (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hf
    exact (integrable_map_measure hf.1 (by fun_prop)).mp hf
  have houter : AEStronglyMeasurable
      (fun x : ℝ => ∫ y, Real.tanh (h + (x + y)) ^ 2 ∂gaussianReal 0 vb)
      (gaussianReal 0 va) := hprod.integral_prod_left.1
  have hinner (x : ℝ) :
      (∫ y, Real.tanh (h + a * x + b * y) ^ 2 ∂gaussianReal 0 1) =
        ∫ y, Real.tanh (h + a * x + y) ^ 2 ∂gaussianReal 0 vb := by
    have hm : AEStronglyMeasurable (fun y : ℝ => Real.tanh (h + a * x + y) ^ 2)
        (Measure.map (fun y : ℝ => b * y) (gaussianReal 0 1)) :=
      ((htanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
    rw [← hmb, integral_map (by fun_prop) hm]
  have houter_map :
      (∫ x, ∫ y, Real.tanh (h + a * x + y) ^ 2 ∂gaussianReal 0 vb
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.tanh (h + x + y) ^ 2 ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y, Real.tanh (h + (x + y)) ^ 2 ∂gaussianReal 0 vb)
        (Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1)) := by
      simpa [hma] using houter
    rw [← hma]
    simpa only [add_assoc] using (integral_map (by fun_prop) hm).symm
  unfold standardGaussianExpectation
  calc
    (∫ x, ∫ y, Real.tanh (h + a * x + b * y) ^ 2 ∂gaussianReal 0 1
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.tanh (h + x + y) ^ 2 ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
            exact houter_map
    _ = ∫ z, Real.tanh (h + z) ^ 2
          ∂(gaussianReal 0 va ∗ gaussianReal 0 vb) := by
            simpa only [add_assoc] using (integral_conv hf).symm
    _ = ∫ z, Real.tanh (h + z) ^ 2 ∂gaussianReal 0 vc := by
          rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    _ = ∫ z, Real.tanh (h + c * z) ^ 2 ∂gaussianReal 0 1 := by
          rw [← hmc, integral_map (by fun_prop)]
          exact ((htanh.comp (by fun_prop)).pow 2).aestronglyMeasurable

/-! #### Identification of the endpoint derivative with `g_s(v) - v` -/

/--
A bounded continuous test function only sees the total variance of two
independent centered Gaussian increments.
-/
private lemma flatness_gaussian_convolution_bounded
    (f : ℝ → ℝ) (hfcont : Continuous f)
    (hfbound : ∀ x, ‖f x‖ ≤ 1)
    (h a b c : ℝ)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    standardGaussianExpectation (fun x =>
      standardGaussianExpectation (fun y =>
        f (h + a * x + b * y))) =
    standardGaussianExpectation (fun z =>
      f (h + c * z)) := by
  let va : NNReal := NNReal.mk (a ^ 2) (sq_nonneg a) * 1
  let vb : NNReal := NNReal.mk (b ^ 2) (sq_nonneg b) * 1
  let vc : NNReal := NNReal.mk (c ^ 2) (sq_nonneg c) * 1

  have hma :
      Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1) =
        gaussianReal 0 va := by
    simpa [va] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : NNReal)) a)

  have hmb :
      Measure.map (fun x : ℝ => b * x) (gaussianReal 0 1) =
        gaussianReal 0 vb := by
    simpa [vb] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : NNReal)) b)

  have hmc :
      Measure.map (fun x : ℝ => c * x) (gaussianReal 0 1) =
        gaussianReal 0 vc := by
    simpa [vc] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : NNReal)) c)

  have hv : va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]

  have hfint :
      Integrable (fun z : ℝ => f (h + z))
        (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    apply Integrable.of_bound (C := 1)
    · exact (hfcont.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with z
      exact hfbound (h + z)

  have hprod :
      Integrable
        (fun p : ℝ × ℝ => f (h + (p.1 + p.2)))
        ((gaussianReal 0 va).prod (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hfint
    exact (integrable_map_measure hfint.1 (by fun_prop)).mp hfint

  have houter :
      AEStronglyMeasurable
        (fun x : ℝ =>
          ∫ y, f (h + (x + y)) ∂gaussianReal 0 vb)
        (gaussianReal 0 va) :=
    hprod.integral_prod_left.1

  have hinner (x : ℝ) :
      (∫ y, f (h + a * x + b * y) ∂gaussianReal 0 1) =
        ∫ y, f (h + a * x + y) ∂gaussianReal 0 vb := by
    have hm :
        AEStronglyMeasurable
          (fun y : ℝ => f (h + a * x + y))
          (Measure.map (fun y : ℝ => b * y)
            (gaussianReal 0 1)) :=
      (hfcont.comp (by fun_prop)).aestronglyMeasurable
    rw [← hmb, integral_map (by fun_prop) hm]

  have houter_map :
      (∫ x,
          ∫ y, f (h + a * x + y) ∂gaussianReal 0 vb
        ∂gaussianReal 0 1) =
      ∫ x,
          ∫ y, f (h + x + y) ∂gaussianReal 0 vb
        ∂gaussianReal 0 va := by
    have hm :
        AEStronglyMeasurable
          (fun x : ℝ =>
            ∫ y, f (h + (x + y)) ∂gaussianReal 0 vb)
          (Measure.map (fun x : ℝ => a * x)
            (gaussianReal 0 1)) := by
      simpa [hma] using houter
    rw [← hma]
    simpa only [add_assoc] using
      (integral_map (by fun_prop) hm).symm

  unfold standardGaussianExpectation
  calc
    (∫ x,
        ∫ y, f (h + a * x + b * y) ∂gaussianReal 0 1
      ∂gaussianReal 0 1)
        =
      ∫ x,
        ∫ y, f (h + x + y) ∂gaussianReal 0 vb
      ∂gaussianReal 0 va := by
        rw [integral_congr_ae
          (Filter.Eventually.of_forall hinner)]
        exact houter_map

    _ = ∫ z, f (h + z)
          ∂(gaussianReal 0 va ∗ gaussianReal 0 vb) := by
        simpa only [add_assoc] using (integral_conv hfint).symm

    _ = ∫ z, f (h + z) ∂gaussianReal 0 vc := by
        rw [gaussianReal_conv_gaussianReal, hv, zero_add]

    _ = ∫ z, f (h + c * z) ∂gaussianReal 0 1 := by
        rw [← hmc, integral_map (by fun_prop)]
        exact (hfcont.comp (by fun_prop)).aestronglyMeasurable


/--
The lower-branch endpoint profile.  This is
`(H_{a^2} tanh)^2`, written in the same two-Gaussian form
which occurs naturally in the GT derivative.
-/
private noncomputable def flatnessLowerProfile
    (a x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z₁ =>
    standardGaussianExpectation (fun z₂ =>
      Real.tanh (x + a * z₁) *
        Real.tanh (x + a * z₂)))


private lemma flatnessLowerProfile_eq_sq (a x : ℝ) :
    flatnessLowerProfile a x =
      (standardGaussianExpectation (fun z =>
        Real.tanh (x + a * z))) ^ 2 := by
  unfold flatnessLowerProfile standardGaussianExpectation
  calc
    (∫ z₁,
        ∫ z₂,
          Real.tanh (x + a * z₁) *
            Real.tanh (x + a * z₂)
        ∂gaussianReal 0 1
      ∂gaussianReal 0 1)
        =
      ∫ z₁,
        Real.tanh (x + a * z₁) *
          (∫ z₂,
            Real.tanh (x + a * z₂)
            ∂gaussianReal 0 1)
      ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [] with z₁
        rw [integral_const_mul]

    _ =
      (∫ z, Real.tanh (x + a * z)
        ∂gaussianReal 0 1) ^ 2 := by
        rw [integral_mul_const]
        ring


private lemma flatnessLowerProfile_zero (x : ℝ) :
    flatnessLowerProfile 0 x = Real.tanh x ^ 2 := by
  rw [flatnessLowerProfile_eq_sq]
  simp [standardGaussianExpectation]


/--
Continuity and the bound `|flatnessLowerProfile| ≤ 1` follow directly
from the `GoodFam` package already used for the endpoint computation.
-/
private lemma flatnessLowerProfile_good (a : ℝ) :
    Continuous (flatnessLowerProfile a) ∧
      ∀ x, ‖flatnessLowerProfile a x‖ ≤ 1 := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbase l x + 0 ^ 2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x

  have hF : GTFrame.GoodFam F D :=
    flatness_upper_goodFam 0

  let F₂ := GTFrame.step0 flatnessGauss
    (fun _ : Unit => 0) (fun _ => a) F
  let D₂ := GTFrame.step0 flatnessGauss
    (fun _ : Unit => 0) (fun _ => a) D

  have hF₂ : GTFrame.GoodFam F₂ D₂ :=
    GTFrame.step0_good
      (GTFrame.expMoments_gaussianReal 0 1)
      hF continuous_const continuous_const

  let F₃ := GTFrame.step0 flatnessGauss
    (fun _ : Unit => a) (fun _ => 0) F₂
  let D₃ := GTFrame.step0 flatnessGauss
    (fun _ : Unit => a) (fun _ => 0) D₂

  have hF₃ : GTFrame.GoodFam F₃ D₃ :=
    GTFrame.step0_good
      (GTFrame.expMoments_gaussianReal 0 1)
      hF₂ continuous_const continuous_const

  have hdiag : Continuous (fun x : ℝ => (x, x)) := by
    fun_prop

  have heq (x : ℝ) :
      D₃ () 0 (x, x) = flatnessLowerProfile a x := by
    simp [D₃, D₂, D, GTFrame.step0, flatnessGauss,
      flatnessLowerProfile, standardGaussianExpectation,
      flatness_fLbaseD_zero]

  constructor
  · have hc := (hF₃.contD_pt () 0).comp hdiag
    have hfun :
        flatnessLowerProfile a =
          fun x => D₃ () 0 (x, x) := by
      funext x
      exact (heq x).symm
    rw [hfun]
    exact hc

  · intro x
    have hb := hF₃.bddD () 0 (x, x)
    rw [Real.norm_eq_abs, ← heq x]
    exact hb


/--
The upper-branch tilted profile written as the endpoint derivative
of the half-mass GT step.
-/
private noncomputable def flatnessUpperProfile
    (a b x : ℝ) : ℝ :=
  gtHalfStepEndpoint a b 1 x x


private lemma flatnessUpperProfile_good (a b : ℝ) :
    Continuous (flatnessUpperProfile a b) ∧
      ∀ x, ‖flatnessUpperProfile a b x‖ ≤ 1 := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbase l x + b ^ 2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x

  have hF : GTFrame.GoodFam F D :=
    flatness_upper_goodFam b

  let FH := GTFrame.stepM flatnessGauss (1 / 2)
    (fun _ : Unit => a) (fun _ => a) F
  let DH := GTFrame.stepMD flatnessGauss (1 / 2)
    (fun _ : Unit => a) (fun _ => a) F D

  have hFH : GTFrame.GoodFam FH DH :=
    GTFrame.stepM_good
      (GTFrame.expMoments_gaussianReal 0 1)
      hF (by norm_num) continuous_const continuous_const

  have hdiag : Continuous (fun x : ℝ => (x, x)) := by
    fun_prop

  have heq (x : ℝ) :
      DH () 0 (x, x) = flatnessUpperProfile a b x := by
    simp [DH, F, D, GTFrame.stepMD, flatnessGauss,
      standardGaussianExpectation, flatness_fLbaseD_zero,
      flatnessUpperProfile, gtHalfStepEndpoint]

  constructor
  · have hc := (hFH.contD_pt () 0).comp hdiag
    have hfun :
        flatnessUpperProfile a b =
          fun x => DH () 0 (x, x) := by
      funext x
      exact (heq x).symm
    rw [hfun]
    exact hc

  · intro x
    have hb := hFH.bddD () 0 (x, x)
    rw [Real.norm_eq_abs, ← heq x]
    exact hb


private lemma flatness_incrementScale_eq_sqrt_product
    (β s lower upper : ℝ) (hs : 0 ≤ s) :
    gtIncrementScale β s lower upper =
      β * Real.sqrt (s * (upper - lower)) := by
  unfold gtIncrementScale
  rw [Real.sqrt_mul hs]
  ring


/--
Variance identity for the two outer Gaussian increments occurring
in the GT formula.
-/
private lemma flatness_outer_variance_sq
    (β q s v : ℝ)
    (hβ : 0 ≤ β) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hv : 0 ≤ v) :
    (Real.sqrt
      (β ^ 2 * ((1 - s) * q + s * v))) ^ 2 =
      (β * Real.sqrt ((1 - s) * q)) ^ 2 +
        (gtIncrementScale β s 0 v) ^ 2 := by
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hbase :
      0 ≤ (1 - s) * q + s * v :=
    add_nonneg (mul_nonneg h1s hq) (mul_nonneg hs0 hv)
  have hvar :
      0 ≤ β ^ 2 * ((1 - s) * q + s * v) :=
    mul_nonneg (sq_nonneg β) hbase

  rw [Real.sq_sqrt hvar]
  rw [mul_pow, Real.sq_sqrt (mul_nonneg h1s hq)]
  rw [gtIncrementScale_sq_of_nonneg
    β s 0 v hβ hs0 hv]
  ring


/--
For `0 ≤ v ≤ q`, rewrite the scalar order parameter in exactly the
Gaussian form produced by the GT endpoint derivative.
-/
private lemma flatness_scalarOrderParameter_lower_eq
    (β h q s v : ℝ)
    (hβ : 0 ≤ β)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 ≤ q)
    (hv : v ∈ Set.Icc (0 : ℝ) q) :
    scalarOrderParameter β h q s v =
      standardGaussianExpectation (fun z =>
        standardGaussianExpectation (fun z₀ =>
          flatnessLowerProfile
            (gtIncrementScale β s v q)
            (h + β * Real.sqrt ((1 - s) * q) * z +
              gtIncrementScale β s 0 v * z₀))) := by
  have hmax :
      max (q - v) 0 = q - v :=
    max_eq_left (sub_nonneg.mpr hv.2)

  have hd :
      gtIncrementScale β s v q =
        β * Real.sqrt (s * (q - v)) :=
    flatness_incrementScale_eq_sqrt_product β s v q hs.1

  have hpsi (x : ℝ) :
      scalarPsiX β q s v x ^ 2 =
        flatnessLowerProfile
          (gtIncrementScale β s v q) x := by
    unfold scalarPsiX
    rw [hmax, hd]
    exact (flatnessLowerProfile_eq_sq _ x).symm

  have hsq :=
    flatness_outer_variance_sq
      β q s v hβ hs.1 hs.2 hq hv.1

  have hgood :=
    flatnessLowerProfile_good
      (gtIncrementScale β s v q)

  have hconv :=
    flatness_gaussian_convolution_bounded
      (flatnessLowerProfile
        (gtIncrementScale β s v q))
      hgood.1 hgood.2
      h
      (β * Real.sqrt ((1 - s) * q))
      (gtIncrementScale β s 0 v)
      (Real.sqrt
        (β ^ 2 * ((1 - s) * q + s * v)))
      hsq

  unfold scalarOrderParameter localFieldExpectation
  rw [if_pos hv.2]
  unfold heatSemigroup
  simp_rw [hpsi]
  exact hconv.symm


/--
For `q < v`, rewrite the scalar order parameter in exactly the
tilted-semigroup form produced by the GT endpoint derivative.
-/
private lemma flatness_scalarOrderParameter_upper_eq
    (β h q s v : ℝ)
    (hβ : 0 ≤ β)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 ≤ q)
    (hqv : q < v) :
    scalarOrderParameter β h q s v =
      standardGaussianExpectation (fun z =>
        standardGaussianExpectation (fun z₀ =>
          tiltedHeatSemigroup
            (s * β ^ 2 * (v - q))
            (fun y => Real.tanh y ^ 2)
            (h + β * Real.sqrt ((1 - s) * q) * z +
              gtIncrementScale β s 0 q * z₀))) := by
  have hmax :
      max (q - v) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr hqv.le)

  have hpsi (x : ℝ) :
      scalarPsiX β q s v x = Real.tanh x := by
    unfold scalarPsiX
    rw [hmax]
    simp [standardGaussianExpectation]

  let a : ℝ := gtIncrementScale β s q v

  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact gtIncrementScale_nonneg β s q v hβ

  have hasq :
      a ^ 2 = s * β ^ 2 * (v - q) := by
    dsimp [a]
    exact gtIncrementScale_sq_of_nonneg
      β s q v hβ hs.1 hqv.le

  have hprofile (x : ℝ) :
      tiltedHeatSemigroup
        (s * β ^ 2 * (v - q))
        (fun y => Real.tanh y ^ 2) x =
      flatnessUpperProfile a 0 x := by
    symm
    unfold flatnessUpperProfile
    rw [gtHalfStepEndpoint_diagonal_eq_tilted
      a 0 x ha0, hasq]

  have hgood := flatnessUpperProfile_good a 0

  have hfcont :
      Continuous (fun x =>
        tiltedHeatSemigroup
          (s * β ^ 2 * (v - q))
          (fun y => Real.tanh y ^ 2) x) := by
    have heq :
        (fun x =>
          tiltedHeatSemigroup
            (s * β ^ 2 * (v - q))
            (fun y => Real.tanh y ^ 2) x) =
        flatnessUpperProfile a 0 := by
      funext x
      exact hprofile x
    rw [heq]
    exact hgood.1

  have hfbound :
      ∀ x,
        ‖tiltedHeatSemigroup
          (s * β ^ 2 * (v - q))
          (fun y => Real.tanh y ^ 2) x‖ ≤ 1 := by
    intro x
    rw [hprofile x]
    exact hgood.2 x

  have hsq0 :=
    flatness_outer_variance_sq
      β q s q hβ hs.1 hs.2 hq hq

  have hcollapse :
      (1 - s) * q + s * q = q := by
    ring

  have hsq :
      (Real.sqrt (β ^ 2 * q)) ^ 2 =
        (β * Real.sqrt ((1 - s) * q)) ^ 2 +
          (gtIncrementScale β s 0 q) ^ 2 := by
    simpa [hcollapse] using hsq0

  have hconv :=
    flatness_gaussian_convolution_bounded
      (fun x =>
        tiltedHeatSemigroup
          (s * β ^ 2 * (v - q))
          (fun y => Real.tanh y ^ 2) x)
      hfcont hfbound
      h
      (β * Real.sqrt ((1 - s) * q))
      (gtIncrementScale β s 0 q)
      (Real.sqrt (β ^ 2 * q))
      hsq

  unfold scalarOrderParameter localFieldExpectation
  rw [if_neg (not_le_of_gt hqv)]
  simp_rw [hpsi]
  unfold heatSemigroup
  exact hconv.symm


/--
For every positive overlap `0 ≤ v ≤ 1`, the endpoint multiplier
derivative of the GT functional is `g_s(v) - v`.
-/
lemma flatness_deriv_gtFunctional_zero_eq_scalarOrderParameter_sub
    (β h q s v : ℝ)
    (hβ : 0 ≤ β)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun lam => gtFunctional β h q s lam v) 0 =
      scalarOrderParameter β h q s v - v := by

  by_cases hvq : v < q

  · by_cases hvzero : v = 0

    · subst v
      rw [flatness_deriv_gtFunctional_zero_abs_v_eq_zero
        β h q s 0 hq.1 abs_zero]
      rw [flatness_scalarOrderParameter_lower_eq
        β h q s 0 hβ hs hq.1.le
        ⟨le_rfl, hq.1.le⟩]
      simp [flatnessLowerProfile, gtIncrementScale,
        standardGaussianExpectation]

    · have hvpos : 0 < v :=
        lt_of_le_of_ne hv.1 (Ne.symm hvzero)

      rw [flatness_deriv_gtFunctional_zero_abs_v_lt_q
        β h q s v
        (by simpa [abs_of_nonneg hv.1] using hvpos)
        (by simpa [abs_of_nonneg hv.1] using hvq)]

      rw [flatness_scalarOrderParameter_lower_eq
        β h q s v hβ hs hq.1.le
        ⟨hv.1, hvq.le⟩]

      simp [flatnessLowerProfile,
        abs_of_nonneg hv.1, gtPathSign, hv.1]

  · have hqv : q ≤ v := le_of_not_gt hvq

    by_cases hvqeq : v = q

    · subst v

      rw [flatness_deriv_gtFunctional_zero_q_le_v_lt_one
        β h q s q hβ hs.1 hq.1 le_rfl hq.2]

      rw [flatness_scalarOrderParameter_lower_eq
        β h q s q hβ hs hq.1.le
        ⟨hq.1.le, le_rfl⟩]

      simp [flatness_tiltedHeatSemigroup_zero,
        flatnessLowerProfile_zero, gtIncrementScale]

    · have hqvlt : q < v :=
        lt_of_le_of_ne hqv (Ne.symm hvqeq)

      by_cases hvone : v = 1

      · subst v

        rw [flatness_deriv_gtFunctional_zero_v_eq_one
          β h q s hβ hs.1 hq.1 hq.2.le]

        rw [flatness_scalarOrderParameter_upper_eq
          β h q s 1 hβ hs hq.1.le hq.2]

      · have hvlt1 : v < 1 :=
          lt_of_le_of_ne hv.2 hvone

        rw [flatness_deriv_gtFunctional_zero_q_le_v_lt_one
          β h q s v hβ hs.1 hq.1 hqv hvlt1]

        rw [flatness_scalarOrderParameter_upper_eq
          β h q s v hβ hs hq.1.le hqvlt]

/--
For the canonical replica-symmetric fixed point and every `0 ≤ v ≤ 1`,
`∂_lam GT_s(0,v) = g_s(v) - v`.
-/
lemma flatness_deriv_gtFunctional_zero_eq_g_sub
    (β h s v : ℝ)
    (hβ : 0 < β) (hh : 0 < h)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    deriv
        (fun lam =>
          gtFunctional β h (rsQ β h) s lam v) 0 =
      scalarOrderParameterCorrect β h s v - v := by
  unfold scalarOrderParameterCorrect
  exact
    flatness_deriv_gtFunctional_zero_eq_scalarOrderParameter_sub
      β h (rsQ β h) s v
      hβ.le hs
      ⟨rsQ_pos hβ hh, rsQ_lt_one hβ hh⟩
      hv

/-- At an interior replica-symmetric fixed point, the partial derivative of
the GT functional in the multiplier vanishes when the overlap is that fixed
point. -/
lemma flatness_deriv_gtFunctional_zero_at_fixedPoint
    (β h q s : ℝ) (hβ : 0 ≤ β) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q) (hq1 : q < 1) (hfixed : IsRSFixedPoint β h q) :
    deriv (fun lam => gtFunctional β h q s lam q) 0 = 0 := by
  rw [flatness_deriv_gtFunctional_zero_q_le_v_lt_one
    β h q s q hβ hs.1 hq le_rfl hq1]
  simp only [sub_self, mul_zero, flatness_tiltedHeatSemigroup_zero]
  rw [sub_eq_zero]
  have hsquare :
      (β * Real.sqrt q) ^ 2 =
        (β * Real.sqrt ((1 - s) * q)) ^ 2 +
          (gtIncrementScale β s 0 q) ^ 2 := by
    have hq0 : 0 ≤ q := hq.le
    have hs0 : 0 ≤ s := hs.1
    have h1s0 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    simp only [gtIncrementScale, sub_zero]
    rw [mul_pow, Real.sq_sqrt hq0, mul_pow,
      Real.sq_sqrt (mul_nonneg h1s0 hq0)]
    rw [mul_pow, mul_pow, Real.sq_sqrt hs0, Real.sq_sqrt hq0]
    ring
  rw [flatness_gaussian_convolution_tanh_sq h
    (β * Real.sqrt ((1 - s) * q)) (gtIncrementScale β s 0 q)
    (β * Real.sqrt q) hsquare]
  exact hfixed.symm

/-- For the canonical replica-symmetric overlap `q = rsQ β h`, the partial
derivative of the GT functional in `lam` vanishes at `(lam, v) = (0, q)`. -/
lemma flatness_deriv_gtFunctional_zero_at_rsQ
    (β h s : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    deriv (fun lam => gtFunctional β h (rsQ β h) s lam (rsQ β h)) 0 = 0 := by
  rw [flatness_deriv_gtFunctional_zero_eq_g_sub
    β h s (rsQ β h) hβ hh hs (rsQ_mem_Icc β h)]
  exact sub_eq_zero.mpr (scalarOrderParameterCorrect_at_rsQ hβ s)

/-- The sign of the endpoint multiplier derivative follows from the scalar
order-parameter crossing theorem. -/
lemma flatness_deriv_gtFunctional_zero_sign
    {K : Set (ℝ × ℝ)} (data : UniformATData K) {β h s : ℝ}
    (hp : (β, h) ∈ K) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∀ v ∈ Set.Ico (0 : ℝ) (rsQ β h),
      0 < deriv (fun lam => gtFunctional β h (rsQ β h) s lam v) 0) ∧
    deriv (fun lam => gtFunctional β h (rsQ β h) s lam (rsQ β h)) 0 = 0 ∧
    (∀ v ∈ Set.Ioc (rsQ β h) 1,
      deriv (fun lam => gtFunctional β h (rsQ β h) s lam v) 0 < 0) := by
  obtain ⟨hlower, hzero, hupper⟩ :=
    scalarOrderParameterCorrect_sign data hp hs
  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp
  have hq : rsQ β h ∈ Set.Icc (0 : ℝ) 1 := rsQ_mem_Icc β h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [flatness_deriv_gtFunctional_zero_eq_g_sub β h s v hβ hh hs
      ⟨hv.1, hv.2.le.trans hq.2⟩]
    exact hlower v hv
  · rw [flatness_deriv_gtFunctional_zero_eq_g_sub β h s (rsQ β h) hβ hh hs
      (rsQ_mem_Icc β h)]
    exact hzero
  · intro v hv
    rw [flatness_deriv_gtFunctional_zero_eq_g_sub β h s v hβ hh hs
      ⟨hq.1.trans hv.1.le, hv.2⟩]
    exact hupper v hv

/-!
### The AT estimate after Price's identity
-/

/--
The Cauchy--Schwarz part of the Price-theorem estimate for `tilde g`.

The hypotheses `hY₁` and `hY₂` say that the two fourth-sech moments
have the RS marginal law. In the application these follow from the fact
that both coordinates of the Gaussian pair have law
`N (h, β^2 q)`.
-/

private lemma flatness_mul_sech_sq_le_average_sech_fourth
    (x y : ℝ) :
    (Real.cosh x)⁻¹ ^ 2 * (Real.cosh y)⁻¹ ^ 2
      ≤
    ((Real.cosh x)⁻¹ ^ 4 + (Real.cosh y)⁻¹ ^ 4) / 2 := by
  have hx : 0 ≤ (Real.cosh x)⁻¹ ^ 2 := sq_nonneg _
  have hy : 0 ≤ (Real.cosh y)⁻¹ ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg
    ((Real.cosh x)⁻¹ ^ 2 - (Real.cosh y)⁻¹ ^ 2)]

/--
The derivative expression appearing in Price's theorem for `tilde g`.
`Y₁` and `Y₂` are parametrizations of the two coordinates of the
Gaussian pair by an auxiliary probability space.
-/
noncomputable def flatnessTildeGPriceTerm
    (β s : ℝ) (Y₁ Y₂ : ℝ → ℝ) : ℝ :=
  s * β ^ 2 *
    standardGaussianExpectation (fun z =>
      (Real.cosh (Y₁ z))⁻¹ ^ 2 *
      (Real.cosh (Y₂ z))⁻¹ ^ 2)

lemma flatness_tildeGPriceTerm_le_pathAT
    (β h s : ℝ) (Y₁ Y₂ : ℝ → ℝ)
    (hβ : 0 < β) (hh : 0 < h) (hs : 0 ≤ s)
    (hInt₁ :
      Integrable
        (fun z =>
          (Real.cosh (Y₁ z))⁻¹ ^ 4)
        (gaussianReal 0 1))
    (hInt₂ :
      Integrable
        (fun z =>
          (Real.cosh (Y₂ z))⁻¹ ^ 4)
        (gaussianReal 0 1))
    (hY₁ :
      standardGaussianExpectation (fun z =>
        (Real.cosh (Y₁ z))⁻¹ ^ 4)
        =
      standardGaussianExpectation (fun z =>
        (Real.cosh
          (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4))
    (hY₂ :
      standardGaussianExpectation (fun z =>
        (Real.cosh (Y₂ z))⁻¹ ^ 4)
        =
      standardGaussianExpectation (fun z =>
        (Real.cosh
          (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4)) :
    flatnessTildeGPriceTerm β s Y₁ Y₂
      ≤ s * atParameter β h := by

  let A : ℝ :=
    standardGaussianExpectation (fun z =>
      (Real.cosh
        (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4)

  have hprod :
      standardGaussianExpectation (fun z =>
          (Real.cosh (Y₁ z))⁻¹ ^ 2 *
          (Real.cosh (Y₂ z))⁻¹ ^ 2)
        ≤ A := by
    unfold standardGaussianExpectation
    have haverageInt : Integrable
        (fun z =>
          ((Real.cosh (Y₁ z))⁻¹ ^ 4 +
            (Real.cosh (Y₂ z))⁻¹ ^ 4) / 2)
        (gaussianReal 0 1) :=
      hInt₁.add hInt₂ |>.div_const 2
    have hsqMeas₁ : AEStronglyMeasurable
        (fun z => (Real.cosh (Y₁ z))⁻¹ ^ 2)
        (gaussianReal 0 1) := by
      convert Real.continuous_sqrt.comp_aestronglyMeasurable
        hInt₁.aestronglyMeasurable using 1
      funext z
      rw [show (Real.cosh (Y₁ z))⁻¹ ^ 4 =
          ((Real.cosh (Y₁ z))⁻¹ ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsqMeas₂ : AEStronglyMeasurable
        (fun z => (Real.cosh (Y₂ z))⁻¹ ^ 2)
        (gaussianReal 0 1) := by
      convert Real.continuous_sqrt.comp_aestronglyMeasurable
        hInt₂.aestronglyMeasurable using 1
      funext z
      rw [show (Real.cosh (Y₂ z))⁻¹ ^ 4 =
          ((Real.cosh (Y₂ z))⁻¹ ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hprodInt : Integrable
        (fun z =>
          (Real.cosh (Y₁ z))⁻¹ ^ 2 *
          (Real.cosh (Y₂ z))⁻¹ ^ 2)
        (gaussianReal 0 1) := by
      apply haverageInt.mono'
      · exact hsqMeas₁.mul hsqMeas₂
      · filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact flatness_mul_sech_sq_le_average_sech_fourth
          (Y₁ z) (Y₂ z)
    calc
      (∫ z,
          (Real.cosh (Y₁ z))⁻¹ ^ 2 *
          (Real.cosh (Y₂ z))⁻¹ ^ 2
          ∂gaussianReal 0 1)
          ≤
        ∫ z,
          ((Real.cosh (Y₁ z))⁻¹ ^ 4 +
            (Real.cosh (Y₂ z))⁻¹ ^ 4) / 2
          ∂gaussianReal 0 1 := by
            apply integral_mono
            · exact hprodInt
            · exact haverageInt
            · intro z
              exact flatness_mul_sech_sq_le_average_sech_fourth
                (Y₁ z) (Y₂ z)

      _ =
        ((∫ z, (Real.cosh (Y₁ z))⁻¹ ^ 4
              ∂gaussianReal 0 1) +
          (∫ z, (Real.cosh (Y₂ z))⁻¹ ^ 4
              ∂gaussianReal 0 1)) / 2 := by
            rw [integral_div]
            rw [integral_add hInt₁ hInt₂]

      _ = A := by
        change
          (standardGaussianExpectation (fun z =>
              (Real.cosh (Y₁ z))⁻¹ ^ 4) +
           standardGaussianExpectation (fun z =>
              (Real.cosh (Y₂ z))⁻¹ ^ 4)) / 2 = A
        rw [hY₁, hY₂]
        simp [A]

  unfold flatnessTildeGPriceTerm
  rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]

  simpa only [mul_assoc, A] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod (sq_nonneg β)) hs)

/-- For fixed model parameters and overlap, the GT functional is convex in
its Lagrange multiplier. -/
lemma convexOn_gtFunctional_lam (β h q s v : ℝ) :
    ConvexOn ℝ Set.univ (fun lam => gtFunctional β h q s lam v) := by
  apply convexOn_univ_of_deriv2_nonneg
  · intro lam
    exact (hasDerivAt_gtFunctional β h q s lam v).differentiableAt
  · exact differentiable_deriv_gtFunctional β h q s v
  · intro lam
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (gt_lambda_derivative_bounds β h q s lam v 0 0 0).2.1

/-- The second derivative of the GT functional in its multiplier is globally
bounded above on the admissible overlap interval. -/
lemma flatness_second_deriv_gtFunctional_le
    {β h q s v lam : ℝ}
    (_hv : v ∈ Icc (-1 : ℝ) 1) :
    deriv
      (fun l =>
        deriv (fun l' => gtFunctional β h q s l' v) l)
      lam ≤ 5 / 2 := by
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    (gt_lambda_derivative_bounds β h q s lam v 0 0 0).2.2

/-!
## Continuity of the GT functional
-/

/-- For fixed model parameters and overlap, the GT functional is continuous
in its Lagrange multiplier. -/
lemma continuous_gtFunctional_lam (β h q s v : ℝ) :
    Continuous (fun lam : ℝ => gtFunctional β h q s lam v) := by
  rw [continuous_iff_continuousAt]
  intro lam
  exact (hasDerivAt_gtFunctional β h q s lam v).continuousAt

/-- The compact parameter set carried by `UniformATData` lies in the strict
AT region. -/
lemma UniformATData.subset_strictATRegion {K : Set (ℝ × ℝ)}
    (data : UniformATData K) : K ⊆ strictATRegion := by
  intro p hp
  refine ⟨data.β_pos p hp, data.h_pos p hp, ?_⟩
  have hAT := data.strictAT p hp
  linarith [data.gap_pos]

/-- Joint continuity of the canonical GT functional on
`K × [0,1] × [-1,1] × [-1,1]`, with the last coordinate representing
the multiplier restricted to the compact interval used in the flatness
argument. -/
lemma continuousOn_gtFunctional_uniformATData {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) =>
      gtFunctional w.1.1 w.1.2 (rsQ w.1.1 w.1.2)
        w.2.1 w.2.2.2 w.2.2.1)
      (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))) := by
  exact continuousOn_gtFunctional K data.subset_strictATRegion

/-!
## Elementary facts about the GT envelope
-/

/--
The infimum defining `gtEnvelope` is bounded above by every value of
`gtFunctional`, provided the range is bounded below.
-/
lemma gtEnvelope_le_functional
    (β h q s v lam : ℝ)
    (hbdd :
      BddBelow
        (Set.range (fun l : ℝ =>
          gtFunctional β h q s l v))) :
    gtEnvelope β h q s v ≤
      gtFunctional β h q s lam v := by
  rw [gtEnvelope]
  exact csInf_le hbdd ⟨lam, rfl⟩


/--
If `lam₀` is a global minimizer of the GT functional, then the GT envelope
equals the value at `lam₀`.
-/
lemma gtEnvelope_eq_functional_of_global_min
    (β h q s v lam₀ : ℝ)
    (hbdd :
      BddBelow
        (Set.range (fun l : ℝ =>
          gtFunctional β h q s l v)))
    (hmin :
      ∀ lam : ℝ,
        gtFunctional β h q s lam₀ v ≤
          gtFunctional β h q s lam v) :
    gtEnvelope β h q s v =
      gtFunctional β h q s lam₀ v := by
  apply le_antisymm

  · exact
      gtEnvelope_le_functional
        β h q s v lam₀ hbdd

  · rw [gtEnvelope]
    refine le_csInf (Set.range_nonempty _) ?_
    intro y hy
    rcases hy with ⟨lam, rfl⟩
    exact hmin lam




/-!
## Equality at the replica-symmetric overlap
-/


/-!
## Final theorem
-/

/-- Uniform linear separation of the multiplier derivative from zero near the
replica-symmetric overlap.  Shrinking the neighborhood by `qmin / 2` ensures
that it lies in the nonnegative-overlap branch. -/
lemma flatness_local_deriv_linear_separation
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ {β h s v : ℝ},
        (β, h) ∈ K →
        s ∈ Icc (0 : ℝ) 1 →
        v ∈ Icc (-1 : ℝ) 1 →
        |v - rsQ β h| ≤ ε →
        c * |v - rsQ β h| ≤
          |deriv
            (fun lam =>
              gtFunctional β h (rsQ β h) s lam v) 0| := by
  obtain ⟨c, ε, hc, hε, hsep⟩ :=
    scalarOrderParameterCorrect_linear_separation data

  let ε₀ : ℝ := min ε (data.qmin / 2)

  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    apply lt_min
    · exact hε
    · linarith [data.qmin_pos]

  refine ⟨c, ε₀, hc, hε₀, ?_⟩

  intro β h s v hp hs hv hnear

  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp

  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp

  have hqmin : data.qmin ≤ rsQ β h := by
    simpa using data.q_lower (β, h) hp

  have hnear_qmin :
      |v - rsQ β h| ≤ data.qmin / 2 := by
    exact hnear.trans (min_le_right _ _)

  have hlo :
      -(data.qmin / 2) ≤ v - rsQ β h :=
    (abs_le.mp hnear_qmin).1

  have hv0 : 0 ≤ v := by
    nlinarith [data.qmin_pos]

  have hv01 : v ∈ Icc (0 : ℝ) 1 :=
    ⟨hv0, hv.2⟩

  rw [flatness_deriv_gtFunctional_zero_eq_g_sub
    β h s v hβ hh hs hv01]

  exact hsep hp hs hv01
    (hnear.trans (min_le_left _ _))

/-- Global second-order Taylor upper bound in the multiplier. -/
lemma flatness_gtFunctional_taylor_upper
    (β h q s v lam : ℝ) :
    gtFunctional β h q s lam v
      ≤
    gtFunctional β h q s 0 v
      + deriv (fun l => gtFunctional β h q s l v) 0 * lam
      + (5 / 4 : ℝ) * lam ^ 2 := by
  let F : ℝ → ℝ :=
    fun l => gtFunctional β h q s l v

  let G : ℝ → ℝ :=
    fun l => F l - (5 / 4 : ℝ) * l ^ 2

  have hFdiff : Differentiable ℝ F := by
    intro x
    dsimp [F]
    exact
      (hasDerivAt_gtFunctional β h q s x v).differentiableAt

  have hGdiff : Differentiable ℝ G := by
    intro x
    dsimp [G]
    exact
      (hFdiff x).sub
        (by fun_prop)

  have hGderiv (x : ℝ) :
      deriv G x =
        deriv F x - (5 / 2 : ℝ) * x := by
    have hF :
        HasDerivAt F (deriv F x) x :=
      (hFdiff x).hasDerivAt

    have hquad :
        HasDerivAt
          (fun y : ℝ => (5 / 4 : ℝ) * y ^ 2)
          ((5 / 2 : ℝ) * x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      exact (hsq.const_mul (5 / 4 : ℝ)).congr_deriv (by ring)

    exact (hF.sub hquad).deriv

  have hFderivDiff :
      Differentiable ℝ (deriv F) := by
    simpa [F] using
      differentiable_deriv_gtFunctional β h q s v

  have hGderivDiff :
      Differentiable ℝ (deriv G) := by
    have hfun :
        deriv G =
          fun x => deriv F x - (5 / 2 : ℝ) * x := by
      funext x
      exact hGderiv x

    rw [hfun]
    exact hFderivDiff.sub (by fun_prop)

  have hGsecond (x : ℝ) :
      deriv (deriv G) x ≤ 0 := by
    have hfun :
        deriv G =
          fun y => deriv F y - (5 / 2 : ℝ) * y := by
      funext y
      exact hGderiv y

    have hD :
        HasDerivAt
          (deriv F)
          (deriv (deriv F) x) x :=
      (hFderivDiff x).hasDerivAt

    have hlin :
        HasDerivAt
          (fun y : ℝ => (5 / 2 : ℝ) * y)
          (5 / 2 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (5 / 2 : ℝ)

    have heq :
        deriv (deriv G) x =
          deriv (deriv F) x - (5 / 2 : ℝ) := by
      rw [hfun]
      exact (hD.sub hlin).deriv

    rw [heq]

    have hbound :=
      (gt_lambda_derivative_bounds
        β h q s x v 0 0 0).2.2

    change
      deriv (deriv F) x ≤ (5 / 2 : ℝ)
      at hbound

    linarith

  have hconc :
      ConcaveOn ℝ Set.univ G := by
    apply concaveOn_univ_of_deriv2_nonpos
    · exact hGdiff
    · exact hGderivDiff
    · intro x
      simpa only
        [Function.iterate_succ_apply,
         Function.iterate_zero_apply]
        using hGsecond x

  have hGzero :
      HasDerivAt G (deriv F 0) 0 := by
    have hz : deriv G 0 = deriv F 0 := by
      simpa using hGderiv 0
    rw [← hz]
    exact (hGdiff 0).hasDerivAt

  by_cases hlam0 : lam = 0
  · subst lam
    simp

  by_cases hlam : 0 < lam
  · have hslope :=
      hconc.slope_le_of_hasDerivAt
        (Set.mem_univ 0)
        (Set.mem_univ lam)
        hlam
        hGzero

    rw [slope_def_field] at hslope
    simp only [sub_zero] at hslope

    have hmul :=
      (div_le_iff₀ hlam).mp hslope

    dsimp [G, F] at hmul ⊢
    nlinarith

  · have hlamle : lam ≤ 0 :=
      le_of_not_gt hlam

    have hlamneg : lam < 0 :=
      lt_of_le_of_ne hlamle hlam0

    have hslope :=
      hconc.le_slope_of_hasDerivAt
        (Set.mem_univ lam)
        (Set.mem_univ 0)
        hlamneg
        hGzero

    rw [slope_def_field] at hslope

    have hden : 0 < 0 - lam := by
      linarith

    have hmul :=
      (le_div_iff₀ hden).mp hslope

    dsimp [G, F] at hmul ⊢
    nlinarith

/-- The squared distance between any two admissible overlaps is at most four. -/
lemma sub_sq_le_four_of_overlap
    {q v : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    (v - q) ^ 2 ≤ 4 := by
  have hleft : -2 ≤ v - q := by
    linarith [hv.1, hq.2]

  have hright : v - q ≤ 2 := by
    linarith [hv.2, hq.1]

  have hprod :
      0 ≤ ((v - q) + 2) * (2 - (v - q)) := by
    exact mul_nonneg
      (by linarith)
      (by linarith)
  nlinarith




abbrev FlatnessPair := Fin 2

def flatnessTanhPair (h : ℝ) : EuclideanSpace ℝ FlatnessPair → ℝ :=
  fun x => Real.tanh (h + x 0) * Real.tanh (h + x 1)

private lemma flatness_tanhPair_contDiff (h : ℝ) : ContDiff ℝ 2 (flatnessTanhPair h) := by
  unfold flatnessTanhPair
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  apply ((Real.contDiff_sinh.comp (by fun_prop)).div
    (Real.contDiff_cosh.comp (by fun_prop)) (fun x => (Real.cosh_pos _).ne')).mul
  exact (Real.contDiff_sinh.comp (by fun_prop)).div
    (Real.contDiff_cosh.comp (by fun_prop)) (fun x => (Real.cosh_pos _).ne')

private lemma flatness_tanhPair_fderiv (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    fderiv ℝ (flatnessTanhPair h) x =
      Real.tanh (h + x 1) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 0) •
            EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) +
        Real.tanh (h + x 0) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 1) •
            EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) := by
  have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)).hasFDerivAt.const_add h
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)).hasFDerivAt.const_add h
  have ht0 := (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 0)).hasFDerivAt.comp x h0
  have ht1 := (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 1)).hasFDerivAt.comp x h1
  have hp := ht0.mul ht1
  change fderiv ℝ ((Real.tanh ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 0) *
    (Real.tanh ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)) x = _
  rw [hp.fderiv]
  ext y
  simp
  ring

private lemma flatness_abs_sechSq_le_one (x : ℝ) :
    |ProbabilityTheory.PriceTanh.sechSq x| ≤ 1 := by
  rw [ProbabilityTheory.PriceTanh.sechSq,
    abs_of_nonneg (sub_nonneg.mpr (Real.tanh_sq_lt_one x).le)]
  nlinarith [sq_nonneg (Real.tanh x)]

private lemma flatness_proj_norm_le_one (i : FlatnessPair) :
    ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => by
    change |y i| ≤ 1 * ‖y‖
    rw [← ProbabilityTheory.inner_euclidBasis]
    simpa [ProbabilityTheory.norm_euclidBasis] using
      (abs_real_inner_le_norm (ProbabilityTheory.euclidBasis (n := FlatnessPair) i) y)

private lemma flatness_sechSq_hasDerivAt (x : ℝ) :
    HasDerivAt ProbabilityTheory.PriceTanh.sechSq
      (-2 * Real.tanh x * ProbabilityTheory.PriceTanh.sechSq x) x := by
  change HasDerivAt (fun y => 1 - Real.tanh y ^ 2)
    (-2 * Real.tanh x * (1 - Real.tanh x ^ 2)) x
  have hd0 := (hasDerivAt_const x (1 : ℝ)).sub
    ((ProbabilityTheory.PriceTanh.tanh_hasDerivAt x).pow 2)
  have hfun : (fun y : ℝ => 1 - Real.tanh y ^ 2) =
      (fun _ : ℝ => 1) - Real.tanh ^ 2 := by
    funext y
    rfl
  rw [hfun]
  exact hd0.congr_deriv (by
    simp [ProbabilityTheory.PriceTanh.sechSq])

private noncomputable def flatnessCoeff0 (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) : ℝ :=
  Real.tanh (h + x 1) * ProbabilityTheory.PriceTanh.sechSq (h + x 0)

private noncomputable def flatnessCoeff1 (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) : ℝ :=
  Real.tanh (h + x 0) * ProbabilityTheory.PriceTanh.sechSq (h + x 1)

private lemma flatness_coeff0_fderiv_bound (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    ‖fderiv ℝ (flatnessCoeff0 h) x‖ ≤ 3 := by
  have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)).hasFDerivAt.const_add h
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)).hasFDerivAt.const_add h
  have ht := (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 1)).hasFDerivAt.comp x h1
  have hs := (flatness_sechSq_hasDerivAt (h + x 0)).hasFDerivAt.comp x h0
  have hp := ht.mul hs
  change ‖fderiv ℝ ((Real.tanh ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 1) *
    (ProbabilityTheory.PriceTanh.sechSq ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)) x‖ ≤ 3
  rw [hp.fderiv]
  have heq :
      (Real.tanh (h + x 1) •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (-2 * Real.tanh (h + x 0) * ProbabilityTheory.PriceTanh.sechSq (h + x 0))).comp
              (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) +
        ProbabilityTheory.PriceTanh.sechSq (h + x 0) •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (ProbabilityTheory.PriceTanh.sechSq (h + x 1))).comp
              (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair))) =
      (Real.tanh (h + x 1) • ((-2 * Real.tanh (h + x 0) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 0)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) +
        ProbabilityTheory.PriceTanh.sechSq (h + x 0) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair))) := by
    ext y
    simp
    ring
  simp only [Function.comp_apply]
  rw [heq]
  calc
    _ ≤ ‖Real.tanh (h + x 1) • ((-2 * Real.tanh (h + x 0) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 0)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair))‖ +
        ‖ProbabilityTheory.PriceTanh.sechSq (h + x 0) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair))‖ := norm_add_le _ _
    _ ≤ 2 + 1 := by
      apply add_le_add
      · simp only [norm_smul, Real.norm_eq_abs, abs_mul]
        have ht1 := (Real.abs_tanh_lt_one (h + x 1)).le
        have ht0 := (Real.abs_tanh_lt_one (h + x 0)).le
        have hs0 := flatness_abs_sechSq_le_one (h + x 0)
        have hp0 := flatness_proj_norm_le_one (0 : FlatnessPair)
        have hBCD : |Real.tanh (h + x 0)| *
            |ProbabilityTheory.PriceTanh.sechSq (h + x 0)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖ ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ ht0 (abs_nonneg _) hs0) (norm_nonneg _) hp0
        have hABCD : |Real.tanh (h + x 1)| *
            (|Real.tanh (h + x 0)| *
              |ProbabilityTheory.PriceTanh.sechSq (h + x 0)| *
                ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖) ≤ 1 :=
          mul_le_one₀ ht1 (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)) hBCD
        rw [show |(-2 : ℝ)| = 2 by norm_num]
        calc
          _ = 2 * (|Real.tanh (h + x 1)| *
            (|Real.tanh (h + x 0)| * |ProbabilityTheory.PriceTanh.sechSq (h + x 0)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖)) := by ring
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hABCD (by norm_num)
          _ = 2 := by norm_num
      · simp only [norm_smul, Real.norm_eq_abs]
        have hs0 := flatness_abs_sechSq_le_one (h + x 0)
        have hs1 := flatness_abs_sechSq_le_one (h + x 1)
        have hp1 := flatness_proj_norm_le_one (1 : FlatnessPair)
        have hBC := mul_le_one₀ hs1 (norm_nonneg _) hp1
        exact mul_le_one₀ hs0 (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hBC
    _ = 3 := by norm_num

private lemma flatness_coeff1_fderiv_bound (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    ‖fderiv ℝ (flatnessCoeff1 h) x‖ ≤ 3 := by
  -- The proof is the coordinate-swapped copy of `flatness_coeff0_fderiv_bound`.
  unfold flatnessCoeff1
  have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)).hasFDerivAt.const_add h
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)).hasFDerivAt.const_add h
  have ht := (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 0)).hasFDerivAt.comp x h0
  have hs := (flatness_sechSq_hasDerivAt (h + x 1)).hasFDerivAt.comp x h1
  have hp := ht.mul hs
  change ‖fderiv ℝ ((Real.tanh ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 0) *
    (ProbabilityTheory.PriceTanh.sechSq ∘ fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)) x‖ ≤ 3
  rw [hp.fderiv]
  have heq :
      (Real.tanh (h + x 0) •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (-2 * Real.tanh (h + x 1) * ProbabilityTheory.PriceTanh.sechSq (h + x 1))).comp
              (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) +
        ProbabilityTheory.PriceTanh.sechSq (h + x 1) •
          (ContinuousLinearMap.toSpanSingleton ℝ
            (ProbabilityTheory.PriceTanh.sechSq (h + x 0))).comp
              (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair))) =
      (Real.tanh (h + x 0) • ((-2 * Real.tanh (h + x 1) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 1)) • EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) +
        ProbabilityTheory.PriceTanh.sechSq (h + x 1) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair))) := by
    ext y
    simp
    ring
  simp only [Function.comp_apply]
  rw [heq]
  calc
    _ ≤ ‖Real.tanh (h + x 0) • ((-2 * Real.tanh (h + x 1) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 1)) • EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair))‖ +
        ‖ProbabilityTheory.PriceTanh.sechSq (h + x 1) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair))‖ := norm_add_le _ _
    _ ≤ 2 + 1 := by
      apply add_le_add
      · simp only [norm_smul, Real.norm_eq_abs, abs_mul]
        have ht0 := (Real.abs_tanh_lt_one (h + x 0)).le
        have ht1 := (Real.abs_tanh_lt_one (h + x 1)).le
        have hs1 := flatness_abs_sechSq_le_one (h + x 1)
        have hp1 := flatness_proj_norm_le_one (1 : FlatnessPair)
        have hBCD : |Real.tanh (h + x 1)| *
            |ProbabilityTheory.PriceTanh.sechSq (h + x 1)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖ ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ ht1 (abs_nonneg _) hs1) (norm_nonneg _) hp1
        have hABCD : |Real.tanh (h + x 0)| *
            (|Real.tanh (h + x 1)| *
              |ProbabilityTheory.PriceTanh.sechSq (h + x 1)| *
                ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖) ≤ 1 :=
          mul_le_one₀ ht0 (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)) hBCD
        rw [show |(-2 : ℝ)| = 2 by norm_num]
        calc
          _ = 2 * (|Real.tanh (h + x 0)| *
            (|Real.tanh (h + x 1)| * |ProbabilityTheory.PriceTanh.sechSq (h + x 1)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖)) := by ring
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hABCD (by norm_num)
          _ = 2 := by norm_num
      · simp only [norm_smul, Real.norm_eq_abs]
        have hs1 := flatness_abs_sechSq_le_one (h + x 1)
        have hs0 := flatness_abs_sechSq_le_one (h + x 0)
        have hp0 := flatness_proj_norm_le_one (0 : FlatnessPair)
        have hBC := mul_le_one₀ hs0 (norm_nonneg _) hp0
        exact mul_le_one₀ hs1 (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hBC
    _ = 3 := by norm_num

private lemma flatness_tanhPair_fderiv_coeff (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    fderiv ℝ (flatnessTanhPair h) x =
      flatnessCoeff0 h x • EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair) +
        flatnessCoeff1 h x • EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair) := by
  rw [flatness_tanhPair_fderiv]
  ext y
  simp [flatnessCoeff0, flatnessCoeff1]
  ring

private lemma flatness_tanhPair_hess_bound (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    ‖PriceFourier.hess (flatnessTanhPair h) x‖ ≤ 6 := by
  have hc0diff : DifferentiableAt ℝ (flatnessCoeff0 h) x := by
    unfold flatnessCoeff0
    have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) x := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)).hasFDerivAt.const_add h
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) x := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)).hasFDerivAt.const_add h
    exact ((ProbabilityTheory.PriceTanh.tanh_hasDerivAt _).hasFDerivAt.comp x h1).differentiableAt.mul
      ((flatness_sechSq_hasDerivAt _).hasFDerivAt.comp x h0).differentiableAt
  have hc1diff : DifferentiableAt ℝ (flatnessCoeff1 h) x := by
    unfold flatnessCoeff1
    have h0 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 0)
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)) x := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)).hasFDerivAt.const_add h
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ FlatnessPair => h + y 1)
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)) x := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)).hasFDerivAt.const_add h
    exact ((ProbabilityTheory.PriceTanh.tanh_hasDerivAt _).hasFDerivAt.comp x h0).differentiableAt.mul
      ((flatness_sechSq_hasDerivAt _).hasFDerivAt.comp x h1).differentiableAt
  let L0 := EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)
  let L1 := EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)
  have hd0 := hc0diff.hasFDerivAt.smul_const L0
  have hd1 := hc1diff.hasFDerivAt.smul_const L1
  have hd := hd0.add hd1
  have hfun : fderiv ℝ (flatnessTanhPair h) = fun y => flatnessCoeff0 h y • L0 + flatnessCoeff1 h y • L1 := by
    funext y
    exact flatness_tanhPair_fderiv_coeff h y
  rw [PriceFourier.hess, hfun]
  change ‖fderiv ℝ ((fun y => flatnessCoeff0 h y • L0) +
    (fun y => flatnessCoeff1 h y • L1)) x‖ ≤ 6
  rw [hd.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  simp only [add_apply]
  calc
    ‖(fderiv ℝ (flatnessCoeff0 h) x y) • L0 + (fderiv ℝ (flatnessCoeff1 h) x y) • L1‖ ≤
        ‖(fderiv ℝ (flatnessCoeff0 h) x y) • L0‖ + ‖(fderiv ℝ (flatnessCoeff1 h) x y) • L1‖ := norm_add_le _ _
    _ ≤ (3 * ‖y‖) * 1 + (3 * ‖y‖) * 1 := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul
        · exact (ContinuousLinearMap.le_opNorm _ y).trans
            (mul_le_mul_of_nonneg_right (flatness_coeff0_fderiv_bound h x) (norm_nonneg y))
        · exact flatness_proj_norm_le_one _
        · exact norm_nonneg _
        · positivity
      · rw [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul
        · exact (ContinuousLinearMap.le_opNorm _ y).trans
            (mul_le_mul_of_nonneg_right (flatness_coeff1_fderiv_bound h x) (norm_nonneg y))
        · exact flatness_proj_norm_le_one _
        · exact norm_nonneg _
        · positivity
    _ = 6 * ‖y‖ := by ring

private lemma flatness_tanhPair_hess_mixed_zero_one (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    (PriceFourier.hess (flatnessTanhPair h) x)
      (ProbabilityTheory.euclidBasis (n := FlatnessPair) 0)
      (ProbabilityTheory.euclidBasis (n := FlatnessPair) 1) =
        ProbabilityTheory.PriceTanh.sechSq (h + x 0) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 1) := by
  let e0 := ProbabilityTheory.euclidBasis (n := FlatnessPair) (0 : FlatnessPair)
  let e1 := ProbabilityTheory.euclidBasis (n := FlatnessPair) (1 : FlatnessPair)
  have hline : HasDerivAt (fun t : ℝ => x + t • e0) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).const_add x
  have hh0 := PriceFourier.hasFDerivAt_fderiv_apply (flatness_tanhPair_contDiff h) e1 (x + (0 : ℝ) • e0)
  have hh := hh0.comp_hasDerivAt 0 hline
  have hfun : (fun t : ℝ => fderiv ℝ (flatnessTanhPair h) (x + t • e0) e1) =
      fun t => Real.tanh (h + x 0 + t) *
        ProbabilityTheory.PriceTanh.sechSq (h + x 1) := by
    funext t
    rw [flatness_tanhPair_fderiv_coeff]
    simp [flatnessCoeff0, flatnessCoeff1, e0, e1, ProbabilityTheory.euclidBasis]
    left
    congr 1
    ring
  change HasDerivAt (fun t : ℝ => fderiv ℝ (flatnessTanhPair h) (x + t • e0) e1) _ 0 at hh
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] at hh
  rw [hfun] at hh
  have hd := ((ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 0 + 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add (h + x 0))).mul_const
      (ProbabilityTheory.PriceTanh.sechSq (h + x 1))
  have heq := hh.unique hd
  simpa [e0, e1, PriceFourier.hess] using heq

private lemma flatness_tanhPair_hess_mixed_one_zero (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    (PriceFourier.hess (flatnessTanhPair h) x)
      (ProbabilityTheory.euclidBasis (n := FlatnessPair) 1)
      (ProbabilityTheory.euclidBasis (n := FlatnessPair) 0) =
        ProbabilityTheory.PriceTanh.sechSq (h + x 0) *
          ProbabilityTheory.PriceTanh.sechSq (h + x 1) := by
  let e0 := ProbabilityTheory.euclidBasis (n := FlatnessPair) (0 : FlatnessPair)
  let e1 := ProbabilityTheory.euclidBasis (n := FlatnessPair) (1 : FlatnessPair)
  have hline : HasDerivAt (fun t : ℝ => x + t • e1) e1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e1).const_add x
  have hh0 := PriceFourier.hasFDerivAt_fderiv_apply (flatness_tanhPair_contDiff h) e0 (x + (0 : ℝ) • e1)
  have hh := hh0.comp_hasDerivAt 0 hline
  have hfun : (fun t : ℝ => fderiv ℝ (flatnessTanhPair h) (x + t • e1) e0) =
      fun t => ProbabilityTheory.PriceTanh.sechSq (h + x 0) *
        Real.tanh (h + x 1 + t) := by
    funext t
    rw [flatness_tanhPair_fderiv_coeff]
    simp [flatnessCoeff0, flatnessCoeff1, e0, e1, ProbabilityTheory.euclidBasis]
    rw [show h + (x 1 + t) = h + x 1 + t by ring]
    ring
  change HasDerivAt (fun t : ℝ => fderiv ℝ (flatnessTanhPair h) (x + t • e1) e0) _ 0 at hh
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] at hh
  rw [hfun] at hh
  have hd := ((ProbabilityTheory.PriceTanh.tanh_hasDerivAt (h + x 1 + 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add (h + x 1))).const_mul
      (ProbabilityTheory.PriceTanh.sechSq (h + x 0))
  have heq := hh.unique hd
  simpa [e0, e1, PriceFourier.hess] using heq

private lemma flatness_tanhPair_fderiv_bound (h : ℝ) (x : EuclideanSpace ℝ FlatnessPair) :
    ‖fderiv ℝ (flatnessTanhPair h) x‖ ≤ 2 := by
  rw [flatness_tanhPair_fderiv]
  calc
    _ ≤ ‖Real.tanh (h + x 1) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 0) •
            EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair))‖ +
        ‖Real.tanh (h + x 0) •
          (ProbabilityTheory.PriceTanh.sechSq (h + x 1) •
            EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair))‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
      apply add_le_add
      · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hp : ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖ ≤ 1 := by
          exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => by
            change |y 0| ≤ 1 * ‖y‖
            rw [← ProbabilityTheory.inner_euclidBasis]
            simpa [ProbabilityTheory.norm_euclidBasis] using
              (abs_real_inner_le_norm (ProbabilityTheory.euclidBasis (n := FlatnessPair) 0) y)
        calc
          _ ≤ 1 * (|ProbabilityTheory.PriceTanh.sechSq (h + x 0)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖) :=
            mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one _).le (mul_nonneg (abs_nonneg _) (norm_nonneg _))
          _ ≤ 1 * (1 * ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : FlatnessPair)‖) := by gcongr; exact flatness_abs_sechSq_le_one _
          _ ≤ 1 * (1 * 1) := by gcongr
          _ = 1 := by norm_num
      · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hp : ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖ ≤ 1 := by
          exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => by
            change |y 1| ≤ 1 * ‖y‖
            rw [← ProbabilityTheory.inner_euclidBasis]
            simpa [ProbabilityTheory.norm_euclidBasis] using
              (abs_real_inner_le_norm (ProbabilityTheory.euclidBasis (n := FlatnessPair) 1) y)
        calc
          _ ≤ 1 * (|ProbabilityTheory.PriceTanh.sechSq (h + x 1)| *
              ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖) :=
            mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one _).le (mul_nonneg (abs_nonneg _) (norm_nonneg _))
          _ ≤ 1 * (1 * ‖EuclideanSpace.proj (𝕜 := ℝ) (1 : FlatnessPair)‖) := by gcongr; exact flatness_abs_sechSq_le_one _
          _ ≤ 1 * (1 * 1) := by gcongr
          _ = 1 := by norm_num
    _ = 2 := by norm_num

private lemma flatness_stdGaussian_fin_two_eq_map_prod :
    ProbabilityTheory.PriceGaussian.stdGaussian FlatnessPair =
      (gaussianReal 0 1 |>.prod <| gaussianReal 0 1).map
        (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2]) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let e : (FlatnessPair → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e (Measure.pi fun _ : FlatnessPair => γ) (γ.prod γ) :=
    measurePreserving_finTwoArrow γ
  have hinv : Measure.map e.symm (γ.prod γ) = Measure.pi fun _ : FlatnessPair => γ := by
    rw [← he.map_eq, Measure.map_map e.symm.measurable e.measurable]
    simp
  rw [ProbabilityTheory.PriceGaussian.stdGaussian, ← hinv,
    Measure.map_map (by fun_prop) e.symm.measurable]
  congr 1

noncomputable def flatnessTildeGCov (β q s v : ℝ) : Matrix FlatnessPair FlatnessPair ℝ :=
  fun i j => if i = j then β ^ 2 * q else β ^ 2 * ((1 - s) * q + s * v)

private noncomputable def flatnessPriceMatM (β q s v : ℝ) : Matrix FlatnessPair FlatnessPair ℝ :=
  let c := β * Real.sqrt ((1 - s) * q)
  let a := β * Real.sqrt s * Real.sqrt (-v)
  fun i j => if i = 0 then (if j = 0 then c else a)
    else (if j = 0 then c else -a)

private noncomputable def flatnessPriceMatN (β q s v : ℝ) : Matrix FlatnessPair FlatnessPair ℝ :=
  let b := β * Real.sqrt s * Real.sqrt (q + v)
  fun i j => if i = j then b else 0

private lemma flatness_price_matrices_cov (β q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Ioo (-q) 0) :
    flatnessPriceMatM β q s v * Matrix.transpose (flatnessPriceMatM β q s v) +
      flatnessPriceMatN β q s v * Matrix.transpose (flatnessPriceMatN β q s v) =
        flatnessTildeGCov β q s v := by
  have hq : 0 < q := by linarith [hv.1, hv.2]
  have hc : Real.sqrt (-(s * q) + q) ^ 2 = -(s * q) + q := by
    apply Real.sq_sqrt
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hq.le]
  have hs' : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.1
  have ha : Real.sqrt (-v) ^ 2 = -v := Real.sq_sqrt (by linarith [hv.2])
  have hb : Real.sqrt (q + v) ^ 2 = q + v := Real.sq_sqrt (by linarith [hv.1])
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    simp [flatnessPriceMatM, flatnessPriceMatN, flatnessTildeGCov]
    ring_nf
    simp only [hc, hs', ha, hb]
    ring

private lemma flatness_raw_eq_Gint (β h q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Ioo (-q) 0) :
    (let c := β * Real.sqrt ((1 - s) * q)
     let a := β * Real.sqrt s * Real.sqrt (-v)
     let b := β * Real.sqrt s * Real.sqrt (q + v)
     standardGaussianExpectation (fun z =>
       standardGaussianExpectation (fun z₀ =>
         standardGaussianExpectation (fun z₁ =>
           standardGaussianExpectation (fun z₂ =>
             Real.tanh (h + c*z + a*z₀ + b*z₁) *
             Real.tanh (h + c*z - a*z₀ + b*z₂))))) =
      ProbabilityTheory.Gint (flatnessTanhPair h) (flatnessTildeGCov β q s v)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let M := flatnessPriceMatM β q s v
  let N := flatnessPriceMatN β q s v
  have hobscont : Continuous (flatnessTanhPair h) := (flatness_tanhPair_contDiff h).continuous
  have hbound (x : EuclideanSpace ℝ FlatnessPair) : |flatnessTanhPair h x| ≤ 1 := by
    rw [flatnessTanhPair, abs_mul]
    nlinarith [abs_nonneg (Real.tanh (h + x 0)), abs_nonneg (Real.tanh (h + x 1)),
      (Real.abs_tanh_lt_one (h + x 0)).le, (Real.abs_tanh_lt_one (h + x 1)).le]
  have hint (p : EuclideanSpace ℝ FlatnessPair) : Integrable
      (fun w : EuclideanSpace ℝ FlatnessPair => flatnessTanhPair h
        (ProbabilityTheory.PriceGaussian.matCLM M p +
          ProbabilityTheory.PriceGaussian.matCLM N w))
      (ProbabilityTheory.PriceGaussian.stdGaussian FlatnessPair) := by
    apply Integrable.of_bound (C := 1)
    · exact (hobscont.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with w
      simpa [Real.norm_eq_abs] using hbound _
  have hprodint : Integrable
      (fun p : EuclideanSpace ℝ FlatnessPair × EuclideanSpace ℝ FlatnessPair => flatnessTanhPair h
        (ProbabilityTheory.PriceGaussian.matCLM M p.1 +
          ProbabilityTheory.PriceGaussian.matCLM N p.2))
      ((ProbabilityTheory.PriceGaussian.stdGaussian FlatnessPair).prod
        (ProbabilityTheory.PriceGaussian.stdGaussian FlatnessPair)) := by
    apply Integrable.of_bound (C := 1)
    · exact (hobscont.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hbound _
  rw [← flatness_price_matrices_cov β q s v hs hv]
  unfold ProbabilityTheory.Gint
  rw [← ProbabilityTheory.PriceGaussian.map_add_prod_stdGaussian M N,
    integral_map (by fun_prop) hobscont.aestronglyMeasurable]
  have hprodint' := hprodint
  rw [flatness_stdGaussian_fin_two_eq_map_prod,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at hprodint'
  rw [flatness_stdGaussian_fin_two_eq_map_prod,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [integral_map (by fun_prop) hprodint'.aestronglyMeasurable]
  let F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    flatnessTanhPair h (ProbabilityTheory.PriceGaussian.matCLM M (WithLp.toLp 2 ![p.1.1, p.1.2]) +
      ProbabilityTheory.PriceGaussian.matCLM N (WithLp.toLp 2 ![p.2.1, p.2.2]))
  have hF : Integrable F ((γ.prod γ).prod (γ.prod γ)) := by
    apply Integrable.of_bound (C := 1)
    · exact (hobscont.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [F, Real.norm_eq_abs] using hbound _
  have hFsec (z z₀ : ℝ) : Integrable (fun p : ℝ × ℝ => F ((z, z₀), p))
      (γ.prod γ) := by
    apply Integrable.of_bound (C := 1)
    · exact (hobscont.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [F, Real.norm_eq_abs] using hbound _
  have hgroup :
      (∫ p, F p ∂((γ.prod γ).prod (γ.prod γ))) =
        ∫ z, ∫ z₀, ∫ z₁, ∫ z₂, F ((z, z₀), (z₁, z₂)) ∂γ ∂γ ∂γ ∂γ := by
    calc
      (∫ p, F p ∂((γ.prod γ).prod (γ.prod γ))) =
          ∫ p, ∫ r, F (p, r) ∂(γ.prod γ) ∂(γ.prod γ) := integral_prod _ hF
      _ = ∫ z, ∫ z₀, ∫ r, F ((z, z₀), r) ∂(γ.prod γ) ∂γ ∂γ :=
        integral_prod _ hF.integral_prod_left
      _ = ∫ z, ∫ z₀, ∫ z₁, ∫ z₂, F ((z, z₀), (z₁, z₂)) ∂γ ∂γ ∂γ ∂γ := by
        apply integral_congr_ae
        filter_upwards [] with z
        apply integral_congr_ae
        filter_upwards [] with z₀
        exact integral_prod _ (hFsec z z₀)
  change _ = ∫ p, F p ∂((γ.prod γ).prod (γ.prod γ))
  rw [hgroup]
  simp only [standardGaussianExpectation]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with z₀
  apply integral_congr_ae
  filter_upwards [] with z₁
  apply integral_congr_ae
  filter_upwards [] with z₂
  dsimp [F, flatnessTanhPair]
  simp_rw [ProbabilityTheory.PriceGaussian.matCLM_apply, Fin.sum_univ_two]
  dsimp [M, N, flatnessPriceMatM, flatnessPriceMatN, γ]
  simp
  ring_nf

noncomputable def flatnessTildeGPriceExpectation (β h q s v : ℝ) : ℝ :=
  ProbabilityTheory.Gint
    (fun x : EuclideanSpace ℝ FlatnessPair =>
      ProbabilityTheory.PriceTanh.sechSq (h + x 0) *
        ProbabilityTheory.PriceTanh.sechSq (h + x 1))
    (flatnessTildeGCov β q s v)

private lemma flatness_Gint_hasDerivAt (β h q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (_hq : 0 < q)
    (hv : v ∈ Set.Ioo (-q) 0) :
    HasDerivAt (fun u => ProbabilityTheory.Gint (flatnessTanhPair h) (flatnessTildeGCov β q s u))
      (s * β ^ 2 * flatnessTildeGPriceExpectation β h q s v) v := by
  let U : Set ℝ := Set.Ioo (-q) 0
  let S : ℝ → Matrix FlatnessPair FlatnessPair ℝ := fun u => flatnessTildeGCov β q s u
  let Sdot : Matrix FlatnessPair FlatnessPair ℝ := fun i j => if i = j then 0 else s * β ^ 2
  have hPSD (u : ℝ) (hu : u ∈ U) : (S u).PosSemidef := by
    rw [show S u = flatnessPriceMatM β q s u * Matrix.transpose (flatnessPriceMatM β q s u) +
        flatnessPriceMatN β q s u * Matrix.transpose (flatnessPriceMatN β q s u) by
      symm
      exact flatness_price_matrices_cov β q s u hs hu]
    exact (Matrix.posSemidef_self_mul_conjTranspose (A := flatnessPriceMatM β q s u)).add
      (Matrix.posSemidef_self_mul_conjTranspose (A := flatnessPriceMatN β q s u))
  have htrace (u : ℝ) (hu : u ∈ U) : (S u).trace = (S v).trace := by
    simp [S, flatnessTildeGCov, Matrix.trace]
  have hSd (i j : FlatnessPair) :
      HasDerivWithinAt (fun u => S u i j) (Sdot i j) U v := by
    apply HasDerivAt.hasDerivWithinAt
    by_cases hij : i = j
    · subst j
      simpa [S, Sdot, flatnessTildeGCov] using hasDerivAt_const v (β ^ 2 * q)
    · have hd := (((hasDerivAt_const v ((1 - s) * q)).add
          ((hasDerivAt_id v).const_mul s)).const_mul (β ^ 2))
      simpa [S, Sdot, flatnessTildeGCov, hij, mul_add, mul_comm, mul_left_comm, mul_assoc] using hd
  have hd := ProbabilityTheory.hasDerivWithinAt_Gint
    (M0 := 1) (M1 := 2) (M2 := 6)
    (flatness_tanhPair_contDiff h) (fun x => by
      rw [flatnessTanhPair, abs_mul]
      nlinarith [abs_nonneg (Real.tanh (h + x 0)), abs_nonneg (Real.tanh (h + x 1)),
        (Real.abs_tanh_lt_one (h + x 0)).le, (Real.abs_tanh_lt_one (h + x 1)).le])
    (flatness_tanhPair_fderiv_bound h) (flatness_tanhPair_hess_bound h) hv S Sdot hPSD htrace hSd
  have hd' := hd.hasDerivAt (Ioo_mem_nhds hv.1 hv.2)
  apply hd'.congr_deriv
  simp only [Fin.sum_univ_two]
  simp [Sdot, flatnessTildeGPriceExpectation, S, flatness_tanhPair_hess_mixed_zero_one,
    flatness_tanhPair_hess_mixed_one_zero]
  ring



/-- On the interior negative branch, the four-Gaussian definition of
`flatnessTildeG` is the Gaussian integral with its two-by-two covariance
matrix. -/
lemma flatnessTildeG_eq_Gint_neg
    (β h q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (_hq : 0 < q)
    (hv : v ∈ Set.Ioo (-q) 0) :
    flatnessTildeG β h q s v =
      ProbabilityTheory.Gint
        (flatnessTanhPair h)
        (flatnessTildeGCov β q s v) := by
  simpa [flatnessTildeG, gtIncrementScale, gtPathSign,
    abs_of_neg hv.2, not_le.mpr hv.2, Real.sqrt_mul hs.1,
    sub_eq_add_neg] using flatness_raw_eq_Gint β h q s v hs hv

/-- Price's identity for `flatnessTildeG` on the interior negative branch. -/
lemma flatnessTildeG_hasDerivAt_neg_price
    (β h q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q)
    (hv : v ∈ Set.Ioo (-q) 0) :
    HasDerivAt
      (fun u => flatnessTildeG β h q s u)
      (s * β ^ 2 *
        flatnessTildeGPriceExpectation β h q s v)
      v := by
  have hd := flatness_Gint_hasDerivAt β h q s v hs hq hv
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu
  exact flatnessTildeG_eq_Gint_neg β h q s u hs hq hu

/-- The explicit derivative supplied by Price's identity on negative overlaps. -/
lemma flatnessTildeG_deriv_eq_price_neg
    (β h q s v : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q)
    (hv : v ∈ Set.Ioo (-q) 0) :
    deriv (fun u => flatnessTildeG β h q s u) v =
      s * β ^ 2 *
        flatnessTildeGPriceExpectation β h q s v := by
  exact (flatnessTildeG_hasDerivAt_neg_price β h q s v hs hq hv).deriv

open Matrix in
private lemma flatness_priceGaussian_eq_multivariateGaussian
    {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) :
    ProbabilityTheory.PriceGaussian.multivariateGaussian 0 S =
      ProbabilityTheory.multivariateGaussian 0 S := by
  apply Measure.ext_of_charFun
  ext t
  rw [ProbabilityTheory.PriceGaussian.charFun_multivariateGaussian hS,
    ProbabilityTheory.charFun_multivariateGaussian hS]
  have hreal :
      ⟪t, ProbabilityTheory.PriceGaussian.matCLM S t⟫ =
        t.ofLp ⬝ᵥ S *ᵥ t.ofLp := by
    simp [PiLp.inner_apply, RCLike.inner_apply,
      ProbabilityTheory.PriceGaussian.matCLM_apply, dotProduct, mulVec, mul_comm]
  rw [hreal]
  congr 1
  simp
  ring

private lemma flatness_Gint_coord_eq_gaussianReal
    {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (i : n)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ProbabilityTheory.Gint (fun x : EuclideanSpace ℝ n => f (x i)) S =
      ∫ y, f y ∂gaussianReal 0 (S i i).toNNReal := by
  unfold ProbabilityTheory.Gint
  rw [flatness_priceGaussian_eq_multivariateGaussian hS]
  have hmp := ProbabilityTheory.measurePreserving_eval_multivariateGaussian
    (S := S) (i := i) (hS := hS) (μ := (0 : EuclideanSpace ℝ n))
  have hmap : Measure.map (fun x : EuclideanSpace ℝ n => x i)
      (ProbabilityTheory.multivariateGaussian 0 S) =
        gaussianReal 0 (S i i).toNNReal := by
    simpa using hmp.map_eq
  rw [← hmap, integral_map hmp.measurable.aemeasurable
    hf.aestronglyMeasurable]

private lemma flatness_gaussianReal_beta_sqrt_integral
    {β q : ℝ} (hq : 0 ≤ q) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ y, f y ∂gaussianReal 0 (β ^ 2 * q).toNNReal) =
      ∫ z, f (β * Real.sqrt q * z) ∂gaussianReal 0 1 := by
  have hvar : NNReal.mk ((β * Real.sqrt q) ^ 2) (sq_nonneg _) =
      (β ^ 2 * q).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mk, Real.coe_toNNReal _
      (mul_nonneg (sq_nonneg β) hq)]
    rw [mul_pow, Real.sq_sqrt hq]
  have hmap : Measure.map (fun z : ℝ => β * Real.sqrt q * z)
      (gaussianReal 0 1) = gaussianReal 0 (β ^ 2 * q).toNNReal := by
    simpa [hvar] using
      (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal))
        (β * Real.sqrt q))
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]

private lemma flatness_price_sechSq_eq_cosh (x : ℝ) :
    ProbabilityTheory.PriceTanh.sechSq x = (Real.cosh x)⁻¹ ^ 2 := by
  rw [ProbabilityTheory.PriceTanh.sechSq, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [inv_pow]
  field_simp
  nlinarith [Real.cosh_sq x]

private lemma flatness_price_sechSq_nonneg (x : ℝ) :
    0 ≤ ProbabilityTheory.PriceTanh.sechSq x := by
  rw [flatness_price_sechSq_eq_cosh]
  positivity

/-- On the negative branch, the Price derivative is uniformly below one
by the strict AT gap. -/
lemma flatnessTildeG_deriv_lt_one_neg
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    {β h q s v : ℝ}
    (hp : (β, h) ∈ K)
    (hq : q = rsQ β h)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (-q) 0) :
    deriv (fun u => flatnessTildeG β h q s u) v
      ≤ 1 - data.gap := by
  have hβ : 0 < β := data.β_pos (β, h) hp
  have hh : 0 < h := data.h_pos (β, h) hp
  have hqpos : 0 < q := by
    rw [hq]
    exact rsQ_pos hβ hh
  let S := flatnessTildeGCov β q s v
  have hS : S.PosSemidef := by
    rw [show S =
        flatnessPriceMatM β q s v * Matrix.transpose (flatnessPriceMatM β q s v) +
          flatnessPriceMatN β q s v * Matrix.transpose (flatnessPriceMatN β q s v) by
      dsimp [S]
      symm
      exact flatness_price_matrices_cov β q s v hs hv]
    exact (Matrix.posSemidef_self_mul_conjTranspose
      (A := flatnessPriceMatM β q s v)).add
      (Matrix.posSemidef_self_mul_conjTranspose
        (A := flatnessPriceMatN β q s v))
  let g : ℝ → ℝ := fun y => ProbabilityTheory.PriceTanh.sechSq (h + y) ^ 2
  have htanhcont : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div₀ Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')
  have hgcont : Continuous g := by
    dsimp [g, ProbabilityTheory.PriceTanh.sechSq]
    exact (continuous_const.sub
      ((htanhcont.comp (by fun_prop)).pow 2)).pow 2
  have hcoord (i : FlatnessPair) :
      ProbabilityTheory.Gint
          (fun x : EuclideanSpace ℝ FlatnessPair => g (x i)) S =
        standardGaussianExpectation (fun z =>
          (Real.cosh (h + β * Real.sqrt q * z))⁻¹ ^ 4) := by
    calc
      ProbabilityTheory.Gint
          (fun x : EuclideanSpace ℝ FlatnessPair => g (x i)) S =
          ∫ y, g y ∂gaussianReal 0 (β ^ 2 * q).toNNReal := by
            simpa [S, flatnessTildeGCov] using
              flatness_Gint_coord_eq_gaussianReal hS i g hgcont
      _ = ∫ z, g (β * Real.sqrt q * z) ∂gaussianReal 0 1 :=
        flatness_gaussianReal_beta_sqrt_integral hqpos.le g hgcont
      _ = standardGaussianExpectation (fun z =>
          (Real.cosh (h + β * Real.sqrt q * z))⁻¹ ^ 4) := by
        unfold standardGaussianExpectation
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [g]
        rw [flatness_price_sechSq_eq_cosh]
        ring
  have hprice :
      flatnessTildeGPriceExpectation β h q s v ≤
        standardGaussianExpectation (fun z =>
          (Real.cosh (h + β * Real.sqrt q * z))⁻¹ ^ 4) := by
    let μ : Measure (EuclideanSpace ℝ FlatnessPair) :=
      ProbabilityTheory.PriceGaussian.multivariateGaussian 0 S
    let F : EuclideanSpace ℝ FlatnessPair → ℝ := fun x =>
      ProbabilityTheory.PriceTanh.sechSq (h + x 0) *
        ProbabilityTheory.PriceTanh.sechSq (h + x 1)
    let A : EuclideanSpace ℝ FlatnessPair → ℝ := fun x =>
      (g (x 0) + g (x 1)) / 2
    have hFcont : Continuous F := by
      dsimp [F, ProbabilityTheory.PriceTanh.sechSq]
      exact (continuous_const.sub
        ((htanhcont.comp (by fun_prop)).pow 2)).mul
        (continuous_const.sub
          ((htanhcont.comp (by fun_prop)).pow 2))
    have hAcont : Continuous A := by
      dsimp [A]
      exact ((hgcont.comp (by fun_prop)).add
        (hgcont.comp (by fun_prop))).div_const 2
    have hFint : Integrable F μ := by
      apply Integrable.of_bound (C := 1)
      · exact hFcont.aestronglyMeasurable
      · filter_upwards [] with x
        dsimp [F]
        rw [abs_mul]
        nlinarith [abs_nonneg (ProbabilityTheory.PriceTanh.sechSq (h + x 0)),
          abs_nonneg (ProbabilityTheory.PriceTanh.sechSq (h + x 1)),
          flatness_abs_sechSq_le_one (h + x 0),
          flatness_abs_sechSq_le_one (h + x 1)]
    have hAint : Integrable A μ := by
      apply Integrable.of_bound (C := 1)
      · exact hAcont.aestronglyMeasurable
      · filter_upwards [] with x
        dsimp [A, g]
        have h0 := flatness_abs_sechSq_le_one (h + x 0)
        have h1 := flatness_abs_sechSq_le_one (h + x 1)
        have h0sq : ProbabilityTheory.PriceTanh.sechSq (h + x 0) ^ 2 ≤ 1 := by
          have h0n := flatness_price_sechSq_nonneg (h + x 0)
          rw [abs_of_nonneg h0n] at h0
          nlinarith [mul_nonneg h0n (sub_nonneg.mpr h0)]
        have h1sq : ProbabilityTheory.PriceTanh.sechSq (h + x 1) ^ 2 ≤ 1 := by
          have h1n := flatness_price_sechSq_nonneg (h + x 1)
          rw [abs_of_nonneg h1n] at h1
          nlinarith [mul_nonneg h1n (sub_nonneg.mpr h1)]
        rw [abs_of_nonneg (div_nonneg
          (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))]
        linarith
    have hFA : ∀ x, F x ≤ A x := by
      intro x
      dsimp [F, A, g]
      rw [flatness_price_sechSq_eq_cosh,
        flatness_price_sechSq_eq_cosh]
      convert flatness_mul_sech_sq_le_average_sech_fourth
        (h + x 0) (h + x 1) using 1
      all_goals ring
    have hgint (i : FlatnessPair) :
        Integrable (fun x : EuclideanSpace ℝ FlatnessPair => g (x i)) μ := by
      apply Integrable.of_bound (C := 1)
      · exact (hgcont.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards [] with x
        dsimp [g]
        have hi := flatness_abs_sechSq_le_one (h + x i)
        have hin := flatness_price_sechSq_nonneg (h + x i)
        rw [abs_of_nonneg hin] at hi
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [mul_nonneg hin (sub_nonneg.mpr hi)]
    calc
      flatnessTildeGPriceExpectation β h q s v = ∫ x, F x ∂μ := by
        rfl
      _ ≤ ∫ x, A x ∂μ := integral_mono hFint hAint hFA
      _ = (ProbabilityTheory.Gint
              (fun x : EuclideanSpace ℝ FlatnessPair => g (x 0)) S +
            ProbabilityTheory.Gint
              (fun x : EuclideanSpace ℝ FlatnessPair => g (x 1)) S) / 2 := by
        dsimp [A, μ]
        rw [integral_div, integral_add]
        · rfl
        · exact hgint 0
        · exact hgint 1
      _ = standardGaussianExpectation (fun z =>
          (Real.cosh (h + β * Real.sqrt q * z))⁻¹ ^ 4) := by
        rw [hcoord 0, hcoord 1]
        ring
  rw [flatnessTildeG_deriv_eq_price_neg β h q s v hs hqpos hv]
  have hstrict := data.strictAT (β, h) hp
  have hatnonneg : 0 ≤ atParameter β h := by
    rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
    exact mul_nonneg (sq_nonneg β) (integral_nonneg fun z => by positivity)
  have hpath : data.gap ≤ 1 - s * atParameter β h := by
    have hsat : s * atParameter β h ≤ atParameter β h := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hatnonneg]
    linarith
  have hat :
      s * β ^ 2 * flatnessTildeGPriceExpectation β h q s v ≤
        s * atParameter β h := by
    rw [atParameter_eq_beta_sq_mul_gaussian_sech_fourth hβ hh]
    have hprice' := hprice
    rw [hq] at hprice'
    simpa only [hq, mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprice' (sq_nonneg β)) hs.1
  linarith


lemma flatnessTildeG_hasDerivAt_neg
    (β h q s v : ℝ)
    (hβ : 0 ≤ β)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 < q)
    (hv : v ∈ Set.Ioo (-q) 0) :
    ∃ D : ℝ,
      HasDerivAt (fun u => flatnessTildeG β h q s u) D v := by
  by_cases hβ0 : β = 0
  · refine ⟨0, ?_⟩
    have heq : (fun u => flatnessTildeG β h q s u) = fun _ => flatnessTildeG β h q s v := by
      funext u
      simp [flatnessTildeG, gtIncrementScale, hβ0]
    rw [heq]
    exact hasDerivAt_const v _
  by_cases hs0 : s = 0
  · refine ⟨0, ?_⟩
    have heq : (fun u => flatnessTildeG β h q s u) = fun _ => flatnessTildeG β h q s v := by
      funext u
      simp [flatnessTildeG, gtIncrementScale, hs0]
    rw [heq]
    exact hasDerivAt_const v _

  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)

  let γ : Measure ℝ := gaussianReal 0 1
  let μ : Measure (ℝ × (ℝ × (ℝ × ℝ))) :=
    γ.prod (γ.prod (γ.prod γ))
  let J : Set ℝ := Set.Ioo ((-q + v) / 2) (v / 2)
  let a : ℝ → ℝ := fun t => β * Real.sqrt s * Real.sqrt (-t)
  let b : ℝ → ℝ := fun t => β * Real.sqrt s * Real.sqrt (q + t)
  let y₁ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    h + β * Real.sqrt ((1 - s) * q) * p.1
      + a t * p.2.1 + b t * p.2.2.1
  let y₂ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    h + β * Real.sqrt ((1 - s) * q) * p.1
      - a t * p.2.1 + b t * p.2.2.2
  let H : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    Real.tanh (y₁ t p) * Real.tanh (y₂ t p)

  have htanhcont : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    have hc : ContDiff ℝ ⊤ (fun x : ℝ => Real.sinh x / Real.cosh x) :=
      Real.contDiff_sinh.div Real.contDiff_cosh
        (fun x => (Real.cosh_pos x).ne')
    exact hc.continuous

  have hHbound (t : ℝ) (p : ℝ × (ℝ × (ℝ × ℝ))) : |H t p| ≤ 1 := by
    dsimp [H]
    rw [abs_mul]
    have h₁ := (Real.abs_tanh_lt_one (y₁ t p)).le
    have h₂ := (Real.abs_tanh_lt_one (y₂ t p)).le
    nlinarith [abs_nonneg (Real.tanh (y₁ t p)), abs_nonneg (Real.tanh (y₂ t p))]

  have hHInt (t : ℝ) : Integrable (H t) μ := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) : Continuous (H t)).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound t p

  have hHInt₃ (t z : ℝ) :
      Integrable (fun p : ℝ × (ℝ × ℝ) => H t (z, p))
        (γ.prod (γ.prod γ)) := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) :
        Continuous (fun p : ℝ × (ℝ × ℝ) => H t (z, p))).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound t (z, p)

  have hHInt₂ (t z z₀ : ℝ) :
      Integrable (fun p : ℝ × ℝ => H t (z, z₀, p))
        (γ.prod γ) := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) :
        Continuous (fun p : ℝ × ℝ => H t (z, z₀, p))).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound t (z, z₀, p)

  have hHInt₁ (t z z₀ z₁ : ℝ) :
      Integrable (fun z₂ : ℝ => H t (z, z₀, z₁, z₂)) γ := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) :
        Continuous (fun z₂ : ℝ => H t (z, z₀, z₁, z₂))).aestronglyMeasurable
    · filter_upwards [] with z₂
      simpa [Real.norm_eq_abs] using hHbound t (z, z₀, z₁, z₂)

  have hrepr (t : ℝ) (ht : t ∈ J) :
      flatnessTildeG β h q s t = ∫ p, H t p ∂μ := by
    have htneg : t < 0 := by dsimp [J] at ht; linarith [ht.2, hv.2]
    symm
    calc
      (∫ p, H t p ∂μ) =
          ∫ z, ∫ p, H t (z, p) ∂(γ.prod (γ.prod γ)) ∂γ := by
            exact integral_prod _ (hHInt t)
      _ = ∫ z, ∫ z₀, ∫ p, H t (z, z₀, p) ∂(γ.prod γ) ∂γ ∂γ := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact integral_prod _ (hHInt₃ t z)
      _ = ∫ z, ∫ z₀, ∫ z₁, ∫ z₂, H t (z, z₀, z₁, z₂) ∂γ ∂γ ∂γ ∂γ := by
            apply integral_congr_ae
            filter_upwards [] with z
            apply integral_congr_ae
            filter_upwards [] with z₀
            exact integral_prod _ (hHInt₂ t z z₀)
      _ = flatnessTildeG β h q s t := by
            simp only [flatnessTildeG, standardGaussianExpectation]
            dsimp [H, y₁, y₂, a, b, γ, μ]
            simp [gtIncrementScale, gtPathSign, abs_of_neg htneg, not_le.mpr htneg,
              sub_eq_add_neg]

  let da : ℝ → ℝ := fun t => -(β * Real.sqrt s) / (2 * Real.sqrt (-t))
  let db : ℝ → ℝ := fun t => (β * Real.sqrt s) / (2 * Real.sqrt (q + t))
  let dy₁ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    da t * p.2.1 + db t * p.2.2.1
  let dy₂ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    -da t * p.2.1 + db t * p.2.2.2
  let H' : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun t p =>
    ProbabilityTheory.PriceTanh.sechSq (y₁ t p) * dy₁ t p * Real.tanh (y₂ t p)
      + Real.tanh (y₁ t p) * ProbabilityTheory.PriceTanh.sechSq (y₂ t p) * dy₂ t p

  have haDeriv (t : ℝ) (ht : t ∈ J) : HasDerivAt a (da t) t := by
    have htneg : t < 0 := by dsimp [J] at ht; linarith [ht.2, hv.2]
    have hsqrtne : Real.sqrt (-t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have harg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
    have hd := ((Real.hasDerivAt_sqrt (by linarith : -t ≠ 0)).comp t harg).const_mul
      (β * Real.sqrt s)
    have hdeq : β * Real.sqrt s * (1 / (2 * Real.sqrt (-t)) * -1) = da t := by
      dsimp [da]
      field_simp [hsqrtne]
    simpa only [a, Function.comp_apply, hdeq] using hd

  have hbDeriv (t : ℝ) (ht : t ∈ J) : HasDerivAt b (db t) t := by
    have htq : 0 < q + t := by dsimp [J] at ht; linarith [ht.1, hv.1]
    have hsqrtne : Real.sqrt (q + t) ≠ 0 := (Real.sqrt_pos.2 htq).ne'
    have harg : HasDerivAt (fun x : ℝ => q + x) 1 t :=
      (hasDerivAt_id t).const_add q
    have hd := ((Real.hasDerivAt_sqrt htq.ne').comp t harg).const_mul
      (β * Real.sqrt s)
    have hdeq : β * Real.sqrt s * (1 / (2 * Real.sqrt (q + t)) * 1) = db t := by
      dsimp [db]
      field_simp [hsqrtne]
    simpa only [b, Function.comp_apply, hdeq] using hd

  have hy₁Deriv (t : ℝ) (p : ℝ × (ℝ × (ℝ × ℝ))) (ht : t ∈ J) :
      HasDerivAt (fun x => y₁ x p) (dy₁ t p) t := by
    dsimp [y₁, dy₁]
    simpa [add_assoc] using
      (((haDeriv t ht).mul_const p.2.1).add
        ((hbDeriv t ht).mul_const p.2.2.1)).const_add
          (h + β * Real.sqrt ((1 - s) * q) * p.1)

  have hy₂Deriv (t : ℝ) (p : ℝ × (ℝ × (ℝ × ℝ))) (ht : t ∈ J) :
      HasDerivAt (fun x => y₂ x p) (dy₂ t p) t := by
    dsimp [y₂, dy₂]
    simpa [add_assoc, sub_eq_add_neg] using
      ((((haDeriv t ht).mul_const p.2.1).neg.add
        ((hbDeriv t ht).mul_const p.2.2.2)).const_add
          (h + β * Real.sqrt ((1 - s) * q) * p.1))

  have hHDiff (p : ℝ × (ℝ × (ℝ × ℝ))) (t : ℝ) (ht : t ∈ J) :
      HasDerivAt (fun x => H x p) (H' t p) t := by
    have hd₁ :=
      (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (y₁ t p)).comp t (hy₁Deriv t p ht)
    have hd₂ :=
      (ProbabilityTheory.PriceTanh.tanh_hasDerivAt (y₂ t p)).comp t (hy₂Deriv t p ht)
    have hdiff : DifferentiableAt ℝ (fun x => H x p) t := by
      dsimp [H]
      exact hd₁.differentiableAt.mul hd₂.differentiableAt
    apply hdiff.hasDerivAt.congr_deriv
    have hraw := (hd₁.mul hd₂).deriv
    have hfun :
        (fun x => H x p) =
          (Real.tanh ∘ fun x => y₁ x p) * (Real.tanh ∘ fun x => y₂ x p) := by
      funext x
      rfl
    dsimp [H']
    rw [hfun]
    simpa only [Function.comp_apply, mul_assoc] using hraw

  let c₀ : ℝ := β * Real.sqrt s
  let rₐ : ℝ := Real.sqrt (-v / 2)
  let rᵦ : ℝ := Real.sqrt ((q + v) / 2)
  let C : ℝ := c₀ * (rₐ⁻¹ + rᵦ⁻¹)

  have hc₀ : 0 ≤ c₀ := by dsimp [c₀]; positivity
  have hrₐ : 0 < rₐ := by
    dsimp [rₐ]
    exact Real.sqrt_pos.2 (by linarith [hv.2])
  have hrᵦ : 0 < rᵦ := by
    dsimp [rᵦ]
    exact Real.sqrt_pos.2 (by linarith [hv.1])
  have hC : 0 ≤ C := by dsimp [C]; positivity

  have hda_bound (t : ℝ) (ht : t ∈ J) : |da t| ≤ C := by
    have htneg : t < 0 := by dsimp [J] at ht; linarith [ht.2, hv.2]
    have hsqrtpos : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
    have hra_le : rₐ ≤ Real.sqrt (-t) := by
      apply Real.sqrt_le_sqrt
      dsimp [rₐ, J] at ht ⊢
      linarith [ht.2]
    have hinv : (2 * Real.sqrt (-t))⁻¹ ≤ rₐ⁻¹ := by
      apply (inv_le_inv₀ (by positivity : 0 < 2 * Real.sqrt (-t)) hrₐ).2
      linarith
    have heq : |da t| = c₀ * (2 * Real.sqrt (-t))⁻¹ := by
      dsimp [da, c₀]
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hβpos,
        abs_of_nonneg (Real.sqrt_nonneg s), abs_of_pos (by positivity : 0 < 2 * Real.sqrt (-t))]
      rw [div_eq_mul_inv]
    rw [heq]
    calc
      c₀ * (2 * Real.sqrt (-t))⁻¹ ≤ c₀ * rₐ⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hc₀
      _ ≤ C := by
        dsimp [C]
        have : 0 ≤ c₀ * rᵦ⁻¹ := mul_nonneg hc₀ (inv_nonneg.mpr hrᵦ.le)
        linarith

  have hdb_bound (t : ℝ) (ht : t ∈ J) : |db t| ≤ C := by
    have htq : 0 < q + t := by dsimp [J] at ht; linarith [ht.1, hv.1]
    have hsqrtpos : 0 < Real.sqrt (q + t) := Real.sqrt_pos.2 htq
    have hrb_le : rᵦ ≤ Real.sqrt (q + t) := by
      apply Real.sqrt_le_sqrt
      dsimp [rᵦ, J] at ht ⊢
      linarith [ht.1]
    have hinv : (2 * Real.sqrt (q + t))⁻¹ ≤ rᵦ⁻¹ := by
      apply (inv_le_inv₀ (by positivity : 0 < 2 * Real.sqrt (q + t)) hrᵦ).2
      linarith
    have heq : |db t| = c₀ * (2 * Real.sqrt (q + t))⁻¹ := by
      dsimp [db, c₀]
      rw [abs_div, abs_mul, abs_of_pos hβpos,
        abs_of_nonneg (Real.sqrt_nonneg s), abs_of_pos (by positivity : 0 < 2 * Real.sqrt (q + t))]
      rw [div_eq_mul_inv]
    rw [heq]
    calc
      c₀ * (2 * Real.sqrt (q + t))⁻¹ ≤ c₀ * rᵦ⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hc₀
      _ ≤ C := by
        dsimp [C]
        have : 0 ≤ c₀ * rₐ⁻¹ := mul_nonneg hc₀ (inv_nonneg.mpr hrₐ.le)
        linarith

  have hsechSq (x : ℝ) : |ProbabilityTheory.PriceTanh.sechSq x| ≤ 1 := by
    have hnonneg : 0 ≤ ProbabilityTheory.PriceTanh.sechSq x := by
      dsimp [ProbabilityTheory.PriceTanh.sechSq]
      exact sub_nonneg.mpr (Real.tanh_sq_lt_one x).le
    rw [abs_of_nonneg hnonneg]
    dsimp [ProbabilityTheory.PriceTanh.sechSq]
    nlinarith [sq_nonneg (Real.tanh x)]

  let bound : (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun p =>
    C * (2 * |p.2.1| + |p.2.2.1| + |p.2.2.2|)

  have hH'bound (p : ℝ × (ℝ × (ℝ × ℝ))) (t : ℝ) (ht : t ∈ J) :
      |H' t p| ≤ bound p := by
    have hdy₁ : |dy₁ t p| ≤ C * (|p.2.1| + |p.2.2.1|) := by
      dsimp [dy₁]
      calc
        |da t * p.2.1 + db t * p.2.2.1| ≤
            |da t * p.2.1| + |db t * p.2.2.1| := abs_add_le _ _
        _ = |da t| * |p.2.1| + |db t| * |p.2.2.1| := by rw [abs_mul, abs_mul]
        _ ≤ C * |p.2.1| + C * |p.2.2.1| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hda_bound t ht) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hdb_bound t ht) (abs_nonneg _))
        _ = C * (|p.2.1| + |p.2.2.1|) := by ring
    have hdy₂ : |dy₂ t p| ≤ C * (|p.2.1| + |p.2.2.2|) := by
      dsimp [dy₂]
      calc
        |-da t * p.2.1 + db t * p.2.2.2| ≤
            |-da t * p.2.1| + |db t * p.2.2.2| := abs_add_le _ _
        _ = |da t| * |p.2.1| + |db t| * |p.2.2.2| := by
          rw [abs_mul, abs_mul, abs_neg]
        _ ≤ C * |p.2.1| + C * |p.2.2.2| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hda_bound t ht) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hdb_bound t ht) (abs_nonneg _))
        _ = C * (|p.2.1| + |p.2.2.2|) := by ring
    have hterm₁ :
        |ProbabilityTheory.PriceTanh.sechSq (y₁ t p) * dy₁ t p * Real.tanh (y₂ t p)|
          ≤ |dy₁ t p| := by
      rw [abs_mul, abs_mul]
      calc
        |ProbabilityTheory.PriceTanh.sechSq (y₁ t p)| * |dy₁ t p| *
            |Real.tanh (y₂ t p)| ≤ 1 * |dy₁ t p| * 1 := by
              gcongr
              · exact hsechSq _
              · exact (Real.abs_tanh_lt_one _).le
        _ = |dy₁ t p| := by ring
    have hterm₂ :
        |Real.tanh (y₁ t p) * ProbabilityTheory.PriceTanh.sechSq (y₂ t p) * dy₂ t p|
          ≤ |dy₂ t p| := by
      rw [abs_mul, abs_mul]
      calc
        |Real.tanh (y₁ t p)| * |ProbabilityTheory.PriceTanh.sechSq (y₂ t p)| *
            |dy₂ t p| ≤ 1 * 1 * |dy₂ t p| := by
              gcongr
              · exact (Real.abs_tanh_lt_one _).le
              · exact hsechSq _
        _ = |dy₂ t p| := by ring
    dsimp [H']
    calc
      |ProbabilityTheory.PriceTanh.sechSq (y₁ t p) * dy₁ t p * Real.tanh (y₂ t p) +
          Real.tanh (y₁ t p) * ProbabilityTheory.PriceTanh.sechSq (y₂ t p) * dy₂ t p| ≤
          |ProbabilityTheory.PriceTanh.sechSq (y₁ t p) * dy₁ t p * Real.tanh (y₂ t p)| +
            |Real.tanh (y₁ t p) * ProbabilityTheory.PriceTanh.sechSq (y₂ t p) * dy₂ t p| :=
        abs_add_le _ _
      _ ≤ |dy₁ t p| + |dy₂ t p| := add_le_add hterm₁ hterm₂
      _ ≤ C * (|p.2.1| + |p.2.2.1|) + C * (|p.2.1| + |p.2.2.2|) :=
        add_le_add hdy₁ hdy₂
      _ = bound p := by dsimp [bound]; ring

  have hzabs : Integrable (fun z : ℝ => |z|) γ := by
    dsimp [γ]
    simpa using integrable_abs_pow_gaussianReal_centered (1 : NNReal) 1
  have hz₀ : Integrable (fun p : ℝ × (ℝ × (ℝ × ℝ)) => |p.2.1|) μ :=
    (hzabs.comp_fst (γ.prod γ)).comp_snd γ
  have hz₁ : Integrable (fun p : ℝ × (ℝ × (ℝ × ℝ)) => |p.2.2.1|) μ :=
    ((hzabs.comp_fst γ).comp_snd γ).comp_snd γ
  have hz₂ : Integrable (fun p : ℝ × (ℝ × (ℝ × ℝ)) => |p.2.2.2|) μ :=
    ((hzabs.comp_snd γ).comp_snd γ).comp_snd γ
  have hboundInt : Integrable bound μ := by
    dsimp [bound]
    exact (((hz₀.const_mul 2).add hz₁).add hz₂).const_mul C

  have hH'meas : AEStronglyMeasurable (H' v) μ := by
    have hy₁cont : Continuous (y₁ v) := by dsimp [y₁, a, b]; fun_prop
    have hy₂cont : Continuous (y₂ v) := by dsimp [y₂, a, b]; fun_prop
    have hdy₁cont : Continuous (dy₁ v) := by dsimp [dy₁, da, db]; fun_prop
    have hdy₂cont : Continuous (dy₂ v) := by dsimp [dy₂, da, db]; fun_prop
    have ht₁ : Continuous (fun p => Real.tanh (y₁ v p)) := htanhcont.comp hy₁cont
    have ht₂ : Continuous (fun p => Real.tanh (y₂ v p)) := htanhcont.comp hy₂cont
    have hs₁ : Continuous (fun p => ProbabilityTheory.PriceTanh.sechSq (y₁ v p)) := by
      dsimp [ProbabilityTheory.PriceTanh.sechSq]
      exact continuous_const.sub (ht₁.pow 2)
    have hs₂ : Continuous (fun p => ProbabilityTheory.PriceTanh.sechSq (y₂ v p)) := by
      dsimp [ProbabilityTheory.PriceTanh.sechSq]
      exact continuous_const.sub (ht₂.pow 2)
    exact ((hs₁.mul hdy₁cont).mul ht₂).add ((ht₁.mul hs₂).mul hdy₂cont)
      |>.aestronglyMeasurable

  have hvJ : v ∈ J := by
    dsimp [J]
    constructor <;> linarith [hv.1, hv.2]
  have hJnhds : J ∈ nhds v := Ioo_mem_nhds hvJ.1 hvJ.2

  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := H) (F' := H') (x₀ := v) (s := J) (bound := bound)
    hJnhds
    (Filter.Eventually.of_forall fun t => (hHInt t).aestronglyMeasurable)
    (hHInt v)
    hH'meas
    (Filter.Eventually.of_forall fun p t ht => by
      simpa [Real.norm_eq_abs] using hH'bound p t ht)
    hboundInt
    (Filter.Eventually.of_forall fun p t ht => hHDiff p t ht)

  refine ⟨∫ p, H' v p ∂μ, ?_⟩
  apply hd.2.congr_of_eventuallyEq
  filter_upwards [hJnhds] with t ht
  exact hrepr t ht


lemma flatnessTildeG_continuousOn_neg
    (β h q s : ℝ) :
    ContinuousOn
      (fun v => flatnessTildeG β h q s v)
      (Set.Icc (-q) 0) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let μ : Measure (ℝ × (ℝ × (ℝ × ℝ))) :=
    γ.prod (γ.prod (γ.prod γ))
  let a : ℝ → ℝ := fun v => β * Real.sqrt s * Real.sqrt (-v)
  let b : ℝ → ℝ := fun v => β * Real.sqrt s * Real.sqrt (q + v)
  let y₁ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun v p =>
    h + β * Real.sqrt ((1 - s) * q) * p.1
      + a v * p.2.1 + b v * p.2.2.1
  let y₂ : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun v p =>
    h + β * Real.sqrt ((1 - s) * q) * p.1
      - a v * p.2.1 + b v * p.2.2.2
  let H : ℝ → (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun v p =>
    Real.tanh (y₁ v p) * Real.tanh (y₂ v p)

  have htanhcont : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div₀ Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')

  have hHbound (v : ℝ) (p : ℝ × (ℝ × (ℝ × ℝ))) : |H v p| ≤ 1 := by
    dsimp [H]
    rw [abs_mul]
    have h₁ := (Real.abs_tanh_lt_one (y₁ v p)).le
    have h₂ := (Real.abs_tanh_lt_one (y₂ v p)).le
    nlinarith [abs_nonneg (Real.tanh (y₁ v p)), abs_nonneg (Real.tanh (y₂ v p))]

  have hHcontLeft (v : ℝ) : Continuous (H v) := by
    dsimp [H, y₁, y₂, a, b]
    exact (htanhcont.comp (by fun_prop)).mul (htanhcont.comp (by fun_prop))

  have hHcontRight (p : ℝ × (ℝ × (ℝ × ℝ))) :
      Continuous (fun v => H v p) := by
    dsimp [H, y₁, y₂, a, b]
    exact (htanhcont.comp (by fun_prop)).mul (htanhcont.comp (by fun_prop))

  have hGcont : Continuous (fun v => ∫ p, H v p ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro v
    refine continuousAt_of_dominated
      (Filter.Eventually.of_forall fun u => (hHcontLeft u).aestronglyMeasurable)
      ?_ (integrable_const 1) ?_
    · filter_upwards [] with u
      filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound u p
    · filter_upwards [] with p
      exact (hHcontRight p).continuousAt

  have hHInt (v : ℝ) : Integrable (H v) μ := by
    apply Integrable.of_bound (C := 1)
    · exact (hHcontLeft v).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound v p

  have hHInt₃ (v z : ℝ) :
      Integrable (fun p : ℝ × (ℝ × ℝ) => H v (z, p))
        (γ.prod (γ.prod γ)) := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) :
        Continuous (fun p : ℝ × (ℝ × ℝ) => H v (z, p))).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound v (z, p)

  have hHInt₂ (v z z₀ : ℝ) :
      Integrable (fun p : ℝ × ℝ => H v (z, z₀, p)) (γ.prod γ) := by
    apply Integrable.of_bound (C := 1)
    · exact (by
        dsimp [H, y₁, y₂, a, b]
        exact (htanhcont.comp (by fun_prop)).mul
          (htanhcont.comp (by fun_prop)) :
        Continuous (fun p : ℝ × ℝ => H v (z, z₀, p))).aestronglyMeasurable
    · filter_upwards [] with p
      simpa [Real.norm_eq_abs] using hHbound v (z, z₀, p)

  have hrepr (v : ℝ) (hv : v ∈ Set.Icc (-q) 0) :
      flatnessTildeG β h q s v = ∫ p, H v p ∂μ := by
    have hprod :
        (∫ p, H v p ∂μ) =
          ∫ z, ∫ z₀, ∫ z₁, ∫ z₂, H v (z, z₀, z₁, z₂) ∂γ ∂γ ∂γ ∂γ := by
      calc
        (∫ p, H v p ∂μ) =
            ∫ z, ∫ p, H v (z, p) ∂(γ.prod (γ.prod γ)) ∂γ := by
              exact integral_prod _ (hHInt v)
        _ = ∫ z, ∫ z₀, ∫ p, H v (z, z₀, p) ∂(γ.prod γ) ∂γ ∂γ := by
              apply integral_congr_ae
              filter_upwards [] with z
              exact integral_prod _ (hHInt₃ v z)
        _ = ∫ z, ∫ z₀, ∫ z₁, ∫ z₂, H v (z, z₀, z₁, z₂) ∂γ ∂γ ∂γ ∂γ := by
              apply integral_congr_ae
              filter_upwards [] with z
              apply integral_congr_ae
              filter_upwards [] with z₀
              exact integral_prod _ (hHInt₂ v z z₀)
    rw [hprod]
    by_cases hv0 : v = 0
    · subst v
      simp [flatnessTildeG, standardGaussianExpectation, H, y₁, y₂, a, b, γ,
        gtIncrementScale]
    · have hvneg : v < 0 := lt_of_le_of_ne hv.2 hv0
      simp [flatnessTildeG, standardGaussianExpectation, H, y₁, y₂, a, b, γ,
        gtIncrementScale, gtPathSign, abs_of_neg hvneg, not_le.mpr hvneg,
        sub_eq_add_neg]

  refine hGcont.continuousOn.congr ?_
  intro v hv
  exact hrepr v hv

/-!
Case-specific consequences live in `Lemmas.GuerraTalagrand.Flatness` modules.
They import this shared file, keeping the common GT recursion, derivative
formulas, and envelope lemmas free of import cycles.
-/

end SpinGlass.AT
