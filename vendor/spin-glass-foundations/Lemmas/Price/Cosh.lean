module

/- Compatibility adaptation: supply measurable law to the Gaussian moment-generating theorem. -/
public import Lemmas.Price.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Price's formula for a product of hyperbolic cosines

The bounded `C²` theorem in `Lemmas.Price.Deriv` cannot be applied directly to
`(x, y) ↦ cosh x * cosh y`.  This file treats that observable using the exact
Gaussian moment-generating function.  In particular, no boundedness hypothesis
on the observable and no constant-trace hypothesis on the covariance path are
needed.
-/

open Matrix MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory
namespace PriceCosh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exponential moment of a linear functional of a centered multivariate Gaussian. -/
theorem integral_exp_inner_multivariateGaussian {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (a : EuclideanSpace ℝ ι) :
    ∫ z, Real.exp ⟪a, z⟫ ∂(ProbabilityTheory.multivariateGaussian 0 S) =
      Real.exp ((a ⬝ᵥ S *ᵥ a) / 2) := by
  let μ : Measure (EuclideanSpace ℝ ι) := ProbabilityTheory.multivariateGaussian 0 S
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := innerSL ℝ a
  have hmean : μ[L] = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id]
    simp [μ]
  have hvar : Var[L; μ] = a ⬝ᵥ S *ᵥ a := by
    dsimp [L]
    rw [← covarianceBilin_self IsGaussian.memLp_two_id a]
    exact covarianceBilin_multivariateGaussian hS a a
  have hmap : μ.map L = gaussianReal 0 ((a ⬝ᵥ S *ᵥ a).toNNReal) := by
    simpa [hmean, hvar] using (IsGaussian.map_eq_gaussianReal (μ := μ) L)
  have hlaw : HasLaw L (gaussianReal 0 ((a ⬝ᵥ S *ᵥ a).toNNReal)) μ :=
    { aemeasurable := L.continuous.measurable.aemeasurable, map_eq := hmap }
  have hmgf := mgf_gaussianReal hlaw 1
  rw [mgf] at hmgf
  have hq : 0 ≤ a ⬝ᵥ S *ᵥ a := hS.dotProduct_mulVec_nonneg a
  simpa [μ, L, Real.coe_toNNReal _ hq] using hmgf

/-- Exponentials of linear functionals are integrable under a multivariate Gaussian. -/
theorem integrable_exp_inner_multivariateGaussian {S : Matrix ι ι ℝ}
    (_hS : S.PosSemidef) (a : EuclideanSpace ℝ ι) :
    Integrable (fun z => Real.exp ⟪a, z⟫)
      (ProbabilityTheory.multivariateGaussian 0 S) := by
  let μ : Measure (EuclideanSpace ℝ ι) := ProbabilityTheory.multivariateGaussian 0 S
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := innerSL ℝ a
  have hmap : μ.map L = gaussianReal μ[L] Var[L; μ].toNNReal :=
    IsGaussian.map_eq_gaussianReal L
  have hint : Integrable (fun x : ℝ => Real.exp (1 * x)) (μ.map L) := by
    rw [hmap]
    exact integrable_exp_mul_gaussianReal 1
  have hint' := hint.comp_measurable L.continuous.measurable
  simpa [μ, L, Function.comp_def] using hint'

/-- Hyperbolic cosines of linear functionals are integrable under a multivariate Gaussian. -/
theorem integrable_cosh_inner_multivariateGaussian {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (a : EuclideanSpace ℝ ι) :
    Integrable (fun z => Real.cosh ⟪a, z⟫)
      (ProbabilityTheory.multivariateGaussian 0 S) := by
  rw [show (fun z => Real.cosh ⟪a, z⟫) =
      fun z => (Real.exp ⟪a, z⟫ + Real.exp ⟪-a, z⟫) / 2 by
    funext z
    rw [Real.cosh_eq]
    simp]
  exact ((integrable_exp_inner_multivariateGaussian hS a).add
    (integrable_exp_inner_multivariateGaussian hS (-a))).div_const 2

/-- Exact expectation of the hyperbolic cosine of a centered Gaussian linear functional. -/
theorem integral_cosh_inner_multivariateGaussian {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (a : EuclideanSpace ℝ ι) :
    ∫ z, Real.cosh ⟪a, z⟫ ∂(ProbabilityTheory.multivariateGaussian 0 S) =
      Real.exp ((a ⬝ᵥ S *ᵥ a) / 2) := by
  rw [show (fun z => Real.cosh ⟪a, z⟫) =
      fun z => (Real.exp ⟪a, z⟫ + Real.exp ⟪-a, z⟫) / 2 by
    funext z
    rw [Real.cosh_eq]
    simp]
  rw [integral_div, integral_add
    (integrable_exp_inner_multivariateGaussian hS a)
    (integrable_exp_inner_multivariateGaussian hS (-a)),
    integral_exp_inner_multivariateGaussian hS a,
    integral_exp_inner_multivariateGaussian hS (-a)]
  have hq : ((-a).ofLp) ⬝ᵥ S *ᵥ ((-a).ofLp) = a ⬝ᵥ S *ᵥ a := by
    simp [dotProduct, mulVec]
  rw [hq]
  ring

section Pair

abbrev Pair := Fin 2

/-- The Gaussian expectation of `cosh` in each of two coordinates. -/
noncomputable def coshPairGint (S : Matrix Pair Pair ℝ) : ℝ :=
  ∫ z, Real.cosh (z 0) * Real.cosh (z 1)
    ∂(ProbabilityTheory.multivariateGaussian 0 S)

/-- Closed form for the Gaussian expectation of a product of two hyperbolic cosines. -/
theorem coshPairGint_eq {S : Matrix Pair Pair ℝ} (hS : S.PosSemidef) :
    coshPairGint S =
      Real.exp ((S 0 0 + S 1 1) / 2) * Real.cosh (S 0 1) := by
  let ep : EuclideanSpace ℝ Pair := euclidBasis 0 + euclidBasis 1
  let em : EuclideanSpace ℝ Pair := euclidBasis 0 - euclidBasis 1
  have hsym : S 1 0 = S 0 1 := by
    have h := congrFun (congrFun hS.isHermitian 0) 1
    simpa [Matrix.conjTranspose_apply] using h
  have hep (z : EuclideanSpace ℝ Pair) : ⟪ep, z⟫ = z 0 + z 1 := by
    simp only [ep, inner_add_left, ProbabilityTheory.inner_euclidBasis]
  have hem (z : EuclideanSpace ℝ Pair) : ⟪em, z⟫ = z 0 - z 1 := by
    simp only [em, inner_sub_left, ProbabilityTheory.inner_euclidBasis]
  have hqp : ep ⬝ᵥ S *ᵥ ep = S 0 0 + S 1 1 + 2 * S 0 1 := by
    simp [ep, euclidBasis, dotProduct, mulVec, Fin.sum_univ_two, hsym]
    ring
  have hqm : em ⬝ᵥ S *ᵥ em = S 0 0 + S 1 1 - 2 * S 0 1 := by
    simp [em, euclidBasis, dotProduct, mulVec, Fin.sum_univ_two, hsym]
    ring
  have hpoint (z : EuclideanSpace ℝ Pair) :
      Real.cosh (z 0) * Real.cosh (z 1) =
        (Real.cosh ⟪ep, z⟫ + Real.cosh ⟪em, z⟫) / 2 := by
    rw [hep, hem, Real.cosh_add, Real.cosh_sub]
    ring
  rw [coshPairGint]
  simp_rw [hpoint]
  rw [integral_div, integral_add
    (integrable_cosh_inner_multivariateGaussian hS ep)
    (integrable_cosh_inner_multivariateGaussian hS em),
    integral_cosh_inner_multivariateGaussian hS ep,
    integral_cosh_inner_multivariateGaussian hS em, hqp, hqm]
  have hp : (S 0 0 + S 1 1 + 2 * S 0 1) / 2 =
      (S 0 0 + S 1 1) / 2 + S 0 1 := by ring
  have hm : (S 0 0 + S 1 1 - 2 * S 0 1) / 2 =
      (S 0 0 + S 1 1) / 2 - S 0 1 := by ring
  rw [hp, hm, Real.exp_add, Real.exp_sub, Real.cosh_eq]
  rw [Real.exp_neg]
  ring

/-- Price's formula for `E[cosh G₁(t) cosh G₂(t)]` along a smooth covariance path.

Unlike `hasDerivWithinAt_Gint`, this specialized result needs neither bounded derivatives
of the observable nor a constant covariance trace.
-/
theorem hasDerivWithinAt_coshPairGint
    {U : Set ℝ} {t : ℝ} (S : ℝ → Matrix Pair Pair ℝ)
    (ht : t ∈ U)
    (hPSD : ∀ s ∈ U, (S s).PosSemidef)
    {a' b' c' : ℝ}
    (ha : HasDerivWithinAt (fun s => S s 0 0) a' U t)
    (hb : HasDerivWithinAt (fun s => S s 1 1) b' U t)
    (hc : HasDerivWithinAt (fun s => S s 0 1) c' U t) :
    HasDerivWithinAt (fun s => coshPairGint (S s))
      (((a' + b') / 2) * coshPairGint (S t) +
        c' * Real.exp ((S t 0 0 + S t 1 1) / 2) * Real.sinh (S t 0 1)) U t := by
  have hdiag : HasDerivWithinAt (fun s => (S s 0 0 + S s 1 1) / 2)
      ((a' + b') / 2) U t := (ha.add hb).div_const 2
  have hexp : HasDerivWithinAt
      (fun s => Real.exp ((S s 0 0 + S s 1 1) / 2))
      (Real.exp ((S t 0 0 + S t 1 1) / 2) * ((a' + b') / 2)) U t :=
    (Real.hasDerivAt_exp _).comp_hasDerivWithinAt t hdiag
  have hcosh : HasDerivWithinAt (fun s => Real.cosh (S s 0 1))
      (Real.sinh (S t 0 1) * c') U t :=
    (Real.hasDerivAt_cosh _).comp_hasDerivWithinAt t hc
  have hclosed := hexp.mul hcosh
  refine (hclosed.congr_of_mem (f₁ := fun s => coshPairGint (S s))
    (fun s hs => coshPairGint_eq (hPSD s hs)) ht).congr_deriv ?_
  rw [coshPairGint_eq (hPSD t ht)]
  ring

end Pair

end PriceCosh
end ProbabilityTheory
