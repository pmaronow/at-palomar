module

public import Paper.Hyperbolic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Polynomial observables of tanh

Differentiating a polynomial in `tanh` preserves that class of observables.
Every such observable is uniformly bounded because `tanh` takes values in the
compact interval `[-1,1]`.
-/

open scoped Polynomial

namespace Paper

noncomputable def tanhPolynomialDeriv (P : ℝ[X]) : ℝ[X] :=
  P.derivative * (1 - Polynomial.X ^ 2)

theorem hasDerivAt_tanhPolynomial (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => P.eval (Real.tanh y))
      ((tanhPolynomialDeriv P).eval (Real.tanh x)) x := by
  have he : (tanhPolynomialDeriv P).eval (Real.tanh x) =
      P.derivative.eval (Real.tanh x) * sech x ^ 2 := by
    simp only [tanhPolynomialDeriv, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show 1 - Real.tanh x ^ 2 = sech x ^ 2 by linarith [tanh_sq_add_sech_sq x]]
  rw [he]
  simpa only [Function.comp_def] using
    (P.hasDerivAt (Real.tanh x)).comp x (hasDerivAt_tanh x)

theorem continuous_tanhPolynomial (P : ℝ[X]) :
    Continuous (fun y => P.eval (Real.tanh y)) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanhPolynomial P x).continuousAt)

theorem exists_bound_tanhPolynomial (P : ℝ[X]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖P.eval (Real.tanh x)‖ ≤ M := by
  have hc : Continuous (fun y : ℝ => P.eval y) :=
    continuous_iff_continuousAt.mpr (fun x => (P.hasDerivAt x).continuousAt)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have hx : Real.tanh x ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp (Real.abs_tanh_lt_one x).le
  exact (hM _ hx).trans (le_max_left _ _)

theorem tanhPolynomial_bounded (P : ℝ[X]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖P.eval (Real.tanh x)‖ ≤ M :=
  exists_bound_tanhPolynomial P

end Paper
