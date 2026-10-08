module

public import Mathlib

@[expose] public section

/-!
# Converting regional deficits to one quadratic bound

This file contains the elementary last step used after the local and compact
Section 5 estimates have been assembled.  It is deliberately abstract in the
finite-size/disorder variables: no continuity of the constrained free energy
or of the attainable-overlap set is needed.  The regional hypotheses must be
proved separately from Talagrand's interpolation argument.
-/

open Set

namespace SpinGlass.Targets

/-- If a deficit is quadratic near `q` and uniformly positive away from `q`,
then it is bounded below by one quadratic function on `[-1,1]`.  The constant
`4 / c` uses only `|u-q| ≤ 2`; the statement is independent of all auxiliary
parameters such as system size and disorder. -/
theorem exists_quadratic_constant_of_local_and_outside
    {X : Type*} {B : X → ℝ} {F : X → ℝ → ℝ} {q η a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hη : 0 < η)
    (hq : q ∈ Icc (-1 : ℝ) 1)
    (hlocal : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1,
      |u - q| ≤ η → F x u ≤ B x - a * (u - q) ^ 2)
    (houtside : ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1,
      η ≤ |u - q| → F x u ≤ B x - c) :
    ∃ K > 0, ∀ x, ∀ u ∈ Icc (-1 : ℝ) 1,
      F x u ≤ B x - (u - q) ^ 2 / K := by
  let K : ℝ := max (1 / a) (4 / c)
  have hK_a : 1 / a ≤ K := le_max_left _ _
  have hK_c : 4 / c ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le (by positivity : 0 < 1 / a) hK_a
  refine ⟨K, hK, ?_⟩
  intro x u hu
  by_cases hnear : |u - q| ≤ η
  · have H := hlocal x u hu hnear
    have hKa : 0 < a := ha
    have hKpos : 0 < K := hK
    have hquad : (u - q) ^ 2 / K ≤ a * (u - q) ^ 2 := by
      have hprod : 1 ≤ K * a := by
        apply (div_le_iff₀ ha).mp
        simpa only [one_div] using hK_a
      have hdiv : 1 / K ≤ a := (div_le_iff₀ hKpos).2 (by
        simpa only [one_mul, mul_comm] using hprod)
      calc
        (u - q) ^ 2 / K = (1 / K) * (u - q) ^ 2 := by ring
        _ ≤ a * (u - q) ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
    linarith
  · have H := houtside x u hu (le_of_not_ge hnear)
    have hqabs : |q| ≤ 1 := by
      rw [abs_le]
      exact ⟨hq.1, hq.2⟩
    have huabs : |u| ≤ 1 := by
      rw [abs_le]
      exact ⟨hu.1, hu.2⟩
    have hdiff : |u - q| ≤ 2 := by
      calc
        |u - q| = |u + (-q)| := by rw [sub_eq_add_neg]
        _ ≤ |u| + |-q| := abs_add_le _ _
        _ = |u| + |q| := by rw [abs_neg]
        _ ≤ 2 := by linarith
    have hsq : (u - q) ^ 2 ≤ 4 := by
      rw [← sq_abs]
      nlinarith [sq_nonneg (|u - q| - 2)]
    have hquad : (u - q) ^ 2 / K ≤ c := by
      have hdiv : 4 / K ≤ c := by
        have hKc : 4 / c ≤ K := hK_c
        exact (div_le_iff₀ hK).2 (by
          have hprod : 4 ≤ K * c := by
            exact (div_le_iff₀ hc).mp hKc
          simpa only [mul_comm] using hprod)
      have hnonneg : 0 ≤ (u - q) ^ 2 := sq_nonneg _
      have hscale : (u - q) ^ 2 / K ≤ 4 / K :=
        (div_le_div_of_nonneg_right hsq (le_of_lt hK))
      exact hscale.trans hdiv
    linarith

end SpinGlass.Targets
