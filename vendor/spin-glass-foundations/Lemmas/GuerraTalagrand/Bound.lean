module

public import Lemmas.GuerraTalagrand.Bound.Interpolation

@[expose] public section

/-!
# Guerra--Talagrand bound

This public entry module exposes the finite-volume two-replica bound after the
finite-state, endpoint, comparison, and interpolation layers have been assembled.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal

set_option autoImplicit false

namespace SpinGlass.AT

universe u

/--
Finite-volume two-replica Guerra--Talagrand bound.

For every Lagrange multiplier `lam : ℝ`,
the constrained two-replica free energy satisfies

  N⁻¹ E log Z_{N,s}^v ≤ gtFunctional β h q s lam v.
-/
theorem twoReplica_GT_bound
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s v : ℝ}
    (path : RSSmartPathDisorder Ω N β h q)
    (lam : ℝ)
    (hN : 0 < N)
    (hβ : 0 < β)
    (hh : 0 < h)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    expectedConstrainedFreeEnergy path s v ≤
      gtFunctional β h q s lam v := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hβ0 : 0 ≤ β := hβ.le
  have hh0 : 0 ≤ h := hh.le
  have hqpos : 0 < q := hq.1
  have hqlt : q < 1 := hq.2
  have hq0 : 0 ≤ q := hqpos.le
  have hq1 : q ≤ 1 := hqlt.le
  have h1q0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have h1qpos : 0 < 1 - q := sub_pos.mpr hqlt
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1s0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have htransport := constrained_log_partition_integral_eq_canonical
    (path := path) hN hs ⟨hq0, hq1⟩ hv
  have hInvN : 0 ≤ 1 / (N : ℝ) := (one_div_pos.mpr hNr).le
  have hcanonical :
      (∫ x, coupledConstrainedLogPartition N β h q s v x
          ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) ≤
        (N : ℝ) * gtFunctional β h q s lam v := by
    by_cases hrq : |v| < q
    · exact canonical_constrained_le_gtFunctional_of_abs_lt_q
        hN hs hq hv hrq
    · exact canonical_constrained_le_gtFunctional_of_q_le_abs
        hN hs hq hv (le_of_not_gt hrq)
  unfold expectedConstrainedFreeEnergy
  rw [htransport]
  calc
    (1 / (N : ℝ)) *
        (∫ x, coupledConstrainedLogPartition N β h q s v x
          ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) ≤
      (1 / (N : ℝ)) * ((N : ℝ) * gtFunctional β h q s lam v) :=
        mul_le_mul_of_nonneg_left hcanonical hInvN
    _ = gtFunctional β h q s lam v := by field_simp

end SpinGlass.AT
