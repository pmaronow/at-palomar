module

public import Targets.Section4MassDerivative
public import Targets.Section4InsertedScheme

@[expose] public section

/-!
# The actual first variation in Talagrand (4.46)

The checked mass derivative of the full scalar recursion identifies the first
variation of the actual inserted Parisi functional. This does not yet assert
the mixed mass/variance identities or the quantitative stationarity bounds.
-/

open Real

namespace SpinGlass.Targets

/-- Talagrand's first variation (4.46), with the actual `U` of (4.42). -/
noncomputable def section4FirstVariation {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4U s β h r (β ^ 2 * (s.q r - u)) / 2 -
    β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2)

/-- The first variation is the genuine baseline mass derivative of `Φ`,
including zero baseline mass and both overlap endpoints. -/
theorem hasDerivAt_section4Phi_mass_baseline {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivAt (fun m => section4Phi s β h r m u)
      (section4FirstVariation s β h r u) (s.m (r - 1)) := by
  have hv := section5SplitVariance_mem s β (t := 1)
    (by constructor <;> norm_num) hu
  simp only [one_mul] at hv
  have hT := hasDerivAt_section4T_mass_baseline s β h hr0 hr hv
  have hC := ((hasDerivAt_id (s.m (r - 1))).const_sub (s.m (r - 1))).mul_const
    (β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2))
  simpa [section4Phi, section4FirstVariation, sub_eq_add_neg] using!
    ((hT.const_add (Real.log 2)).sub_const (parisiCorrection s β)).add hC

/-- At the original upper overlap, the actual first variation vanishes. -/
theorem section4FirstVariation_at_upper_overlap {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4FirstVariation s β h r (s.q r) = 0 := by
  simp [section4FirstVariation, section4U_zero_variance s β h hr0 hr]

end SpinGlass.Targets
