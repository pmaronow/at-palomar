module

public import Targets.Section4RightVarianceFactor
public import Targets.Section5RightLambdaFactor
public import Targets.Section4RightFactor

@[expose] public section

/-!
# Equality of the actual right factor and its reflected baseline

Only the baseline mass is reflected: the two scalar mass arrays then agree
exactly, and the variance arrays agree by the existing reflection identity.
The normalized observable recursions are consequently equal at every depth.
The terminal interval requires no padding or minimality assumption here.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The scalar mass arrays coincide at baseline. This equality is not
asserted for the variable-mass right and left families. -/
theorem section4Mass_baseline_eq_next {k : ℕ} (s : RSBScheme k) (r p : ℕ) :
    section4Mass s r (s.m r) p = section4Mass s (r + 1) (s.m r) p := by
  by_cases hlt : p < r
  · simp only [section4Mass, if_pos hlt, if_pos (show p < r + 1 by omega)]
  · by_cases heq : p = r
    · subst p
      simp [section4Mass]
    · by_cases heq' : p = r + 1
      · subst p
        simp [section4Mass]
      · simp only [section4Mass, if_neg hlt, if_neg heq,
          if_neg (show ¬p < r + 1 by omega), if_neg heq']

/-- Every scalar prefix agrees after baseline reflection. No restriction on
the real variance coordinate is needed for this algebraic identity. -/
theorem section4RightCascade_baseline_eq_reflected_next {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r j : ℕ) (v : ℝ) :
    scalarFieldCascade (fun l => section4Mass s r (s.m r) (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) j =
    scalarFieldCascade (fun l => section4Mass s (r + 1) (s.m r) (k + 2 - l))
      (fun l => section5Variance s β (r + 1) (k + 2 - l)
        (β ^ 2 * (s.q (r + 1) - s.q r) - v)) j := by
  simp_rw [section4Mass_baseline_eq_next, section5RightVariance_eq_reflected_next]

/-- Equality of the entire normalized factor recursion at baseline, rather
than merely equality after multiplying by a vanishing mass gap. -/
theorem section4RightVarianceQ_baseline_eq_reflected_next {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4RightVarianceQ s β r (s.m r) j v x y =
      section4VarianceQ s β (r + 1) (s.m r) j
        (β ^ 2 * (s.q (r + 1) - s.q r) - v) x y := by
  have hi : k + 2 - (r + 1) = k + 1 - r := by omega
  induction j generalizing x y with
  | zero =>
    simp only [section4RightVarianceQ, section4VarianceQ, Nat.add_sub_cancel,
      hi, sub_sub_cancel]
  | succ j ih =>
    have he := funext fun x => funext fun y => ih x y
    simp only [section4RightVarianceQ, section4VarianceQ, hi,
      section4RightCascade_baseline_eq_reflected_next, he]

/-- The actual right normalized factor at the original mass is the reflected
factor used by the checked lambda and Hessian identities. The equality holds
for all real variances, including both physical endpoints and the terminal
interval. -/
theorem section4RightTVarianceQ_baseline_eq {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (_hr : r ≤ k + 1) {v : ℝ}
    (_hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section4RightTVarianceQ s β h r (s.m r) v = section4RightQ s β h r v := by
  simpa only [section4RightTVarianceQ, section4RightQ, section4TVarianceQ,
    Nat.add_sub_cancel] using
    section4RightVarianceQ_baseline_eq_reflected_next s β r r v 0 (fun _ => h)

end SpinGlass.Targets
