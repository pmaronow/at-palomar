module

public import Targets.TalagrandRightZero
public import Targets.Section5LambdaUPrime

@[expose] public section

/-!
# The right-interval zero-lambda factor by exact reflection

At its baseline mass, the right paired split is exactly the next left paired
split with variance coordinate reversed. The mass arrays and sharing cutoff
coincide. Thus the existing full lambda family, and not just its value at zero,
can be reused. Its actual zero-lambda derivative is the reflected normalized
squared-slope factor. Zero masses and both variance endpoints are included.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- A finite split cascade depends only on the masses and the evaluated
variances of the levels it traverses. Parameter spaces may differ. -/
theorem splitScalarCascade_congr_at {P Q : Type*}
    (m m' : ℕ → ℝ) (v : ℕ → P → ℝ) (v' : ℕ → Q → ℝ)
    (d j : ℕ) (p : P) (q : Q)
    (hm : ∀ i < j, m i = m' i) (hv : ∀ i < j, v i p = v' i q) :
    splitScalarCascade m v d j p = splitScalarCascade m' v' d j q := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have he := ih (fun i hi => hm i (by omega)) (fun i hi => hv i (by omega))
    funext ℓ x
    simp only [splitScalarCascade, hm j (by omega), GTFrame.finiteStep]
    split_ifs <;> simp only [GTFrame.step0, GTFrame.stepM, hv j (by omega), he]

/-- The right baseline paired masses equal the next left baseline masses,
including the shared half-mass at the newly inserted level. -/
theorem section5RightMass_baseline_eq_next {k : ℕ} (s : RSBScheme k) (r p : ℕ) :
    section5RightMass s r (s.m r) p = section5Mass s (r + 1) (s.m r) p := by
  by_cases hlt : p < r
  · simp only [section5RightMass, section5Mass, if_pos hlt, if_pos (show p < r + 1 by omega)]
  · by_cases heq : p = r
    · subst p
      simp [section5RightMass, section5Mass]
    · by_cases heq' : p = r + 1
      · subst p
        simp [section5RightMass, section5Mass]
      · simp only [section5RightMass, section5Mass, if_neg hlt, if_neg heq,
          if_neg (show ¬p < r + 1 by omega), if_neg heq']

/-- The next left variance array is exactly the right variance array after
reflection in the total interval variance. No positivity premise is needed
for this algebraic identity. -/
theorem section5RightVariance_eq_reflected_next {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r p : ℕ) (v : ℝ) :
    section5RightVariance s β r p v = section5Variance s β (r + 1) p
      (β ^ 2 * (s.q (r + 1) - s.q r) - v) := by
  by_cases hlt : p < r
  · simp only [section5RightVariance, section5Variance, if_pos hlt,
      if_neg (show ¬r + 1 < p by omega), if_neg (show p ≠ r + 1 by omega),
      if_neg (show p + 1 ≠ r + 1 by omega)]
  · by_cases heq : p = r
    · subst p
      simp [section5RightVariance, section5Variance]
    · by_cases heq' : p = r + 1
      · subst p
        simp [section5RightVariance, section5Variance]
      · simp only [section5RightVariance, section5Variance, if_neg hlt, if_neg heq,
          if_neg heq', if_pos (show r + 1 < p by omega)]

/-- Full equality of the right baseline lambda family with the next left
family at reflected variance. This is stronger than a zero-lambda identity. -/
theorem section5RightV_baseline_eq_reflected_next {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k) (v : ℝ) :
    section5RightV s β h r (s.m r) v =
      section5V s β h (r + 1) (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) := by
  have hd : k + 3 - (r + 1) = k + 2 - r := by omega
  unfold section5RightV section5V
  rw [hd]
  have H := splitScalarCascade_congr_at
    (fun i => section5RightMass s r (s.m r) (k + 2 - i))
    (fun i => section5Mass s (r + 1) (s.m r) (k + 2 - i))
    (fun i => section5RightVariance s β r (k + 2 - i))
    (fun i => section5Variance s β (r + 1) (k + 2 - i))
    (k + 2 - r) (k + 3) v (β ^ 2 * (s.q (r + 1) - s.q r) - v)
    (fun i _ => section5RightMass_baseline_eq_next s r _)
    (fun i _ => section5RightVariance_eq_reflected_next s β r _ v)
  exact congrArg (fun F ℓ => F ℓ (h, h)) H

/-- The right baseline family's actual zero-lambda derivative is the
reflected next-level squared-slope factor, on the closed physical interval. -/
theorem hasDerivAt_section5RightV_zero_Q {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (section5RightV s β h r (s.m r) v)
      (section4TVarianceQ s β h (r + 1) (s.m r)
        (β ^ 2 * (s.q (r + 1) - s.q r) - v)) 0 := by
  rw [section5RightV_baseline_eq_reflected_next s β h hr]
  apply hasDerivAt_section5V_zero_Q s β h (by omega) (by omega)
    (s.m_nonneg (by omega))
  simp only [Nat.add_sub_cancel]
  exact ⟨sub_nonneg.mpr hv.2, sub_le_self _ hv.1⟩

/-- Numerical zero-lambda derivative, with differentiability already proved;
it is not a default value assigned at a nondifferentiable parameter. -/
theorem deriv_section5RightV_zero_eq_Q {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    deriv (section5RightV s β h r (s.m r) v) 0 =
      section4TVarianceQ s β h (r + 1) (s.m r)
        (β ^ 2 * (s.q (r + 1) - s.q r) - v) :=
  (hasDerivAt_section5RightV_zero_Q s β h hr hv).deriv

end SpinGlass.Targets
