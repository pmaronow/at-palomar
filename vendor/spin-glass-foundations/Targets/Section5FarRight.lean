module

public import Targets.Section5RightScalarGain
public import Targets.Section4RightConvexity
public import Targets.Section5FarLeft

@[expose] public section

/-!
# The far-right strict improvement of Proposition 5.6

Quantitative optimality bounds the actual right first variation from above.
The convex supporting line makes the corrected mass derivative negative when
the lambda slope vanishes and the overlap is sufficiently far from the original
level. The actual mass-or-lambda dichotomy then supplies a positive deficit
chosen before the system size and disorder. The terminal mass one is included.
The beta-only smallness constant and arithmetic are reused from the far-left
case. Compactness over time and overlap is not asserted here.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A sufficiently large right overlap gap gives an actual pressure deficit
independent of the system size, using only the original scheme's optimality. -/
theorem exists_constrainedPhi_right_gap_uniform_in_size
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (u - s.q r) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ} (_hn : 0 < n) (sk : SKDisorder (Ω := Ω) n β h),
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - c := by
  have hmpos : 0 < s.m r := (s.m_nonneg (by omega : r - 1 ≤ k + 1)).trans_lt hgap
  apply exists_constrainedPhi_right_scalar_gain_uniform_in_size s β h hr0 hr hmpos ht hu
  intro hQ
  have hf := section4RightFirstVariation_upper_bound s β h ε hr0 hr hgap hu hmin hnear
  have H := section4RightU_interpolation_slope_upper_bound_of_factor_eq s β h hr hmpos
    hu ht hQ hf
  linarith

/-- Pointwise strict right improvement under the quantitative overlap-gap
condition, including the first and terminal physical intervals. -/
theorem constrainedPhi_lt_two_guerraPsi_of_right_gap
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hgap : s.m (r - 1) < s.m r)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (u - s.q r) ^ 2) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  obtain ⟨c, hc, H⟩ := exists_constrainedPhi_right_gap_uniform_in_size (Ω := Ω)
    s β h ε hr0 hr hgap ht hu hmin hnear hsmall
  exact (H hn sk inferInstance).trans_lt (sub_lt_self _ hc)

/-- Proposition 5.6's far-right smallness condition yields a positive
deficit chosen before system size. The same beta-only constant as the far-left
case suffices, with no quantitative lower bound on the mass gap. -/
theorem exists_constrainedPhi_far_right_uniform_in_size
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {L₁ t₀ t u : ℝ} (hβ : β ≠ 0) (hL : 0 < L₁) (ht₀ : t₀ < 1)
    (ht : t ∈ Set.Icc 0 t₀) (hgap : s.m (r - 1) < s.m r)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (u - s.q r))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ} (_hn : 0 < n) (sk : SKDisorder (Ω := Ω) n β h),
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - c := by
  exact exists_constrainedPhi_right_gap_uniform_in_size s β h ε hr0 hr hgap
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu hmin hnear
    (section5FarLeft_smallness hβ hL ht₀ ht.2 hfar hsmall)

/-- The far-right strict improvement of Proposition 5.6 in the project's
exact-covariance SK setting. All physical levels of a reduced scheme satisfy
the strict mass-gap hypothesis; no adjacent overlap gap is assumed. -/
theorem constrainedPhi_lt_two_guerraPsi_of_far_right
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {L₁ t₀ t u : ℝ}
    (hβ : β ≠ 0) (hL : 0 < L₁) (ht₀ : t₀ < 1) (ht : t ∈ Set.Icc 0 t₀)
    (hgap : s.m (r - 1) < s.m r) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hfar : 1 - t₀ ≤ L₁ * (u - s.q r))
    (hsmall : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) * ((1 - t₀) / L₁) ^ 2) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  obtain ⟨c, hc, H⟩ := exists_constrainedPhi_far_right_uniform_in_size (Ω := Ω)
    s β h ε hr0 hr hβ hL ht₀ ht hgap hu hmin hnear hfar hsmall
  exact (H hn sk inferInstance).trans_lt (sub_lt_self _ hc)

end SpinGlass.Targets
