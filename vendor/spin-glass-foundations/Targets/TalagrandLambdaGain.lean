module

/-
# The optimized scalar endpoint in Talagrand Section 5

Combine the proved uniform lambda curvature with the actual second-interpolation
endpoint. This is an unconditional endpoint gain, not the still-open bound on
the derivative of the second interpolation or Theorem 2.4.
-/
public import Targets.CoupledLambdaCurvature
public import Targets.TalagrandSection5Zero
public import Targets.TalagrandSecondInterpolation

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The lambda gain at the baseline mass, using the exact zero-lambda identity. -/
theorem section5V_baseline_lambda_gain {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (u : ℝ) :
    ∃ l : ℝ, section5V s β h r (s.m (r - 1)) v l - l * u ≤
      2 * parisiF s β (k + 2) h -
        (deriv (section5V s β h r (s.m (r - 1)) v) 0 - u) ^ 2 / 2 := by
  simpa only [section5V_zero_baseline s β h hr0 hr hv] using
    section5V_lambda_gain s β h hr (m := s.m (r - 1))
      ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ v u

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Equations (5.17), (5.19), and (5.33) combined for the actual interpolated pressure.
The remaining Theorem 3.1 bound is needed to transport this gain from time zero to one. -/
theorem section5Interpolation_zero_lambda_gain
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5Interpolation n s β h U r (s.m (r - 1)) t u 0 ≤
      2 * (Real.log 2 + parisiF s β (k + 2) h) -
        (deriv (section5V s β h r (s.m (r - 1)) (t * (β ^ 2 * (s.q r - u)))) 0 - u) ^ 2 / 2 := by
  obtain ⟨l, hl⟩ := section5V_baseline_lambda_gain s β h hr0 hr
    (section5SplitVariance_mem s β ht hu) u
  have H := section5Interpolation_zero_le hn s β h U hr0 hr (m := s.m (r - 1))
    (s.m_nonneg (by omega)) ht hu hu' l
  linarith

end SpinGlass.Targets
