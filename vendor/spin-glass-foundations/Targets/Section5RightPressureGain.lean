module

public import Targets.Section5InterpolationBound
public import Targets.TalagrandRightZero

@[expose] public section

/-!
# The actual right-interval pressure gain

The proved right-interpolation endpoint bound and optimized lambda estimate
combine at baseline mass `m_r`. Their original correction cancels to give a
bound relative to `2 ψ(t)`, with the squared error in the actual right lambda
derivative. The local comparison with `u - q_r` is proved separately in
`Section5LocalRight` and `Section5RightBoundary`; the far-right mass variation
is treated in `Section5FarRight`.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The right lambda optimization gives an actual constrained-pressure gain
relative to `2 ψ(t)`. Both time endpoints and repeated overlap levels are allowed. -/
theorem constrainedPhi_le_guerraPsi_right_lambda_gain
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (deriv (section5RightV s β h r (s.m r)
          (t * (β ^ 2 * (u - s.q r)))) 0 - u) ^ 2 / 2 := by
  have hm : s.m r ∈ Set.Icc (s.m (r - 1)) (2 * s.m r) :=
    ⟨s.m_mono' r hr (r - 1) (by omega), by linarith [s.m_nonneg hr]⟩
  have H := section5RightInterpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  simp only [sub_self, zero_mul, add_zero] at H
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have G := section5RightInterpolation_zero_lambda_gain hn s β h sk.U hr ht hu
    ⟨p.1.1, p.1.2, p.2⟩
  unfold guerraPsi
  linarith

/-- In particular the actual constrained pressure is at most `2 ψ(t)` on
the right interval, without any optimality or stationarity hypothesis. -/
theorem constrainedPhi_le_guerraPsi_right
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t := by
  have H := constrainedPhi_le_guerraPsi_right_lambda_gain hn s β h sk hr0 hr ht hu
  exact H.trans (sub_le_self _ (div_nonneg (sq_nonneg _) (by norm_num)))

/-- A nonzero error in the actual right lambda derivative gives strict
improvement. No identity between this derivative and a scalar `U'` is assumed. -/
theorem constrainedPhi_lt_guerraPsi_right_of_lambda_deriv_ne
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)]
    (hderiv : deriv (section5RightV s β h r (s.m r)
      (t * (β ^ 2 * (u - s.q r)))) 0 ≠ u) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  have H := constrainedPhi_le_guerraPsi_right_lambda_gain hn s β h sk hr0 hr ht hu
  exact H.trans_lt (sub_lt_self _ (div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hderiv))
    (by norm_num)))

end SpinGlass.Targets
