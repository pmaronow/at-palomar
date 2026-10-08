module

public import Targets.Section5RightMassGain
public import Targets.Section5LocalRight

@[expose] public section

/-!
# Right-interval mass-or-lambda improvement

The lambda estimate already improves the actual constrained free energy
unless its squared-slope factor equals the specified overlap. In the equality
case a negative corrected mass derivative gives the improvement instead.
The deficit is chosen from the scalar construction before the system size
and disorder. Proving that derivative sign from optimality is a separate step.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The actual right mass-or-lambda dichotomy, with a deficit independent of
system size. The only remaining scalar input is the mass derivative sign in
the zero-lambda-slope case. -/
theorem exists_constrainedPhi_right_scalar_gain_uniform_in_size
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hD : section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) = u →
      section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
        t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) < 0) :
    ∃ c > 0, ∀ {n : ℕ} (_hn : 0 < n) (sk : SKDisorder (Ω := Ω) n β h),
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - c := by
  by_cases hQ : section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) = u
  · exact exists_constrainedPhi_right_mass_gap_uniform_in_size s β h hr0 hr hmpos ht hu
      (hD hQ)
  · refine ⟨(section5RightSlope s β h r t u) ^ 2 / 2, ?_, ?_⟩
    · exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num)
    · intro n hn sk hpair
      letI := hpair
      exact constrainedPhi_le_two_guerraPsi_sub_right_factor_sq hn s β h sk hr0 hr ht hu

end SpinGlass.Targets
