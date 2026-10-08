module

public import Paper.SoftMoment
public import Paper.DoobDifferentiation

@[expose] public section

/-!
# Concrete RS second moment and its variational minimum

The pre-interface Gaussian conditional second moment and the post-interface
Gaussian Doob second moment are assembled into a continuous real function.
Gaussian Poincaré, Gaussian heat differentiation, and the moment comparison
prove its two signs and the minimum of the actual variational integral.
No Poincaré, Itô, transition-law, or regularity hypothesis is assumed here.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace Paper

/-- The concrete analytic RS second moment, using the soft Gaussian expression
before the interface and the normalized Doob expression after it. -/
def rsSecondMoment (β h q t : ℝ) : ℝ :=
  if t ≤ q then softSecondMoment β h q t else hardSecondMoment β h q t

/-- Before and at the interface, the RS moment is the actual soft moment. -/
theorem rsSecondMoment_eq_soft {β h q t : ℝ} (ht : t ≤ q) :
    rsSecondMoment β h q t = softSecondMoment β h q t := by
  simp [rsSecondMoment, ht]

/-- Strictly after the interface, the RS moment is the actual hard moment. -/
theorem rsSecondMoment_eq_hard {β h q t : ℝ} (ht : q < t) :
    rsSecondMoment β h q t = hardSecondMoment β h q t := by
  simp [rsSecondMoment, not_le_of_gt ht]

/-- The two actual moment formulas agree at the interface. -/
theorem rs_moments_match (β h q : ℝ) (hq : 0 ≤ q) :
    softSecondMoment β h q q = hardSecondMoment β h q q := by
  rw [softSecondMoment_interface, hardSecondMoment_initial hq]

/-- The hard expression also represents the RS moment at the interface. -/
theorem rsSecondMoment_eq_hard_of_le {β h q t : ℝ} (hq : 0 ≤ q) (ht : q ≤ t) :
    rsSecondMoment β h q t = hardSecondMoment β h q t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [rsSecondMoment_eq_soft le_rfl, rs_moments_match β h q hq]
  · exact rsSecondMoment_eq_hard h

/-- The RS moment is continuous, including at the matching interface. -/
theorem continuous_rsSecondMoment (β h q : ℝ) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    Continuous (rsSecondMoment β h q) := by
  apply Continuous.if_le (continuous_softSecondMoment β h q hβ)
    (continuous_hardSecondMoment β h q) continuous_id continuous_const
  intro t ht
  change t = q at ht
  subst t
  exact rs_moments_match β h q hq

@[simp] theorem rsSecondMoment_interface (β h q : ℝ) :
    rsSecondMoment β h q q = overlapMap β h q := by
  rw [rsSecondMoment_eq_soft le_rfl, softSecondMoment_interface]

/-- The actual interface moment equals the selected RS fixed point. -/
theorem rsSecondMoment_interface_fixed {β h q : ℝ}
    (hfixed : q = overlapMap β h q) : rsSecondMoment β h q q = q := by
  rw [rsSecondMoment_interface, ← hfixed]

/-- The original left-hand sign is proved for the concrete RS moment. -/
theorem rsSecondMoment_left_sign {β h q t : ℝ}
    (hβ : 0 ≤ β) (ht : t ∈ Icc (0 : ℝ) q)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    t ≤ rsSecondMoment β h q t := by
  rw [rsSecondMoment_eq_soft ht.2]
  exact softSecondMoment_left_sign hβ ht hfixed hAT

/-- The original right-hand sign is proved for the concrete RS moment. -/
theorem rsSecondMoment_right_sign {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc q (1 : ℝ)) : rsSecondMoment β h q t ≤ t := by
  rw [rsSecondMoment_eq_hard_of_le hq.1 ht.1]
  exact hardSecondMoment_le_time hβ hh hq hfixed hAT t ht

/-- Strictness after the interface in the small-mean regime is inherited by
the concrete RS moment. -/
theorem rsSecondMoment_right_strict_of_small_field {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hfield : h ≤ β ^ 2 * q) (ht : t ∈ Ioc q (1 : ℝ)) :
    rsSecondMoment β h q t < t := by
  rw [rsSecondMoment_eq_hard ht.1]
  exact hardSecondMoment_lt_time_of_small_field hβ hh hq hfixed hAT hfield t ht

/-- The actual variational function `G` for the assembled Gaussian RS moment. -/
def rsParisiG (β h q t : ℝ) : ℝ := parisiG β (rsSecondMoment β h q) t

/-- The concrete variational integral has its global minimum at the RS overlap,
under the original parameter, fixed-point, and AT assumptions alone. -/
theorem rsParisiG_minimum {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, rsParisiG β h q q ≤ rsParisiG β h q t := by
  apply parisiG_minimum_of_signs hq
    (continuous_rsSecondMoment β h q hβ.le hq.1).continuousOn
  · intro t ht
    exact rsSecondMoment_left_sign hβ.le ht hfixed hAT
  · intro t ht
    exact rsSecondMoment_right_sign hβ hh hq hfixed hAT ht

/-- The concrete RS variational integral decreases up to the interface. -/
theorem rsParisiG_antitoneOn {β h q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    AntitoneOn (rsParisiG β h q) (Icc (0 : ℝ) q) := by
  apply parisiG_antitoneOn (by constructor <;> norm_num) hq
    (continuous_rsSecondMoment β h q hβ.le hq.1).continuousOn
  intro t ht
  exact rsSecondMoment_left_sign hβ.le ht hfixed hAT

/-- The concrete RS variational integral increases after the interface. -/
theorem rsParisiG_monotoneOn {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    MonotoneOn (rsParisiG β h q) (Icc q (1 : ℝ)) := by
  apply parisiG_monotoneOn hq (by constructor <;> norm_num)
    (continuous_rsSecondMoment β h q hβ.le hq.1).continuousOn
  intro t ht
  exact rsSecondMoment_right_sign hβ hh hq hfixed hAT ht

end Paper
