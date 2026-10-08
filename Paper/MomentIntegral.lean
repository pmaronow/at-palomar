module

public import Paper.MomentEndpoints
public import Paper.ParisiDiracIdentification
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! The genuine integrated post-interface second-moment identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace Paper

/-- Integrating the proved interior derivative recovers the actual hard
moment at every post-interface time, including the interface itself. -/
theorem hardSecondMoment_eq_initial_add_integral (β h q t : ℝ) (ht : q ≤ t) :
    hardSecondMoment β h q t = hardSecondMoment β h q q +
      β ^ 2 * ∫ s in q..t, hardFourthMoment β h q s := by
  have hi : IntervalIntegrable (fun s => β ^ 2 * hardFourthMoment β h q s) volume q t :=
    ((continuous_hardFourthMoment β h q).const_mul (β ^ 2)).intervalIntegrable _ _
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (continuous_hardSecondMoment β h q).continuousOn
    (fun s hs => hasDerivAt_hardSecondMoment β h q hs.1) hi
  rw [intervalIntegral.integral_const_mul] at hf
  linarith

theorem hardSecondMoment_eq_fixedPoint_add_integral {β h q t : ℝ}
    (hq : 0 ≤ q) (hfixed : q = overlapMap β h q) (ht : q ≤ t) :
    hardSecondMoment β h q t = q + β ^ 2 * ∫ s in q..t, hardFourthMoment β h q s := by
  rw [hardSecondMoment_eq_initial_add_integral β h q t ht,
    hardSecondMoment_initial_fixed hq hfixed]

/-- The integrated identity for the literal constructed Brownian state.
Both moment laws were proved; no stochastic moment identity is supplied. -/
theorem physicalHardSecondMoment_eq_fixedPoint_add_integral {β h q t : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    physicalHardSecondMoment β h q hq t = q + β ^ 2 *
      ∫ s in q..t, physicalHardFourthMoment β h q hq s := by
  rw [physicalHardSecondMoment_eq β h q hq ht,
    hardSecondMoment_eq_fixedPoint_add_integral hq.1 hfixed ht.1]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact (physicalHardFourthMoment_eq β h q hq ⟨hs.1, hs.2.trans ht.2⟩).symm

theorem canonicalDiracState_secondMoment_eq_fixedPoint_add_integral {β h q t : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    (∫ omega, Real.tanh (canonicalDiracStateReal β h q hq omega t) ^ 2
      ∂canonicalBrownianMeasure) = q + β ^ 2 * ∫ s in q..t,
        (∫ omega, sech (canonicalDiracStateReal β h q hq omega s) ^ 4
          ∂canonicalBrownianMeasure) :=
  physicalHardSecondMoment_eq_fixedPoint_add_integral hq hfixed ht

/-- The actual PDE-selected Dirac second moment satisfies the same exact
integral formula, with the actual Dirac state's fourth moment. -/
theorem selectedParisiSecondMoment_dirac_eq_fixedPoint_add_integral {β h q t : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q)
    (ht : t ∈ Icc q (1 : ℝ)) :
    selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t = q + β ^ 2 *
      ∫ s in q..t, physicalHardFourthMoment β h q hq s := by
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩,
    physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1, ht.2⟩,
    rsSecondMoment_eq_hard_of_le hq.1 ht.1,
    hardSecondMoment_eq_fixedPoint_add_integral hq.1 hfixed ht.1]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact (physicalHardFourthMoment_eq β h q hq ⟨hs.1, hs.2.trans ht.2⟩).symm

end Paper
