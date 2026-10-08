module

public import Paper.DoobDifferentiation
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-!
# One-sided derivatives of the actual Gaussian hard moments

Continuity of the second moment and of its proved interior derivative extends
that derivative to the breakpoint from the right. No new heat expansion or Itô
hypothesis is needed. The clipped extension has a different derivative to the
left of the breakpoint, so the endpoint statement uses the correct one-sided
notion.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace Paper

/-- The actual hard moment has its expected right derivative at the breakpoint. -/
theorem hasDerivWithinAt_hardSecondMoment_interface (β h q : ℝ) :
    HasDerivWithinAt (hardSecondMoment β h q) (β ^ 2 * hardFourthMoment β h q q) (Ici q) q := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi q)
  · exact fun t ht => (hasDerivAt_hardSecondMoment β h q ht).differentiableAt.differentiableWithinAt
  · exact (continuous_hardSecondMoment β h q).continuousAt.continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hl := ((continuous_hardFourthMoment β h q).const_mul (β ^ 2)).continuousAt.tendsto.mono_left
      (show 𝓝[>] q ≤ 𝓝 q from nhdsWithin_le_nhds)
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin (s := Ioi q) (a := q)] with t ht
    exact (deriv_hardSecondMoment β h q ht).symm

/-- The right derivative at the breakpoint is the literal AT parameter. -/
theorem hasDerivWithinAt_hardSecondMoment_interface_AT (β h q : ℝ) (hq : 0 ≤ q) :
    HasDerivWithinAt (hardSecondMoment β h q) (atParameter β h q) (Ici q) q := by
  simpa only [hardFourthMoment_initial hq] using hasDerivWithinAt_hardSecondMoment_interface β h q

/-- The derivative identity holds on the entire closed post-breakpoint half-line. -/
theorem hasDerivWithinAt_hardSecondMoment_closed (β h q : ℝ) {t : ℝ} (ht : q ≤ t) :
    HasDerivWithinAt (hardSecondMoment β h q) (β ^ 2 * hardFourthMoment β h q t) (Ici q) t := by
  rcases ht.eq_or_lt with he | he
  · subst t
    exact hasDerivWithinAt_hardSecondMoment_interface β h q
  · exact (hasDerivAt_hardSecondMoment β h q he).hasDerivWithinAt

theorem derivWithin_hardSecondMoment_closed (β h q : ℝ) {t : ℝ} (ht : q ≤ t) :
    derivWithin (hardSecondMoment β h q) (Ici q) t = β ^ 2 * hardFourthMoment β h q t :=
  (hasDerivWithinAt_hardSecondMoment_closed β h q ht).derivWithin
    (uniqueDiffOn_Ici q t ht)

/-- The actual one-sided derivative is continuous up to the breakpoint. -/
theorem continuousOn_derivWithin_hardSecondMoment_closed (β h q : ℝ) :
    ContinuousOn (derivWithin (hardSecondMoment β h q) (Ici q)) (Ici q) := by
  apply ((continuous_hardFourthMoment β h q).const_mul (β ^ 2)).continuousOn.congr
  intro t ht
  exact derivWithin_hardSecondMoment_closed β h q ht

/-- At time one the left derivative is the same actual fourth-moment coefficient. -/
theorem hasDerivWithinAt_hardSecondMoment_terminal (β h q : ℝ) (hq : q < 1) :
    HasDerivWithinAt (hardSecondMoment β h q) (β ^ 2 * hardFourthMoment β h q 1) (Iic 1) 1 :=
  (hasDerivAt_hardSecondMoment β h q hq).hasDerivWithinAt

/-- Endpoint transport for a physical moment agreeing with the actual Gaussian moment. -/
theorem hasDerivWithinAt_physicalMoment_interface {β h q : ℝ} (hq : q < 1)
    {m : ℝ → ℝ} (hm : EqOn m (hardSecondMoment β h q) (Icc q (1 : ℝ))) :
    HasDerivWithinAt m (β ^ 2 * hardFourthMoment β h q q) (Ici q) q := by
  apply (hasDerivWithinAt_hardSecondMoment_interface β h q).congr_of_eventuallyEq
  · exact Filter.eventuallyEq_of_mem (Icc_mem_nhdsGE hq) hm
  · exact hm ⟨le_rfl, hq.le⟩

/-- The hard moment is C¹ on the entire closed post-breakpoint interval. -/
theorem contDiffOn_hardSecondMoment_closed (β h q : ℝ) :
    ContDiffOn ℝ 1 (hardSecondMoment β h q) (Ici q) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici q)]
  exact ⟨fun t ht => (hasDerivWithinAt_hardSecondMoment_closed β h q ht).differentiableWithinAt,
    continuousOn_derivWithin_hardSecondMoment_closed β h q⟩

/-- Transport of the left terminal derivative to a literal physical moment. -/
theorem hasDerivWithinAt_physicalMoment_terminal {β h q : ℝ} (hq : q < 1)
    {m : ℝ → ℝ} (hm : EqOn m (hardSecondMoment β h q) (Icc q (1 : ℝ))) :
    HasDerivWithinAt m (β ^ 2 * hardFourthMoment β h q 1) (Iic 1) 1 := by
  apply (hasDerivWithinAt_hardSecondMoment_terminal β h q hq).congr_of_eventuallyEq
  · exact Filter.eventuallyEq_of_mem (Icc_mem_nhdsLE hq) hm
  · exact hm ⟨hq.le, le_rfl⟩

end Paper
