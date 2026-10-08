module

public import Paper.ParisiWeakMild
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

/-! # Almost-everywhere uniqueness of the weak spatial gradient

The weak solution class does not select values of the measurable gradient
on null sets.  The uniqueness theorem below has the mathematically correct
almost-everywhere conclusion.
-/

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem ae_parisiSpaceTime_openStrip :
    ∀ᵐ p : ℝ × ℝ ∂parisiSpaceTime, 0 < p.1 ∧ p.1 < 1 := by
  unfold parisiSpaceTime
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_fst measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact .of_forall fun _ => ht

theorem locallyIntegrable_of_ae_bounded_parisiSpaceTime (v : ℝ × ℝ → ℝ)
    (hv : AEStronglyMeasurable v parisiSpaceTime) (M : ℝ)
    (hb : ∀ᵐ p ∂parisiSpaceTime, ‖v p‖ ≤ M) : LocallyIntegrable v parisiSpaceTime := by
  apply (locallyIntegrable_const (μ := parisiSpaceTime) M).mono hv
  filter_upwards [hb] with p hp
  exact hp.trans (le_abs_self M)

/-- Two bounded measurable distributional gradients of the same potential
coincide almost everywhere on the actual Parisi time-space strip. -/
theorem parisiWeakGradient_ae_unique (u v w : ℝ × ℝ → ℝ)
    (hv : IsParisiWeakGradient u v) (hw : IsParisiWeakGradient u w)
    (hvm : AEStronglyMeasurable v parisiSpaceTime)
    (hwm : AEStronglyMeasurable w parisiSpaceTime)
    (M K : ℝ) (hvb : ∀ᵐ p ∂parisiSpaceTime, ‖v p‖ ≤ M)
    (hwb : ∀ᵐ p ∂parisiSpaceTime, ‖w p‖ ≤ K) : v =ᵐ[parisiSpaceTime] w := by
  have hvl := locallyIntegrable_of_ae_bounded_parisiSpaceTime v hvm M hvb
  have hwl := locallyIntegrable_of_ae_bounded_parisiSpaceTime w hwm K hwb
  let U : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < 1}
  have hU : IsOpen U := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hvl.sub hwl).locallyIntegrableOn U) (fun φ hφ hc hsupp => by
      obtain ⟨hi, he⟩ := hv φ hφ hc hsupp
      obtain ⟨hj, hf⟩ := hw φ hφ hc hsupp
      calc
        (∫ p, φ p • (v p - w p) ∂parisiSpaceTime) =
            ∫ p, (u p * parisiTestX φ p + v p * φ p) -
              (u p * parisiTestX φ p + w p * φ p) ∂parisiSpaceTime := by
          apply integral_congr_ae
          exact .of_forall fun p => by simp only [smul_eq_mul]; ring
        _ = 0 := by rw [integral_sub hi hj, he, hf, sub_self])
  filter_upwards [hz, ae_parisiSpaceTime_openStrip] with p hp hstrip
  exact sub_eq_zero.mp (hp hstrip)

theorem IsParisiWeakSolution.gradient_ae_unique {β : ℝ} {μ : ParisiMeasure}
    {u v w : ℝ × ℝ → ℝ} (hv : IsParisiWeakSolution β μ u v)
    (hw : IsParisiWeakSolution β μ u w) : v =ᵐ[parisiSpaceTime] w := by
  obtain ⟨M, hM⟩ := hv.bounded_gradient
  obtain ⟨K, hK⟩ := hw.bounded_gradient
  exact parisiWeakGradient_ae_unique u v w hv.weak_gradient hw.weak_gradient
    hv.measurable_gradient hw.measurable_gradient M K hM hK

end Paper
