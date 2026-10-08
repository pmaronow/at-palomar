module

public import Targets.ParisiStepStrictInterchange
public import Targets.ParisiCascadeSorting

@[expose] public section

/-!
# Regularity of scalar operator lists

The outer-first list representation preserves the same positive-Hessian
regularity as the indexed scalar cascade, even before the masses are sorted.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Actual derivatives exist throughout an unsorted scalar list. Variance
positivity is not needed for this regularity result. -/
theorem parisiListCascade_C2_pos (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, p.1 ∈ Set.Icc 0 1) {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hc'' : Continuous A'') (hpos : ∀ x, 0 < A'' x) :
    ∃ D E : ℝ → ℝ, HasParisiC2 (parisiListCascade L A) D E ∧
      Continuous E ∧ ∀ x, 0 < E x := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  induction L with
  | nil => exact ⟨A', A'', hC2, hc'', hpos⟩
  | cons p L ih =>
    have hp := hL p List.mem_cons_self
    obtain ⟨D, E, hDE, hcE, hE⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem p hq))
    have hB := parisiListCascade_props L hA hc.measurable
    have hcD : Continuous D := continuous_iff_continuousAt.mpr fun y => (hDE.2.1 y).continuousAt
    refine ⟨stepD1 (parisiListCascade L A) D p.1 p.2,
      stepD2 (parisiListCascade L A) D E p.1 p.2, ?_, ?_, ?_⟩
    · exact hasParisiC2_parisiStep_nonneg hp.1 hp.2 hDE hB.1 hB.2 hcD.measurable hcE.measurable
    · exact (continuous_parisiStep_variance_spatial hDE hcE hp.1).2.2.comp
        (continuous_const.prodMk continuous_id)
    · exact stepD2_pos hp.1 hB.1 hDE hB.2 hcD.measurable hcE.measurable hE

/-- The log-cosh terminal discharges all analytic assumptions on a finite
unsorted list, leaving only the physical mass bounds. -/
theorem parisiListCascade_logcosh_C2_pos (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, p.1 ∈ Set.Icc 0 1) :
    ∃ D E : ℝ → ℝ, HasParisiC2 (parisiListCascade L (fun x => Real.log (Real.cosh x))) D E ∧
      Continuous E ∧ ∀ x, 0 < E x :=
  parisiListCascade_C2_pos L hL hasLinearGrowth_log_cosh hasParisiC2_log_cosh
    (continuous_const.sub ((Real.continuous_sinh.div Real.continuous_cosh
      (fun x => (Real.cosh_pos x).ne')).pow 2)) log_cosh_second_pos

theorem continuous_parisiListCascade_logcosh (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, p.1 ∈ Set.Icc 0 1) :
    Continuous (parisiListCascade L (fun x => Real.log (Real.cosh x))) := by
  obtain ⟨D, E, hDE, _⟩ := parisiListCascade_logcosh_C2_pos L hL
  exact continuous_iff_continuousAt.mpr fun x => (hDE.1 x).continuousAt

/-- Strict adjacent interchange on any actual log-cosh scalar list suffix. -/
theorem parisiStep_interchange_parisiListCascade_strict (L : List (ℝ × ℝ))
    (hL : ∀ p ∈ L, p.1 ∈ Set.Icc 0 1)
    {m l a b : ℝ} (hm : m ∈ Set.Icc 0 1) (hl : 0 ≤ l) (hlm : l < m)
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    parisiStep m a (parisiStep l b (parisiListCascade L (fun x => Real.log (Real.cosh x)))) x <
      parisiStep l b (parisiStep m a (parisiListCascade L (fun x => Real.log (Real.cosh x)))) x := by
  obtain ⟨D, E, hDE, hcE, hE⟩ := parisiListCascade_logcosh_C2_pos L hL
  exact parisiStep_interchange_strict
    (hasLinearGrowth_parisiListCascade L hasLinearGrowth_log_cosh
      (Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')).measurable)
    hDE hcE hE hm hl hlm ha hb x

end SpinGlass.Targets
