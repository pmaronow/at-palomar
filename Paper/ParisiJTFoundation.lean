module

public import Paper.ParisiSelectedGFubini
public import Paper.ParisiMixConvexity
public import Paper.ParisiDiracIdentification
public import Paper.ParisiPDEFormula
public import Paper.Targets

@[expose] public section

/-! # Final JT assembly for the actual PDE functional and actual state

This module proves the assembly steps with the single actual first-variation
identity explicit. Its unconditional proof is supplied by ParisiFirstVariation.
Convexity, observable continuity, strict Dirac G minima, and the physical
free-energy formula are already actual closed theorems.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem parisiJT_support_criterion_of_actualFirstVariation (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure)
    (hd : ∀ ν : ParisiMeasure,
      HasDerivWithinAt (fun θ => parisiPDEFunctional β h (parisiMix μ ν θ))
        ((∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
          (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap)))
        (Ioi (0 : ℝ)) 0) :
    (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) ↔
      (μ : Measure Overlap).support ⊆ overlapArgmin (fun q => selectedParisiG β h hβ μ q) :=
  jt_support_criterion_of_firstVariation (parisiPDEFunctional β h) μ
    (fun q => selectedParisiG β h hβ μ q) (continuous_selectedParisiG_overlap β h hβ μ)
    (fun ν => convexOn_parisiPDEFunctional_mix β h μ ν) hd

theorem selectedParisiG_dirac_strict_minimum {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ y : Overlap, y ≠ ⟨q, hq⟩ →
      selectedParisiG β h hβ.ne' (diracOverlap q hq) q <
        selectedParisiG β h hβ.ne' (diracOverlap q hq) y := by
  intro y hy
  have hle := selectedParisiG_dirac_minimum hβ hh hq hfixed hAT y y.property
  apply lt_of_le_of_ne hle
  intro he
  have hv := (selectedParisiG_dirac_eq_minimum_iff hβ hh hq hfixed hAT y.property).mp he.symm
  exact hy (Subtype.ext hv)

/-- The actual AT-region strict G minimum gives a unique Dirac minimizer;
no strict convexity of the PDE functional is assumed. -/
theorem parisiUniqueDirac_of_actualFirstVariation {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hd : ∀ ν : ParisiMeasure,
      HasDerivWithinAt (fun θ => parisiPDEFunctional β h (parisiMix (diracOverlap q hq) ν θ))
        ((∫ y : Overlap, selectedParisiG β h hβ.ne' (diracOverlap q hq) y ∂(ν : Measure Overlap)) -
          (∫ y : Overlap, selectedParisiG β h hβ.ne' (diracOverlap q hq) y
            ∂(diracOverlap q hq : Measure Overlap))) (Ioi (0 : ℝ)) 0) :
    (∀ ν : ParisiMeasure, parisiPDEFunctional β h (diracOverlap q hq) ≤ parisiPDEFunctional β h ν) ∧
      ∀ μ : ParisiMeasure, (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) →
        μ = diracOverlap q hq := by
  apply jt_unique_dirac_minimizer_of_firstVariation (parisiPDEFunctional β h) ⟨q, hq⟩
    (fun y => selectedParisiG β h hβ.ne' (diracOverlap q hq) y)
    (continuous_selectedParisiG_overlap β h hβ.ne' (diracOverlap q hq))
    (selectedParisiG_dirac_strict_minimum hβ hh hq hfixed hAT)
    (fun ν => convexOn_parisiPDEFunctional_mix β h (diracOverlap q hq) ν)
  intro ν
  simpa only [diracOverlap, Measure.toProbabilityMeasure, ProbabilityMeasure.toMeasure,
    integral_dirac] using hd ν

theorem parisiPDEValue_eq_of_minimizer (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) :
    parisiPDEValue β h = parisiPDEFunctional β h μ := by
  apply le_antisymm
  · exact csInf_le (bddBelow_parisiPDESet β hβ h) ⟨μ, rfl⟩
  · apply le_csInf (parisiPDESet_nonempty β h)
    rintro r ⟨ν, rfl⟩
    exact hmin ν

/-- The paper's proof route: actual strict Dirac G minimum, actual JT
variational derivative, and the all-measure Parisi formula give replica symmetry. -/
theorem replicaSymmetry_via_parisiPDE_of_actualFirstVariation
    (hd : ∀ (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure),
      HasDerivWithinAt (fun θ => parisiPDEFunctional β h (parisiMix μ ν θ))
        ((∫ y : Overlap, selectedParisiG β h hβ μ y ∂(ν : Measure Overlap)) -
          (∫ y : Overlap, selectedParisiG β h hβ μ y ∂(μ : Measure Overlap)))
        (Ioi (0 : ℝ)) 0) : MainReplicaSymmetryTarget := by
  intro β h q hβ hh hq hfixed hAT
  have hmin := (parisiUniqueDirac_of_actualFirstVariation hβ hh hq hfixed hAT
    (hd β h hβ.ne' (diracOverlap q hq))).1
  have hv := parisiPDEValue_eq_of_minimizer β h hβ.ne' (diracOverlap q hq) hmin
  rw [parisiPDEFunctional_dirac_eq_rsFreeEnergy β h q hβ hq] at hv
  simpa only [hv] using physicalParisiFormula β h hβ

end Paper
