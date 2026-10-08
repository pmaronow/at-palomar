module

public import Paper.ParisiJTFoundation
public import Paper.ParisiFirstVariation

@[expose] public section

/-! # Proposition 2.3, Remark 6.2, and the paper's PDE proof of Theorem 1.1

All ingredients concern the actual constructed Parisi PDE, canonical Brownian
state, probability-measure mixing path, and physical SK free energy. No
convexity, first-variation, uniqueness, or PDE/SDE identification premise
remains in the final theorems.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

/-- **Proposition 2.3.** The actual support characterization of minimizers. -/
theorem parisiJT_support_criterion (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) ↔
      (μ : Measure Overlap).support ⊆ overlapArgmin (fun q => selectedParisiG β h hβ μ q) :=
  parisiJT_support_criterion_of_actualFirstVariation β h hβ μ
    (fun ν => hasDerivWithinAt_parisiPDEFunctional_mix_G β h hβ μ ν)

/-- **Remark 6.2.** In the closed AT region the actual Parisi minimizer is
exactly the replica-symmetric Dirac law. The proof uses the strict minimum
of its actual G observable, without requiring strict functional convexity. -/
theorem parisiUniqueDirac {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    (∀ ν : ParisiMeasure, parisiPDEFunctional β h (diracOverlap q hq) ≤ parisiPDEFunctional β h ν) ∧
      ∀ μ : ParisiMeasure, (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) →
        μ = diracOverlap q hq :=
  parisiUniqueDirac_of_actualFirstVariation hβ hh hq hfixed hAT
    (fun ν => hasDerivWithinAt_parisiPDEFunctional_mix_G β h hβ.ne' (diracOverlap q hq) ν)

/-- **Theorem 1.1**, following the paper's PDE and variational proof route. -/
theorem replicaSymmetry_via_parisiPDE : MainReplicaSymmetryTarget :=
  replicaSymmetry_via_parisiPDE_of_actualFirstVariation
    (fun β h hβ μ ν => hasDerivWithinAt_parisiPDEFunctional_mix_G β h hβ μ ν)

end Paper
