module

public import Paper.RSFunctional
public import Paper.Targets
public import Paper.MomentBridge
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-!
# Conditional assembly of the replica-symmetry argument

This module checks the final argument with its unresolved mathematical inputs
visible in the theorem statement. `hJT` is the cited variational criterion,
`hTalagrand` is the cited physical free-energy limit, and `hu0` identifies the
PDE potential at the Dirac measure. None is introduced as a global axiom.
These theorems do not prove `MainReplicaSymmetryTarget`.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace Paper

/-- The sufficient half of Proposition 2.3, stated on actual probability
measures and their actual topological supports. This is an unproved input
predicate, not an asserted fact about arbitrary potentials or moments. -/
def VariationalCriterion (β h : ℝ) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (moments : ParisiMeasure → ℝ → ℝ) : Prop :=
  ∀ μ : ParisiMeasure,
    (∀ r ∈ (μ : Measure Overlap).support,
      ∀ t ∈ Icc (0 : ℝ) 1,
        parisiG β (moments μ) (r : ℝ) ≤ parisiG β (moments μ) t) →
    ∀ ν : ParisiMeasure, parisiFunctional β h u μ ≤ parisiFunctional β h u ν

/-- Sign estimates imply the Dirac minimizer once the variational criterion
has been supplied. The support calculation is proved, not assumed. -/
theorem dirac_minimizer_of_signs {β h q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (moments : ParisiMeasure → ℝ → ℝ)
    (hf : ContinuousOn (moments (diracOverlap q hq)) (Icc (0 : ℝ) 1))
    (hleft : ∀ t ∈ Icc (0 : ℝ) q, t ≤ moments (diracOverlap q hq) t)
    (hright : ∀ t ∈ Icc q (1 : ℝ), moments (diracOverlap q hq) t ≤ t)
    (hJT : VariationalCriterion β h u moments) :
    ∀ ν : ParisiMeasure,
      parisiFunctional β h u (diracOverlap q hq) ≤ parisiFunctional β h u ν := by
  apply hJT
  intro r hr t ht
  have hrq : (r : ℝ) = q := by
    rw [support_diracOverlap] at hr
    have he : r = (⟨q, hq⟩ : Overlap) := mem_singleton_iff.mp hr
    exact congrArg Subtype.val he
  rw [hrq]
  exact parisiG_minimum_of_signs hq hf hleft hright t ht

/-- A minimum at the Dirac measure makes the actual infimum equal to its
functional value. No compactness or hidden nonemptiness assumption is needed. -/
theorem parisi_infimum_eq_dirac {β h q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (hmin : ∀ ν : ParisiMeasure,
      parisiFunctional β h u (diracOverlap q hq) ≤ parisiFunctional β h u ν) :
    sInf (range (parisiFunctional β h u)) = parisiFunctional β h u (diracOverlap q hq) := by
  apply IsLeast.csInf_eq
  refine ⟨⟨diracOverlap q hq, rfl⟩, ?_⟩
  rintro y ⟨ν, rfl⟩
  exact hmin ν

/-- Physical free-energy conclusion conditional on the cited Parisi formula,
variational criterion, explicit PDE value, and proved moment signs. -/
theorem conditional_replica_symmetry_of_signs {β h q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (moments : ParisiMeasure → ℝ → ℝ)
    (hf : ContinuousOn (moments (diracOverlap q hq)) (Icc (0 : ℝ) 1))
    (hleft : ∀ t ∈ Icc (0 : ℝ) q, t ≤ moments (diracOverlap q hq) t)
    (hright : ∀ t ∈ Icc q (1 : ℝ), moments (diracOverlap q hq) t ≤ t)
    (hJT : VariationalCriterion β h u moments)
    (hu0 : u (diracOverlap q hq) 0 h = β ^ 2 / 2 * (1 - q) +
      gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z))))
    (hTalagrand : Tendsto (finiteSKFreeEnergy β h) atTop
      (𝓝 (sInf (range (parisiFunctional β h u))))) :
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q)) := by
  have hm := dirac_minimizer_of_signs hq u moments hf hleft hright hJT
  have hi := parisi_infimum_eq_dirac hq u hm
  rw [hi, parisiFunctional_dirac_eq_rsFreeEnergy hq u hu0] at hTalagrand
  exact hTalagrand

/-- The uniqueness argument of Remark 6.2, with the independently cited
minimizer-uniqueness theorem as an explicit assumption. -/
theorem parisi_minimizer_eq_dirac {β h q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (hdirac : ∀ ν : ParisiMeasure,
      parisiFunctional β h u (diracOverlap q hq) ≤ parisiFunctional β h u ν)
    (hunique : ∀ μ ν : ParisiMeasure,
      (∀ ρ : ParisiMeasure, parisiFunctional β h u μ ≤ parisiFunctional β h u ρ) →
      (∀ ρ : ParisiMeasure, parisiFunctional β h u ν ≤ parisiFunctional β h u ρ) → μ = ν)
    (μ : ParisiMeasure)
    (hμ : ∀ ν : ParisiMeasure, parisiFunctional β h u μ ≤ parisiFunctional β h u ν) :
    μ = diracOverlap q hq :=
  hunique μ (diracOverlap q hq) hμ hdirac

/-- The complete checked deterministic/Gaussian argument, with precisely the
remaining stochastic and cited variational inputs exposed. Unlike the simpler
sign-based assembly, its right-hand sign estimate is derived from the actual
Gaussian Doob transform, its proved decay, and Proposition 5.3.
-/
theorem conditional_replica_symmetry {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (u : ParisiMeasure → ℝ → ℝ → ℝ) (moments : ParisiMeasure → ℝ → ℝ)
    (hf : ContinuousOn (moments (diracOverlap q hq)) (Icc (0 : ℝ) 1))
    (hd : DifferentiableOn ℝ (moments (diracOverlap q hq)) (Ioo q 1))
    (hPoincare : ∀ t ∈ Icc (0 : ℝ) q,
      q - moments (diracOverlap q hq) t ≤ atParameter β h q * (q - t))
    (hLaw : ∀ t ∈ Icc q (1 : ℝ),
      moments (diracOverlap q hq) t = hardSecondMoment β h q t)
    (hIto : ∀ t ∈ Ioo q (1 : ℝ),
      deriv (moments (diracOverlap q hq)) t = β ^ 2 * hardFourthMoment β h q t)
    (hJT : VariationalCriterion β h u moments)
    (hu0 : u (diracOverlap q hq) 0 h = β ^ 2 / 2 * (1 - q) +
      gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z))))
    (hTalagrand : Tendsto (finiteSKFreeEnergy β h) atTop
      (𝓝 (sInf (range (parisiFunctional β h u))))) :
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q)) := by
  apply conditional_replica_symmetry_of_signs hq u moments hf
  · intro t ht
    exact left_sign_of_poincare_bound hAT ht.2 (hPoincare t ht)
  · have hfRight : ContinuousOn (moments (diracOverlap q hq)) (Icc q (1 : ℝ)) :=
      hf.mono (fun t ht => ⟨hq.1.trans ht.1, ht.2⟩)
    exact right_bound_of_doob_moment_inputs hβ hh hq hfixed hAT hfRight hd hLaw hIto
  · exact hJT
  · exact hu0
  · exact hTalagrand

end Paper
