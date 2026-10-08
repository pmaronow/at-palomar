module

public import Paper.ParisiWeakSelected

@[expose] public section

/-! # The correct space for literal uniqueness of weak Parisi potentials

The weak equation specifies a continuous potential on the closed time strip.
Its values outside that strip and the values of its measurable gradient on
null sets are not part of the specified solution. Continuous maps on the
strip express literal uniqueness without selecting either irrelevant datum.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace Paper

abbrev ParisiPotentialSpace := C((Icc (0 : ℝ) 1) × ℝ, ℝ)

noncomputable def parisiContinuousExtend (U : ParisiPotentialSpace) (p : ℝ × ℝ) : ℝ :=
  U (projIcc 0 1 zero_le_one p.1, p.2)

theorem continuous_parisiContinuousExtend (U : ParisiPotentialSpace) :
    Continuous (parisiContinuousExtend U) :=
  U.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)

theorem parisiContinuousExtend_eq (U : ParisiPotentialSpace) (p : Icc (0 : ℝ) 1 × ℝ) :
    parisiContinuousExtend U ((p.1 : ℝ), p.2) = U p := by
  simp only [parisiContinuousExtend, projIcc_of_mem _ p.1.property]

noncomputable def parisiPotentialOnStrip (β : ℝ) (μ : ParisiMeasure) : ParisiPotentialSpace :=
  ⟨fun p => parisiPotential β μ ((p.1 : ℝ), p.2),
    (continuous_parisiPotential β μ).comp (by fun_prop)⟩

def IsParisiWeakPotential (β : ℝ) (μ : ParisiMeasure) (U : ParisiPotentialSpace) : Prop :=
  ∃ v : ℝ × ℝ → ℝ, IsParisiWeakSolution β μ (parisiContinuousExtend U) v

theorem parisiPotentialOnStrip_isWeakPotential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    IsParisiWeakPotential β μ (parisiPotentialOnStrip β μ) := by
  refine ⟨parisiGradient β μ, (parisiPotential_isWeakSolution β hβ μ).congr_potential_on
    (continuous_parisiContinuousExtend _).continuousOn ?_⟩
  intro p hp
  simp only [parisiContinuousExtend, parisiPotentialOnStrip, ContinuousMap.coe_mk,
    projIcc_of_mem _ hp.1, Prod.mk.eta]

theorem parisiPotentialOnStrip_eq_of_strip_eq (β : ℝ) (μ : ParisiMeasure)
    (U : ParisiPotentialSpace)
    (he : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ,
      parisiContinuousExtend U p = parisiPotential β μ p) :
    U = parisiPotentialOnStrip β μ := by
  apply ContinuousMap.ext
  intro p
  have hh := he ((p.1 : ℝ), p.2) ⟨p.1.property, mem_univ _⟩
  simpa only [parisiContinuousExtend_eq, parisiPotentialOnStrip, ContinuousMap.coe_mk] using hh

end Paper
