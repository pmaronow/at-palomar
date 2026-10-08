module

public import Paper.SKBackendParameters
public import Paper.MainExtension
public import Lemmas.MainResult

@[expose] public section

/-!
# Replica symmetry in the entire Almeida--Thouless region

The strict-region backend is instantiated with the concrete independent Gaussian
model in `PhysicalSKDisorder`. Its exact expected free energy is the paper's
increasing unordered-pair model. A compact singleton gives an `M/n` comparison;
the explicit strict AT approximation extends convergence to the AT boundary.
-/

open Filter
open scoped Topology

namespace Paper

/-- The concrete physical SK free energy converges throughout the strict AT region. -/
theorem strictReplicaSymmetry : StrictReplicaSymmetryTarget := by
  intro β h q hβ hh hq hfixed hα
  have hQ := skBackend_rsQ_eq β h q hβ hh hq.1 hfixed
  have hAT := skBackend_atParameter_eq β h q hβ hh hq.1 hfixed
  have hRS := skBackend_rsFreeEnergy_eq β h q hβ hh hq.1 hfixed
  have hp : (β, h) ∈ SpinGlass.AT.strictATRegion := by
    exact ⟨hβ, hh, by rwa [hAT]⟩
  have hsub : {(β, h)} ⊆ SpinGlass.AT.strictATRegion := by
    intro p hmem
    rcases Set.mem_singleton_iff.mp hmem with rfl
    exact hp
  have hquant := SpinGlass.AT.quantitative_strictAT_on_compact
    (Ω := PhysicalSKGaussianSpace) {(β, h)} isCompact_singleton hsub
  obtain ⟨M, _, hbound⟩ := hquant.freeEnergy
  apply finiteSKFreeEnergy_tendsto_of_error_bound β h q M
  intro n hn
  have hineq := hbound hn (β := β) (h := h) (q := q)
    (Set.mem_singleton (β, h)) hQ (physicalGaussianPath n β h q hq.1)
  rwa [physicalGaussianPath_freeEnergy_eq, hRS] at hineq

/-- **Theorem 1.1.** Replica symmetry for the actual SK model in the closed AT region. -/
theorem replicaSymmetry : MainReplicaSymmetryTarget :=
  mainReplicaSymmetry_of_strict strictReplicaSymmetry

end Paper
