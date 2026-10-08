module

public import Paper.Gaussian
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

/-!
# Concrete theorem statements

These definitions state the two top-level results of the uploaded paper using
the actual finite Sherrington--Kirkpatrick model and Gaussian RS quantities.
They are propositions, not assumptions or axioms. Their closed proofs are
`Paper.replicaSymmetry` in `ReplicaSymmetry.lean` and
`Paper.smoothATBoundary` in `ATSmoothGraph.lean`.

The model includes one independent standard normal coupling for each unordered
pair of distinct sites, represented by its increasing ordered pair. The value
at size zero is harmless for the `atTop` limit; real division by zero has its
usual totalized Lean interpretation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ContDiff

namespace Paper

/-- A spin configuration at `n` sites. `true` represents `+1`; `false`, `-1`. -/
abbrev SKConfiguration (n : ℕ) := Fin n → Bool

/-- One edge for each pair `i < j`, so there are no self-couplings or duplicates. -/
abbrev SKEdge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- The real Gaussian coupling attached to each edge. -/
abbrev SKCouplings (n : ℕ) := SKEdge n → ℝ

def spinSign (s : Bool) : ℝ := if s then 1 else -1

/-- Product standard Gaussian law: the SK couplings are independent. -/
noncomputable def skCouplingLaw (n : ℕ) : Measure (SKCouplings n) :=
  Measure.pi (fun _ : SKEdge n => gaussianReal 0 1)

/-- The Hamiltonian from the paper's introduction, with its exact normalization. -/
noncomputable def skHamiltonian {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : ℝ :=
  β / Real.sqrt (n : ℝ) *
      ∑ ij : SKEdge n, g ij * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)
    + h * ∑ i : Fin n, spinSign (σ i)

noncomputable def skPartitionFunction {n : ℕ} (β h : ℝ) (g : SKCouplings n) : ℝ :=
  ∑ σ : SKConfiguration n, Real.exp (skHamiltonian β h g σ)

/-- The physical finite-volume expected free energy `F_n(β,h)`. -/
noncomputable def finiteSKFreeEnergy (β h : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ g : SKCouplings n, Real.log (skPartitionFunction β h g) ∂skCouplingLaw n

/-- **Theorem 1.1.** Replica symmetry throughout the AT region.

Stating the free-energy limit directly avoids silently assuming that the
thermodynamic limit exists. Every expectation and Gaussian quantity here has
the concrete definition in `Paper.Gaussian` or above.
-/
def MainReplicaSymmetryTarget : Prop :=
  ∀ β h q : ℝ, 0 < β → 0 < h → q ∈ Set.Icc (0 : ℝ) 1 →
    q = overlapMap β h q → atParameter β h q ≤ 1 →
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q))

/-- The paper's positive-field AT boundary, together with the stipulated `(1,0)`.

The fixed point is expressed existentially, so no existence/uniqueness theorem
or choice of an unproved fixed-point selector is hidden in this definition.
-/
def atBoundary : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ q = overlapMap p.1 p.2 q ∧
      atParameter p.1 p.2 q = 1} ∪ {(1, 0)}

/-- **Proposition 1.2.** Smooth, strictly increasing AT graph.

The function is represented on all of `ℝ`, with its required regularity,
positivity and monotonicity restricted to `(1,∞)`. The endpoint assertion is
the right-hand limit at `1`, not a smoothness assertion at the endpoint.
-/
def SmoothATBoundaryTarget : Prop :=
  ∃ hAT : ℝ → ℝ,
    (∀ β : ℝ, 1 < β → 0 < hAT β) ∧
    ContDiffOn ℝ ∞ hAT (Set.Ioi (1 : ℝ)) ∧
    StrictMonoOn hAT (Set.Ioi (1 : ℝ)) ∧
    Tendsto hAT (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (0 : ℝ)) ∧
    atBoundary = {p : ℝ × ℝ | 1 < p.1 ∧ p.2 = hAT p.1} ∪ {(1, 0)}

end Paper
