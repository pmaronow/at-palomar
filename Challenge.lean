module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

/-!
# Replica symmetry up to the de Almeida–Thouless line

This independent statement surface uses only Mathlib. It formalizes Theorem 1.1
and Proposition 1.2 of Patrick Lopatto, *Replica symmetry up to the de
Almeida–Thouless line in the Sherrington–Kirkpatrick model*, arXiv:2604.11921v2.
All expectations below are integrals against actual Gaussian probability laws.
The hypotheses retain positive inverse temperature and positive uniform field;
the AT inequality includes equality. The free-energy conclusion states the
finite-volume limit directly, including its existence.

The AT graph is smooth on `(1,∞)`. It tends to zero from the right at `1`;
no smoothness at the endpoint or zero-field phase theorem is asserted. The
fixed point is explicit rather than an assumed selector. The proof development
contains additional PDE and variational results; these two headline results are
the claims selected by this Comparator configuration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ContDiff

namespace PalomarAT

/-- Hyperbolic secant, `sech x = 1 / cosh x`. -/
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

/-- Expectation of a real observable under the standard normal law. -/
noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1

/-- The scalar Gaussian field `β sqrt(q) Z + h`. -/
noncomputable def gaussianField (β h q z : ℝ) : ℝ := β * Real.sqrt q * z + h

/-- The overlap fixed-point map `E[tanh²(β sqrt(q) Z + h)]`. -/
noncomputable def overlapMap (β h q : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (gaussianField β h q z) ^ 2)

/-- The AT parameter `β² E[sech⁴(β sqrt(q) Z + h)]`. -/
noncomputable def atParameter (β h q : ℝ) : ℝ :=
  β ^ 2 * gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 4)

/-- The replica-symmetric value `log 2 + E[log cosh(β sqrt(q) Z + h)]
    + β²(1-q)²/4`. -/
noncomputable def rsFreeEnergy (β h q : ℝ) : ℝ :=
  Real.log 2 + gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z)))
    + β ^ 2 / 4 * (1 - q) ^ 2

/-- A configuration of `n` Ising spins; `true` is `+1` and `false` is `-1`. -/
abbrev SKConfiguration (n : ℕ) := Fin n → Bool

/-- Increasing unordered pairs of distinct sites, with no diagonal terms. -/
abbrev SKEdge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- One real coupling for each increasing site pair. -/
abbrev SKCouplings (n : ℕ) := SKEdge n → ℝ

/-- The two Ising spin values encoded by a Boolean. -/
def spinSign (s : Bool) : ℝ := if s then 1 else -1

/-- Independent standard normal coupling law, one coordinate per pair. -/
noncomputable def skCouplingLaw (n : ℕ) : Measure (SKCouplings n) :=
  Measure.pi (fun _ : SKEdge n => gaussianReal 0 1)

/-- The paper's Hamiltonian `β/√n ∑_{i<j} gᵢⱼ σᵢσⱼ + h ∑ᵢ σᵢ`. -/
noncomputable def skHamiltonian {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) : ℝ :=
  β / Real.sqrt (n : ℝ) *
      ∑ ij : SKEdge n, g ij * spinSign (σ ij.val.1) * spinSign (σ ij.val.2)
    + h * ∑ i : Fin n, spinSign (σ i)

/-- Partition function, summing `exp(H)` over all `2ⁿ` spin configurations. -/
noncomputable def skPartitionFunction {n : ℕ} (β h : ℝ) (g : SKCouplings n) : ℝ :=
  ∑ σ : SKConfiguration n, Real.exp (skHamiltonian β h g σ)

/-- Expected finite-volume free energy `(1/n) E[log Zₙ]`. Lean's totalized
    division gives a harmless zero-size value; the theorem takes `n → ∞`. -/
noncomputable def finiteSKFreeEnergy (β h : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ g : SKCouplings n, Real.log (skPartitionFunction β h g) ∂skCouplingLaw n

/-- The positive-field AT boundary `α=1`, together with the stipulated `(1,0)`.
    The existential fixed point avoids any dependence on an unproved selector. -/
def atBoundary : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ q = overlapMap p.1 p.2 q ∧
      atParameter p.1 p.2 q = 1} ∪ {(1, 0)}

/-- **Theorem 1.1.** For every positive `β,h`, and every overlap fixed point
    in `[0,1]` with AT parameter at most one, the expected SK free energy
    converges to the replica-symmetric Gaussian value. -/
theorem replicaSymmetry :
    ∀ β h q : ℝ, 0 < β → 0 < h → q ∈ Set.Icc (0 : ℝ) 1 →
      q = overlapMap β h q → atParameter β h q ≤ 1 →
      Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q)) := by
  sorry

/-- **Proposition 1.2.** The actual positive-field AT boundary is the graph
    of a positive, strictly increasing `C∞` function on `(1,∞)`, with right
    limit zero at `1`, together with `(1,0)`. The function is represented on
    all reals and all regularity and order requirements use the stated domain. -/
theorem smoothATBoundary :
    ∃ hAT : ℝ → ℝ,
      (∀ β : ℝ, 1 < β → 0 < hAT β) ∧
      ContDiffOn ℝ ∞ hAT (Set.Ioi (1 : ℝ)) ∧
      StrictMonoOn hAT (Set.Ioi (1 : ℝ)) ∧
      Tendsto hAT (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (0 : ℝ)) ∧
      atBoundary = {p : ℝ × ℝ | 1 < p.1 ∧ p.2 = hAT p.1} ∪ {(1, 0)} := by
  sorry

end PalomarAT
