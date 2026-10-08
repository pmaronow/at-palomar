module

public import Lemmas.AT.FixedPoint
public import Lemmas.SpinGlass.SKModel

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal

set_option autoImplicit false

namespace SpinGlass.AT

universe u

/-!
# Definitions for the strict Almeida-Thouless argument

The declarations below follow
`refs/latalaArgumentsStrictAlmeidaThoulessCondition.tex`.  The canonical
replica-symmetric fixed point `rsQ`, its fourth moment `rsR`, and the AT
parameter `atParameter` are imported from `fixed_point`.
-/

/-! ## Replicas over the existing SK model -/

/-- An indexed family of replicas from `SpinGlass.Config`. -/
abbrev Replicas (N n : ℕ) :=
  Fin n → SpinGlass.Config N

/-- A function of finitely many replicas. -/
abbrev ReplicaFun (N n : ℕ) :=
  Replicas N n → ℝ

/-- Product Gibbs expectation formed from `SpinGlass.gibbs_pmf`. -/
noncomputable def replicaGibbsAverage {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) : ℝ :=
  ∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs

/-- Disorder-averaged product Gibbs expectation. -/
noncomputable def quenchedReplicaAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N)
    (F : ReplicaFun N n) : ℝ :=
  ∫ ω, replicaGibbsAverage (H ω) F ∂(volume : Measure Ω)

/-- The overlap of two selected replicas, using `SpinGlass.overlap`. -/
noncomputable def replicaOverlap {N n : ℕ}
    (σs : Replicas N n) (a b : Fin n) : ℝ :=
  SpinGlass.overlap N (σs a) (σs b)

/-- The overlap centered at the replica-symmetric parameter. -/
noncomputable def centeredOverlap {N n : ℕ} (q : ℝ)
    (σs : Replicas N n) (a b : Fin n) : ℝ :=
  replicaOverlap σs a b - q

/-! ## Compact parameter data -/

/-- Uniform numerical data attached to a compact subset of the strict AT
region. -/
structure UniformATData (K : Set (ℝ × ℝ)) where
  isCompact : IsCompact K
  βmax : ℝ
  qmin : ℝ
  gap : ℝ
  βmax_pos : 0 < βmax
  qmin_pos : 0 < qmin
  gap_pos : 0 < gap
  β_pos : ∀ p ∈ K, 0 < p.1
  h_pos : ∀ p ∈ K, 0 < p.2
  β_bound : ∀ p ∈ K, p.1 ≤ βmax
  q_lower : ∀ p ∈ K, qmin ≤ rsQ p.1 p.2
  strictAT : ∀ p ∈ K, atParameter p.1 p.2 ≤ 1 - gap

/-! ## Scalar heat semigroups and the RS path -/

/-- The one-dimensional heat semigroup
`(H_t f)(x) = E[f(x + sqrt(t) Z)]`. -/
noncomputable def heatSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z => f (x + Real.sqrt t * z))

/-- The tilted heat semigroup used above the RS breakpoint. -/
noncomputable def tiltedHeatSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t / 2) * heatSemigroup t (fun y => f y * Real.cosh y) x /
    Real.cosh x

/-- The scalar Parisi function along the replica-symmetric path. -/
noncomputable def scalarPsi (β q s u x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z =>
    Real.log (Real.cosh
      (x + β * Real.sqrt (s * max (q - u) 0) * z))) +
    s * β ^ 2 / 2 * (1 - max u q)

/-- The explicit spatial derivative of `scalarPsi`. -/
noncomputable def scalarPsiX (β q s u x : ℝ) : ℝ :=
  standardGaussianExpectation (fun z =>
    Real.tanh (x + β * Real.sqrt (s * max (q - u) 0) * z))

/-- Expectation against the local-field law `X_{s,u}`. -/
noncomputable def localFieldExpectation
    (β h q s u : ℝ) (f : ℝ → ℝ) : ℝ :=
  if u ≤ q then
    heatSemigroup (β ^ 2 * ((1 - s) * q + s * u)) f h
  else
    heatSemigroup (β ^ 2 * q)
      (tiltedHeatSemigroup (s * β ^ 2 * (u - q)) f) h

/-- The scalar order-parameter map
`g_s(u) = E[(partial_x Psi(u,X_{s,u}))^2]`. -/
noncomputable def scalarOrderParameter (β h q s u : ℝ) : ℝ :=
  localFieldExpectation β h q s u
    (fun x => scalarPsiX β q s u x ^ 2)

/-- The scalar order-parameter map at the canonical fixed point. -/
noncomputable def scalarOrderParameterCorrect (β h s u : ℝ) : ℝ :=
  scalarOrderParameter β h (rsQ β h) s u

/-- Replica-symmetric scalar trial value before simplifying the Gaussian
semigroup. -/
noncomputable def scalarTrialValue (β h q s : ℝ) : ℝ :=
  Real.log 2 + standardGaussianExpectation (fun z =>
    scalarPsi β q s 0
      (h + β * Real.sqrt ((1 - s) * q) * z)) -
    s * β ^ 2 / 4 * (1 - q ^ 2)

/-- Simplified replica-symmetric path value `P_s^*`. -/
noncomputable def rsPathValue (β h q s : ℝ) : ℝ :=
  Real.log 2 + standardGaussianExpectation
    (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
    s * β ^ 2 / 4 * (1 - q) ^ 2

/-! ## Smart-path disorder and Gibbs observables -/

/-- Covariance kernel of the centered random part of the smart path. -/
noncomputable def smartPathCovKernel (N : ℕ) (β q s : ℝ)
    (σ τ : SpinGlass.Config N) : ℝ :=
  s * SpinGlass.sk_cov_kernel N β σ τ +
    (1 - s) *
      SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ

/-- A centered Gaussian realization of the replica-symmetric smart path. -/
structure RSSmartPathDisorder (Ω : Type u) [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (N : ℕ) (β h q : ℝ) where
  sk : SpinGlass.SKDisorder (Ω := Ω) N β h
  simple : SpinGlass.SimpleDisorder (Ω := Ω) N β q
  independent : IndepFun sk.U simple.V (volume : Measure Ω)

/-- The full smart-path Hamiltonian, including the deterministic field. -/
noncomputable def fullPathHamiltonian {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) (ω : Ω) :
    SpinGlass.EnergySpace N :=
  Real.sqrt s • path.sk.U ω +
    Real.sqrt (1 - s) • path.simple.V ω +
    SpinGlass.magnetic_field_vector N h

/-- The quenched free-energy density along the smart path. -/
noncomputable def pathFreeEnergy {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  ∫ ω, SpinGlass.free_energy_density
      (N := N) (fullPathHamiltonian path s ω)
    ∂(volume : Measure Ω)

/-- The replica-symmetric free energy at the canonical fixed point. -/
noncomputable def rsFreeEnergy (β h : ℝ) : ℝ :=
  rsPathValue β h (rsQ β h) 1

/-- The finite-volume SK free energy at the endpoint of the smart path. -/
noncomputable def skFreeEnergy {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) : ℝ :=
  pathFreeEnergy path 1

/-- The free-energy comparison gap `D_N(s)`. -/
noncomputable def rsFreeEnergyGap {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  rsPathValue β h q s - pathFreeEnergy path s

/-- The second centered-overlap moment `A_s`. -/
noncomputable def A {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 => centeredOverlap q σs 0 1 ^ 2)

/-- The shared-index overlap moment `B_s`. -/
noncomputable def B {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 =>
      centeredOverlap q σs 0 1 * centeredOverlap q σs 0 2)

/-- The disjoint-index overlap moment `C_s`. -/
noncomputable def C {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 =>
      centeredOverlap q σs 0 1 * centeredOverlap q σs 2 3)

/-- Compatibility name for `A_s`. -/
noncomputable def overlapSecondMoment {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  A path s

/-- The third absolute centered-overlap moment. -/
noncomputable def thirdMoment {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 => |centeredOverlap q σs 0 1| ^ 3)

/-- The quenched probability of a fixed overlap deviation. -/
noncomputable def quenchedTail {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s eps : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 =>
      if eps ≤ |centeredOverlap q σs 0 1| then 1 else 0)

/-- The smart-path AT parameter `s * alpha`. -/
noncomputable def pathATParameter (β h s : ℝ) : ℝ :=
  s * atParameter β h

/-! ## Latała's scalar kernel -/

noncomputable def latalaH (t y : ℝ) : ℝ :=
  (1 + (4 - 3 * y) * t) / (1 + y * t) ^ 3

noncomputable def latalaF (lam y : ℝ) : ℝ :=
  Real.exp (-lam / 2) * standardGaussianExpectation (fun z =>
    Real.cosh (Real.sqrt lam * z) *
      latalaH (Real.sinh (Real.sqrt lam * z) ^ 2) y)

noncomputable def referenceDensity (y : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (1 - y))

noncomputable def referenceExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Icc (0 : ℝ) 1, f y * referenceDensity y

/-! ## Two-replica Guerra-Talagrand objects -/

/-- The finite set of overlaps attainable by two size-`N` configurations. -/
noncomputable def attainableOverlaps (N : ℕ) : Finset ℝ :=
  Finset.univ.image
    (fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.overlap N p.1 p.2)

/-- The constrained two-replica partition function. -/
noncomputable def constrainedPartition {N : ℕ}
    (H : SpinGlass.EnergySpace N) (v : ℝ) : ℝ :=
  ∑ p : SpinGlass.Config N × SpinGlass.Config N,
    if SpinGlass.overlap N p.1 p.2 = v then
      Real.exp (-(H p.1 + H p.2))
    else 0

/-- The expected constrained two-replica free energy. -/
noncomputable def expectedConstrainedFreeEnergy
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s v : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ ω,
    Real.log (constrainedPartition (fullPathHamiltonian path s ω) v)
      ∂(volume : Measure Ω)

/-- The covariance function `xi_s`. -/
noncomputable def gtCovarianceFunction (β q s r : ℝ) : ℝ :=
  β ^ 2 * (1 - s) * q * r + s * β ^ 2 / 2 * r ^ 2

/-- The sign used in the signed overlap path. -/
noncomputable def gtPathSign (v : ℝ) : ℝ :=
  if 0 ≤ v then 1 else -1

/-- The signed two-replica overlap path `Q^v(u)`. -/
noncomputable def signedMatrixPath (v u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let sign := gtPathSign v
  !![u, sign * min u |v|; sign * min u |v|, u]

/-- The mass profile on the signed overlap path. -/
noncomputable def gtMassParameter (q v u : ℝ) : ℝ :=
  if u ≤ q then 0 else if u ≤ |v| then 1 / 2 else 1

/-- The covariance matrix `B(u) = beta^2(1-s)q J + s beta^2 Q^v(u)`. -/
noncomputable def gtCovarianceMatrix
    (β q s v u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (β ^ 2 * (1 - s) * q) •
      (!![(1 : ℝ), 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
    (s * β ^ 2) • signedMatrixPath v u

/-- The scalar covariance correction at a path value `u`. -/
noncomputable def gtScalarVariance (β s v u : ℝ) : ℝ :=
  if u ≤ |v| then 2 * s * β ^ 2 * u ^ 2
  else s * β ^ 2 * (u ^ 2 + v ^ 2)

/-- Terminal function `f_lambda` in the two-replica recursion. -/
noncomputable def gtTerminal (lam x₁ x₂ : ℝ) : ℝ :=
  Real.log ((Real.exp (x₁ + x₂ + lam) +
    Real.exp (x₁ - x₂ - lam) +
    Real.exp (-x₁ + x₂ - lam) +
    Real.exp (-x₁ - x₂ + lam)) / 4)

/-- The correction `L_s(v)`, after evaluating its finite sum. -/
noncomputable def gtCorrection (β q s : ℝ) : ℝ :=
  s * β ^ 2 / 2 * (1 - q ^ 2)

/-- A function of the two local fields in the finite GT recursion. -/
abbrev GTTwoField := ℝ → ℝ → ℝ

/-- Standard deviation for an active covariance increment. -/
noncomputable def gtIncrementScale
    (β s lower upper : ℝ) : ℝ :=
  β * Real.sqrt s * Real.sqrt (upper - lower)

/-- A diagonal Gaussian recursion step. -/
noncomputable def gtDiagonalStep
    (m scale : ℝ) (F : GTTwoField) : GTTwoField :=
  fun x₁ x₂ =>
    if m = 0 then
      standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          F (x₁ + scale * z₁) (x₂ + scale * z₂)))
    else
      (1 / m) * Real.log (standardGaussianExpectation (fun z₁ =>
        standardGaussianExpectation (fun z₂ =>
          Real.exp (m * F
            (x₁ + scale * z₁) (x₂ + scale * z₂)))))

/-- A rank-one Gaussian recursion step below the signed breakpoint. -/
noncomputable def gtRankOneStep
    (m scale sign : ℝ) (F : GTTwoField) : GTTwoField :=
  fun x₁ x₂ =>
    if m = 0 then
      standardGaussianExpectation (fun z =>
        F (x₁ + scale * z) (x₂ + sign * scale * z))
    else
      (1 / m) * Real.log (standardGaussianExpectation (fun z =>
        Real.exp (m * F
          (x₁ + scale * z) (x₂ + sign * scale * z))))

/-- The explicit finite GT recursion with breakpoints `q` and `|v|`. -/
noncomputable def gtSemigroupSolution
    (β q s lam v u x₁ x₂ : ℝ) : ℝ :=
  let r : ℝ := |v|
  let sign : ℝ := gtPathSign v
  let terminal : GTTwoField := gtTerminal lam
  let upper : ℝ → GTTwoField := fun lower =>
    gtDiagonalStep 1 (gtIncrementScale β s lower 1) terminal
  if q ≤ r then
    let atR : GTTwoField := upper r
    let atQ : GTTwoField :=
      gtRankOneStep (1 / 2) (gtIncrementScale β s q r) sign atR
    if r ≤ u then
      upper u x₁ x₂
    else if q ≤ u then
      gtRankOneStep (1 / 2) (gtIncrementScale β s u r) sign atR x₁ x₂
    else
      gtRankOneStep 0 (gtIncrementScale β s u q) sign atQ x₁ x₂
  else
    let atQ : GTTwoField := upper q
    let atR : GTTwoField :=
      gtDiagonalStep 0 (gtIncrementScale β s r q) atQ
    if q ≤ u then
      upper u x₁ x₂
    else if r ≤ u then
      gtDiagonalStep 0 (gtIncrementScale β s u q) atQ x₁ x₂
    else
      gtRankOneStep 0 (gtIncrementScale β s u r) sign atR x₁ x₂

/-- The specialized two-replica GT functional `mathfrak P_s(lambda,v)`. -/
noncomputable def gtFunctional (β h q s lam v : ℝ) : ℝ :=
  2 * Real.log 2 + standardGaussianExpectation (fun z =>
    gtSemigroupSolution β q s lam v 0
      (h + β * Real.sqrt ((1 - s) * q) * z)
      (h + β * Real.sqrt ((1 - s) * q) * z)) -
    lam * v - gtCorrection β q s

/-- The optimized GT functional `Gamma_s(v)`. -/
noncomputable def gtEnvelope (β h q s v : ℝ) : ℝ :=
  sInf (Set.range (fun lam : ℝ => gtFunctional β h q s lam v))

/-! ## Coupled pressure -/

/-- The quadratically coupled two-replica partition function. -/
noncomputable def quadraticCoupledPartition {N : ℕ}
    (H : SpinGlass.EnergySpace N) (q rho : ℝ) : ℝ :=
  ∑ p : SpinGlass.Config N × SpinGlass.Config N,
    Real.exp (-(H p.1 + H p.2) +
      rho * (N : ℝ) / 2 * (SpinGlass.overlap N p.1 p.2 - q) ^ 2)

/-- The coupled partition function is the finite log-sum-exp envelope of
the constrained two-replica partition functions. -/
theorem quadraticCoupledPartition_eq_sum_constrained {N : ℕ}
    (H : SpinGlass.EnergySpace N) (q rho : ℝ) :
    quadraticCoupledPartition H q rho =
      ∑ v ∈ attainableOverlaps N,
        Real.exp (rho * (N : ℝ) / 2 * (v - q) ^ 2) *
          constrainedPartition H v := by
  classical
  unfold quadraticCoupledPartition constrainedPartition
  symm
  calc
    (∑ v ∈ attainableOverlaps N,
        Real.exp (rho * (N : ℝ) / 2 * (v - q) ^ 2) *
          ∑ p : SpinGlass.Config N × SpinGlass.Config N,
            if SpinGlass.overlap N p.1 p.2 = v then
              Real.exp (-(H p.1 + H p.2)) else 0) =
        ∑ v ∈ attainableOverlaps N,
          ∑ p : SpinGlass.Config N × SpinGlass.Config N,
            Real.exp (rho * (N : ℝ) / 2 * (v - q) ^ 2) *
              (if SpinGlass.overlap N p.1 p.2 = v then
                Real.exp (-(H p.1 + H p.2)) else 0) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ p : SpinGlass.Config N × SpinGlass.Config N,
          ∑ v ∈ attainableOverlaps N,
            Real.exp (rho * (N : ℝ) / 2 * (v - q) ^ 2) *
              (if SpinGlass.overlap N p.1 p.2 = v then
                Real.exp (-(H p.1 + H p.2)) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ p : SpinGlass.Config N × SpinGlass.Config N,
          Real.exp (-(H p.1 + H p.2) +
            rho * (N : ℝ) / 2 *
              (SpinGlass.overlap N p.1 p.2 - q) ^ 2) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_eq_single (SpinGlass.overlap N p.1 p.2)]
      · simp [attainableOverlaps, ← Real.exp_add, add_comm]
      · intro v _ hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (by
          unfold attainableOverlaps
          exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)).elim

/-- The coupled pressure `p^{(2)}_{N,s}(rho)`. -/
noncomputable def quadraticCoupledPressure
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s rho : ℝ) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∫ ω,
    Real.log
      (quadraticCoupledPartition (fullPathHamiltonian path s ω) q rho)
      ∂(volume : Measure Ω)

/-- The normalized coupled-pressure excess `F_{N,s}(rho)`. -/
noncomputable def normalizedCouplingExcess
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s rho : ℝ) : ℝ :=
  quadraticCoupledPressure path s rho - pathFreeEnergy path s

/-! ## Cavity modes and stability -/

/-- Vector of the three overlap moments `(A_s,B_s,C_s)`. -/
noncomputable def cavityVector {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : Fin 3 → ℝ :=
  ![A path s, B path s, C path s]

/-- Source vector in the cavity system. -/
def theta (q r : ℝ) : Fin 3 → ℝ :=
  ![1 - q ^ 2, q - q ^ 2, r - q ^ 2]

/-- The cavity coefficient matrix in the `(A,B,C)` basis. -/
def cavityMatrix (β q r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let b₂ := β ^ 2 * (1 - q ^ 2)
  let b₁ := β ^ 2 * (q - q ^ 2)
  let b₀ := β ^ 2 * (r - q ^ 2)
  !![b₂, -4 * b₁, 3 * b₀;
     b₁, b₂ - 2 * b₁ - 3 * b₀, 6 * b₀ - 3 * b₁;
     b₀, 4 * b₁ - 8 * b₀, b₂ - 8 * b₁ + 10 * b₀]

/-- The cavity stability operator `I - s M`. -/
def stabilityOperator (β q r s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 - s • cavityMatrix β q r

/-- The fixed change of basis to the `(U,V,D)` cavity modes. -/
def cavityChangeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 2, -3;
     1, -4, 3;
     1, -2, 1]

/-- The explicit inverse of `cavityChangeMatrix`. -/
noncomputable def cavityChangeMatrixInv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, -2, 3;
     -1, -(3 / 2 : ℝ), 3 / 2;
     -1, -1, 1]

/-- The replicon row selecting `A_s - 2 B_s + C_s`. -/
def repliconRow : Fin 3 → ℝ :=
  ![1, -2, 1]

/-- The anomalous cavity mode `U_s`. -/
noncomputable def cavityU {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  A path s - 4 * B path s + 3 * C path s

/-- The second anomalous cavity mode `V_s`. -/
noncomputable def cavityV {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  2 * B path s - 3 * C path s

/-- The replicon cavity mode `D_s`. -/
noncomputable def cavityD {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  A path s - 2 * B path s + C path s

/-- The anomalous scalar coefficient `kappa`. -/
def cavityKappa (q r : ℝ) : ℝ :=
  1 - 4 * q + 3 * r

/-- The off-diagonal anomalous coefficient `zeta`. -/
def cavityZeta (q r : ℝ) : ℝ :=
  2 * q + q ^ 2 - 3 * r

/-- A pair of distinct replica indices. -/
abbrev ReplicaEdge (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2}

/-- Intersection type of two replica edges. -/
inductive EdgeRelation
  | equal
  | sharesOne
  | disjoint
  deriving DecidableEq

/-- The intersection type of two replica edges. -/
def edgeRelation {n : ℕ} (e f : ReplicaEdge n) : EdgeRelation :=
  if e = f then .equal
  else if e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨
      e.1.2 = f.1.1 ∨ e.1.2 = f.1.2 then
    .sharesOne
  else
    .disjoint

/-- Last-spin coefficient determined by the edge intersection type. -/
def decoupledSpinCoefficient (q r : ℝ) : EdgeRelation → ℝ
  | .equal => 1 - q ^ 2
  | .sharesOne => q - q ^ 2
  | .disjoint => r - q ^ 2

/-- The remainder obtained by subtracting the linear cavity system. -/
noncomputable def cavityRemainder {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : Fin 3 → ℝ :=
  cavityVector path s -
    s • (cavityMatrix β q (rsR β h)).mulVec (cavityVector path s) -
    (1 / (N : ℝ)) • theta q (rsR β h)

/-- The scale of the cavity error. -/
noncomputable def cavityErrorScale {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  (N : ℝ) ^ (-(3 : ℝ) / 2) + thirdMoment path s

/-- The uniform cavity-remainder estimate used by the absorption argument. -/
def HasCavityRemainderBound {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {K : Set (ℝ × ℝ)}
    (data : UniformATData K) (C : ℝ) : Prop :=
  0 < C ∧ ∀ {N : ℕ}, 0 < N → ∀ {β h q s : ℝ},
    (β, h) ∈ K → q = rsQ β h → s ∈ Set.Icc (0 : ℝ) 1 →
    ∀ path : RSSmartPathDisorder Ω N β h q,
      ‖cavityRemainder path s‖ ≤ C * cavityErrorScale path s


end SpinGlass.AT
