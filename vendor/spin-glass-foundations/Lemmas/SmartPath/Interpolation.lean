module

public import Lemmas.SpinGlass.SKModel
public import Lemmas.SpinGlass.Calculus
public import Lemmas.SpinGlass.GuerraBound
public import Lemmas.SmartPath.KSInequality
public import Lemmas.SmartPath.IndependentEndpoint
public import Lemmas.SmartPath.IndependentGaussianAffineIBP
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 800000

namespace SpinGlass
namespace GeneralizedLatala

/-!
# Generalized Latała argument for the SK model

This module develops the finite-volume SK and simple Gaussian disorders from
`Lemmas.SpinGlass.SKModel`, together with the smart path, replica Gibbs averages, and annealed
expectation `nu` from `Lemmas.SpinGlass.Replicas`.

The scalar order parameter `q` is kept as an input satisfying the replica-symmetric fixed-point
equation.  This is preferable to making an arbitrary global choice of a fixed point.  The
remaining analytic work is split into small lemmas below, with comments recording the intended
Gaussian-IBP and characteristic arguments.  The final overlap and free-energy bounds are then
assembled from those ingredients.
-/

universe uΩ uι

variable {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
**# Hubbard--Stratonovich identity**

This file records the scalar Gaussian identity used to linearize a positive
quadratic exponential.  It depends only on mathlib.
-/

/-- The moment-generating function identity for a standard real Gaussian,
written directly as an integral. -/
lemma integral_exp_mul_standardGaussian (t : ℝ) :
    ∫ z, Real.exp (t * z) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
  simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t

/-- The scalar Hubbard--Stratonovich identity.  If `a` is nonnegative and
`Z` is a standard real Gaussian, then
`exp (a * x ^ 2 / 2) = E[exp (sqrt a * x * Z)]`. -/
lemma hubbard_stratonovich (a x : ℝ) (ha : 0 ≤ a) :
    Real.exp (a * x ^ 2 / 2) =
      ∫ z, Real.exp (Real.sqrt a * x * z) ∂gaussianReal 0 1 := by
  rw [integral_exp_mul_standardGaussian, mul_pow, Real.sq_sqrt ha]

/-! ## Scalar replica-symmetric data -/

/-- Expectation against a standard real Gaussian. -/
noncomputable def standardGaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂ProbabilityTheory.gaussianReal 0 1

/-- The replica-symmetric fixed-point equation
`q = E[tanh (h + β sqrt(q) Z)^2]`. -/
def IsRSFixedPoint (β h q : ℝ) : Prop :=
  q = standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)

/-- The sharp Bernoulli sub-Gaussian coefficient used at the independent endpoint. -/
noncomputable def kappa (q : ℝ) : ℝ :=
  if q = 0 then 1 else q / Real.artanh q

/-- The improved high-temperature parameter `ρ = β² κ(q)`. -/
noncomputable def rho (β q : ℝ) : ℝ :=
  β ^ 2 * kappa q

/-- Coupling strength used in the quadratic replica estimate. -/
noncomputable def lambdaStar (β q : ℝ) : ℝ :=
  ((kappa q)⁻¹ - β ^ 2) / 4

/-- The constant on the right side of the uniform logarithmic quadratic estimate. -/
noncomputable def quadraticConstant (β q : ℝ) : ℝ :=
  (1 / 2) * Real.exp (2 * rho β q / (1 - rho β q)) *
    Real.log (2 / (1 - rho β q))

/-- The replica-symmetric free-energy prediction. -/
noncomputable def rsPressure (β h q : ℝ) : ℝ :=
  Real.log 2 +
    standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
    (β ^ 2 / 4) * (1 - q) ^ 2

lemma kappa_zero : kappa 0 = 1 := by
  simp [kappa]

lemma kappa_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < kappa q := by
  by_cases hq : q = 0
  · simp [hq, kappa]
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have ha : 0 < Real.artanh q := Real.artanh_pos ⟨hqpos, hq1⟩
    simp only [kappa, if_neg hq]
    exact div_pos hqpos ha

lemma rho_eq (β q : ℝ) : rho β q = β ^ 2 * kappa q := by
  rfl

lemma lambdaStar_eq (β q : ℝ) :
    lambdaStar β q = ((kappa q)⁻¹ - β ^ 2) / 4 := by
  rfl

/-! ## Smart-path observables -/

variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder.{uΩ} (Ω := Ω) N β h)
variable (sim : SimpleDisorder.{uΩ} (Ω := Ω) N β q)

private lemma measurable_H_t_updated (t : ℝ) :
    Measurable (H_t (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t) := by
  have hU : Measurable (fun w => Real.sqrt t • sk.U w) :=
    sk.hU.repr_measurable.const_smul (Real.sqrt t)
  have hV : Measurable (fun w => Real.sqrt (1 - t) • sim.V w) :=
    sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
  have hfield : Measurable (fun _w : Ω => H_field (N := N) (h := h)) := measurable_const
  change Measurable (((fun w => Real.sqrt t • sk.U w) +
    fun w => Real.sqrt (1 - t) • sim.V w) +
    fun _w : Ω => H_field (N := N) (h := h))
  exact (hU.add hV).add hfield

private lemma measurable_dH_t_updated (t : ℝ) :
    Measurable (fun w => dH_t (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t w) := by
  have hU : Measurable (fun w => (1 / (2 * Real.sqrt t)) • sk.U w) :=
    sk.hU.repr_measurable.const_smul (1 / (2 * Real.sqrt t))
  have hV : Measurable (fun w => (1 / (2 * Real.sqrt (1 - t))) • sim.V w) :=
    sim.hV.repr_measurable.const_smul (1 / (2 * Real.sqrt (1 - t)))
  change Measurable ((fun w => (1 / (2 * Real.sqrt t)) • sk.U w) +
    -(fun w => (1 / (2 * Real.sqrt (1 - t))) • sim.V w))
  exact hU.add hV.neg

/-- Centered overlap `Q_ab = R_ab - q`. -/
noncomputable def centeredOverlap {n : ℕ} (a b : Fin n) : ReplicaFun N n :=
  fun σs => overlap N (σs a) (σs b) - q

/-- The square of the centered overlap of the first two replicas. -/
noncomputable def centeredOverlapSq : ReplicaFun N 2 :=
  fun σs => (overlap N (σs 0) (σs 1) - q) ^ 2

/-- Annealed second moment `ν_t[Q_12²]`. -/
noncomputable def overlapVariance (t : ℝ) : ℝ :=
  nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    2 t (centeredOverlapSq N q)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma overlapVariance_nonneg (t : ℝ) :
    0 ≤ overlapVariance
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  classical
  apply integral_nonneg
  intro ω
  apply Finset.sum_nonneg
  intro σs _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro l _
  exact gibbs_pmf_nonneg
    (N := N)
    (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    (σ := σs l)

/-- The interpolated pressure `N⁻¹ E log Z_{N,t}`. -/
noncomputable def interpolatedPressure (t : ℝ) : ℝ :=
  ∫ ω, free_energy_density (N := N)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) ∂ℙ

/-- The logarithmic quadratic moment
`E log ⟨exp(λ N Q_12²)⟩_t`. -/
noncomputable def logQuadraticMoment (t coupling : ℝ) : ℝ :=
  ∫ ω, Real.log
    (gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 t (fun σs => Real.exp (coupling * (N : ℝ) * (centeredOverlapSq N q σs))) ω) ∂ℙ

/-- The logarithmic quadratic moment in the physical coupling `Λ`.

The exponential appearing in this quantity is `exp ((Λ / 2) * N * Q₁₂²)`.  Keeping this
wrapper separate from `logQuadraticMoment` prevents the physical coupling from being confused
with the coefficient appearing directly in the exponential. -/
noncomputable def physicalLogQuadraticMoment (t Λ : ℝ) : ℝ :=
  logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (Λ / 2)

/-! ### Positivity and explicit tilted observables -/

/-- The two-replica tilted partition function at fixed disorder `H`.

Here `coupling` is the coefficient in `exp (coupling * N * Q₁₂²)`, not the physical coupling
`Λ` used by `coupledFreeEnergy`. -/
noncomputable def tiltedReplicaPartitionDet (H : EnergySpace N) (coupling : ℝ) : ℝ :=
  gibbs_average_n_det (N := N) (n := 2) H
    (fun σs => Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs))

/-- The tilted partition function evaluated along the smart path. -/
noncomputable def tiltedReplicaPartition (t coupling : ℝ) (ω : Ω) : ℝ :=
  tiltedReplicaPartitionDet (N := N) (q := q)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    coupling

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Strict positivity of the finite-disorder tilted denominator. -/
lemma tiltedReplicaPartitionDet_pos (H : EnergySpace N) (coupling : ℝ) :
    0 < tiltedReplicaPartitionDet (N := N) (q := q) H coupling := by
  classical
  unfold tiltedReplicaPartitionDet gibbs_average_n_det
  apply Finset.sum_pos
  · intro σs _
    exact mul_pos (Real.exp_pos _)
      (Finset.prod_pos fun l _ => gibbs_pmf_pos (N := N) (H := H) (σ := σs l))
  · exact Finset.univ_nonempty

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For nonnegative exponential coupling, the tilted partition function is at least one. -/
lemma tiltedReplicaPartitionDet_one_le
    (H : EnergySpace N) {coupling : ℝ} (hcoupling : 0 ≤ coupling) :
    1 ≤ tiltedReplicaPartitionDet (N := N) (q := q) H coupling := by
  classical
  unfold tiltedReplicaPartitionDet gibbs_average_n_det
  rw [← sum_prod_gibbs_pmf_eq_one (N := N) (n := 2) (H := H)]
  apply Finset.sum_le_sum
  intro σs _
  have hexp : 1 ≤ Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs) :=
    Real.one_le_exp
      (mul_nonneg (mul_nonneg hcoupling (Nat.cast_nonneg N)) (sq_nonneg _))
  have hweight : 0 ≤ ∏ l, gibbs_pmf N H (σs l) :=
    Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hweight

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Strict positivity of the tilted denominator along the smart path. -/
lemma tiltedReplicaPartition_pos (t coupling : ℝ) (ω : Ω) :
    0 < tiltedReplicaPartition
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      t coupling ω :=
  tiltedReplicaPartitionDet_pos
    (N := N) (q := q)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    coupling

/-- The centered-overlap square under the quadratic tilt at fixed disorder. -/
noncomputable def tiltedCenteredOverlapSqDet
    (H : EnergySpace N) (coupling : ℝ) : ℝ :=
  gibbs_average_n_det (N := N) (n := 2) H
      (fun σs => centeredOverlapSq N q σs *
        Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs)) /
    tiltedReplicaPartitionDet (N := N) (q := q) H coupling

/-- Annealed centered-overlap square under the quadratic two-replica tilt. -/
noncomputable def tiltedCenteredOverlapSq (t coupling : ℝ) : ℝ :=
  ∫ ω, tiltedCenteredOverlapSqDet (N := N) (q := q)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    coupling ∂ℙ

/-- The average of the four cross-pair centered-overlap squares for replicas grouped as
`(1,2)` and `(3,4)`. -/
noncomputable def crossPairCenteredOverlapSq : ReplicaFun N 4 :=
  fun σs =>
    ((centeredOverlap (N := N) (q := q) (0 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap (N := N) (q := q) (0 : Fin 4) (3 : Fin 4) σs) ^ 2 +
      (centeredOverlap (N := N) (q := q) (1 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap (N := N) (q := q) (1 : Fin 4) (3 : Fin 4) σs) ^ 2) / 4

/-- The four-replica cross moment at fixed disorder.  The pairs `(1,2)` and `(3,4)` receive
independent copies of the same quadratic tilt. -/
noncomputable def coupledCrossMomentDet (H : EnergySpace N) (coupling : ℝ) : ℝ :=
  gibbs_average_n_det (N := N) (n := 4) H
      (fun σs => crossPairCenteredOverlapSq (N := N) (q := q) σs *
        Real.exp (coupling * (N : ℝ) *
          ((centeredOverlap (N := N) (q := q) (0 : Fin 4) (1 : Fin 4) σs) ^ 2 +
            (centeredOverlap (N := N) (q := q) (2 : Fin 4) (3 : Fin 4) σs) ^ 2))) /
    (tiltedReplicaPartitionDet (N := N) (q := q) H coupling) ^ 2

/-- Annealed four-replica cross moment generated by coupled Gaussian integration by parts. -/
noncomputable def coupledCrossMoment (t coupling : ℝ) : ℝ :=
  ∫ ω, coupledCrossMomentDet (N := N) (q := q)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    coupling ∂ℙ

/-- The four-replica cross moment is nonnegative. -/
lemma coupledCrossMoment_nonneg (t coupling : ℝ) :
    0 ≤ coupledCrossMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      t coupling := by
  classical
  apply integral_nonneg
  intro ω
  unfold coupledCrossMomentDet gibbs_average_n_det
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro σs _
    apply mul_nonneg
    · apply mul_nonneg
      · unfold crossPairCenteredOverlapSq
        positivity
      · exact Real.exp_nonneg _
    · exact Finset.prod_nonneg fun l _ =>
        gibbs_pmf_nonneg
          (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          (σ := σs l)
  · positivity

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Finite-volume Jensen inequality for an arbitrary replica observable. -/
lemma gibbs_average_n_det_exp_jensen {n : ℕ}
    (H : EnergySpace N) (f : ReplicaFun N n) :
    Real.exp (gibbs_average_n_det (N := N) (n := n) H f) ≤
      gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs)) := by
  classical
  let weight : ReplicaSpace N n → ℝ :=
    fun σs => ∏ l, gibbs_pmf N H (σs l)
  have hweight : ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)), 0 ≤ weight σs := by
    intro σs _
    exact Finset.prod_nonneg fun l _ =>
      gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  have hsum : ∑ σs : ReplicaSpace N n, weight σs = 1 := by
    simpa [weight] using sum_prod_gibbs_pmf_eq_one (N := N) (n := n) H
  have hjensen := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset (ReplicaSpace N n)))
    (w := weight) (p := f) hweight hsum
    (fun σs _ => Set.mem_univ (f σs))
  simpa [gibbs_average_n_det, weight, smul_eq_mul, mul_comm] using hjensen

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Logarithmic form of the finite-volume Jensen inequality. -/
lemma gibbs_average_n_det_le_log_exp {n : ℕ}
    (H : EnergySpace N) (f : ReplicaFun N n) :
    gibbs_average_n_det (N := N) (n := n) H f ≤
      Real.log
        (gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs))) := by
  have hjensen := gibbs_average_n_det_exp_jensen (N := N) H f
  calc
    gibbs_average_n_det (N := N) (n := n) H f =
        Real.log (Real.exp (gibbs_average_n_det (N := N) (n := n) H f)) := by
          rw [Real.log_exp]
    _ ≤ Real.log
        (gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs))) :=
      Real.log_le_log (Real.exp_pos _) hjensen

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Jensen's inequality specialized to the scaled centered-overlap square. -/
lemma scaled_centeredOverlapSq_le_log_gibbs_exp
    (H : EnergySpace N) (coupling : ℝ) :
    coupling * (N : ℝ) *
        gibbs_average_n_det (N := N) (n := 2) H (centeredOverlapSq N q) ≤
      Real.log
        (gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => Real.exp
            (coupling * (N : ℝ) * centeredOverlapSq N q σs))) := by
  have hjensen := gibbs_average_n_det_le_log_exp (N := N) H
    (fun σs : ReplicaSpace N 2 =>
      coupling * (N : ℝ) * centeredOverlapSq N q σs)
  simpa only [gibbs_average_n_det, Finset.mul_sum, mul_assoc] using hjensen

/-- Excess coupled free energy with coupling `(Λ N / 2) Q_12²`.

Adding this quantity to `interpolatedPressure` gives the two-replica coupled free energy from
the blueprint, normalized by `2N`.
-/
noncomputable def coupledExcess (t Λ : ℝ) : ℝ :=
  (1 / (2 * (N : ℝ))) * physicalLogQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t Λ

/-- Fixed-disorder normalized two-replica free energy with physical coupling `Λ`. -/
noncomputable def coupledFreeEnergyDet (H : EnergySpace N) (Λ : ℝ) : ℝ :=
  free_energy_density (N := N) H +
    (1 / (2 * (N : ℝ))) * Real.log
      (tiltedReplicaPartitionDet (N := N) (q := q) H (Λ / 2))

/-- The normalized coupled two-replica free energy. -/
noncomputable def coupledFreeEnergy (t Λ : ℝ) : ℝ :=
  interpolatedPressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t +
    coupledExcess
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t Λ

/-! ## Independent endpoint -/

/-- The one-site moment generating function for the product of two replicas. -/
noncomputable def localPairMGF (a q c : ℝ) : ℝ :=
  ∑ bs : Fin 2 → Bool,
    Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
      ∏ l : Fin 2,
        Real.exp (-(a * boolSpin (bs l))) /
          (∑ b : Bool, Real.exp (-(a * boolSpin b)))

private lemma sum_replica_site_factor (N n : ℕ)
    (G : Fin N → (Fin n → Bool) → ℝ) :
    ∑ σs : ReplicaSpace N n, ∏ i, G i (fun l => σs l i) =
      ∏ i, ∑ bs : Fin n → Bool, G i bs := by
  classical
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (transposeReplicaEquiv N n)
    (fun σs => ∏ i, G i (fun l => σs l i))
    (fun x => ∏ i, G i (x i)) (fun _ => rfl)

private lemma gibbs_average_siteEnergy_pair_mgf
    (N : ℕ) (a : Fin N → ℝ) (q c : ℝ) :
    gibbs_average_n_det (N := N) (n := 2) (siteEnergy N a)
        (fun σs => Real.exp
          (c * ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q))) =
      ∏ i : Fin N, localPairMGF (a i) q c := by
  classical
  simp only [gibbs_average_n_det, gibbs_pmf_siteEnergy, spin_eq_boolSpin]
  rw [show (∑ σs : ReplicaSpace N 2,
      Real.exp (c * ∑ i : Fin N,
        (boolSpin (σs 0 i) * boolSpin (σs 1 i) - q)) *
        ∏ l : Fin 2,
          (∏ i : Fin N,
            Real.exp (-(a i * boolSpin (σs l i))) /
              ∑ b : Bool, Real.exp (-(a i * boolSpin b)))) =
      ∑ σs : ReplicaSpace N 2,
        ∏ i : Fin N,
          (Real.exp (c *
              (boolSpin (σs 0 i) * boolSpin (σs 1 i) - q)) *
            ∏ l : Fin 2,
              Real.exp (-(a i * boolSpin (σs l i))) /
                ∑ b : Bool, Real.exp (-(a i * boolSpin b))) by
    congr 1
    funext σs
    rw [Finset.prod_comm]
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [Finset.prod_mul_distrib]]
  exact sum_replica_site_factor N 2
    (fun i bs =>
      Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
        ∏ l : Fin 2,
          Real.exp (-(a i * boolSpin (bs l))) /
            ∑ b : Bool, Real.exp (-(a i * boolSpin b)))

private lemma localPairMGF_eq (a q c : ℝ) :
    localPairMGF a q c =
      ((1 + Real.tanh a ^ 2) / 2) * Real.exp (c * (1 - q)) +
      ((1 - Real.tanh a ^ 2) / 2) * Real.exp (-c * (1 + q)) := by
  let F : (Fin 2 → Bool) → ℝ := fun bs =>
    Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
      ∏ l : Fin 2,
        Real.exp (-(a * boolSpin (bs l))) /
          (∑ b : Bool, Real.exp (-(a * boolSpin b)))
  rw [show localPairMGF a q c = ∑ bs, F bs by rfl]
  rw [Fintype.sum_equiv (finTwoArrowEquiv Bool) F
    (fun p => F ((finTwoArrowEquiv Bool).symm p)) (by
      intro x
      apply congrArg F
      funext i
      fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [F, boolSpin, Fin.prod_univ_two, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_eq, Real.cosh_eq]
  ring_nf
  simp only [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- Kearns--Saul at the independent endpoint, in the form needed for the smart path. -/
lemma endpoint_subGaussian
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) (u : ℝ) :
    nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        2 0
        (fun σs => Real.exp
          ((u / Real.sqrt N) *
            ∑ i : Fin N,
              (spin N (σs 0) i * spin N (σs 1) i - q)))
      ≤ Real.exp (kappa q * u ^ 2 / 2) := by
  classical
  let c : ℝ := u / Real.sqrt N
  let f : ReplicaFun N 2 := fun σs => Real.exp
    (c * ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q))
  let F : EnergySpace N → ℝ := fun H =>
    gibbs_average_n_det (N := N) (n := 2)
      (H + H_field (N := N) (h := h)) f
  have hFcont : Continuous F := by
    simp only [F, gibbs_average_n_det]
    apply continuous_finset_sum
    intro σs _
    apply Continuous.mul continuous_const
    apply continuous_finset_prod
    intro l _
    exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.comp
      (continuous_id.add continuous_const)
  have hHt0 (ω : Ω) :
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω =
        sim.V ω + H_field (N := N) (h := h) := by
    simp [H_t, H_gauss]
  have hrefLaw := referenceField_hasGaussianLaw N β q
  have hnu :
      nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 f =
        ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
    calc
      nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 f =
          ∫ ω, F (sim.V ω) ∂ℙ := by
            rw [nu]
            apply integral_congr_ae
            filter_upwards with ω
            simp only [gibbs_average_n]
            rw [hHt0]
      _ = ∫ H, F H ∂Measure.map sim.V ℙ := by
            rw [integral_map sim.hV.repr_measurable.aemeasurable hFcont.aestronglyMeasurable]
      _ = ∫ H, F H ∂Measure.map (referenceField N β q) (gaussianProduct N) := by
            rw [simpleDisorder_law_eq_reference N β q sim hN hq0]
      _ = ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
            rw [integral_map hrefLaw.aemeasurable hFcont.aestronglyMeasurable]
  let A : ℝ :=
    ((1 + q) / 2) * Real.exp (c * (1 - q)) +
      ((1 - q) / 2) * Real.exp (-c * (1 + q))
  have htanh : Integrable
      (fun z : ℝ => Real.tanh (h + β * Real.sqrt q * z) ^ 2)
      (gaussianReal 0 1) := by
    have htanh_cont : Continuous Real.tanh := by
      rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => (Real.cosh_pos x).ne')
    apply (integrable_const (1 : ℝ)).mono
    · exact (htanh_cont.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards with z
      simp only [Real.norm_eq_abs, abs_pow, abs_one]
      rw [sq_abs]
      exact (Real.tanh_sq_lt_one _).le
  have hlocal :
      ∫ z, localPairMGF (h + β * Real.sqrt q * z) q c ∂gaussianReal 0 1 = A := by
    have hT :
        ∫ z, Real.tanh (h + β * Real.sqrt q * z) ^ 2 ∂gaussianReal 0 1 = q := by
      simpa [IsRSFixedPoint, standardGaussianExpectation] using hfp.symm
    rw [show (∫ z, localPairMGF (h + β * Real.sqrt q * z) q c
          ∂gaussianReal 0 1) =
        ∫ z,
          ((Real.exp (c * (1 - q)) + Real.exp (-c * (1 + q))) / 2 +
            Real.tanh (h + β * Real.sqrt q * z) ^ 2 *
              ((Real.exp (c * (1 - q)) - Real.exp (-c * (1 + q))) / 2))
          ∂gaussianReal 0 1 by
      apply integral_congr_ae
      filter_upwards with z
      rw [localPairMGF_eq]
      ring]
    rw [integral_add (integrable_const _)
      (htanh.mul_const ((Real.exp (c * (1 - q)) - Real.exp (-c * (1 + q))) / 2))]
    simp only [integral_const, probReal_univ, one_smul, integral_mul_const, hT]
    simp only [A]
    ring
  have hfactor :
      ∫ z, F (referenceField N β q z) ∂gaussianProduct N = A ^ N := by
    rw [show (∫ z, F (referenceField N β q z) ∂gaussianProduct N) =
        ∫ z, ∏ i : Fin N,
          localPairMGF (h + β * Real.sqrt q * z i) q c ∂gaussianProduct N by
      apply integral_congr_ae
      filter_upwards with z
      simp only [F]
      change gibbs_average_n_det (N := N) (n := 2)
        (referenceField N β q z + magnetic_field_vector (N := N) h) f = _
      rw [reference_add_field_eq_siteEnergy,
        gibbs_average_siteEnergy_pair_mgf]]
    rw [gaussianProduct]
    calc
      (∫ z : Fin N → ℝ, ∏ i : Fin N,
          localPairMGF (h + β * Real.sqrt q * z i) q c
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
          (∫ z, localPairMGF (h + β * Real.sqrt q * z) q c
            ∂gaussianReal 0 1) ^ Fintype.card (Fin N) :=
        MeasureTheory.integral_fintype_prod_eq_pow
          (f := fun z : ℝ => localPairMGF (h + β * Real.sqrt q * z) q c)
      _ = A ^ N := by simpa using congrArg (fun x => x ^ N) hlocal
  have hkappa : kappa q = ksCoefficient q := by
    simp [kappa, ksCoefficient]
  have hKS : A ≤ Real.exp (kappa q * c ^ 2 / 2) := by
    simpa only [A, hkappa] using
      (kearns_saul_inequality (u := c) hq0 hq1)
  have hA0 : 0 ≤ A := by
    simp only [A]
    apply add_nonneg
    · exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (Real.exp_nonneg _)
    · exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (Real.exp_nonneg _)
  have hpow : A ^ N ≤ (Real.exp (kappa q * c ^ 2 / 2)) ^ N :=
    pow_le_pow_left₀ hA0 hKS N
  rw [show nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 0 (fun σs => Real.exp
        ((u / Real.sqrt N) * ∑ i : Fin N,
          (spin N (σs 0) i * spin N (σs 1) i - q))) = A ^ N by
    change nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 0 f = A ^ N
    exact hnu.trans hfactor]
  calc
    A ^ N ≤ (Real.exp (kappa q * c ^ 2 / 2)) ^ N := hpow
    _ = Real.exp (kappa q * u ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      simp only [c]
      rw [div_pow, Real.sq_sqrt hNr.le]
      field_simp [ne_of_gt hNr]

/-- Hubbard--Stratonovich combined with `endpoint_subGaussian`. -/
lemma endpoint_quadratic
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : kappa q * Λ < 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 (Λ / 2)
      ≤ (1 / 2) * Real.log (1 / (1 - kappa q * Λ)) := by
  classical
  let F : ReplicaFun N 2 := fun σs => Real.exp
    ((Λ / 2) * (N : ℝ) * centeredOverlapSq N q σs)
  let A : Ω → ℝ := gibbs_average_n
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 F
  let S : ReplicaSpace N 2 → ℝ := fun σs =>
    ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q)
  let B : ℝ → Ω → ℝ := fun z ω =>
    gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0
      (fun σs => Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)) ω
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN : Real.sqrt (N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hNr
  have hS (σs : ReplicaSpace N 2) :
      S σs = (N : ℝ) * (overlap N (σs 0) (σs 1) - q) := by
    simp only [S, overlap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul]
    field_simp
  have hHS (σs : ReplicaSpace N 2) :
      F σs = ∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
        ∂gaussianReal 0 1 := by
    calc
      F σs = Real.exp (Λ * (Real.sqrt N *
          (overlap N (σs 0) (σs 1) - q)) ^ 2 / 2) := by
        simp only [F, centeredOverlapSq]
        congr 1
        rw [mul_pow, Real.sq_sqrt hNr.le]
        ring
      _ = ∫ z, Real.exp (Real.sqrt Λ *
          (Real.sqrt N * (overlap N (σs 0) (σs 1) - q)) * z)
          ∂gaussianReal 0 1 := hubbard_stratonovich Λ _ hΛ0
      _ = ∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
          ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hS]
        congr 1
        field_simp
        rw [Real.sq_sqrt hNr.le]
        ring
  have hlin_int (σs : ReplicaSpace N 2) :
      Integrable (fun z => Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs))
        (gaussianReal 0 1) := by
    convert integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (Real.sqrt Λ * S σs / Real.sqrt N) using 1
    funext z
    congr 1
    ring
  have hAeq (ω : Ω) : A ω = ∫ z, B z ω ∂gaussianReal 0 1 := by
    simp only [A, B, gibbs_average_n, gibbs_average_n_det]
    rw [show (∑ σs : ReplicaSpace N 2,
        F σs * ∏ l, gibbs_pmf N
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
          (σs l)) =
        ∑ σs : ReplicaSpace N 2,
          (∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
            ∂gaussianReal 0 1) *
          ∏ l, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
            (σs l) by
      congr 1
      funext σs
      rw [hHS]]
    simp_rw [← integral_mul_const]
    rw [integral_finset_sum]
    intro σs _
    exact (hlin_int σs).mul_const _
  have hAint : Integrable A ℙ := by
    exact integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 F
  have hAone (ω : Ω) : 1 ≤ A ω := by
    simp only [A, gibbs_average_n, F, centeredOverlapSq, gibbs_average_n_det]
    rw [← sum_prod_gibbs_pmf_eq_one
      (N := N) (n := 2)
      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)]
    apply Finset.sum_le_sum
    intro σs _
    have hexp : 1 ≤ Real.exp
        (Λ / 2 * (N : ℝ) * (overlap N (σs 0) (σs 1) - q) ^ 2) :=
      Real.one_le_exp (mul_nonneg
        (mul_nonneg (div_nonneg hΛ0 (by norm_num)) (Nat.cast_nonneg N))
        (sq_nonneg _))
    have hweight : 0 ≤ ∏ l, gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
        (σs l) := by
      apply Finset.prod_nonneg
      intro l _
      exact gibbs_pmf_nonneg
        (N := N)
        (H := H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) 0 ω)
        (σ := σs l)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hweight
  have hlogAint : Integrable (fun ω => Real.log (A ω)) ℙ := by
    apply hAint.mono'
    · exact (Real.measurable_log.comp_aemeasurable hAint.aemeasurable).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hAone ω))]
      exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (hAone ω))).trans
        (sub_le_self _ zero_le_one)
  have hJensen : (∫ ω, Real.log (A ω) ∂ℙ) ≤ Real.log (∫ ω, A ω ∂ℙ) := by
    have hj := (strictConcaveOn_log_Ioi.concaveOn.subset
      (Set.Ici_subset_Ioi.2 zero_lt_one) (convex_Ici (1 : ℝ))).le_map_integral
      (f := A) (μ := ℙ)
      (Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (zero_lt_one.trans_le hx)))
      isClosed_Ici (ae_of_all _ hAone) hAint
      (hlogAint.congr (ae_of_all _ fun ω => by rfl))
    exact hj
  have hweight_int (σs : ReplicaSpace N 2) : Integrable (fun ω =>
      ∏ l, gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
        (σs l)) ℙ := by
    let I : ReplicaFun N 2 := fun τs => if τs = σs then 1 else 0
    have hi := integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 I
    convert hi using 1
    funext ω
    simp [I, gibbs_average_n, gibbs_average_n_det]
  have hBprod : Integrable (fun p : ℝ × Ω => B p.1 p.2)
      ((gaussianReal 0 1).prod ℙ) := by
    simp only [B, gibbs_average_n, gibbs_average_n_det]
    apply integrable_finset_sum
    intro σs _
    exact (hlin_int σs).mul_prod (hweight_int σs)
  have hBbound (z : ℝ) :
      (∫ ω, B z ω ∂ℙ) ≤ Real.exp (kappa q * Λ * z ^ 2 / 2) := by
    have hend := endpoint_subGaussian
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hq1 hfp (Real.sqrt Λ * z)
    simpa only [B, S, nu, mul_pow, Real.sq_sqrt hΛ0, mul_assoc] using hend
  have hquad_int : Integrable (fun z : ℝ => Real.exp (kappa q * Λ * z ^ 2 / 2))
      (gaussianReal 0 1) := by
    have hi := ProbabilityTheory.integrable_polynomial_exp_sq_gaussian_param_nondeg
      (v := (1 : ℝ≥0)) (by norm_num) 0
      (s := kappa q * Λ / 2) (by norm_num; linarith)
    convert hi using 1
    funext z
    ring
  have hquad_eq :
      (∫ z, Real.exp (kappa q * Λ * z ^ 2 / 2) ∂gaussianReal 0 1) =
        1 / Real.sqrt (1 - kappa q * Λ) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp only [smul_eq_mul, gaussianPDFReal]
    norm_num only [NNReal.coe_one, zero_sub, sub_zero, mul_one]
    rw [show (∫ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
        Real.exp (kappa q * Λ * x ^ 2 / 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 - kappa q * Λ) / 2) * x ^ 2) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring]
    rw [integral_gaussian]
    have hgap : 0 < 1 - kappa q * Λ := sub_pos.mpr hΛ
    rw [show Real.pi / ((1 - kappa q * Λ) / 2) =
        (2 * Real.pi) / (1 - kappa q * Λ) by field_simp]
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi),
      Real.sqrt_ne_zero'.mpr hgap]
  have hAmean : (∫ ω, A ω ∂ℙ) ≤ 1 / Real.sqrt (1 - kappa q * Λ) := by
    calc
      (∫ ω, A ω ∂ℙ) = ∫ ω, ∫ z, B z ω ∂gaussianReal 0 1 ∂ℙ := by
        apply integral_congr_ae
        exact ae_of_all _ hAeq
      _ = ∫ z, ∫ ω, B z ω ∂ℙ ∂gaussianReal 0 1 := by
        exact (integral_integral_swap hBprod).symm
      _ ≤ ∫ z, Real.exp (kappa q * Λ * z ^ 2 / 2) ∂gaussianReal 0 1 := by
        exact integral_mono hBprod.integral_prod_left hquad_int hBbound
      _ = 1 / Real.sqrt (1 - kappa q * Λ) := hquad_eq
  have hAmean_one : 1 ≤ ∫ ω, A ω ∂ℙ := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const (1 : ℝ)) hAint hAone
  change (∫ ω, Real.log (A ω) ∂ℙ) ≤
    (1 / 2) * Real.log (1 / (1 - kappa q * Λ))
  calc
    (∫ ω, Real.log (A ω) ∂ℙ) ≤ Real.log (∫ ω, A ω ∂ℙ) := hJensen
    _ ≤ Real.log (1 / Real.sqrt (1 - kappa q * Λ)) :=
      Real.log_le_log (zero_lt_one.trans_le hAmean_one) hAmean
    _ = (1 / 2) * Real.log (1 / (1 - kappa q * Λ)) := by
      have hgap : 0 ≤ 1 - kappa q * Λ := (sub_pos.mpr hΛ).le
      simp only [one_div, ← Real.sqrt_inv]
      rw [Real.log_sqrt (inv_nonneg.mpr hgap)]
      ring

/-! ## Gaussian interpolation and quadratic coupling -/

/-- Differentiation of the smart-path pressure before Gaussian integration by parts. -/
lemma pressure_derivative_before_ibp
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) t := by
  classical
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) := lt_min ht0 h1t0
    have : 0 < (min t (1 - t)) / 2 := by linarith
    simpa [ε] using this
  have hball_Ioo : ∀ x ∈ Metric.ball t ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
    have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    have hx_lower : t / 2 < x := by
      have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      exact lt_of_le_of_lt ht_eps hx_gt
    have hx_gt0 : 0 < x := by
      have ht_eps : t - ε ≥ t / 2 := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      have : t / 2 < x := lt_of_le_of_lt ht_eps hx_gt
      have : 0 < t / 2 := by nlinarith [ht0]
      exact Std.lt_trans this hx_lower
    have hx_lt1 : x < 1 := by
      have hx_lt : x < t + ε := by linarith
      have ht_eps : t + ε ≤ (1 + t) / 2 := by nlinarith [hε_le_1t]
      have : x < (1 + t) / 2 := lt_of_lt_of_le hx_lt ht_eps
      have : (1 + t) / 2 < 1 := by nlinarith [ht1]
      simp; grind
    exact ⟨hx_gt0, hx_lt1⟩
  let F : ℝ → Ω → ℝ :=
    fun s w => free_energy_density (N := N) (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
  let F' : ℝ → Ω → ℝ :=
    fun s w =>
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt s)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - s))
      exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s
    exact ((contDiff_free_energy_density (N := N)).continuous.measurable.comp
      hH_meas).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) := by
    let C : ℝ := (SpinGlass.hasModerateGrowth_free_energy_density N).C
    have hH_meas : Measurable
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t
    have hF_meas : AEStronglyMeasurable (F t) (ℙ : Measure Ω) :=
      ((contDiff_free_energy_density (N := N)).continuous.measurable.comp
        hH_meas).aestronglyMeasurable
    let boundFun : Ω → ℝ := fun w => C * (1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖)
    have hbound_int : Integrable boundFun (ℙ : Measure Ω) := by
      apply Integrable.const_mul
      exact (((integrable_const (1 : ℝ)).add
        (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)).add
          (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)).add
            (integrable_const _)
    refine MeasureTheory.Integrable.mono' hbound_int hF_meas ?_
    have hsqrtt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsqrtt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt ht1)
    have hsqrt1t0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hsqrt1t1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [ht0])
    filter_upwards with w
    have hnorm : ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      calc
        ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖
            ≤ ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ +
                ‖H_field (N := N) (h := h)‖ := by
          simp only [H_t, H_gauss]
          exact (norm_add_le
            ((Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w)
            (H_field (N := N) (h := h))).trans
            (by
              gcongr
              exact norm_add_le ((Real.sqrt t) • sk.U w)
                ((Real.sqrt (1 - t)) • sim.V w))
        _ ≤ ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hsqrtt0, abs_of_nonneg hsqrt1t0]
            gcongr
            · exact mul_le_of_le_one_left (norm_nonneg _) hsqrtt1
            · exact mul_le_of_le_one_left (norm_nonneg _) hsqrt1t1
    have hgrowth :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).F_bound
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    have hm : (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 := by rfl
    rw [hm, pow_one] at hgrowth
    rw [Real.norm_eq_abs]
    have hinside : 1 + ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hinside
      (le_of_lt (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos)
    exact hgrowth.trans (by simpa only [C] using hmul)
  -- Define the bound
  let Cf : ℝ := 1 / (N : ℝ)
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let bound : Ω → ℝ := fun w => Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖)
  have hCf_nonneg : 0 ≤ Cf := by positivity
  have hcU_nonneg : 0 ≤ cU := by positivity
  have hcV_nonneg : 0 ≤ cV := by positivity
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)
    have h1 : Integrable (fun w => cU * ‖sk.U w‖) (ℙ : Measure Ω) := (hU_int.const_mul cU)
    have h2 : Integrable (fun w => cV * ‖sim.V w‖) (ℙ : Measure Ω) := (hV_int.const_mul cV)
    have hsum : Integrable (fun w => cU * ‖sk.U w‖ + cV * ‖sim.V w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, Cf, mul_add, mul_assoc] using hsum.const_mul Cf
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    have hdH_meas : Measurable (fun w => dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [dH_t]
      have hU := sk.hU.repr_measurable.const_smul ((1 : ℝ) / (2 * Real.sqrt t))
      have hV := sim.hV.repr_measurable.const_smul ((1 : ℝ) / (2 * Real.sqrt (1 - t)))
      exact measurable_dH_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t
    have hHM : Measurable (fun w => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t
    have hfderiv_cont : Continuous (fun p : EnergySpace N × EnergySpace N =>
        fderiv ℝ (fun H => free_energy_density (N := N) H) p.1 p.2) := by
      have hcd := contDiff_free_energy_density (N := N)
      have hfderiv_cont' : Continuous (fun H => fderiv ℝ (fun H => free_energy_density (N := N) H) H) :=
        hcd.continuous_fderiv (by simp)
      exact ((hfderiv_cont'.comp continuous_fst).clm_apply continuous_snd)
    have hpair : Measurable (fun w => (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w,
        dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)) :=
      hHM.prodMk hdH_meas
    exact (hfderiv_cont.measurable.comp hpair).aestronglyMeasurable
  have h_bound :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x w‖ ≤ bound w := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    -- Bound the operator norm of the derivative of free_energy_density
    have h_op :
        ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ (1 / (N : ℝ)) := by
      refine ContinuousLinearMap.opNorm_le_bound _ hCf_nonneg ?_
      intro v
      have h_eval :
          (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v =
            -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * v σ :=
        fderiv_free_energy_density_apply (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) (h := v)
      have hs1 : (∑ σ : Config N, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) = 1 :=
        sum_gibbs_pmf (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)
      have hsum_bound :
          |∑ σ : Config N, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| ≤ ‖v‖ := by
        have h_abs_le :
            |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|
              ≤ ∑ σ : Config N, |gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σ : Config N => gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ)
              (s := (Finset.univ : Finset (Config N))))
        have h_abs_term :
            (∑ σ : Config N, |gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|)
              = ∑ σ : Config N, (gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ| := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          have hg : 0 ≤ gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ :=
            gibbs_pmf_nonneg (N := N)
              (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ
          simp [abs_mul, abs_of_nonneg hg]
        have hsum_le :
            (∑ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ|)
              ≤ (∑ σ : Config N, gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
          have hterm : ∀ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ|
                ≤ (gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
            intro σ
            have hσ : |v σ| ≤ ‖v‖ := (abs_apply_le_norm (N := N) v σ)
            exact mul_le_mul_of_nonneg_left hσ (gibbs_pmf_nonneg (N := N)
              (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ)
          have hsum' :=
            (Finset.sum_le_sum (s := (Finset.univ : Finset (Config N)))
              (fun σ _ => hterm σ))
          have hfactor :
              (∑ σ : Config N, (gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖)
                = (∑ σ : Config N, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                (f := fun σ : Config N => gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ)
                (a := ‖v‖)).symm
          simpa [hfactor] using hsum'
        calc
          |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|
            ≤ ∑ σ : Config N, |gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := h_abs_le
          _ = ∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * |v σ| := h_abs_term
          _ ≤ (∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := hsum_le
          _ = ‖v‖ := by simp [hs1]
      have : ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
          ≤ (1 / (N : ℝ)) * ‖v‖ := by
        have :
            ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
              = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := by
          simp [h_eval, Real.norm_eq_abs]
        calc
          ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
          = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := this
          _ ≤ (1 / (N : ℝ)) * ‖v‖ := by
                exact mul_le_mul_of_nonneg_left hsum_bound hCf_nonneg
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have hL :
        ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ Cf := by
      simpa [Cf] using h_op
    -- Bound the coefficients
    have hCoeffU :
        |1 / (2 * Real.sqrt x)| ≤ cU := by
      have hx_gt0 : 0 < x := hxIoo.1
      have hx_lower : t / 2 ≤ x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
        have hε_le_t : ε ≤ t / 2 := by
          have : min t (1 - t) ≤ t := min_le_left _ _
          have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
          simpa [ε] using this
        have hx_gt : t - ε < x := by linarith
        have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
        exact le_trans ht_eps (le_of_lt hx_gt)
      have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_lower
      have hpos : 0 < 2 * Real.sqrt (t / 2) := by
        have : 0 < Real.sqrt (t / 2) := by
          have : 0 < t / 2 := by nlinarith [ht0]
          exact Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
      simpa [cU, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg', abs_of_nonneg (Real.sqrt_nonneg x), one_div]
        using this
    have hCoeffV :
        |1 / (2 * Real.sqrt (1 - x))| ≤ cV := by
      have hx_lt1 : x < 1 := hxIoo.2
      have h1x_pos : 0 < 1 - x := by linarith
      have h1x_lower : (1 - t) / 2 ≤ 1 - x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
        have hε_le_1t : ε ≤ (1 - t) / 2 := by
          have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
          have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
          simpa [ε] using this
        have hx_le : x ≤ t + (1 - t) / 2 := by
          have hx_le' : x ≤ t + ε := by linarith
          exact le_trans hx_le' (by nlinarith [hε_le_1t])
        nlinarith [hx_le]
      have hsqrt_le : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt h1x_lower
      have hpos : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
        have : 0 < (1 - t) / 2 := by nlinarith [h1t0]
        have : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - x) := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt (1 - x)) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
      simpa [cV, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg',
        abs_of_nonneg (Real.sqrt_nonneg (1 - x)), one_div] using this
    -- Bound ‖dH_t x w‖
    have hdH_norm :
        ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
      have htri :
          ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
              |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖ := by
        simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
          (norm_add_le ((1 / (2 * Real.sqrt x)) • sk.U w) (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))
      have : |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
        gcongr
      exact le_trans htri this
    -- Combine bounds
    have hF'_bound :
        ‖F' x w‖ ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w‖ := by
      have hop : ‖(fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖
          ≤ ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
            ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hmul :
          ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
            ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      simpa [F'] using le_trans hop hmul
    have : ‖F' x w‖ ≤ bound w := by
      have : ‖F' x w‖ ≤ Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖) := by
        exact le_trans hF'_bound (mul_le_mul_of_nonneg_left hdH_norm (hCf_nonneg))
      simpa [bound, mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  have h_diff :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s w) (F' x w) x := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    -- Chain rule: F = free_energy_density ∘ H_t, so dF/ds = fderiv(free_energy_density) ∘ dH_t/ds
    have hHt_diff : HasDerivAt
        (fun s => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) x :=
      hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x hxIoo w
    have hFed : HasFDerivAt (fun H => free_energy_density (N := N) H)
        (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) :=
      ((contDiff_free_energy_density (N := N)).differentiable (by simp) ).differentiableAt.hasFDerivAt
    have hcomp := hFed.comp_hasDerivAt x hHt_diff
    change HasDerivAt
      ((fun H : EnergySpace N => free_energy_density (N := N) H) ∘
        fun s => H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w)
      (F' x w) x
    simpa [F'] using hcomp
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  change HasDerivAt (fun s => ∫ w, F s w ∂ℙ) (∫ w, F' t w ∂ℙ) t
  exact hMain

/-!
### How to invoke the Hilbert-space Gaussian IBP theorem

The theorem intended here is
`PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op` from
`SpinGlass.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert`.  Its schematic form is

```
E[⟪g, e⟫ * F(g)] = E[(fderiv ℝ F (g)) ((covOp hg) e)].
```

It requires `hg : IsGaussianHilbert g`, `ContDiff ℝ 1 F`, and
`HasModerateGrowth F`.  The disorder structures already provide the Gaussian models
`sk.hU` and `sim.hV`, while `sk.cov_eq` and `sim.cov_eq` identify the matrix entries of their
covariance operators in the configuration basis.

There is one important formal point.  The first-variation test function depends on both
`sk.U` and `sim.V`, so calling the theorem on `sk.hU` while leaving `sim.V ω` inside the test
function is not valid.  A convenient bridge is a local lemma constructing

```
G ω := (sk.U ω, sim.V ω)
```

as an `IsGaussianHilbert` random variable on the product Hilbert space.  Build its basis from
the two component bases, and use `hIndep` to prove that the two coordinate families are jointly
independent.  Its covariance operator is block diagonal.  This bridge is the only additional
Gaussian-model construction needed by the affine joint-IBP lemma below.

For the SK term, set

```
Φ p := free_energy_density (N := N) (a • p.1 + b • p.2 + field)
Fσ p := (fderiv ℝ Φ p) (std_basis N σ, 0)
```

and expand the random direction in the configuration basis.  For each `σ`, the main call is
schematically

```
have hIBP :=
  PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op
    (hg := hG) (h := (std_basis N σ, 0)) (F := Fσ)
    (hF_diff := hFσ_diff) (hF_growth := hFσ_growth)
```

The derivative of `Fσ` is the Hessian of the pressure.  Expand the block covariance vector in
the configuration basis, use `sk.cov_eq σ τ`, interchange the finite sums with the integral,
and collect `a * a'`.  The simple-disorder term uses `(0, std_basis N σ)` and
`sim.cov_eq σ τ` in exactly the same way.

The required smoothness follows from `contDiff_free_energy_density`.  For moderate growth,
prove a small helper for each `Fσ`; the explicit Gibbs Hessian is uniformly bounded in finite
volume, so a constant polynomial bound suffices.  The integrability helpers surrounding the
IBP theorem then justify every finite-sum and expectation interchange.
-/

/-- Measurability of a configuration-basis entry of the pressure Hessian.  This helper is
shared by both covariance traces. -/
lemma measurable_hessian_free_energy_std_basis (σ τ : Config N) :
    Measurable (fun H : EnergySpace N =>
      hessian_free_energy N H (std_basis N σ) (std_basis N τ)) := by
  simp_rw [hessian_free_energy]
  apply Measurable.mul measurable_const
  apply Measurable.sub
  · exact Finset.measurable_sum _ fun x _ => by
      apply Measurable.mul _ measurable_const
      apply Measurable.mul _ measurable_const
      exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
  · apply Measurable.mul
    · exact Finset.measurable_sum _ fun x _ => by
        apply Measurable.mul
        · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
        · exact measurable_const
    · exact Finset.measurable_sum _ fun x _ => by
        apply Measurable.mul
        · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
        · exact measurable_const

/-- Uniform finite-volume bound for a configuration-basis entry of the pressure Hessian. -/
lemma abs_hessian_free_energy_std_basis_le
    (H : EnergySpace N) (σ τ : Config N) :
    |hessian_free_energy N H (std_basis N σ) (std_basis N τ)| ≤ 1 / (N : ℝ) := by
  classical
  have hσ0 : 0 ≤ gibbs_pmf N H σ := gibbs_pmf_nonneg N H σ
  have hτ0 : 0 ≤ gibbs_pmf N H τ := gibbs_pmf_nonneg N H τ
  have hσ1 : gibbs_pmf N H σ ≤ 1 := gibbs_pmf_le_one N H σ
  have hτ1 : gibbs_pmf N H τ ≤ 1 := gibbs_pmf_le_one N H τ
  by_cases hστ : σ = τ
  · subst τ
    simp [hessian_free_energy, std_basis]
    have hp : 0 ≤ gibbs_pmf N H σ - gibbs_pmf N H σ * gibbs_pmf N H σ := by
      nlinarith
    rw [abs_of_nonneg hp]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hp1 : gibbs_pmf N H σ - gibbs_pmf N H σ * gibbs_pmf N H σ ≤ 1 := by
      nlinarith
    calc
      (N : ℝ)⁻¹ * (gibbs_pmf N H σ - gibbs_pmf N H σ * gibbs_pmf N H σ)
          ≤ (N : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hp1 (inv_nonneg.mpr hN0)
      _ = (N : ℝ)⁻¹ := mul_one _
  · simp [hessian_free_energy, std_basis, hστ]
    rw [abs_of_nonneg hσ0, abs_of_nonneg hτ0]
    calc
      (N : ℝ)⁻¹ * (gibbs_pmf N H σ * gibbs_pmf N H τ)
          ≤ (N : ℝ)⁻¹ * 1 := by
            have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            exact mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.mpr hN0)
      _ = (N : ℝ)⁻¹ := by ring

/-- Gaussian integration by parts for an affine combination of two independent Gaussian
Hamiltonians, expressed in the canonical configuration basis.

This is the sole measure-theoretic Gaussian-IBP interface used by the ordinary smart path.
Construct the product-Hilbert Gaussian model described above, apply the operator-form theorem
along the two block basis directions, use block diagonality, and collect the coefficients.
Keeping both covariance traces in one statement avoids duplicating the conditional or product
law argument. -/
lemma independent_gaussian_affine_ibp
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field) (a' • sk.U w + b' • sim.V w) ∂ℙ) =
      (a * a') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        sk_cov_kernel N β σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ +
      (b * b') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  exact independent_gaussian_affine_ibp_reproved
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hIndep a b a' b' field

/-- Joint Gaussian integration by parts for the raw smart-path derivative, before evaluating
its two covariance traces. -/
lemma pressure_derivative_ibp_trace
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (1 / 2) * ∫ w,
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
          hessian_free_energy N
            (H_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) t w)
            (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  have ht0 : t > 0 := ht.1
  have ht1 : t < 1 := ht.2
  -- Set up the IBP parameters
  set a := Real.sqrt t with ha_def
  set b := Real.sqrt (1 - t) with hb_def
  set a' := 1 / (2 * Real.sqrt t) with ha'_def
  set b' := -1 / (2 * Real.sqrt (1 - t)) with hb'_def
  -- Apply the independent_gaussian_affine_ibp lemma
  have h_ibp := independent_gaussian_affine_ibp (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hIndep a b a' b' (H_field (N := N) (h := h))
  -- Show that a * a' = 1/2 and b * b' = -1/2
  have ha_aa' : a * a' = 1 / 2 := by
    simp [ha_def, ha'_def]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr ht0)]
  have hb_bb' : b * b' = -(1 / 2) := by
    simp [hb_def, hb'_def]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ht1))]
  -- Show that a • sk.U w + b • sim.V w + H_field = H_t t w
  have h_eq_H : H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t =
      fun w => a • sk.U w + b • sim.V w + H_field (N := N) (h := h) := by
    unfold H_t H_gauss
    simp [ha_def, hb_def]
  -- Show that a' • sk.U w + b' • sim.V w = dH_t t w
  have h_eq_dH : dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t =
      fun w => a' • sk.U w + b' • sim.V w := by
    unfold dH_t
    ext w
    simp [ha'_def, hb'_def]
    ring
  -- Rewrite h_ibp using the equalities
  have h_ibp' : ∫ w, fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) ∂ℙ =
    (a * a') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
      sk_cov_kernel N β σ τ * hessian_free_energy N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (std_basis N σ) (std_basis N τ)) ∂ℙ +
    (b * b') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
      simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (std_basis N σ) (std_basis N τ)) ∂ℙ := by
    simp only [h_eq_H, h_eq_dH] at *
    convert h_ibp using 2
  -- Substitute a * a' = 1/2 and b * b' = -1/2
  rw [ha_aa', hb_bb'] at h_ibp'
  -- Combine the integrals
  convert h_ibp' using 1
  have integral_eq : ∀ w, ∑ σ, ∑ τ, (sk_cov_kernel N β σ τ - simple_cov_kernel N β (fun x => q * x) σ τ) *
      hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ) =
      (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ)) -
      (∑ σ, ∑ τ, simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ)) := by
    intro w
    simp_rw [sub_mul]
    simp only [Finset.sum_sub_distrib]
  -- Bound on hessian_free_energy for standard basis
  have std_basis_apply : ∀ σ τ : Config N, (std_basis N σ) τ = if σ = τ then 1 else 0 := by
    intro σ τ
    simp [std_basis]
  -- Integrability of finite sums of bounded functions
  have h_int1 : MeasureTheory.Integrable
      (fun x => ∑ σ : Config N, ∑ τ : Config N,
        sk_cov_kernel N β σ τ * hessian_free_energy N (H_t N β h q sk sim t x) (std_basis N σ) (std_basis N τ))
      ℙ := by
    apply MeasureTheory.integrable_finset_sum _
    intro σ _
    apply MeasureTheory.integrable_finset_sum _
    intro τ _
    refine MeasureTheory.Integrable.const_mul ?_ (sk_cov_kernel N β σ τ)
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 / (N : ℝ))) ?_ ?_
    · have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
        have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
        have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
        exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t
      have hheff_meas : Measurable
          (fun H => hessian_free_energy N H (std_basis N σ) (std_basis N τ)) :=
        measurable_hessian_free_energy_std_basis (N := N) σ τ
      exact (hheff_meas.comp hH_meas).aestronglyMeasurable
    · filter_upwards with x
      exact abs_hessian_free_energy_std_basis_le
        (N := N)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t x) σ τ
  have h_int2 : MeasureTheory.Integrable
      (fun x => ∑ σ : Config N, ∑ τ : Config N,
        simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t N β h q sk sim t x) (std_basis N σ) (std_basis N τ))
      ℙ := by
    apply MeasureTheory.integrable_finset_sum _
    intro σ _
    apply MeasureTheory.integrable_finset_sum _
    intro τ _
    refine MeasureTheory.Integrable.const_mul ?_ (simple_cov_kernel N β (fun x => q * x) σ τ)
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 / (N : ℝ))) ?_ ?_
    · have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
        have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
        have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
        exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t
      have hheff_meas : Measurable
          (fun H => hessian_free_energy N H (std_basis N σ) (std_basis N τ)) :=
        measurable_hessian_free_energy_std_basis (N := N) σ τ
      exact (hheff_meas.comp hH_meas).aestronglyMeasurable
    · filter_upwards with x
      exact abs_hessian_free_energy_std_basis_le
        (N := N)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t x) σ τ
  rw [funext integral_eq, MeasureTheory.integral_sub h_int1 h_int2]
  rw [mul_sub]
  ring

/-
The covariance-trace difference is the centered-overlap square, pointwise in the disorder.
-/
lemma pressure_trace_algebra
    (hN : 0 < N) (H : EnergySpace N) :
    (1 / 2) *
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
          hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β ^ 2 / 4) * ((1 - q) ^ 2 -
        gibbs_average_n_det (N := N) (n := 2) H (centeredOverlapSq N q)) := by
  unfold gibbs_average_n_det centeredOverlapSq;
  have h_sum_gibbs_pmf : ∑ σ : Config N, gibbs_pmf N H σ = 1 := by
    exact sum_gibbs_pmf (N := N) (H := H)
  have h_sum_prod_gibbs_pmf : ∑ σs : ReplicaSpace N 2, (∏ l, gibbs_pmf N H (σs l)) * (overlap N (σs 0) (σs 1) - q) ^ 2 = ∑ σ : Config N, ∑ τ : Config N, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q) ^ 2 := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x 0, x 1 ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h₀ h₁ => funext fun i => by fin_cases i <;> assumption;
    · exact fun a b => ⟨ fun i => if i = 0 then a else b, rfl, rfl ⟩;
  convert congr_arg ( fun x : ℝ => β ^ 2 / 4 * ( ( 1 - q ) ^ 2 - x ) ) h_sum_prod_gibbs_pmf using 1;
  · convert SpinGlass.guerra_derivative_bound_algebra_core hN H ( fun x => q * x ) using 1;
    any_goals exact β;
    · simp +decide only [sub_mul, Finset.sum_sub_distrib];
    · rw [ h_sum_prod_gibbs_pmf ] ; ring;
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_sum_gibbs_pmf ] ; ring;
  · simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-- The annealed Gibbs average of the centered overlap square is `overlapVariance`. -/
lemma integral_centeredOverlapSq_eq_overlapVariance (t : ℝ) :
    (∫ w, gibbs_average_n_det (N := N) (n := 2)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w) (centeredOverlapSq N q) ∂ℙ) =
      overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  rfl

/-
Gaussian integration by parts evaluates the raw smart-path pressure derivative.
-/
lemma pressure_derivative_ibp
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (β ^ 2 / 4) * ((1 - q) ^ 2 -
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
  have := @SpinGlass.GeneralizedLatala.pressure_derivative_ibp_trace;
  rw [ this N β h q sk sim hIndep ht, MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall fun w => ?_ ) ];
  any_goals exact fun w => ( β ^ 2 / 4 ) * ( ( 1 - q ) ^ 2 - gibbs_average_n_det ( N := N ) ( n := 2 ) ( H_t N β h q sk sim t w ) ( centeredOverlapSq N q ) ) * 2;
  · rw [ MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
    rw [ MeasureTheory.integral_sub ] <;> norm_num;
    · rw [ integral_centeredOverlapSq_eq_overlapVariance ] ; ring;
    · apply_rules [ SpinGlass.integrable_gibbs_average_n ];
  · have htrace := pressure_trace_algebra (N := N) (β := β) (q := q)
      hN (H_t N β h q sk sim t w)
    linarith

/-- The ordinary Guerra smart-path sum-rule derivative.

The repository already provides the smart path and Hilbert-space Gaussian integration by parts.
This lemma records their specialization to the centered overlap square.
-/
lemma pressure_derivative
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      ((β ^ 2 / 4) * ((1 - q) ^ 2 -
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t)) t := by
  rw [← pressure_derivative_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep ht]
  exact pressure_derivative_before_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ht

/-! ## Coupled smart path and its characteristic

The lemmas in this section deliberately use `HasDerivAt`.  Thus the differential identities
also carry the regularity needed by the later chain-rule and endpoint arguments.
-/

private lemma tiltedLog_hasDerivAt_coupling
    (H : EnergySpace N) (coupling : ℝ) :
    HasDerivAt
      (fun c => Real.log (tiltedReplicaPartitionDet (N := N) (q := q) H c))
      ((N : ℝ) * tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling)
      coupling := by
  classical
  let A : ReplicaSpace N 2 → ℝ := fun σs =>
    (N : ℝ) * centeredOverlapSq N q σs
  let W : ReplicaSpace N 2 → ℝ := fun σs =>
    ∏ l, gibbs_pmf N H (σs l)
  have hterm (σs : ReplicaSpace N 2) :
      HasDerivAt (fun c : ℝ => Real.exp (c * A σs) * W σs)
        (A σs * Real.exp (coupling * A σs) * W σs) coupling := by
    have hi : HasDerivAt (fun c : ℝ => c * A σs) (A σs) coupling := by
      simpa using (hasDerivAt_id coupling).mul_const (A σs)
    simpa [Function.comp_def, mul_comm, mul_left_comm] using
      ((Real.hasDerivAt_exp _).comp coupling hi).mul_const (W σs)
  have hpart : HasDerivAt
      (fun c => tiltedReplicaPartitionDet (N := N) (q := q) H c)
      (∑ σs : ReplicaSpace N 2,
        A σs * Real.exp (coupling * A σs) * W σs) coupling := by
    simpa [tiltedReplicaPartitionDet, gibbs_average_n_det, A, W, mul_assoc] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (ReplicaSpace N 2)))
        (A := fun σs => fun c : ℝ => Real.exp (c * A σs) * W σs)
        (A' := fun σs => A σs * Real.exp (coupling * A σs) * W σs)
        (x := coupling) (fun σs _ => hterm σs))
  have hlog := (Real.hasDerivAt_log
    (ne_of_gt (tiltedReplicaPartitionDet_pos (N := N) (q := q) H coupling))).comp
      coupling hpart
  simpa [Function.comp_def, tiltedCenteredOverlapSqDet,
    tiltedReplicaPartitionDet, gibbs_average_n_det, A, W, div_eq_mul_inv,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hlog

private lemma norm_tiltedLog_deriv_le
    (H : EnergySpace N) (coupling : ℝ) :
    ‖(N : ℝ) * tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling‖ ≤
      ∑ σs : ReplicaSpace N 2, (N : ℝ) * centeredOverlapSq N q σs := by
  classical
  let A : ReplicaSpace N 2 → ℝ := fun σs =>
    (N : ℝ) * centeredOverlapSq N q σs
  let P : ReplicaSpace N 2 → ℝ := fun σs =>
    Real.exp (coupling * A σs) * ∏ l, gibbs_pmf N H (σs l)
  have hA (σs : ReplicaSpace N 2) : 0 ≤ A σs :=
    mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hP (σs : ReplicaSpace N 2) : 0 ≤ P σs :=
    mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun l _ =>
      gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l))
  have hsum : 0 < ∑ σs : ReplicaSpace N 2, P σs := by
    simpa [P, A, tiltedReplicaPartitionDet, gibbs_average_n_det,
      mul_comm, mul_left_comm, mul_assoc] using
      tiltedReplicaPartitionDet_pos (N := N) (q := q) H coupling
  have hnonneg : 0 ≤ (N : ℝ) *
      tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling := by
    apply mul_nonneg (Nat.cast_nonneg N)
    unfold tiltedCenteredOverlapSqDet gibbs_average_n_det
    exact div_nonneg (Finset.sum_nonneg fun σs _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
        (Finset.prod_nonneg fun l _ =>
          gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)))
      (le_of_lt (tiltedReplicaPartitionDet_pos (N := N) (q := q) H coupling))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hratio (σs : ReplicaSpace N 2) : P σs / (∑ τ, P τ) ≤ 1 :=
    (div_le_one hsum).2
      (Finset.single_le_sum (fun τ _ => hP τ) (Finset.mem_univ σs))
  have hle : (∑ σs : ReplicaSpace N 2, A σs * (P σs / ∑ τ, P τ)) ≤
      ∑ σs : ReplicaSpace N 2, A σs := by
    apply Finset.sum_le_sum
    intro σs _
    simpa using mul_le_mul_of_nonneg_left (hratio σs) (hA σs)
  simpa [tiltedCenteredOverlapSqDet, tiltedReplicaPartitionDet,
    gibbs_average_n_det, A, P, div_eq_mul_inv, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc] using hle

/-- Coupling derivative of the logarithmic quadratic moment.

The factor `N` comes from differentiating `exp (coupling * N * Q₁₂²)`.  The quotient defining
`tiltedCenteredOverlapSq` is legitimate by `tiltedReplicaPartitionDet_pos`. -/
lemma logQuadraticMoment_hasDerivAt_coupling_formula (t coupling : ℝ) :
    HasDerivAt
      (fun c => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t c)
      ((N : ℝ) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t coupling) coupling := by
  classical
  let F : ℝ → Ω → ℝ := fun c ω => Real.log
    (tiltedReplicaPartitionDet (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω) c)
  let F' : ℝ → Ω → ℝ := fun c ω => (N : ℝ) *
    tiltedCenteredOverlapSqDet (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω) c
  let B : ℝ := ∑ σs : ReplicaSpace N 2, (N : ℝ) * centeredOverlapSq N q σs
  have hdiff (c : ℝ) (ω : Ω) : HasDerivAt (F · ω) (F' c ω) c := by
    simpa [F, F'] using tiltedLog_hasDerivAt_coupling (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω) c
  have hbound (c : ℝ) (ω : Ω) : ‖F' c ω‖ ≤ B := by
    simpa [F', B] using norm_tiltedLog_deriv_le (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω) c
  have hU_meas : Measurable sk.U := sk.hU.repr_measurable
  have hV_meas : Measurable sim.V := sim.hV.repr_measurable
  have hHt_meas : Measurable
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t) := by
    have h1 : Measurable (fun ω => (Real.sqrt t) • sk.U ω) :=
      hU_meas.const_smul (Real.sqrt t)
    have h2 : Measurable (fun ω => (Real.sqrt (1 - t)) • sim.V ω) :=
      hV_meas.const_smul (Real.sqrt (1 - t))
    have h3 : Measurable (fun _ω : Ω => H_field (N := N) (h := h)) := measurable_const
    exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t
  have hpmf_meas (σ : Config N) : Measurable fun ω =>
      gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω) σ :=
    (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σ)).continuous.measurable.comp hHt_meas
  have hpart_meas (c : ℝ) : Measurable fun ω =>
      tiltedReplicaPartitionDet (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω) c := by
    unfold tiltedReplicaPartitionDet gibbs_average_n_det
    apply Finset.measurable_sum
    intro σs _
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro l _
    exact hpmf_meas (σs l)
  have hnum_meas (c : ℝ) : Measurable fun ω =>
      gibbs_average_n_det (N := N) (n := 2)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω)
        (fun σs => centeredOverlapSq N q σs *
          Real.exp (c * (N : ℝ) * centeredOverlapSq N q σs)) := by
    unfold gibbs_average_n_det
    apply Finset.measurable_sum
    intro σs _
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro l _
    exact hpmf_meas (σs l)
  have hF_meas (c : ℝ) : AEStronglyMeasurable (F c) ℙ := by
    exact ((hpart_meas c).log).aestronglyMeasurable
  have hF'_meas (c : ℝ) : AEStronglyMeasurable (F' c) ℙ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [F', tiltedCenteredOverlapSqDet]
    exact measurable_const.mul ((hnum_meas c).div (hpart_meas c))
  have hzero (ω : Ω) : F 0 ω = 0 := by
    dsimp only [F]
    rw [show tiltedReplicaPartitionDet (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω) 0 = 1 by
      unfold tiltedReplicaPartitionDet gibbs_average_n_det
      simp only [zero_mul, Real.exp_zero, one_mul]
      exact sum_prod_gibbs_pmf_eq_one (N := N) (n := 2) _]
    exact Real.log_one
  have hF_int : Integrable (F coupling) ℙ := by
    apply Integrable.of_bound (hF_meas coupling) (B * ‖coupling‖)
    filter_upwards with ω
    have hm := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun c => F c ω) (f' := fun c => F' c ω)
      (C := B) (x := 0) (y := coupling)
      (fun c _ => (hdiff c ω).hasDerivWithinAt)
      (fun c _ => hbound c ω) (by simp) (by simp)
    simpa [hzero] using hm
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := coupling)
      (bound := fun _ => B) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hF_meas) hF_int (hF'_meas coupling)
      (ae_of_all _ fun ω c _ => hbound c ω) (integrable_const B)
      (ae_of_all _ fun ω c _ => hdiff c ω)).2
  rw [show logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t =
      fun c => ∫ ω, F c ω ∂ℙ by
        funext c
        rfl]
  rw [tiltedCenteredOverlapSq, ← integral_const_mul]
  exact hmain

/-- Coupling derivative of the normalized coupled free energy.

The physical coupling is `Λ`, while the exponential coupling is `Λ / 2`.  The chain-rule
factor `1 / 2` and the normalization `1 / (2N)` turn the preceding derivative into `1 / 4`
times the annealed tilted overlap. -/
lemma coupledFreeEnergy_hasDerivAt_coupling_formula (t Λ : ℝ) :
    HasDerivAt
      (fun L => coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t L)
      ((1 / 4) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (Λ / 2)) Λ := by
  have hlog := logQuadraticMoment_hasDerivAt_coupling_formula
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (Λ / 2)
  have hinner : HasDerivAt (fun L : ℝ => L / 2) (1 / 2) Λ := by
    simpa using (hasDerivAt_id Λ).div_const 2
  have hcomp : HasDerivAt
      (fun L => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (L / 2))
      (((N : ℝ) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (Λ / 2)) * (1 / 2)) Λ :=
    by
      change HasDerivAt
        ((fun c => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t c) ∘
          fun L : ℝ => L / 2) _ Λ
      exact hlog.comp Λ hinner
  have hscaled := hcomp.const_mul (1 / (2 * (N : ℝ)))
  have hcoeff :
      (1 / (2 * (N : ℝ))) *
          (((N : ℝ) * tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t (Λ / 2)) * (1 / 2)) =
        (1 / 4) * tiltedCenteredOverlapSq
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          t (Λ / 2) := by
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    field_simp [hN]
    ring
  rw [hcoeff] at hscaled
  simpa only [coupledFreeEnergy, coupledExcess, physicalLogQuadraticMoment] using
    hscaled.const_add
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t)

/-- Evaluation of a Hamiltonian direction on two replicas. -/
private noncomputable def pairEval_beforeIBP
    (u : EnergySpace N) : ReplicaFun N 2 :=
  fun σs => u (σs 0) + u (σs 1)

/-- Expectation under the normalized quadratically tilted two-replica law. -/
private noncomputable def tiltedReplicaAverageDet_beforeIBP
    (H : EnergySpace N) (coupling : ℝ)
    (f : ReplicaFun N 2) : ℝ :=
  gibbs_average_n_det (N := N) (n := 2) H
      (fun σs =>
        f σs *
          Real.exp
            (coupling * (N : ℝ) * centeredOverlapSq N q σs)) /
    tiltedReplicaPartitionDet (N := N) (q := q) H coupling

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma fderiv_tiltedReplicaPartitionDet_apply_beforeIBP
    (H u : EnergySpace N) (coupling : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          tiltedReplicaPartitionDet (N := N) (q := q) K coupling)
        H u =
      2 * (∑ τ : Config N, gibbs_pmf N H τ * u τ) *
          tiltedReplicaPartitionDet (N := N) (q := q) H coupling -
        gibbs_average_n_det (N := N) (n := 2) H
          (fun σs =>
            pairEval_beforeIBP (N := N) u σs *
              Real.exp
                (coupling * (N : ℝ) *
                  centeredOverlapSq N q σs)) := by
  unfold gibbs_average_n_det pairEval_beforeIBP
  unfold gibbs_pmf tiltedReplicaPartitionDet
  rw [fderiv_gibbs_average_n_det_apply]
  unfold gibbs_average_n_det gibbs_pmf
  simp +decide [
    Fin.sum_univ_two,
    mul_sub,
    sub_mul,
    mul_assoc,
    mul_comm,
    mul_left_comm,
    Finset.mul_sum _ _ _,
    Finset.sum_mul
  ]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma fderiv_coupledFreeEnergyDet_apply_beforeIBP
    (H u : EnergySpace N) (Λ : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          coupledFreeEnergyDet (N := N) (q := q) K Λ)
        H u =
      -(1 / (2 * (N : ℝ))) *
        tiltedReplicaAverageDet_beforeIBP
          (N := N) (q := q) H (Λ / 2)
          (pairEval_beforeIBP (N := N) u) := by
  erw [fderiv_add] <;>
    norm_num [fderiv_free_energy_density_apply]
  · erw [fderiv_mul, fderiv.log] <;>
      norm_num [fderiv_tiltedReplicaPartitionDet_apply_beforeIBP]
    · unfold tiltedReplicaAverageDet_beforeIBP
      ring
      rw [
        mul_inv_cancel_right₀
          (ne_of_gt
            (tiltedReplicaPartitionDet_pos
              (N := N) (q := q) H (Λ * (1 / 2))))
      ]
      ring
    · have hdiff :
          ∀ σs : ReplicaSpace N 2,
            DifferentiableAt ℝ
              (fun K : EnergySpace N =>
                Real.exp
                    (Λ / 2 * (N : ℝ) *
                      centeredOverlapSq N q σs) *
                  ∏ l,
                    Real.exp (-K.ofLp (σs l)) / Z N K)
              H := by
        intro σs
        have hpmf :
            ∀ l : Fin 2,
              DifferentiableAt ℝ
                (fun K : EnergySpace N =>
                  Real.exp (-K.ofLp (σs l)) / Z N K)
                H :=
          fun l => differentiableAt_gibbs_pmf N H (σs l)
        fun_prop
      exact DifferentiableAt.fun_sum fun i _ => hdiff i
    · exact
        ne_of_gt
          (tiltedReplicaPartitionDet_pos
            (N := N) (q := q) H (Λ / 2))
    · refine DifferentiableAt.log ?_ ?_
      · unfold tiltedReplicaPartitionDet gibbs_average_n_det
        unfold gibbs_pmf
        norm_num [
          Real.exp_ne_zero,
          Finset.prod_eq_zero_iff,
          Real.differentiableAt_exp,
          differentiableAt_pi
        ]
        have hdiff :
            ∀ x : ReplicaSpace N 2,
              DifferentiableAt ℝ
                (fun K : EnergySpace N =>
                  Real.exp (-K.ofLp (x 0)) *
                      Real.exp (-K.ofLp (x 1)) /
                    Z N K ^ 2)
                H := by
          intro x
          apply_rules [
            DifferentiableAt.div,
            DifferentiableAt.mul,
            DifferentiableAt.exp,
            differentiableAt_id,
            differentiableAt_const
          ]
          · fun_prop
          · fun_prop
          · apply_rules [
              DifferentiableAt.inv,
              DifferentiableAt.pow,
              differentiableAt_id
            ]
            · unfold Z
              fun_prop
            · exact
                ne_of_gt
                  (sq_pos_of_pos
                    (Z_pos (N := N) H))
        fun_prop
      · exact
          ne_of_gt
            (tiltedReplicaPartitionDet_pos
              (N := N) (q := q) H (Λ / 2))
  · apply_rules [
      DifferentiableAt.mul,
      DifferentiableAt.log
    ] <;> norm_num
    · unfold Z
      fun_prop
    · exact
        ne_of_gt
          (Finset.sum_pos
            (fun _ _ => Real.exp_pos _)
            Finset.univ_nonempty)
  · apply_rules [
      DifferentiableAt.mul,
      DifferentiableAt.log
    ] <;>
      norm_num [tiltedReplicaPartitionDet_pos]
    · unfold tiltedReplicaPartitionDet
      unfold gibbs_average_n_det
      norm_num [gibbs_average_n, gibbs_pmf]
      have hdiff :
          DifferentiableAt ℝ
            (fun x : EnergySpace N =>
              ∑ σ : Config N, Real.exp (-x σ))
            H := by
        fun_prop
      simp_all +decide [
        ← mul_div_assoc,
        ← Finset.sum_div _ _ _
      ]
      refine DifferentiableAt.mul ?_ ?_
      · fun_prop
      · exact
          DifferentiableAt.inv
            (hdiff.pow 2)
            (ne_of_gt
              (sq_pos_of_pos
                (Finset.sum_pos
                  (fun _ _ => Real.exp_pos _)
                  Finset.univ_nonempty)))
    · exact
        ne_of_gt
          (tiltedReplicaPartitionDet_pos
            (N := N) (q := q) H (Λ / 2))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma abs_pairEval_beforeIBP_le
    (u : EnergySpace N) (σs : ReplicaSpace N 2) :
    |pairEval_beforeIBP (N := N) u σs| ≤ 2 * ‖u‖ := by
  unfold pairEval_beforeIBP
  calc
    |u (σs 0) + u (σs 1)|
        ≤ |u (σs 0)| + |u (σs 1)| := abs_add_le _ _
    _ ≤ ‖u‖ + ‖u‖ := by
      exact add_le_add
        (abs_apply_le_norm (N := N) u (σs 0))
        (abs_apply_le_norm (N := N) u (σs 1))
    _ = 2 * ‖u‖ := by ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma abs_tiltedReplicaAverageDet_pairEval_beforeIBP_le
    (H : EnergySpace N) (coupling : ℝ) (u : EnergySpace N) :
    |tiltedReplicaAverageDet_beforeIBP
        (N := N) (q := q) H coupling
        (pairEval_beforeIBP (N := N) u)|
      ≤ 2 * ‖u‖ := by
  classical
  let W : ReplicaSpace N 2 → ℝ := fun σs =>
    Real.exp
        (coupling * (N : ℝ) *
          centeredOverlapSq N q σs) *
      ∏ l, gibbs_pmf N H (σs l)

  have hW (σs : ReplicaSpace N 2) : 0 ≤ W σs := by
    exact mul_nonneg
      (Real.exp_nonneg _)
      (Finset.prod_nonneg fun l _ =>
        gibbs_pmf_nonneg
          (N := N) (H := H) (σ := σs l))

  have hsum :
      0 < ∑ σs : ReplicaSpace N 2, W σs := by
    simpa [
      W,
      tiltedReplicaPartitionDet,
      gibbs_average_n_det,
      mul_assoc
    ] using
      tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H coupling

  have hform :
      tiltedReplicaAverageDet_beforeIBP
          (N := N) (q := q) H coupling
          (pairEval_beforeIBP (N := N) u) =
        (∑ σs : ReplicaSpace N 2,
            pairEval_beforeIBP (N := N) u σs * W σs) /
          (∑ σs : ReplicaSpace N 2, W σs) := by
    simp [
      tiltedReplicaAverageDet_beforeIBP,
      tiltedReplicaPartitionDet,
      gibbs_average_n_det,
      W,
      mul_assoc
    ]

  rw [hform, abs_div, abs_of_pos hsum]
  apply (div_le_iff₀ hsum).2
  calc
    |∑ σs : ReplicaSpace N 2,
        pairEval_beforeIBP (N := N) u σs * W σs|
        ≤
      ∑ σs : ReplicaSpace N 2,
        |pairEval_beforeIBP (N := N) u σs * W σs| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun σs : ReplicaSpace N 2 =>
                pairEval_beforeIBP (N := N) u σs * W σs))
    _ =
      ∑ σs : ReplicaSpace N 2,
        |pairEval_beforeIBP (N := N) u σs| * W σs := by
          apply Finset.sum_congr rfl
          intro σs _
          rw [abs_mul, abs_of_nonneg (hW σs)]
    _ ≤
      ∑ σs : ReplicaSpace N 2,
        (2 * ‖u‖) * W σs := by
          apply Finset.sum_le_sum
          intro σs _
          exact mul_le_mul_of_nonneg_right
            (abs_pairEval_beforeIBP_le
              (N := N) u σs)
            (hW σs)
    _ =
      (2 * ‖u‖) *
        ∑ σs : ReplicaSpace N 2, W σs := by
          rw [Finset.mul_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma opNorm_fderiv_coupledFreeEnergyDet_le_beforeIBP
    (H : EnergySpace N) (Λ : ℝ) :
    ‖fderiv ℝ
        (fun K : EnergySpace N =>
          coupledFreeEnergyDet (N := N) (q := q) K Λ)
        H‖
      ≤ 1 / (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  have hcoef :
      0 ≤ 1 / (2 * (N : ℝ)) := by
    positivity

  refine ContinuousLinearMap.opNorm_le_bound
    _
    (by positivity)
    ?_

  intro u
  rw [
    fderiv_coupledFreeEnergyDet_apply_beforeIBP
      (N := N) (q := q)
  ]

  have havg :=
    abs_tiltedReplicaAverageDet_pairEval_beforeIBP_le
      (N := N) (q := q)
      H (Λ / 2) u

  calc
    ‖-(1 / (2 * (N : ℝ))) *
        tiltedReplicaAverageDet_beforeIBP
          (N := N) (q := q) H (Λ / 2)
          (pairEval_beforeIBP (N := N) u)‖
        =
      (1 / (2 * (N : ℝ))) *
        |tiltedReplicaAverageDet_beforeIBP
          (N := N) (q := q) H (Λ / 2)
          (pairEval_beforeIBP (N := N) u)| := by
            simp [
              Real.norm_eq_abs,
              abs_mul,
              abs_of_nonneg hcoef
            ]
    _ ≤
      (1 / (2 * (N : ℝ))) * (2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left havg hcoef
    _ =
      (1 / (N : ℝ)) * ‖u‖ := by
        field_simp [ne_of_gt hNr]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma contDiff_tiltedReplicaPartitionDet_beforeIBP
    (coupling : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun H : EnergySpace N =>
        tiltedReplicaPartitionDet
          (N := N) (q := q) H coupling) := by
  unfold tiltedReplicaPartitionDet gibbs_average_n_det
  apply ContDiff.sum
  intro σs _
  apply ContDiff.mul
  · exact contDiff_const
  · have hpmf :
        ∀ l : Fin 2,
          ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun H : EnergySpace N =>
              gibbs_pmf N H (σs l)) :=
      fun l =>
        contDiff_gibbs_pmf
          (N := N) (σ := σs l)
    fun_prop

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma contDiff_coupledFreeEnergyDet_beforeIBP
    (Λ : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun H : EnergySpace N =>
        coupledFreeEnergyDet
          (N := N) (q := q) H Λ) := by
  have hpart :=
    contDiff_tiltedReplicaPartitionDet_beforeIBP
      (N := N) (q := q) (Λ / 2)

  have hlog :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun H : EnergySpace N =>
          Real.log
            (tiltedReplicaPartitionDet
              (N := N) (q := q) H (Λ / 2))) :=
    hpart.log fun H =>
      ne_of_gt
        (tiltedReplicaPartitionDet_pos
          (N := N) (q := q) H (Λ / 2))

  have hscaled :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun H : EnergySpace N =>
          (1 / (2 * (N : ℝ))) *
            Real.log
              (tiltedReplicaPartitionDet
                (N := N) (q := q) H (Λ / 2))) := by
    simpa [smul_eq_mul] using
      (ContDiff.const_smul
        (𝕜 := ℝ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (R := ℝ)
        (c := 1 / (2 * (N : ℝ))) hlog)

  simpa [coupledFreeEnergyDet] using
    (contDiff_free_energy_density (N := N)).add hscaled

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma tiltedLog_hasDerivAt_coupling_beforeIBP
    (H : EnergySpace N) (coupling : ℝ) :
    HasDerivAt
      (fun c =>
        Real.log
          (tiltedReplicaPartitionDet
            (N := N) (q := q) H c))
      ((N : ℝ) *
        tiltedCenteredOverlapSqDet
          (N := N) (q := q) H coupling)
      coupling := by
  classical
  let A : ReplicaSpace N 2 → ℝ := fun σs =>
    (N : ℝ) * centeredOverlapSq N q σs
  let W : ReplicaSpace N 2 → ℝ := fun σs =>
    ∏ l, gibbs_pmf N H (σs l)

  have hterm (σs : ReplicaSpace N 2) :
      HasDerivAt
        (fun c : ℝ =>
          Real.exp (c * A σs) * W σs)
        (A σs *
          Real.exp (coupling * A σs) *
          W σs)
        coupling := by
    have hi :
        HasDerivAt
          (fun c : ℝ => c * A σs)
          (A σs)
          coupling := by
      simpa using
        (hasDerivAt_id coupling).mul_const (A σs)
    simpa [
      Function.comp_def,
      mul_comm,
      mul_left_comm
    ] using
      ((Real.hasDerivAt_exp _).comp coupling hi).mul_const
        (W σs)

  have hpart :
      HasDerivAt
        (fun c =>
          tiltedReplicaPartitionDet
            (N := N) (q := q) H c)
        (∑ σs : ReplicaSpace N 2,
          A σs *
            Real.exp (coupling * A σs) *
            W σs)
        coupling := by
    simpa [
      tiltedReplicaPartitionDet,
      gibbs_average_n_det,
      A,
      W,
      mul_assoc
    ] using
      (HasDerivAt.fun_sum
        (u := Finset.univ)
        (A := fun σs =>
          fun c : ℝ =>
            Real.exp (c * A σs) * W σs)
        (A' := fun σs =>
          A σs *
            Real.exp (coupling * A σs) *
            W σs)
        (x := coupling)
        (fun σs _ => hterm σs))

  have hlog :=
    (Real.hasDerivAt_log
      (ne_of_gt
        (tiltedReplicaPartitionDet_pos
          (N := N) (q := q) H coupling))).comp
      coupling hpart

  simpa [
    Function.comp_def,
    tiltedCenteredOverlapSqDet,
    tiltedReplicaPartitionDet,
    gibbs_average_n_det,
    A,
    W,
    div_eq_mul_inv,
    Finset.mul_sum,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hlog

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma norm_tiltedLog_deriv_le_beforeIBP
    (H : EnergySpace N) (coupling : ℝ) :
    ‖(N : ℝ) *
        tiltedCenteredOverlapSqDet
          (N := N) (q := q) H coupling‖
      ≤
    ∑ σs : ReplicaSpace N 2,
      (N : ℝ) * centeredOverlapSq N q σs := by
  classical
  let A : ReplicaSpace N 2 → ℝ := fun σs =>
    (N : ℝ) * centeredOverlapSq N q σs
  let P : ReplicaSpace N 2 → ℝ := fun σs =>
    Real.exp (coupling * A σs) *
      ∏ l, gibbs_pmf N H (σs l)

  have hA (σs : ReplicaSpace N 2) :
      0 ≤ A σs :=
    mul_nonneg
      (Nat.cast_nonneg N)
      (sq_nonneg _)

  have hP (σs : ReplicaSpace N 2) :
      0 ≤ P σs :=
    mul_nonneg
      (Real.exp_nonneg _)
      (Finset.prod_nonneg fun l _ =>
        gibbs_pmf_nonneg
          (N := N) (H := H) (σ := σs l))

  have hsum :
      0 < ∑ σs : ReplicaSpace N 2, P σs := by
    simpa [
      P,
      A,
      tiltedReplicaPartitionDet,
      gibbs_average_n_det,
      mul_comm,
      mul_left_comm,
      mul_assoc
    ] using
      tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H coupling

  have hnonneg :
      0 ≤
        (N : ℝ) *
          tiltedCenteredOverlapSqDet
            (N := N) (q := q) H coupling := by
    apply mul_nonneg (Nat.cast_nonneg N)
    unfold tiltedCenteredOverlapSqDet gibbs_average_n_det
    exact div_nonneg
      (Finset.sum_nonneg fun σs _ =>
        mul_nonneg
          (mul_nonneg
            (sq_nonneg _)
            (Real.exp_nonneg _))
          (Finset.prod_nonneg fun l _ =>
            gibbs_pmf_nonneg
              (N := N) (H := H) (σ := σs l)))
      (le_of_lt
        (tiltedReplicaPartitionDet_pos
          (N := N) (q := q) H coupling))

  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]

  have hratio (σs : ReplicaSpace N 2) :
      P σs / (∑ τ, P τ) ≤ 1 :=
    (div_le_one hsum).2
      (Finset.single_le_sum
        (fun τ _ => hP τ)
        (Finset.mem_univ σs))

  have hle :
      (∑ σs : ReplicaSpace N 2,
        A σs * (P σs / ∑ τ, P τ))
        ≤
      ∑ σs : ReplicaSpace N 2, A σs := by
    apply Finset.sum_le_sum
    intro σs _
    simpa using
      mul_le_mul_of_nonneg_left
        (hratio σs)
        (hA σs)

  simpa [
    tiltedCenteredOverlapSqDet,
    tiltedReplicaPartitionDet,
    gibbs_average_n_det,
    A,
    P,
    div_eq_mul_inv,
    Finset.mul_sum,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hle

private lemma measurable_H_t_beforeIBP (s : ℝ) :
    Measurable
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s) := by
  have hU :=
    sk.hU.repr_measurable.const_smul
      (Real.sqrt s)
  have hV :=
    sim.hV.repr_measurable.const_smul
      (Real.sqrt (1 - s))
  exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) s

private lemma measurable_dH_t_beforeIBP (s : ℝ) :
    Measurable
      (fun w =>
        dH_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w) := by
  have hU :=
    sk.hU.repr_measurable.const_smul
      (1 / (2 * Real.sqrt s))
  have hV :=
    sim.hV.repr_measurable.const_smul
      (1 / (2 * Real.sqrt (1 - s)))
  exact measurable_dH_t_updated (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) s

private lemma integrable_freeEnergy_H_t_beforeIBP
    (s : ℝ) :
    Integrable
      (fun w =>
        free_energy_density (N := N)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) s w))
      ℙ := by
  let C : ℝ :=
    (SpinGlass.hasModerateGrowth_free_energy_density N).C
  let aU : ℝ := |Real.sqrt s|
  let aV : ℝ := |Real.sqrt (1 - s)|

  let boundFun : Ω → ℝ := fun w =>
    C *
      (1 +
        aU * ‖sk.U w‖ +
        aV * ‖sim.V w‖ +
        ‖H_field (N := N) (h := h)‖)

  have hmeas :
      AEStronglyMeasurable
        (fun w =>
          free_energy_density (N := N)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) s w))
        ℙ :=
    ((contDiff_free_energy_density (N := N)).continuous.measurable.comp
      (measurable_H_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s)).aestronglyMeasurable

  have hU_int :
      Integrable (fun w => ‖sk.U w‖) ℙ :=
    PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian
      (g := sk.U) sk.hU

  have hV_int :
      Integrable (fun w => ‖sim.V w‖) ℙ :=
    PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian
      (g := sim.V) sim.hV

  have hbound_int :
      Integrable boundFun ℙ := by
    dsimp only [boundFun]
    apply Integrable.const_mul
    exact
      ((((integrable_const (1 : ℝ)).add
          (hU_int.const_mul aU)).add
          (hV_int.const_mul aV)).add
          (integrable_const _))

  refine hbound_int.mono' hmeas ?_
  filter_upwards with w

  have hnorm :
      ‖H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w‖
        ≤
      aU * ‖sk.U w‖ +
        aV * ‖sim.V w‖ +
        ‖H_field (N := N) (h := h)‖ := by
    calc
      ‖H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w‖
          ≤
          ‖(Real.sqrt s) • sk.U w‖ +
          ‖(Real.sqrt (1 - s)) • sim.V w‖ +
          ‖H_field (N := N) (h := h)‖ := by
            simp only [H_t, H_gauss]
            exact (norm_add_le
                ((Real.sqrt s) • sk.U w +
                  (Real.sqrt (1 - s)) • sim.V w)
                (H_field (N := N) (h := h))).trans
                (by
                  gcongr
                  exact norm_add_le
                    ((Real.sqrt s) • sk.U w)
                    ((Real.sqrt (1 - s)) • sim.V w))
      _ =
        aU * ‖sk.U w‖ +
          aV * ‖sim.V w‖ +
          ‖H_field (N := N) (h := h)‖ := by
            simp [
              aU,
              aV,
              norm_smul,
              Real.norm_eq_abs
            ]

  have hgrowth :=
    (SpinGlass.hasModerateGrowth_free_energy_density N).F_bound
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s w)

  have hm :
      (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 := by
    rfl

  rw [hm, pow_one] at hgrowth
  rw [Real.norm_eq_abs]

  have hinside :
      1 +
          ‖H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) s w‖
        ≤
      1 +
        aU * ‖sk.U w‖ +
        aV * ‖sim.V w‖ +
        ‖H_field (N := N) (h := h)‖ := by
    linarith

  have hmul :=
    mul_le_mul_of_nonneg_left hinside
      (le_of_lt
        (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos)

  exact hgrowth.trans
    (by simpa only [C, boundFun] using hmul)

private lemma integrable_tiltedLog_H_t_beforeIBP
    (s coupling : ℝ) :
    Integrable
      (fun w =>
        Real.log
          (tiltedReplicaPartitionDet
            (N := N) (q := q)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) s w)
            coupling))
      ℙ := by
  let B : ℝ :=
    ∑ σs : ReplicaSpace N 2,
      (N : ℝ) * centeredOverlapSq N q σs

  have hlog_cont :
      Continuous
        (fun H : EnergySpace N =>
          Real.log
            (tiltedReplicaPartitionDet
              (N := N) (q := q) H coupling)) := by
    exact
      ((contDiff_tiltedReplicaPartitionDet_beforeIBP
          (N := N) (q := q) coupling).log
        (fun H =>
          ne_of_gt
            (tiltedReplicaPartitionDet_pos
              (N := N) (q := q) H coupling))).continuous

  have hmeas :
      AEStronglyMeasurable
        (fun w =>
          Real.log
            (tiltedReplicaPartitionDet
              (N := N) (q := q)
              (H_t
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) s w)
              coupling))
        ℙ :=
    (hlog_cont.measurable.comp
      (measurable_H_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s)).aestronglyMeasurable

  apply Integrable.of_bound hmeas (B * ‖coupling‖)
  filter_upwards with w

  let H :=
    H_t
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) s w

  have hzero :
      Real.log
          (tiltedReplicaPartitionDet
            (N := N) (q := q) H 0)
        = 0 := by
    rw [show
      tiltedReplicaPartitionDet
          (N := N) (q := q) H 0
        = 1 by
      unfold tiltedReplicaPartitionDet gibbs_average_n_det
      simp only [zero_mul, Real.exp_zero, one_mul]
      exact
        sum_prod_gibbs_pmf_eq_one
          (N := N) (n := 2) H]
    exact Real.log_one

  have hm :=
    convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun c =>
        Real.log
          (tiltedReplicaPartitionDet
            (N := N) (q := q) H c))
      (f' := fun c =>
        (N : ℝ) *
          tiltedCenteredOverlapSqDet
            (N := N) (q := q) H c)
      (C := B)
      (x := 0)
      (y := coupling)
      (fun c _ =>
        (tiltedLog_hasDerivAt_coupling_beforeIBP
          (N := N) (q := q) H c).hasDerivWithinAt)
      (fun c _ =>
        norm_tiltedLog_deriv_le_beforeIBP
          (N := N) (q := q) H c)
      (by simp)
      (by simp)

  simpa [H, hzero] using hm

private lemma coupledFreeEnergy_eq_integral_det_beforeIBP
    (s Λ : ℝ) :
    coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s Λ
      =
    ∫ w,
      coupledFreeEnergyDet
        (N := N) (q := q)
        (H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w)
        Λ
      ∂ℙ := by
  have hfree :=
    integrable_freeEnergy_H_t_beforeIBP
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) s

  have hlog :=
    integrable_tiltedLog_H_t_beforeIBP
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) s (Λ / 2)

  change
    (∫ w,
      free_energy_density (N := N)
        (H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w)
      ∂ℙ) +
      (1 / (2 * (N : ℝ))) *
        (∫ w,
          Real.log
            (tiltedReplicaPartitionDet
              (N := N) (q := q)
              (H_t
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) s w)
              (Λ / 2))
          ∂ℙ)
      =
    ∫ w,
      free_energy_density (N := N)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) s w) +
        (1 / (2 * (N : ℝ))) *
          Real.log
            (tiltedReplicaPartitionDet
              (N := N) (q := q)
              (H_t
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) s w)
              (Λ / 2))
      ∂ℙ

  rw [← integral_const_mul]
  rw [← integral_add hfree (hlog.const_mul _)]

/-- Integral representation of the coupled smart-path free energy. -/
lemma coupledFreeEnergy_eq_integral_det
    (s Λ : ℝ) :
    coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s Λ
      =
    ∫ w,
      coupledFreeEnergyDet
        (N := N) (q := q)
        (H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w)
        Λ
      ∂ℙ :=
  coupledFreeEnergy_eq_integral_det_beforeIBP
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) s Λ

private lemma integral_coupledFreeEnergyDet_hasDerivAt_beforeIBP
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s =>
        ∫ w,
          coupledFreeEnergyDet
            (N := N) (q := q)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) s w)
            Λ
          ∂ℙ)
      (∫ w,
        fderiv ℝ
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet
              (N := N) (q := q) H Λ)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
        ∂ℙ)
      t := by
  classical

  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by
    linarith

  let ε : ℝ := min t (1 - t) / 2

  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) :=
      lt_min ht0 h1t0
    dsimp only [ε]
    linarith

  have hball_Ioo :
      ∀ x ∈ Metric.ball t ε,
        x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx

    have hx' : |x - t| < ε := by
      simpa [
        Metric.mem_ball,
        Real.dist_eq,
        abs_sub_comm
      ] using hx

    have hxleft : x - t < ε :=
      (abs_sub_lt_iff.1 hx').1
    have hxright : t - x < ε :=
      (abs_sub_lt_iff.1 hx').2

    have hε_le_t : ε ≤ t / 2 := by
      have hmin : min t (1 - t) ≤ t :=
        min_le_left _ _
      dsimp only [ε]
      linarith

    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have hmin : min t (1 - t) ≤ 1 - t :=
        min_le_right _ _
      dsimp only [ε]
      linarith

    constructor
    · have hxlower : t - ε < x := by
        linarith
      have : 0 < t - ε := by
        linarith
      exact lt_trans this hxlower
    · have hxupper : x < t + ε := by
        linarith
      have : t + ε < 1 := by
        linarith
      exact lt_trans hxupper this

  let F : ℝ → Ω → ℝ := fun s w =>
    coupledFreeEnergyDet
      (N := N) (q := q)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s w)
      Λ

  let F' : ℝ → Ω → ℝ := fun s w =>
    fderiv ℝ
      (fun H : EnergySpace N =>
        coupledFreeEnergyDet
          (N := N) (q := q) H Λ)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s w)
      (dH_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s w)

  have hΦ :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun H : EnergySpace N =>
          coupledFreeEnergyDet
            (N := N) (q := q) H Λ) :=
    contDiff_coupledFreeEnergyDet_beforeIBP
      (N := N) (q := q) Λ

  have hF_meas :
      ∀ᶠ s in nhds t,
        AEStronglyMeasurable (F s) ℙ := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact
      (hΦ.continuous.measurable.comp
        (measurable_H_t_beforeIBP
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s)).aestronglyMeasurable

  have hF_int :
      Integrable (F t) ℙ := by
    have hfree :=
      integrable_freeEnergy_H_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t

    have hlog :=
      integrable_tiltedLog_H_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (Λ / 2)

    change Integrable (fun w =>
      free_energy_density (N := N)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) +
        (1 / (2 * (N : ℝ))) * Real.log
          (tiltedReplicaPartitionDet (N := N) (q := q)
            (H_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) t w) (Λ / 2))) ℙ
    exact (hfree.add (hlog.const_mul (1 / (2 * (N : ℝ))))).congr
      (ae_of_all _ fun w => by rfl)

  let Cf : ℝ := 1 / (N : ℝ)
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ :=
    1 / (2 * Real.sqrt ((1 - t) / 2))

  let bound : Ω → ℝ := fun w =>
    Cf *
      (cU * ‖sk.U w‖ +
        cV * ‖sim.V w‖)

  have hCf_nonneg : 0 ≤ Cf := by
    positivity
  have hcU_nonneg : 0 ≤ cU := by
    positivity
  have hcV_nonneg : 0 ≤ cV := by
    positivity

  have hbound_int :
      Integrable bound ℙ := by
    have hU_int :
        Integrable (fun w => ‖sk.U w‖) ℙ :=
      PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian
        (g := sk.U) sk.hU

    have hV_int :
        Integrable (fun w => ‖sim.V w‖) ℙ :=
      PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian
        (g := sim.V) sim.hV

    have h1 :
        Integrable
          (fun w => cU * ‖sk.U w‖)
          ℙ :=
      hU_int.const_mul cU

    have h2 :
        Integrable
          (fun w => cV * ‖sim.V w‖)
          ℙ :=
      hV_int.const_mul cV

    have hsum :
        Integrable
          (fun w =>
            cU * ‖sk.U w‖ +
              cV * ‖sim.V w‖)
          ℙ :=
      h1.add h2

    simpa [bound, Cf, mul_add, mul_assoc] using
      hsum.const_mul Cf

  have hF'_meas :
      AEStronglyMeasurable (F' t) ℙ := by
    have hHt_meas :=
      measurable_H_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t

    have hdHt_meas :=
      measurable_dH_t_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t

    have hfderiv_cont :
        Continuous
          (fun p : EnergySpace N × EnergySpace N =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                coupledFreeEnergyDet
                  (N := N) (q := q) H Λ)
              p.1 p.2) := by
      have hcont :
          Continuous
            (fun H : EnergySpace N =>
              fderiv ℝ
                (fun K : EnergySpace N =>
                  coupledFreeEnergyDet
                    (N := N) (q := q) K Λ)
                H) :=
        hΦ.continuous_fderiv (by simp)

      exact
        ((hcont.comp continuous_fst).clm_apply continuous_snd)

    have hpair :
        Measurable
          (fun w =>
            (H_t
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) t w,
              dH_t
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) t w)) :=
      hHt_meas.prodMk hdHt_meas

    exact
      (hfderiv_cont.measurable.comp hpair).aestronglyMeasurable

  have h_bound :
      ∀ᵐ w ∂ℙ,
        ∀ x ∈ Metric.ball t ε,
          ‖F' x w‖ ≤ bound w := by
    refine ae_of_all _ ?_
    intro w x hx

    have hxIoo :
        x ∈ Set.Ioo (0 : ℝ) 1 :=
      hball_Ioo x hx

    have hCoeffU :
        |1 / (2 * Real.sqrt x)| ≤ cU := by
      have hx_lower : t / 2 ≤ x := by
        have hx' : |x - t| < ε := by
          simpa [
            Metric.mem_ball,
            Real.dist_eq,
            abs_sub_comm
          ] using hx
        have hxright : t - x < ε :=
          (abs_sub_lt_iff.1 hx').2

        have hε_le_t : ε ≤ t / 2 := by
          have hmin : min t (1 - t) ≤ t :=
            min_le_left _ _
          dsimp only [ε]
          linarith

        linarith

      have hsqrt_le :
          Real.sqrt (t / 2) ≤ Real.sqrt x :=
        Real.sqrt_le_sqrt hx_lower

      have hpos :
          0 < 2 * Real.sqrt (t / 2) := by
        have : 0 < Real.sqrt (t / 2) :=
          Real.sqrt_pos.2 (by linarith)
        linarith

      have hle :
          2 * Real.sqrt (t / 2) ≤
            2 * Real.sqrt x := by
        linarith

      have hdiv :
          1 / (2 * Real.sqrt x) ≤
            1 / (2 * Real.sqrt (t / 2)) := by
        simpa [one_div] using
          one_div_le_one_div_of_le hpos hle

      have hnonneg :
          0 ≤ 1 / (2 * Real.sqrt x) := by
        positivity

      simpa [
        cU,
        abs_of_nonneg hnonneg,
        abs_of_nonneg (Real.sqrt_nonneg x)
      ] using hdiv

    have hCoeffV :
        |1 / (2 * Real.sqrt (1 - x))| ≤ cV := by
      have h1x_lower :
          (1 - t) / 2 ≤ 1 - x := by
        have hx' : |x - t| < ε := by
          simpa [
            Metric.mem_ball,
            Real.dist_eq,
            abs_sub_comm
          ] using hx

        have hxleft : x - t < ε :=
          (abs_sub_lt_iff.1 hx').1

        have hε_le_1t :
            ε ≤ (1 - t) / 2 := by
          have hmin :
              min t (1 - t) ≤ 1 - t :=
            min_le_right _ _
          dsimp only [ε]
          linarith

        linarith

      have hsqrt_le :
          Real.sqrt ((1 - t) / 2) ≤
            Real.sqrt (1 - x) :=
        Real.sqrt_le_sqrt h1x_lower

      have hpos :
          0 <
            2 * Real.sqrt ((1 - t) / 2) := by
        have :
            0 <
              Real.sqrt ((1 - t) / 2) :=
          Real.sqrt_pos.2 (by linarith)
        linarith

      have hle :
          2 * Real.sqrt ((1 - t) / 2) ≤
            2 * Real.sqrt (1 - x) := by
        linarith

      have hdiv :
          1 / (2 * Real.sqrt (1 - x)) ≤
            1 /
              (2 * Real.sqrt ((1 - t) / 2)) := by
        simpa [one_div] using
          one_div_le_one_div_of_le hpos hle

      have hnonneg :
          0 ≤
            1 / (2 * Real.sqrt (1 - x)) := by
        positivity

      simpa [
        cV,
        abs_of_nonneg hnonneg,
        abs_of_nonneg (Real.sqrt_nonneg (1 - x))
      ] using hdiv

    have hdH_norm :
        ‖dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w‖
          ≤
        cU * ‖sk.U w‖ +
          cV * ‖sim.V w‖ := by
      have htri :
          ‖dH_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w‖
            ≤
          |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| *
              ‖sim.V w‖ := by
        simpa [
          dH_t,
          sub_eq_add_neg,
          norm_smul,
          abs_mul
        ] using
          (norm_add_le
            ((1 / (2 * Real.sqrt x)) • sk.U w)
            (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))

      exact htri.trans
        (by
          gcongr)

    have hop :
        ‖fderiv ℝ
            (fun H : EnergySpace N =>
              coupledFreeEnergyDet
                (N := N) (q := q) H Λ)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w)‖
          ≤ Cf := by
      simpa [Cf] using
        opNorm_fderiv_coupledFreeEnergyDet_le_beforeIBP
          (N := N) (q := q)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w)
          Λ

    have happ :
        ‖F' x w‖
          ≤
        Cf *
          ‖dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w‖ := by
      have hle :=
        ContinuousLinearMap.le_opNorm
          (fderiv ℝ
            (fun H : EnergySpace N =>
              coupledFreeEnergyDet
                (N := N) (q := q) H Λ)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w))
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w)

      have hmul :=
        mul_le_mul_of_nonneg_right hop
          (norm_nonneg
            (dH_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w))

      simpa [F'] using hle.trans hmul

    have :
        ‖F' x w‖
          ≤
        Cf *
          (cU * ‖sk.U w‖ +
            cV * ‖sim.V w‖) :=
      happ.trans
        (mul_le_mul_of_nonneg_left
          hdH_norm hCf_nonneg)

    simpa [bound] using this

  have h_diff :
      ∀ᵐ w ∂ℙ,
        ∀ x ∈ Metric.ball t ε,
          HasDerivAt
            (fun s => F s w)
            (F' x w)
            x := by
    refine ae_of_all _ ?_
    intro w x hx

    have hxIoo :
        x ∈ Set.Ioo (0 : ℝ) 1 :=
      hball_Ioo x hx

    have hHt_diff :
        HasDerivAt
          (fun s =>
            H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) s w)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w)
          x :=
      hasDerivAt_H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) x hxIoo w

    have houter :
        HasFDerivAt
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet
              (N := N) (q := q) H Λ)
          (fderiv ℝ
            (fun H : EnergySpace N =>
              coupledFreeEnergyDet
                (N := N) (q := q) H Λ)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w))
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) x w) :=
      (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt

    change HasDerivAt
      ((fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ) ∘
        fun s => H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w)
      (F' x w) x
    simpa [F'] using houter.comp_hasDerivAt x hHt_diff

  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω))
      (F := F)
      (F' := F')
      (x₀ := t)
      (bound := bound)
      (s := Metric.ball t ε)
      (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas
      hF_int
      hF'_meas
      h_bound
      hbound_int
      h_diff).2

  simpa [F] using hmain

/-- Differentiate the coupled smart path before Gaussian integration by parts.

This isolates differentiation under the disorder integral from the covariance calculation.
The intended proof repeats `pressure_derivative_before_ibp` with
`coupledFreeEnergyDet (N := N) (q := q) · Λ`; positivity of
`tiltedReplicaPartitionDet` handles the logarithm. -/
lemma coupledFreeEnergy_hasDerivAt_time_before_ibp
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s Λ)
      (∫ ω,
        fderiv ℝ (fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        ∂ℙ) t := by
  have hraw :=
    integral_coupledFreeEnergyDet_hasDerivAt_beforeIBP
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) (Λ := Λ) ht

  have hfun :
      (fun s =>
        coupledFreeEnergy
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s Λ)
        =
      (fun s =>
        ∫ w,
          coupledFreeEnergyDet
            (N := N) (q := q)
            (H_t
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) s w)
            Λ
          ∂ℙ) := by
    funext s
    exact
      coupledFreeEnergy_eq_integral_det_beforeIBP
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s Λ

  rw [hfun]
  exact hraw

/-- Evaluation of a Hamiltonian direction on the two replicas. -/
noncomputable def pairEval
    (u : EnergySpace N) : ReplicaFun N 2 :=
  fun σs => u (σs 0) + u (σs 1)

/-- Expectation under the normalized quadratically tilted two-replica Gibbs law. -/
noncomputable def tiltedReplicaAverageDet
    (H : EnergySpace N) (coupling : ℝ)
    (f : ReplicaFun N 2) : ℝ :=
  gibbs_average_n_det (N := N) (n := 2) H
      (fun σs =>
        f σs *
          Real.exp
            (coupling * (N : ℝ) * centeredOverlapSq N q σs)) /
    tiltedReplicaPartitionDet (N := N) (q := q) H coupling

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma tiltedReplicaAverageDet_one
    (H : EnergySpace N) (coupling : ℝ) :
    tiltedReplicaAverageDet
        (N := N) (q := q) H coupling (fun _ => 1) = 1 := by
  unfold tiltedReplicaAverageDet tiltedReplicaPartitionDet
  simp only [one_mul]
  exact div_self
    (ne_of_gt
      (tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H coupling))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma tiltedReplicaAverageDet_centeredOverlapSq
    (H : EnergySpace N) (coupling : ℝ) :
    tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (centeredOverlapSq N q) =
      tiltedCenteredOverlapSqDet
        (N := N) (q := q) H coupling := by
  rfl

/-- Explicit Hessian of the normalized coupled two-replica free energy.

The formula is the covariance of `pairEval u` and `pairEval v` under the tilted law,
with normalization `1 / (2N)`.
-/
noncomputable def coupledHessianDet
    (H : EnergySpace N) (coupling : ℝ)
    (u v : EnergySpace N) : ℝ :=
  (1 / (2 * (N : ℝ))) *
    (tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (fun σs =>
          pairEval (N := N) u σs * pairEval (N := N) v σs) -
      tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (pairEval (N := N) u) *
      tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (pairEval (N := N) v))

/-! ## Calculus layer

These are the first lemmas to prove. They use finite sums, the quotient rule,
`fderiv_gibbs_average_n_det_apply`, and positivity of
`tiltedReplicaPartitionDet`.
-/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fderiv_tiltedReplicaPartitionDet_apply_workspace
    (H u : EnergySpace N) (coupling : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          tiltedReplicaPartitionDet (N := N) (q := q) K coupling)
        H u =
      2 * (∑ τ : Config N, gibbs_pmf N H τ * u τ) *
          tiltedReplicaPartitionDet (N := N) (q := q) H coupling -
        gibbs_average_n_det (N := N) (n := 2) H
          (fun σs =>
            pairEval (N := N) u σs *
              Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs)) := by
  unfold gibbs_average_n_det pairEval;
  unfold gibbs_pmf tiltedReplicaPartitionDet;
  rw [ fderiv_gibbs_average_n_det_apply ];
  unfold gibbs_average_n_det gibbs_pmf;
  simp +decide [ Fin.sum_univ_two, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-
First Hamiltonian derivative of the deterministic coupled free energy.
-/
lemma fderiv_coupledFreeEnergyDet_apply_workspace
    (H u : EnergySpace N) (Λ : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          coupledFreeEnergyDet (N := N) (q := q) K Λ)
        H u =
      -(1 / (2 * (N : ℝ))) *
        tiltedReplicaAverageDet
          (N := N) (q := q) H (Λ / 2)
          (pairEval (N := N) u) := by
  /-
  Suggested proof:

  * unfold `coupledFreeEnergyDet`;
  * differentiate `free_energy_density` using
    `fderiv_free_energy_density_apply`;
  * differentiate the logarithm of the tilted partition function;
  * use `fderiv_gibbs_average_n_det_apply` for its Hamiltonian derivative;
  * collect the two ordinary Gibbs-average terms, which cancel;
  * divide by the positive tilted partition function.
  -/
  erw [ fderiv_add ] <;> norm_num [ fderiv_free_energy_density_apply ];
  · erw [ fderiv_mul, fderiv.log ] <;> norm_num [ fderiv_tiltedReplicaPartitionDet_apply_workspace ];
    · unfold tiltedReplicaAverageDet; ring;
      rw [ mul_inv_cancel_right₀ ( ne_of_gt ( tiltedReplicaPartitionDet_pos _ _ _ _ ) ) ] ; ring;
    · -- The sum of differentiable functions is differentiable.
      have h_diff : ∀ σs : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (Λ / 2 * N * centeredOverlapSq N q σs) * ∏ l, Real.exp (-K.ofLp (σs l)) / Z N K) H := by
        intro σs;
        have h_diff : ∀ l : Fin 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (σs l)) / Z N K) H := by
          exact fun l => differentiableAt_gibbs_pmf N H (σs l)
        fun_prop
      exact DifferentiableAt.fun_sum fun i _ => h_diff i
    · exact ne_of_gt (tiltedReplicaPartitionDet_pos N q H (Λ / 2));
    · refine' DifferentiableAt.log _ _;
      · unfold tiltedReplicaPartitionDet gibbs_average_n_det;
        unfold gibbs_pmf; norm_num [ Real.exp_ne_zero, Finset.prod_eq_zero_iff, Real.differentiableAt_exp, differentiableAt_pi ] ;
        have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
          intro x;
          apply_rules [ DifferentiableAt.div, DifferentiableAt.mul, DifferentiableAt.exp, differentiableAt_id, differentiableAt_const ];
          · fun_prop;
          · fun_prop;
          · apply_rules [ DifferentiableAt.inv, DifferentiableAt.pow, differentiableAt_id ];
            · unfold Z;
              fun_prop;
            · exact ne_of_gt ( sq_pos_of_pos ( Z_pos N H ) );
        fun_prop;
      · exact ne_of_gt ( tiltedReplicaPartitionDet_pos N q H ( Λ / 2 ) );
  · apply_rules [ DifferentiableAt.mul, DifferentiableAt.log ] <;> norm_num;
    · unfold Z ;
      fun_prop;
    · exact ne_of_gt ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty );
  · apply_rules [ DifferentiableAt.mul, DifferentiableAt.log ] <;> norm_num [ tiltedReplicaPartitionDet_pos ];
    · unfold tiltedReplicaPartitionDet;
      unfold gibbs_average_n_det; norm_num [ gibbs_average_n, gibbs_pmf ] ;
      have h_diff : DifferentiableAt ℝ (fun x : EnergySpace N => (∑ σ : Config N, Real.exp (-x σ))) H := by
        fun_prop;
      simp_all +decide [ ← mul_div_assoc, ← Finset.sum_div _ _ _ ];
      refine' DifferentiableAt.mul _ _;
      · fun_prop;
      · exact DifferentiableAt.inv ( h_diff.pow 2 ) ( ne_of_gt ( sq_pos_of_pos ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ( Finset.univ_nonempty ) ) ) );
    · exact ne_of_gt (tiltedReplicaPartitionDet_pos N q H (Λ / 2))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma differentiableAt_tiltedReplicaAverageDet_workspace
    (H : EnergySpace N) (coupling : ℝ) (f : ReplicaFun N 2) :
    DifferentiableAt ℝ
      (fun K : EnergySpace N =>
        tiltedReplicaAverageDet (N := N) (q := q) K coupling f) H := by
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun K => (∑ σs : ReplicaSpace N 2, (∏ l : Fin 2, gibbs_pmf N K (σs l)) * f σs * Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs)) / (∑ σs : ReplicaSpace N 2, (∏ l : Fin 2, gibbs_pmf N K (σs l)) * Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs));
  · refine' DifferentiableAt.mul _ _;
    · have h_diff : ∀ σs : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => ∏ l : Fin 2, gibbs_pmf N K (σs l)) H := by
        exact fun σs => differentiableAt_prod_gibbs_pmf N 2 H σs;
      fun_prop;
    · refine' DifferentiableAt.inv _ _;
      · have h_diff : ∀ σ : Config N, DifferentiableAt ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) H := by
          exact fun σ => differentiableAt_gibbs_pmf N H σ;
        fun_prop (disch := norm_num);
      · refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ ( fun _ => fun _ => Bool.true ) ) ) );
        · exact mul_pos ( Finset.prod_pos fun _ _ => gibbs_pmf_pos _ _ _ ) ( Real.exp_pos _ );
        · exact mul_nonneg ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ( Real.exp_nonneg _ );
  · filter_upwards [ ] with K ; unfold tiltedReplicaAverageDet gibbs_average_n_det tiltedReplicaPartitionDet ; simp +decide [ Finset.prod_mul_distrib, mul_assoc ] ;
    unfold gibbs_average_n_det; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fderiv_tiltedReplicaAverageDet_apply_workspace
    (H u v : EnergySpace N) (coupling : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          tiltedReplicaAverageDet (N := N) (q := q) K coupling
            (pairEval (N := N) u))
        H v =
      - (tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (fun σs => pairEval (N := N) u σs * pairEval (N := N) v σs) -
          tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (pairEval (N := N) u) *
          tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (pairEval (N := N) v)) := by
  unfold tiltedReplicaAverageDet;
  erw [ fderiv_mul ];
  · erw [ fderiv_fun_comp (𝕜 := ℝ) (x := H)
      (f := fun K : EnergySpace N => tiltedReplicaPartitionDet N q K coupling)
      (g := fun x : ℝ => x⁻¹)
      (differentiableAt_inv
        (ne_of_gt (tiltedReplicaPartitionDet_pos (N := N) (q := q) H coupling)))
      (by
        apply_rules [ ContDiff.differentiable ];
        apply_rules [ ContDiff.sum, ContDiff.mul, ContDiff.exp, contDiff_const, contDiff_id ];
        any_goals exact ⊤;
        · intro i hi; apply_rules [ ContDiff.mul, ContDiff.exp, contDiff_const, contDiff_id ] ;
          · fun_prop;
          · refine' ContDiff.inv _ _;
            · refine' ContDiff.sum fun σ _ => ContDiff.exp _;
              fun_prop;
            · exact fun x => ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty;
          · fun_prop;
          · refine' ContDiff.inv _ _;
            · refine' ContDiff.sum fun σ _ => ContDiff.exp _;
              fun_prop;
            · exact fun x => ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty;
        · norm_num) ];
    simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, fderiv_tiltedReplicaPartitionDet_apply_workspace, fderiv_gibbs_average_n_det_apply ];
    unfold gibbs_average_n_det; ring;
    unfold pairEval; simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
    by_cases h : tiltedReplicaPartitionDet N q H coupling = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
    simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
  · unfold gibbs_average_n_det;
    simp +decide [ gibbs_pmf ];
    have h_diff : DifferentiableAt ℝ (fun K : EnergySpace N => Z N K) H := by
      unfold Z ;
      fun_prop (disch := norm_num);
    have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
      intro x;
      refine' DifferentiableAt.mul _ _;
      · fun_prop;
      · exact DifferentiableAt.inv ( h_diff.pow 2 ) ( by exact ne_of_gt ( sq_pos_of_pos ( Z_pos ( N := N ) H ) ) );
    fun_prop;
  · apply DifferentiableAt.inv;
    · unfold tiltedReplicaPartitionDet;
      unfold gibbs_average_n_det;
      unfold gibbs_pmf; norm_num [ Finset.prod_mul_distrib, Real.exp_ne_zero ] ;
      have h_diff : DifferentiableAt ℝ (fun K : EnergySpace N => Z N K) H := by
        unfold Z
        fun_prop
      have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
        intro x
        refine' DifferentiableAt.mul _ _
        · fun_prop
        · exact DifferentiableAt.inv (h_diff.pow 2)
            (by exact ne_of_gt (sq_pos_of_pos (Z_pos (N := N) H)))
      fun_prop;
    · refine' ne_of_gt ( _ );
      exact tiltedReplicaPartitionDet_pos _ _ _ _

/-
Second Hamiltonian derivative of the deterministic coupled free energy.
-/
lemma fderiv_coupledFirstVariation_apply_workspace
    (H u v : EnergySpace N) (Λ : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          fderiv ℝ
            (fun L : EnergySpace N =>
              coupledFreeEnergyDet (N := N) (q := q) L Λ)
            K u)
        H v =
      coupledHessianDet
        (N := N) (q := q) H (Λ / 2) u v := by
  /-
  Rewrite the inner derivative with
  `fderiv_coupledFreeEnergyDet_apply_workspace` and differentiate the
  normalized tilted expectation. The quotient rule gives exactly the
  tilted covariance in `coupledHessianDet`.
  -/
  have h_deriv : (fderiv ℝ (fun K => (fderiv ℝ (fun L => coupledFreeEnergyDet N q L Λ) K) u) H) v = -(1 / (2 * (N : ℝ))) * (fderiv ℝ (fun K => tiltedReplicaAverageDet N q K (Λ / 2) (pairEval N u)) H) v := by
    rw [ show ( fun K => ( fderiv ℝ ( fun L => coupledFreeEnergyDet N q L Λ ) K ) u ) = fun K => - ( 1 / ( 2 * N ) ) * tiltedReplicaAverageDet N q K ( Λ / 2 ) ( pairEval N u ) from funext fun K => fderiv_coupledFreeEnergyDet_apply_workspace N q K u Λ ];
    rw [ fderiv_const_mul ] ; norm_num [ differentiableAt_tiltedReplicaAverageDet_workspace ];
    exact differentiableAt_tiltedReplicaAverageDet_workspace N q H (Λ / 2) (pairEval N u)
  rw [ h_deriv, fderiv_tiltedReplicaAverageDet_apply_workspace ] ; unfold coupledHessianDet ; ring

/-! ## Gaussian-IBP trace layer -/

private noncomputable def coupledIBPJointCLM (a b : ℝ) :
    WithLp 2 (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => a • (WithLp.ofLp p).1 + b • (WithLp.ofLp p).2
      map_add' := by intro x y; simp; abel
      map_smul' := by intro c x; simp [smul_add, smul_smul, mul_comm] }

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma abs_tiltedReplicaAverageDet_workspace_le
    (H : EnergySpace N) (coupling M : ℝ) (f : ReplicaFun N 2)
    (hM : 0 ≤ M) (hf : ∀ σs, |f σs| ≤ M) :
    |tiltedReplicaAverageDet (N := N) (q := q) H coupling f| ≤ M := by
  classical
  let W : ReplicaSpace N 2 → ℝ := fun σs =>
    Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs) *
      ∏ l, gibbs_pmf N H (σs l)
  have hW (σs : ReplicaSpace N 2) : 0 ≤ W σs := by
    exact mul_nonneg (Real.exp_nonneg _)
      (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg N H (σs l))
  have hsum : 0 < ∑ σs : ReplicaSpace N 2, W σs := by
    simpa [W, tiltedReplicaPartitionDet, gibbs_average_n_det, mul_assoc] using
      tiltedReplicaPartitionDet_pos (N := N) (q := q) H coupling
  have hform :
      tiltedReplicaAverageDet (N := N) (q := q) H coupling f =
        (∑ σs : ReplicaSpace N 2, f σs * W σs) / ∑ σs, W σs := by
    simp [tiltedReplicaAverageDet, tiltedReplicaPartitionDet,
      gibbs_average_n_det, W, mul_assoc]
  rw [hform, abs_div, abs_of_pos hsum]
  apply (div_le_iff₀ hsum).2
  calc
    |∑ σs : ReplicaSpace N 2, f σs * W σs| ≤
        ∑ σs : ReplicaSpace N 2, |f σs * W σs| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σs : ReplicaSpace N 2, |f σs| * W σs := by
      apply Finset.sum_congr rfl
      intro σs _
      rw [abs_mul, abs_of_nonneg (hW σs)]
    _ ≤ ∑ σs : ReplicaSpace N 2, M * W σs := by
      exact Finset.sum_le_sum fun σs _ => mul_le_mul_of_nonneg_right (hf σs) (hW σs)
    _ = M * ∑ σs : ReplicaSpace N 2, W σs := by rw [Finset.mul_sum]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma abs_coupledHessianDet_workspace_le
    (H : EnergySpace N) (coupling : ℝ) (u v : EnergySpace N) :
    |coupledHessianDet (N := N) (q := q) H coupling u v| ≤
      (4 / (N : ℝ)) * ‖u‖ * ‖v‖ := by
  have hu (σs : ReplicaSpace N 2) : |pairEval (N := N) u σs| ≤ 2 * ‖u‖ := by
    unfold pairEval
    calc
      |u (σs 0) + u (σs 1)| ≤ |u (σs 0)| + |u (σs 1)| := abs_add_le _ _
      _ ≤ ‖u‖ + ‖u‖ := add_le_add (abs_apply_le_norm N u _) (abs_apply_le_norm N u _)
      _ = 2 * ‖u‖ := by ring
  have hv (σs : ReplicaSpace N 2) : |pairEval (N := N) v σs| ≤ 2 * ‖v‖ := by
    unfold pairEval
    calc
      |v (σs 0) + v (σs 1)| ≤ |v (σs 0)| + |v (σs 1)| := abs_add_le _ _
      _ ≤ ‖v‖ + ‖v‖ := add_le_add (abs_apply_le_norm N v _) (abs_apply_le_norm N v _)
      _ = 2 * ‖v‖ := by ring
  have huv (σs : ReplicaSpace N 2) :
      |pairEval (N := N) u σs * pairEval (N := N) v σs| ≤ 4 * ‖u‖ * ‖v‖ := by
    rw [abs_mul]
    nlinarith [hu σs, hv σs, abs_nonneg (pairEval N u σs),
      abs_nonneg (pairEval N v σs), norm_nonneg u, norm_nonneg v]
  have hxy := abs_tiltedReplicaAverageDet_workspace_le
    (N := N) (q := q) H coupling (4 * ‖u‖ * ‖v‖)
    (fun σs => pairEval N u σs * pairEval N v σs) (by positivity) huv
  have hx := abs_tiltedReplicaAverageDet_workspace_le
    (N := N) (q := q) H coupling (2 * ‖u‖) (pairEval N u) (by positivity) hu
  have hy := abs_tiltedReplicaAverageDet_workspace_le
    (N := N) (q := q) H coupling (2 * ‖v‖) (pairEval N v) (by positivity) hv
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold coupledHessianDet
  rw [abs_mul]
  have hc : |1 / (2 * (N : ℝ))| = 1 / (2 * (N : ℝ)) := abs_of_pos (by positivity)
  rw [hc]
  calc
    1 / (2 * (N : ℝ)) *
        |tiltedReplicaAverageDet N q H coupling
            (fun σs => pairEval N u σs * pairEval N v σs) -
          tiltedReplicaAverageDet N q H coupling (pairEval N u) *
            tiltedReplicaAverageDet N q H coupling (pairEval N v)|
      ≤ 1 / (2 * (N : ℝ)) *
          (|tiltedReplicaAverageDet N q H coupling
              (fun σs => pairEval N u σs * pairEval N v σs)| +
            |tiltedReplicaAverageDet N q H coupling (pairEval N u)| *
              |tiltedReplicaAverageDet N q H coupling (pairEval N v)|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          |tiltedReplicaAverageDet N q H coupling
                (fun σs => pairEval N u σs * pairEval N v σs) -
              tiltedReplicaAverageDet N q H coupling (pairEval N u) *
                tiltedReplicaAverageDet N q H coupling (pairEval N v)|
              ≤ |tiltedReplicaAverageDet N q H coupling
                  (fun σs => pairEval N u σs * pairEval N v σs)| +
                |tiltedReplicaAverageDet N q H coupling (pairEval N u) *
                  tiltedReplicaAverageDet N q H coupling (pairEval N v)| := abs_sub _ _
          _ = _ := by rw [abs_mul]
    _ ≤ 1 / (2 * (N : ℝ)) *
          (4 * ‖u‖ * ‖v‖ + (2 * ‖u‖) * (2 * ‖v‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hxy
          (mul_le_mul hx hy (abs_nonneg _) (by positivity))
    _ = (4 / (N : ℝ)) * ‖u‖ * ‖v‖ := by field_simp; ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma fderiv_coupledFirstVariation_affine_workspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N) (field u : EnergySpace N)
    (x y : E) (Λ : ℝ) :
    fderiv ℝ
        (fun z : E => fderiv ℝ
          (fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (A z + field) u) x y =
      coupledHessianDet (N := N) (q := q) (A x + field) (Λ / 2) u (A y) := by
  have hΦ := contDiff_coupledFreeEnergyDet_beforeIBP (N := N) (q := q) Λ
  have hgrad : ContDiff ℝ 1
      (fderiv ℝ (fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ)) :=
    hΦ.fderiv_right (m := (1 : WithTop ℕ∞)) (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hscalar : ContDiff ℝ 1
      (fun H : EnergySpace N =>
        fderiv ℝ
          (fun K : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) K Λ) H u) :=
    hgrad.clm_apply contDiff_const
  have hc := (hscalar.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp
    x (A.hasFDerivAt.add_const field)
  change (fderiv ℝ
    ((fun H : EnergySpace N =>
      fderiv ℝ (fun K : EnergySpace N => coupledFreeEnergyDet N q K Λ) H u) ∘
      fun z => A z + field) x) y = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact fderiv_coupledFirstVariation_apply_workspace
    (N := N) (q := q) (A x + field) u (A y) Λ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private noncomputable def coupledFirstVariationModerateGrowth_workspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N) (field u : EnergySpace N) (Λ : ℝ) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun x : E => fderiv ℝ
        (fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ)
        (A x + field) u) := by
  let C := 1 + (1 / (N : ℝ)) * ‖u‖ + (4 / (N : ℝ)) * ‖A‖ * ‖u‖
  refine ⟨C, 0, ?_, ?_, ?_⟩
  · dsimp [C]; positivity
  · intro x
    have hop := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ)
        (A x + field)) u
    have hb := opNorm_fderiv_coupledFreeEnergyDet_le_beforeIBP
      (N := N) (q := q) (A x + field) Λ
    rw [Real.norm_eq_abs] at hop
    calc
      |(fderiv ℝ (fun H => coupledFreeEnergyDet N q H Λ) (A x + field)) u|
          ≤ (1 / (N : ℝ)) * ‖u‖ :=
        hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))
      _ ≤ C := by
        dsimp [C]
        have hn : 0 ≤ (4 / (N : ℝ)) * ‖A‖ * ‖u‖ := by positivity
        linarith
      _ = C * (1 + ‖x‖) ^ 0 := by simp
  · intro x
    simp only [pow_zero, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by dsimp [C]; positivity) ?_
    intro y
    rw [fderiv_coupledFirstVariation_affine_workspace (N := N) (q := q)]
    have hb := abs_coupledHessianDet_workspace_le
      (N := N) (q := q) (A x + field) (Λ / 2) u (A y)
    rw [Real.norm_eq_abs]
    calc
      |coupledHessianDet N q (A x + field) (Λ / 2) u (A y)|
          ≤ (4 / (N : ℝ)) * ‖u‖ * ‖A y‖ := hb
      _ ≤ C * ‖y‖ := by
        have hAy := A.le_opNorm y
        have hfac : 0 ≤ 4 / (N : ℝ) * ‖u‖ := by positivity
        have hmul := mul_le_mul_of_nonneg_left hAy hfac
        calc
          (4 / (N : ℝ)) * ‖u‖ * ‖A y‖
              ≤ (4 / (N : ℝ)) * ‖u‖ * (‖A‖ * ‖y‖) := hmul
          _ = ((4 / (N : ℝ)) * ‖A‖ * ‖u‖) * ‖y‖ := by ring
          _ ≤ C * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
            dsimp [C]
            have h₁ : 0 ≤ (1 / (N : ℝ)) * ‖u‖ := by positivity
            linarith

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma coupledHessian_eq_secondFDeriv_workspace
    (H u v : EnergySpace N) (Λ : ℝ) :
    coupledHessianDet (N := N) (q := q) H (Λ / 2) u v =
      (fderiv ℝ
        (fderiv ℝ
          (fun K : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) K Λ)) H v) u := by
  have hΦ := contDiff_coupledFreeEnergyDet_beforeIBP (N := N) (q := q) Λ
  have hgrad : Differentiable ℝ
      (fderiv ℝ (fun K : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) K Λ)) :=
    (hΦ.fderiv_right (m := (1 : WithTop ℕ∞)) (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).differentiable (by norm_num)
  have hc := hgrad.differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_const (x := H) (c := u))
  have happ := congrArg (fun L : EnergySpace N →L[ℝ] ℝ => L v) hc.fderiv
  have hcoupled := fderiv_coupledFirstVariation_apply_workspace
    (N := N) (q := q) H u v Λ
  simpa [ContinuousLinearMap.comp_apply] using hcoupled.symm.trans happ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
private lemma coupledGaussianTrace_eq_stdBasis_workspace
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (volume : Measure Ω')]
    (g : Ω' → EnergySpace N)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (H : EnergySpace N) (Λ : ℝ) :
    (∑ i : hg.ι, (hg.τ i : ℝ) *
      coupledHessianDet (N := N) (q := q) H (Λ / 2) (hg.w i) (hg.w i)) =
      ∑ σ : Config N, ∑ τ : Config N,
        inner ℝ ((PhysLean.Probability.GaussianIBP.covOp (g := g) hg)
          (std_basis N σ)) (std_basis N τ) *
        coupledHessianDet (N := N) (q := q) H (Λ / 2)
          (std_basis N σ) (std_basis N τ) := by
  classical
  let D := fderiv ℝ
    (fderiv ℝ (fun K : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) K Λ)) H
  have hB (u v : EnergySpace N) :
      coupledHessianDet N q H (Λ / 2) u v = (D v) u := by
    exact coupledHessian_eq_secondFDeriv_workspace (N := N) (q := q) H u v Λ
  have hrepr (v : EnergySpace N) :
      v = ∑ σ : Config N, v σ • std_basis N σ := by
    ext τ
    simp [std_basis]
  simp_rw [hB]
  simp only [PhysLean.Probability.GaussianIBP.covOp_apply]
  have hinner (σ τ : Config N) :
      inner ℝ (∑ i : hg.ι,
        ((hg.τ i : ℝ) * inner ℝ (std_basis N σ) (hg.w i)) • hg.w i)
        (std_basis N τ) =
      ∑ i : hg.ι, (hg.τ i : ℝ) * (hg.w i) σ * (hg.w i) τ := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left, inner_std_basis_apply]
    rw [real_inner_comm, inner_std_basis_apply]
    simp
  simp_rw [hinner]
  have hexpand (i : hg.ι) :
      (D (hg.w i)) (hg.w i) =
        ∑ σ : Config N, ∑ τ : Config N,
          (hg.w i) σ * (hg.w i) τ * (D (std_basis N τ)) (std_basis N σ) := by
    let S := ∑ σ : Config N, (hg.w i) σ • std_basis N σ
    have hwi : hg.w i = S := hrepr (hg.w i)
    calc
      (D (hg.w i)) (hg.w i) = (D S) S :=
        congrArg₂ (fun v u => (D v) u) hwi hwi
      _ = _ := by
        simp [S, std_basis, map_sum, map_smul, smul_eq_mul,
          Finset.mul_sum, Finset.sum_mul]
        ring
  simp_rw [hexpand]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma coupledJointTrace_split_workspace
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (H : EnergySpace N) (Λ : ℝ) :
    (∑ i : (isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) hIndep).ι,
      ((isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) hIndep).τ i : ℝ) *
      coupledHessianDet N q H (Λ / 2)
        (coupledIBPJointCLM (N := N) a b
          ((isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) hIndep).w i))
        (coupledIBPJointCLM (N := N) a' b'
          ((isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) hIndep).w i))) =
      (a * a') * ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
        coupledHessianDet N q H (Λ / 2) (sk.hU.w i) (sk.hU.w i) +
      (b * b') * ∑ i : sim.hV.ι, (sim.hV.τ i : ℝ) *
        coupledHessianDet N q H (Λ / 2) (sim.hV.w i) (sim.hV.w i) := by
  classical
  have hU (i : sk.hU.ι) :
      coupledIBPJointCLM (N := N) a b (WithLp.toLp 2 (sk.hU.w i, 0)) =
        a • sk.hU.w i := by simp [coupledIBPJointCLM]
  have hU' (i : sk.hU.ι) :
      coupledIBPJointCLM (N := N) a' b' (WithLp.toLp 2 (sk.hU.w i, 0)) =
        a' • sk.hU.w i := by simp [coupledIBPJointCLM]
  have hV (i : sim.hV.ι) :
      coupledIBPJointCLM (N := N) a b (WithLp.toLp 2 (0, sim.hV.w i)) =
        b • sim.hV.w i := by simp [coupledIBPJointCLM]
  have hV' (i : sim.hV.ι) :
      coupledIBPJointCLM (N := N) a' b' (WithLp.toLp 2 (0, sim.hV.w i)) =
        b' • sim.hV.w i := by simp [coupledIBPJointCLM]
  simp only [isGaussianHilbert_UV,
    OrthonormalBasis.prod_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    LinearMap.inl_apply, LinearMap.inr_apply, Function.comp_apply]
  simp_rw [hU, hU', hV, hV']
  simp_rw [coupledHessian_eq_secondFDeriv_workspace (N := N) (q := q)]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Joint Gaussian IBP for the smart-path derivative, expressed as a canonical
configuration-basis covariance trace.

This should be proved with `UV`, `isGaussianHilbert_UV`, and
`gaussian_integration_by_parts_hilbert_cov_op`, following the existing proof of
`pressure_derivative_ibp_trace` and the scratch development in
`.tmp_gaussian_interp.lean`.
-/
lemma coupledFreeEnergy_time_ibp_trace_workspace
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (1 / 2) *
        ∫ w,
          (∑ σ : Config N, ∑ τ : Config N,
            (sk_cov_kernel N β σ τ -
              simple_cov_kernel N β (fun x => q * x) σ τ) *
              coupledHessianDet
                (N := N) (q := q)
                (H_t
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := sk) (sim := sim) t w)
                (Λ / 2)
                (std_basis N σ) (std_basis N τ))
          ∂ℙ := by
  /-
  Recommended structure:

  1. set `a = sqrt t`, `b = sqrt (1-t)`,
     `a' = 1/(2*sqrt t)`, `b' = -1/(2*sqrt (1-t))`;
  2. package `(sk.U, sim.V)` using `isGaussianHilbert_UV hIndep`;
  3. apply Gaussian IBP to the first variation of `coupledFreeEnergyDet`;
  4. rewrite the derivative using
     `fderiv_coupledFirstVariation_apply_workspace`;
  5. split the product-Hilbert eigenbasis trace into the U and V blocks;
  6. change each eigenbasis trace to the canonical `std_basis` trace;
  7. use `sk.cov_eq` and `sim.cov_eq`;
  8. simplify `a*a' = 1/2` and `b*b' = -1/2`.
  -/
  classical
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  set a := Real.sqrt t
  set b := Real.sqrt (1 - t)
  set a' := 1 / (2 * Real.sqrt t)
  set b' := -1 / (2 * Real.sqrt (1 - t))
  let field := H_field (N := N) (h := h)
  let hg := isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hIndep
  let A := coupledIBPJointCLM (N := N) a b
  let B := coupledIBPJointCLM (N := N) a' b'
  let Φ := fun H : EnergySpace N => coupledFreeEnergyDet (N := N) (q := q) H Λ
  have hFi_diff : ∀ i : hg.ι, ContDiff ℝ 1
      (fun x => fderiv ℝ Φ (A x + field) (B (hg.w i))) := by
    intro i
    have hΦ := contDiff_coupledFreeEnergyDet_beforeIBP (N := N) (q := q) Λ
    have hgrad : ContDiff ℝ 1 (fderiv ℝ Φ) :=
      hΦ.fderiv_right (m := (1 : WithTop ℕ∞)) (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    exact (hgrad.comp (A.contDiff.add contDiff_const)).clm_apply contDiff_const
  have hFi_growth : ∀ i : hg.ι,
      PhysLean.Probability.GaussianIBP.HasModerateGrowth
        (fun x => fderiv ℝ Φ (A x + field) (B (hg.w i))) := by
    intro i
    exact coupledFirstVariationModerateGrowth_workspace
      (N := N) (q := q) A field (B (hg.w i)) Λ
  have hmain := gaussian_ibp_gradient_linear
    (g := UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
    (hg := hg) A B field Φ hFi_diff hFi_growth
  have hraw :
      (∫ w, fderiv ℝ Φ
        (a • sk.U w + b • sim.V w + field)
        (a' • sk.U w + b' • sim.V w) ∂ℙ) =
      ∫ w, ∑ i : hg.ι, (hg.τ i : ℝ) *
        coupledHessianDet N q
          (a • sk.U w + b • sim.V w + field) (Λ / 2)
          (B (hg.w i)) (A (hg.w i)) ∂ℙ := by
    change (∫ w, fderiv ℝ Φ
      (A (UV (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) w) + field)
      (B (UV (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) w)) ∂ℙ) = _
    rw [hmain]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_coupledFirstVariation_affine_workspace
      (N := N) (q := q) A field (B (hg.w i))
      (UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) w)
      (hg.w i) Λ]
    simp [A, B, UV, coupledIBPJointCLM]
  have haa : a * a' = 1 / 2 := by
    dsimp [a, a']
    field_simp [ne_of_gt (Real.sqrt_pos.mpr ht0)]
  have hbb : b * b' = -(1 / 2) := by
    dsimp [b, b']
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ht1))]
  have hH : H_t (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t =
      fun w => a • sk.U w + b • sim.V w + field := by
    unfold H_t H_gauss
    simp [a, b, field]
  have hdH : dH_t (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) t =
      fun w => a' • sk.U w + b' • sim.V w := by
    unfold dH_t
    ext w
    simp [a', b']
    ring
  simp only [hH, hdH]
  rw [hraw]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  rw [coupledJointTrace_split_workspace
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hIndep a' b' a b (a • sk.U w + b • sim.V w + field) Λ]
  rw [mul_comm a' a, mul_comm b' b, haa, hbb]
  rw [coupledGaussianTrace_eq_stdBasis_workspace
    (N := N) (q := q) sk.U sk.hU
    (a • sk.U w + b • sim.V w + field) Λ]
  rw [coupledGaussianTrace_eq_stdBasis_workspace
    (N := N) (q := q) sim.V sim.hV
    (a • sk.U w + b • sim.V w + field) Λ]
  simp_rw [sk.cov_eq, sim.cov_eq]
  simp_rw [sub_mul]
  simp only [Finset.sum_sub_distrib]
  ring

/-! ## Finite replica algebra -/

private lemma weighted_sum_sub_constant
    {ι : Type*} [Fintype ι] (c a : ℝ) (f weight : ι → ℝ) :
    (∑ i, c * (f i - a) * weight i) =
      c * (∑ i, f i * weight i) - c * a * ∑ i, weight i := by
  calc
    (∑ i, c * (f i - a) * weight i) =
        ∑ i, (c * f i * weight i - c * a * weight i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      refine congrArg₂ (· - ·) ?_ ?_
      · calc
          (∑ i, c * f i * weight i) = ∑ i, c * (f i * weight i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := (Finset.mul_sum _ _ _).symm
      · exact (Finset.mul_sum _ _ _).symm

lemma covKernelDiff_eq_centered_sq_workspace
    (σ τ : Config N) :
    sk_cov_kernel N β σ τ -
        simple_cov_kernel N β (fun x => q * x) σ τ =
      ((N : ℝ) * β ^ 2 / 2) *
        ((overlap N σ τ - q) ^ 2 - q ^ 2) := by
  simp [sk_cov_kernel, simple_cov_kernel]
  ring

lemma sum_crossPairCenteredOverlapSq_workspace
    (σs : ReplicaSpace N 4) :
    (centeredOverlap
        (N := N) (q := q)
        (0 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (0 : Fin 4) (3 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (1 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (1 : Fin 4) (3 : Fin 4) σs) ^ 2 =
      4 * crossPairCenteredOverlapSq
        (N := N) (q := q) σs := by
  unfold crossPairCenteredOverlapSq
  ring

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma sum_pairEval_std_basis_product_workspace
    (D : Config N → Config N → ℝ) (σs : ReplicaSpace N 2) :
    (∑ σ : Config N, ∑ τ : Config N,
      D σ τ * pairEval N (std_basis N σ) σs *
        pairEval N (std_basis N τ) σs) =
      D (σs 0) (σs 0) + D (σs 0) (σs 1) +
        D (σs 1) (σs 0) + D (σs 1) (σs 1) := by
  simp only [pairEval, std_basis]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  simp

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma sum_pairEval_std_basis_cross_workspace
    (D : Config N → Config N → ℝ)
    (σs ρs : ReplicaSpace N 2) :
    (∑ σ : Config N, ∑ τ : Config N,
      D σ τ * pairEval N (std_basis N σ) σs *
        pairEval N (std_basis N τ) ρs) =
      D (σs 0) (ρs 0) + D (σs 0) (ρs 1) +
        D (σs 1) (ρs 0) + D (σs 1) (ρs 1) := by
  simp only [pairEval, std_basis]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  simp

/-- Pointwise finite-volume trace identity.

This is the main algebraic goal. Unfold `coupledHessianDet`; the first tilted
expectation gives `(1-q)^2 + tilted Q₁₂²`, while the product of tilted means is
represented by four replicas and gives `2 * coupledCrossMomentDet` after all
normalizations are collected.
-/
lemma coupled_trace_algebra_workspace
    (hN : 0 < N)
    (H : EnergySpace N) (coupling : ℝ) :
    (1 / 2) *
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
            coupledHessianDet
              (N := N) (q := q) H coupling
              (std_basis N σ) (std_basis N τ)) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSqDet
            (N := N) (q := q) H coupling -
          2 * coupledCrossMomentDet
            (N := N) (q := q) H coupling) := by
  /-
  Useful ingredients:

  * `covKernelDiff_eq_centered_sq_workspace`;
  * `overlap_self hN`;
  * `sum_gibbs_pmf` and `sum_prod_gibbs_pmf_eq_one`;
  * `tiltedReplicaPartitionDet_pos`;
  * an explicit equivalence
    `ReplicaSpace N 4 ≃ ReplicaSpace N 2 × ReplicaSpace N 2`;
  * `sum_crossPairCenteredOverlapSq_workspace`.
  -/
  classical

    let D : Config N → Config N → ℝ := fun σ τ =>
      (overlap N σ τ - q) ^ 2 - q ^ 2

    let W₂ : ReplicaSpace N 2 → ℝ := fun σs =>
      Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs) *
        ∏ l, gibbs_pmf N H (σs l)

    let W₄ : ReplicaSpace N 4 → ℝ := fun σs =>
      Real.exp (coupling * (N : ℝ) *
        ((centeredOverlap (N := N) (q := q) (0 : Fin 4) (1 : Fin 4) σs) ^ 2 +
        (centeredOverlap (N := N) (q := q) (2 : Fin 4) (3 : Fin 4) σs) ^ 2)) *
        ∏ l, gibbs_pmf N H (σs l)

    let e : ReplicaSpace N 4 ≃ ReplicaSpace N 2 × ReplicaSpace N 2 :=
      { toFun := fun σs =>
          (fun i => σs (if i = 0 then 0 else 1),
          fun i => σs (if i = 0 then 2 else 3))
        invFun := fun p i =>
          if i = 0 then p.1 0
          else if i = 1 then p.1 1
          else if i = 2 then p.2 0
          else p.2 1
        left_inv := by
          intro σs
          ext i
          fin_cases i <;> rfl
        right_inv := by
          intro p
          rcases p with ⟨σs, ρs⟩
          apply Prod.ext
          · ext i
            fin_cases i <;> rfl
          · ext i
            fin_cases i <;> rfl }

    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast hN.ne'

    have hoverlap_comm (σ τ : Config N) :
        overlap N σ τ = overlap N τ σ := by
      unfold overlap
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

    have hpart :
        tiltedReplicaPartitionDet (N := N) (q := q) H coupling =
          ∑ σs : ReplicaSpace N 2, W₂ σs := by
      rfl

    have hZpos : 0 < ∑ σs : ReplicaSpace N 2, W₂ σs := by
      rw [← hpart]
      exact tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H coupling

    have hZ0 : (∑ σs : ReplicaSpace N 2, W₂ σs) ≠ 0 :=
      ne_of_gt hZpos

    have htilt (f : ReplicaFun N 2) :
        tiltedReplicaAverageDet (N := N) (q := q) H coupling f =
          (∑ σs : ReplicaSpace N 2, f σs * W₂ σs) /
            (∑ σs : ReplicaSpace N 2, W₂ σs) := by
      unfold tiltedReplicaAverageDet gibbs_average_n_det
      rw [hpart]
      congr 1
      apply Finset.sum_congr rfl
      intro σs _
      dsimp only [W₂]
      ring

    have htiltedSq :
        tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling =
          (∑ σs : ReplicaSpace N 2,
              centeredOverlapSq N q σs * W₂ σs) /
            (∑ σs : ReplicaSpace N 2, W₂ σs) := by
      unfold tiltedCenteredOverlapSqDet gibbs_average_n_det
      rw [hpart]
      congr 1
      apply Finset.sum_congr rfl
      intro σs _
      dsimp only [W₂]
      ring

    have hcross :
        coupledCrossMomentDet (N := N) (q := q) H coupling =
          (∑ σs : ReplicaSpace N 4,
              crossPairCenteredOverlapSq (N := N) (q := q) σs * W₄ σs) /
            (∑ σs : ReplicaSpace N 2, W₂ σs) ^ 2 := by
      unfold coupledCrossMomentDet gibbs_average_n_det
      rw [hpart]
      congr 1
      apply Finset.sum_congr rfl
      intro σs _
      dsimp only [W₄]
      ring

    have hsplit_weight (σs : ReplicaSpace N 4) :
        W₄ σs = W₂ (e σs).1 * W₂ (e σs).2 := by
      change W₄ σs =
        W₂ (fun i : Fin 2 => σs (if i = 0 then 0 else 1)) *
          W₂ (fun i : Fin 2 => σs (if i = 0 then 2 else 3))
      dsimp only [W₄, W₂, centeredOverlapSq, centeredOverlap]
      simp +decide only [Fin.prod_univ_two, Fin.prod_univ_four, if_true, if_false]
      rw [show coupling * (N : ℝ) *
            ((overlap N (σs 0) (σs 1) - q) ^ 2 +
              (overlap N (σs 2) (σs 3) - q) ^ 2) =
          coupling * (N : ℝ) * (overlap N (σs 0) (σs 1) - q) ^ 2 +
            coupling * (N : ℝ) * (overlap N (σs 2) (σs 3) - q) ^ 2 by
        ring]
      rw [Real.exp_add]
      ring_nf

    have hweight_sq :
        (∑ σs : ReplicaSpace N 4, W₄ σs) =
          (∑ σs : ReplicaSpace N 2, W₂ σs) ^ 2 := by
      calc
        (∑ σs : ReplicaSpace N 4, W₄ σs) =
            ∑ p : ReplicaSpace N 2 × ReplicaSpace N 2,
              W₂ p.1 * W₂ p.2 := by
          exact Fintype.sum_equiv e W₄
            (fun p => W₂ p.1 * W₂ p.2) hsplit_weight
        _ = (∑ σs : ReplicaSpace N 2, W₂ σs) ^ 2 := by
          simp only [Fintype.sum_prod_type]
          rw [sq, Finset.sum_mul]
          simp only [Finset.mul_sum]

    have hfour_pair :
        (∑ σs : ReplicaSpace N 4,
            (4 * crossPairCenteredOverlapSq (N := N) (q := q) σs - 4 * q ^ 2) *
              W₄ σs) =
          ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
            (4 * crossPairCenteredOverlapSq (N := N) (q := q)
                (e.symm (σs, ρs)) - 4 * q ^ 2) * W₂ σs * W₂ ρs := by
      calc
        (∑ σs : ReplicaSpace N 4,
            (4 * crossPairCenteredOverlapSq (N := N) (q := q) σs - 4 * q ^ 2) *
              W₄ σs) =
            ∑ p : ReplicaSpace N 2 × ReplicaSpace N 2,
              (4 * crossPairCenteredOverlapSq (N := N) (q := q) (e.symm p) -
                4 * q ^ 2) * W₂ p.1 * W₂ p.2 := by
          exact Fintype.sum_equiv e
            (fun σs =>
              (4 * crossPairCenteredOverlapSq (N := N) (q := q) σs - 4 * q ^ 2) *
                W₄ σs)
            (fun p =>
              (4 * crossPairCenteredOverlapSq (N := N) (q := q) (e.symm p) -
                4 * q ^ 2) * W₂ p.1 * W₂ p.2)
            (fun σs => by
              simpa only [hsplit_weight σs, Equiv.symm_apply_apply, mul_assoc])
        _ = _ := by
          simp only [Fintype.sum_prod_type]

    have hwithin_point (σs : ReplicaSpace N 2) :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ * pairEval N (std_basis N σ) σs *
            pairEval N (std_basis N τ) σs) =
          2 * (1 - q) ^ 2 + 2 * centeredOverlapSq N q σs - 4 * q ^ 2 := by
      rw [sum_pairEval_std_basis_product_workspace
        (N := N) (D := D) σs]
      dsimp only [D]
      rw [overlap_self (N := N) hN (σs 0),
        overlap_self (N := N) hN (σs 1),
        hoverlap_comm (σs 1) (σs 0)]
      dsimp only [centeredOverlapSq]
      ring

    have hcross_point (σs ρs : ReplicaSpace N 2) :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ * pairEval N (std_basis N σ) σs *
            pairEval N (std_basis N τ) ρs) =
          4 * crossPairCenteredOverlapSq (N := N) (q := q)
              (e.symm (σs, ρs)) - 4 * q ^ 2 := by
      rw [sum_pairEval_std_basis_cross_workspace
        (N := N) (D := D) σs ρs]
      simp +decide [D, e, crossPairCenteredOverlapSq, centeredOverlap]
      ring

    have hwithin_num :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (∑ σs : ReplicaSpace N 2,
              (pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs) * W₂ σs)) =
          ∑ σs : ReplicaSpace N 2,
            (2 * (1 - q) ^ 2 + 2 * centeredOverlapSq N q σs - 4 * q ^ 2) *
              W₂ σs := by
      calc
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (∑ σs : ReplicaSpace N 2,
              (pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs) * W₂ σs)) =
            ∑ σ : Config N, ∑ τ : Config N, ∑ σs : ReplicaSpace N 2,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs * W₂ σs := by
          apply Finset.sum_congr rfl
          intro σ _
          apply Finset.sum_congr rfl
          intro τ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σs _
          ring
        _ = ∑ σ : Config N, ∑ σs : ReplicaSpace N 2, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs * W₂ σs := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2, ∑ σ : Config N, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs * W₂ σs := by
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2,
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs) * W₂ σs := by
          apply Finset.sum_congr rfl
          intro σs _
          calc
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs * W₂ σs) =
                ∑ σ : Config N,
                  (∑ τ : Config N,
                    D σ τ * pairEval N (std_basis N σ) σs *
                      pairEval N (std_basis N τ) σs) * W₂ σs := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [Finset.sum_mul]
            _ = _ := by
              rw [Finset.sum_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro σs _
          rw [hwithin_point σs]

    have hcross_num :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (∑ σs : ReplicaSpace N 2,
              pairEval N (std_basis N σ) σs * W₂ σs) *
            (∑ ρs : ReplicaSpace N 2,
              pairEval N (std_basis N τ) ρs * W₂ ρs)) =
          ∑ σs : ReplicaSpace N 4,
            (4 * crossPairCenteredOverlapSq (N := N) (q := q) σs - 4 * q ^ 2) *
              W₄ σs := by
      calc
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (∑ σs : ReplicaSpace N 2,
              pairEval N (std_basis N σ) σs * W₂ σs) *
            (∑ ρs : ReplicaSpace N 2,
              pairEval N (std_basis N τ) ρs * W₂ ρs)) =
            ∑ σ : Config N, ∑ τ : Config N,
              ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
                D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                  pairEval N (std_basis N τ) ρs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σ _
          apply Finset.sum_congr rfl
          intro τ _
          calc
            D σ τ *
                  (∑ σs : ReplicaSpace N 2,
                    pairEval N (std_basis N σ) σs * W₂ σs) *
                  (∑ ρs : ReplicaSpace N 2,
                    pairEval N (std_basis N τ) ρs * W₂ ρs) =
                (∑ σs : ReplicaSpace N 2,
                  D σ τ * (pairEval N (std_basis N σ) σs * W₂ σs)) *
                  (∑ ρs : ReplicaSpace N 2,
                    pairEval N (std_basis N τ) ρs * W₂ ρs) := by
              congr 1
              rw [Finset.mul_sum]
            _ = ∑ σs : ReplicaSpace N 2,
                  (D σ τ * (pairEval N (std_basis N σ) σs * W₂ σs)) *
                    (∑ ρs : ReplicaSpace N 2,
                      pairEval N (std_basis N τ) ρs * W₂ ρs) := by
              rw [Finset.sum_mul]
            _ = ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
                  D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                    pairEval N (std_basis N τ) ρs * W₂ ρs := by
              apply Finset.sum_congr rfl
              intro σs _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ρs _
              ring
        _ = ∑ σ : Config N, ∑ σs : ReplicaSpace N 2,
              ∑ τ : Config N, ∑ ρs : ReplicaSpace N 2,
                D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                  pairEval N (std_basis N τ) ρs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2, ∑ σ : Config N,
              ∑ τ : Config N, ∑ ρs : ReplicaSpace N 2,
                D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                  pairEval N (std_basis N τ) ρs * W₂ ρs := by
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2, ∑ σ : Config N,
              ∑ ρs : ReplicaSpace N 2, ∑ τ : Config N,
                D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                  pairEval N (std_basis N τ) ρs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σs _
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
              ∑ σ : Config N, ∑ τ : Config N,
                D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                  pairEval N (std_basis N τ) ρs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σs _
          rw [Finset.sum_comm]
        _ = ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) ρs) * W₂ σs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σs _
          apply Finset.sum_congr rfl
          intro ρs _
          calc
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ * pairEval N (std_basis N σ) σs * W₂ σs *
                pairEval N (std_basis N τ) ρs * W₂ ρs) =
                ∑ σ : Config N, ∑ τ : Config N,
                  (D σ τ * pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) ρs) * (W₂ σs * W₂ ρs) := by
              apply Finset.sum_congr rfl
              intro σ _
              apply Finset.sum_congr rfl
              intro τ _
              ring
            _ = ∑ σ : Config N,
                  (∑ τ : Config N,
                    D σ τ * pairEval N (std_basis N σ) σs *
                      pairEval N (std_basis N τ) ρs) * (W₂ σs * W₂ ρs) := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [Finset.sum_mul]
            _ = (∑ σ : Config N, ∑ τ : Config N,
                  D σ τ * pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) ρs) * (W₂ σs * W₂ ρs) := by
              rw [Finset.sum_mul]
            _ = _ := by
              ring
        _ = ∑ σs : ReplicaSpace N 2, ∑ ρs : ReplicaSpace N 2,
            (4 * crossPairCenteredOverlapSq (N := N) (q := q)
                (e.symm (σs, ρs)) - 4 * q ^ 2) * W₂ σs * W₂ ρs := by
          apply Finset.sum_congr rfl
          intro σs _
          apply Finset.sum_congr rfl
          intro ρs _
          rw [hcross_point σs ρs]
        _ = _ := hfour_pair.symm

    have hwithin :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (fun σs => pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs)) =
          2 * (1 - q) ^ 2 +
            2 * tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling -
            4 * q ^ 2 := by
      calc
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (fun σs => pairEval N (std_basis N σ) σs *
                pairEval N (std_basis N τ) σs)) =
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                (∑ σs : ReplicaSpace N 2,
                  (pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) σs) * W₂ σs)) /
              (∑ σs : ReplicaSpace N 2, W₂ σs) := by
          simp_rw [htilt]
          simp only [div_eq_mul_inv]
          calc
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                ((∑ σs : ReplicaSpace N 2,
                  (pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) σs) * W₂ σs) *
                  (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹)) =
                ∑ σ : Config N, ∑ τ : Config N,
                  (D σ τ *
                    (∑ σs : ReplicaSpace N 2,
                      (pairEval N (std_basis N σ) σs *
                        pairEval N (std_basis N τ) σs) * W₂ σs)) *
                    (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹ := by
              apply Finset.sum_congr rfl
              intro σ _
              apply Finset.sum_congr rfl
              intro τ _
              ring
            _ = ∑ σ : Config N,
                  (∑ τ : Config N,
                    D σ τ *
                      (∑ σs : ReplicaSpace N 2,
                        (pairEval N (std_basis N σ) σs *
                          pairEval N (std_basis N τ) σs) * W₂ σs)) *
                    (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹ := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [Finset.sum_mul]
            _ = (∑ σ : Config N, ∑ τ : Config N,
                  D σ τ *
                    (∑ σs : ReplicaSpace N 2,
                      (pairEval N (std_basis N σ) σs *
                        pairEval N (std_basis N τ) σs) * W₂ σs)) *
                  (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹ := by
              rw [Finset.sum_mul]
        _ = (∑ σs : ReplicaSpace N 2,
              (2 * (1 - q) ^ 2 + 2 * centeredOverlapSq N q σs - 4 * q ^ 2) *
                W₂ σs) /
              (∑ σs : ReplicaSpace N 2, W₂ σs) := by
          rw [hwithin_num]
        _ = 2 * (1 - q) ^ 2 +
            2 * tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling -
            4 * q ^ 2 := by
          rw [htiltedSq]
          field_simp [hZ0]
          calc
            (∑ σs : ReplicaSpace N 2,
                (2 * ((1 - q) ^ 2 + centeredOverlapSq N q σs) - q ^ 2 * 4) *
                  W₂ σs) =
                ∑ σs : ReplicaSpace N 2,
                  ((2 * (1 - q) ^ 2 - 4 * q ^ 2) * W₂ σs +
                    2 * (centeredOverlapSq N q σs * W₂ σs)) := by
              apply Finset.sum_congr rfl
              intro σs _
              ring
            _ = (∑ σs : ReplicaSpace N 2,
                  (2 * (1 - q) ^ 2 - 4 * q ^ 2) * W₂ σs) +
                ∑ σs : ReplicaSpace N 2,
                  2 * (centeredOverlapSq N q σs * W₂ σs) :=
              Finset.sum_add_distrib
            _ = _ := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              ring

    have hbetween :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (pairEval N (std_basis N σ)) *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (pairEval N (std_basis N τ))) =
          4 * coupledCrossMomentDet (N := N) (q := q) H coupling -
            4 * q ^ 2 := by
      calc
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (pairEval N (std_basis N σ)) *
            tiltedReplicaAverageDet (N := N) (q := q) H coupling
              (pairEval N (std_basis N τ))) =
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                (∑ σs : ReplicaSpace N 2,
                  pairEval N (std_basis N σ) σs * W₂ σs) *
                (∑ ρs : ReplicaSpace N 2,
                  pairEval N (std_basis N τ) ρs * W₂ ρs)) /
              (∑ σs : ReplicaSpace N 2, W₂ σs) ^ 2 := by
          simp_rw [htilt]
          simp only [div_eq_mul_inv]
          rw [← inv_pow]
          calc
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                ((∑ σs : ReplicaSpace N 2,
                  pairEval N (std_basis N σ) σs * W₂ σs) *
                  (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹) *
                ((∑ ρs : ReplicaSpace N 2,
                  pairEval N (std_basis N τ) ρs * W₂ ρs) *
                  (∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹)) =
                ∑ σ : Config N, ∑ τ : Config N,
                  (D σ τ *
                    (∑ σs : ReplicaSpace N 2,
                      pairEval N (std_basis N σ) σs * W₂ σs) *
                    (∑ ρs : ReplicaSpace N 2,
                      pairEval N (std_basis N τ) ρs * W₂ ρs)) *
                    ((∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹) ^ 2 := by
              apply Finset.sum_congr rfl
              intro σ _
              apply Finset.sum_congr rfl
              intro τ _
              ring
            _ = ∑ σ : Config N,
                  (∑ τ : Config N,
                    D σ τ *
                      (∑ σs : ReplicaSpace N 2,
                        pairEval N (std_basis N σ) σs * W₂ σs) *
                      (∑ ρs : ReplicaSpace N 2,
                        pairEval N (std_basis N τ) ρs * W₂ ρs)) *
                    ((∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹) ^ 2 := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [Finset.sum_mul]
            _ = (∑ σ : Config N, ∑ τ : Config N,
                  D σ τ *
                    (∑ σs : ReplicaSpace N 2,
                      pairEval N (std_basis N σ) σs * W₂ σs) *
                    (∑ ρs : ReplicaSpace N 2,
                      pairEval N (std_basis N τ) ρs * W₂ ρs)) *
                  ((∑ σs : ReplicaSpace N 2, W₂ σs)⁻¹) ^ 2 := by
              rw [Finset.sum_mul]
        _ = (∑ σs : ReplicaSpace N 4,
              (4 * crossPairCenteredOverlapSq (N := N) (q := q) σs - 4 * q ^ 2) *
                W₄ σs) /
              (∑ σs : ReplicaSpace N 2, W₂ σs) ^ 2 := by
          rw [hcross_num]
        _ = 4 * coupledCrossMomentDet (N := N) (q := q) H coupling -
            4 * q ^ 2 := by
          rw [hcross]
          field_simp [hZ0]
          rw [← hweight_sq]
          rw [weighted_sum_sub_constant]
          ring

    have hcore :
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (fun σs => pairEval N (std_basis N σ) σs *
                  pairEval N (std_basis N τ) σs) -
              tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (pairEval N (std_basis N σ)) *
              tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (pairEval N (std_basis N τ)))) =
          2 * ((1 - q) ^ 2 +
            tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling -
            2 * coupledCrossMomentDet (N := N) (q := q) H coupling) := by
      calc
        (∑ σ : Config N, ∑ τ : Config N,
          D σ τ *
            (tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (fun σs => pairEval N (std_basis N σ) σs *
                  pairEval N (std_basis N τ) σs) -
              tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (pairEval N (std_basis N σ)) *
              tiltedReplicaAverageDet (N := N) (q := q) H coupling
                (pairEval N (std_basis N τ)))) =
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                tiltedReplicaAverageDet (N := N) (q := q) H coupling
                  (fun σs => pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) σs)) -
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                tiltedReplicaAverageDet (N := N) (q := q) H coupling
                  (pairEval N (std_basis N σ)) *
                tiltedReplicaAverageDet (N := N) (q := q) H coupling
                  (pairEval N (std_basis N τ))) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc]
        _ = _ := by
          rw [hwithin, hbetween]
          ring

    simp_rw [covKernelDiff_eq_centered_sq_workspace
      (N := N) (β := β) (q := q)]
    unfold coupledHessianDet

    have hfactor :
        (∑ σ : Config N, ∑ τ : Config N,
          (((N : ℝ) * β ^ 2 / 2) *
            ((overlap N σ τ - q) ^ 2 - q ^ 2)) *
            ((1 / (2 * (N : ℝ))) *
              (tiltedReplicaAverageDet (N := N) (q := q) H coupling
                  (fun σs => pairEval N (std_basis N σ) σs *
                    pairEval N (std_basis N τ) σs) -
                tiltedReplicaAverageDet (N := N) (q := q) H coupling
                    (pairEval N (std_basis N σ)) *
                  tiltedReplicaAverageDet (N := N) (q := q) H coupling
                    (pairEval N (std_basis N τ))))) =
          (((N : ℝ) * β ^ 2 / 2) * (1 / (2 * (N : ℝ)))) *
            (∑ σ : Config N, ∑ τ : Config N,
              D σ τ *
                (tiltedReplicaAverageDet (N := N) (q := q) H coupling
                    (fun σs => pairEval N (std_basis N σ) σs *
                      pairEval N (std_basis N τ) σs) -
                  tiltedReplicaAverageDet (N := N) (q := q) H coupling
                      (pairEval N (std_basis N σ)) *
                    tiltedReplicaAverageDet (N := N) (q := q) H coupling
                      (pairEval N (std_basis N τ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      dsimp only [D]
      ring

    rw [hfactor, hcore]
    field_simp [hN0]
    ring

/-! ## Integrability of the normalized finite-state observables -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fourReplicaTiltWeight_sum_workspace
    (H : EnergySpace N) (coupling : ℝ) :
    (∑ σs : ReplicaSpace N 4,
      Real.exp (coupling * (N : ℝ) *
        ((centeredOverlap (N := N) (q := q) (0 : Fin 4) (1 : Fin 4) σs) ^ 2 +
          (centeredOverlap (N := N) (q := q) (2 : Fin 4) (3 : Fin 4) σs) ^ 2)) *
        ∏ l, gibbs_pmf N H (σs l)) =
      (tiltedReplicaPartitionDet (N := N) (q := q) H coupling) ^ 2 := by
  rw [ sq, tiltedReplicaPartitionDet ];
  unfold gibbs_average_n_det;
  simp +decide only [Fin.prod_univ_two, Finset.sum_mul];
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( fun i => x ( if i = 0 then 0 else 1 ), fun i => x ( if i = 0 then 2 else 3 ) ) ) _ _ _ _ <;> simp +decide;
  · simp +decide [ funext_iff, Fin.forall_fin_succ ];
    tauto;
  · exact fun a b => ⟨ fun i => if i = 0 then a 0 else if i = 1 then a 1 else if i = 2 then b 0 else b 1, by ext i; fin_cases i <;> rfl, by ext i; fin_cases i <;> rfl ⟩;
  · simp +decide [ Fin.prod_univ_four, centeredOverlapSq ];
    simp +decide [ centeredOverlap, overlap ] ; intros ; ring;
    simpa only [ mul_assoc, ← Real.exp_add ] using by ring;

lemma measurable_H_t_workspace (t : ℝ) :
    Measurable
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t) := by
  have hU : Measurable sk.U := sk.hU.repr_measurable
  have hV : Measurable sim.V := sim.hV.repr_measurable
  exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) t

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_coupledCrossMomentDet_workspace (coupling : ℝ) :
    Measurable
      (fun H : EnergySpace N =>
        coupledCrossMomentDet (N := N) (q := q) H coupling) := by
  refine' Measurable.mul _ _;
  · apply_rules [ Finset.measurable_sum, Finset.measurable_prod ];
    refine' fun σ _ => Measurable.mul _ _;
    · fun_prop;
    · exact Finset.measurable_prod _ fun _ _ => ( contDiff_gibbs_pmf N ( σ _ ) |> ContDiff.continuous |> Continuous.measurable );
  · refine' Measurable.inv ( Measurable.pow_const _ _ );
    refine' Finset.measurable_sum _ fun σs _ => _;
    refine' Measurable.mul _ _;
    · exact measurable_const;
    · exact Finset.measurable_prod _ fun _ _ => ( contDiff_gibbs_pmf ( N := N ) ( σ := σs _ ) |> ContDiff.continuous |> Continuous.measurable )

lemma integrable_tiltedCenteredOverlapSqDet_Ht_workspace
    (t coupling : ℝ) :
    Integrable
      (fun ω =>
        tiltedCenteredOverlapSqDet
          (N := N) (q := q)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          coupling) ℙ := by
  /-
  The tilted quantity is a normalized expectation of a fixed observable on a
  finite state space. Bound it by

    `∑ σs : ReplicaSpace N 2, |centeredOverlapSq N q σs|`.
  -/
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ( ∑ σs : ReplicaSpace N 2, ( N : ℝ ) * centeredOverlapSq N q σs );
  · norm_num;
  · have h_measurable : Measurable (fun H : EnergySpace N => tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling) := by
      refine' Measurable.div _ _;
      · refine' Finset.measurable_sum _ fun σs _ => _;
        refine' Measurable.mul _ _;
        · fun_prop;
        · refine' Finset.measurable_prod _ fun i _ => _;
          refine' Measurable.div _ _;
          · fun_prop;
          · refine' Finset.measurable_sum _ fun σ _ => _;
            fun_prop;
      · refine' Finset.measurable_sum _ fun σs _ => _;
        refine' Measurable.mul _ _;
        · exact measurable_const;
        · refine' Finset.measurable_prod _ fun i _ => _;
          refine' Measurable.div _ _;
          · fun_prop;
          · exact Finset.measurable_sum _ fun _ _ => Real.continuous_exp.measurable.comp ( measurable_neg.comp ( by measurability ) );
    have h_measurable : Measurable (fun ω => H_t (N := N) (β := β) (h := h)
        (q := q) (sk := sk) (sim := sim) t ω) :=
      measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t
    exact Measurable.aestronglyMeasurable ( by measurability );
  · refine' Filter.Eventually.of_forall fun ω => _;
    rw [ tiltedCenteredOverlapSqDet ];
    rw [ gibbs_average_n_det, tiltedReplicaPartitionDet ];
    rw [ gibbs_average_n_det ];
    rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( by exact sq_nonneg _ ) ( Real.exp_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => by exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => by exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ) ) ];
    rw [ div_le_iff₀ ];
    · rw [ Finset.sum_mul _ _ _ ];
      refine' Finset.sum_le_sum fun i _ => _;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun a _ => mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun b _ => _ ) ) ( Finset.mem_univ i ) ) _ );
      · rw [ mul_assoc ];
        gcongr;
        · exact mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) );
        · exact le_mul_of_one_le_left ( sq_nonneg _ ) ( mod_cast NeZero.pos N );
      · exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ );
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ );
    · refine' Finset.sum_pos _ _ <;> simp +decide [ gibbs_pmf ];
      exact fun _ => mul_pos ( Real.exp_pos _ ) ( div_pos ( mul_pos ( Real.exp_pos _ ) ( Real.exp_pos _ ) ) ( sq_pos_of_pos ( Z_pos _ _ ) ) )

lemma integrable_coupledCrossMomentDet_Ht_workspace
    (t coupling : ℝ) :
    Integrable
      (fun ω =>
        coupledCrossMomentDet
          (N := N) (q := q)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          coupling) ℙ := by
  /-
  Again use the normalized finite four-replica law and bound by the finite sum
  of `|crossPairCenteredOverlapSq|`.
  -/
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ∑ σs : ReplicaSpace N 4, |crossPairCenteredOverlapSq N q σs|;
  · norm_num;
  · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( measurable_coupledCrossMomentDet_workspace N q coupling ) ( measurable_H_t_workspace N β h q sk sim t ) );
  · refine' Filter.Eventually.of_forall fun ω => _;
    unfold coupledCrossMomentDet gibbs_average_n_det;
    rw [ norm_div ];
    refine' div_le_of_le_mul₀ _ _ _;
    · positivity;
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _;
    · refine' le_trans ( norm_sum_le _ _ ) _;
      rw [ Finset.sum_mul _ _ _ ];
      refine' Finset.sum_le_sum fun σs _ => _;
      rw [ ← fourReplicaTiltWeight_sum_workspace ];
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_abs_self _ ) ( abs_nonneg _ ) );
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun σs _ => _ ) ( Finset.mem_univ σs ) ) ( abs_nonneg _ ) );
      · simp +decide [ abs_mul, abs_of_nonneg, Real.exp_nonneg, gibbs_pmf_nonneg ];
        rw [ mul_assoc ];
      · exact mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) )

/-! ## Evaluate the raw differentiated integral -/

lemma coupledFreeEnergy_time_derivative_ibp_formula_workspace
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω,
        fderiv ℝ
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
        ∂ℙ) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2)) := by
  let T : Ω → ℝ := fun ω =>
    tiltedCenteredOverlapSqDet
      (N := N) (q := q)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω)
      (Λ / 2)
  let X : Ω → ℝ := fun ω =>
    coupledCrossMomentDet
      (N := N) (q := q)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω)
      (Λ / 2)

  have hT : Integrable T ℙ := by
    simpa only [T] using
      integrable_tiltedCenteredOverlapSqDet_Ht_workspace
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (Λ / 2)

  have hX : Integrable X ℙ := by
    simpa only [X] using
      integrable_coupledCrossMomentDet_Ht_workspace
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (Λ / 2)

  have hconst : Integrable (fun _ : Ω => (1 - q) ^ 2) ℙ :=
    integrable_const _

  have hsum : Integrable (fun ω => (1 - q) ^ 2 + T ω) ℙ :=
    hconst.add hT

  have htwiceX : Integrable (fun ω => 2 * X ω) ℙ :=
    hX.const_mul 2

  rw [coupledFreeEnergy_time_ibp_trace_workspace
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hIndep ht]

  rw [← integral_const_mul]

  rw [integral_congr_ae
    (ae_of_all _ fun ω =>
      coupled_trace_algebra_workspace
        (N := N) (β := β) (q := q) hN
        (H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω)
        (Λ / 2))]

  rw [integral_const_mul]
  rw [integral_sub hsum htwiceX]
  rw [integral_add hconst hT]
  rw [integral_const]
  rw [integral_const_mul]

  simp only [probReal_univ, one_smul]

  change
    (β ^ 2 / 4) *
        ((1 - q) ^ 2 + (∫ ω, T ω ∂ℙ) - 2 * (∫ ω, X ω ∂ℙ)) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2))

  simp only [T, X, tiltedCenteredOverlapSq, coupledCrossMoment]

/-- Gaussian IBP formula for the time derivative of the coupled free energy.

The term `coupledCrossMoment` is the named annealed four-replica quantity generated by the
covariance trace.  Its nonnegativity is recorded separately in `coupledCrossMoment_nonneg`.

Use the same joint Gaussian model and the same call to
`gaussian_integration_by_parts_hilbert_cov_op` as in the ordinary pressure calculation.  Replace
`Φ` by the normalized logarithm of the coupled two-replica partition sum.  Its first derivative
is the tilted two-replica Gibbs average, while its second derivative is the corresponding Gibbs
covariance.  After applying `sk.cov_eq` and `sim.cov_eq`, introduce enough replicas to express
that covariance as the ordinary overlap term minus the nonnegative four-replica cross moment.
Finite configuration space again gives `ContDiff` and a constant moderate-growth bound for each
basis-direction test function.

Normalization note: `crossPairCenteredOverlapSq` is the average of the four cross-pair squares.
With that convention, the trace computation produces `-2 * coupledCrossMoment`, while the two
within-pair terms produce one copy of `tiltedCenteredOverlapSq`.  These coefficients should be
checked directly when the IBP proof is completed. -/
lemma coupledFreeEnergy_hasDerivAt_time_ibp
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s Λ)
      ((β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t (Λ / 2))) t := by
  rw [← coupledFreeEnergy_time_derivative_ibp_formula_workspace
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hN hIndep ht]

  exact coupledFreeEnergy_hasDerivAt_time_before_ibp
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) ht

/-- The logarithmic quadratic moment is differentiable in the smart-path variable away from
the endpoints.

Proof route: subtract `pressure_derivative` from
`coupledFreeEnergy_hasDerivAt_time_ibp`, unfold `coupledExcess`, and rescale by `2N`.
The resulting derivative is retained existentially because only its inequality is used later. -/
lemma logQuadraticMoment_hasDerivAt_time
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t coupling : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ dt : ℝ,
      HasDerivAt
        (fun s => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s coupling) dt t := by
  have hcoupled := coupledFreeEnergy_hasDerivAt_time_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep (Λ := 2 * coupling) ht
  have hpressure := pressure_derivative
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep ht
  have hexcess := hcoupled.sub hpressure
  have hscaled := hexcess.const_mul (2 * (N : ℝ))
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hfun :
      (fun s => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        s coupling) =
      fun s => (2 * (N : ℝ)) *
        (coupledFreeEnergy
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            s (2 * coupling) -
          interpolatedPressure
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
    funext s
    simp only [coupledFreeEnergy, coupledExcess, physicalLogQuadraticMoment]
    rw [show (2 : ℝ) * coupling / 2 = coupling by ring]
    calc
      logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s coupling =
          (2 * (N : ℝ)) * (1 / (2 * (N : ℝ)) *
            logQuadraticMoment
              (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
              s coupling) := by field_simp [hN0]
      _ = _ := by ring
  rw [hfun]
  exact ⟨_, hscaled⟩

/-- Compatibility form of the explicit coupling derivative. -/
lemma deriv_logQuadraticMoment_coupling (t coupling : ℝ) :
    deriv
      (fun c => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t c) coupling =
      (N : ℝ) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t coupling :=
  (logQuadraticMoment_hasDerivAt_coupling_formula
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    t coupling).deriv

/-- The first-order differential inequality behind the moving-coupling estimate.

Proof route: combine the two preceding derivative lemmas with the coupled Gaussian-IBP
identity.  Drop the nonnegative cross moment, cancel the ordinary pressure derivative, and use
the standard tilted-moment estimate to bound the remaining covariance term by
`β² * logQuadraticMoment / (2 * coupling)`. -/
lemma logQuadraticMoment_differential_inequality
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t coupling : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hcoupling : 0 < coupling) :
    deriv
        (fun s => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s coupling) t -
        (β ^ 2 / 2) * deriv
          (fun c => logQuadraticMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t c) coupling
      ≤ (β ^ 2 / (2 * coupling)) *
          logQuadraticMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t coupling := by
  let L : ℝ → ℝ := fun s => logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s coupling
  let V : ℝ := overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
  let T : ℝ := tiltedCenteredOverlapSq
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t coupling
  let X : ℝ := coupledCrossMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t coupling
  have hC := coupledFreeEnergy_hasDerivAt_time_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep (t := t) (Λ := 2 * coupling) ht
  have hP := pressure_derivative
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep ht
  have hdiff := hC.sub hP
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hfun : L = fun s => (2 * (N : ℝ)) *
      (coupledFreeEnergy
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s (2 * coupling) -
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
    funext s
    simp only [L, coupledFreeEnergy, coupledExcess, physicalLogQuadraticMoment]
    rw [show (2 : ℝ) * coupling / 2 = coupling by ring]
    calc
      logQuadraticMoment N β h q sk sim s coupling =
          (2 * (N : ℝ)) * (1 / (2 * (N : ℝ)) *
            logQuadraticMoment N β h q sk sim s coupling) := by field_simp [hNr]
      _ = _ := by ring
  have hLraw := hdiff.const_mul (2 * (N : ℝ))
  change HasDerivAt
      (fun s => (2 * (N : ℝ)) *
        (coupledFreeEnergy
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            s (2 * coupling) -
          interpolatedPressure
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s))
      _ t at hLraw
  rw [← hfun] at hLraw
  have hL : HasDerivAt L
      ((N : ℝ) * (β ^ 2 / 2) * (T + V - 2 * X)) t := by
    convert hLraw using 1 <;> simp [T, V, X] <;> ring
  have htime : deriv L t =
      (N : ℝ) * (β ^ 2 / 2) * (T + V - 2 * X) := hL.deriv
  have hcouplingDeriv : deriv
      (fun c => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t c)
      coupling = (N : ℝ) * T := by
    simpa [T] using deriv_logQuadraticMoment_coupling
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t coupling
  have hX : 0 ≤ X := coupledCrossMoment_nonneg
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t coupling
  have hleft : deriv L t - (β ^ 2 / 2) * ((N : ℝ) * T)
      ≤ (β ^ 2 / 2) * ((N : ℝ) * V) := by
    rw [htime]
    calc
      (N : ℝ) * (β ^ 2 / 2) * (T + V - 2 * X) -
          (β ^ 2 / 2) * ((N : ℝ) * T) =
          (β ^ 2 / 2) * ((N : ℝ) * V) -
            ((N : ℝ) * β ^ 2) * X := by ring
      _ ≤ (β ^ 2 / 2) * ((N : ℝ) * V) :=
        sub_le_self _ (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β)) hX)
  have hscaled : coupling * (N : ℝ) * V ≤ logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      t coupling := by
    refine' trans _ (MeasureTheory.integral_mono_of_nonneg _ _ _)
    case refine'_2 =>
      exact fun ω => coupling * N * gibbs_average_n_det N 2
        (H_t N β h q sk sim t ω) (centeredOverlapSq N q)
    · rw [MeasureTheory.integral_const_mul]
      rfl
    · exact Filter.Eventually.of_forall fun ω =>
        mul_nonneg (mul_nonneg (le_of_lt hcoupling) (Nat.cast_nonneg _))
          (by
            apply Finset.sum_nonneg
            intro σs _
            exact mul_nonneg (sq_nonneg _)
              (Finset.prod_nonneg fun l _ => gibbs_pmf_nonneg
                (N := N) (H := H_t N β h q sk sim t ω) (σ := σs l)))
    · have hi : Integrable (fun ω => gibbs_average_n N β h q sk sim 2 t
          (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ω) ℙ := by
        apply SpinGlass.integrable_gibbs_average_n
      refine hi.mono'
        (Real.measurable_log.comp_aemeasurable hi.aemeasurable).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
        simpa [tiltedReplicaPartition, tiltedReplicaPartitionDet, gibbs_average_n] using
          tiltedReplicaPartitionDet_one_le (N := N) (q := q)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
            (le_of_lt hcoupling)))]
      refine (Real.log_le_sub_one_of_pos ?_).trans (by linarith)
      simpa [tiltedReplicaPartition, tiltedReplicaPartitionDet, gibbs_average_n] using
        tiltedReplicaPartition_pos
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          t coupling ω
    · filter_upwards with ω
      exact scaled_centeredOverlapSq_le_log_gibbs_exp
        (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        coupling
  rw [hcouplingDeriv]
  refine hleft.trans ?_
  have hv : (N : ℝ) * V ≤
      logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t coupling / coupling := (le_div_iff₀ hcoupling).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  calc
    (β ^ 2 / 2) * ((N : ℝ) * V)
        ≤ (β ^ 2 / 2) *
            (logQuadraticMoment
              (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
              t coupling / coupling) :=
      mul_le_mul_of_nonneg_left hv (div_nonneg (sq_nonneg β) (by norm_num))
    _ = (β ^ 2 / (2 * coupling)) *
          logQuadraticMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t coupling := by field_simp

/-- Nonnegativity of the logarithmic quadratic moment for nonnegative exponential coupling. -/
lemma logQuadraticMoment_nonneg
    {t coupling : ℝ} (hcoupling : 0 ≤ coupling) :
    0 ≤ logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      t coupling := by
  rw [logQuadraticMoment]
  apply integral_nonneg
  intro ω
  apply Real.log_nonneg
  simpa [tiltedReplicaPartition, tiltedReplicaPartitionDet, gibbs_average_n] using
    tiltedReplicaPartitionDet_one_le
      (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
      hcoupling

/-- Coupling followed backwards from time `u` to the independent endpoint. -/
noncomputable def characteristicCoupling (coupling u s : ℝ) : ℝ :=
  coupling + (β ^ 2 / 2) * (u - s)

/-- The logarithmic moment restricted to the moving-coupling characteristic. -/
noncomputable def characteristicQuadraticMoment (coupling u s : ℝ) : ℝ :=
  logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    s (characteristicCoupling β coupling u s)

/-- The moving coupling stays at least as large as its terminal value. -/
lemma characteristicCoupling_ge
    {coupling u s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) u) :
    coupling ≤ characteristicCoupling β coupling u s := by
  unfold characteristicCoupling
  have hus : 0 ≤ u - s := sub_nonneg.mpr hs.2
  nlinarith [sq_nonneg β]

/-- A two-variable function is differentiable when its first partial derivative exists and its
second partial derivative exists nearby and is continuous. -/
private lemma hasFDerivAt_prod_of_continuous_snd
    (f g : ℝ × ℝ → ℝ) {t c a b : ℝ}
    (ht : HasDerivAt (fun x => f (x, c)) a t)
    (hc : ∀ p, HasDerivAt (fun y => f (p.1, y)) (g p) p.2)
    (hg : ContinuousAt g (t, c)) (hb : g (t, c) = b) :
    HasFDerivAt f
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, c) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have htO := hasFDerivAt_iff_isLittleO_nhds_zero.mp ht.hasFDerivAt
  have htbound := htO.bound (half_pos hε)
  have htbound' : ∀ᶠ z : ℝ × ℝ in 𝓝 0,
      ‖f (t + z.1, c) - f (t, c) - a * z.1‖ ≤ (ε / 2) * ‖z.1‖ := by
    have hlim : Filter.Tendsto (fun z : ℝ × ℝ => z.1) (𝓝 0) (𝓝 0) :=
      continuous_fst.continuousAt
    filter_upwards [hlim.eventually htbound] with z hz
    simpa [ContinuousLinearMap.toSpanSingleton_apply, mul_comm] using hz
  have hge : ∀ᶠ p in 𝓝 (t, c), ‖g p - b‖ < ε / 2 := by
    have hnear := (Metric.tendsto_nhds.mp hg.tendsto) (ε / 2) (half_pos hε)
    filter_upwards [hnear] with p hp
    simpa [Real.dist_eq, hb] using hp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hge
  have hsmall : ∀ᶠ z : ℝ × ℝ in 𝓝 0, ‖z‖ < δ := by
    exact Metric.eventually_nhds_iff.mpr ⟨δ, hδ, by
      intro z hz
      simpa [dist_zero_right] using hz⟩
  filter_upwards [htbound', hsmall] with z htime hzδ
  let x := t + z.1
  let y := c + z.2
  have hvertical : ‖f (x, y) - f (x, c) - b * z.2‖ ≤ (ε / 2) * ‖z.2‖ := by
    let k : ℝ → ℝ := fun w => f (x, w) - b * w
    have hkderiv (w : ℝ) : HasDerivAt k (g (x, w) - b) w := by
      change HasDerivAt ((fun y => f (x, y)) - fun y => b * y) (g (x, w) - b) w
      simpa only [id_eq, mul_one] using
        (hc (x, w)).sub ((hasDerivAt_id w).const_mul b)
    have hclose (w : ℝ) (hw : w ∈ Set.uIcc c y) : ‖g (x, w) - b‖ ≤ ε / 2 := by
      apply le_of_lt
      apply hball
      rw [Prod.dist_eq]
      have hx : dist x t ≤ ‖z‖ := by
        simp only [x, Real.dist_eq]
        simpa [Real.norm_eq_abs] using norm_fst_le z
      have hw' : dist w c ≤ ‖z‖ := by
        have : dist w c ≤ dist y c := by
          rcases le_total c y with hcy | hyc
          · rw [Set.uIcc_of_le hcy] at hw
            simp only [Real.dist_eq]
            rw [abs_of_nonneg (sub_nonneg.mpr hw.1),
              abs_of_nonneg (sub_nonneg.mpr hcy)]
            linarith [hw.2]
          · rw [Set.uIcc_of_ge hyc] at hw
            simp only [Real.dist_eq]
            rw [abs_of_nonpos (sub_nonpos.mpr hw.2),
              abs_of_nonpos (sub_nonpos.mpr hyc)]
            linarith [hw.1]
        calc
          dist w c ≤ dist y c := this
          _ = ‖z.2‖ := by simp [y, Real.norm_eq_abs]
          _ ≤ ‖z‖ := norm_snd_le z
      exact max_lt (lt_of_le_of_lt hx hzδ) (lt_of_le_of_lt hw' hzδ)
    have hmvt := (convex_uIcc c y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (hkderiv w).hasDerivWithinAt)
      (fun w hw => hclose w hw) Set.left_mem_uIcc Set.right_mem_uIcc
    convert hmvt using 1 <;> simp [k, x, y, Real.norm_eq_abs] <;> ring
  change ‖f ((t, c) + z) - f (t, c) -
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) z‖ ≤
      ε * ‖z‖
  have hsplit : f ((t, c) + z) - f (t, c) - (a * z.1 + b * z.2) =
      (f (x, y) - f (x, c) - b * z.2) +
      (f (t + z.1, c) - f (t, c) - a * z.1) := by
    change f (t + z.1, c + z.2) - f (t, c) - (a * z.1 + b * z.2) = _
    simp only [x, y]
    ring
  change ‖f ((t, c) + z) - f (t, c) - (a * z.1 + b * z.2)‖ ≤ ε * ‖z‖
  rw [hsplit]
  calc
    ‖(f (x, y) - f (x, c) - b * z.2) +
      (f (t + z.1, c) - f (t, c) - a * z.1)‖ ≤
        ‖f (x, y) - f (x, c) - b * z.2‖ +
          ‖f (t + z.1, c) - f (t, c) - a * z.1‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖z.2‖ + (ε / 2) * ‖z.1‖ := add_le_add hvertical htime
    _ ≤ ε * ‖z‖ := by
      nlinarith [norm_fst_le z, norm_snd_le z]

/-- Joint continuity of the coupling partial derivative of the logarithmic moment. -/
private lemma couplingPartial_continuous : Continuous (fun p : ℝ × ℝ =>
    (N : ℝ) * tiltedCenteredOverlapSq
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2) := by
  let G : ℝ × ℝ → Ω → ℝ := fun p ω => (N : ℝ) *
    tiltedCenteredOverlapSqDet (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω) p.2
  let B : ℝ := ∑ σs : ReplicaSpace N 2,
    (N : ℝ) * centeredOverlapSq N q σs
  have hHt_meas (r : ℝ) : Measurable (H_t
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) r) := by
    have hU := sk.hU.repr_measurable.const_smul (Real.sqrt r)
    have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - r))
    exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) r
  have hG_meas (p : ℝ × ℝ) : AEStronglyMeasurable (G p) ℙ := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G, tiltedCenteredOverlapSqDet]
    apply measurable_const.mul
    apply Measurable.div
    · unfold gibbs_average_n_det
      apply Finset.measurable_sum
      intro σs _
      apply measurable_const.mul
      apply Finset.measurable_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.measurable.comp
        (hHt_meas p.1)
    · unfold tiltedReplicaPartitionDet gibbs_average_n_det
      apply Finset.measurable_sum
      intro σs _
      apply measurable_const.mul
      apply Finset.measurable_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.measurable.comp
        (hHt_meas p.1)
  have hbound (p : ℝ × ℝ) (ω : Ω) : ‖G p ω‖ ≤ B := by
    simpa [G, B] using norm_tiltedLog_deriv_le
      (N := N) (q := q)
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω)
      p.2
  have hG_cont (ω : Ω) : Continuous (fun p => G p ω) := by
    have hHt : Continuous (fun p : ℝ × ℝ => H_t
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω) := by
      simp only [H_t, H_gauss]
      fun_prop
    dsimp only [G, tiltedCenteredOverlapSqDet]
    apply Continuous.mul continuous_const
    apply Continuous.div
    · unfold gibbs_average_n_det
      apply continuous_finset_sum
      intro σs _
      apply Continuous.mul
      · fun_prop
      · apply continuous_finset_prod
        intro l _
        exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.comp hHt
    · unfold tiltedReplicaPartitionDet gibbs_average_n_det
      apply continuous_finset_sum
      intro σs _
      apply Continuous.mul
      · fun_prop
      apply continuous_finset_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.comp hHt
    · intro p
      exact (tiltedReplicaPartitionDet_pos
        (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω)
        p.2).ne'
  have hint : Continuous (fun p => ∫ ω, G p ω ∂ℙ) := by
    rw [continuous_iff_continuousAt]
    intro p
    apply MeasureTheory.continuousAt_of_dominated
    · exact Filter.Eventually.of_forall hG_meas
    · exact Filter.Eventually.of_forall fun r => ae_of_all _ fun ω => hbound r ω
    · exact integrable_const B
    · exact ae_of_all _ fun ω => (hG_cont ω).continuousAt
  have heq : (fun p => ∫ ω, G p ω ∂ℙ) = fun p : ℝ × ℝ =>
      (N : ℝ) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2 := by
    funext p
    simp only [G, tiltedCenteredOverlapSq, MeasureTheory.integral_const_mul]
  rwa [heq] at hint

/-- The logarithmic moment is jointly differentiable in time and coupling away from the time
endpoints. -/
lemma logQuadraticMoment_differentiableAt_two_variables
    (hN : 0 < N) (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t coupling : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2)
      (t, coupling) := by
  obtain ⟨dt, htime⟩ := logQuadraticMoment_hasDerivAt_time
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep ht (coupling := coupling)
  let g : ℝ × ℝ → ℝ := fun p => (N : ℝ) * tiltedCenteredOverlapSq
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2
  have hcoupling (p : ℝ × ℝ) : HasDerivAt
      (fun y => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 y)
      (g p) p.2 := by
    simpa [g] using logQuadraticMoment_hasDerivAt_coupling_formula
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2
  exact (hasFDerivAt_prod_of_continuous_snd
    (f := fun p : ℝ × ℝ => logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2)
    (g := g) htime hcoupling (by
      simpa [g] using (couplingPartial_continuous
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)).continuousAt)
    rfl).differentiableAt

/-- Chain rule and PDE inequality along the characteristic.

Proof route: obtain `HasDerivAt` in both variables, note that the coupling path has derivative
`-β² / 2`, and use `HasDerivAt.scomp` or the two-variable Fréchet chain rule.  Apply
`logQuadraticMoment_differential_inequality`; then use `characteristicCoupling_ge` and
nonnegativity of the logarithmic moment to replace the moving denominator by `coupling`. -/
lemma characteristicQuadraticMoment_differential_inequality
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling u s : ℝ} (hcoupling : 0 < coupling)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) u) :
    ∃ d : ℝ,
      HasDerivAt
        (characteristicQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          coupling u) d s ∧
      d ≤ (β ^ 2 / (2 * coupling)) *
        characteristicQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          coupling u s := by
  let c : ℝ := characteristicCoupling β coupling u s
  let L : ℝ × ℝ → ℝ := fun p => logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 p.2
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_lt_of_le hs.2 hu.2⟩
  have hcge : coupling ≤ c := characteristicCoupling_ge
    (β := β) (coupling := coupling) (u := u) (s := s) ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hc : 0 < c := lt_of_lt_of_le hcoupling hcge
  obtain ⟨dt, hdt⟩ := logQuadraticMoment_hasDerivAt_time
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep hs01 (coupling := c)
  have hdc := logQuadraticMoment_hasDerivAt_coupling_formula
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s c
  have hL : DifferentiableAt ℝ L (s, c) := by
    simpa [L] using logQuadraticMoment_differentiableAt_two_variables
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hIndep hs01 (coupling := c)
  have hpath : HasDerivAt
      (fun r : ℝ => (r, characteristicCoupling β coupling u r))
      (1, -(β ^ 2 / 2)) s := by
    have hcpath := (hasDerivAt_const s coupling).add
      (((hasDerivAt_const s u).sub (hasDerivAt_id s)).const_mul (β ^ 2 / 2))
    have hcoeff : 0 + (β ^ 2 / 2) * (0 - 1) = -(β ^ 2 / 2) := by ring
    rw [hcoeff] at hcpath
    have hcpath' : HasDerivAt
        (fun r => characteristicCoupling β coupling u r) (-(β ^ 2 / 2)) s := by
      apply hcpath.congr_of_eventuallyEq
      filter_upwards with r
      simp [characteristicCoupling]
    exact (hasDerivAt_id s).prodMk hcpath'
  have hdiag := hL.hasFDerivAt.comp_hasDerivAt s hpath
  have htimeComp := hL.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s c))
  have hcouplingComp := hL.hasFDerivAt.comp_hasDerivAt c
    ((hasDerivAt_const c s).prodMk (hasDerivAt_id c))
  have htimeEval : fderiv ℝ L (s, c) (1, 0) = dt := by
    exact htimeComp.unique (by simpa [L, Function.comp_def] using hdt)
  have hcouplingEval : fderiv ℝ L (s, c) (0, 1) =
      (N : ℝ) * tiltedCenteredOverlapSq
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s c := by
    exact hcouplingComp.unique (by simpa [L, Function.comp_def] using hdc)
  let dc : ℝ := (N : ℝ) * tiltedCenteredOverlapSq
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s c
  let d : ℝ := dt - (β ^ 2 / 2) * dc
  have hdiag' : HasDerivAt
      (characteristicQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        coupling u) d s := by
    have heval : fderiv ℝ L (s, c) (1, -(β ^ 2 / 2)) = d := by
      rw [show (1, -(β ^ 2 / 2)) =
          ((1 : ℝ), (0 : ℝ)) + (-(β ^ 2 / 2)) • ((0 : ℝ), (1 : ℝ)) by
        ext <;> simp]
      rw [map_add, map_smul, htimeEval, hcouplingEval]
      simp only [smul_eq_mul, dc, d]
      ring
    rw [heval] at hdiag
    change HasDerivAt
      (L ∘ fun r => (r, characteristicCoupling β coupling u r)) d s
    simpa [c] using hdiag
  refine ⟨d, hdiag', ?_⟩
  have hpde := logQuadraticMoment_differential_inequality
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep hs01 hc
  have hdtDeriv : deriv (fun r => logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) r c) s = dt := hdt.deriv
  have hdcDeriv : deriv (fun z => logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s z) c = dc := by
    simpa [dc] using hdc.deriv
  rw [hdtDeriv, hdcDeriv] at hpde
  have hmoment : 0 ≤ logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s c :=
    logQuadraticMoment_nonneg
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (le_of_lt hc)
  have hcoef : β ^ 2 / (2 * c) ≤ β ^ 2 / (2 * coupling) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * c)
      (by positivity : 0 < 2 * coupling)]
    nlinarith [sq_nonneg β]
  dsimp only [d]
  refine hpde.trans ?_
  simpa [characteristicQuadraticMoment, c] using
    mul_le_mul_of_nonneg_right hcoef hmoment

/-- Continuity on the closed characteristic, including both endpoints.

Proof route: use the same dominated-convergence argument as
`interpolatedPressure_continuousOn`.  The finite replica sum is continuous jointly in time and
coupling.  On the compact characteristic its exponential tilt is uniformly bounded, which
provides an integrable disorder-independent dominator. -/
lemma characteristicQuadraticMoment_continuousOn
    {coupling u : ℝ} (hcoupling : 0 < coupling) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn
      (characteristicQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        coupling u) (Set.Icc (0 : ℝ) u) := by
  classical
  let K : ℝ := ∑ σs : ReplicaSpace N 2,
    Real.exp ((coupling + β ^ 2 / 2) * (N : ℝ) * centeredOverlapSq N q σs)
  unfold characteristicQuadraticMoment logQuadraticMoment
  apply MeasureTheory.continuousOn_of_dominated (bound := fun _ : Ω => K)
  · intro s _
    have hHt_meas : Measurable
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt s)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - s))
      exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s
    have hpart : Measurable fun w =>
        gibbs_average_n
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          2 s
          (fun σs => Real.exp
            (characteristicCoupling β coupling u s * (N : ℝ) *
              centeredOverlapSq N q σs)) w := by
      unfold gibbs_average_n gibbs_average_n_det
      apply Finset.measurable_sum
      intro σs _
      apply measurable_const.mul
      apply Finset.measurable_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.measurable.comp
        hHt_meas
    exact hpart.log.aestronglyMeasurable
  · intro s hs
    filter_upwards with w
    let c := characteristicCoupling β coupling u s
    have hc0 : 0 ≤ c :=
      le_trans (le_of_lt hcoupling)
        (characteristicCoupling_ge (β := β) (coupling := coupling) hs)
    have hcu : c ≤ coupling + β ^ 2 / 2 := by
      dsimp only [c, characteristicCoupling]
      have hus : u - s ≤ 1 := by linarith [hu.2, hs.1]
      nlinarith [sq_nonneg β]
    have hpart_one : 1 ≤
        gibbs_average_n
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          2 s (fun σs => Real.exp
            (c * (N : ℝ) * centeredOverlapSq N q σs)) w := by
      change 1 ≤ tiltedReplicaPartitionDet (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w) c
      exact tiltedReplicaPartitionDet_one_le (N := N) (q := q)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) s w) hc0
    have hpart_le :
        gibbs_average_n
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          2 s (fun σs => Real.exp
            (c * (N : ℝ) * centeredOverlapSq N q σs)) w ≤ K := by
      calc
        gibbs_average_n
              (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
              2 s (fun σs => Real.exp
                (c * (N : ℝ) * centeredOverlapSq N q σs)) w
            ≤ |gibbs_average_n
                (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
                2 s (fun σs => Real.exp
                  (c * (N : ℝ) * centeredOverlapSq N q σs)) w| := le_abs_self _
        _ ≤ ∑ σs : ReplicaSpace N 2,
              |Real.exp (c * (N : ℝ) * centeredOverlapSq N q σs)| :=
          abs_gibbs_average_n_le
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            (n := 2) (t := s)
            (f := fun σs => Real.exp
              (c * (N : ℝ) * centeredOverlapSq N q σs)) (w := w)
        _ ≤ K := by
          dsimp only [K]
          apply Finset.sum_le_sum
          intro σs _
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcu (Nat.cast_nonneg N)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hpart_one)]
    exact (Real.log_le_self (le_trans zero_le_one hpart_one)).trans hpart_le
  · exact integrable_const K
  · filter_upwards with w
    have hHt : Continuous fun s =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w := by
      simp only [H_t, H_gauss]
      fun_prop
    have hc : Continuous fun s => characteristicCoupling β coupling u s := by
      unfold characteristicCoupling
      fun_prop
    have hpart : Continuous fun s =>
        gibbs_average_n
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          2 s (fun σs => Real.exp
            (characteristicCoupling β coupling u s * (N : ℝ) *
              centeredOverlapSq N q σs)) w := by
      unfold gibbs_average_n gibbs_average_n_det
      apply continuous_finset_sum
      intro σs _
      apply Continuous.mul
      · exact (Real.continuous_exp.comp
          ((hc.mul continuous_const).mul continuous_const))
      · apply continuous_finset_prod
        intro l _
        exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.comp hHt
    exact (hpart.log fun s => (tiltedReplicaPartition_pos
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      s (characteristicCoupling β coupling u s) w).ne').continuousOn

/-- One-dimensional integrating-factor estimate with explicit endpoint hypotheses.

Proof route: multiply `f` by `exp (-a * s)`, use the product rule to show that the result has
nonpositive derivative on `Ioo 0 u`, apply monotonicity on `Icc 0 u`, and rearrange. -/
lemma gronwall_le_endpoint
    {f : ℝ → ℝ} {a u : ℝ} (hu : 0 ≤ u)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) u))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) u, ∃ d : ℝ,
      HasDerivAt f d s ∧ d ≤ a * f s) :
    f u ≤ Real.exp (a * u) * f 0 := by
  let g : ℝ → ℝ := fun s => Real.exp (-a * s) * f s
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) u) := by
    exact (Real.continuous_exp.comp
      ((continuous_const : Continuous (fun _ : ℝ => -a)).mul continuous_id)).continuousOn.mul hcont
  have hganti : AntitoneOn g (Set.Icc (0 : ℝ) u) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) u) hgcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hfd, hd⟩ := hderiv s hs
      have hinner : HasDerivAt (fun x : ℝ => -a * x) (-a) s := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-a)
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
          (Real.exp (-a * s) * (-a)) s :=
        (Real.hasDerivAt_exp (-a * s)).comp s hinner
      exact (hexp.mul hfd).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨d, hfd, hd⟩ := hderiv s hs
      have hgderiv : HasDerivAt g
          (Real.exp (-a * s) * (d - a * f s)) s := by
        have hinner : HasDerivAt (fun x : ℝ => -a * x) (-a) s := by
          simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (-a)
        have hexp : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
            (Real.exp (-a * s) * (-a)) s :=
          (Real.hasDerivAt_exp (-a * s)).comp s hinner
        change HasDerivAt ((fun x : ℝ => Real.exp (-a * x)) * f) _ s
        exact (hexp.mul hfd).congr_deriv (by ring)
      rw [hgderiv.deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (sub_nonpos.mpr hd)
  have hgu : g u ≤ g 0 := hganti (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  dsimp only [g] at hgu
  have hexp : 0 < Real.exp (a * u) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hgu hexp.le
  have hinv : Real.exp (a * u) * Real.exp (-a * u) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    f u = Real.exp (a * u) * (Real.exp (-a * u) * f u) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ Real.exp (a * u) * (Real.exp (-a * 0) * f 0) := hmul
    _ = Real.exp (a * u) * f 0 := by simp

/-- Characteristic (Grönwall) estimate for the logarithmic quadratic moment.

This theorem is now only the assembly of the characteristic regularity, its differential
inequality, and the generic integrating-factor lemma. -/
lemma logQuadraticMoment_characteristic
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling u : ℝ} (hcoupling : 0 < coupling)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        u coupling
      ≤ Real.exp (β ^ 2 * u / (2 * coupling)) *
        logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          0 ((2 * coupling + β ^ 2 * u) / 2) := by
  have hgronwall := gronwall_le_endpoint
    (f := characteristicQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      coupling u)
    (a := β ^ 2 / (2 * coupling)) hu.1
    (characteristicQuadraticMoment_continuousOn
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hcoupling hu)
    (fun s hs => characteristicQuadraticMoment_differential_inequality
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hIndep hcoupling hu hs)
  simp only [characteristicQuadraticMoment, characteristicCoupling] at hgronwall ⊢
  convert hgronwall using 1 <;> ring

/-- Positivity of the coupling scale in the improved region. -/
lemma lambdaStar_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    0 < lambdaStar β q := by
  have hk : 0 < kappa q := kappa_pos hq0 hq1
  have hβ : β ^ 2 < (kappa q)⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hk).2 (by simpa [rho] using hρ)
  simp only [lambdaStar]
  linarith

/-- The parameter `rho` is nonnegative on the physical range of `q`. -/
lemma rho_nonneg
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ rho β q := by
  exact mul_nonneg (sq_nonneg β) (le_of_lt (kappa_pos hq0 hq1))

/-- The coupling scale written in terms of the distance to the boundary `rho = 1`. -/
lemma lambdaStar_eq_one_sub_rho_div
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lambdaStar β q = (1 - rho β q) / (4 * kappa q) := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  simp only [lambdaStar, rho]
  field_simp [hk0]

/-- Algebraic identity for the moving coupling used in the quadratic interpolation. -/
lemma kappa_mul_movingCoupling
    (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    kappa q * (2 * lambdaStar β q + β ^ 2 * t) =
      (1 - rho β q) / 2 + rho β q * t := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  simp only [lambdaStar, rho]
  field_simp [hk0]
  ring

/-- The moving coupling remains in the range allowed by the endpoint estimate. -/
lemma movingCoupling_admissible
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    kappa q * (2 * lambdaStar β q + β ^ 2 * t) < 1 := by
  rw [kappa_mul_movingCoupling (β := β) (q := q) hq0 hq1]
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hmul : rho β q * t ≤ rho β q :=
    mul_le_of_le_one_right hρ0 ht.2
  linarith

/-- Quantitative slack in the endpoint admissibility inequality. -/
lemma movingCoupling_gap
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - rho β q) / 2 ≤
      1 - kappa q * (2 * lambdaStar β q + β ^ 2 * t) := by
  rw [kappa_mul_movingCoupling (β := β) (q := q) hq0 hq1]
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hmul : rho β q * t ≤ rho β q :=
    mul_le_of_le_one_right hρ0 ht.2
  linarith

/-- The moving coupling is strictly positive throughout the interpolation interval. -/
lemma movingCoupling_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 2 * lambdaStar β q + β ^ 2 * t := by
  have hlambda : 0 < lambdaStar β q :=
    lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
  have hβt : 0 ≤ β ^ 2 * t := mul_nonneg (sq_nonneg β) ht.1
  linarith

/-- Exact exponent appearing after applying Grönwall's inequality. -/
lemma beta_sq_div_two_lambdaStar
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    β ^ 2 / (2 * lambdaStar β q) =
      2 * rho β q / (1 - rho β q) := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  have hgap0 : 1 - rho β q ≠ 0 := ne_of_gt (sub_pos.mpr hρ)
  rw [lambdaStar_eq_one_sub_rho_div (β := β) (q := q) hq0 hq1]
  simp only [rho]
  field_simp [hk0, hgap0]
  ring

/-- The explicit constant in the quadratic estimate is positive in the improved region. -/
lemma quadraticConstant_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    0 < quadraticConstant β q := by
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hgap : 0 < 1 - rho β q := sub_pos.mpr hρ
  have hratio : 1 < 2 / (1 - rho β q) := by
    rw [lt_div_iff₀ hgap]
    linarith
  have hlog : 0 < Real.log (2 / (1 - rho β q)) := Real.log_pos hratio
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hlog

/-- Endpoint control for the moving coupling, already simplified to the uniform bound. -/
lemma endpoint_movingCoupling
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        0 ((2 * lambdaStar β q + β ^ 2 * t) / 2)
      ≤ (1 / 2) * Real.log (2 / (1 - rho β q)) := by
  let Λ : ℝ := 2 * lambdaStar β q + β ^ 2 * t
  have hΛ0 : 0 ≤ Λ := le_of_lt
    (movingCoupling_pos (β := β) (q := q) hq0 hq1 hρ ht)
  have hΛ : kappa q * Λ < 1 :=
    movingCoupling_admissible (β := β) (q := q) hq0 hq1 hρ ht
  have hend := endpoint_quadratic
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hq0 hq1 hfp hΛ0 hΛ
  have hgap : (1 - rho β q) / 2 ≤ 1 - kappa q * Λ :=
    movingCoupling_gap (β := β) (q := q) hq0 hq1 ht
  have hdenom : 0 < 1 - kappa q * Λ := sub_pos.mpr hΛ
  have hρgap : 0 < 1 - rho β q := sub_pos.mpr hρ
  have hratio : 1 / (1 - kappa q * Λ) ≤ 2 / (1 - rho β q) := by
    rw [div_le_div_iff₀ hdenom hρgap]
    linarith
  have hlog :
      Real.log (1 / (1 - kappa q * Λ)) ≤
        Real.log (2 / (1 - rho β q)) := by
    exact Real.log_le_log (by positivity) hratio
  exact hend.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- The moving-coupling estimate obtained by following the characteristic
`Λ(s) = 2 * coupling + β² * (t - s)` in the coupled interpolation. -/
lemma logQuadraticMoment_le_endpoint
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling t : ℝ} (hcoupling : 0 < coupling)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t coupling
      ≤ Real.exp (β ^ 2 * t / (2 * coupling)) *
        logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          0 ((2 * coupling + β ^ 2 * t) / 2) := by
  exact logQuadraticMoment_characteristic
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep hcoupling ht

/-
Proposition `quadratic-estimate` from the blueprint.
-/
theorem uniform_quadratic_coupling
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (lambdaStar β q)
      ≤ quadraticConstant β q := by
  -- Apply the lemma `logQuadraticMoment_le_endpoint` with coupling `lambdaStar β q`.
  have h_logQuadraticMoment_le_endpoint : logQuadraticMoment N β h q sk sim t (lambdaStar β q) ≤ Real.exp (β ^ 2 * t / (2 * lambdaStar β q)) * logQuadraticMoment N β h q sk sim 0 ((2 * lambdaStar β q + β ^ 2 * t) / 2) := by
    apply logQuadraticMoment_le_endpoint;
    · exact hN;
    · exact hIndep;
    · exact lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
    · exact ht;
  have h_logQuadraticMoment_le_endpoint : logQuadraticMoment N β h q sk sim 0 ((2 * lambdaStar β q + β ^ 2 * t) / 2) ≤ (1 / 2) * Real.log (2 / (1 - rho β q)) := by
    apply_rules [ endpoint_movingCoupling ];
  refine' le_trans ‹_› ( le_trans ( mul_le_mul_of_nonneg_left h_logQuadraticMoment_le_endpoint ( Real.exp_nonneg _ ) ) _ );
  -- Simplify the exponent using the fact that `β^2 / (2 * lambdaStar β q) = 2 * rho β q / (1 - rho β q)`.
  have h_exp_simplified : Real.exp (β ^ 2 * t / (2 * lambdaStar β q)) ≤ Real.exp (2 * rho β q / (1 - rho β q)) := by
    have h_exp_bound : β ^ 2 / (2 * lambdaStar β q) = 2 * rho β q / (1 - rho β q) :=
      beta_sq_div_two_lambdaStar (β := β) (q := q) hq0 hq1 hρ
    exact Real.exp_le_exp.mpr ( by rw [ ← h_exp_bound ] ; exact div_le_div_of_nonneg_right ( mul_le_of_le_one_right ( sq_nonneg _ ) ht.2 ) ( mul_nonneg zero_le_two ( by exact le_of_lt ( lambdaStar_pos ( hq0 := hq0 ) ( hq1 := hq1 ) ( hρ := hρ ) ) ) ) );
  refine' le_trans ( mul_le_mul_of_nonneg_right h_exp_simplified ( mul_nonneg ( by norm_num ) ( Real.log_nonneg _ ) ) ) _;
  · rw [le_div_iff₀] <;>
      linarith [rho_nonneg (β := β) (q := q) hq0 hq1]
  · unfold quadraticConstant; ring_nf; norm_num;

/-! ## Consequences -/

/-
Integrated finite-volume Jensen inequality for the centered overlap square.
-/
lemma scaled_overlapVariance_le_logQuadraticMoment
    (coupling : ℝ) (hcoupling : 0 ≤ coupling) (t : ℝ) :
    coupling * (N : ℝ) *
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
      ≤ logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          t coupling := by
  refine' trans _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
  case refine'_2 => exact fun ω => coupling * N * gibbs_average_n_det N 2 ( H_t N β h q sk sim t ω ) ( centeredOverlapSq N q );
  · rw [ MeasureTheory.integral_const_mul ] ; rfl;
  · refine' Filter.Eventually.of_forall fun ω => mul_nonneg ( mul_nonneg hcoupling ( Nat.cast_nonneg _ ) ) _;
    refine' Finset.sum_nonneg fun σs _ => mul_nonneg _ _;
    · exact sq_nonneg _;
    · exact Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Z_pos _ _ |> le_of_lt );
  · have h_integrable : Integrable (fun ω => gibbs_average_n N β h q sk sim 2 t (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ω) ℙ := by
      apply SpinGlass.integrable_gibbs_average_n;
    refine' h_integrable.mono' _ _;
    · exact Real.measurable_log.comp_aemeasurable h_integrable.aemeasurable |> fun h => h.aestronglyMeasurable;
    · filter_upwards [ ] with ω;
      rw [ Real.norm_eq_abs, abs_of_nonneg ( Real.log_nonneg _ ) ];
      · refine' le_trans ( Real.log_le_sub_one_of_pos _ ) _;
        · refine' Finset.sum_pos _ _;
          · intro σs _;
            refine' mul_pos ( Real.exp_pos _ ) ( Finset.prod_pos fun l _ => _ );
            exact div_pos ( Real.exp_pos _ ) ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ( Finset.univ_nonempty ) );
          · exact ⟨ fun _ => fun _ => Bool.true, Finset.mem_univ _ ⟩;
        · linarith;
      · have h_gibbs_exp : ∀ H : EnergySpace N, gibbs_average_n_det N 2 H (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ≥ 1 := by
          intro H
          have h_gibbs_exp : gibbs_average_n_det N 2 H (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ≥ Real.exp (gibbs_average_n_det N 2 H (fun σs => coupling * N * centeredOverlapSq N q σs)) := by
            apply gibbs_average_n_det_exp_jensen;
          refine' le_trans _ h_gibbs_exp;
          refine' Real.one_le_exp _;
          refine' Finset.sum_nonneg fun σs _ => mul_nonneg _ _;
          · exact mul_nonneg ( mul_nonneg hcoupling ( Nat.cast_nonneg _ ) ) ( sq_nonneg _ );
          · exact Finset.prod_nonneg fun _ _ => gibbs_pmf_nonneg N H _;
        exact h_gibbs_exp _;
  · filter_upwards [ ] with ω using scaled_centeredOverlapSq_le_log_gibbs_exp _ _ _ _

/-- Convexity of the log moment converts the quadratic exponential estimate into an overlap
second-moment estimate, uniformly along the smart path. -/
theorem overlap_concentration_uniform
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
      ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) := by
  have hlambda : 0 < lambdaStar β q :=
    lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hlambdaN : 0 < lambdaStar β q * (N : ℝ) := mul_pos hlambda hNreal
  have hJensen :=
    scaled_overlapVariance_le_logQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (coupling := lambdaStar β q) (le_of_lt hlambda) t
  have hquadratic :=
    uniform_quadratic_coupling
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hq1 hfp hρ hIndep ht
  apply (le_div_iff₀ hlambdaN).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hJensen.trans hquadratic


private lemma overlapVariance_continuous : Continuous (overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  let f : ReplicaFun N 2 := centeredOverlapSq N q
  let B : ℝ := ∑ σs : ReplicaSpace N 2, ‖f σs‖
  rw [continuous_iff_continuousAt]
  intro t
  apply MeasureTheory.continuousAt_of_dominated
  · filter_upwards with s
    exact (integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (n := 2) (t := s) (f := f)).aestronglyMeasurable
  · filter_upwards with s
    filter_upwards with w
    simpa [B, Real.norm_eq_abs] using
      (abs_gibbs_average_n_le
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        (n := 2) (t := s) (f := f) w)
  · exact integrable_const B
  · filter_upwards with w
    have hHt : Continuous (fun t =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [H_t, H_gauss]
      fun_prop
    have hg : Continuous (fun H : EnergySpace N =>
        gibbs_average_n_det (N := N) (n := 2) H f) := by
      simp only [gibbs_average_n_det]
      apply continuous_finset_sum
      intro σs _
      apply Continuous.mul continuous_const
      apply continuous_finset_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous
    exact (hg.comp hHt).continuousAt

private lemma free_energy_siteEnergy_eq (N : ℕ) (a : Fin N → ℝ) :
    free_energy_density (N := N) (siteEnergy N a) =
      (1 / (N : ℝ)) * ∑ i : Fin N, (Real.log 2 + Real.log (Real.cosh (a i))) := by
  rw [free_energy_density, Z_siteEnergy]
  rw [Real.log_prod]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ b : Bool, Real.exp (-(a i * boolSpin b))) =
        2 * Real.cosh (a i) by
      simp [boolSpin, Real.cosh_eq]
      ring]
    rw [Real.log_mul]
    · norm_num
    · exact ne_of_gt (Real.cosh_pos _)
  · intro i _
    exact ne_of_gt (Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty)

private lemma integrable_log_cosh_affine (h a : ℝ) : Integrable
    (fun z => Real.log (Real.cosh (h + a * z))) (gaussianReal 0 1) := by
  have hplus : Integrable (fun z => Real.exp (h + a * z)) (gaussianReal 0 1) := by
    simpa [Real.exp_add] using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).const_mul
        (Real.exp h)
  have hminus : Integrable (fun z => Real.exp (-(h + a * z))) (gaussianReal 0 1) := by
    have hi :=
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a)).const_mul
        (Real.exp (-h))
    simpa [Real.exp_add, mul_comm] using hi
  have hbound : Integrable
      (fun z => Real.exp (h + a * z) + Real.exp (-(h + a * z)))
      (gaussianReal 0 1) := hplus.add hminus
  apply hbound.mono'
  · have hc : Continuous (fun z => Real.cosh (h + a * z)) := by fun_prop
    exact (hc.log (fun z => ne_of_gt (Real.cosh_pos _))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh _))]
    calc
      Real.log (Real.cosh (h + a * z))
          ≤ Real.cosh (h + a * z) - 1 :=
        Real.log_le_sub_one_of_pos (Real.cosh_pos _)
      _ ≤ Real.exp (h + a * z) + Real.exp (-(h + a * z)) := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (h + a * z), Real.exp_pos (-(h + a * z))]

private lemma endpoint_pressure
    (hN : 0 < N) (hq0 : 0 ≤ q) :
    interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 =
      Real.log 2 + standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) := by
  letI : IsProbabilityMeasure (gaussianProduct N) := by
    rw [gaussianProduct]
    infer_instance
  let F : EnergySpace N → ℝ := fun H =>
    free_energy_density (N := N) (H + H_field (N := N) (h := h))
  have hFcont : Continuous F :=
    (SpinGlass.contDiff_free_energy_density (N := N)).continuous.comp
      (continuous_id.add continuous_const)
  have hHt0 (ω : Ω) :
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω =
        sim.V ω + H_field (N := N) (h := h) := by
    simp [H_t, H_gauss]
  have hrefLaw := referenceField_hasGaussianLaw N β q
  calc
    interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 =
        ∫ ω, F (sim.V ω) ∂ℙ := by
          rw [interpolatedPressure]
          apply integral_congr_ae
          filter_upwards with ω
          rw [hHt0]
    _ = ∫ H, F H ∂Measure.map sim.V ℙ := by
          rw [integral_map sim.hV.repr_measurable.aemeasurable
            hFcont.aestronglyMeasurable]
    _ = ∫ H, F H ∂Measure.map (referenceField N β q) (gaussianProduct N) := by
          rw [simpleDisorder_law_eq_reference N β q sim hN hq0]
    _ = ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
          rw [integral_map hrefLaw.aemeasurable hFcont.aestronglyMeasurable]
    _ = Real.log 2 + standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) := by
      let g : ℝ → ℝ := fun z =>
        Real.log (Real.cosh (h + β * Real.sqrt q * z))
      have hg : Integrable g (gaussianReal 0 1) :=
        integrable_log_cosh_affine h (β * Real.sqrt q)
      have hcoord (i : Fin N) : Integrable (fun z : Fin N → ℝ => g (z i))
          (gaussianProduct N) := by
        exact ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
          hg.aestronglyMeasurable).2 hg
      rw [show (∫ z, F (referenceField N β q z) ∂gaussianProduct N) =
          ∫ z, (1 / (N : ℝ)) * ∑ i : Fin N, (Real.log 2 + g (z i))
            ∂gaussianProduct N by
        apply integral_congr_ae
        filter_upwards with z
        simp only [F]
        change free_energy_density (N := N)
          (referenceField N β q z + magnetic_field_vector (N := N) h) = _
        rw [reference_add_field_eq_siteEnergy, free_energy_siteEnergy_eq]]
      rw [integral_const_mul]
      rw [show (∫ z : Fin N → ℝ, ∑ i : Fin N, (Real.log 2 + g (z i))
            ∂gaussianProduct N) =
          ∫ z : Fin N → ℝ, ((N : ℝ) * Real.log 2 + ∑ i : Fin N, g (z i))
            ∂gaussianProduct N by
        apply integral_congr_ae
        filter_upwards with z
        simp [Finset.sum_add_distrib]]
      rw [integral_add (integrable_const _)
        (integrable_finset_sum Finset.univ (fun i _ => hcoord i))]
      rw [integral_finset_sum Finset.univ (fun i _ => hcoord i)]
      simp only [integral_const, probReal_univ, one_smul]
      have hcoord_integral (i : Fin N) :
          (∫ z : Fin N → ℝ, g (z i) ∂gaussianProduct N) =
            ∫ z, g z ∂gaussianReal 0 1 :=
        integral_comp_eval hg.aestronglyMeasurable
      simp_rw [hcoord_integral]
      simp only [standardGaussianExpectation, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp
      ring

private lemma interpolatedPressure_continuousOn :
    ContinuousOn
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (Set.Icc (0 : ℝ) 1) := by
  let C : ℝ := (SpinGlass.hasModerateGrowth_free_energy_density N).C
  let B : Ω → ℝ := fun w => C *
    (1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖)
  apply MeasureTheory.continuousOn_of_dominated
  · intro t _
    have hHt_meas : Measurable
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      exact measurable_H_t_updated (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t
    exact ((SpinGlass.contDiff_free_energy_density (N := N)).continuous.measurable.comp
      hHt_meas).aestronglyMeasurable
  · intro t ht
    filter_upwards with w
    have hsqrtt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsqrtt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
    have hsqrt1t0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hsqrt1t1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [ht.1])
    have hnorm : ‖H_t
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      calc
        ‖H_t (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w‖
            ≤ ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ +
                ‖H_field (N := N) (h := h)‖ := by
              simp only [H_t, H_gauss]
              exact (norm_add_le
                ((Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w)
                (H_field (N := N) (h := h))).trans
                (by
                  gcongr
                  exact norm_add_le ((Real.sqrt t) • sk.U w)
                    ((Real.sqrt (1 - t)) • sim.V w))
        _ ≤ ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hsqrtt0, abs_of_nonneg hsqrt1t0]
              gcongr
              · exact mul_le_of_le_one_left (norm_nonneg _) hsqrtt1
              · exact mul_le_of_le_one_left (norm_nonneg _) hsqrt1t1
    have hgrowth :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).F_bound
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w)
    have hm : (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 := by rfl
    rw [hm, pow_one] at hgrowth
    change |free_energy_density (N := N)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w)| ≤
      C * (1 + ‖H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w‖) at hgrowth
    have hinside :
        1 + ‖H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w‖ ≤
        1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hinside
      (le_of_lt (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos)
    rw [Real.norm_eq_abs]
    exact hgrowth.trans (by simpa only [C] using hmul)
  · apply Integrable.const_mul
    exact (((integrable_const (1 : ℝ)).add
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)).add
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)).add
        (integrable_const _)
  · filter_upwards with w
    have hHt : Continuous (fun t =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [H_t, H_gauss]
      fun_prop
    exact ((SpinGlass.contDiff_free_energy_density (N := N)).continuous.comp hHt).continuousOn

/-- Public form of continuity of the interpolated pressure on the smart-path interval. -/
lemma interpolatedPressure_continuousOn_Icc :
    ContinuousOn
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (Set.Icc (0 : ℝ) 1) :=
  interpolatedPressure_continuousOn
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)

/-- Value of the interpolated pressure at the independent endpoint. -/
lemma interpolatedPressure_zero
    (hN : 0 < N) (hq0 : 0 ≤ q) :
    interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 =
      Real.log 2 + standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) :=
  endpoint_pressure
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hN hq0

/-- Integrated Guerra sum rule, including evaluation of the independent endpoint. -/
lemma replica_symmetric_sum_rule
    (hN : 0 < N) (hq0 : 0 ≤ q)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    MeasureTheory.IntegrableOn
        (overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (Set.Icc (0 : ℝ) 1) (MeasureTheory.volume : Measure ℝ) ∧
      rsPressure β h q -
          interpolatedPressure
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        = (β ^ 2 / 4) *
            ∫ t in Set.Icc (0 : ℝ) 1,
              overlapVariance
                (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  let P : ℝ → ℝ := interpolatedPressure
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let v : ℝ → ℝ := overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let g : ℝ → ℝ := fun t => (β ^ 2 / 4) * ((1 - q) ^ 2 - v t)
  have hvcont : Continuous v := overlapVariance_continuous
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hvint : IntegrableOn v (Set.Icc (0 : ℝ) 1) := hvcont.integrableOn_Icc
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hPcont : ContinuousOn P (Set.Icc (0 : ℝ) 1) :=
    interpolatedPressure_continuousOn
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt P (g t) t := by
    intro t ht
    exact pressure_derivative
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hIndep ht
  have hFTC : (∫ t in (0 : ℝ)..1, g t) = P 1 - P 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hPcont
      hderiv (hgcont.intervalIntegrable 0 1)
  have hinterval :
      (∫ t in (0 : ℝ)..1, g t) =
        (β ^ 2 / 4) * ((1 - q) ^ 2 - ∫ t in (0 : ℝ)..1, v t) := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 - q) ^ 2) volume 0 1)
      (hvcont.intervalIntegrable 0 1)]
    norm_num
  have hset :
      (∫ t in Set.Icc (0 : ℝ) 1, v t) = ∫ t in (0 : ℝ)..1, v t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le zero_le_one]
  have hP0 : P 0 = Real.log 2 + standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) :=
    endpoint_pressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hN hq0
  have hrel : P 1 - P 0 =
      (β ^ 2 / 4) * ((1 - q) ^ 2 - ∫ t in (0 : ℝ)..1, v t) :=
    hFTC.symm.trans hinterval
  refine ⟨hvint, ?_⟩
  rw [rsPressure, show interpolatedPressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 = P 1 by rfl,
    hset, ← hP0]
  linear_combination -hrel

/-- Generalized Latała bound for the finite-volume SK model.

At `t = 1`, `H_t` is the SK disorder plus the external-field vector.  The theorem gives both
the `O(1/N)` centered-overlap estimate and the corresponding replica-symmetric pressure error.
-/
theorem generalized_latala
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) ∧
      0 ≤ rsPressure β h q -
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 ∧
      rsPressure β h q -
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        ≤ (β ^ 2 * quadraticConstant β q) /
            (4 * lambdaStar β q * (N : ℝ)) := by
  let C : ℝ := quadraticConstant β q / (lambdaStar β q * (N : ℝ))
  have hoverlap :=
    overlap_concentration_uniform
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hq1 hfp hρ hIndep (t := (1 : ℝ)) (by simp)
  have hsum :=
    replica_symmetric_sum_rule
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hIndep
  have hvar0 : ∀ t : ℝ, 0 ≤ overlapVariance
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t :=
    fun t => overlapVariance_nonneg
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
  have hint0 : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1,
      overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t :=
    integral_nonneg hvar0
  have hpressure0 : 0 ≤ rsPressure β h q -
      interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 := by
    rw [hsum.2]
    exact mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num)) hint0
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ≤ C := by
    intro t ht
    simpa [C] using
      overlap_concentration_uniform
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hN hq0 hq1 hfp hρ hIndep ht
  have hconstInt : MeasureTheory.IntegrableOn
      (fun _ : ℝ => C) (Set.Icc (0 : ℝ) 1) (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.integrableOn_const (hs := by
      rw [Real.volume_Icc]
      finiteness)
  have hint_le :
      (∫ t in Set.Icc (0 : ℝ) 1,
          overlapVariance
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) ≤ C := by
    calc
      (∫ t in Set.Icc (0 : ℝ) 1,
          overlapVariance
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t)
          ≤ ∫ _t in Set.Icc (0 : ℝ) 1, C := by
              exact integral_mono_ae hsum.1 hconstInt
                (ae_restrict_of_forall_mem measurableSet_Icc hbound)
      _ = C := by
        norm_num [MeasureTheory.integral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  refine ⟨hoverlap, hpressure0, ?_⟩
  rw [hsum.2]
  calc
    (β ^ 2 / 4) *
          ∫ t in Set.Icc (0 : ℝ) 1,
            overlapVariance
              (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
        ≤ (β ^ 2 / 4) * C :=
          mul_le_mul_of_nonneg_left hint_le (div_nonneg (sq_nonneg β) (by norm_num))
    _ = (β ^ 2 * quadraticConstant β q) /
          (4 * lambdaStar β q * (N : ℝ)) := by
      simp only [C]
      ring

end GeneralizedLatala
end SpinGlass
