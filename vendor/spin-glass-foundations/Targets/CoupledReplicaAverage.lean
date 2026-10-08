module

public import Targets.CoupledReplicaWeights
public import Targets.CoupledMeasurability

@[expose] public section

/-!
# Averaging the actual split-level replica weights over disorder

The existing weights are defined at fixed disorder. Joint measurability in
disorder and both fields, together with their unit bound, justifies their
outer expectation and its finite-moment identities. No covariance formula for
the interpolation derivative is assumed or asserted in this module.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

abbrev ReplicaInput (n : ℕ) := EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ))

private theorem measurable_secondStepPi_disorder
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2)) (m v : ℝ) :
    Measurable (fun p : ReplicaInput n => parisiStepPi n m v (A p.1 p.2.1) p.2.2) := by
  have H := hA.comp (f := fun q : ReplicaInput n × (Fin n → ℝ) =>
    (q.1.1, (q.1.2.1, fun i => q.1.2.2 i + Real.sqrt v * q.2 i))) (by fun_prop)
  unfold parisiStepPi
  split_ifs
  · exact H.stronglyMeasurable.integral_prod_right'.measurable
  · exact (H.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable.log.const_mul _

/-- Joint measurability of one normalized mean, retaining the disorder. -/
theorem measurable_pairedSecondMean_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : ReplicaInput n => G p.1 p.2.1 p.2.2)) (m v : ℝ) :
    Measurable (fun p : ReplicaInput n => pairedSecondMean m v (A p.1) (G p.1) p.2.1 p.2.2) := by
  have hshift : Measurable (fun q : ReplicaInput n × (Fin n → ℝ) =>
      (q.1.1, (q.1.2.1, fun i => q.1.2.2 i + Real.sqrt v * q.2 i))) := by fun_prop
  have ha := hA.comp hshift
  have hg := hG.comp hshift
  simp only [pairedSecondMean, pairedTiltMean, tiltWeightPi]
  by_cases hm : m = 0
  · simp only [hm, if_true, mul_one]
    exact hg.stronglyMeasurable.integral_prod_right'.measurable
  · simp only [if_neg hm, ← mul_div_assoc, integral_div]
    exact (hg.mul (ha.const_mul m).exp).stronglyMeasurable.integral_prod_right'.measurable.div
      (ha.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable

private theorem measurable_pairedIndependentMean_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : ReplicaInput n => G p.1 p.2.1 p.2.2)) (m v : ℝ) :
    Measurable (fun p : ReplicaInput n => pairedIndependentMean m v (A p.1) (G p.1) p.2.1 p.2.2) := by
  have hswap : Measurable (fun p : ReplicaInput n => (p.1, (p.2.2, p.2.1))) := by fun_prop
  exact (measurable_pairedSecondMean_disorder
    (A := fun U y x => parisiStepPi n m v (A U x) y)
    (G := fun U y x => pairedSecondMean m v (A U) (G U) x y)
    ((measurable_secondStepPi_disorder hA m v).comp hswap)
    ((measurable_pairedSecondMean_disorder hA hG m v).comp hswap) m v).comp hswap

private theorem measurable_pairedSharedMean_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : ReplicaInput n => G p.1 p.2.1 p.2.2)) (m v : ℝ) :
    Measurable (fun p : ReplicaInput n => pairedSharedMean m v (A p.1) (G p.1) p.2.1 p.2.2) := by
  exact (measurable_pairedSecondMean_disorder
    (A := fun U x y => A U (x + y) y) (G := fun U x y => G U (x + y) y)
    (hA.comp (f := fun p : ReplicaInput n => (p.1, (p.2.1 + p.2.2, p.2.2))) (by fun_prop))
    (hG.comp (f := fun p : ReplicaInput n => (p.1, (p.2.1 + p.2.2, p.2.2))) (by fun_prop)) m v).comp
    (f := fun p : ReplicaInput n => (p.1, (p.2.1 - p.2.2, p.2.2))) (by fun_prop)

/-- The actual arbitrary-profile potential is jointly measurable in disorder
and fields. This reuses the existing independent/shared Gaussian-step rules. -/
theorem measurable_coupledFieldCascade_disorder
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2))
    (m v : ℕ → ℝ) (d j : ℕ) :
    Measurable (fun p : ReplicaInput n => coupledFieldCascade n m v d (A p.1) j p.2.1 p.2.2) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    simp only [coupledFieldCascade]
    split_ifs
    · exact measurable_independentStepPi_joint _ _ (A := fun U => coupledFieldCascade n m v d (A U) j) ih
    · exact measurable_sharedStepPi_joint _ _ (A := fun U => coupledFieldCascade n m v d (A U) j) ih

/-- Full normalized derivative transport is jointly measurable as a function
of the original disorder and both physical fields. -/
theorem measurable_coupledFieldCascadeD_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : ReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : ReplicaInput n => G p.1 p.2.1 p.2.2))
    (m v : ℕ → ℝ) (d j : ℕ) :
    Measurable (fun p : ReplicaInput n => coupledFieldCascadeD m v d (A p.1) (G p.1) j p.2.1 p.2.2) := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    have hF := measurable_coupledFieldCascade_disorder hA m v d j
    simp only [coupledFieldCascadeD]
    split_ifs
    · exact measurable_pairedIndependentMean_disorder
        (A := fun U => coupledFieldCascade n m v d (A U) j)
        (G := fun U => coupledFieldCascadeD m v d (A U) (G U) j) hF ih _ _
    · exact measurable_pairedSharedMean_disorder
        (A := fun U => coupledFieldCascade n m v d (A U) j)
        (G := fun U => coupledFieldCascadeD m v d (A U) (G U) j) hF ih _ _

private theorem measurable_constrainedPairFieldBase_disorder (u : ℝ) :
    Measurable (fun p : ReplicaInput n => constrainedPairFieldBase n p.1 u p.2.1 p.2.2) := by
  classical
  unfold constrainedPairFieldBase
  apply Measurable.log
  apply Finset.measurable_sum
  intro σ _
  apply Finset.measurable_sum
  intro τ _
  split_ifs <;> fun_prop

private theorem measurable_constrainedPairGibbs_disorder (u : ℝ) (p : AT.ConstrainedPair n u) :
    Measurable (fun z : ReplicaInput n => constrainedPairGibbs n z.1 u z.2.1 z.2.2 p) := by
  classical
  unfold constrainedPairGibbs AT.gtStateGibbs AT.gtStatePartition pairFieldPotential
  fun_prop

/-- Actual Gibbs coordinates are measurable jointly, not just at fixed disorder. -/
theorem measurable_constrainedCascadeGibbs_disorder (u : ℝ)
    (m v : ℕ → ℝ) (d j : ℕ) (p : AT.ConstrainedPair n u) :
    Measurable (fun z : ReplicaInput n => constrainedCascadeGibbs m v d j z.1 u z.2.1 z.2.2 p) :=
  measurable_coupledFieldCascadeD_disorder (measurable_constrainedPairFieldBase_disorder u)
    (A := fun U => constrainedPairFieldBase n U u)
    (G := fun U x y => constrainedPairGibbs n U u x y p)
    (measurable_constrainedPairGibbs_disorder u p) m v d j

/-- Joint measurability of the actual product-before-outer-transport replica law. -/
theorem measurable_constrainedCascadeReplica_disorder (u : ℝ)
    (m v : ℕ → ℝ) (d l r : ℕ) (p q : AT.ConstrainedPair n u) :
    Measurable (fun z : ReplicaInput n => constrainedCascadeReplica m v d l r z.1 u z.2.1 z.2.2 p q) :=
  measurable_coupledFieldCascadeD_disorder
    (A := fun U => coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
    (G := fun U x y => constrainedCascadeGibbs m v d l U u x y p *
      constrainedCascadeGibbs m v d l U u x y q)
    (measurable_coupledFieldCascade_disorder (A := fun U => constrainedPairFieldBase n U u)
      (measurable_constrainedPairFieldBase_disorder u) m v d l)
    ((measurable_constrainedCascadeGibbs_disorder u m v d l p).mul
      (measurable_constrainedCascadeGibbs_disorder u m v d l q))
    (fun i => m (l + i)) (fun i => v (l + i)) (d - l) r

section DisorderAverage

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Every actual replica weight is integrable over any measurable random
disorder, not only Gaussian disorder, by its proved unit bound. -/
theorem integrable_constrainedCascadeReplica {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    Integrable (fun ω => constrainedCascadeReplica m v d l r (Z ω) u x y p q) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_constrainedCascadeReplica_disorder u m v d l r p q).comp
      (hZ.prodMk (measurable_const.prodMk measurable_const))).aestronglyMeasurable
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, Function.comp_apply] using!
    (constrainedCascadeReplica_measurable_bound (Z ω) u m v hm hv d l r p q).2 x y

/-- The actual split-level replica law after taking the outer disorder average. -/
noncomputable def averagedConstrainedCascadeReplica (Z : Ω → EnergySpace n) (u : ℝ)
    (m v : ℕ → ℝ) (d l r : ℕ) (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) : ℝ :=
  ∫ ω, constrainedCascadeReplica m v d l r (Z ω) u x y p q

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem averagedConstrainedCascadeReplica_nonneg (Z : Ω → EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    0 ≤ averagedConstrainedCascadeReplica Z u m v d l r x y p q :=
  integral_nonneg (fun ω => constrainedCascadeReplica_nonneg (Z ω) u m v hm hv d l r x y p q)

/-- Outer expectation commutes with each finite replica moment because the
actual weights are integrable; no integrability is left as a hypothesis. -/
theorem averagedConstrainedCascadeReplica_moment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (f : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    (∫ ω, ∑ p, ∑ q, constrainedCascadeReplica m v d l r (Z ω) u x y p q * f p q) =
      ∑ p, ∑ q, averagedConstrainedCascadeReplica Z u m v d l r x y p q * f p q := by
  have hi (p q : AT.ConstrainedPair n u) :=
    (integrable_constrainedCascadeReplica hZ u m v hm hv d l r x y p q).mul_const (f p q)
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  simp only [integral_mul_const, averagedConstrainedCascadeReplica]

/-- The disorder-averaged weights are still normalized probabilities. -/
theorem sum_averagedConstrainedCascadeReplica {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    ∑ p, ∑ q, averagedConstrainedCascadeReplica Z u m v d l r x y p q = 1 := by
  have H := averagedConstrainedCascadeReplica_moment hZ u m v hm hv d l r x y (fun _ _ => 1)
  simp only [mul_one, sum_constrainedCascadeReplica _ u m v hm hv, integral_const,
    probReal_univ, smul_eq_mul] at H
  exact H.symm

/-- Averaging the actual transported product of disorder derivatives yields
the moment of the averaged split law. The product is formed at the split,
before either the remaining Gaussian levels or the disorder are averaged. -/
theorem averagedConstrainedCascadeReplica_disorder_product
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (V W : EnergySpace n)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n (Z ω) u) l)
      (fun x y => constrainedPairFieldCascadeDirection m v d l (Z ω) V u x y *
        constrainedPairFieldCascadeDirection m v d l (Z ω) W u x y) r x y) =
      ∑ p, ∑ q, averagedConstrainedCascadeReplica Z u m v d l r x y p q *
        (V p.1.1 + V p.1.2) * (W q.1.1 + W q.1.2) := by
  simp_rw [constrainedCascadeReplica_disorder_product _ V W u m v hm hv d l r,
    mul_assoc]
  exact averagedConstrainedCascadeReplica_moment hZ u m v hm hv d l r x y _

/-- The same averaged law represents transported products of actual spatial
derivatives, so disorder and heat contractions use identical replica weights. -/
theorem averagedConstrainedCascadeReplica_spatial_product
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (A B C D x y : Fin n → ℝ) :
    (∫ ω, coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n (Z ω) u) l)
      (fun x y => constrainedPairCascadeSpatialFirst m v d l (Z ω) u A B x y *
        constrainedPairCascadeSpatialFirst m v d l (Z ω) u C D x y) r x y) =
      ∑ p, ∑ q, averagedConstrainedCascadeReplica Z u m v d l r x y p q *
        pairFieldPotential n u A B p * pairFieldPotential n u C D q := by
  simp_rw [constrainedCascadeReplica_spatial_product _ u m v hm hv d l r,
    mul_assoc]
  exact averagedConstrainedCascadeReplica_moment hZ u m v hm hv d l r x y _

/-- Completing the SK covariance square survives both the nested transport
and disorder expectation because the actual split law has total mass one. -/
theorem averagedConstrainedCascadeReplica_covariance_completion
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (β q c : ℝ) :
    (∑ p, ∑ z, averagedConstrainedCascadeReplica Z u m v d l r x y p z *
      (pairSKCovariance β p.1 z.1 - pairFieldCovariance β q c p.1 z.1)) =
      (∑ p, ∑ z, averagedConstrainedCascadeReplica Z u m v d l r x y p z *
        pairCovarianceDefect β q c p.1 z.1) - β ^ 2 * (q ^ 2 + c ^ 2) := by
  simp_rw [pairCovariance_completion, mul_sub, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  rw [sum_averagedConstrainedCascadeReplica hZ u m v hm hv d l r x y, one_mul]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The actual averaged four-replica square remainder is nonnegative. -/
theorem averagedConstrainedCascadeReplica_defect_nonneg
    (Z : Ω → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (β q c : ℝ) :
    0 ≤ ∑ p, ∑ z, averagedConstrainedCascadeReplica Z u m v d l r x y p z *
      pairCovarianceDefect β q c p.1 z.1 := by
  exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun z _ => mul_nonneg
    (averagedConstrainedCascadeReplica_nonneg Z u m v hm hv d l r x y p z)
    (pairCovarianceDefect_nonneg β q c p.1 z.1)))

end DisorderAverage

end SpinGlass.Targets
