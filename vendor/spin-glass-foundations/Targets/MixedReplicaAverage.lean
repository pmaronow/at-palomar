module

public import Targets.MixedReplicaWeights
public import Targets.CoupledReplicaAverage

@[expose] public section

/-!
# Disorder averages of the actual mixed split-replica law

Joint measurability is proved for the same normalized kernels as the actual
mixed derivatives. Their unit bounds justify the disorder integral and all
finite moment interchanges; no Gaussian assumption on that disorder is needed.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

abbrev MixedReplicaInput (n : ℕ) := EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ))

private theorem measurable_gtVectorStep_disorder
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : MixedReplicaInput n => A p.1 p.2.1 p.2.2)) (m a b : ℝ) :
    Measurable (fun p : MixedReplicaInput n => AT.gtVectorStep n m a b (A p.1) p.2.1 p.2.2) := by
  have H := hA.comp (f := fun q : MixedReplicaInput n × (Fin n → ℝ) =>
    (q.1.1, (fun i => q.1.2.1 i + a * q.2 i, fun i => q.1.2.2 i + b * q.2 i))) (by fun_prop)
  unfold AT.gtVectorStep GeneralizedLatala.gaussianProduct
  split_ifs
  · exact H.stronglyMeasurable.integral_prod_right'.measurable
  · exact (H.const_mul m).exp.stronglyMeasurable.integral_prod_right'.measurable.log.const_mul _

theorem measurable_mixedVectorStep_disorder
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : MixedReplicaInput n => A p.1 p.2.1 p.2.2))
    (mode : Section5GaussianMode) (m v : ℝ) :
    Measurable (fun p : MixedReplicaInput n => mixedVectorStep n mode m v (A p.1) p.2.1 p.2.2) := by
  cases mode with
  | independent =>
    exact measurable_gtVectorStep_disorder
      (A := fun U => AT.gtVectorStep n m 0 (Real.sqrt v) (A U))
      (measurable_gtVectorStep_disorder hA m 0 (Real.sqrt v)) m (Real.sqrt v) 0
  | shared => exact measurable_gtVectorStep_disorder hA m (Real.sqrt v) (Real.sqrt v)
  | opposite => exact measurable_gtVectorStep_disorder hA m (Real.sqrt v) (-Real.sqrt v)

theorem measurable_mixedVectorCascade_disorder
    {A : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : MixedReplicaInput n => A p.1 p.2.1 p.2.2))
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ) :
    Measurable (fun p : MixedReplicaInput n => mixedVectorCascade n mode m v (A p.1) j p.2.1 p.2.2) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    exact measurable_mixedVectorStep_disorder (A := fun U => mixedVectorCascade n mode m v (A U) j)
      ih (mode j) (m j) (v j)

/-- Joint measurability reuses the checked normalized one-cut means at a
single level; opposite sharing is a fixed second-field substitution. -/
theorem measurable_mixedVectorMean_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : MixedReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : MixedReplicaInput n => G p.1 p.2.1 p.2.2))
    (mode : Section5GaussianMode) (m v : ℝ) :
    Measurable (fun p : MixedReplicaInput n =>
      mixedVectorMean n mode m v (A p.1) (G p.1) p.2.1 p.2.2) := by
  cases mode with
  | independent =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, Nat.zero_lt_succ, if_true] using
      measurable_coupledFieldCascadeD_disorder hA hG (fun _ => m) (fun _ => v) 1 1
  | shared =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, lt_self_iff_false, if_false] using
      measurable_coupledFieldCascadeD_disorder hA hG (fun _ => m) (fun _ => v) 0 1
  | opposite =>
    have hf : Measurable (fun p : MixedReplicaInput n => (p.1, (p.2.1, -p.2.2))) := by fun_prop
    have H := measurable_coupledFieldCascadeD_disorder
      (A := fun U x y => A U x (-y)) (G := fun U x y => G U x (-y))
      (hA.comp hf) (hG.comp hf) (fun _ => m) (fun _ => v) 0 1
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade,
      lt_self_iff_false, if_false, Function.comp_def] using H.comp hf

theorem measurable_mixedVectorCascadeD_disorder
    {A G : EnergySpace n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : Measurable (fun p : MixedReplicaInput n => A p.1 p.2.1 p.2.2))
    (hG : Measurable (fun p : MixedReplicaInput n => G p.1 p.2.1 p.2.2))
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ) :
    Measurable (fun p : MixedReplicaInput n =>
      mixedVectorCascadeD n mode m v (A p.1) (G p.1) j p.2.1 p.2.2) := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    exact measurable_mixedVectorMean_disorder
      (A := fun U => mixedVectorCascade n mode m v (A U) j)
      (G := fun U => mixedVectorCascadeD n mode m v (A U) (G U) j)
      (measurable_mixedVectorCascade_disorder hA mode m v j) ih (mode j) (m j) (v j)

private theorem measurable_terminal_disorder (u : ℝ) :
    Measurable (fun p : MixedReplicaInput n => constrainedPairFieldBase n p.1 u p.2.1 p.2.2) := by
  classical
  unfold constrainedPairFieldBase
  apply Measurable.log
  apply Finset.measurable_sum
  intro σ _
  apply Finset.measurable_sum
  intro τ _
  split_ifs <;> fun_prop

theorem measurable_mixedConstrainedGibbs_disorder (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j : ℕ) (p : AT.ConstrainedPair n u) :
    Measurable (fun z : MixedReplicaInput n => mixedConstrainedGibbs mode m v j z.1 u z.2.1 z.2.2 p) := by
  apply measurable_mixedVectorCascadeD_disorder (A := fun U => constrainedPairFieldBase n U u)
    (G := fun U x y => constrainedPairGibbs n U u x y p) (measurable_terminal_disorder u)
  exact measurable_constrainedCascadeGibbs_disorder u (fun _ => 0) (fun _ => 0) 0 0 p

theorem measurable_mixedConstrainedReplica_disorder (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ) (p q : AT.ConstrainedPair n u) :
    Measurable (fun z : MixedReplicaInput n => mixedConstrainedReplica mode m v l r z.1 u z.2.1 z.2.2 p q) :=
  measurable_mixedVectorCascadeD_disorder
    (A := fun U => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) l)
    (G := fun U x y => mixedConstrainedGibbs mode m v l U u x y p *
      mixedConstrainedGibbs mode m v l U u x y q)
    (measurable_mixedVectorCascade_disorder (A := fun U => constrainedPairFieldBase n U u)
      (measurable_terminal_disorder u) mode m v l)
    ((measurable_mixedConstrainedGibbs_disorder u mode m v l p).mul
      (measurable_mixedConstrainedGibbs_disorder u mode m v l q))
    (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i)) r

section DisorderAverage

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem integrable_mixedConstrainedReplica {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    Integrable (fun ω => mixedConstrainedReplica mode m v l r (Z ω) u x y p q) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_mixedConstrainedReplica_disorder u mode m v l r p q).comp
      (hZ.prodMk (measurable_const.prodMk measurable_const))).aestronglyMeasurable
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, Function.comp_apply] using!
    (mixedConstrainedReplica_measurable_bound (Z ω) u mode m v hm hv l r p q).2 x y

/-- The same actual split law averaged over the original disorder. -/
noncomputable def averagedMixedConstrainedReplica (Z : Ω → EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ)
    (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) : ℝ :=
  ∫ ω, mixedConstrainedReplica mode m v l r (Z ω) u x y p q

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem averagedMixedConstrainedReplica_nonneg (Z : Ω → EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    0 ≤ averagedMixedConstrainedReplica Z u mode m v l r x y p q :=
  integral_nonneg (fun ω => mixedConstrainedReplica_nonneg (Z ω) u mode m v hm hv l r x y p q)

theorem averagedMixedConstrainedReplica_moment {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ)
    (f : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    (∫ ω, ∑ p, ∑ q, mixedConstrainedReplica mode m v l r (Z ω) u x y p q * f p q) =
      ∑ p, ∑ q, averagedMixedConstrainedReplica Z u mode m v l r x y p q * f p q := by
  have hi (p q : AT.ConstrainedPair n u) :=
    (integrable_mixedConstrainedReplica hZ u mode m v hm hv l r x y p q).mul_const (f p q)
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  simp only [integral_mul_const, averagedMixedConstrainedReplica]

theorem sum_averagedMixedConstrainedReplica {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    ∑ p, ∑ q, averagedMixedConstrainedReplica Z u mode m v l r x y p q = 1 := by
  have H := averagedMixedConstrainedReplica_moment hZ u mode m v hm hv l r x y (fun _ _ => 1)
  simp only [mul_one, sum_mixedConstrainedReplica _ u mode m v hm hv, integral_const,
    probReal_univ, smul_eq_mul] at H
  exact H.symm

/-- Signed SK square completion under the actual averaged probability law. -/
theorem averagedMixedConstrainedReplica_covariance_completion
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (x y : Fin n → ℝ) (β q c : ℝ) :
    (∑ p, ∑ z, averagedMixedConstrainedReplica Z u mode m v l r x y p z *
      (pairSKCovariance β p.1 z.1 - pairFieldCovariance β q c p.1 z.1)) =
      (∑ p, ∑ z, averagedMixedConstrainedReplica Z u mode m v l r x y p z *
        pairCovarianceDefect β q c p.1 z.1) - β ^ 2 * (q ^ 2 + c ^ 2) := by
  simp_rw [pairCovariance_completion, mul_sub, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul]
  rw [sum_averagedMixedConstrainedReplica hZ u mode m v hm hv l r x y, one_mul]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem averagedMixedConstrainedReplica_defect_nonneg
    (Z : Ω → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (x y : Fin n → ℝ) (β q c : ℝ) :
    0 ≤ ∑ p, ∑ z, averagedMixedConstrainedReplica Z u mode m v l r x y p z *
      pairCovarianceDefect β q c p.1 z.1 := by
  exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun z _ => mul_nonneg
    (averagedMixedConstrainedReplica_nonneg Z u mode m v hm hv l r x y p z)
    (pairCovarianceDefect_nonneg β q c p.1 z.1)))

end DisorderAverage

end SpinGlass.Targets
