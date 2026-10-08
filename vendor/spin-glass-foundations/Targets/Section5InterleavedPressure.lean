module

public import Targets.MixedReplicaPressure
public import Targets.Section5InterleavedScalarCore
public import Targets.Section5InterleavedCovariance
public import Targets.Section5InterleavedZero
public import Targets.MixedPathPressureFormula
public import Targets.Section5TaggedVelocity
public import Targets.Section5InterpolationPath

@[expose] public section

/-!
# The genuine mixed replica covariance bound for the tagged interpolation

The signed trial increments are matched to the actual reversed Gaussian
modes, including unchanged positive physical sharing. The covariance bound
uses the genuine split law; a varying-pressure derivative is not assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

/-- The genuine moving variance at a reversed tag; frozen physical levels
retain their original variance and Gaussian mode. -/
noncomputable def section5ReversePathVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j i : ℕ) (w : ℝ) : ℝ :=
  section5TaggedPathVariance s β t |u| j w (section5ReverseTag s r j i)

theorem section5ReversePathVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hw : w ≤ 1)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (i : ℕ) : 0 ≤ section5ReversePathVariance s β t u r j i w :=
  section5TaggedPathVariance_nonneg s β ht hj hu hw _

/-- Exact finite-list to bottom-up identification at every second time. -/
theorem section5InterleavedInterpolation_eq_reverse {Ω : Type*} [MeasureSpace Ω]
    {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r j : ℕ) (t u w : ℝ) :
    section5InterleavedInterpolation n s β h U r j t u w =
      (1 / (n : ℝ)) * ∫ ω,
        mixedVectorCascade n (section5ReverseMode s r j (decide (u < 0)))
          (section5ReverseMass s r j) (fun l => section5ReversePathVariance s β t u r j l w)
          (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u)
          ((k + 2) + (k + 3)) (fun _ => h) (fun _ => h) := by
  unfold section5InterleavedInterpolation
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  exact congrFun (congrFun (mixedVectorListCascade_ofFn n (by omega) _ _ _
    (section5Interleaving s r j) _) (fun _ => h)) (fun _ => h)

theorem section5ReverseMass_eq_massNat {k : ℕ} (s : RSBScheme k) (r j i : ℕ) :
    section5ReverseMass s r j i = section5InterleavedMassNat s r j (2 * k + 4 - i) := by
  have hi : 2 * k + 4 - i < (k + 2) + (k + 3) := by omega
  simp only [section5ReverseMass, section5ReverseTag, section5InterleavedMassNat,
    dif_pos hi, section5InterleavedMass]
  congr 2
  apply Fin.ext
  simp only
  omega

/-- Actual reversed modes, not a synthetic sharing cutoff, give the signed
velocity at every visited tagged level. -/
theorem section5ReverseMode_covariance_increment {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) (l : ℕ) (hl : l < 2 * k + 4 + 1) :
    section5InterleavedCross s r hj u (2 * k + 4 - l + 1) -
      section5InterleavedCross s r hj u (2 * k + 4 - l) =
      (section5InterleavedRho s r j |u| (2 * k + 4 - l + 1) -
        section5InterleavedRho s r j |u| (2 * k + 4 - l)) *
        (section5ReverseMode s r j (decide (u < 0)) l).correlation := by
  have hi : 2 * k + 4 - l < (k + 2) + (k + 3) := by omega
  have H := section5InterleavedCross_increment s r hj u ⟨2 * k + 4 - l, hi⟩
  have he : (⟨2 * k + 4 - l, hi⟩ : Fin ((k + 2) + (k + 3))) =
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  simpa only [section5ReverseMode, section5ReverseTag, he] using H

/-- The finite signed covariance inequality under the actual pointwise
mixed replica law. There is no hypothesized probability law or pressure
derivative in this statement. -/
theorem section5Interleaved_actualCovariance_le {k n : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (U : EnergySpace n) [Nonempty (AT.ConstrainedPair n u)]
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (x y : Fin n → ℝ) :
    pairCovarianceExpression β t u (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4)
      (fun p => mixedConstrainedReplica (section5ReverseMode s r j (decide (u < 0)))
        (section5ReverseMass s r j) v (2 * k + 4 - p)
        (2 * k + 4 + 1 - (2 * k + 4 - p)) U u x y) ≤
      -(2 * t * parisiCorrection s β) := by
  exact section5InterleavedCovarianceExpression_le s r hj0 hj β u ht _
    (fun _ _ p q => mixedConstrainedReplica_nonneg U u _ _ v
      (section5ReverseMass_nonneg s r hj) hv _ _ x y p q)
    (fun _ _ => sum_mixedConstrainedReplica U u _ _ v
      (section5ReverseMass_nonneg s r hj) hv _ _ x y)

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The same deterministic bound after the genuine disorder average. -/
theorem section5Interleaved_averagedCovariance_le {k n : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) [Nonempty (AT.ConstrainedPair n u)]
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (x y : Fin n → ℝ) :
    pairCovarianceExpression β t u (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4)
      (fun p => averagedMixedConstrainedReplica Z u
        (section5ReverseMode s r j (decide (u < 0))) (section5ReverseMass s r j) v
        (2 * k + 4 - p) (2 * k + 4 + 1 - (2 * k + 4 - p)) x y) ≤
      -(2 * t * parisiCorrection s β) := by
  exact section5InterleavedCovarianceExpression_le s r hj0 hj β u ht _
    (fun _ _ p q => averagedMixedConstrainedReplica_nonneg Z u _ _ v
      (section5ReverseMass_nonneg s r hj) hv _ _ x y p q)
    (fun _ _ => sum_averagedMixedConstrainedReplica hZ u _ _ v
      (section5ReverseMass_nonneg s r hj) hv _ _ x y)

/-- The normalized combination of the actual SK trace and actual tagged
level heat is bounded by the original deterministic correction. This includes
zero velocity levels and does not change their physical Gaussian mode. -/
theorem section5Interleaved_actualTraceHeat_le {k n : ℕ}
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (u : ℝ) {t : ℝ} (ht : 0 ≤ t) (U : EnergySpace n)
    [Nonempty (AT.ConstrainedPair n u)]
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (x y : Fin n → ℝ) :
    let mode := section5ReverseMode s r j (decide (u < 0))
    let m := section5ReverseMass s r j
    let ρ := section5InterleavedRho s r j |u|
    (1 / (n : ℝ)) *
      (t / 2 * (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
          mixedConstrainedSecond mode m v (2 * k + 4 + 1)
            U (sk.hU.w i) (sk.hU.w i) u x y) -
        t * ∑ l : Fin (2 * k + 4 + 1), β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l)) *
          mixedLevelVarianceD U u mode m v l
            (2 * k + 4 + 1 - (l + 1)) (v l) x y) ≤
      -(2 * t * parisiCorrection s β) := by
  dsimp only
  have hm : section5ReverseMass s r j = fun i => section5InterleavedMassNat s r j (2 * k + 4 - i) :=
    funext (section5ReverseMass_eq_massNat s r j)
  have hρ := section5InterleavedRho_endpoints s r hj0 hj |u|
  have hc := section5InterleavedCross_endpoints s r hj0 hj u
  have H := mixedConstrained_trace_sub_heat_eq_covariance hn β h sk U t u
    (section5ReverseMode s r j (decide (u < 0))) (section5InterleavedMassNat s r j)
    (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) v (2 * k + 4)
    (by intro i; rw [← section5ReverseMass_eq_massNat]; exact section5ReverseMass_nonneg s r hj i) hv
    (section5InterleavedMassNat_endpoints s r hj0 hj).1
    (section5InterleavedMassNat_endpoints s r hj0 hj).2 hρ.1 hc.1
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hρ.2)
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hc.2)
    (section5ReverseMode_covariance_increment s r hj u) x y
  rw [← hm] at H
  rw [H]
  exact section5Interleaved_actualCovariance_le s r hj0 hj β u ht U v hv x y

/-- The actual signed covariance expression at fixed disorder. Its replica
law is the genuine mixed law at the moving physical variances. -/
noncomputable def section5InterleavedReplicaCovariance {k n : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (t u w : ℝ)
    (U : EnergySpace n) : ℝ :=
  pairCovarianceExpression β t u (section5InterleavedMassNat s r j)
    (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4)
    (fun p => mixedConstrainedReplica (section5ReverseMode s r j (decide (u < 0)))
      (section5ReverseMass s r j) (fun l => section5ReversePathVariance s β t u r j l w)
      (2 * k + 4 - p) (2 * k + 4 + 1 - (2 * k + 4 - p)) U u (fun _ => h) (fun _ => h))

private theorem interleaved_sqrt_time_derivative_mul {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

/-- Genuine simultaneous differentiation of the actual tagged free energy.
The derivative is the covariance expression under the actual split law,
averaged over the original disorder. Every inactive zero variance has zero
velocity; no ordinary derivative at a clamped variance endpoint is asserted. -/
theorem hasDerivAt_section5InterleavedInterpolation_replica {k n : ℕ}
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (section5InterleavedInterpolation n s β h sk.U r j t u)
      (∫ ω, section5InterleavedReplicaCovariance s β h r hj t u w
        (Real.sqrt (w * t) • sk.U ω)) w := by
  let N := 2 * k + 4 + 1
  let mode := section5ReverseMode s r j (decide (u < 0))
  let m := section5ReverseMass s r j
  let v := section5ReversePathVariance s β t u r j
  let ρ := section5InterleavedRho s r j |u|
  let a := fun l => β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l))
  let Z := fun ω => Real.sqrt (w * t) • sk.U ω
  let R := fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
    mixedConstrainedSecond mode m (fun l => v l w) N (Z ω) (sk.hU.w i) (sk.hU.w i)
      u (fun _ => h) (fun _ => h)
  let D := fun (l : Fin N) ω => mixedLevelVarianceD (Z ω) u mode m (fun i => v i w)
    l (N - (l + 1)) (v l w) (fun _ => h) (fun _ => h)
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg s r hj
  have hv0 : ∀ l, 0 ≤ v l w := section5ReversePathVariance_nonneg s β ht hw.2.le r hj hu
  have hv (l : ℕ) (_hl : l < N) : HasDerivAt (v l) (-(t * a l)) w := by
    change HasDerivAt (fun z => section5TaggedPathVariance s β t |u| j z
      (section5ReverseTag s r j l)) (-(t * a l)) w
    have H := hasDerivAt_section5TaggedPathVariance s β t |u| r hj
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ w
    simpa only [v, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc] using H
  have hvn : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    exact section5ReversePathVariance_nonneg s β ht hz.2.le r hj hu
  have hvf (l : ℕ) (_hl : l < N) : 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0) := by
    rcases section5TaggedPathVariance_pos_or_eq_zero s β ht hj hu hw.2
      (section5ReverseTag s r j l) with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := (hasDerivAt_mixedConstrainedGaussian_path_trace sk.hU (fun z => Real.sqrt (z * t))
    u mode m v hm N (hasDerivAt_sqrt_mul_time ht.1 hw.1) hv hvn hvf
      (fun _ => h) (fun _ => h)).const_mul (1 / (n : ℝ))
  have hf : (fun z => (1 / (n : ℝ)) * ∫ ω, mixedVectorCascade n mode m (fun l => v l z)
      (constrainedPairFieldBase n (Real.sqrt (z * t) • sk.U ω) u) N (fun _ => h) (fun _ => h)) =
      section5InterleavedInterpolation n s β h sk.U r j t u := by
    funext z
    simpa only [N, show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using
      (section5InterleavedInterpolation_eq_reverse n s β h sk.U r j t u z).symm
  rw [hf, interleaved_sqrt_time_derivative_mul ht.1 hw.1] at H
  have he (l : Fin N) : -(t * a l) * (if 0 < v l w then ∫ ω, D l ω else 0) =
      -(t * (a l * ∫ ω, D l ω)) := by
    have HH := section5TaggedPathVelocity_mul_ite s β r ht hj hu hw.2
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ (∫ ω, D l ω)
    simpa only [v, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc, neg_mul] using HH
  change HasDerivAt _ ((1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) +
    ∑ l : Fin N, -(t * a l) * (if 0 < v l w then ∫ ω, D l ω else 0))) w at H
  simp_rw [he] at H
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← sub_eq_add_neg] at H
  have hZ : Measurable Z := sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))
  have hiR : Integrable R := integrable_mixedConstrainedSecond_SK_trace hn β h sk hZ
    u mode m (fun l => v l w) hm hv0 N (fun _ => h) (fun _ => h)
  have hiD (l : Fin N) : Integrable (D l) := integrable_mixedLevelVarianceD_all_variances hn hZ
    u mode m (fun i => v i w) hm hv0 l (N - (l + 1)) (fun _ => h) (fun _ => h)
  have hiS : Integrable (fun ω => ∑ l : Fin N, a l * D l ω) :=
    integrable_finsetSum _ fun l _ => (hiD l).const_mul (a l)
  have hlin : (∫ ω, (1 / (n : ℝ)) * (t / 2 * R ω - t * ∑ l : Fin N, a l * D l ω)) =
      (1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) - t * ∑ l : Fin N, a l * ∫ ω, D l ω) := by
    rw [integral_const_mul, integral_sub (hiR.const_mul _) (hiS.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun l _ => (hiD l).const_mul (a l))]
    simp_rw [integral_const_mul]
  apply H.congr_deriv
  rw [← hlin]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hmass : m = fun i => section5InterleavedMassNat s r j (2 * k + 4 - i) :=
    funext (section5ReverseMass_eq_massNat s r j)
  have hρ := section5InterleavedRho_endpoints s r hj0 hj |u|
  have hc := section5InterleavedCross_endpoints s r hj0 hj u
  have HP := mixedConstrained_trace_sub_heat_eq_covariance hn β h sk (Z ω) t u mode
    (section5InterleavedMassNat s r j) ρ (section5InterleavedCross s r hj u)
    (fun l => v l w) (2 * k + 4)
    (by intro i; rw [← section5ReverseMass_eq_massNat]; exact hm i) hv0
    (section5InterleavedMassNat_endpoints s r hj0 hj).1
    (section5InterleavedMassNat_endpoints s r hj0 hj).2 hρ.1 hc.1
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hρ.2)
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hc.2)
    (section5ReverseMode_covariance_increment s r hj u) (fun _ => h) (fun _ => h)
  rw [← hmass] at HP
  exact HP

/-- Integrability of the actual covariance expression is inherited from its
finite split moments, including every zero-variance face. -/
theorem integrable_section5InterleavedReplicaCovariance {k n : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w ≤ 1)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) [Nonempty (AT.ConstrainedPair n u)] :
    Integrable (fun ω => section5InterleavedReplicaCovariance s β h r hj t u w (Z ω)) := by
  unfold section5InterleavedReplicaCovariance pairCovarianceExpression
  apply Integrable.const_mul
  apply Integrable.add
  · exact integrable_const _
  · apply integrable_finsetSum
    intro p _
    apply Integrable.const_mul
    exact integrable_mixedReplicaMoment hZ u _ _ _ (section5ReverseMass_nonneg s r hj)
      (section5ReversePathVariance_nonneg s β ht hw r hj hu) _ _ _ (fun _ => h) (fun _ => h)

/-- The actual mixed pressure derivative has the original deterministic
upper bound, for either overlap sign and all zero masses/unchanged variances. -/
theorem deriv_section5InterleavedInterpolation_le {k n : ℕ}
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5InterleavedInterpolation n s β h sk.U r j t u) w ≤
      -(2 * t * parisiCorrection s β) := by
  rw [(hasDerivAt_section5InterleavedInterpolation_replica hn s β h sk r hj0 hj ht hu hw).deriv]
  have hi := integrable_section5InterleavedReplicaCovariance s β h r hj ht hu hw.2.le
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t)))
  calc
    _ ≤ ∫ _ : Ω, -(2 * t * parisiCorrection s β) := integral_mono hi (integrable_const _)
      (fun ω => section5Interleaved_actualCovariance_le s r hj0 hj β u ht.1
        (Real.sqrt (w * t) • sk.U ω) _
        (section5ReversePathVariance_nonneg s β ht hw.2.le r hj hu) (fun _ => h) (fun _ => h))
    _ = _ := by simp

end Disorder

end SpinGlass.Targets
