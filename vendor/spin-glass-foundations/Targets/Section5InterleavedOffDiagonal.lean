module

public import Targets.Section5InterleavedPressure
public import Targets.Section5InterleavedContinuity
public import Targets.Section5OffDiagonalAlgebra

@[expose] public section

/-!
# Off-diagonal interleaved interpolation

The constrained overlap `u` and the overlap `v` used by the trial path are
kept as separate parameters.  The Gaussian modes and trial covariance use
`v`, while the constrained pair and its external fields use `u`.  This is the
endpoint-safe form needed when a physical-neighbor path is transported across
an overlap breakpoint.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def section5InterleavedInterpolationOffDiagonal
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r j : ℕ) (t u v w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    mixedVectorListCascade n (section5TaggedMode r j (decide (v < 0)))
      (section5TaggedMass s r j)
      (section5TaggedPathVariance s β t |v| j w)
      (List.ofFn (section5Interleaving s r j))
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u)
      (fun _ => h) (fun _ => h)

theorem section5InterleavedInterpolationOffDiagonal_eq_reverse
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r j : ℕ) (t u v w : ℝ) :
    section5InterleavedInterpolationOffDiagonal n s β h U r j t u v w =
      (1 / (n : ℝ)) * ∫ ω,
      mixedVectorCascade n (section5ReverseMode s r j (decide (v < 0)))
        (section5ReverseMass s r j)
        (fun l => section5ReversePathVariance s β t v r j l w)
          (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u)
          ((k + 2) + (k + 3)) (fun _ => h) (fun _ => h) := by
  unfold section5InterleavedInterpolationOffDiagonal
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [mixedVectorListCascade_ofFn n (by omega)]
  rfl

theorem continuousOn_section5InterleavedInterpolationOffDiagonal
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    {t u v : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn
      (section5InterleavedInterpolationOffDiagonal n s β h Z r j t u v)
      (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_mixedConstrainedGaussian_path (S := Set.Icc (0 : ℝ) 1)
    hZ u isCompact_Icc (fun w => Real.sqrt (w * t)) (by fun_prop)
    (section5TaggedMode r j (decide (v < 0))) (section5TaggedMass s r j)
    (fun tag w => section5TaggedPathVariance s β t |v| j w tag)
    (List.ofFn (section5Interleaving s r j))
    (fun tag _ => (section5TaggedMass_mem_Icc s r hj tag).1)
    (fun tag _ => by cases tag <;> dsimp [section5TaggedPathVariance] <;> fun_prop)
    (fun tag _ w hw => section5TaggedPathVariance_nonneg s β ht hj hv hw.2 tag)
    (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  change ContinuousOn _ (Set.Icc (0 : ℝ) 1)
  apply H.const_mul

theorem section5InterleavedInterpolationOffDiagonal_one
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (j : ℕ)
    {t u v : ℝ} (ht : t ≤ 1) [Nonempty (AT.ConstrainedPair n u)] :
    section5InterleavedInterpolationOffDiagonal n s β h U r j t u v 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  unfold section5InterleavedInterpolationOffDiagonal constrainedPhi
  simp only [one_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  let F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    constrainedPairFieldBase n (Real.sqrt t • U ω) u
  have hF : CoupledGrowth F := constrainedPairFieldCascade_growth _ u
    (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) 0 0
  rw [section5InterleavedCascade_one_eq_fieldCascade n s β |v| ht hr0 hr j
    (decide (v < 0)) hF]
  let d := k + 2 - r
  let M := fun l => if l < d then s.m (k + 1 - l) else s.m (k + 1 - l) / 2
  let V := fun l => β ^ 2 * (s.q (k + 2 - l) - s.q (k + 1 - l))
  have hv : (fun l => (1 - t) * V l) = fun l => (Real.sqrt (1 - t)) ^ 2 * V l := by
    simp only [Real.sq_sqrt (sub_nonneg.mpr ht)]
  change coupledFieldCascade n M (fun l => (1 - t) * V l) d F (k + 2) (fun _ => h)
    (fun _ => h) = _
  rw [hv]
  have H := coupledFieldCascade_affine n M V d (k + 2) (Real.sqrt (1 - t)) h
    (Real.sqrt_nonneg _) F 0 0
  simp only [Pi.zero_apply, mul_zero, zero_add] at H
  rw [H]
  rw [show (fun x y => F (fun i => Real.sqrt (1 - t) * x i + h)
      (fun i => Real.sqrt (1 - t) * y i + h)) =
      constrainedBase n (U ω) h t u from funext fun x => funext fun y =>
        (constrainedBase_eq_pairFieldBase n (U ω) h t u x y).symm]
  exact congrFun (congrFun (coupledCascade_eq_fieldCascade n s β d (k + 2) _).symm 0) 0

noncomputable def section5InterleavedReplicaCovarianceOffDiagonal
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (j : ℕ) {hj : j ≤ k + 1}
    (t u v w : ℝ)
    (U : EnergySpace n) : ℝ :=
  pairCovarianceExpression β t u (section5InterleavedMassNat s r j)
    (section5InterleavedRho s r j |v|) (section5InterleavedCross s r hj v) (2 * k + 4)
    (fun p => mixedConstrainedReplica
      (section5ReverseMode s r j (decide (v < 0)))
      (section5ReverseMass s r j)
      (fun l => section5ReversePathVariance s β t v r j l w)
      (2 * k + 4 - p) (2 * k + 4 + 1 - (2 * k + 4 - p)) U u
      (fun _ => h) (fun _ => h))

noncomputable def section5InterleavedInterpolationOffDiagonalDerivative
    (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (r j : ℕ) (hj : j ≤ k + 1) (t u v w : ℝ) : ℝ :=
  ∫ ω, (1 / (n : ℝ)) *
    (t / 2 * (∑ i : sk.hU.ι,
      ((sk.hU.τ i : ℝ) *
        mixedConstrainedSecond (section5ReverseMode s r j (decide (v < 0)))
          (section5ReverseMass s r j)
          (fun l => section5ReversePathVariance s β t v r j l w)
          (2 * k + 4 + 1) (Real.sqrt (w * t) • sk.U ω)
          (sk.hU.w i) (sk.hU.w i) u (fun _ => h) (fun _ => h))) -
      t * ∑ l : Fin (2 * k + 4 + 1),
        (β ^ 2 *
          (section5InterleavedRho s r j |v|
            (2 * k + 4 - l + 1) -
            section5InterleavedRho s r j |v| (2 * k + 4 - l))) *
        mixedLevelVarianceD (Real.sqrt (w * t) • sk.U ω) u
          (section5ReverseMode s r j (decide (v < 0)))
          (section5ReverseMass s r j)
          (fun i => section5ReversePathVariance s β t v r j i w)
          (l : ℕ) (2 * k + 4 + 1 - ((l : ℕ) + 1))
          (section5ReversePathVariance s β t v r j (l : ℕ) w)
          (fun _ => h) (fun _ => h))

/- The derivative is the same genuine mixed replica expression as in the
diagonal construction, but with the covariance square completed at `(u,v)`.
The proof below is the existing finite-cascade differentiation argument with
the two overlap parameters kept distinct. -/
theorem hasDerivAt_section5InterleavedInterpolationOffDiagonal
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (r : ℕ) {j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u v w : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt
      (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v)
      (section5InterleavedInterpolationOffDiagonalDerivative s β h sk r j hj t u v w) w := by
  let N := 2 * k + 4 + 1
  let mode := section5ReverseMode s r j (decide (v < 0))
  let m := section5ReverseMass s r j
  let path := section5ReversePathVariance s β t v r j
  let ρ := section5InterleavedRho s r j |v|
  let a := fun l => β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l))
  let Z := fun ω => Real.sqrt (w * t) • sk.U ω
  let R := fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
    mixedConstrainedSecond mode m (fun l => path l w) N (Z ω)
      (sk.hU.w i) (sk.hU.w i) u (fun _ => h) (fun _ => h)
  let D := fun l : Fin N => fun ω => mixedLevelVarianceD (Z ω) u mode m
    (fun i => path i w) l (N - (l + 1)) (path l w) (fun _ => h) (fun _ => h)
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg s r hj
  have hv0 : ∀ l, 0 ≤ path l w := by
    intro l
    exact section5ReversePathVariance_nonneg s β ht hw.2.le r hj hv l
  have hpath (l : ℕ) (_hl : l < N) : HasDerivAt (path l)
      (-(t * a l)) w := by
    change HasDerivAt (fun z => section5TaggedPathVariance s β t |v| j z
      (section5ReverseTag s r j l)) (-(t * a l)) w
    have H := hasDerivAt_section5TaggedPathVariance s β t |v| r hj
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ w
    simpa only [path, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc] using H
  have hpathn : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ path l z := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    exact section5ReversePathVariance_nonneg s β ht hz.2.le r hj hv
  have hpathf (l : ℕ) (_hl : l < N) : 0 < path l w ∨
      (path l =ᶠ[𝓝 w] fun _ => 0) := by
    rcases section5TaggedPathVariance_pos_or_eq_zero s β ht hj hv hw.2
      (section5ReverseTag s r j l) with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := (hasDerivAt_mixedConstrainedGaussian_path_trace sk.hU
    (fun z => Real.sqrt (z * t)) u mode m path hm N
    (hasDerivAt_sqrt_mul_time ht.1 hw.1) hpath hpathn hpathf
    (fun _ => h) (fun _ => h)).const_mul (1 / (n : ℝ))
  have he (l : Fin N) : -(t * a l) *
      (if 0 < path l w then ∫ ω, D l ω else 0) =
      -(t * (a l * ∫ ω, D l ω)) := by
    have HH := section5TaggedPathVelocity_mul_ite s β r ht hj hv hw.2
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ (∫ ω, D l ω)
    simpa only [path, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc, neg_mul] using HH
  have hZ : Measurable Z := sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))
  have hiR : Integrable R := integrable_mixedConstrainedSecond_SK_trace hn β h sk hZ
    u mode m (fun l => path l w) hm hv0 N (fun _ => h) (fun _ => h)
  have hiD (l : Fin N) : Integrable (D l) := integrable_mixedLevelVarianceD_all_variances hn hZ
    u mode m (fun i => path i w) hm hv0 l (N - (l + 1)) (fun _ => h) (fun _ => h)
  have hiS : Integrable (fun ω => ∑ l : Fin N, a l * D l ω) :=
    integrable_finsetSum _ fun l _ => (hiD l).const_mul (a l)
  have hlin : (∫ ω, (1 / (n : ℝ)) * (t / 2 * R ω -
      t * ∑ l : Fin N, a l * D l ω)) =
      (1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) -
        t * ∑ l : Fin N, a l * ∫ ω, D l ω) := by
    rw [integral_const_mul, integral_sub (hiR.const_mul _) (hiS.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun l _ => (hiD l).const_mul (a l))]
    simp_rw [integral_const_mul]
  have hf : (fun z => (1 / (n : ℝ)) * ∫ ω, mixedVectorCascade n mode m
      (fun l => path l z) (constrainedPairFieldBase n
        (Real.sqrt (z * t) • sk.U ω) u) N (fun _ => h) (fun _ => h)) =
      (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v) := by
    funext z
    simpa only [N, mode, m, path,
      show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using
      (section5InterleavedInterpolationOffDiagonal_eq_reverse n s β h sk.U r j t u v z).symm
  have hsqrt : t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
    by_cases hz : t = 0
    · simp [hz]
    · have hs : Real.sqrt (w * t) ≠ 0 :=
        (Real.sqrt_pos.mpr (mul_pos hw.1 (lt_of_le_of_ne ht.1 (Ne.symm hz)))).ne'
      field_simp [hs]
      have hs' : Real.sqrt (t * w) ≠ 0 := by simpa only [mul_comm] using hs
      exact mul_inv_cancel₀ hs'
  rw [hf, hsqrt] at H
  change HasDerivAt _ ((1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) +
    ∑ l : Fin N, -(t * a l) * (if 0 < path l w then ∫ ω, D l ω else 0))) w at H
  simp_rw [he] at H
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← sub_eq_add_neg] at H
  apply H.congr_deriv
  rw [← hlin]
  simp only [section5InterleavedInterpolationOffDiagonalDerivative, R, D, a, mode, m,
    path, ρ, N, Z, show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega]

theorem section5InterleavedInterpolationOffDiagonal_zero_le_lambda
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) {t u v : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5InterleavedInterpolationOffDiagonal n s β h U r j t u v 0 ≤
      2 * Real.log 2 + section5InterleavedScalarV s β h r j t v ℓ - ℓ * u := by
  have H := mixedVectorListCascade_constrained_zero_le hn
    (show 0 < (k + 2) + (k + 3) by omega)
    (section5TaggedMode r j (decide (v < 0)))
    (section5TaggedMass s r j)
    (section5TaggedVariance s β t |v| j)
    (fun tag => (section5TaggedMass_mem_Icc s r hj tag).1)
    (section5TaggedVariance_nonneg s β ht hj hv)
    (section5Interleaving s r j) u ℓ h hatt
  change mixedVectorListCascade n (section5TaggedMode r j (decide (v < 0)))
      (section5TaggedMass s r j) (section5TaggedVariance s β t |v| j)
      (List.ofFn (section5Interleaving s r j))
      (constrainedPairFieldBase n (0 : EnergySpace n) u) (fun _ => h) (fun _ => h) ≤
    n * (2 * Real.log 2 + section5InterleavedScalarV s β h r j t v ℓ - ℓ * u) at H
  have Hoff := H
  rw [show section5InterleavedInterpolationOffDiagonal n s β h U r j t u v 0 =
      (1 / (n : ℝ)) *
        mixedVectorListCascade n (section5TaggedMode r j (decide (v < 0)))
          (section5TaggedMass s r j) (section5TaggedVariance s β t |v| j)
          (List.ofFn (section5Interleaving s r j))
          (constrainedPairFieldBase n (0 : EnergySpace n) u) (fun _ => h) (fun _ => h) by
    unfold section5InterleavedInterpolationOffDiagonal
    simp only [zero_mul, Real.sqrt_zero, zero_smul, one_mul,
      section5TaggedPathVariance_zero, integral_const, probReal_univ,
      smul_eq_mul]
  ]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left Hoff (one_div_nonneg.mpr hnR.le)
  simpa only [one_div, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul] using H'

theorem section5InterleavedInterpolationOffDiagonal_zero_le
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) {t u v : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolationOffDiagonal n s β h U r j t u v 0 ≤
      2 * Real.log 2 + section5InterleavedScalarV s β h r j t v 0 := by
  simpa only [zero_mul, sub_zero] using
    section5InterleavedInterpolationOffDiagonal_zero_le_lambda hn s β h U r hj ht hv hatt 0

/-! A finite-volume mismatch version of the covariance telescope.  The
terminal cross-overlap is allowed to be `v`, while the constrained overlap is
`u`; the endpoint discrepancy is the explicit linear term shown below. -/

theorem sum_pairField_increment_diagonal_mismatch (β u v : ℝ) (ρ c : ℕ → ℝ)
    (κ : ℕ) (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hc1 : c (κ + 1) = v) :
    (∑ l : Fin (κ + 1), 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))) =
      2 * β ^ 2 * (1 + u * v) := by
  let F := fun p => 2 * β ^ 2 * (ρ p + u * c p)
  have he (l : ℕ) : 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l))) =
      F (κ - l + 1) - F (κ - l) := by
    dsimp [F]
    ring
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun l => F (κ - l + 1) - F (κ - l)) (κ + 1)]
  have hrev := Finset.sum_range_reflect (fun p => F (p + 1) - F p) (κ + 1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [hrev, Finset.sum_range_sub]
  simp only [F, hρ0, hc0, hρ1, hc1]
  ring

theorem pairCovarianceExpression_eq_trace_sub_increment_heat_mismatch {n : ℕ}
    (β t u v : ℝ) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
    let B := fun i l => ∑ p, ∑ q, μ i p q *
      pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
        (c (κ - l + 1) - c (κ - l)) p.1 q.1
    let D := fun l => 2 * β ^ 2 *
      ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))
    t / 2 *
      ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
          m (κ - i) * (A i - A (i + 1))) -
        ∑ l : Fin (κ + 1),
          ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
            m (κ - l) * B l l)) =
      pairCovarianceExpression β t u m ρ c κ (fun p => μ (κ - p)) +
        t * β ^ 2 * u * (u - v) := by
  dsimp only
  let A := fun i => ∑ p, ∑ q, μ i p q * pairSKCovariance β p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
      (c (κ - l + 1) - c (κ - l)) p.1 q.1
  let D := fun l => 2 * β ^ 2 *
    ((ρ (κ - l + 1) - ρ (κ - l)) + u * (c (κ - l + 1) - c (κ - l)))
  change t / 2 *
    ((β ^ 2 * (1 + u ^ 2) - A 0 + ∑ i : Fin (κ + 1),
      m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1),
        ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
          m (κ - l) * B l l)) = _
  have H := replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A (fun _ => 1) D B
    (β ^ 2 * (1 + u ^ 2)) κ (by simpa using hmκ) (by simpa using hm0)
  simp only [one_mul] at H
  rw [H]
  have hd : (∑ l : Fin (κ + 1), D l) = 2 * β ^ 2 * (1 + u * v) :=
    sum_pairField_increment_diagonal_mismatch β u v ρ c κ hρ0 hc0 hρ1 hc1
  rw [hd]
  have hb (i : ℕ) : replicaHeatTail B (κ + 1) i =
      ∑ p, ∑ q, μ i p q *
        pairFieldCovariance β (ρ (κ + 1 - i)) (c (κ + 1 - i)) p.1 q.1 :=
    replicaHeatTail_pairField_increments β ρ c hρ0 hc0 κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance β (ρ (κ + 1 - i)) (c (κ + 1 - i)) p.1 q.1
  change t / 2 * (β ^ 2 * (1 + u ^ 2) - 2 * β ^ 2 * (1 + u * v) +
    ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ,
    replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (pairSKCovariance β a.1 b.1 -
          pairFieldCovariance β (ρ (p + 1)) (c (p + 1)) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [pairCovarianceExpression]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z)
      (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  ring

theorem mixedConstrained_trace_sub_heat_eq_covariance_mismatch
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}
    (hn : 0 < n) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (U : EnergySpace n) (t u v : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (M ρ c w : ℕ → ℝ) (κ : ℕ)
    (hm : ∀ i, 0 ≤ M (κ - i)) (hv : ∀ i, 0 ≤ w i)
    (hm0 : M 0 = 0) (hmκ : M κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = v)
    (hinc : ∀ l < κ + 1, c (κ - l + 1) - c (κ - l) =
      (ρ (κ - l + 1) - ρ (κ - l)) * (mode l).correlation)
    (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) *
      (t / 2 * (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
          mixedConstrainedSecond mode (fun i => M (κ - i)) w (κ + 1)
            U (sk.hU.w i) (sk.hU.w i) u x y) -
        t * ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
          mixedLevelVarianceD U u mode (fun i => M (κ - i)) w l
            (κ + 1 - (l + 1)) (w l) x y) =
      pairCovarianceExpression β t u M ρ c κ
        (fun p => mixedConstrainedReplica mode (fun i => M (κ - i)) w
          (κ - p) (κ + 1 - (κ - p)) U u x y) + t * β ^ 2 * u * (u - v) := by
  let m := fun i => M (κ - i)
  let μ := fun i => mixedConstrainedReplica mode m w i (κ + 1 - i) U u x y
  let A := fun i => mixedReplicaMoment mode m w i (κ + 1 - i) U u
    (fun p q => pairSKCovariance β p.1 q.1) x y
  let B := fun i l => mixedReplicaMoment mode m w i (κ + 1 - i) U u
    (fun p q => pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
      (c (κ - l + 1) - c (κ - l)) p.1 q.1) x y
  let D := fun l => 2 * β ^ 2 * ((ρ (κ - l + 1) - ρ (κ - l)) +
    u * (c (κ - l + 1) - c (κ - l)))
  have hheat (l : Fin (κ + 1)) :
      β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        mixedLevelVarianceD U u mode m w l (κ + 1 - (l + 1)) (w l) x y =
      (n : ℝ) / 2 * ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l) := by
    rw [mixedLevelVarianceD_overlap hn U u mode m w hm hv]
    have hsum : (l : ℕ) + (κ + 1 - (l + 1) + 1) = κ + 1 := by omega
    have hrest : κ + 1 - (l + 1) + 1 = κ + 1 - l := by omega
    have hK (p q : AT.ConstrainedPair n u) :
        pairFieldCovariance β (ρ (κ - l + 1) - ρ (κ - l))
          (c (κ - l + 1) - c (κ - l)) p.1 q.1 =
        (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) *
          pairFieldCovariance 1 1 (mode l).correlation p.1 q.1 := by
      rw [hinc l l.isLt]
      simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
      ring
    have hD : D l = (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l))) *
        (2 * (1 + (mode l).correlation * u)) := by
      dsimp [D]
      rw [hinc l l.isLt]
      ring
    have HH := mixedReplicaHeatExpression_const_mul mode m w l
      (κ + 1 - (l + 1) + 1) U u (2 * (1 + (mode l).correlation * u))
      (β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)))
      (fun p q => pairFieldCovariance 1 1 (mode l).correlation p.1 q.1) x y
    rw [← hD] at HH
    simp_rw [← hK] at HH
    rw [mixedReplicaHeatExpression, hsum, hrest] at HH
    change (D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) + m l * B l l = _ at HH
    rw [HH, hrest]
    ring
  rw [mixedConstrainedSecond_SK_trace hn β h sk U u mode m w hm hv]
  change (1 / (n : ℝ)) *
    (t / 2 * (n * (β ^ 2 * (1 + u ^ 2) - A 0 +
      ∑ i : Fin (κ + 1), m i * (A i - A (i + 1)))) -
      t * ∑ l : Fin (κ + 1), β ^ 2 * (ρ (κ - l + 1) - ρ (κ - l)) *
        mixedLevelVarianceD U u mode m w l (κ + 1 - (l + 1)) (w l) x y) = _
  simp_rw [hheat]
  rw [← Finset.mul_sum]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have H := pairCovarianceExpression_eq_trace_sub_increment_heat_mismatch β t u v M ρ c κ
    hm0 hmκ hρ0 hc0 hρ1 hc1 μ
  change t / 2 * ((β ^ 2 * (1 + u ^ 2) - A 0 +
    ∑ i : Fin (κ + 1), m i * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) = _ at H
  rw [← H]
  change (1 / (n : ℝ)) * (t / 2 * (n * _) - t * (n / 2 * _)) = _
  field_simp [hnR]

end SpinGlass.Targets
