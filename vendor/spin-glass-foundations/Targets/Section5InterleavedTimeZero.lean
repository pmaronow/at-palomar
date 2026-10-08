module

public import Targets.Section5InterleavedZero
public import Targets.Section5LambdaUPrime
public import Targets.Section4StationarityTerminal
public import Targets.Section4TerminalFactors

@[expose] public section

/-!
# The actual interleaved scalar lambda family at physical time zero

All interpolating variances vanish at physical time zero, including those
with negative shared direction. The surviving physical cascade is precisely
the original scalar lambda family with a redundant zero-variance insertion.
The identification holds for every lambda and keeps both fields equal to `h`.
It supplies a genuine scalar witness for a later time/overlap neighborhood,
not merely a strict bound for the finite-size constrained free energy.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Deleting the inserted zero-variance independent level recovers the
original physical cascade. Its inserted mass and terminal function are
arbitrary; this identity needs no integrability or optimality assumption. -/
theorem section5FieldCascade_zero_eq_physical {n k : ℕ}
    (s : RSBScheme k) (β : ℝ) {r : ℕ} (hr : r ≤ k + 1) (m : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (fun i => section5Mass s r m (k + 2 - i))
      (fun i => section5Variance s β r (k + 2 - i) 0) (k + 3 - r) F (k + 3) =
      coupledFieldCascade n
        (fun i => if i < k + 2 - r then s.m (k + 1 - i) else s.m (k + 1 - i) / 2)
        (fun i => β ^ 2 * (s.q (k + 2 - i) - s.q (k + 1 - i)))
        (k + 2 - r) F (k + 2) := by
  let d := k + 2 - r
  let M := fun i => if i < d then s.m (k + 1 - i) else s.m (k + 1 - i) / 2
  let V := fun i => β ^ 2 * (s.q (k + 2 - i) - s.q (k + 1 - i))
  have hz (p : ℕ) : section5Variance s β r p 0 = section5FrozenVariance s β 0 r p := by
    simpa only [section5InterpolationVariance, mul_zero, zero_mul, add_zero] using
      (section5InterpolationVariance_zero s β 0 0 r p).symm
  have hd : k + 3 - r = d + 1 := by dsimp [d]; omega
  rw [hd, coupledFieldCascade_congr n _ _ (insertLevel M d m) (insertLevel V d 0)
    (d + 1) (k + 3)
    (fun i hi => section5Mass_eq_insert s hr m hi)
    (fun i hi => by
      rw [hz]
      simpa only [sub_zero, one_mul] using section5FrozenVariance_eq_insert s β 0 hr hi)]
  rw [show k + 3 = d + r + 1 by dsimp [d]; omega, coupledFieldCascade_insert_zero,
    show d + r = k + 2 by dsimp [d]; omega]

/-- The whole actual interleaved lambda family at physical time zero equals
the original zero-split baseline family. No assumption on the sign or trial
interval of `u` is required. Zero masses and zero physical gaps are allowed. -/
theorem section5InterleavedScalarV_time_zero {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r j : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj : j ≤ k + 1)
    (u ℓ : ℝ) :
    section5InterleavedScalarV s β h r j 0 u ℓ =
      section5V s β h r (s.m (r - 1)) 0 ℓ := by
  let F := fun x y : Fin 1 → ℝ => ∑ i, coupledSite ℓ (x i) (y i)
  have hF : CoupledGrowth F := coupledSite_sum_growth 1 ℓ
  have htag : section5TaggedVariance s β 0 |u| j =
      section5TaggedPathVariance s β 0 |u| j 1 := by
    funext tag
    cases tag <;> simp [section5TaggedPathVariance, section5TaggedVariance]
  have Hv := mixedVectorCascade_eq_sum 1
    (section5ReverseMode s r j (decide (u < 0))) (section5ReverseMass s r j)
    (fun i (_ : Unit) => section5ReverseVariance s β 0 |u| r j i)
    (section5ReverseMass_nonneg s r hj) (fun _ => continuous_const)
    ((k + 2) + (k + 3)) () ℓ (fun _ => h) (fun _ => h)
  have Hlist : mixedVectorListCascade 1 (section5TaggedMode r j (decide (u < 0)))
      (section5TaggedMass s r j) (section5TaggedVariance s β 0 |u| j)
    (List.ofFn (section5Interleaving s r j)) F (fun _ => h) (fun _ => h) =
      section5InterleavedScalarV s β h r j 0 u ℓ := by
    rw [mixedVectorListCascade_ofFn 1 (by omega)]
    change mixedVectorCascade 1 (section5ReverseMode s r j (decide (u < 0)))
      (section5ReverseMass s r j) (fun i => section5ReverseVariance s β 0 |u| r j i)
      F ((k + 2) + (k + 3)) (fun _ => h) (fun _ => h) =
      mixedScalarCascade (section5ReverseMode s r j (decide (u < 0)))
        (section5ReverseMass s r j) (fun i (_ : Unit) => section5ReverseVariance s β 0 |u| r j i)
        ((k + 2) + (k + 3)) () ℓ (h, h)
    simpa only [Fin.sum_univ_one, F] using Hv
  have Hphys := congrArg (fun G => G (fun _ => h) (fun _ => h))
    (section5InterleavedCascade_one_eq_fieldCascade 1 s β |u| (t := 0)
      (by norm_num) hr0 hr j (decide (u < 0)) hF)
  simp only [sub_zero, one_mul, F, Fin.sum_univ_one] at Hphys
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  have Hsplit := coupledFieldCascade_eq_sum 1
    (fun i => section5Mass s r (s.m (r - 1)) (k + 2 - i))
    (fun i => section5Variance s β r (k + 2 - i))
    (fun i => section5Mass_nonneg s hr (s.m_nonneg (by omega)) (by omega))
    (fun i => section5Variance_continuous s β r (k + 2 - i))
    (k + 3 - r) (k + 3) 0
    (fun i => section5Variance_nonneg s β hr (by omega) hzero) ℓ (fun _ => h) (fun _ => h)
  rw [section5FieldCascade_zero_eq_physical s β hr] at Hsplit
  simp only [Fin.sum_univ_one] at Hsplit
  change _ = section5V s β h r (s.m (r - 1)) 0 ℓ at Hsplit
  rw [← Hlist, htag]
  simpa only [F, Fin.sum_univ_one] using Hphys.trans Hsplit

/-- A time-zero scalar lambda witness with its actual baseline slope.
Unlike a constrained finite-size bound, this scalar expression can be used
in continuity arguments on real overlap parameters. -/
theorem section5InterleavedScalarV_time_zero_lambda_gain_Q {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj : j ≤ k + 1) (u : ℝ) :
    ∃ ℓ : ℝ, section5InterleavedScalarV s β h r j 0 u ℓ - ℓ * u ≤
      2 * parisiF s β (k + 2) h -
        (section4TVarianceQ s β h r (s.m (r - 1)) 0 - u) ^ 2 / 2 := by
  have hv : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  simpa only [section5InterleavedScalarV_time_zero s β h hr0 hr hj] using
    section5V_baseline_lambda_gain_Q s β h hr0 hr hv u

/-- Original fixed-level minimality identifies the time-zero scalar witness
centre with `q_r`. It is strict whenever `u ≠ q_r`, independently of system
size, disorder, trial interval, or overlap sign. -/
theorem section5InterleavedScalarV_time_zero_lambda_gain_of_min {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj : j ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (u : ℝ) :
    ∃ ℓ : ℝ, section5InterleavedScalarV s β h r j 0 u ℓ - ℓ * u ≤
      2 * parisiF s β (k + 2) h - (u - s.q r) ^ 2 / 2 := by
  obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q s β h hr0 hr hj u
  rw [section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ
    hm hleft hright hmin] at H
  exact ⟨ℓ, by nlinarith only [H]⟩

/-- The padded scalar family has the same original stationary time-zero
gain, including the final trial interval. Only the original scheme is
assumed minimizing; the padding is never required to be a minimizer. -/
theorem section5InterleavedScalarV_padded_time_zero_lambda_gain_of_min {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj : j ≤ k + 2) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (u : ℝ) :
    ∃ ℓ : ℝ, section5InterleavedScalarV s.padOneLast β h r j 0 u ℓ - ℓ * u ≤
      2 * parisiF s β (k + 2) h - (u - s.q r) ^ 2 / 2 := by
  obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
    s.padOneLast β h hr0 (by omega) (by omega : j ≤ k + 1 + 1) u
  rw [s.padOneLast_m (p := r - 1) (by omega),
    section4TVarianceQ_padOneLast s β h hr0 (by omega),
    show k + 1 + 2 = (k + 2) + 1 by omega, parisiF_padOneLast_succ,
    section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ
      hm hleft hright hmin] at H
  exact ⟨ℓ, by nlinarith only [H]⟩

end SpinGlass.Targets
