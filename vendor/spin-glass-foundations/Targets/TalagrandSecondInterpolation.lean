module

/-
# The two endpoints of Talagrand's second interpolation

We use canonical independent standard Gaussian coordinates with the combined
variances of Z + sqrt(1-w)y. For positive overlap in [q(r-1),q(r)], both fields
are shared below r and independent at/above r, exactly as in (5.5)--(5.7).

The endpoint equalities and bound below are unconditional checked results.
The nested-cascade covariance derivative inequality of Theorem 3.1 is still open.
-/
public import Targets.TalagrandSection5
public import Targets.CoupledReindex

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- A constrained terminal with disorder and physical fields specified separately. -/
noncomputable def constrainedPairFieldBase (n : ℕ) (U : EnergySpace n) (u : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, ∑ τ : Config n, if overlap n σ τ = u then
    Real.exp ((U σ + ∑ i, spin n σ i * x i) + (U τ + ∑ i, spin n τ i * y i)) else 0)

theorem constrainedBase_eq_pairFieldBase (n : ℕ) (U : EnergySpace n) (h t u : ℝ)
    (x y : Fin n → ℝ) :
    constrainedBase n U h t u x y =
      constrainedPairFieldBase n (Real.sqrt t • U) u
        (fun i => Real.sqrt (1 - t) * x i + h)
        (fun i => Real.sqrt (1 - t) * y i + h) := by
  simp only [constrainedBase, constrainedZ, guerraH, constrainedPairFieldBase, PiLp.smul_apply,
    smul_eq_mul]

@[simp] theorem constrainedPairFieldBase_zero (n : ℕ) (u : ℝ) :
    constrainedPairFieldBase n (0 : EnergySpace n) u = constrainedBase n 0 0 0 u := by
  funext x y
  simpa only [Real.sqrt_zero, Real.sqrt_one, zero_smul, zero_mul, one_mul,
    sub_zero, add_zero] using (constrainedBase_eq_pairFieldBase n 0 0 0 u x y).symm

variable {Ω : Type*} [MeasureSpace Ω]

/-- The Section 5 instance of eta(w), using combined Gaussian variances rather
than retaining redundant independent copies of Z and y. -/
noncomputable def section5Interpolation {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
      (fun j => section5InterpolationVariance s β t u r (k + 2 - j) w) (k + 3 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

/-- The disorder-free endpoint is the actual inserted-level field integral. -/
theorem section5Interpolation_zero [IsProbabilityMeasure (ℙ : Measure Ω)] {k : ℕ}
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u : ℝ) :
    section5Interpolation n s β h U r m t u 0 =
      section5FieldEndpoint n s β h u r m (t * (β ^ 2 * (s.q r - u))) := by
  simp only [section5Interpolation, zero_mul, Real.sqrt_zero, zero_smul,
    constrainedPairFieldBase_zero, section5InterpolationVariance_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    section5FieldEndpoint, one_div]

theorem section5Mass_eq_insert {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) (m : ℝ) {j : ℕ} (hj : j < k + 3) :
    section5Mass s r m (k + 2 - j) =
      insertLevel (fun i => if i < k + 2 - r then s.m (k + 1 - i)
        else s.m (k + 1 - i) / 2) (k + 2 - r) m j := by
  unfold section5Mass insertLevel
  by_cases hlt : j < k + 2 - r
  · have hp : ¬k + 2 - j < r := by omega
    have hp' : k + 2 - j ≠ r := by omega
    simp only [if_pos hlt, if_neg hp, if_neg hp']
    congr 1
    omega
  · by_cases heq : j = k + 2 - r
    · have hp : k + 2 - j = r := by omega
      simp only [hp, lt_self_iff_false, if_false, if_true, if_neg hlt, if_pos heq]
    · have hp : k + 2 - j < r := by omega
      have hi : ¬j - 1 < k + 2 - r := by omega
      simp only [if_pos hp, if_neg hlt, if_neg heq, if_neg hi]
      congr 2
      omega

theorem section5FrozenVariance_eq_insert {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    {j : ℕ} (hj : j < k + 3) :
    section5FrozenVariance s β t r (k + 2 - j) =
      insertLevel (fun i => (1 - t) * (β ^ 2 *
        (s.q (k + 2 - i) - s.q (k + 1 - i)))) (k + 2 - r) 0 j := by
  unfold section5FrozenVariance insertLevel
  by_cases hlt : j < k + 2 - r
  · have hp : ¬k + 2 - j < r := by omega
    have hp' : k + 2 - j ≠ r := by omega
    simp only [if_pos hlt, if_neg hp, if_neg hp']
    have hi : k + 2 - j - 1 = k + 1 - j := by omega
    rw [hi]
  · by_cases heq : j = k + 2 - r
    · have hp : k + 2 - j = r := by omega
      simp only [hp, lt_self_iff_false, if_false, if_true, if_neg hlt, if_pos heq, mul_zero]
    · have hp : k + 2 - j < r := by omega
      have hi : k + 2 - (j - 1) = k + 2 - j + 1 := by omega
      have hi' : k + 1 - (j - 1) = k + 2 - j := by omega
      simp only [if_pos hp, if_neg hlt, if_neg heq, hi, hi']

/-- Pointwise form of (5.8). The new level disappears at w=1, and the field
rescaling recovers the original constrained cascade exactly. -/
theorem section5Cascade_one {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (U : EnergySpace n) {r : ℕ} (_hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    coupledFieldCascade n (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5FrozenVariance s β t r (k + 2 - j)) (k + 3 - r)
        (constrainedPairFieldBase n (Real.sqrt t • U) u) (k + 3) (fun _ => h) (fun _ => h) =
      coupledCascade n s β (k + 2 - r) (constrainedBase n U h t u) (k + 2) 0 0 := by
  let d := k + 2 - r
  let masses := fun j => if j < d then s.m (k + 1 - j) else s.m (k + 1 - j) / 2
  let vars := fun j => β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))
  have hd : k + 3 - r = d + 1 := by dsimp [d]; omega
  have hdepth : k + 3 = d + r + 1 := by dsimp [d]; omega
  have hdepth' : d + r = k + 2 := by dsimp [d]; omega
  rw [hd, coupledFieldCascade_congr n _ _ (insertLevel masses d m)
    (insertLevel (fun j => (1 - t) * vars j) d 0) (d + 1) (k + 3)
    (fun j hj => section5Mass_eq_insert s hr m hj)
    (fun j hj => section5FrozenVariance_eq_insert s β t hr hj)]
  rw [hdepth, coupledFieldCascade_insert_zero, hdepth']
  have hv : (fun j => (1 - t) * vars j) = fun j => (Real.sqrt (1 - t)) ^ 2 * vars j := by
    simp only [Real.sq_sqrt (sub_nonneg.mpr ht)]
  rw [hv]
  have H := coupledFieldCascade_affine n masses vars d (k + 2)
    (Real.sqrt (1 - t)) h (Real.sqrt_nonneg _) (constrainedPairFieldBase n (Real.sqrt t • U) u)
    0 0
  simp only [Pi.zero_apply, mul_zero, zero_add] at H
  rw [H]
  rw [show (fun x y => constrainedPairFieldBase n (Real.sqrt t • U) u
      (fun i => Real.sqrt (1 - t) * x i + h) (fun i => Real.sqrt (1 - t) * y i + h)) =
      constrainedBase n U h t u from funext fun x => funext fun y =>
        (constrainedBase_eq_pairFieldBase n U h t u x y).symm]
  exact congrFun (congrFun (coupledCascade_eq_fieldCascade n s β d (k + 2) _).symm 0) 0

/-- Talagrand (5.8), including equality after averaging over the disorder. -/
theorem section5Interpolation_one {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    section5Interpolation n s β h U r m t u 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  simp only [section5Interpolation, section5InterpolationVariance_one, one_mul,
    section5Cascade_one s β h _ hr0 hr m u ht, constrainedPhi]

/-- Talagrand (5.17) for the actual canonical second interpolation, for the
positive-overlap left-interval construction. No unknown derivative bound is assumed. -/
theorem section5Interpolation_zero_le [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (_hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5Interpolation n s β h U r m t u 0 ≤
      2 * Real.log 2 + section5V s β h r m (t * (β ^ 2 * (s.q r - u))) ℓ - ℓ * u := by
  rw [section5Interpolation_zero]
  exact section5FieldEndpoint_le hn s β h u hr hm (section5SplitVariance_mem s β ht hu) hu' ℓ

end SpinGlass.Targets
