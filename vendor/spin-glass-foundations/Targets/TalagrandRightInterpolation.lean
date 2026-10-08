module

public import Targets.TalagrandSecondInterpolation
public import Targets.CoupledSharedInsertion
public import Targets.TalagrandSection5Zero

@[expose] public section

/-!
# The right-interval dual construction in Talagrand Section 5

The last paragraph of Section 4 splits `[q_r,q_(r+1)]`, assigning scalar mass
`m` to its lower part and `m_r` to its upper part. Section 5 invokes this dual
construction for Propositions 5.2 and 5.6. Here the inserted paired mass is
`m/2`, its frozen variance is zero, and its trial field is shared. Thus the
independent-depth cutoff stays unchanged when this level is deleted at time one.

Only the concrete coefficients and cascade endpoints are asserted here, not
the missing second-interpolation derivative bound or either proposition.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The right-interval overlap sequence inserts `u` after `q_r`. -/
noncomputable def section5RightRho {k : ℕ} (s : RSBScheme k) (r : ℕ) (u : ℝ) : ℕ → ℝ :=
  section5Rho s (r + 1) u

/-- Actual paired masses. The new shared level has mass `m/2`. -/
noncomputable def section5RightMass {k : ℕ} (s : RSBScheme k) (r : ℕ) (m : ℝ) : ℕ → ℝ :=
  section5Mass s r (m / 2)

/-- At time zero, the split interval has shared variance `v`, followed in
forward order by independent variance `a-v`. -/
def section5RightVariance {k : ℕ} (s : RSBScheme k) (β : ℝ) (r p : ℕ) (v : ℝ) : ℝ :=
  if p < r then β ^ 2 * (s.q (p + 1) - s.q p)
  else if p = r then v
  else if p = r + 1 then β ^ 2 * (s.q (r + 1) - s.q r) - v
  else β ^ 2 * (s.q p - s.q (p - 1))

/-- The frozen fields are those of the original coupled cascade, with a zero
increment inserted at `r`; only the trial sharing cutoff has changed. -/
noncomputable def section5RightInterpolationVariance {k : ℕ} (s : RSBScheme k) (β t u : ℝ)
    (r p : ℕ) (w : ℝ) : ℝ :=
  section5FrozenVariance s β t r p +
    (1 - w) * t * β ^ 2 * (section5RightRho s r u (p + 1) - section5RightRho s r u p)

theorem section5RightMass_nonneg {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) {p : ℕ} (hp : p ≤ k + 2) :
    0 ≤ section5RightMass s r m p :=
  section5Mass_nonneg s hr (div_nonneg hm (by norm_num)) hp

theorem section5RightMass_mono {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    {p : ℕ} (hp : p ≤ k + 1) :
    section5RightMass s r m p ≤ section5RightMass s r m (p + 1) := by
  apply section5Mass_mono s hr (p := p) (hp := hp)
  constructor <;> linarith [hm.1, hm.2]

theorem section5RightMass_endpoints {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    section5RightMass s r m 0 = 0 ∧ section5RightMass s r m (k + 2) = 1 :=
  section5Mass_endpoints s hr0 hr (m / 2)

theorem section5RightRho_mono {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) {u : ℝ} (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    {p : ℕ} (hp : p ≤ k + 2) :
    section5RightRho s r u p ≤ section5RightRho s r u (p + 1) := by
  unfold section5RightRho section5Rho
  by_cases hlt : p < r + 1
  · by_cases heq : p + 1 = r + 1
    · have hi : p = r := by omega
      subst p
      simpa using hu.1
    · have hl : p + 1 < r + 1 := by omega
      simp only [if_pos hlt, if_pos hl]
      exact s.q_mono p (by omega)
  · by_cases heq : p = r + 1
    · subst p
      simpa using hu.2
    · have hnl : ¬p + 1 < r + 1 := by omega
      have hne : p + 1 ≠ r + 1 := by omega
      simp only [if_neg hlt, if_neg heq, if_neg hnl, if_neg hne, Nat.add_sub_cancel]
      exact s.q_mono' p hp (p - 1) (by omega)

theorem section5RightRho_endpoints {k : ℕ} (s : RSBScheme k) {r : ℕ}
    (hr : r ≤ k + 1) (u : ℝ) :
    section5RightRho s r u 0 = 0 ∧ section5RightRho s r u (k + 3) = 1 := by
  simp [section5RightRho, section5Rho, show ¬k + 3 < r + 1 by omega,
    show k + 3 ≠ r + 1 by omega, s.q_zero, s.q_top,
    show k + 3 - 1 = k + 2 by omega]

theorem section5RightVariance_continuous {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r p : ℕ) : Continuous (section5RightVariance s β r p) := by
  unfold section5RightVariance
  split_ifs <;> fun_prop

theorem section5RightVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    0 ≤ section5RightVariance s β r p v := by
  unfold section5RightVariance
  split_ifs with hlt heq heq
  · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
  · exact hv.1
  · exact sub_nonneg.mpr hv.2
  · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono' p hp (p - 1) (by omega)))

theorem section5RightSplitVariance_mem {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    t * (β ^ 2 * (u - s.q r)) ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) := by
  have ha : 0 ≤ β ^ 2 * (u - s.q r) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1)
  constructor
  · exact mul_nonneg ht.1 ha
  · calc
      t * (β ^ 2 * (u - s.q r)) ≤ 1 * (β ^ 2 * (u - s.q r)) :=
        mul_le_mul_of_nonneg_right ht.2 ha
      _ ≤ β ^ 2 * (s.q (r + 1) - s.q r) := by nlinarith [sq_nonneg β, hu.2]

theorem section5RightInterpolationVariance_zero {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) :
    section5RightInterpolationVariance s β t u r p 0 =
      section5RightVariance s β r p (t * (β ^ 2 * (u - s.q r))) := by
  unfold section5RightInterpolationVariance section5FrozenVariance section5RightVariance
    section5RightRho section5Rho
  by_cases hlt : p < r
  · have hp : p < r + 1 := by omega
    have hp' : p + 1 < r + 1 := by omega
    simp only [if_pos hlt, if_pos hp, if_pos hp']
    ring
  · by_cases heq : p = r
    · subst p
      simp
      ring
    · by_cases heq' : p = r + 1
      · subst p
        simp
        ring
      · have hp : ¬p < r + 1 := by omega
        have hp' : ¬p + 1 < r + 1 := by omega
        have hp'' : p + 1 ≠ r + 1 := by omega
        simp only [if_neg hlt, if_neg heq, if_neg heq', if_neg hp, if_neg hp',
          if_neg hp'', Nat.add_sub_cancel]
        ring

@[simp] theorem section5RightInterpolationVariance_one {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r p : ℕ) :
    section5RightInterpolationVariance s β t u r p 1 = section5FrozenVariance s β t r p := by
  simp [section5RightInterpolationVariance]

theorem section5RightInterpolationVariance_nonneg {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r p : ℕ} (hr : r ≤ k + 1) (hp : p ≤ k + 2) {t u w : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Icc 0 1) : 0 ≤ section5RightInterpolationVariance s β t u r p w := by
  unfold section5RightInterpolationVariance
  apply add_nonneg
  · unfold section5FrozenVariance
    apply mul_nonneg (sub_nonneg.mpr ht.2)
    split_ifs with hlt heq
    · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono' p hp (p - 1) (by omega)))
  · exact mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) ht.1) (sq_nonneg β))
      (sub_nonneg.mpr (section5RightRho_mono s hr hu hp))

/-- The scalar paired endpoint for the right interval, with the new level shared. -/
noncomputable def section5RightV {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v ℓ : ℝ) : ℝ :=
  splitScalarCascade (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j))
    (k + 2 - r) (k + 3) v ℓ (h, h)

noncomputable def section5RightFieldEndpoint {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h u : ℝ) (r : ℕ) (m v : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j) v) (k + 2 - r)
    (constrainedBase n (0 : EnergySpace n) 0 0 u) (k + 3) (fun _ => h) (fun _ => h)

theorem section5RightFieldEndpoint_le {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β h u : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5RightFieldEndpoint n s β h u r m v ≤
      2 * Real.log 2 + section5RightV s β h r m v ℓ - ℓ * u := by
  have H := constrainedFieldCascade_le hn
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightVariance_continuous s β r (k + 2 - j))
    (k + 2 - r) (k + 3) v
    (fun j => section5RightVariance_nonneg s β hr (by omega) hv) u ℓ h hu
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hnR.le)
  simpa only [section5RightFieldEndpoint, section5RightV, ← mul_assoc,
    inv_mul_cancel₀ hnR.ne', one_mul] using H'

variable {Ω : Type*} [MeasureSpace Ω]

/-- Actual canonical second interpolation for `q_r ≤ u ≤ q_(r+1)`. -/
noncomputable def section5RightInterpolation {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) (m t u w : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
      (fun j => section5RightInterpolationVariance s β t u r (k + 2 - j) w) (k + 2 - r)
      (constrainedPairFieldBase n (Real.sqrt (w * t) • U ω) u) (k + 3)
      (fun _ => h) (fun _ => h) ∂ℙ

theorem section5RightInterpolation_zero [IsProbabilityMeasure (ℙ : Measure Ω)] {k : ℕ}
    (n : ℕ) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) (m t u : ℝ) :
    section5RightInterpolation n s β h U r m t u 0 =
      section5RightFieldEndpoint n s β h u r m (t * (β ^ 2 * (u - s.q r))) := by
  simp only [section5RightInterpolation, zero_mul, Real.sqrt_zero, zero_smul,
    constrainedPairFieldBase_zero, section5RightInterpolationVariance_zero,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    section5RightFieldEndpoint, one_div]

/-- The counterpart of (5.8): the same constrained pressure is recovered.
Only the sharing type of the inserted zero-variance level differs from the
already proved left endpoint. -/
theorem section5RightCascade_one {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (U : EnergySpace n) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    coupledFieldCascade n (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5FrozenVariance s β t r (k + 2 - j)) (k + 2 - r)
        (constrainedPairFieldBase n (Real.sqrt t • U) u) (k + 3) (fun _ => h) (fun _ => h) =
      coupledCascade n s β (k + 2 - r) (constrainedBase n U h t u) (k + 2) 0 0 := by
  have hv : section5FrozenVariance s β t r (k + 2 - (k + 2 - r)) = 0 := by
    rw [Nat.sub_sub_self (by omega), section5FrozenVariance_inserted]
  rw [← coupledFieldCascade_cutoff_zero n _ _ (k + 2 - r) (k + 3) hv,
    show k + 2 - r + 1 = k + 3 - r by omega]
  exact section5Cascade_one s β h U hr0 hr (m / 2) u ht

theorem section5RightInterpolation_one {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (m u : ℝ) {t : ℝ} (ht : t ≤ 1) :
    section5RightInterpolation n s β h U r m t u 1 =
      constrainedPhi n s β h U (k + 2 - r) t u := by
  simp only [section5RightInterpolation, section5RightInterpolationVariance_one, one_mul,
    section5RightCascade_one s β h _ hr0 hr m u ht, constrainedPhi]

/-- The counterpart of (5.17) for the dual right-interval construction. -/
theorem section5RightInterpolation_zero_le [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr : r ≤ k + 1) {m t u : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5RightInterpolation n s β h U r m t u 0 ≤
      2 * Real.log 2 + section5RightV s β h r m (t * (β ^ 2 * (u - s.q r))) ℓ - ℓ * u := by
  rw [section5RightInterpolation_zero]
  exact section5RightFieldEndpoint_le hn s β h u hr hm
    (section5RightSplitVariance_mem s β ht hu) hu' ℓ

end SpinGlass.Targets
