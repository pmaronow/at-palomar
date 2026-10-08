module

/-
# The zero-lambda identification in Talagrand Section 5

The paired recursion at lambda zero reduces to the actual scalar split-variance
recursion T of (4.35). Independent-step factorization, diagonal mass cancellation,
and site tensorization are reused; no new Gaussian integration theorem is needed.
-/
public import Targets.TalagrandSection5
public import Targets.ParisiStepSemigroup

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- A scalar Parisi recursion with its masses and variances exposed. -/
noncomputable def scalarFieldCascade (m v : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => Real.log (Real.cosh x)
  | j + 1 => parisiStep (m j) (v j) (scalarFieldCascade m v j)

theorem scalarFieldCascade_props (m v : ℕ → ℝ) (j : ℕ) :
    Measurable (scalarFieldCascade m v j) ∧ HasLinearGrowth (scalarFieldCascade m v j) ∧
      ∀ x y, |scalarFieldCascade m v j x - scalarFieldCascade m v j y| ≤ |x - y| := by
  induction j with
  | zero =>
    exact ⟨(Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne')).measurable,
      hasLinearGrowth_log_cosh, log_cosh_dist_le⟩
  | succ j ih =>
    have hLip : ∀ x y, |scalarFieldCascade m v (j + 1) x -
        scalarFieldCascade m v (j + 1) y| ≤ |x - y| := by
      intro x y
      simpa only [scalarFieldCascade, one_mul] using parisiStep_lipschitz (m := m j) (v := v j)
        (L := 1) (fun x y => by simpa using ih.2.2 x y) ih.2.1 ih.1 x y
    refine ⟨?_, hasLinearGrowth_parisiStep ih.2.1 ih.1 _ _, hLip⟩
    have hL : LipschitzWith 1 (scalarFieldCascade m v (j + 1)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hLip x y
    exact hL.continuous.measurable

private theorem scalar_guerraGrowth {A : ℝ → ℝ} (hA : HasLinearGrowth A)
    (hm : Measurable A) : GuerraGrowth (fun x : Fin 1 → ℝ => A (x 0)) := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  refine ⟨hm.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
  intro x
  simpa [l1] using hb (x 0)

private theorem parisiStepPi_one (m v : ℝ) {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hm : Measurable A) (x : Fin 1 → ℝ) :
    parisiStepPi 1 m v (fun y => A (y 0)) x = parisiStep m v A (x 0) := by
  simpa using parisiStepPi_sum (n := 1) m v hA hm x

/-- Before the branch, zero lambda separates the two replicas. -/
theorem coupledFieldCascade_zero_independent (m v : ℕ → ℝ) (d j : ℕ) (hj : j ≤ d)
    (x y : Fin 1 → ℝ) :
    coupledFieldCascade 1 m v d (fun x y => coupledSite 0 (x 0) (y 0)) j x y =
      scalarFieldCascade m v j (x 0) + scalarFieldCascade m v j (y 0) := by
  induction j generalizing x y with
  | zero => exact coupledSite_zero (x 0) (y 0)
  | succ j ih =>
    have hlt : j < d := by omega
    have he := funext fun x => funext fun y => ih (by omega) x y
    rw [coupledFieldCascade, if_pos hlt, he, independentStepPi_add]
    · rw [parisiStepPi_one _ _ (scalarFieldCascade_props m v j).2.1
        (scalarFieldCascade_props m v j).1,
        parisiStepPi_one _ _ (scalarFieldCascade_props m v j).2.1
          (scalarFieldCascade_props m v j).1]
      rfl
    all_goals
      exact scalar_guerraGrowth (scalarFieldCascade_props m v j).2.1
        (scalarFieldCascade_props m v j).1

/-- The scalar recursion uses twice the paired mass at shared levels. -/
theorem coupledFieldCascade_zero_diag (m v : ℕ → ℝ) (d j : ℕ) (x : Fin 1 → ℝ) :
    coupledFieldCascade 1 m v d (fun x y => coupledSite 0 (x 0) (y 0)) j x x =
      2 * scalarFieldCascade (fun i => if i < d then m i else 2 * m i) v j (x 0) := by
  induction j generalizing x with
  | zero => simp only [coupledFieldCascade, scalarFieldCascade, coupledSite_zero, two_mul]
  | succ j ih =>
    by_cases hj : j < d
    · rw [coupledFieldCascade_zero_independent m v d (j + 1) (by omega), ← two_mul]
      congr 1
      have he : ∀ l, l ≤ j + 1 → scalarFieldCascade m v l =
          scalarFieldCascade (fun i => if i < d then m i else 2 * m i) v l := by
        intro l hl
        induction l with
        | zero => rfl
        | succ l il =>
          simp only [scalarFieldCascade, if_pos (show l < d by omega), il (by omega)]
      exact congrFun (he (j + 1) le_rfl) (x 0)
    · rw [coupledFieldCascade, if_neg hj]
      rw [sharedStepPi_diag (2 * m j) (v j) _ _ ih]
      rw [parisiStepPi_one _ _ (scalarFieldCascade_props _ v j).2.1
        (scalarFieldCascade_props _ v j).1]
      simp only [scalarFieldCascade, if_neg hj]

/-- Zero-lambda factorization of the actual scalar paired recursion, at any depth. -/
theorem splitScalarCascade_zero_diag (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, Continuous (v j))
    (d j : ℕ) (p : ℝ) (hp : ∀ j, 0 ≤ v j p) (x : ℝ) :
    splitScalarCascade m v d j p 0 (x, x) =
      2 * scalarFieldCascade (fun i => if i < d then m i else 2 * m i)
        (fun i => v i p) j x := by
  have H := coupledFieldCascade_eq_sum 1 m v hm hv d j p hp 0
    (fun _ => x) (fun _ => x)
  simp only [Fin.sum_univ_one] at H
  rw [← H]
  exact coupledFieldCascade_zero_diag m (fun i => v i p) d j (fun _ => x)

/-- The original scalar mass with one inserted mass, before reversing the levels. -/
noncomputable def section4Mass {k : ℕ} (s : RSBScheme k) (r : ℕ) (m : ℝ) (p : ℕ) : ℝ :=
  if p < r then s.m p else if p = r then m else s.m (p - 1)

/-- The actual split-variance scalar recursion T(v,m) of (4.35).
The Lean arguments are mass `m` then variance `v`. -/
noncomputable def section4T {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m v : ℝ) : ℝ :=
  scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j) v) (k + 3) h

/-- The unchanged inner part of the inserted scalar recursion. -/
theorem section4Cascade_prefix {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m v : ℝ) {j : ℕ} (hj : j ≤ k + 2 - r) :
    scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
      (fun j => section5Variance s β r (k + 2 - j) v) j = parisiF s β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp : r < k + 2 - j := by omega
    have hp' : ¬k + 2 - j < r := by omega
    have hp'' : k + 2 - j ≠ r := by omega
    have he : k + 2 - j - 1 = k + 1 - j := by omega
    rw [scalarFieldCascade, ih (by omega)]
    simp only [section4Mass, section5Variance, if_pos hp,
      if_neg hp', if_neg hp'', he, parisiF]

/-- The inserted step is precisely the scalar B(x,v,m) used in Section 4. -/
theorem section4Cascade_inserted {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 2) (m v : ℝ) :
    scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
      (fun j => section5Variance s β r (k + 2 - j) v) (k + 2 - r + 1) =
      parisiStep m v (parisiF s β (k + 2 - r)) := by
  rw [scalarFieldCascade, section4Cascade_prefix s β r m v le_rfl]
  simp [section4Mass, section5Variance, Nat.sub_sub_self hr]

/-- Talagrand (5.18), including zero masses and split-variance endpoints. -/
theorem section5V_zero_eq_two_section4T {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section5V s β h r m v 0 = 2 * section4T s β h r m v := by
  unfold section5V
  rw [splitScalarCascade_zero_diag _ _
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j))
    _ _ _ (fun j => section5Variance_nonneg s β hr (by omega) hv)]
  have he : (fun i => if i < k + 3 - r then section5Mass s r m (k + 2 - i)
      else 2 * section5Mass s r m (k + 2 - i)) =
      fun i => section4Mass s r m (k + 2 - i) := by
    funext i
    by_cases hi : i < k + 3 - r
    · have hp : ¬k + 2 - i < r := by omega
      simp only [if_pos hi, section5Mass, section4Mass, if_neg hp]
    · have hp : k + 2 - i < r := by omega
      simp only [if_neg hi, section5Mass, section4Mass, if_pos hp]
      ring
  rw [he]
  rfl

/-- At the old mass the split variance disappears, including when that mass is zero. -/
theorem section4Cascade_baseline {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    {j : ℕ} (hj : j ≤ r - 1) :
    scalarFieldCascade (fun j => section4Mass s r (s.m (r - 1)) (k + 2 - j))
      (fun j => section5Variance s β r (k + 2 - j) v) (k + 2 - r + 2 + j) =
      parisiF s β (k + 2 - r + 1 + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero]
    rw [show k + 2 - r + 2 = (k + 2 - r + 1) + 1 by omega,
      scalarFieldCascade, section4Cascade_inserted s β (by omega)]
    have hi : k + 2 - (k + 2 - r + 1) = r - 1 := by omega
    have hprev : r - 1 < r := by omega
    have hne : r - 1 ≠ r := by omega
    have hng : ¬r < r - 1 := by omega
    have hnext : r - 1 + 1 = r := by omega
    rw [hi]
    simp only [section4Mass, section5Variance, if_pos hprev, if_neg hng,
      if_neg hne, if_pos hnext]
    have H := (parisiStep_add (s.m (r - 1))
      (β ^ 2 * (s.q r - s.q (r - 1)) - v) v (by linarith [hv.2]) hv.1
      (parisiF_hasLinearGrowth s β (k + 2 - r)) (parisiF_measurable s β (k + 2 - r))).symm
    refine H.trans ?_
    rw [sub_add_cancel]
    simp only [parisiF, show k + 1 - (k + 2 - r) = r - 1 by omega,
      Nat.sub_sub_self (show r ≤ k + 2 by omega)]
  | succ j ih =>
    rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
      scalarFieldCascade, ih (by omega)]
    have hp : k + 2 - (k + 2 - r + 2 + j) < r := by omega
    have hpn : k + 2 - (k + 2 - r + 2 + j) ≠ r := by omega
    have hpn' : ¬r < k + 2 - (k + 2 - r + 2 + j) := by omega
    have hpn'' : k + 2 - (k + 2 - r + 2 + j) + 1 ≠ r := by omega
    have hi : k + 1 - (k + 2 - r + 1 + j) =
        k + 2 - (k + 2 - r + 2 + j) := by omega
    have hi' : k + 2 - (k + 2 - r + 1 + j) =
        k + 2 - (k + 2 - r + 2 + j) + 1 := by omega
    rw [show k + 2 - r + 1 + (j + 1) = (k + 2 - r + 1 + j) + 1 by omega, parisiF]
    simp only [section4Mass, section5Variance, if_pos hp, if_neg hpn,
      if_neg hpn', if_neg hpn'', hi, hi']

/-- Talagrand (4.36): at the original mass, T is independent of the split variance. -/
theorem section4T_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4T s β h r (s.m (r - 1)) v = parisiF s β (k + 2) h := by
  have H := section4Cascade_baseline s β hr0 hr hv (j := r - 1) le_rfl
  have hi : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  have hi' : k + 2 - r + 1 + (r - 1) = k + 2 := by omega
  simpa only [section4T, hi, hi'] using congrFun H h

/-- Talagrand (5.19), with no positive-mass or nondegenerate-variance restriction. -/
theorem section5V_zero_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section5V s β h r (s.m (r - 1)) v 0 = 2 * parisiF s β (k + 2) h := by
  rw [section5V_zero_eq_two_section4T s β h hr0 hr (s.m_nonneg (by omega)) hv,
    section4T_baseline s β h hr0 hr hv]

end SpinGlass.Targets
