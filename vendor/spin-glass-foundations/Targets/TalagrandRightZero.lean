module

public import Targets.TalagrandRightInterpolation
public import Targets.CoupledLambdaCurvature

@[expose] public section

/-!
# The right-interval scalar baseline and lambda gain

At zero coupling, the actual paired construction reduces to the dual scalar
split of the interval `[q_r,q_(r+1)]`. Its baseline is `m_r`, not `m_(r-1)`.
The scalar Gaussian semigroup restores the original recursion, including the
last interval ending at 1 and both variance endpoints. The lambda estimates
reuse the existing level-independent curvature invariant.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The dual scalar split: mass `m` on the lower part of `[q_r,q_(r+1)]`.
Arguments are mass then variance, as in the existing `section4T`. -/
noncomputable def section4RightT {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) : ℝ :=
  scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j) v) (k + 3) h

theorem section5RightV_zero_eq_two_section4RightT {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : 0 ≤ m)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section5RightV s β h r m v 0 = 2 * section4RightT s β h r m v := by
  unfold section5RightV
  rw [splitScalarCascade_zero_diag _ _
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightVariance_continuous s β r (k + 2 - j))
    (k + 2 - r) (k + 3) v
    (fun j => section5RightVariance_nonneg s β hr (by omega) hv)]
  have he : (fun i => if i < k + 2 - r then section5RightMass s r m (k + 2 - i)
      else 2 * section5RightMass s r m (k + 2 - i)) =
      fun i => section4Mass s r m (k + 2 - i) := by
    funext i
    by_cases hi : i < k + 2 - r
    · have hp : ¬k + 2 - i < r := by omega
      have hp' : k + 2 - i ≠ r := by omega
      simp only [if_pos hi, section5RightMass, section5Mass, section4Mass,
        if_neg hp, if_neg hp']
    · have hp : k + 2 - i ≤ r := by omega
      simp only [if_neg hi, section5RightMass, section5Mass, section4Mass]
      by_cases hlt : k + 2 - i < r
      · simp only [if_pos hlt]
        ring
      · have heq : k + 2 - i = r := by omega
        simp only [if_neg hlt, if_pos heq]
        ring
  rw [he]
  rfl

theorem section4RightCascade_prefix {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m v : ℝ) {j : ℕ} (hj : j ≤ k + 1 - r) :
    scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
      (fun j => section5RightVariance s β r (k + 2 - j) v) j = parisiF s β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp : ¬k + 2 - j < r := by omega
    have hp' : k + 2 - j ≠ r := by omega
    have hp'' : k + 2 - j ≠ r + 1 := by omega
    rw [scalarFieldCascade, ih (by omega)]
    simp only [section4Mass, section5RightVariance, if_neg hp, if_neg hp', if_neg hp'',
      parisiF, show k + 2 - j - 1 = k + 1 - j by omega]

theorem section4RightCascade_baseline {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    {j : ℕ} (hj : j ≤ r) :
    scalarFieldCascade (fun j => section4Mass s r (s.m r) (k + 2 - j))
      (fun j => section5RightVariance s β r (k + 2 - j) v) (k + 1 - r + 2 + j) =
      parisiF s β (k + 1 - r + 1 + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero]
    rw [show k + 1 - r + 2 = (k + 1 - r + 1) + 1 by omega,
      scalarFieldCascade, scalarFieldCascade, section4RightCascade_prefix s β hr _ _ le_rfl]
    have hi : k + 2 - (k + 1 - r + 1) = r := by omega
    have hi' : k + 2 - (k + 1 - r) = r + 1 := by omega
    simp only [hi, hi', section4Mass, section5RightVariance, lt_self_iff_false,
      if_false, if_true, if_neg (show ¬r + 1 < r by omega),
      if_neg (show r + 1 ≠ r by omega), Nat.add_sub_cancel]
    have H := (parisiStep_add (s.m r) v
      (β ^ 2 * (s.q (r + 1) - s.q r) - v) hv.1 (sub_nonneg.mpr hv.2)
      (parisiF_hasLinearGrowth s β (k + 1 - r))
      (parisiF_measurable s β (k + 1 - r))).symm
    refine H.trans ?_
    rw [add_sub_cancel]
    simp only [parisiF, Nat.sub_sub_self hr, hi']
  | succ j ih =>
    rw [show k + 1 - r + 2 + (j + 1) = (k + 1 - r + 2 + j) + 1 by omega,
      scalarFieldCascade, ih (by omega)]
    have hp : k + 2 - (k + 1 - r + 2 + j) < r := by omega
    have hi : k + 1 - (k + 1 - r + 1 + j) = k + 2 - (k + 1 - r + 2 + j) := by omega
    have hi' : k + 2 - (k + 1 - r + 1 + j) =
        k + 2 - (k + 1 - r + 2 + j) + 1 := by omega
    rw [show k + 1 - r + 1 + (j + 1) = (k + 1 - r + 1 + j) + 1 by omega, parisiF]
    simp only [section4Mass, section5RightVariance, if_pos hp, hi, hi']

/-- The dual counterpart of (4.36), including the final overlap interval. -/
theorem section4RightT_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section4RightT s β h r (s.m r) v = parisiF s β (k + 2) h := by
  have H := section4RightCascade_baseline s β hr hv (j := r) le_rfl
  simpa only [section4RightT, show k + 1 - r + 2 + r = k + 3 by omega,
    show k + 1 - r + 1 + r = k + 2 by omega] using congrFun H h

/-- The dual counterpart of (5.19), at baseline mass `m_r`. -/
theorem section5RightV_zero_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section5RightV s β h r (s.m r) v 0 = 2 * parisiF s β (k + 2) h := by
  rw [section5RightV_zero_eq_two_section4RightT s β h hr (s.m_nonneg hr) hv,
    section4RightT_baseline s β h hr hv]

/-- The existing sharp curvature invariant applies to the dual cascade.
The scalar inserted mass may be as large as 2, since its paired mass is `m/2`. -/
theorem section5RightV_lambda_gain {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc 0 2) (v u : ℝ) :
    ∃ l : ℝ, section5RightV s β h r m v l - l * u ≤
      section5RightV s β h r m v 0 - (deriv (section5RightV s β h r m v) 0 - u) ^ 2 / 2 := by
  let M := fun j => section5RightMass s r m (k + 2 - j)
  let V := fun j => section5RightVariance s β r (k + 2 - j)
  have H := splitScalarCascade_unitCurvature M V
    (fun j => ⟨section5RightMass_nonneg s hr hm.1 (by omega),
      section5Mass_le_one s (m := m / 2) (by linarith [hm.2]) r (by omega) hr⟩)
    (fun j => section5RightVariance_continuous s β r (k + 2 - j)) (k + 2 - r) (k + 3)
  let d := fun l => splitScalarCascadeD M V (k + 2 - r) (k + 3) v l (h, h)
  have hd (l : ℝ) : HasDerivAt (section5RightV s β h r m v) (d l) l :=
    H.triple.good.hasDeriv v l (h, h)
  have Hq := quadratic_upper_of_second_le_one hd
    (fun l => H.triple.derivD v l (h, h))
    (fun l => (H.sharp v l (h, h)).trans (sub_le_self _ (sq_nonneg _))) (u - d 0)
  refine ⟨u - d 0, ?_⟩
  rw [(hd 0).deriv]
  nlinarith

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The optimized actual time-zero endpoint for the right interval. No transport
to time one or identification of the lambda derivative with the dual `U′` is assumed. -/
theorem section5RightInterpolation_zero_lambda_gain
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r : ℕ} (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5RightInterpolation n s β h U r (s.m r) t u 0 ≤
      2 * (Real.log 2 + parisiF s β (k + 2) h) -
        (deriv (section5RightV s β h r (s.m r) (t * (β ^ 2 * (u - s.q r)))) 0 - u) ^ 2 / 2 := by
  obtain ⟨l, hl⟩ := section5RightV_lambda_gain s β h hr (m := s.m r)
    ⟨s.m_nonneg hr, (s.m_le_one hr).trans (by norm_num)⟩
    (t * (β ^ 2 * (u - s.q r))) u
  rw [section5RightV_zero_baseline s β h hr (section5RightSplitVariance_mem s β ht hu)] at hl
  have H := section5RightInterpolation_zero_le hn s β h U hr (m := s.m r)
    (s.m_nonneg hr) ht hu hu' l
  linarith

end SpinGlass.Targets
