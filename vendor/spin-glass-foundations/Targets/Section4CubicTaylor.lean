module

public import Targets.Section4Curvature

@[expose] public section

/-!
# Actual cubic Taylor bounds from Hessian-square regularity

Two applications of Mathlib's endpoint-safe mean-value estimate turn a
Lipschitz bound on the actual normalized Hessian-square factor `R` into a
cubic Taylor remainder for the actual first variation. The Lipschitz estimate
for `R` is explicitly assumed: its beta-only, depth-uniform proof is the
remaining analytic input of Lemma 4.9. No cubic remainder is assumed here.
-/

open Real

namespace SpinGlass.Targets

private theorem cubic_remainder_of_second_lipschitz
    {f d d2 : ℝ → ℝ} {l r K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ Set.Icc l r, HasDerivWithinAt f (d x) (Set.Icc l r) x)
    (hd : ∀ x ∈ Set.Icc l r, HasDerivWithinAt d (d2 x) (Set.Icc l r) x)
    (hLip : ∀ x ∈ Set.Icc l r, ∀ y ∈ Set.Icc l r, |d2 x - d2 y| ≤ K * |x - y|)
    {a b : ℝ} (ha : a ∈ Set.Icc l r) (hb : b ∈ Set.Icc l r) :
    |f a - f b - d b * (a - b) - d2 b / 2 * (a - b) ^ 2| ≤ K * |a - b| ^ 3 := by
  have hsub : Set.uIcc b a ⊆ Set.Icc l r := Set.uIcc_subset_Icc hb ha
  let E1 := fun x => d x - d b - d2 b * (x - b)
  have hE1 (x : ℝ) (hx : x ∈ Set.uIcc b a) :
      HasDerivWithinAt E1 (d2 x - d2 b) (Set.uIcc b a) x := by
    simpa only [E1, mul_one, Pi.sub_def, id_eq] using! ((hd x (hsub hx)).sub_const (d b)).sub
      ((((hasDerivAt_id x).sub_const b).const_mul (d2 b)).hasDerivWithinAt) |>.mono hsub
  have hD (x : ℝ) (hx : x ∈ Set.uIcc b a) : |d2 x - d2 b| ≤ K * |a - b| :=
    (hLip x (hsub hx) b hb).trans
      (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx) hK)
  have hE1bound (x : ℝ) (hx : x ∈ Set.uIcc b a) : |E1 x| ≤ K * |a - b| ^ 2 := by
    have H := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le hE1
      (fun y hy => by simpa only [Real.norm_eq_abs] using hD y hy)
      Set.left_mem_uIcc hx
    have H' : |E1 x| ≤ (K * |a - b|) * |x - b| := by
      simpa only [E1, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] using H
    calc
      |E1 x| ≤ (K * |a - b|) * |x - b| := H'
      _ ≤ (K * |a - b|) * |a - b| :=
        mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx)
          (mul_nonneg hK (abs_nonneg _))
      _ = K * |a - b| ^ 2 := by ring
  let E0 := fun x => f x - f b - d b * (x - b) - d2 b / 2 * (x - b) ^ 2
  have hE0 (x : ℝ) (hx : x ∈ Set.uIcc b a) :
      HasDerivWithinAt E0 (E1 x) (Set.uIcc b a) x := by
    have H := (((hf x (hsub hx)).sub_const (f b)).sub
      ((((hasDerivAt_id x).sub_const b).const_mul (d b)).hasDerivWithinAt)).sub
      (((((hasDerivAt_id x).sub_const b).pow 2).const_mul (d2 b / 2)).hasDerivWithinAt)
    convert! H.mono hsub using 1
    simp only [E1, id_eq]
    ring
  have H := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le hE0
    (fun x hx => by simpa only [Real.norm_eq_abs] using hE1bound x hx)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa only [E0, sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    Real.norm_eq_abs, pow_succ, mul_assoc] using H

/-- A variance-Lipschitz bound for the actual Hessian-square factor gives
the correct beta scaling for the overlap curvature: `β^6 L / 2`. -/
theorem section4FirstVariationD2_lipschitz_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ} {L : ℝ}
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|)
    {u w : ℝ} (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariationD2 s β h r u - section4FirstVariationD2 s β h r w| ≤
      (β ^ 6 * L / 2) * |u - w| := by
  have hmap (z : ℝ) (hz : z ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
      β ^ 2 * (s.q r - z) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left (by linarith [hz.1]) (sq_nonneg β)⟩
  have h4 : 0 ≤ β ^ 4 / 2 := by positivity
  calc
    _ = (β ^ 4 / 2) * |section4THessianSquare s β h r (β ^ 2 * (s.q r - u)) -
        section4THessianSquare s β h r (β ^ 2 * (s.q r - w))| := by
      rw [show section4FirstVariationD2 s β h r u - section4FirstVariationD2 s β h r w =
        -(β ^ 4 / 2) * (section4THessianSquare s β h r (β ^ 2 * (s.q r - u)) -
          section4THessianSquare s β h r (β ^ 2 * (s.q r - w))) by
            unfold section4FirstVariationD2; ring]
      rw [abs_mul, abs_neg, abs_of_nonneg h4]
    _ ≤ (β ^ 4 / 2) * (L * |β ^ 2 * (s.q r - u) - β ^ 2 * (s.q r - w)|) :=
      mul_le_mul_of_nonneg_left (hLip _ (hmap u hu) _ (hmap w hw)) h4
    _ = (β ^ 6 * L / 2) * |u - w| := by
      rw [show β ^ 2 * (s.q r - u) - β ^ 2 * (s.q r - w) = -(β ^ 2) * (u - w) by ring,
        abs_mul, abs_neg, abs_of_nonneg (sq_nonneg β)]
      ring

/-- The actual first variation has a cubic Taylor remainder conditional only
on Lipschitz regularity of its actual Hessian-square factor. Expansion is about
any point of the closed physical interval; no stationarity is assumed. -/
theorem section4FirstVariation_cubic_taylor_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|)
    {u w : ℝ} (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariation s β h r u - section4FirstVariation s β h r w -
      section4FirstVariationD s β h r w * (u - w) -
      section4FirstVariationD2 s β h r w / 2 * (u - w) ^ 2| ≤
      (β ^ 6 * L / 2) * |u - w| ^ 3 := by
  apply cubic_remainder_of_second_lipschitz (by positivity)
    (fun x hx => hasDerivWithinAt_section4FirstVariation_D s β h hr0 hr hm hx)
    (fun x hx => hasDerivWithinAt_section4FirstVariationD_D2 s β h hr0 hr hx)
    (fun x hx y hy => section4FirstVariationD2_lipschitz_of_hessian_lipschitz s β h hLip hx hy)
    hu hw

/-- At the stationary upper endpoint the actual constant and linear Taylor
terms vanish. Their vanishing follows from checked optimality, not from the
regularity hypothesis. -/
theorem section4FirstVariation_stationary_cubic_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|)
    {u : ℝ} (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariation s β h r u -
      section4FirstVariationD2 s β h r (s.q r) / 2 * (u - s.q r) ^ 2| ≤
      (β ^ 6 * L / 2) * |u - s.q r| ^ 3 := by
  have H := section4FirstVariation_cubic_taylor_of_hessian_lipschitz s β h hr0 hr
    (hm.trans_le (s.m_le_one hr)) hL hLip hu
    (show s.q r ∈ Set.Icc (s.q (r - 1)) (s.q r) from
      ⟨s.q_mono' r (by omega) (r - 1) (by omega), le_rfl⟩)
  simpa only [section4FirstVariation_at_upper_overlap s β h hr0 hr,
    section4FirstVariationD_upper_zero_of_min s β h hr0 hr hβ hm hleft hright hmin,
    zero_mul, sub_zero] using H

/-- Noninitial Proposition 4.10 conditional only on the missing regularity
of the actual Hessian-square factor. The cubic Taylor estimate is proved above
and is no longer a premise of this adapter. -/
theorem section4FirstVariation_curvature_lower_bound_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|) :
    -section4FirstVariationD2 s β h r (s.q r) ≤
      2 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ) := by
  apply section4FirstVariation_curvature_lower_bound_of_cubic_remainder s β h ε
    (β ^ 6 * L / 2) hr0 hr hβ hm hleft hright (by positivity) hmin hnear
  intro u hu
  exact section4FirstVariation_cubic_taylor_of_hessian_lipschitz s β h (by omega) hr
    (hm.trans_le (s.m_le_one hr)) hL hLip hu ⟨hleft.le, le_rfl⟩

end SpinGlass.Targets
