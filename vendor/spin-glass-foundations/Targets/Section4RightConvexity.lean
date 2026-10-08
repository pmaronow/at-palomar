module

public import Targets.Section4RightUPrime
public import Targets.Section4RightOptimality
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Convex supporting lines for the actual right first variation

The actual right variance factor is increasing, with derivative the nonnegative
reflected Hessian-square factor. Thus the right mass derivative is convex.
The resulting supporting-line estimate has the opposite sign to (5.34), as
required when the inserted coupled mass is increased in Proposition 5.6.
-/

open Real

namespace SpinGlass.Targets

/-- Positivity of the actual right Hessian-square factor, including the
terminal interval. Padding transfers the observable, not minimality. -/
theorem section4RightR_nonneg {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (v : ℝ) : 0 ≤ section4RightR s β h r v := by
  rw [← section4RightR_padOneLast s β h hr]
  exact (section4THessianSquare_mem_Icc s.padOneLast β h (r := r + 1)
    (by omega) _).1

/-- Convexity is derived from the checked actual first and second variance
derivatives. The closed interval may be degenerate. -/
theorem convexOn_section4RightU {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) :
    ConvexOn ℝ (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
      (section4RightU s β h r) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun v hv => (hasDerivWithinAt_section4RightU s β h hr hm hv).continuousWithinAt)
    (f' := section4RightQ s β h r) (f'' := section4RightR s β h r)
  · intro v hv
    exact (hasDerivWithinAt_section4RightU s β h hr hm
      (interior_subset hv)).mono interior_subset
  · intro v hv
    exact (hasDerivWithinAt_section4RightQ_all_levels s β h hr
      (interior_subset hv)).mono interior_subset
  · intro v _
    exact section4RightR_nonneg s β h hr v

/-- The actual right supporting line is valid at both physical endpoints,
with its actual inward slope rather than the default unrestricted derivative. -/
theorem section4RightU_ge_supportingLine {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section4RightU s β h r v + (w - v) * section4RightQ s β h r v ≤
      section4RightU s β h r w := by
  have hc := convexOn_section4RightU s β h hr hm
  have hd := hasDerivWithinAt_section4RightU s β h hr hm hv
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · have H := hc.le_slope_of_hasDerivWithinAt hv hw hvw hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hvw)] at H
    nlinarith only [H]
  · simp
  · have H := hc.slope_le_of_hasDerivWithinAt hw hv hwv hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hwv)] at H
    nlinarith only [H]

/-- The right-side analogue of (5.34), with the actual normalized-factor
error retained. All times in `[0,1]` and all right physical overlaps are included. -/
theorem section4RightU_interpolation_slope_upper_bound {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r) {u t : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) (ht : t ∈ Set.Icc 0 1) :
    section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
        t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) ≤
      2 * section4RightFirstVariation s β h r u -
        (1 - t) * (β ^ 2 / 2) * (u - s.q r) ^ 2 -
        (1 - t) * (β ^ 2 * (u - s.q r)) *
          (section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) - u) := by
  have hv : β ^ 2 * (u - s.q r) ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1),
      mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 _) (sq_nonneg β)⟩
  have htv : t * (β ^ 2 * (u - s.q r)) ∈
      Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    ⟨mul_nonneg ht.1 hv.1, (mul_le_of_le_one_left hv.1 ht.2).trans hv.2⟩
  have H := section4RightU_ge_supportingLine s β h hr hm htv hv
  unfold section4RightFirstVariation
  nlinarith only [H]

/-- If the actual right lambda slope vanishes, the positive-overlap square
appears with a negative sign in the right mass slope. -/
theorem section4RightU_interpolation_slope_upper_bound_of_factor_eq {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) (hm : 0 < s.m r)
    {u t e : ℝ} (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (ht : t ∈ Set.Icc 0 1)
    (hQ : section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) = u)
    (hf : section4RightFirstVariation s β h r u ≤ e) :
    section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
        t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) ≤
      2 * e - (1 - t) * (β ^ 2 / 2) * (u - s.q r) ^ 2 := by
  have H := section4RightU_interpolation_slope_upper_bound s β h hr hm hu ht
  rw [hQ, sub_self, mul_zero, sub_zero] at H
  linarith

end SpinGlass.Targets
