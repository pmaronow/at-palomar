module

public import Targets.Section4HessianUniform

@[expose] public section

/-!
# The dual baseline factors by reflection

The right construction on `[q_r,q_(r+1)]` has shared variance `v` and
independent variance `a-v`. Its baseline factors are the next left interval's
already checked factors evaluated at `a-v`. This reuses the actual normalized
recursion, its endpoint calculus and its universal regularity bound.
Identification with the actual right lambda derivative is proved separately.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The normalized squared-slope factor in the dual baseline construction. -/
noncomputable def section4RightQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (v : ℝ) : ℝ :=
  section4TVarianceQ s β h (r + 1) (s.m r)
    (β ^ 2 * (s.q (r + 1) - s.q r) - v)

/-- The actual squared-Hessian factor with the dual variance orientation. -/
noncomputable def section4RightR {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (v : ℝ) : ℝ :=
  section4THessianSquare s β h (r + 1)
    (β ^ 2 * (s.q (r + 1) - s.q r) - v)

/-- Reversing the split variance preserves its closed physical interval. -/
theorem section4Right_reflectedVariance_mem {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    β ^ 2 * (s.q (r + 1) - s.q r) - v ∈
      Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) := by
  constructor <;> linarith [hv.1, hv.2]

/-- The right squared-slope factor has positive Hessian-square derivative,
including inward derivatives at both variance endpoints. -/
theorem hasDerivWithinAt_section4RightQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivWithinAt (section4RightQ s β h r) (section4RightR s β h r v)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) v := by
  have hmap : Set.MapsTo (fun w => β ^ 2 * (s.q (r + 1) - s.q r) - w)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :=
    fun w hw => section4Right_reflectedVariance_mem s β r hw
  have H := hasDerivWithinAt_section4TVarianceQ_baseline s β h (r := r + 1)
    (v := β ^ 2 * (s.q (r + 1) - s.q r) - v)
    (by omega) (by omega) (by simpa only [Nat.add_sub_cancel] using hmap hv)
  have D := ((hasDerivAt_id v).const_sub (β ^ 2 * (s.q (r + 1) - s.q r))).hasDerivWithinAt
    (s := Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
  simpa [section4RightQ, section4RightR] using! H.comp v D (by simpa using hmap)

/-- Closed-interval continuity of the dual squared-slope factor. -/
theorem continuousOn_section4RightQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k) :
    ContinuousOn (section4RightQ s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :=
  fun _ hv => (hasDerivWithinAt_section4RightQ s β h hr hv).continuousWithinAt

/-- The same universal constant controls the actual reflected Hessian-square
factor. Reflection does not change the variance Lipschitz constant. -/
theorem section4RightR_lipschitz_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    |section4RightR s β h r v - section4RightR s β h r w| ≤ 535 * |v - w| := by
  have H := section4THessianSquare_lipschitz_uniform s β h (r := r + 1)
    (v := β ^ 2 * (s.q (r + 1) - s.q r) - v)
    (w := β ^ 2 * (s.q (r + 1) - s.q r) - w)
    (by omega) (by omega)
    (by simpa only [Nat.add_sub_cancel] using section4Right_reflectedVariance_mem s β r hv)
    (by simpa only [Nat.add_sub_cancel] using section4Right_reflectedVariance_mem s β r hw)
  simpa [section4RightR, sub_sub_sub_cancel_left, abs_sub_comm] using H

end SpinGlass.Targets
