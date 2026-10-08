module

public import Targets.Section4USecond
public import Targets.Section4UEndpoints
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Concavity and the supporting line of Talagrand's actual U

The proved identities `U' = Q` and `Q' = -R`, with `R ≥ 0`, imply
concavity on the full physical variance interval. The supporting-line estimate
uses the proved inward derivative at an endpoint, not the unrestricted
`deriv` there. Thus zero variance gaps and both interpolation endpoints are
included. The final SK estimate is the algebraic form of (5.34), retaining
the actual normalized-factor error instead of assuming a stationarity identity.
-/

open Real

namespace SpinGlass.Targets

/-- The actual normalized squared-slope factor is antitone on the closed
physical interval, including both variance endpoints. -/
theorem antitoneOn_section4TVarianceQ_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    AntitoneOn (section4TVarianceQ s β h r (s.m (r - 1)))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (continuousOn_section4TVarianceQ_variance s β h hr0 hr
      ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩)
  · intro v hv
    rw [interior_Icc] at hv
    exact (hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hv).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    rw [(hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hv).deriv]
    exact neg_nonpos.mpr (section4THessianSquare_mem_Icc s β h hr v).1

/-- Talagrand's actual `U` is concave on its closed physical variance interval.
No concavity hypothesis, positive variance gap, or positive baseline mass is needed. -/
theorem concaveOn_section4U {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) :
    ConcaveOn ℝ (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
      (section4U s β h r) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (continuousOn_section4U s β h hr0 hr hm)
    (f' := section4TVarianceQ s β h r (s.m (r - 1)))
    (f'' := fun v => -section4THessianSquare s β h r v)
  · intro v hv
    rw [interior_Icc] at hv
    exact (hasDerivAt_section4U s β h hr0 hr hm hv).hasDerivWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    exact (hasDerivAt_section4TVarianceQ_baseline s β h hr0 hr hv).hasDerivWithinAt
  · intro v _
    exact neg_nonpos.mpr (section4THessianSquare_mem_Icc s β h hr v).1

/-- The supporting line at any point of the closed interval has slope equal
to the actual normalized squared-slope factor, also at variance endpoints. -/
theorem section4U_le_supportingLine {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section4U s β h r w ≤ section4U s β h r v +
      (w - v) * section4TVarianceQ s β h r (s.m (r - 1)) v := by
  have hc := concaveOn_section4U s β h hr0 hr hm
  have hd := hasDerivWithinAt_section4U s β h hr0 hr hm hv
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · have H := hc.slope_le_of_hasDerivWithinAt hv hw hvw hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hvw)] at H
    nlinarith only [H]
  · simp
  · have H := hc.le_slope_of_hasDerivWithinAt hw hv hwv hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hwv)] at H
    nlinarith only [H]

/-- Talagrand (5.34) in the physical variance interval. This formulation is
valid at `t = 0`, `t = 1`, and when the variance interval is a singleton. -/
theorem section4U_sub_ge_supportingLine {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {v t : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (ht : t ∈ Set.Icc 0 1) :
    section4U s β h r v - (1 - t) * v *
      section4TVarianceQ s β h r (s.m (r - 1)) (t * v) ≤
        section4U s β h r (t * v) := by
  have htv : t * v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨mul_nonneg ht.1 hv.1,
      (mul_le_of_le_one_left hv.1 ht.2).trans hv.2⟩
  have H := section4U_le_supportingLine s β h hr0 hr hm htv hv
  nlinarith only [H]

/-- The SK correction in (5.34) exposes a positive quadratic gap and the
actual normalized-factor error. This is independent of optimality assumptions. -/
theorem section4U_interpolation_slope_lower_bound {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u t : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) (ht : t ∈ Set.Icc 0 1) :
    2 * section4FirstVariation s β h r u +
        (1 - t) * (β ^ 2 / 2) * (s.q r - u) ^ 2 -
        (1 - t) * (β ^ 2 * (s.q r - u)) *
          (section4TVarianceQ s β h r (s.m (r - 1))
            (t * (β ^ 2 * (s.q r - u))) - u) ≤
      section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
        t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2) := by
  have hv : β ^ 2 * (s.q r - u) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.2),
      mul_le_mul_of_nonneg_left (by linarith [hu.1]) (sq_nonneg β)⟩
  have H := section4U_sub_ge_supportingLine s β h hr0 hr hm hv ht
  unfold section4FirstVariation
  nlinarith only [H]

/-- When the actual factor equals the specified overlap, the supporting-line
error disappears. A separately proved lower bound on the first variation can
then be inserted without asserting optimality or stationarity here. -/
theorem section4U_interpolation_slope_lower_bound_of_factor_eq {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) {u t e : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) (ht : t ∈ Set.Icc 0 1)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) = u)
    (hf : -e ≤ section4FirstVariation s β h r u) :
    -2 * e + (1 - t) * (β ^ 2 / 2) * (s.q r - u) ^ 2 ≤
      section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
        t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2) := by
  have H := section4U_interpolation_slope_lower_bound s β h hr0 hr hm hu ht
  rw [hQ, sub_self, mul_zero, sub_zero] at H
  linarith

end SpinGlass.Targets
