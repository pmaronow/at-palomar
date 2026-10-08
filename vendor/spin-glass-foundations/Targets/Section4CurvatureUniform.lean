module

public import Targets.Section4HessianUniform
public import Targets.Section4CurvatureRegularity

@[expose] public section

/-!
# Uniform Taylor and curvature estimates

The proved universal Hessian-square bound discharges the analytic hypothesis
in the earlier Taylor and sixth-root estimates. The remaining hypotheses are
the actual scheme's admissibility, fixed-level minimality and near-optimality.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The actual first variation's cubic Taylor estimate on the full closed
overlap interval, without any assumed regularity bound. -/
theorem section4FirstVariation_cubic_taylor_uniform {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) {u w : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4FirstVariation s β h r u - section4FirstVariation s β h r w -
      section4FirstVariationD s β h r w * (u - w) -
      section4FirstVariationD2 s β h r w / 2 * (u - w) ^ 2| ≤
      (β ^ 6 * 535 / 2) * |u - w| ^ 3 :=
  section4FirstVariation_cubic_taylor_of_hessian_lipschitz s β h hr0 hr hm
    (by norm_num : (0 : ℝ) ≤ 535)
    (fun v hv w hw => section4THessianSquare_lipschitz_uniform s β h hr0 hr hv hw) hu hw

/-- Proposition 4.10's sixth-root bound at every physical positive-gap
level. The uniform analytic constant is now proved, not an extra hypothesis;
the initial zero mass and compulsory final mass are included. -/
theorem section4FirstVariation_curvature_bound_uniform {k : ℕ} (s : RSBScheme k)
    (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    -section4FirstVariationD2 s β h r (s.q r) ≤
      2 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ) :=
  section4FirstVariation_curvature_bound_of_hessian_lipschitz_all_levels s β h ε
    hr0 hr hβ hm hleft hright hmin hnear (by norm_num : (0 : ℝ) ≤ 535)
    (fun v hv w hw => section4THessianSquare_lipschitz_uniform s β h hr0 hr hv hw)

end SpinGlass.Targets
