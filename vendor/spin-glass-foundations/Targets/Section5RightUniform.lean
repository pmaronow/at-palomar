module

public import Targets.Section5LocalRight
public import Targets.Section5LeftUniform
public import Targets.Section4NeighborFactors

@[expose] public section

/-!
# The uniform local-right estimate at all positive-left-gap levels

The dual baseline is the reflected next interval. Neighboring endpoint
identities transfer the original minimizer's stationarity and curvature to
that baseline. Thus the proved right lambda gain has a beta-only quadratic
deficit, with the same constant as the left estimate.

Terminal padding includes `r = k+1` without assuming minimality of the padded
scheme. This theorem retains a positive left overlap gap. The zero-first-overlap
case and the combined estimate for reduced schemes are in `Section5RightBoundary`.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The local-right bound with the proved universal regularity constant.
The positive left gap specifies the current completed scope;
no derivative, Lipschitz, lambda identification or pressure bound is assumed. -/
theorem constrainedPhi_local_right_uniform
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β 535 * (u - s.q r) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * (u - s.q r) ^ 2 := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hA : 0 ≤ β ^ 6 * 535 / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  have hc : 32 ≤ section5LocalLeftConstant β 535 ∧
      4 * 535 * β ^ 4 ≤ section5LocalLeftConstant β 535 ∧
      16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 ≤
        section5LocalLeftConstant β 535 := by
    have h₁ : 0 ≤ 4 * 535 * β ^ 4 := by positivity
    have h₂ : 0 ≤ 16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hA) hB.le
    unfold section5LocalLeftConstant
    constructor
    · linarith
    constructor <;> linarith
  let e := 4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hA) hB.le) hη
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    have he4 : 16 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) / β ^ 2 *
        ε ^ (1 / 6 : ℝ) = 4 * e := by dsimp [e]; ring
    rw [he4] at H
    linarith
  have hu_small : 535 * β ^ 4 * (u - s.q r) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hu.1)
    nlinarith only [H, hlocal]
  have hQ : section4RightQ s β h r 0 = s.q r := by
    rw [section4RightQ, sub_zero, section4TVarianceQ_neighbor_full_eq_zero_all_levels s β h hr0 hr]
    exact section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 (by omega)
      hβ hm (Or.inl hleft) hright hmin
  have Hcurv := section4FirstVariation_curvature_bound_uniform s β h ε hr0 (by omega)
    hβ hm hleft hright hmin hnear
  simp only [section4FirstVariationD2, sub_self, mul_zero] at Hcurv
  have hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e := by
    rw [section4RightR, sub_zero, section4THessianSquare_neighbor_full_eq_zero_all_levels s β h hr0 hr]
    have H : β ^ 2 * section4THessianSquare s β h r 0 - 1 ≤
        (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) / β ^ 2 := by
      apply (le_div_iff₀ hB).mpr
      nlinarith only [Hcurv]
    have heq : (4 * (β ^ 6 * 535 / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) /
        β ^ 2 = e := by dsimp [e]; ring
    rw [heq] at H
    linarith
  have H := constrainedPhi_local_right_of_endpoint_curvature hn s β h sk hr0 hr
    ht ht₀ he hu hQ hR he_small hu_small
  have hcoeff : (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 ≤ (1 - t₀) ^ 2 / 8 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith [hc.1])
  have Hgain := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u - s.q r))
  linarith

end SpinGlass.Targets
