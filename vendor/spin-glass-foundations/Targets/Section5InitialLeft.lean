module

public import Targets.Section5LocalLeft
public import Targets.Section4InitialHessian

@[expose] public section

/-!
# The whole initial left interval in Proposition 5.3

On the initial zero-mass interval the actual Hessian-square factor never
exceeds its value at zero variance. Endpoint stationarity and curvature thus
control the lambda slope throughout the whole interval, with no local-overlap
smallness restriction. The existing lambda gain gives a quadratic deficit for
the actual constrained free energy relative to twice the interpolation bound.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The initial lambda slope has the required linear lower bound on its
entire physical overlap interval. Jensen replaces the local Lipschitz error. -/
theorem section5LeftSlope_initial_ge_of_endpoint_curvature
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {t t₀ u e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 (s.q 1))
    (hQ : section4TVarianceQ s β h 1 (s.m 0) 0 = s.q 1)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 2) :
    (1 - t₀) / 2 * (s.q 1 - u) ≤ section5LeftSlope s β h 1 t u := by
  have ht1 : t ∈ Set.Icc 0 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hsub : Set.Icc u (s.q 1) ⊆ Set.Icc (s.q (1 - 1)) (s.q 1) := by
    simpa only [Nat.sub_self, s.q_zero] using Set.Icc_subset_Icc hu.1 (le_refl (s.q 1))
  have hderiv (z : ℝ) (hz : z ∈ Set.Icc u (s.q 1)) :
      HasDerivWithinAt (section5LeftSlope s β h 1 t)
        (t * β ^ 2 * section4THessianSquare s β h 1 (t * (β ^ 2 * (s.q 1 - z))) - 1)
        (Set.Icc u (s.q 1)) z :=
    (hasDerivWithinAt_section5LeftSlope s β h (r := 1) le_rfl (by omega) ht1 (hsub hz)).mono hsub
  have hbound (z : ℝ) (hz : z ∈ Set.Icc u (s.q 1)) :
      t * β ^ 2 * section4THessianSquare s β h 1 (t * (β ^ 2 * (s.q 1 - z))) - 1 ≤
        -(1 - t₀) / 2 := by
    have hv : t * (β ^ 2 * (s.q 1 - z)) ∈ Set.Icc 0 (β ^ 2 * s.q 1) := by
      simpa only [Nat.sub_self, s.q_zero, sub_zero] using
        section5SplitVariance_mem s β ht1 (hsub hz)
    have HR := section4THessianSquare_initial_le_zero s β h hv
    have Hscaled := mul_le_mul_of_nonneg_left HR (mul_nonneg ht.1 (sq_nonneg β))
    have Hbase := mul_le_mul_of_nonneg_left hR ht.1
    have He := mul_le_of_le_one_left he ht1.2
    nlinarith only [Hscaled, Hbase, He, ht.2, he_small]
  have hc : ContinuousOn (section5LeftSlope s β h 1 t) (Set.Icc u (s.q 1)) :=
    fun z hz => (hderiv z hz).continuousWithinAt
  have hd : DifferentiableOn ℝ (section5LeftSlope s β h 1 t) (interior (Set.Icc u (s.q 1))) := by
    rw [interior_Icc]
    exact fun z hz => ((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt
      (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
  have HB : ∀ z ∈ interior (Set.Icc u (s.q 1)), deriv (section5LeftSlope s β h 1 t) z ≤
      -(1 - t₀) / 2 := by
    rw [interior_Icc]
    intro z hz
    rw [((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).deriv]
    exact hbound z ⟨hz.1.le, hz.2.le⟩
  have H := (convex_Icc u (s.q 1)).image_sub_le_mul_sub_of_deriv_le hc hd HB
    u ⟨le_rfl, hu.2⟩ (s.q 1) ⟨hu.2, le_rfl⟩ hu.2
  have Hzero : section5LeftSlope s β h 1 t (s.q 1) = 0 := by
    simp only [section5LeftSlope, sub_self, mul_zero, Nat.sub_self, hQ]
  rw [Hzero] at H
  linarith

/-- Original near-optimality supplies the initial curvature error needed by
both signs of the initial overlap. This packages the already checked
sixth-root estimate without assuming stationarity or a pressure inequality. -/
theorem section5Initial_curvature_data {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1) {t₀ L : ℝ} (hL : 0 ≤ L)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤ L * |v - w|) :
    32 ≤ section5LocalLeftConstant β L ∧ ∃ e : ℝ, 0 ≤ e ∧
      e ≤ (1 - t₀) / 2 ∧ β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hA : 0 ≤ β ^ 6 * L / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  have hc : 32 ≤ section5LocalLeftConstant β L ∧
      16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 ≤
        section5LocalLeftConstant β L := by
    have hp : 0 ≤ 4 * L * β ^ 4 := by positivity
    have hd : 0 ≤ 16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 := by positivity
    unfold section5LocalLeftConstant
    constructor <;> linarith
  let e := 4 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hA) hB.le) hη
  have he_small : e ≤ (1 - t₀) / 2 := by
    have H := mul_le_mul_of_nonneg_right hc.2 hη
    have he4 : 16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 *
        ε ^ (1 / 6 : ℝ) = 4 * e := by dsimp [e]; ring
    rw [he4] at H
    nlinarith only [H, hsmall, he]
  have Hcurv := section4FirstVariation_initial_curvature_bound_of_hessian_lipschitz
    s β h ε hβ hm hq hright hmin hnear hL hLip
  simp only [section4FirstVariationD2, sub_self, mul_zero] at Hcurv
  have hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e := by
    have H : β ^ 2 * section4THessianSquare s β h 1 0 - 1 ≤
        (4 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) / β ^ 2 := by
      apply (le_div_iff₀ hB).mpr
      nlinarith only [Hcurv]
    have heq : (4 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) /
        β ^ 2 = e := by dsimp [e]; ring
    rw [heq] at H
    linarith
  exact ⟨hc.1, e, he, he_small, hR⟩

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Proposition 5.3's quadratic deficit on the entire initial interval,
from the actual endpoint stationarity and curvature data. -/
theorem constrainedPhi_initial_left_of_endpoint_curvature
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t t₀ u e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 (s.q 1)) [Nonempty (AT.ConstrainedPair n u)]
    (hQ : section4TVarianceQ s β h 1 (s.m 0) 0 = s.q 1)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 2) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / 8 * (u - s.q 1) ^ 2 := by
  have Hslope := section5LeftSlope_initial_ge_of_endpoint_curvature s β h ht ht₀ he hu hQ hR he_small
  have H := constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk (r := 1) le_rfl (by omega)
    ⟨ht.1, ht.2.trans ht₀.le⟩ (by simpa only [Nat.sub_self, s.q_zero] using hu)
  change constrainedPhi n s β h sk.U (k + 2 - 1) t u ≤
    2 * guerraPsi s β h t - (section5LeftSlope s β h 1 t u) ^ 2 / 2 at H
  rw [show k + 2 - 1 = k + 1 by omega] at H
  have Hnonneg : 0 ≤ (1 - t₀) / 2 * (s.q 1 - u) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.2)
  have Hsquare := mul_self_le_mul_self Hnonneg Hslope
  nlinarith only [H, Hsquare]

/-- The actual initial-left estimate, conditional only on the actual Hessian
Lipschitz estimate used for endpoint curvature. The same explicit constant as
the local-left estimate is reused, but no local-overlap condition is imposed.
The constant depends only on beta and the supplied uniform Lipschitz constant.
The degenerate initial interval is included through its sole overlap endpoint. -/
theorem constrainedPhi_initial_left_of_hessian_lipschitz
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u L : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (hL : 0 ≤ L)
    (hu : u ∈ Set.Icc 0 (s.q 1)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤ L * |v - w|) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β L * (u - s.q 1) ^ 2 := by
  by_cases heq : u = s.q 1
  · subst u
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
    have H := constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk (r := 1) le_rfl (by omega)
      ⟨ht.1, ht.2.trans ht₀.le⟩ (by simpa only [Nat.sub_self, s.q_zero] using hu)
    rw [show k + 2 - 1 = k + 1 by omega] at H
    exact H.trans (sub_le_self _ (div_nonneg (sq_nonneg _) (by norm_num)))
  have hq : 0 < s.q 1 := hu.1.trans_lt (lt_of_le_of_ne hu.2 heq)
  obtain ⟨hc, e, he, he_small, hR⟩ :=
    section5Initial_curvature_data s β h ε hβ hm hq hright hL hmin hnear hsmall hLip
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h (r := 1) le_rfl (by omega)
    hβ (by simpa using hm) (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq)) hright hmin
  have H := constrainedPhi_initial_left_of_endpoint_curvature hn s β h sk ht ht₀ he hu hQ hR he_small
  have hcoeff : (1 - t₀) ^ 2 / section5LocalLeftConstant β L ≤ (1 - t₀) ^ 2 / 8 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith [hc])
  have Hgain := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u - s.q 1))
  linarith

end SpinGlass.Targets
