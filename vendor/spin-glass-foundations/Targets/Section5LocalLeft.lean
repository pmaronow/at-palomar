module

public import Targets.Section5PressureGain
public import Targets.Section4CurvatureRegularity

@[expose] public section

/-!
# The local left overlap estimate of Proposition 5.1

The actual lambda slope is `Q(t β²(q_r-u)) - u`. Endpoint stationarity and
the curvature estimate bound its derivative, and Lipschitz regularity of
the actual Hessian-square factor controls that derivative locally. A
mean-value bound and the checked lambda gain then yield a quadratic deficit
for the actual constrained free energy relative to `2 ψ(t)`.

The beta-only, depth-uniform Lipschitz bound for the actual factor is still
an explicit analytic input, not a theorem claimed by this module.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The actual lambda slope in Talagrand (5.30). -/
noncomputable def section5LeftSlope {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (t u : ℝ) : ℝ :=
  section4TVarianceQ s β h r (s.m (r - 1)) (t * (β ^ 2 * (s.q r - u))) - u

/-- The actual lambda slope has the stated inward derivative, including
both overlap endpoints and time zero. -/
theorem hasDerivWithinAt_section5LeftSlope {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (section5LeftSlope s β h r t)
      (t * β ^ 2 * section4THessianSquare s β h r (t * (β ^ 2 * (s.q r - u))) - 1)
      (Set.Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : Set.MapsTo (fun z => t * (β ^ 2 * (s.q r - z)))
      (Set.Icc (s.q (r - 1)) (s.q r))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :=
    fun z hz => section5SplitVariance_mem s β ht hz
  have H := (hasDerivWithinAt_section4TVarianceQ_baseline s β h hr0 hr (hmap hu)).comp u
    ((((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2)).const_mul t).hasDerivWithinAt hmap
  unfold section5LeftSlope
  convert! H.sub ((hasDerivAt_id u).hasDerivWithinAt) using 1
  ring

/-- Local actual-slope control from an explicit endpoint curvature bound.
This is the derivative argument in (5.31)--(5.32), with endpoint-safe calculus.
No lower bound on the lambda slope itself is assumed. -/
theorem section5LeftSlope_ge_local_of_endpoint_curvature
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t t₀ u L e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    (hR : β ^ 2 * section4THessianSquare s β h r 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : L * β ^ 4 * (s.q r - u) ≤ (1 - t₀) / 4)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|) :
    (1 - t₀) / 2 * (s.q r - u) ≤ section5LeftSlope s β h r t u := by
  have ht1 : t ∈ Set.Icc 0 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hsub : Set.Icc u (s.q r) ⊆ Set.Icc (s.q (r - 1)) (s.q r) :=
    Set.Icc_subset_Icc hu.1 le_rfl
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (hu.1.trans hu.2))⟩
  have hderiv (z : ℝ) (hz : z ∈ Set.Icc u (s.q r)) :
      HasDerivWithinAt (section5LeftSlope s β h r t)
        (t * β ^ 2 * section4THessianSquare s β h r (t * (β ^ 2 * (s.q r - z))) - 1)
        (Set.Icc u (s.q r)) z :=
    (hasDerivWithinAt_section5LeftSlope s β h hr0 hr ht1 (hsub hz)).mono hsub
  have hbound (z : ℝ) (hz : z ∈ Set.Icc u (s.q r)) :
      t * β ^ 2 * section4THessianSquare s β h r (t * (β ^ 2 * (s.q r - z))) - 1 ≤
        -(1 - t₀) / 2 := by
    have hv := section5SplitVariance_mem s β ht1 (hsub hz)
    have hvle : t * (β ^ 2 * (s.q r - z)) ≤ β ^ 2 * (s.q r - u) :=
      (mul_le_of_le_one_left (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.2)) ht1.2).trans
        (mul_le_mul_of_nonneg_left (by linarith [hz.1]) (sq_nonneg β))
    have H := (abs_le.mp (hLip _ hv 0 hzero)).2
    rw [sub_zero, abs_of_nonneg hv.1] at H
    have HL := mul_le_mul_of_nonneg_left hvle hL
    have HR : section4THessianSquare s β h r (t * (β ^ 2 * (s.q r - z))) ≤
        section4THessianSquare s β h r 0 + L * β ^ 2 * (s.q r - u) := by
      nlinarith only [H, HL]
    have Hscaled := mul_le_mul_of_nonneg_left HR (mul_nonneg ht.1 (sq_nonneg β))
    have Hbase := mul_le_mul_of_nonneg_left hR ht.1
    have He := mul_le_of_le_one_left he ht1.2
    have Hlocal := mul_le_of_le_one_left
      (mul_nonneg (mul_nonneg hL (by positivity : 0 ≤ β ^ 4)) (sub_nonneg.mpr hu.2)) ht1.2
    nlinarith only [Hscaled, Hbase, He, Hlocal, ht.2, he_small, hu_small]
  have hc : ContinuousOn (section5LeftSlope s β h r t) (Set.Icc u (s.q r)) :=
    fun z hz => (hderiv z hz).continuousWithinAt
  have hd : DifferentiableOn ℝ (section5LeftSlope s β h r t) (interior (Set.Icc u (s.q r))) := by
    rw [interior_Icc]
    exact fun z hz => ((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt
      (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
  have HB : ∀ z ∈ interior (Set.Icc u (s.q r)), deriv (section5LeftSlope s β h r t) z ≤
      -(1 - t₀) / 2 := by
    rw [interior_Icc]
    intro z hz
    rw [((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).deriv]
    exact hbound z ⟨hz.1.le, hz.2.le⟩
  have H := (convex_Icc u (s.q r)).image_sub_le_mul_sub_of_deriv_le hc hd HB
    u ⟨le_rfl, hu.2⟩ (s.q r) ⟨hu.2, le_rfl⟩ hu.2
  have Hzero : section5LeftSlope s β h r t (s.q r) = 0 := by
    simp only [section5LeftSlope, sub_self, mul_zero, hQ]
  rw [Hzero] at H
  linarith

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The local slope estimate gives a quadratic deficit for the actual
constrained free energy. This compares with `2 ψ(t)`, not `2 φ_N(t)`. -/
theorem constrainedPhi_local_left_of_endpoint_curvature
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t t₀ u L e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    (hR : β ^ 2 * section4THessianSquare s β h r 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : L * β ^ 4 * (s.q r - u) ≤ (1 - t₀) / 4)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have Hslope := section5LeftSlope_ge_local_of_endpoint_curvature s β h hr0 hr ht ht₀ hL he
    hu hQ hR he_small hu_small hLip
  have H := constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk hr0 hr
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  change constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
    2 * guerraPsi s β h t - (section5LeftSlope s β h r t u) ^ 2 / 2 at H
  have Hnonneg : 0 ≤ (1 - t₀) / 2 * (s.q r - u) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.2)
  have Hsquare := mul_self_le_mul_self Hnonneg Hslope
  nlinarith only [H, Hsquare]

/-- One explicit common constant for the two smallness conditions and the
quadratic deficit in Proposition 5.1. It depends only on beta and the supplied
Hessian-square Lipschitz constant, not on depth, field, scheme or system size. -/
noncomputable def section5LocalLeftConstant (β L : ℝ) : ℝ :=
  32 + 4 * L * β ^ 4 +
    16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2

/-- The common local-estimate constant dominates the coefficients needed
on both sides, including the zero-first-overlap boundary. -/
theorem section5LocalLeftConstant_bounds (β L : ℝ) (hL : 0 ≤ L) :
    32 ≤ section5LocalLeftConstant β L ∧
      4 * L * β ^ 4 ≤ section5LocalLeftConstant β L ∧
      16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 ≤
        section5LocalLeftConstant β L := by
  have hA : 0 ≤ β ^ 6 * L / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  have hB : 0 ≤ 4 * L * β ^ 4 := by positivity
  have hC : 0 ≤ 16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) hA) (sq_nonneg β)
  unfold section5LocalLeftConstant
  constructor
  · linarith
  · constructor <;> linarith

theorem section5LocalLeftConstant_pos (β L : ℝ) (hL : 0 ≤ L) :
    0 < section5LocalLeftConstant β L := by
  linarith [(section5LocalLeftConstant_bounds β L hL).1]

/-- The actual SK local-left estimate of Proposition 5.1, conditional only on
Lipschitz regularity of the actual Hessian-square factor. The two hypotheses
with the explicit beta-only constant are precisely the near-optimality and
local-overlap smallness requirements; no desired pressure estimate is assumed.

The initial mass-zero interval and compulsory last level are included. A
coincident left overlap is harmless because then the only admissible `u` is
the target overlap itself. The right-neighbor condition supplies the genuine
stationarity input and follows from the checked strict-overlap reduction. -/
theorem constrainedPhi_local_left_of_hessian_lipschitz
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u L : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (hL : 0 ≤ L)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β L * (s.q r - u) ≤ 1 - t₀)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      ∀ w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))),
        |section4THessianSquare s β h r v - section4THessianSquare s β h r w| ≤ L * |v - w|) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β L * (u - s.q r) ^ 2 := by
  by_cases heq : u = s.q r
  · subst u
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
    exact (constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk hr0 hr
      ⟨ht.1, ht.2.trans ht₀.le⟩ hu).trans
      (sub_le_self _ (div_nonneg (sq_nonneg _) (by norm_num)))
  have hleft : s.q (r - 1) < s.q r := hu.1.trans_lt (lt_of_le_of_ne hu.2 heq)
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  have hB : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hA : 0 ≤ β ^ 6 * L / 2 + section4OptimalityBound β := by
    have hO := (section4OptimalityBound_pos β).le
    positivity
  let e := 4 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 * ε ^ (1 / 6 : ℝ)
  have he : 0 ≤ e := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hA) hB.le) hη
  have hc := section5LocalLeftConstant_bounds β L hL
  have he_small : e ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.2 hη
    have he4 : 16 * (β ^ 6 * L / 2 + section4OptimalityBound β) / β ^ 2 *
        ε ^ (1 / 6 : ℝ) = 4 * e := by dsimp [e]; ring
    rw [he4] at H
    nlinarith only [H, hsmall]
  have hu_small : L * β ^ 4 * (s.q r - u) ≤ (1 - t₀) / 4 := by
    have H := mul_le_mul_of_nonneg_right hc.2.1 (sub_nonneg.mpr hu.2)
    nlinarith only [H, hlocal]
  have Hcurv := section4FirstVariation_curvature_bound_of_hessian_lipschitz_all_levels
    s β h ε hr0 hr hβ hm hleft hright hmin hnear hL hLip
  simp only [section4FirstVariationD2, sub_self, mul_zero] at Hcurv
  have hR : β ^ 2 * section4THessianSquare s β h r 0 ≤ 1 + e := by
    have H : β ^ 2 * section4THessianSquare s β h r 0 - 1 ≤
        (4 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) / β ^ 2 := by
      apply (le_div_iff₀ hB).mpr
      nlinarith only [Hcurv]
    have heq : (4 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ)) /
        β ^ 2 = e := by dsimp [e]; ring
    rw [heq] at H
    linarith
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ hm
    (Or.inl hleft) hright hmin
  have H := constrainedPhi_local_left_of_endpoint_curvature hn s β h sk hr0 hr ht ht₀ hL he
    hu hQ hR he_small hu_small hLip
  have hcoeff : (1 - t₀) ^ 2 / section5LocalLeftConstant β L ≤ (1 - t₀) ^ 2 / 8 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith [hc.1])
  have Hgain := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u - s.q r))
  linarith

end SpinGlass.Targets
