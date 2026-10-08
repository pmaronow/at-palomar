module

public import Targets.Section4QuantitativeOptimality
public import Targets.Section4EndpointOptimality
public import Targets.Section4StationarityTerminal
public import Targets.Section4HessianRegularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The deterministic curvature argument of Proposition 4.10

The two-gap argument uses the nonnegative value at the lower endpoint, the
uniform lower bound from Proposition 4.6, and a cubic Taylor remainder at the
stationary upper endpoint. The cubic remainder is an explicit input here:
the uniform higher regularity needed to prove it for the actual Section 4
function is not asserted by this module.
-/

open Real

namespace SpinGlass.Targets

private theorem neg_curvature_le_of_cubic_upper_pos
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hab : a < b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 < η) (hleft : 0 ≤ f a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  by_cases hgap : b - a ≤ η
  · have H := hupper a ⟨le_rfl, hab.le⟩
    have Hprod : 0 ≤ (κ / 2 + C * (b - a)) * (b - a) ^ 2 := by
      nlinarith only [H, hleft]
    have Hslope := nonneg_of_mul_nonneg_left Hprod (sq_pos_of_pos (sub_pos.mpr hab))
    have HC := mul_le_mul_of_nonneg_left hgap hC
    nlinarith [mul_nonneg hL hη.le]
  · have hu : b - η ∈ Set.Icc a b := by constructor <;> linarith
    have H := (hlower (b - η) hu).trans (hupper (b - η) hu)
    have Hprod : 0 ≤ (κ / 2 + (C + L) * η) * η ^ 2 := by
      nlinarith only [H]
    have Hslope := nonneg_of_mul_nonneg_left Hprod (sq_pos_of_pos hη)
    linarith

/-- Talagrand's two-gap curvature argument. When the interval is shorter than
`η`, its lower endpoint controls the curvature; otherwise one tests at `b-η`.
The case `η=0` is included by arbitrarily small positive tests. This theorem
requires only the upper cubic remainder, not an unproved third derivative. -/
theorem neg_curvature_le_of_cubic_upper
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hab : a < b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hleft : 0 ≤ f a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  rcases eq_or_lt_of_le hη with hzero | hpos
  · subst η
    simp only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] at hlower ⊢
    by_contra hn
    have hκ : 0 < -κ := lt_of_not_ge hn
    let δ := -κ / (4 * (C + L + 1))
    have hden : 0 < 4 * (C + L + 1) := by linarith
    have hδ : 0 < δ := div_pos hκ hden
    have H := neg_curvature_le_of_cubic_upper_pos hab hC hL hδ hleft
      (fun u hu => (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL)
        (pow_nonneg hδ.le 3)).trans (hlower u hu))
      hupper
    have he : δ * (4 * (C + L + 1)) = -κ := by
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith only [H, he, hδ, mul_nonneg hC hδ.le, mul_nonneg hL hδ.le]
  · exact neg_curvature_le_of_cubic_upper_pos hab hC hL hpos hleft hlower hupper

/-- A stationary quadratic Taylor expansion with cubic remainder yields the
sixth-root curvature rate in Proposition 4.10. Here `κ` is the actual supplied
quadratic coefficient, not a default endpoint value of `deriv (deriv f)`. -/
theorem neg_curvature_le_sixth_root_of_cubic_remainder
    {f : ℝ → ℝ} {a b κ C L ε : ℝ} (hab : a < b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hleft : 0 ≤ f a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * Real.sqrt ε ≤ f u)
    (hcubic : ∀ u ∈ Set.Icc a b,
      |f u - κ / 2 * (u - b) ^ 2| ≤ C * |u - b| ^ 3) :
    -κ ≤ 2 * (C + L) * ε ^ (1 / 6 : ℝ) := by
  have hpower : (ε ^ (1 / 6 : ℝ)) ^ (3 : ℕ) = Real.sqrt ε := by
    rw [← Real.rpow_mul_natCast hε, Real.sqrt_eq_rpow]
    norm_num
  apply neg_curvature_le_of_cubic_upper hab hC hL (Real.rpow_nonneg hε _) hleft
  · simpa only [hpower] using hlower
  · intro u hu
    have H := (abs_le.mp (hcubic u hu)).2
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2)] at H
    nlinarith only [H]

/-- The actual first-variation slope, including its physical endpoint values. -/
noncomputable def section4FirstVariationD {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (u : ℝ) : ℝ :=
  β ^ 2 / 2 * (u - section4TVarianceQ s β h r (s.m (r - 1))
    (β ^ 2 * (s.q r - u)))

/-- The explicit curvature factor determined by the actual Hessian-square
observable. Its interpretation as an endpoint derivative requires inward
derivatives, not an unrestricted `deriv` at zero variance. -/
noncomputable def section4FirstVariationD2 {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (u : ℝ) : ℝ :=
  β ^ 2 / 2 * (1 - β ^ 2 * section4THessianSquare s β h r
    (β ^ 2 * (s.q r - u)))

/-- The explicit first coefficient is the genuine inward derivative of the
actual first variation at every point of the physical overlap interval. -/
theorem hasDerivWithinAt_section4FirstVariation_D {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (section4FirstVariation s β h r) (section4FirstVariationD s β h r u)
      (Set.Icc (s.q (r - 1)) (s.q r)) u :=
  hasDerivWithinAt_section4FirstVariation_overlap s β h hr0 hr hm hu

/-- The actual curvature coefficient is the inward derivative of the actual
slope throughout the closed physical overlap interval. No positive beta or
variance gap is needed for this derivative statement. -/
theorem hasDerivWithinAt_section4FirstVariationD_D2 {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (section4FirstVariationD s β h r) (section4FirstVariationD2 s β h r u)
      (Set.Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : Set.MapsTo (fun z => β ^ 2 * (s.q r - z))
      (Set.Icc (s.q (r - 1)) (s.q r))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
    intro z hz
    exact ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left (by linarith [hz.1]) (sq_nonneg β)⟩
  have H := (hasDerivWithinAt_section4TVarianceQ_baseline s β h hr0 hr (hmap hu)).comp u
    (((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2)).hasDerivWithinAt hmap
  unfold section4FirstVariationD section4FirstVariationD2
  convert! (((hasDerivAt_id u).hasDerivWithinAt).sub H).const_mul (β ^ 2 / 2) using 1
  ring

/-- Actual second inward differentiation, with endpoint uniqueness justified
by a positive overlap gap. It identifies the derivative of `derivWithin f`,
not the unrestricted default derivative at a boundary. -/
theorem hasDerivWithinAt_derivWithin_section4FirstVariation {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) (hgap : s.q (r - 1) < s.q r) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt
      (derivWithin (section4FirstVariation s β h r) (Set.Icc (s.q (r - 1)) (s.q r)))
      (section4FirstVariationD2 s β h r u) (Set.Icc (s.q (r - 1)) (s.q r)) u := by
  apply (hasDerivWithinAt_section4FirstVariationD_D2 s β h hr0 hr hu).congr_of_mem
    (fun z hz => (hasDerivWithinAt_section4FirstVariation_D s β h hr0 hr hm hz).derivWithin
      (uniqueDiffOn_Icc hgap z hz)) hu

/-- The numerical second inward derivative is the actual Hessian-square
formula, also at the upper overlap corresponding to zero split variance. -/
theorem derivWithin2_section4FirstVariation_eq {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1)
    (hgap : s.q (r - 1) < s.q r) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    derivWithin
      (derivWithin (section4FirstVariation s β h r) (Set.Icc (s.q (r - 1)) (s.q r)))
      (Set.Icc (s.q (r - 1)) (s.q r)) u = section4FirstVariationD2 s β h r u :=
  (hasDerivWithinAt_derivWithin_section4FirstVariation s β h hr0 hr hm hgap hu).derivWithin
    (uniqueDiffOn_Icc hgap u hu)

/-- Fixed-level stationarity identifies the explicit upper-endpoint slope
with zero, without assuming stationarity as an additional premise. -/
theorem section4FirstVariationD_upper_zero_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4FirstVariationD s β h r (s.q r) = 0 := by
  simp only [section4FirstVariationD, sub_self, mul_zero,
    section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ hm hleft hright hmin]

/-- Conditional actual-function form of Proposition 4.10. The sole analytic
input not discharged here is the displayed cubic Taylor remainder. Actual
fixed-level optimality supplies the endpoint stationarity and nonnegative
lower endpoint; actual near-optimality supplies Proposition 4.6's lower bound.
Thus this adapter does not assert the missing uniform higher regularity.

The presently checked lower-endpoint argument requires `r ≥ 2`; all remaining
physical levels, including `r = k + 1`, are covered subject to the specified
neighbor conditions. A positive overlap interval is needed to control its
upper-endpoint curvature. -/
theorem section4FirstVariation_curvature_lower_bound_of_cubic_remainder
    {k : ℕ} (s : RSBScheme k) (β h ε C : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1) (hC : 0 ≤ C)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hcubic : ∀ u ∈ Set.Icc (s.q (r - 1)) (s.q r),
      |section4FirstVariation s β h r u - section4FirstVariation s β h r (s.q r) -
        section4FirstVariationD s β h r (s.q r) * (u - s.q r) -
        section4FirstVariationD2 s β h r (s.q r) / 2 * (u - s.q r) ^ 2| ≤
        C * |u - s.q r| ^ 3) :
    -section4FirstVariationD2 s β h r (s.q r) ≤
      2 * (C + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ) := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  apply neg_curvature_le_sixth_root_of_cubic_remainder hleft hC
    (section4OptimalityBound_pos β).le hε
    (section4FirstVariation_lower_nonneg s β h hr0 (by omega) hm hmin)
  · exact fun u hu => section4FirstVariation_lower_bound s β h ε (by omega) (by omega)
      hm hu hmin hnear
  · intro u hu
    simpa only [section4FirstVariation_at_upper_overlap s β h (r := r) (by omega) (by omega),
      section4FirstVariationD_upper_zero_of_min s β h (by omega) hr hβ hm
        (Or.inl hleft) hright hmin, zero_mul, sub_zero] using hcubic u hu

end SpinGlass.Targets
