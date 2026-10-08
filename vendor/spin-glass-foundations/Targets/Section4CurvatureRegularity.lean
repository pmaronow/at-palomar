module

public import Targets.Section4CubicTaylor
public import Targets.Section4InitialCurvature

@[expose] public section

/-!
# Curvature reduction to actual Hessian-square regularity

The initial short interval uses its genuine `Q'=-R` integral bound, since its
compulsory zero mass cannot be varied. The long interval uses a cubic Taylor
test at distance `ε^(1/6)`. Combined with the noninitial two-gap argument,
this leaves one explicit analytic input: Lipschitz regularity of the actual
factor `R`. No depth-uniform Lipschitz estimate is claimed here.
-/

open Real

namespace SpinGlass.Targets

private theorem neg_curvature_le_long_gap_pos
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hη : 0 < η) (hgap : η ≤ b - a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  have hu : b - η ∈ Set.Icc a b := by constructor <;> linarith
  have H := (hlower (b - η) hu).trans (hupper (b - η) hu)
  have Hprod : 0 ≤ (κ / 2 + (C + L) * η) * η ^ 2 := by
    nlinarith only [H]
  have Hslope := nonneg_of_mul_nonneg_left Hprod (sq_pos_of_pos hη)
  linarith

private theorem neg_curvature_le_long_gap
    {f : ℝ → ℝ} {a b κ C L η : ℝ} (hab : a < b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hgap : η ≤ b - a)
    (hlower : ∀ u ∈ Set.Icc a b, -L * η ^ 3 ≤ f u)
    (hupper : ∀ u ∈ Set.Icc a b,
      f u ≤ κ / 2 * (b - u) ^ 2 + C * (b - u) ^ 3) :
    -κ ≤ 2 * (C + L) * η := by
  rcases eq_or_lt_of_le hη with hzero | hpos
  · subst η
    simp only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] at hlower ⊢
    by_contra hn
    have hκ : 0 < -κ := lt_of_not_ge hn
    let δ := min ((b - a) / 2) (-κ / (4 * (C + L + 1)))
    have hden : 0 < 4 * (C + L + 1) := by linarith
    have hδ : 0 < δ := lt_min (by linarith) (div_pos hκ hden)
    have hδgap : δ ≤ b - a := (min_le_left _ _).trans (by linarith)
    have H := neg_curvature_le_long_gap_pos hδ hδgap
      (fun u hu => (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL)
        (pow_nonneg hδ.le 3)).trans (hlower u hu)) hupper
    have he : δ * (4 * (C + L + 1)) ≤ -κ :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith only [H, he, hδ, mul_nonneg hC hδ.le, mul_nonneg hL hδ.le]
  · exact neg_curvature_le_long_gap_pos hpos hgap hlower hupper

/-- The sixth-root initial curvature bound, conditional only on actual `R`
Lipschitz regularity. No sign is assumed for `f(0)`. Both the short and long
initial intervals, including zero near-optimality tolerance, are covered. -/
theorem section4FirstVariation_initial_curvature_bound_of_hessian_lipschitz
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) (hβ : β ≠ 0)
    (hm : s.m 0 < s.m 1) (hq : 0 < s.q 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ v ∈ Set.Icc 0 (β ^ 2 * s.q 1), ∀ w ∈ Set.Icc 0 (β ^ 2 * s.q 1),
      |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤ L * |v - w|) :
    -section4FirstVariationD2 s β h 1 (s.q 1) ≤
      2 * (β ^ 6 * L / 2 + section4OptimalityBound β) * ε ^ (1 / 6 : ℝ) := by
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  have hη : 0 ≤ ε ^ (1 / 6 : ℝ) := Real.rpow_nonneg hε _
  by_cases hshort : s.q 1 ≤ ε ^ (1 / 6 : ℝ)
  · have H := section4FirstVariation_initial_short_curvature_bound s β h L ε hβ hm hq
      hright hL hshort hmin hLip
    have hc : L * β ^ 6 / 4 ≤ 2 * (β ^ 6 * L / 2 + section4OptimalityBound β) := by
      nlinarith [mul_nonneg hL (by positivity : 0 ≤ β ^ 6), (section4OptimalityBound_pos β).le]
    exact H.trans (mul_le_mul_of_nonneg_right hc hη)
  · have hpower : (ε ^ (1 / 6 : ℝ)) ^ (3 : ℕ) = Real.sqrt ε := by
      rw [← Real.rpow_mul_natCast hε, Real.sqrt_eq_rpow]
      norm_num
    apply neg_curvature_le_long_gap hq (by positivity) (section4OptimalityBound_pos β).le
      hη (by simpa only [sub_zero] using (lt_of_not_ge hshort).le)
      (f := section4FirstVariation s β h 1)
    · intro u hu
      rw [hpower]
      exact section4FirstVariation_lower_bound s β h ε (r := 1) le_rfl (by omega)
        (by simpa only [Nat.sub_self] using hm)
        (by simpa only [Nat.sub_self, s.q_zero] using hu) hmin hnear
    · intro u hu
      have H := (abs_le.mp (section4FirstVariation_stationary_cubic_of_hessian_lipschitz
        s β h (r := 1) le_rfl (by omega) hβ (by simpa only [Nat.sub_self] using hm)
        (Or.inl (by simpa only [Nat.sub_self, s.q_zero] using hq)) hright hmin hL
        (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hLip)
        (by simpa only [Nat.sub_self, s.q_zero] using hu))).2
      rw [abs_of_nonpos (sub_nonpos.mpr hu.2)] at H
      nlinarith only [H]

/-- Proposition 4.10's sixth-root curvature estimate for every physical
level with a positive overlap gap, conditional solely on the actual factor's
Lipschitz bound. The constant is depth-independent whenever `L` is. -/
theorem section4FirstVariation_curvature_bound_of_hessian_lipschitz_all_levels
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
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
  by_cases he : r = 1
  · subst r
    apply section4FirstVariation_initial_curvature_bound_of_hessian_lipschitz s β h ε hβ
      (by simpa only [Nat.sub_self] using hm)
      (by simpa only [Nat.sub_self, s.q_zero] using hleft)
      hright hmin hnear hL
    simpa only [Nat.sub_self, s.q_zero, sub_zero] using hLip
  · exact section4FirstVariation_curvature_lower_bound_of_hessian_lipschitz s β h ε
      (by omega) hr hβ hm hleft hright hmin hnear hL hLip

end SpinGlass.Targets
