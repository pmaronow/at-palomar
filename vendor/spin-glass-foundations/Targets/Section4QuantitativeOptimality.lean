module

public import Targets.Section4MassTaylor

@[expose] public section

/-!
# Quantitative optimality of the actual inserted Parisi functional

Talagrand, Proposition 4.6, equation (4.52). The uniform mass Taylor bound
already proved in `Section4MassTaylor` is combined with the actual competitors
of `Section4InsertedScheme`. The strict adjacent mass gap is the assumption
(2.19) used in the paper; the lower adjacent mass is allowed to be zero.
-/

open Real

namespace SpinGlass.Targets

theorem firstVariation_sq_le_of_quadratic_comparisons
    {C a b ε f : ℝ} (hC : 0 < C) (hab : a < b) (hf : f < 0)
    (hupper : 0 ≤ f * (b - a) + C * (b - a) ^ 2)
    (hnear : ∀ δ ∈ Set.Icc (0 : ℝ) (b - a), -ε ≤ f * δ + C * δ ^ 2) :
    f ^ 2 ≤ 4 * C * ε := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hprod : 0 ≤ (f + C * (b - a)) * (b - a) := by nlinarith [hupper]
  have hslope : 0 ≤ f + C * (b - a) := nonneg_of_mul_nonneg_left hprod hgap
  let δ := -f / (2 * C)
  have hden : 0 < 2 * C := by positivity
  have hδ0 : 0 ≤ δ := div_nonneg (neg_nonneg.mpr hf.le) hden.le
  have hδgap : δ ≤ b - a := by
    dsimp [δ]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hC.le hgap.le]
  have H := mul_le_mul_of_nonneg_left (hnear δ ⟨hδ0, hδgap⟩)
    (show 0 ≤ 4 * C by positivity)
  have hid : 4 * C * (f * δ + C * δ ^ 2) = -f ^ 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hC]
    ring
  rw [hid] at H
  nlinarith

/-- A positive beta-only constant in Proposition 4.6. It is uniform in the
number of levels, the external field, the overlap and the adjacent mass gap. -/
noncomputable def section4OptimalityBound (β : ℝ) : ℝ :=
  2 * Real.sqrt (section4MassSecondBound (β ^ 2) + 1)

theorem section4OptimalityBound_pos (β : ℝ) : 0 < section4OptimalityBound β := by
  unfold section4OptimalityBound
  have hC := section4MassSecondBound_nonneg (β ^ 2)
  positivity

/-- Talagrand's Proposition 4.6, (4.52), for the actual first variation (4.46).
The hypotheses are fixed-level minimality, near-global minimality and the
strict adjacent mass gap from (2.19). No positive lower bound on the gap is
required, and the baseline mass may be zero. -/
theorem section4FirstVariation_lower_bound {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    -section4OptimalityBound β * Real.sqrt ε ≤ section4FirstVariation s β h r u := by
  let C := section4MassSecondBound (β ^ 2) + 1
  have hC : 0 < C := by dsimp [C]; linarith [section4MassSecondBound_nonneg (β ^ 2)]
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  by_cases hf : 0 ≤ section4FirstVariation s β h r u
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (section4OptimalityBound_pos β).le) (Real.sqrt_nonneg ε)) hf
  have hTaylor (m : ℝ) (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r)) :
      section4Phi s β h r m u - parisiFunctional s β h ≤
        section4FirstVariation s β h r u * (m - s.m (r - 1)) +
          C * (m - s.m (r - 1)) ^ 2 := by
    have H := (abs_le.mp (section4Phi_mass_taylor_baseline s β h hr0 hr
      ⟨hm.1, hm.2.trans (s.m_le_one hr)⟩ hu)).2
    dsimp [C]
    nlinarith [sq_nonneg (m - s.m (r - 1))]
  have hupper : 0 ≤ section4FirstVariation s β h r u * (s.m r - s.m (r - 1)) +
      C * (s.m r - s.m (r - 1)) ^ 2 := by
    have H := section4Phi_upper_mass_min s β h hr0 hr hu hmin
    rw [section4Phi_baseline s β h hr0 hr hu] at H
    linarith [hTaylor (s.m r) ⟨hgap.le, le_rfl⟩]
  have hcomp (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (s.m r - s.m (r - 1))) :
      -ε ≤ section4FirstVariation s β h r u * δ + C * δ ^ 2 := by
    have hm : s.m (r - 1) + δ ∈ Set.Icc (s.m (r - 1)) (s.m r) := by
      constructor <;> linarith [hδ.1, hδ.2]
    have H := section4Phi_near_min s β h ε hr0 hr hm hu hnear
    rw [section4Phi_baseline s β h hr0 hr hu] at H
    have HT := hTaylor (s.m (r - 1) + δ) hm
    simp only [add_sub_cancel_left] at HT
    linarith
  have hsq := firstVariation_sq_le_of_quadratic_comparisons hC hgap (lt_of_not_ge hf)
    hupper hcomp
  have H : -section4FirstVariation s β h r u ≤ Real.sqrt (4 * C * ε) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [neg_sq] using hsq
  have hsqrt : Real.sqrt (4 * C * ε) = section4OptimalityBound β * Real.sqrt ε := by
    rw [Real.sqrt_mul' (4 * C) hε, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [section4OptimalityBound, C]
  rw [hsqrt] at H
  linarith

/-- The uniform quantifier order in Proposition 4.6: choose the constant before
the level count, external field, scheme, interval and near-optimality tolerance. -/
theorem exists_section4FirstVariation_lower_bound (β : ℝ) :
    ∃ L > 0, ∀ {k : ℕ} (s : RSBScheme k) (h ε : ℝ) {r : ℕ},
      1 ≤ r → r ≤ k + 1 → s.m (r - 1) < s.m r →
      ∀ {u : ℝ}, u ∈ Set.Icc (s.q (r - 1)) (s.q r) →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      -L * Real.sqrt ε ≤ section4FirstVariation s β h r u := by
  refine ⟨section4OptimalityBound β, section4OptimalityBound_pos β, ?_⟩
  intro k s h ε r hr0 hr hgap u hu hmin hnear
  exact section4FirstVariation_lower_bound s β h ε hr0 hr hgap hu hmin hnear

end SpinGlass.Targets
