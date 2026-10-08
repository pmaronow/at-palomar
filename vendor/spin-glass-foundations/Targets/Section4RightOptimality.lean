module

public import Targets.Section4RightInsertedScheme
public import Targets.Section4RightMassSecond
public import Targets.Section4QuantitativeOptimality

@[expose] public section

/-!
# Quantitative optimality of the actual right first variation

The scalar right insertion varies its lower-interval mass downward from the
original mass. Thus the dual first variation has an upper, rather than lower,
near-optimality bound. The actual inserted-scheme comparisons and uniform
mass Taylor estimate retain zero lower masses and the terminal interval.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The mass derivative of the corrected actual dual scalar construction. -/
noncomputable def section4RightFirstVariation {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) (u : ℝ) : ℝ :=
  section4RightU s β h r (β ^ 2 * (u - s.q r)) / 2 -
    β ^ 2 / 4 * (u ^ 2 - s.q r ^ 2)

/-- The dual first variation is the genuine baseline mass derivative of
the corrected right functional, not an assumed variation formula. -/
theorem hasDerivAt_section4RightPhi_mass_baseline {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    HasDerivAt (fun m => section4RightPhi s β h r m u)
      (section4RightFirstVariation s β h r u) (s.m r) := by
  have H := hasDerivAt_section4RightT_mass_baseline s β h hr
    (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1))
  have HD := ((hasDerivAt_id (s.m r)).const_sub (s.m r)).mul_const
    (β ^ 2 / 4 * (u ^ 2 - s.q r ^ 2))
  convert! ((H.const_add (Real.log 2)).sub_const (parisiCorrection s β)).add HD using 1
  unfold section4RightFirstVariation
  ring

/-- Uniform actual Taylor expansion at the right baseline, on both sides
within physical scalar masses `[0,1]`. The affine correction adds no error. -/
theorem section4RightPhi_mass_taylor_baseline {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    |section4RightPhi s β h r m u - parisiFunctional s β h -
      section4RightFirstVariation s β h r u * (m - s.m r)| ≤
      section4MassSecondBound (β ^ 2) * (m - s.m r) ^ 2 := by
  have hv : β ^ 2 * (u - s.q r) ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1),
      mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 _) (sq_nonneg β)⟩
  have H := section4RightT_mass_taylor_bound s β h hr
    ⟨s.m_nonneg hr, s.m_le_one hr⟩ hm hv
  rw [(hasDerivAt_section4RightT_mass_baseline s β h hr hv.1).deriv,
    section4RightT_baseline s β h hr hv] at H
  convert! H using 1
  unfold section4RightPhi section4RightFirstVariation parisiFunctional parisiCorrection
  congr 1
  ring

/-- The dual of Proposition 4.6 for the actual right variation. Fixed-level
minimality controls the lower-mass endpoint, and near-global minimality
controls all admissible right insertions. No positive mass-gap lower bound
or padded-scheme minimality is assumed. -/
theorem section4RightFirstVariation_upper_bound {k : ℕ} (s : RSBScheme k)
    (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hgap : s.m (r - 1) < s.m r) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    section4RightFirstVariation s β h r u ≤ section4OptimalityBound β * Real.sqrt ε := by
  let C := section4MassSecondBound (β ^ 2) + 1
  have hC : 0 < C := by dsimp [C]; linarith [section4MassSecondBound_nonneg (β ^ 2)]
  have hε : 0 ≤ ε := by linarith [parisiValue_le s β h]
  by_cases hf : section4RightFirstVariation s β h r u ≤ 0
  · exact hf.trans (mul_nonneg (section4OptimalityBound_pos β).le (Real.sqrt_nonneg ε))
  have hTaylor (m : ℝ) (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r)) :
      section4RightPhi s β h r m u - parisiFunctional s β h ≤
        section4RightFirstVariation s β h r u * (m - s.m r) + C * (m - s.m r) ^ 2 := by
    have H := (abs_le.mp (section4RightPhi_mass_taylor_baseline s β h hr
      ⟨(s.m_nonneg (by omega)).trans hm.1, hm.2.trans (s.m_le_one hr)⟩ hu)).2
    dsimp [C]
    nlinarith [sq_nonneg (m - s.m r)]
  have hlower : 0 ≤ -section4RightFirstVariation s β h r u * (s.m r - s.m (r - 1)) +
      C * (s.m r - s.m (r - 1)) ^ 2 := by
    have H := section4RightPhi_lower_mass_min s β h hr0 hr hu hmin
    rw [section4RightPhi_baseline s β h hr hu] at H
    nlinarith only [H, hTaylor (s.m (r - 1)) ⟨le_rfl, hgap.le⟩]
  have hcomp (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (s.m r - s.m (r - 1))) :
      -ε ≤ -section4RightFirstVariation s β h r u * δ + C * δ ^ 2 := by
    have hm : s.m r - δ ∈ Set.Icc (s.m (r - 1)) (s.m r) := by
      constructor <;> linarith [hδ.1, hδ.2]
    have H := section4RightPhi_near_min s β h ε hr0 hr hm hu hnear
    rw [section4RightPhi_baseline s β h hr hu] at H
    nlinarith only [H, hTaylor (s.m r - δ) hm]
  have hsq := firstVariation_sq_le_of_quadratic_comparisons hC hgap
    (neg_neg_of_pos (lt_of_not_ge hf)) hlower hcomp
  rw [neg_sq] at hsq
  have H : section4RightFirstVariation s β h r u ≤ Real.sqrt (4 * C * ε) :=
    Real.le_sqrt_of_sq_le hsq
  have hsqrt : Real.sqrt (4 * C * ε) = section4OptimalityBound β * Real.sqrt ε := by
    rw [Real.sqrt_mul' (4 * C) hε, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [section4OptimalityBound, C]
  rwa [hsqrt] at H

end SpinGlass.Targets
