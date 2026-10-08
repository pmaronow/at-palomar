module

public import Targets.Section4ZeroOverlap
public import Targets.ParisiZeroOverlapDerivative

@[expose] public section

/-!
# The admissible right variation at zero first overlap

Lowering the first mass in the existing auxiliary base, inserting the original
mass, and merging equal masses gives genuine same-level competitors. For the
RS case, the existing terminal-base construction supplies the same variation.
The actual derivative is `beta^2 m_1 / 2 * (u - Q0(beta^2 u))`, with `Q0` the
unweighted squared-slope Gaussian mean. No padded minimality is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

private theorem varianceQ_zero_eq_scalar_integral {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) (m v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β r m 0 v x y =
      ∫ z, (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
        m v (y 0 + Real.sqrt (β ^ 2 * (s.q r - s.q (r - 1)) - v) * z)) ^ 2 *
        tiltWeight (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
          (parisiStep m v (parisiF s β (k + 2 - r))) (y 0) z ∂(gaussianReal 0 1) := by
  unfold section4VarianceQ pairedSecondMean
  exact pairedTiltMean_scalar_integral (measurable_parisiStep (parisiF_measurable s β _) m v)
    ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 m v).pow_const 2) _ _ y

/-- The nonterminal right comparator's actual normalized factor becomes an
unweighted scalar squared-slope mean when the first overlap is zero. -/
theorem section4TVarianceQ_zeroOverlap_stationarityBase {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hk : 1 ≤ k) (hq : s.q 1 = 0) (u : ℝ) :
    section4TVarianceQ (section4StationarityBase s 1 le_rfl hk) β h 2 (s.m 1)
      (β ^ 2 * (s.q 2 - u)) =
      zeroOuterSquaredSlope (parisiF s β k) (parisiFDeriv s β k)
        (s.m 1) (β ^ 2 * s.q 2) h (β ^ 2 * u) := by
  let b := section4StationarityBase s 1 le_rfl hk
  have hb0 : b.m 0 = 0 := b.m_zero
  have hb1 : b.m 1 = 0 := by
    simp [b, section4StationarityBase, RSBScheme.lowerMass, s.m_zero]
  have hq0 : b.q 0 = 0 := b.q_zero
  have hq1 : b.q 1 = 0 := hq
  have hq2 : b.q 2 = s.q 2 := rfl
  have hF : parisiF b β k = parisiF s β k :=
    parisiF_lowerMass_prefix s β 1 le_rfl hk _ _ (by omega)
  have hFD : parisiFDeriv b β k = parisiFDeriv s β k :=
    parisiFDeriv_lowerMass_prefix s β 1 le_rfl hk _ _ (by omega)
  change section4VarianceQ b β 2 (s.m 1) 1 (β ^ 2 * (s.q 2 - u)) 0 (fun _ => h) = _
  rw [section4VarianceQ]
  simp only [Nat.add_zero, show k + 2 - 2 = k by omega,
    show k + 2 - (k + 2) = 0 by omega, hb0, hq1, hq0, sub_self, mul_zero,
    pairedSecondMean_zero_variance]
  rw [varianceQ_zero_eq_scalar_integral]
  simp only [Nat.reduceSub, show k + 2 - 2 = k by omega, hb1, hq1, hq2,
    sub_zero, hF, hFD, tiltWeight, if_true, mul_one]
  have hi : β ^ 2 * (s.q 2 - u) = β ^ 2 * s.q 2 - β ^ 2 * u := by ring
  simp only [hi, zeroOuterSquaredSlope, sub_sub_cancel]

/-- The terminal auxiliary base supplies the identical scalar factor for
the RS case, where the compulsory first mass cannot be lowered. -/
theorem section4TVarianceQ_zeroOverlap_terminalBase (s : RSBScheme 0) (β h u : ℝ) :
    section4TVarianceQ (section4TerminalBase s) β h 1 1 (β ^ 2 * (s.q 2 - u)) =
      zeroOuterSquaredSlope (parisiF s β 0) (parisiFDeriv s β 0)
        (s.m 1) (β ^ 2 * s.q 2) h (β ^ 2 * u) := by
  let b := section4TerminalBase s
  have hF : parisiF b β 1 = parisiF s β 0 := by
    funext x
    simp [b, section4TerminalBase, parisiF, s.q_top, parisiStep_zero_var]
  have hFD : parisiFDeriv b β 1 = parisiFDeriv s β 0 := by
    funext x
    have H := (parisiF_C2_props b β 1).1.1 x
    rw [hF] at H
    exact H.unique ((parisiF_C2_props s β 0).1.1 x)
  change section4VarianceQ b β 1 1 0 (β ^ 2 * (s.q 2 - u)) 0 (fun _ => h) = _
  rw [varianceQ_zero_eq_scalar_integral]
  simp only [Nat.reduceSub, hF, hFD, b.m_zero, b.q_zero, sub_zero,
    show b.q 1 = 1 by simp [b, section4TerminalBase],
    show s.q 2 = 1 from s.q_top, show s.m 1 = 1 from s.m_top,
    mul_one, tiltWeight, if_true]
  have hi : β ^ 2 * (1 - u) = β ^ 2 - β ^ 2 * u := by ring
  simp only [hi, zeroOuterSquaredSlope, sub_sub_cancel]

/-- A genuine same-level minimizing right comparator exists at zero first
overlap. Its derivative is identified throughout the closed admissible
interval, including zero. Only the original scheme's minimality is used.
The coefficient has the positive sign `beta^2 * m_1 / 2`. -/
theorem exists_section4ZeroOverlap_comparator {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hq : s.q 1 = 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∃ f : ℝ → ℝ,
      (∀ u ∈ Set.Icc 0 (s.q 2), f 0 ≤ f u) ∧
      (∀ u ∈ Set.Icc 0 (s.q 2),
        HasDerivWithinAt f
          (β ^ 2 * s.m 1 / 2 * (u - zeroOuterSquaredSlope (parisiF s β k)
            (parisiFDeriv s β k) (s.m 1) (β ^ 2 * s.q 2) h (β ^ 2 * u)))
          (Set.Icc 0 (s.q 2)) u) := by
  cases k with
  | zero =>
    let b := section4TerminalBase s
    refine ⟨section4Phi b β h 1 1, ?_, ?_⟩
    · intro u hu
      have H := section4Phi_terminalBase_min s β h hmin
        (u := u) (by simpa only [s.q_zero, s.q_top] using hu)
      simpa only [Nat.zero_add, hq] using H
    · intro u hu
      have hbq0 : b.q 0 = 0 := b.q_zero
      have hbq1 : b.q 1 = s.q 2 := by simp [b, section4TerminalBase, s.q_top]
      have hd := hasDerivWithinAt_section4Phi_overlap b β h (r := 1) le_rfl le_rfl
        (m := 1) ⟨zero_le_one, le_rfl⟩ (by simpa only [Nat.reduceSub, b.m_zero] using zero_le_one)
        (u := u) (by simpa only [Nat.reduceSub, hbq0, hbq1] using hu)
      rw [show 1 - 1 = (0 : ℕ) by decide, b.m_zero, sub_zero, hbq0, hbq1,
        section4TVarianceQ_zeroOverlap_terminalBase s β h u] at hd
      simpa only [s.m_top, mul_one] using hd
  | succ k =>
    have hk : 1 ≤ k + 1 := by omega
    let b := section4StationarityBase s 1 le_rfl hk
    refine ⟨section4Phi b β h 2 (s.m 1), ?_, ?_⟩
    · intro u hu
      have H := section4Phi_stationarityBase_min s β h (r := 1) le_rfl hk hmin
        (u := u) (by simpa only [hq] using hu)
      simpa only [hq] using H
    · intro u hu
      have hbm1 : b.m 1 = 0 := by
        simp [b, section4StationarityBase, RSBScheme.lowerMass, s.m_zero]
      have hbq1 : b.q 1 = 0 := hq
      have hbq2 : b.q 2 = s.q 2 := rfl
      have hd := hasDerivWithinAt_section4Phi_overlap b β h (r := 2) (by omega) (by omega)
        (m := s.m 1) ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
        (by simpa only [Nat.reduceSub, hbm1] using s.m_nonneg (p := 1) (by omega))
        (u := u) (by simpa only [Nat.reduceSub, hbq1, hbq2] using hu)
      rw [show 2 - 1 = (1 : ℕ) by decide, hbm1, sub_zero, hbq1, hbq2,
        section4TVarianceQ_zeroOverlap_stationarityBase s β h hk hq u] at hd
      exact hd

end SpinGlass.Targets
