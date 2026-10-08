module

/-
# Exact removal of leading zero masses

This is the leading-zero-mass part of Talagrand's reduction (2.19).
The first two scalar increments merge by the Gaussian semigroup, and a
zero-variance padding operation preserves the comparison class of minimizers.
No approximation of a minimizing scheme or transfer of optimality by continuity
is used. General interior coincidences are a separate reduction.
-/
public import Targets.TalagrandSection5Zero
public import Targets.TalagrandOverlapTail
public import Targets.RSBZeroMassPiSemigroup

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- Delete a zero first mass and merge the first two overlap intervals. -/
noncomputable def RSBScheme.dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) : RSBScheme k where
  m p := s.m (p + 1)
  q p := if p = 0 then 0 else s.q (p + 1)
  m_zero := hs
  m_top := by simpa [Nat.add_assoc] using s.m_top
  m_mono p hp := s.m_mono (p + 1) (by omega)
  q_zero := by simp
  q_top := by simpa [Nat.add_assoc] using s.q_top
  q_mono p hp := by
    by_cases hz : p = 0
    · subst p
      simpa using (s.q_nonneg (p := 2) (by omega))
    · simpa [hz] using s.q_mono (p + 1) (by omega)

/-- Add a redundant zero-mass, zero-variance first interval. This supplies a
competitor at the original level when transporting a fixed-level minimizer. -/
noncomputable def RSBScheme.padZeroFirst {k : ℕ} (s : RSBScheme k) : RSBScheme (k + 1) where
  m p := s.m (p - 1)
  q p := s.q (p - 1)
  m_zero := s.m_zero
  m_top := by simpa using s.m_top
  m_mono p hp := by
    by_cases hz : p = 0
    · simp [hz]
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using s.m_mono (p - 1) (by omega)
  q_zero := s.q_zero
  q_top := by simpa using s.q_top
  q_mono p hp := by
    by_cases hz : p = 0
    · simp [hz]
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ p)] using s.q_mono (p - 1) (by omega)

@[simp] theorem RSBScheme.padZeroFirst_mass_one {k : ℕ} (s : RSBScheme k) :
    s.padZeroFirst.m 1 = 0 := s.m_zero

@[simp] theorem RSBScheme.drop_padZeroFirst {k : ℕ} (s : RSBScheme k) :
    s.padZeroFirst.dropZeroFirst s.padZeroFirst_mass_one = s := by
  cases s
  dsimp only [dropZeroFirst, padZeroFirst]
  congr 1
  funext p
  simp only [Nat.add_sub_cancel]
  split_ifs with hp
  · subst p
    simp_all
  · rfl

/-- Before the two zero-mass steps, deletion only renames the levels. -/
theorem parisiF_dropZeroFirst_prefix {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β : ℝ) {j : ℕ} (hj : j ≤ k + 1) :
    parisiF (s.dropZeroFirst hs) β j = parisiF s β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp : k + 1 - j ≠ 0 := by omega
    have hp' : k + 2 - j ≠ 0 := by omega
    have hi : k + 1 - j + 1 = k + 1 + 1 - j := by omega
    have hi' : k + 2 - j + 1 = k + 1 + 2 - j := by omega
    rw [parisiF, parisiF, ih (by omega)]
    simp only [RSBScheme.dropZeroFirst, if_neg hp, if_neg hp', hi, hi']

/-- Exact preservation of the scalar endpoint, including degenerate increments. -/
theorem parisiF_dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β : ℝ) :
    parisiF (s.dropZeroFirst hs) β (k + 2) = parisiF s β (k + 1 + 2) := by
  have hv₁ : 0 ≤ β ^ 2 * s.q 1 := mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))
  have hv₂ : 0 ≤ β ^ 2 * (s.q 2 - s.q 1) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono 1 (by omega)))
  rw [show k + 2 = (k + 1) + 1 by omega, parisiF,
    parisiF_dropZeroFirst_prefix s hs β le_rfl]
  conv_rhs => rw [show k + 1 + 2 = ((k + 1) + 1) + 1 by omega, parisiF, parisiF]
  simp only [show k + 2 - (k + 1) = 1 by omega,
    show k + 1 + 2 - (k + 1 + 1) = 1 by omega,
    Nat.add_sub_cancel_left, Nat.sub_self,
    RSBScheme.dropZeroFirst, if_true, if_false, one_ne_zero, hs, s.m_zero, s.q_zero, sub_zero]
  have H := parisiStep_add 0 (β ^ 2 * s.q 1) (β ^ 2 * (s.q 2 - s.q 1)) hv₁ hv₂
    (parisiF_hasLinearGrowth s β (k + 1)) (parisiF_measurable s β (k + 1))
  convert H using 1
  congr 1
  ring

/-- The removed correction summand has zero mass. -/
theorem parisiCorrection_dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β : ℝ) :
    parisiCorrection (s.dropZeroFirst hs) β = parisiCorrection s β := by
  unfold parisiCorrection
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, hs, zero_mul, add_zero]
  congr 1

theorem parisiFunctional_dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β h : ℝ) :
    parisiFunctional (s.dropZeroFirst hs) β h = parisiFunctional s β h := by
  change Real.log 2 + parisiF (s.dropZeroFirst hs) β (k + 2) h -
      parisiCorrection (s.dropZeroFirst hs) β = _
  rw [parisiF_dropZeroFirst s hs β, parisiCorrection_dropZeroFirst s hs β]
  rfl

theorem guerraPsi_dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β h t : ℝ) :
    guerraPsi (s.dropZeroFirst hs) β h t = guerraPsi s β h t := by
  simp only [guerraPsi, parisiF_dropZeroFirst s hs β, parisiCorrection_dropZeroFirst s hs β]

theorem parisiFunctional_padZeroFirst {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    parisiFunctional s.padZeroFirst β h = parisiFunctional s β h := by
  simpa using (parisiFunctional_dropZeroFirst s.padZeroFirst s.padZeroFirst_mass_one β h).symm

/-- Exact fixed-level optimality transfer: every smaller competitor is padded
to a competitor at the original level with the same functional value. -/
theorem minimizer_dropZeroFirst {k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β h : ℝ)
    (hmin : ∀ s' : RSBScheme (k + 1), parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∀ s' : RSBScheme k, parisiFunctional (s.dropZeroFirst hs) β h ≤ parisiFunctional s' β h := by
  intro s'
  rw [parisiFunctional_dropZeroFirst s hs β h]
  simpa only [parisiFunctional_padZeroFirst] using hmin s'.padZeroFirst

theorem cascadeT_dropZeroFirst_prefix {n k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β scale : ℝ) (A : (Fin n → ℝ) → ℝ)
    {j : ℕ} (hj : j ≤ k + 1) :
    cascadeT n (s.dropZeroFirst hs) β scale A j = cascadeT n s β scale A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp : k + 1 - j ≠ 0 := by omega
    have hp' : k + 2 - j ≠ 0 := by omega
    have hi : k + 1 - j + 1 = k + 1 + 1 - j := by omega
    have hi' : k + 2 - j + 1 = k + 1 + 2 - j := by omega
    rw [cascadeT, cascadeT, ih (by omega)]
    simp only [RSBScheme.dropZeroFirst, if_neg hp, if_neg hp', hi, hi']

/-- Exact preservation of the actual Guerra cascade, not only the scalar
endpoint. The two outer expectation steps merge by the N-site Gaussian law. -/
theorem guerraCascade_dropZeroFirst {n k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β : ℝ) (U : EnergySpace n) (h : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cascadeT n (s.dropZeroFirst hs) β 1 (guerraBase n U h t) (k + 2) =
      cascadeT n s β 1 (guerraBase n U h t) (k + 1 + 2) := by
  have hv₁ : 0 ≤ β ^ 2 * s.q 1 := mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))
  have hv₂ : 0 ≤ β ^ 2 * (s.q 2 - s.q 1) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono 1 (by omega)))
  rw [show k + 2 = (k + 1) + 1 by omega, cascadeT,
    cascadeT_dropZeroFirst_prefix s hs β 1 _ le_rfl]
  conv_rhs => rw [show k + 1 + 2 = ((k + 1) + 1) + 1 by omega, cascadeT, cascadeT]
  simp only [show k + 2 - (k + 1) = 1 by omega,
    show k + 1 + 2 - (k + 1 + 1) = 1 by omega,
    Nat.add_sub_cancel_left, Nat.sub_self,
    RSBScheme.dropZeroFirst, if_true, if_false, one_ne_zero, hs, s.m_zero, s.q_zero,
    sub_zero, one_mul]
  have H := parisiStepPi_zero_add hv₁ hv₂ (guerraGrowth_cascade n s β U h ht (k + 1))
  convert H using 1
  congr 1
  ring

variable {Ω : Type*} [MeasureSpace Ω]

theorem guerraPhi_dropZeroFirst {n k : ℕ} (s : RSBScheme (k + 1))
    (hs : s.m 1 = 0) (β h : ℝ) (U : Ω → EnergySpace n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    guerraPhi n (s.dropZeroFirst hs) β h U t = guerraPhi n s β h U t := by
  unfold guerraPhi
  simp_rw [guerraCascade_dropZeroFirst s hs β _ h ht]

/-- Every scheme has an exactly equivalent scheme with positive first mass.
Both the Parisi data and the actual interpolated pressure are preserved.
This does not assert strictness of every overlap or mass increment. -/
theorem exists_positive_first_mass_reduction {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      0 < s'.m 1 ∧
      parisiFunctional s' β h = parisiFunctional s β h ∧
      (∀ t, guerraPsi s' β h t = guerraPsi s β h t) ∧
      (∀ n (U : Ω → EnergySpace n) t, t ∈ Set.Icc (0 : ℝ) 1 →
        guerraPhi n s' β h U t = guerraPhi n s β h U t) ∧
      ((∀ s'' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s'' β h) →
        ∀ s'' : RSBScheme l, parisiFunctional s' β h ≤ parisiFunctional s'' β h) := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, s, ?_, rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
    rw [show s.m 1 = 1 from s.m_top]
    norm_num
  | succ k ih =>
    by_cases hs : 0 < s.m 1
    · exact ⟨k + 1, le_rfl, s, hs, rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
    · have hs0 : s.m 1 = 0 := le_antisymm (le_of_not_gt hs) (s.m_nonneg (by omega))
      obtain ⟨l, hl, s', hpos, hfunc, hpsi, hphi, hmin⟩ := ih (s.dropZeroFirst hs0)
      refine ⟨l, hl.trans (Nat.le_succ k), s', hpos,
        hfunc.trans (parisiFunctional_dropZeroFirst s hs0 β h), ?_, ?_, ?_⟩
      · intro t
        exact (hpsi t).trans (guerraPsi_dropZeroFirst s hs0 β h t)
      · intro n U t ht
        exact (hphi n U t ht).trans (guerraPhi_dropZeroFirst s hs0 β h U ht)
      · intro hmins
        exact hmin (minimizer_dropZeroFirst s hs0 β h hmins)

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The original Theorem 2.2 quantifiers now follow from a quadratic pressure
bound proved only for schemes with positive first mass. Leading zero masses
are removed exactly, with preservation of near-optimality, fixed-level
minimality, and the actual pressure. The quadratic bound remains an explicit
input to this reusable theorem and is supplied downstream by Theorem 2.4; no
other strictness condition is silently imposed on it. -/
theorem talagrand_theorem_2_2_of_positive_mass_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hquad : ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k), 0 < s.m 1 →
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
        ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
          constrainedPhi n s β h (sk n).U d t u ≤
            2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      parisiFunctional s β h ≤ parisiValue β h + ε →
      (∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun n => guerraPhi n s β h (sk n).U t) atTop (𝓝 (guerraPsi s β h t)) := by
  obtain ⟨ε, hε, hquadε⟩ := hquad
  refine ⟨ε, hε, fun s hnear hmin t ht htt₀ => ?_⟩
  obtain ⟨l, _, s', hpos, hfunc, hpsi, hphi, hmin'⟩ :=
    exists_positive_first_mass_reduction (Ω := Ω) s β h
  obtain ⟨K, hK, hquad'⟩ := hquadε s' hpos (by simpa only [hfunc] using hnear) (hmin' hmin)
  have hconv := guerraPhi_uniform_of_quadratic_bound β h sk s' hpos
    ⟨ht.trans htt₀, ht₀⟩ hK hquad'
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hconv δ hδ] with n hn
  have H := hn t ⟨ht, htt₀⟩
  rw [hphi n (sk n).U t ⟨ht, htt₀.trans ht₀.le⟩, hpsi t] at H
  simpa only [Real.dist_eq] using H

end SpinGlass.Targets
