module

/- Adaptation for Lean 4.34.1: proof elaboration and API compatibility only; original theorem statements are retained. Source revisions and exact patch are recorded in PROVENANCE.json and COMPATIBILITY.patch. -/
public import Targets.Section4EndpointOptimality

@[expose] public section

/-!
# Removing repeated interior overlap levels

If q_(p+1)=q_p, the mass on that zero-variance interval is irrelevant.
Raise it to the next mass and reuse the existing equal-mass merge. This
preserves the actual functional and N-site interpolation, not just a scalar
surrogate. The initial overlap zero and final compulsory overlap one are not
deleted by this operation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- All N-site cascade prefixes ignore a mass on a zero-variance interval,
at arbitrary interpolation scale and for any base function. -/
theorem cascadeT_raiseMass_zero_variance {n k : ℕ} (s : RSBScheme k) (β scale : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) (A : (Fin n → ℝ) → ℝ) {j : ℕ} (hj : j ≤ k + 2) :
    cascadeT n (s.raiseMass p hp0 hp m hm) β scale A j = cascadeT n s β scale A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cascadeT, cascadeT, ih (by omega)]
    change parisiStepPi n (if k + 1 - j = p then m else s.m (k + 1 - j))
      (scale * (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))) _ = _
    by_cases he : k + 1 - j = p
    · have he' : k + 2 - j = p + 1 := by omega
      simp only [he, he', hq, sub_self, mul_zero]
      funext x
      simp only [parisiStepPi_zero_var]
    · rw [if_neg he]

theorem parisiCorrection_raiseMass_zero_variance {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) :
    parisiCorrection (s.raiseMass p hp0 hp m hm) β = parisiCorrection s β := by
  have H := parisiFunctional_raiseMass_zero_variance s β 0 p hp0 hp m hm hq
  change Real.log 2 + parisiF (s.raiseMass p hp0 hp m hm) β (k + 2) 0 -
    parisiCorrection (s.raiseMass p hp0 hp m hm) β =
      Real.log 2 + parisiF s β (k + 2) 0 - parisiCorrection s β at H
  rw [parisiF_raiseMass_zero_variance s β p hp0 hp m hm hq le_rfl] at H
  linarith

theorem guerraPsi_raiseMass_zero_variance {k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) :
    guerraPsi (s.raiseMass p hp0 hp m hm) β h t = guerraPsi s β h t := by
  rw [guerraPsi, guerraPsi, parisiF_raiseMass_zero_variance s β p hp0 hp m hm hq le_rfl,
    parisiCorrection_raiseMass_zero_variance s β p hp0 hp m hm hq]

theorem RSBScheme.nextMass_mem {k : ℕ} (s : RSBScheme k) (p : ℕ) (hp : p ≤ k) :
    s.m (p + 1) ∈ Set.Icc (s.m p) (s.m (p + 1)) :=
  ⟨s.m_mono p hp, le_rfl⟩

/-- Remove a repeated interior overlap by making its irrelevant mass equal
to the next one and applying the checked equal-mass reduction. -/
noncomputable def RSBScheme.mergeEqualOverlap {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (_hq : s.q (p + 1) = s.q p) : RSBScheme k :=
  (s.raiseMass p hp0 hp (s.m (p + 1)) (s.nextMass_mem p hp)).mergeEqualMass p hp
    (by simp [RSBScheme.raiseMass])

/-- The remaining masses are an unchanged subsequence of the original list. -/
theorem RSBScheme.mergeEqualOverlap_mass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p) (j : ℕ) :
    (s.mergeEqualOverlap p hp0 hp hq).m j = s.m (skipLevel p j) := by
  change (if skipLevel p j = p then s.m (p + 1) else s.m (skipLevel p j)) = _
  rw [if_neg (by unfold skipLevel; split_ifs <;> omega)]

/-- Deleting an irrelevant mass preserves strictness of all remaining masses. -/
theorem RSBScheme.mergeEqualOverlap_strict_mass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p)
    (hstrict : ∀ j, j ≤ k + 1 → s.m j < s.m (j + 1)) :
    ∀ j, j ≤ k → (s.mergeEqualOverlap p hp0 hp hq).m j <
      (s.mergeEqualOverlap p hp0 hp hq).m (j + 1) := by
  intro j hj
  rw [RSBScheme.mergeEqualOverlap_mass, RSBScheme.mergeEqualOverlap_mass]
  have hab : skipLevel p j < skipLevel p (j + 1) := by
    unfold skipLevel
    split_ifs <;> omega
  exact (hstrict (skipLevel p j) (by unfold skipLevel; split_ifs <;> omega)).trans_le
    (s.m_mono' (skipLevel p (j + 1)) (by unfold skipLevel; split_ifs <;> omega)
      (skipLevel p j + 1) (by omega))

theorem parisiFunctional_mergeEqualOverlap {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p) (β h : ℝ) :
    parisiFunctional (s.mergeEqualOverlap p hp0 hp hq) β h = parisiFunctional s β h := by
  rw [RSBScheme.mergeEqualOverlap, parisiFunctional_mergeEqualMass,
    parisiFunctional_raiseMass_zero_variance s β h p hp0 hp _ _ hq]

theorem guerraPsi_mergeEqualOverlap {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p) (β h t : ℝ) :
    guerraPsi (s.mergeEqualOverlap p hp0 hp hq) β h t = guerraPsi s β h t := by
  rw [RSBScheme.mergeEqualOverlap, guerraPsi_mergeEqualMass,
    guerraPsi_raiseMass_zero_variance s β h t p hp0 hp _ _ hq]

/-- Fixed-level minimality transfers to the smaller comparison class through
the existing zero-level padding, rather than assuming a stronger optimizer. -/
theorem minimizer_mergeEqualOverlap {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p) (β h : ℝ)
    (hmin : ∀ s' : RSBScheme (k + 1), parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∀ s' : RSBScheme k, parisiFunctional (s.mergeEqualOverlap p hp0 hp hq) β h ≤
      parisiFunctional s' β h := by
  intro s'
  rw [parisiFunctional_mergeEqualOverlap s p hp0 hp hq β h]
  simpa only [parisiFunctional_padZeroFirst] using hmin s'.padZeroFirst

variable {Ω : Type*} [MeasureSpace Ω]

theorem guerraPhi_raiseMass_zero_variance {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) (U : Ω → EnergySpace n) (t : ℝ) :
    guerraPhi n (s.raiseMass p hp0 hp m hm) β h U t = guerraPhi n s β h U t := by
  unfold guerraPhi
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  exact congrFun (cascadeT_raiseMass_zero_variance s β 1 p hp0 hp m hm hq
    (guerraBase n (U ω) h t) le_rfl) 0

/-- Exact preservation of the actual interpolation when an interior overlap
is repeated. No positivity of an adjacent mass is needed. -/
theorem guerraPhi_mergeEqualOverlap {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k + 1) (hq : s.q (p + 1) = s.q p)
    (β h : ℝ) (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    guerraPhi n (s.mergeEqualOverlap p hp0 hp hq) β h U t = guerraPhi n s β h U t := by
  rw [RSBScheme.mergeEqualOverlap, guerraPhi_mergeEqualMass _ p hp _ β h U ht,
    guerraPhi_raiseMass_zero_variance s β h p hp0 hp _ _ hq U t]

/-- Remove every repeated interior overlap while retaining strict masses.
The first overlap may equal zero and the last may equal one; the checked
stationarity results use the available inward direction at these boundaries. -/
theorem exists_strict_overlap_reduction {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1)) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      (∀ p, 1 ≤ p → p ≤ l → s'.q p < s'.q (p + 1)) ∧
      parisiFunctional s' β h = parisiFunctional s β h ∧
      (∀ t, guerraPsi s' β h t = guerraPsi s β h t) ∧
      (∀ n (U : Ω → EnergySpace n) t, t ∈ Set.Icc (0 : ℝ) 1 →
        guerraPhi n s' β h U t = guerraPhi n s β h U t) ∧
      ((∀ s'' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s'' β h) →
        ∀ s'' : RSBScheme l, parisiFunctional s' β h ≤ parisiFunctional s'' β h) := by
  classical
  induction k with
  | zero =>
    exact ⟨0, le_rfl, s, hmass, fun p hp hp' => by omega,
      rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
  | succ k ih =>
    by_cases hstrict : ∀ p, 1 ≤ p → p ≤ k + 1 → s.q p < s.q (p + 1)
    · exact ⟨k + 1, le_rfl, s, hmass, hstrict,
        rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
    · push Not at hstrict
      obtain ⟨p, hp0, hp, hle⟩ := hstrict
      have hq : s.q (p + 1) = s.q p := le_antisymm hle (s.q_mono p (by omega))
      obtain ⟨l, hl, s', hm', hq', hfunc, hpsi, hphi, hmin⟩ :=
        ih (s.mergeEqualOverlap p hp0 hp hq) (s.mergeEqualOverlap_strict_mass p hp0 hp hq hmass)
      refine ⟨l, hl.trans (Nat.le_succ k), s', hm', hq',
        hfunc.trans (parisiFunctional_mergeEqualOverlap s p hp0 hp hq β h), ?_, ?_, ?_⟩
      · intro t
        exact (hpsi t).trans (guerraPsi_mergeEqualOverlap s p hp0 hp hq β h t)
      · intro n U t ht
        exact (hphi n U t ht).trans (guerraPhi_mergeEqualOverlap s p hp0 hp hq β h U ht)
      · intro hmins
        exact hmin (minimizer_mergeEqualOverlap s p hp0 hp hq β h hmins)

/-- The mass and interior-overlap strictness reductions together, with exact
preservation of the objects occurring in the original Theorem 2.2 statement. -/
theorem exists_strict_mass_overlap_reduction {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      (∀ p, 1 ≤ p → p ≤ l → s'.q p < s'.q (p + 1)) ∧
      parisiFunctional s' β h = parisiFunctional s β h ∧
      (∀ t, guerraPsi s' β h t = guerraPsi s β h t) ∧
      (∀ n (U : Ω → EnergySpace n) t, t ∈ Set.Icc (0 : ℝ) 1 →
        guerraPhi n s' β h U t = guerraPhi n s β h U t) ∧
      ((∀ s'' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s'' β h) →
        ∀ s'' : RSBScheme l, parisiFunctional s' β h ≤ parisiFunctional s'' β h) := by
  obtain ⟨j, hj, sj, hmj, hfuncj, hpsij, hphij, hminj⟩ :=
    exists_strict_mass_reduction (Ω := Ω) s β h
  obtain ⟨l, hl, s', hm', hq', hfunc, hpsi, hphi, hmin⟩ :=
    exists_strict_overlap_reduction (Ω := Ω) sj β h hmj
  exact ⟨l, hl.trans hj, s', hm', hq', hfunc.trans hfuncj,
    fun t => (hpsi t).trans (hpsij t),
    fun n U t ht => (hphi n U t ht).trans (hphij n U t ht),
    fun H => hmin (hminj H)⟩

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The original convergence statement needs the missing quadratic bound
only for strict masses and strict interior overlaps. No extra strictness is
assumed of the original near-minimizing scheme. This reduction keeps the
quadratic input explicit; the completed Theorem 2.4 supplies it downstream. -/
theorem talagrand_theorem_2_2_of_strict_mass_overlap_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hquad : ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
      (∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1)) →
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
  obtain ⟨l, _, s', hmass, hoverlap, hfunc, hpsi, hphi, hmin'⟩ :=
    exists_strict_mass_overlap_reduction (Ω := Ω) s β h
  have hpos : 0 < s'.m 1 := by
    simpa only [s'.m_zero, zero_add] using hmass 0 (Nat.zero_le l)
  obtain ⟨K, hK, hquad'⟩ := hquadε s' hmass hoverlap (by simpa only [hfunc] using hnear) (hmin' hmin)
  have hconv := guerraPhi_uniform_of_quadratic_bound β h sk s' hpos
    ⟨ht.trans htt₀, ht₀⟩ hK hquad'
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hconv δ hδ] with n hn
  have H := hn t ⟨ht, htt₀⟩
  rw [hphi n (sk n).U t ⟨ht, htt₀.trans ht₀.le⟩, hpsi t] at H
  simpa only [Real.dist_eq] using H

end SpinGlass.Targets
