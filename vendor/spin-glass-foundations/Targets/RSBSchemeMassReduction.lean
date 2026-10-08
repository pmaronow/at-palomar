module

/-
# Exact merging of equal adjacent RSB masses

The equal-mass part of Talagrand (2.19), preserving the actual scalar functional
and N-site interpolation. Overlap coincidences are not assumed absent.
-/
public import Targets.RSBSchemeReduction
public import Targets.RSBMassPiSemigroup

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- Delete position `p` from a naturally indexed sequence. -/
def skipLevel (p j : ℕ) : ℕ := if j < p then j else j + 1

theorem skipLevel_mono (p : ℕ) : Monotone (skipLevel p) := by
  intro a b hab
  unfold skipLevel
  split_ifs <;> omega

/-- Merge the two intervals with equal masses `m_p=m_(p+1)`, deleting
`q_(p+1)` and `m_p`. In particular `p=0` is permitted when `m_1=0`. -/
noncomputable def RSBScheme.mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) : RSBScheme k where
  m j := s.m (skipLevel p j)
  q j := s.q (skipLevel (p + 1) j)
  m_zero := by
    by_cases hp0 : p = 0
    · simpa [skipLevel, hp0, s.m_zero] using hm.symm
    · simp [skipLevel, show 0 < p by omega, s.m_zero]
  m_top := by simp [skipLevel, show ¬k + 1 < p by omega, s.m_top]
  m_mono j hj := s.m_mono' (skipLevel p (j + 1))
    (by unfold skipLevel; split_ifs <;> omega) _ ((skipLevel_mono p) (by omega))
  q_zero := by simp [skipLevel, s.q_zero]
  q_top := by simp [skipLevel, show ¬k + 2 < p + 1 by omega, s.q_top, Nat.add_assoc]
  q_mono j hj := s.q_mono' (skipLevel (p + 1) (j + 1))
    (by unfold skipLevel; split_ifs <;> omega) _ ((skipLevel_mono (p + 1)) (by omega))

private theorem growth_step {n : ℕ} {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A)
    {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) : GuerraGrowth (parisiStepPi n m v A) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  exact ⟨measurable_parisiStepPi hA.measurable m v, C + stepK n m v D, D, hD,
    parisiStepPi_abs_le hm hv hD hb hA.measurable⟩

private theorem growth_cascade {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) {j : ℕ} (hj : j ≤ k + 2) :
    GuerraGrowth (cascadeT n s β 1 A j) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    apply growth_step (ih (by omega)) (s.m_nonneg (by omega))
    exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' (k + 2 - j) (by omega) (k + 1 - j) (by omega))))

theorem cascadeT_mergeEqualMass_prefix {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1))
    (β : ℝ) (A : (Fin n → ℝ) → ℝ) {j : ℕ} (hj : j ≤ k + 1 - p) :
    cascadeT n (s.mergeEqualMass p hp hm) β 1 A j = cascadeT n s β 1 A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hi : ¬k + 1 - j < p := by omega
    have hi' : ¬k + 1 - j < p + 1 := by omega
    have hi'' : ¬k + 2 - j < p + 1 := by omega
    rw [cascadeT, cascadeT, ih (by omega)]
    simp only [RSBScheme.mergeEqualMass, skipLevel, if_neg hi, if_neg hi', if_neg hi'',
      show k + 1 - j + 1 = k + 1 + 1 - j by omega,
      show k + 2 - j + 1 = k + 1 + 2 - j by omega]

/-- The cascade equality immediately after the merged interval. -/
theorem cascadeT_mergeEqualMass_merged {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1))
    (β : ℝ) {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) :
    cascadeT n (s.mergeEqualMass p hp hm) β 1 A (k + 1 - p + 1) =
      cascadeT n s β 1 A (k + 1 - p + 2) := by
  rw [cascadeT, cascadeT_mergeEqualMass_prefix s p hp hm β A le_rfl]
  conv_rhs => rw [show k + 1 - p + 2 = (k + 1 - p + 1) + 1 by omega, cascadeT, cascadeT]
  have hidx : k + 1 - (k + 1 - p) = p := by omega
  have hidx' : k + 2 - (k + 1 - p) = p + 1 := by omega
  have hidx''' : k + 1 + 2 - (k + 1 - p) = p + 2 := by omega
  have ho : k + 1 + 1 - (k + 1 - p + 1) = p := by omega
  have ho' : k + 1 + 2 - (k + 1 - p + 1) = p + 1 := by omega
  simp only [RSBScheme.mergeEqualMass, hidx, hidx', hidx''', ho, ho', skipLevel,
    lt_self_iff_false, if_false, Nat.lt_succ_self, if_true, one_mul, hm]
  have hv₁ : 0 ≤ β ^ 2 * (s.q (p + 1) - s.q p) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono p (by omega)))
  have hv₂ : 0 ≤ β ^ 2 * (s.q (p + 2) - s.q (p + 1)) :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono (p + 1) (by omega)))
  have H := parisiStepPi_add (s.m (p + 1)) hv₁ hv₂
    (growth_cascade s β hA (j := k + 1 - p) (by omega))
  convert H using 1
  congr 1
  ring

theorem cascadeT_mergeEqualMass_outer {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1))
    (β : ℝ) {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A)
    {j : ℕ} (hj : j ≤ p) :
    cascadeT n (s.mergeEqualMass p hp hm) β 1 A (k + 1 - p + 1 + j) =
      cascadeT n s β 1 A (k + 1 - p + 2 + j) := by
  induction j with
  | zero => simpa using cascadeT_mergeEqualMass_merged s p hp hm β hA
  | succ j ih =>
    rw [show k + 1 - p + 1 + (j + 1) = (k + 1 - p + 1 + j) + 1 by omega,
      show k + 1 - p + 2 + (j + 1) = (k + 1 - p + 2 + j) + 1 by omega,
      cascadeT, cascadeT, ih (by omega)]
    have hi : k + 1 - (k + 1 - p + 1 + j) < p := by omega
    have hi' : k + 2 - (k + 1 - p + 1 + j) < p + 1 := by omega
    simp only [RSBScheme.mergeEqualMass, skipLevel, if_pos hi, if_pos hi',
      if_pos (show k + 1 - (k + 1 - p + 1 + j) < p + 1 by omega),
      show k + 1 + 1 - (k + 1 - p + 2 + j) = k + 1 - (k + 1 - p + 1 + j) by omega,
      show k + 1 + 2 - (k + 1 - p + 2 + j) = k + 2 - (k + 1 - p + 1 + j) by omega]

/-- Exact merging of arbitrary equal adjacent masses in an N-site cascade. -/
theorem cascadeT_mergeEqualMass {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1))
    (β : ℝ) {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) :
    cascadeT n (s.mergeEqualMass p hp hm) β 1 A (k + 2) =
      cascadeT n s β 1 A (k + 1 + 2) := by
  have H := cascadeT_mergeEqualMass_outer s p hp hm β hA (j := p) le_rfl
  simpa only [show k + 1 - p + 1 + p = k + 2 by omega,
    show k + 1 - p + 2 + p = k + 1 + 2 by omega] using H

/-- Scalar preservation is the one-site specialization of the exact N-site
identity, using the already proved site factorization. -/
theorem parisiF_mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β : ℝ) :
    parisiF (s.mergeEqualMass p hp hm) β (k + 2) = parisiF s β (k + 1 + 2) := by
  have hg : GuerraGrowth (fun w : Fin 1 → ℝ => ∑ i, Real.log (2 * Real.cosh (w i))) := by
    simpa only [cascadeT, guerraBase_zero, Pi.add_apply, add_zero] using
      guerraGrowth_cascade 1 s β (0 : EnergySpace 1) 0 (t := 0) (by norm_num) 0
  have H := cascadeT_mergeEqualMass s p hp hm β hg
  funext x
  have Hx := congrFun H (fun _ => x)
  have Hx' := ((cascadeT_one_scale 1 (s.mergeEqualMass p hp hm) β (k + 2) (fun _ => x)).symm.trans Hx).trans
    (cascadeT_one_scale 1 s β (k + 1 + 2) (fun _ => x))
  simp only [Fin.sum_univ_one] at Hx'
  linarith only [Hx']

private theorem sum_merge_adjacent (f g : ℕ → ℝ) {n p : ℕ} (hp : p ≤ n)
    (hbefore : ∀ j < p, g j = f j) (hmerge : g p = f p + f (p + 1))
    (hafter : ∀ j, p < j → j ≤ n → g j = f (j + 1)) :
    ∑ j ∈ Finset.range (n + 1), g j = ∑ j ∈ Finset.range (n + 2), f j := by
  induction n with
  | zero =>
    have hp0 : p = 0 := by omega
    subst p
    simpa [Finset.sum_range_succ] using hmerge
  | succ n ih =>
    by_cases hpn : p ≤ n
    · rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        Finset.sum_range_succ (f := g) (n + 1), Finset.sum_range_succ (f := f) (n + 2),
        ih hpn (fun j hpj hj => hafter j hpj (by omega)), hafter (n + 1) (by omega) le_rfl]
    · have hpe : p = n + 1 := by omega
      subst p
      have he : (∑ j ∈ Finset.range (n + 1), g j) = ∑ j ∈ Finset.range (n + 1), f j :=
        Finset.sum_congr rfl (fun j hj => hbefore j (Finset.mem_range.mp hj))
      rw [show n + 1 + 2 = ((n + 1) + 1) + 1 by omega,
        Finset.sum_range_succ (f := g) (n + 1),
        Finset.sum_range_succ (f := f) (n + 1 + 1),
        Finset.sum_range_succ (f := f) (n + 1), he, hmerge]
      ring

private theorem correction_eq_all {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiCorrection s β = (β ^ 2 / 4) *
      ∑ j ∈ Finset.range (k + 2), s.m j * (s.q (j + 1) ^ 2 - s.q j ^ 2) := by
  rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [s.m_zero, zero_mul, add_zero]
  rfl

/-- The two same-mass correction terms telescope exactly. -/
theorem parisiCorrection_mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β : ℝ) :
    parisiCorrection (s.mergeEqualMass p hp hm) β = parisiCorrection s β := by
  rw [correction_eq_all, correction_eq_all]
  congr 1
  apply sum_merge_adjacent _ _ hp
  · intro j hj
    simp only [RSBScheme.mergeEqualMass, skipLevel, if_pos hj,
      if_pos (show j < p + 1 by omega), if_pos (show j + 1 < p + 1 by omega)]
  · simp only [RSBScheme.mergeEqualMass, skipLevel, lt_self_iff_false, if_false,
      Nat.lt_succ_self, if_true, hm]
    ring
  · intro j hj hjk
    simp only [RSBScheme.mergeEqualMass, skipLevel, if_neg (show ¬j < p by omega),
      if_neg (show ¬j < p + 1 by omega), if_neg (show ¬j + 1 < p + 1 by omega)]

theorem parisiFunctional_mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β h : ℝ) :
    parisiFunctional (s.mergeEqualMass p hp hm) β h = parisiFunctional s β h := by
  change Real.log 2 + parisiF (s.mergeEqualMass p hp hm) β (k + 2) h -
      parisiCorrection (s.mergeEqualMass p hp hm) β = _
  rw [parisiF_mergeEqualMass s p hp hm β, parisiCorrection_mergeEqualMass s p hp hm β]
  rfl

theorem guerraPsi_mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β h t : ℝ) :
    guerraPsi (s.mergeEqualMass p hp hm) β h t = guerraPsi s β h t := by
  simp only [guerraPsi, parisiF_mergeEqualMass s p hp hm β,
    parisiCorrection_mergeEqualMass s p hp hm β]

theorem minimizer_mergeEqualMass {k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β h : ℝ)
    (hmin : ∀ s' : RSBScheme (k + 1), parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∀ s' : RSBScheme k, parisiFunctional (s.mergeEqualMass p hp hm) β h ≤ parisiFunctional s' β h := by
  intro s'
  rw [parisiFunctional_mergeEqualMass s p hp hm β h]
  simpa only [parisiFunctional_padZeroFirst] using hmin s'.padZeroFirst

variable {Ω : Type*} [MeasureSpace Ω]

theorem guerraPhi_mergeEqualMass {n k : ℕ} (s : RSBScheme (k + 1))
    (p : ℕ) (hp : p ≤ k + 1) (hm : s.m p = s.m (p + 1)) (β h : ℝ)
    (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    guerraPhi n (s.mergeEqualMass p hp hm) β h U t = guerraPhi n s β h U t := by
  unfold guerraPhi
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  exact congrFun (cascadeT_mergeEqualMass s p hp hm β
    (guerraGrowth_cascade n s β (U ω) h ht 0)) 0

/-- The entire mass-strictness part of (2.19): all equal adjacent masses may
be removed with exact preservation and rigorous minimizer transfer. This
does not assert strictness of the overlap sequence, including its endpoints. -/
theorem exists_strict_mass_reduction {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      parisiFunctional s' β h = parisiFunctional s β h ∧
      (∀ t, guerraPsi s' β h t = guerraPsi s β h t) ∧
      (∀ n (U : Ω → EnergySpace n) t, t ∈ Set.Icc (0 : ℝ) 1 →
        guerraPhi n s' β h U t = guerraPhi n s β h U t) ∧
      ((∀ s'' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s'' β h) →
        ∀ s'' : RSBScheme l, parisiFunctional s' β h ≤ parisiFunctional s'' β h) := by
  classical
  induction k with
  | zero =>
    refine ⟨0, le_rfl, s, ?_, rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
    intro p hp
    have hp0 : p = 0 := by omega
    subst p
    rw [s.m_zero, show s.m (0 + 1) = 1 from s.m_top]
    norm_num
  | succ k ih =>
    by_cases hstrict : ∀ p, p ≤ k + 1 → s.m p < s.m (p + 1)
    · exact ⟨k + 1, le_rfl, s, hstrict, rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun hmin => hmin⟩
    · push Not at hstrict
      obtain ⟨p, hp, hle⟩ := hstrict
      have hm : s.m p = s.m (p + 1) := le_antisymm (s.m_mono p hp) hle
      obtain ⟨l, hl, s', hpos, hfunc, hpsi, hphi, hmin⟩ := ih (s.mergeEqualMass p hp hm)
      refine ⟨l, hl.trans (Nat.le_succ k), s', hpos,
        hfunc.trans (parisiFunctional_mergeEqualMass s p hp hm β h), ?_, ?_, ?_⟩
      · intro t
        exact (hpsi t).trans (guerraPsi_mergeEqualMass s p hp hm β h t)
      · intro n U t ht
        exact (hphi n U t ht).trans (guerraPhi_mergeEqualMass s p hp hm β h U ht)
      · intro hmins
        exact hmin (minimizer_mergeEqualMass s p hp hm β h hmins)

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The original Theorem 2.2 quantifiers need a quadratic bound only for
strictly increasing mass sequences. All mass coincidences are removed exactly;
no extra strictness of the overlap sequence is inserted into the hypothesis.
The completed Theorem 2.4 supplies this explicit input downstream. -/
theorem talagrand_theorem_2_2_of_strict_mass_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hquad : ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      (∀ p, p ≤ k → s.m p < s.m (p + 1)) →
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
  obtain ⟨l, _, s', hstrict, hfunc, hpsi, hphi, hmin'⟩ :=
    exists_strict_mass_reduction (Ω := Ω) s β h
  have hpos : 0 < s'.m 1 := by
    simpa only [s'.m_zero, zero_add] using hstrict 0 (Nat.zero_le l)
  obtain ⟨K, hK, hquad'⟩ := hquadε s' hstrict (by simpa only [hfunc] using hnear) (hmin' hmin)
  have hconv := guerraPhi_uniform_of_quadratic_bound β h sk s' hpos
    ⟨ht.trans htt₀, ht₀⟩ hK hquad'
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [hconv δ hδ] with n hn
  have H := hn t ⟨ht, htt₀⟩
  rw [hphi n (sk n).U t ⟨ht, htt₀.trans ht₀.le⟩, hpsi t] at H
  simpa only [Real.dist_eq] using H

end SpinGlass.Targets
