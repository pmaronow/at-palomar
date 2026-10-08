module

public import Targets.Section4StationarityInterior

@[expose] public section

/-!
# Stationarity at the compulsory last mass

For the last overlap, lowering the next mass is inadmissible because that mass
must remain one. Instead, set the last overlap of an auxiliary same-level
scheme to one. Inserting the original mass one and merging two equal masses
then parametrizes genuine fixed-level competitors. The existing Section 4
derivative applies unchanged, including zero variances and the RS case `k=0`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Move only the last nonfixed overlap to one, preserving the compulsory
last mass and the fixed number of levels. -/
noncomputable def section4TerminalBase {k : ℕ} (s : RSBScheme k) : RSBScheme k where
  m := s.m
  q j := if j = k + 1 then 1 else s.q j
  m_zero := s.m_zero
  m_top := s.m_top
  m_mono := s.m_mono
  q_zero := by simp [s.q_zero]
  q_top := by simp [s.q_top]
  q_mono j hj := by
    by_cases he : j = k + 1
    · subst j
      simp [show k + 1 + 1 = k + 2 by omega, s.q_top]
    · by_cases he' : j + 1 = k + 1
      · simp only [if_neg he, if_pos he']
        exact s.q_le_one (by omega)
      · simpa only [if_neg he, if_neg he'] using s.q_mono j hj

private theorem terminal_scheme_eq_of_fields {k : ℕ} {s t : RSBScheme k}
    (hm : s.m = t.m) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hm
  cases hq
  rfl

/-- Inserting mass one into the auxiliary base gives a genuine same-level
competitor after an exact equal-mass merge. -/
theorem section4Phi_terminalBase_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {u : ℝ} (hu : u ∈ Set.Icc (s.q k) 1) :
    section4Phi (section4TerminalBase s) β h (k + 1) 1 (s.q (k + 1)) ≤
      section4Phi (section4TerminalBase s) β h (k + 1) 1 u := by
  let b := section4TerminalBase s
  have hm : (1 : ℝ) ∈ Set.Icc (b.m (k + 1 - 1)) (b.m (k + 1)) :=
    ⟨s.m_le_one (by omega), s.m_top.ge⟩
  have hq (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :
      u ∈ Set.Icc (b.q (k + 1 - 1)) (b.q (k + 1)) := by
    simpa [b, section4TerminalBase, show k ≠ k + 1 by omega] using hu
  have hq0 : s.q (k + 1) ∈ Set.Icc (s.q k) 1 :=
    ⟨s.q_mono k (by omega), s.q_le_one (by omega)⟩
  let si (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :=
    b.insertLevel (k + 1) (by omega) le_rfl 1 u hm (hq u hu)
  have he (u : ℝ) (hu : u ∈ Set.Icc (s.q k) 1) :
      (si u hu).m (k + 1) = (si u hu).m (k + 1 + 1) := by
    simp [si, RSBScheme.insertLevel, section4Mass, b, section4TerminalBase,
      show ¬k + 1 + 1 < k + 1 by omega, s.m_top]
  have heq : (si (s.q (k + 1)) hq0).mergeEqualMass (k + 1) le_rfl
      (he (s.q (k + 1)) hq0) = s := by
    apply terminal_scheme_eq_of_fields
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section4Mass, b, section4TerminalBase]
      split_ifs <;> first | rfl | (congr 1; omega)
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section5Rho, b, section4TerminalBase]
      split_ifs <;> first | rfl | (congr 1; omega)
  have hb : section4Phi b β h (k + 1) 1 (s.q (k + 1)) = parisiFunctional s β h := by
    rw [← parisiFunctional_insertLevel b β h (k + 1) (by omega) le_rfl 1 (s.q (k + 1)) hm (hq _ hq0)]
    change parisiFunctional (si (s.q (k + 1)) hq0) β h = _
    rw [← parisiFunctional_mergeEqualMass (si (s.q (k + 1)) hq0) (k + 1) le_rfl
      (he (s.q (k + 1)) hq0), heq]
  have H := hmin ((si u hu).mergeEqualMass (k + 1) le_rfl (he u hu))
  rw [parisiFunctional_mergeEqualMass] at H
  change parisiFunctional s β h ≤ parisiFunctional
    (b.insertLevel (k + 1) (by omega) le_rfl 1 u hm (hq u hu)) β h at H
  rw [parisiFunctional_insertLevel] at H
  exact hb.trans_le H

private theorem terminalBase_inner {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiStep 1 (β ^ 2 * (1 - s.q (k + 1)))
      (parisiF (section4TerminalBase s) β 1) = parisiF s β 1 := by
  have hF : parisiF (section4TerminalBase s) β 1 = fun x => Real.log (Real.cosh x) := by
    funext x
    simp [parisiF, section4TerminalBase, s.q_top, parisiStep_zero_var]
  rw [hF]
  simp only [parisiF, Nat.sub_zero, s.m_top, s.q_top]

private theorem terminalBase_inner_deriv {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    stepD1 (parisiF (section4TerminalBase s) β 1)
      (parisiFDeriv (section4TerminalBase s) β 1) 1 (β ^ 2 * (1 - s.q (k + 1))) =
      parisiFDeriv s β 1 := by
  let b := section4TerminalBase s
  funext x
  have H := hasDerivAt_parisiStep_spatial (parisiF_hasLinearGrowth b β 1)
    (parisiF_measurable b β _) (parisiF_C2_props b β _).2.1
    (parisiF_C2_props b β _).1.1 (parisiF_C2_props b β _).1.abs_first_le_one
    1 (β ^ 2 * (1 - s.q (k + 1))) x
  rw [terminalBase_inner s β] at H
  exact H.unique ((parisiF_C2_props s β 1).1.1 x)

/-- The auxiliary base with the original last overlap inserted has exactly
the original outer potentials. The initial extra level has zero variance. -/
theorem section4Cascade_terminalBase_endpoint {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k) :
    scalarFieldCascade
      (fun l => section4Mass (section4TerminalBase s) (k + 1) 1 (k + 2 - l))
      (fun l => section5Variance (section4TerminalBase s) β (k + 1) (k + 2 - l)
        (β ^ 2 * (1 - s.q (k + 1)))) (3 + j) = parisiF s β (2 + j) := by
  let b := section4TerminalBase s
  induction j with
  | zero =>
    have H := section4Cascade_split b β (r := k + 1) (by omega) le_rfl 1
      (β ^ 2 * (1 - s.q (k + 1)))
    simp only [show k + 2 - (k + 1) = 1 by omega] at H
    change scalarFieldCascade _ _ 3 = parisiF s β 2
    rw [H, terminalBase_inner s β]
    simp only [b, section4TerminalBase, Nat.add_sub_cancel,
      ite_true, if_neg (show k ≠ k + 1 by omega)]
    conv_rhs => rw [parisiF]
    rw [show k + 1 - 1 = k by omega, show k + 2 - 1 = k + 1 by omega]
    congr 1
    ring
  | succ j ih =>
    rw [show 3 + (j + 1) = (3 + j) + 1 by omega, scalarFieldCascade, ih (by omega),
      show 2 + (j + 1) = (2 + j) + 1 by omega, parisiF]
    let l := k + 2 - (3 + j)
    have hl : l < k + 1 := by dsimp [l]; omega
    have hl1 : l + 1 < k + 1 := by dsimp [l]; omega
    change parisiStep (section4Mass b (k + 1) 1 l)
      (section5Variance b β (k + 1) l _) _ = _
    simp only [section4Mass, section5Variance, if_pos hl, if_neg (Nat.ne_of_lt hl),
      if_neg (show ¬k + 1 < l by omega), if_neg (Nat.ne_of_lt hl1),
      b, section4TerminalBase]
    rw [show l = k + 1 - (2 + j) by dsimp [l]; omega,
      show k + 1 - (2 + j) + 1 = k + 2 - (2 + j) by omega]

/-- The normalized observable at the restored terminal overlap agrees with
the original endpoint factor through every outer level. -/
theorem section4VarianceQ_terminalBase_endpoint {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {j : ℕ} (hj : j ≤ k) (x y : Fin 1 → ℝ) :
    section4VarianceQ (section4TerminalBase s) β (k + 1) 1 j
      (β ^ 2 * (1 - s.q (k + 1))) x y =
      section4VarianceQ s β (k + 1) (s.m k) j 0 x y := by
  let b := section4TerminalBase s
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q (k + 1) - s.q (k + 1 - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono k (by omega)))⟩
  induction j generalizing x y with
  | zero =>
    simp only [section4VarianceQ, show k + 2 - (k + 1) = 1 by omega,
      terminalBase_inner s β, terminalBase_inner_deriv s β,
      parisiStep_zero_var, stepD1_parisiF_zero_variance, Nat.add_sub_cancel, sub_zero]
    simp only [section4TerminalBase, ite_true, if_neg (show k ≠ k + 1 by omega)]
    change pairedSecondMean (s.m k)
      (β ^ 2 * (1 - s.q k) - β ^ 2 * (1 - s.q (k + 1))) _ _ x y = _
    have hv : β ^ 2 * (1 - s.q k) - β ^ 2 * (1 - s.q (k + 1)) =
        β ^ 2 * (s.q (k + 1) - s.q k) := by ring
    rw [hv]
  | succ j ih =>
    have hG : section4VarianceQ b β (k + 1) 1 j (β ^ 2 * (1 - s.q (k + 1))) =
        section4VarianceQ s β (k + 1) (s.m k) j 0 := by
      funext x y
      exact ih (by omega) x y
    change section4VarianceQ b β (k + 1) 1 (j + 1) _ x y = _
    conv_lhs => rw [section4VarianceQ]
    conv_rhs => rw [section4VarianceQ]
    dsimp only
    rw [hG]
    simp only [show k + 2 - (k + 1) = 1 by omega]
    rw [section4Cascade_terminalBase_endpoint s β (j := j) (by omega)]
    have H := section4Cascade_baseline s β (r := k + 1) (by omega) le_rfl hzero
      (j := j) (by omega)
    simp only [Nat.add_sub_cancel, show k + 2 - (k + 1) = 1 by omega] at H
    rw [H]
    let l := k + 2 - (3 + j)
    have hl : l < k + 1 := by dsimp [l]; omega
    have hl1 : l + 1 < k + 1 := by dsimp [l]; omega
    change pairedSecondMean (b.m l) (β ^ 2 * (b.q (l + 1) - b.q l)) _ _ x y = _
    simp only [b, section4TerminalBase, if_neg (Nat.ne_of_lt hl), if_neg (Nat.ne_of_lt hl1)]
    rfl

theorem section4TVarianceQ_terminalBase_endpoint {k : ℕ} (s : RSBScheme k) (β h : ℝ) :
    section4TVarianceQ (section4TerminalBase s) β h (k + 1) 1
      (β ^ 2 * (1 - s.q (k + 1))) = section4TVarianceQ s β h (k + 1) (s.m k) 0 := by
  exact section4VarianceQ_terminalBase_endpoint s β le_rfl _ _

/-- The right-hand inequality in Proposition 4.7 at the compulsory last
mass. The mass remains one; only the last overlap is varied. -/
theorem section4_terminal_endpointQ_le_overlap_of_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (hm : s.m k < 1) (hq : s.q (k + 1) < 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4TVarianceQ s β h (k + 1) (s.m k) 0 ≤ s.q (k + 1) := by
  let b := section4TerminalBase s
  have hmass : b.m (k + 1 - 1) = s.m k := by simp [b, section4TerminalBase]
  have hbq : b.q (k + 1) = 1 := by simp [b, section4TerminalBase]
  have hbq' : b.q (k + 1 - 1) = s.q k := by
    simp [b, section4TerminalBase]
  have hu : s.q (k + 1) ∈ Set.Icc (b.q (k + 1 - 1)) (b.q (k + 1)) := by
    rw [hbq, hbq']
    exact ⟨s.q_mono k (by omega), hq.le⟩
  have hd := hasDerivWithinAt_section4Phi_overlap b β h (r := k + 1) (by omega) le_rfl
    (m := 1) ⟨zero_le_one, le_rfl⟩ (hmass ▸ hm.le) hu
  rw [hmass, hbq, hbq', section4TVarianceQ_terminalBase_endpoint s β h] at hd
  have H := derivative_nonneg_of_min_at_left hq
    (fun u hu => section4Phi_terminalBase_min s β h hmin
      ⟨(s.q_mono k (by omega)).trans hu.1, hu.2⟩)
    (hd.mono (Set.Icc_subset_Icc (s.q_mono k (by omega)) le_rfl))
  have hc : 0 < β ^ 2 * (1 - s.m k) / 2 :=
    div_pos (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hm)) (by norm_num)
  nlinarith

/-- Proposition 4.7 at the final compulsory-mass level. The initial RS case
`k=0`, last overlap zero, and last overlap one are all included. -/
theorem section4TVarianceQ_terminal_zero_eq_overlap_of_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (hm : s.m k < 1)
    (hleft : s.q k < s.q (k + 1) ∨ s.q (k + 1) = 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4TVarianceQ s β h (k + 1) (s.m k) 0 = s.q (k + 1) := by
  have hQ := section4TVarianceQ_mem_Icc s β h (k + 1) (m := s.m k)
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ 0
  apply le_antisymm
  · by_cases hq : s.q (k + 1) < 1
    · exact section4_terminal_endpointQ_le_overlap_of_min s β h hβ hm hq hmin
    · exact hQ.2.trans (le_of_not_gt hq)
  · rcases hleft with hleft | hleft
    · have H := section4_overlap_le_endpointQ_of_min s β h (r := k + 1) (by omega) le_rfl
        hβ (by simpa only [Nat.add_sub_cancel, s.m_top] using hm)
        (by simpa only [Nat.add_sub_cancel] using hleft) hmin
      simpa only [Nat.add_sub_cancel] using H
    · simpa only [hleft] using hQ.1

/-- Proposition 4.7 for every physical level, now including the compulsory
last mass. Coincident interior overlaps still require their separate reduction. -/
theorem section4TVarianceQ_zero_eq_overlap_of_min_all_levels {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r := by
  by_cases hrk : r ≤ k
  · exact section4TVarianceQ_zero_eq_overlap_of_min s β h hr0 hrk hβ hm hleft hright hmin
  · have he : r = k + 1 := by omega
    subst r
    simpa only [Nat.add_sub_cancel] using
      section4TVarianceQ_terminal_zero_eq_overlap_of_min s β h hβ
        (by simpa only [Nat.add_sub_cancel, s.m_top] using hm)
        (by simpa only [Nat.add_sub_cancel] using hleft) hmin

/-- Genuine inward endpoint derivative in (4.54), for all physical levels. -/
theorem hasDerivWithinAt_section4U_zero_of_min_all_levels {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    HasDerivWithinAt (section4U s β h r) (s.q r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) 0 := by
  have H := hasDerivWithinAt_section4U s β h hr0 hr
    (hm.trans_le (s.m_le_one hr)) (v := 0)
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  rwa [section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ hm hleft hright hmin] at H

/-- The upper endpoint derivative in Proposition 4.8 now covers the terminal
level as well, with no stationarity premise supplied by the caller. -/
theorem hasDerivWithinAt_section4FirstVariation_upper_zero_of_min_all_levels {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    HasDerivWithinAt (section4FirstVariation s β h r) 0
      (Set.Icc (s.q (r - 1)) (s.q r)) (s.q r) := by
  have H := hasDerivWithinAt_section4FirstVariation_overlap s β h hr0 hr
    (hm.trans_le (s.m_le_one hr)) (u := s.q r)
    ⟨s.q_mono' r (by omega) (r - 1) (by omega), le_rfl⟩
  simpa only [sub_self, mul_zero,
    section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ hm hleft hright hmin] using H

/-- Numerical inward derivative of U on a nondegenerate physical interval. -/
theorem derivWithin_section4U_zero_of_min_all_levels {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    derivWithin (section4U s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) 0 = s.q r := by
  have ha : 0 < β ^ 2 * (s.q r - s.q (r - 1)) :=
    mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hleft)
  exact (hasDerivWithinAt_section4U_zero_of_min_all_levels s β h hr0 hr hβ hm (Or.inl hleft)
    hright hmin).derivWithin (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)

/-- Numerical inward derivative of f at its upper endpoint, for all levels. -/
theorem derivWithin_section4FirstVariation_upper_zero_of_min_all_levels {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    derivWithin (section4FirstVariation s β h r)
      (Set.Icc (s.q (r - 1)) (s.q r)) (s.q r) = 0 :=
  (hasDerivWithinAt_section4FirstVariation_upper_zero_of_min_all_levels s β h hr0 hr hβ hm
    (Or.inl hleft) hright hmin).derivWithin (uniqueDiffOn_Icc hleft _ ⟨hleft.le, le_rfl⟩)

end SpinGlass.Targets
