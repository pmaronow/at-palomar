module

/- Adaptation for Lean 4.34.1: proof elaboration and API compatibility only; original theorem statements are retained. Source revisions and exact patch are recorded in PROVENANCE.json and COMPATIBILITY.patch. -/
public import Targets.Section4Stationarity

@[expose] public section

/-!
# Opposite overlap variations for nonterminal Section 4 levels

The right variation can reuse the checked left calculus: first lower the mass
on the next interval to the preceding mass, then insert the original mass.
At the lower overlap endpoint this is exactly the original scheme after an
equal-mass merge. No new Gaussian differentiation is needed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Lower a nonboundary mass while preserving the fixed number of levels. -/
noncomputable def RSBScheme.lowerMass {k : ℕ} (s : RSBScheme k) (p : ℕ)
    (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m (p - 1)) (s.m p)) : RSBScheme k where
  m j := if j = p then m else s.m j
  q := s.q
  m_zero := by simp [show (0 : ℕ) ≠ p by omega, s.m_zero]
  m_top := by simp [show k + 1 ≠ p by omega, s.m_top]
  m_mono j hj := by
    by_cases he : j = p
    · subst j
      simpa [show p + 1 ≠ p by omega] using hm.2.trans (s.m_mono p hp)
    · by_cases he' : j + 1 = p
      · simp only [if_neg he, if_pos he']
        simpa [show j = p - 1 by omega] using hm.1
      · simpa only [if_neg he, if_neg he'] using s.m_mono j hj
  q_zero := s.q_zero
  q_top := s.q_top
  q_mono := s.q_mono

/-- Lowering a mass leaves every strictly inner prefix unchanged. -/
theorem parisiF_lowerMass_prefix {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r)) {j : ℕ} (hj : j ≤ k + 1 - r) :
    parisiF (s.lowerMass r hr0 hr m hm) β j = parisiF s β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parisiF, parisiF, ih (by omega)]
    simp only [RSBScheme.lowerMass, if_neg (show k + 1 - j ≠ r by omega)]

theorem parisiFDeriv_lowerMass_prefix {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r)) {j : ℕ} (hj : j ≤ k + 1 - r) :
    parisiFDeriv (s.lowerMass r hr0 hr m hm) β j = parisiFDeriv s β j := by
  funext x
  have H := (parisiF_C2_props (s.lowerMass r hr0 hr m hm) β j).1.1 x
  rw [parisiF_lowerMass_prefix s β r hr0 hr m hm hj] at H
  exact H.unique ((parisiF_C2_props s β j).1.1 x)

private theorem scheme_eq_of_fields {k : ℕ} {s t : RSBScheme k}
    (hm : s.m = t.m) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hm
  cases hq
  rfl

/-- The auxiliary base for the right variation: the two masses immediately
below the moved overlap are made equal. -/
noncomputable def section4StationarityBase {k : ℕ} (s : RSBScheme k)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k) : RSBScheme k :=
  s.lowerMass r hr0 hr (s.m (r - 1))
    ⟨le_rfl, s.m_mono' r (by omega) (r - 1) (by omega)⟩

/-- Actual fixed-level minimality for the opposite overlap variation. The
intermediate insertion is merged at two equal masses, including mass zero. -/
theorem section4Phi_stationarityBase_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {u : ℝ} (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    section4Phi (section4StationarityBase s r hr0 hr) β h (r + 1) (s.m r) (s.q r) ≤
      section4Phi (section4StationarityBase s r hr0 hr) β h (r + 1) (s.m r) u := by
  let b := section4StationarityBase s r hr0 hr
  have hm : s.m r ∈ Set.Icc (b.m (r + 1 - 1)) (b.m (r + 1)) := by
    simp only [b, section4StationarityBase, RSBScheme.lowerMass, Nat.add_sub_cancel,
      if_neg (show r + 1 ≠ r by omega)]
    exact ⟨s.m_mono' r (by omega) (r - 1) (by omega), s.m_mono r hr⟩
  have hq : s.q r ∈ Set.Icc (b.q (r + 1 - 1)) (b.q (r + 1)) := by
    exact ⟨le_rfl, s.q_mono r (by omega)⟩
  let si (u : ℝ) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :=
    b.insertLevel (r + 1) (by omega) (by omega) (s.m r) u hm hu
  have he (u : ℝ) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
      (si u hu).m (r - 1) = (si u hu).m (r - 1 + 1) := by
    simp [si, RSBScheme.insertLevel, section4Mass, b, section4StationarityBase,
      RSBScheme.lowerMass, show r - 1 + 1 = r by omega,
      show r - 1 < r + 1 by omega, show r - 1 ≠ r by omega]
  have heq : (si (s.q r) hq).mergeEqualMass (r - 1) (by omega) (he (s.q r) hq) = s := by
    apply scheme_eq_of_fields
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section4Mass, b, section4StationarityBase, RSBScheme.lowerMass]
      split_ifs <;> first | rfl | (congr 1; omega)
    · funext j
      simp only [RSBScheme.mergeEqualMass, skipLevel, si, RSBScheme.insertLevel,
        section5Rho, b, section4StationarityBase, RSBScheme.lowerMass]
      split_ifs <;> first | rfl | (congr 1; omega)
  have hb : section4Phi b β h (r + 1) (s.m r) (s.q r) = parisiFunctional s β h := by
    rw [← parisiFunctional_insertLevel b β h (r + 1) (by omega) (by omega) (s.m r) (s.q r) hm hq]
    change parisiFunctional (si (s.q r) hq) β h = _
    rw [← parisiFunctional_mergeEqualMass (si (s.q r) hq) (r - 1) (by omega) (he (s.q r) hq), heq]
  have H := hmin ((si u hu).mergeEqualMass (r - 1) (by omega) (he u hu))
  rw [parisiFunctional_mergeEqualMass] at H
  change parisiFunctional s β h ≤ parisiFunctional
    (b.insertLevel (r + 1) (by omega) (by omega) (s.m r) u hm hu) β h at H
  have hu' : u ∈ Set.Icc (b.q (r + 1 - 1)) (b.q (r + 1)) := hu
  exact hb.trans_le (H.trans_eq
    (parisiFunctional_insertLevel b β h (r + 1) (by omega) (by omega)
      (s.m r) u hm hu'))

/-- A minimum at the left endpoint has a nonnegative inward derivative. -/
theorem derivative_nonneg_of_min_at_left {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hmin : ∀ x ∈ Set.Icc a b, f a ≤ f x)
    (hd : HasDerivWithinAt f d (Set.Icc a b) a) : 0 ≤ d := by
  have hlocal : IsLocalMinOn f (Set.Icc a b) a :=
    (show IsMinOn f (Set.Icc a b) a from hmin).localize
  have ht : b - a ∈ posTangentConeAt (Set.Icc a b) a :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩)
  have H := hlocal.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt ht
  change 0 ≤ (b - a) * d at H
  nlinarith

/-- A zero-variance normalized mean is exactly evaluation, at every mass. -/
theorem pairedSecondMean_zero_variance {n : ℕ}
    (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (m : ℝ) (x y : Fin n → ℝ) :
    pairedSecondMean m 0 F G x y = G x y := by
  simp [pairedSecondMean, pairedTiltMean, tiltWeightPi, Real.exp_ne_zero]

private theorem stationarityBase_inner {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) :
    parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r))
      (parisiF (section4StationarityBase s r hr0 hr) β (k + 2 - (r + 1))) =
      parisiF s β (k + 2 - r) := by
  rw [show k + 2 - (r + 1) = k + 1 - r by omega]
  rw [show parisiF (section4StationarityBase s r hr0 hr) β (k + 1 - r) =
    parisiF s β (k + 1 - r) from
      parisiF_lowerMass_prefix s β r hr0 hr _ _ le_rfl]
  rw [show k + 2 - r = (k + 1 - r) + 1 by omega, parisiF]
  rw [show k + 1 - (k + 1 - r) = r by omega,
    show k + 2 - (k + 1 - r) = r + 1 by omega]

private theorem stationarityBase_inner_deriv {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) :
    stepD1 (parisiF (section4StationarityBase s r hr0 hr) β (k + 2 - (r + 1)))
      (parisiFDeriv (section4StationarityBase s r hr0 hr) β (k + 2 - (r + 1)))
      (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r)) = parisiFDeriv s β (k + 2 - r) := by
  let b := section4StationarityBase s r hr0 hr
  funext x
  have H := hasDerivAt_parisiStep_spatial (parisiF_hasLinearGrowth b β (k + 2 - (r + 1)))
    (parisiF_measurable b β _) (parisiF_C2_props b β _).2.1
    (parisiF_C2_props b β _).1.1 (parisiF_C2_props b β _).1.abs_first_le_one
    (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r)) x
  rw [stationarityBase_inner s β hr0 hr] at H
  exact H.unique ((parisiF_C2_props s β _).1.1 x)

/-- At the right variation's zero-length lower subinterval, all its outer
potentials are the corresponding original potentials. -/
theorem section4Cascade_stationarityBase_endpoint {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) {j : ℕ} (hj : j ≤ r) :
    scalarFieldCascade
      (fun l => section4Mass (section4StationarityBase s r hr0 hr) (r + 1) (s.m r) (k + 2 - l))
      (fun l => section5Variance (section4StationarityBase s r hr0 hr) β (r + 1)
        (k + 2 - l) (β ^ 2 * (s.q (r + 1) - s.q r)))
      (k + 2 - (r + 1) + 2 + j) = parisiF s β (k + 2 - r + j) := by
  let b := section4StationarityBase s r hr0 hr
  change scalarFieldCascade (fun l => section4Mass b (r + 1) (s.m r) (k + 2 - l))
    (fun l => section5Variance b β (r + 1) (k + 2 - l)
      (β ^ 2 * (s.q (r + 1) - s.q r))) _ = _
  induction j with
  | zero =>
    simp only [Nat.add_zero, section4Cascade_split b β (r := r + 1) (by omega) (by omega)]
    have hq : b.q = s.q := rfl
    rw [hq, Nat.add_sub_cancel, sub_self, stationarityBase_inner s β hr0 hr]
    funext x
    exact parisiStep_zero_var _ _ x
  | succ j ih =>
    rw [show k + 2 - (r + 1) + 2 + (j + 1) =
      (k + 2 - (r + 1) + 2 + j) + 1 by omega,
      scalarFieldCascade, ih (by omega),
      show k + 2 - r + (j + 1) = (k + 2 - r + j) + 1 by omega, parisiF]
    let l := k + 2 - (k + 2 - (r + 1) + 2 + j)
    have hl : l < r := by dsimp [l]; omega
    change parisiStep (section4Mass b (r + 1) (s.m r) l)
      (section5Variance b β (r + 1) l _) _ = _
    simp only [section4Mass, section5Variance, if_pos (show l < r + 1 by omega),
      if_neg (show l ≠ r + 1 by omega), if_neg (show ¬r + 1 < l by omega),
      if_neg (show l + 1 ≠ r + 1 by omega)]
    simp only [b, section4StationarityBase, RSBScheme.lowerMass, if_neg (Nat.ne_of_lt hl)]
    rw [show l = k + 1 - (k + 2 - r + j) by dsimp [l]; omega,
      show k + 1 - (k + 2 - r + j) + 1 = k + 2 - (k + 2 - r + j) by omega]

/-- The first normalized observable of the opposite variation is the square
of the original slope, because its outer variance is zero. -/
theorem section4VarianceQ_stationarityBase_endpoint_base {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (x y : Fin 1 → ℝ) :
    section4VarianceQ (section4StationarityBase s r hr0 hr) β (r + 1) (s.m r) 0
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y = (parisiFDeriv s β (k + 2 - r) (y 0)) ^ 2 := by
  simp only [section4VarianceQ]
  have hq : (section4StationarityBase s r hr0 hr).q = s.q := rfl
  rw [hq, Nat.add_sub_cancel, sub_self, pairedSecondMean_zero_variance,
    stationarityBase_inner_deriv s β hr0 hr]

/-- Explicit identification of the two endpoint observables, with the extra
zero-variance level accounted for. -/
theorem section4VarianceQ_stationarityBase_endpoint {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) {j : ℕ} (hj : j ≤ r - 1) (x y : Fin 1 → ℝ) :
    section4VarianceQ (section4StationarityBase s r hr0 hr) β (r + 1) (s.m r) (j + 1)
      (β ^ 2 * (s.q (r + 1) - s.q r)) x y =
      section4VarianceQ s β r (s.m (r - 1)) j 0 x y := by
  let b := section4StationarityBase s r hr0 hr
  have hq : b.q = s.q := rfl
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  induction j generalizing x y with
  | zero =>
    have hG : section4VarianceQ b β (r + 1) (s.m r) 0
        (β ^ 2 * (s.q (r + 1) - s.q r)) =
        fun _ y => (parisiFDeriv s β (k + 2 - r) (y 0)) ^ 2 := by
      funext x y
      exact section4VarianceQ_stationarityBase_endpoint_base s β hr0 hr x y
    change section4VarianceQ b β (r + 1) (s.m r) 1 _ x y = _
    conv_lhs => unfold section4VarianceQ
    dsimp only
    rw [hG, section4Cascade_stationarityBase_endpoint s β hr0 hr (j := 0) (by omega)]
    have hl : k + 2 - (k + 2 - (r + 1) + 2 + 0) = r - 1 := by omega
    simp only [hl, b, section4StationarityBase, RSBScheme.lowerMass,
      if_neg (show r - 1 ≠ r by omega), show r - 1 + 1 = r by omega,
      section4VarianceQ, sub_zero, parisiStep_zero_var, stepD1_parisiF_zero_variance, Nat.add_zero]
  | succ j ih =>
    have hG : section4VarianceQ b β (r + 1) (s.m r) (j + 1)
        (β ^ 2 * (s.q (r + 1) - s.q r)) = section4VarianceQ s β r (s.m (r - 1)) j 0 := by
      funext x y
      exact ih (by omega) x y
    change section4VarianceQ b β (r + 1) (s.m r) ((j + 1) + 1) _ x y = _
    conv_lhs => rw [section4VarianceQ]
    dsimp only
    rw [hG]
    conv_rhs => rw [section4VarianceQ]
    dsimp only
    rw [section4Cascade_stationarityBase_endpoint s β hr0 hr (j := j + 1) (by omega),
      section4Cascade_baseline s β hr0 (by omega) hzero (j := j) (by omega)]
    let l := k + 2 - (k + 2 - (r + 1) + 2 + (j + 1))
    have hl : l < r := by dsimp [l]; omega
    change pairedSecondMean (b.m l) (β ^ 2 * (b.q (l + 1) - b.q l)) _ _ x y = _
    simp only [b, section4StationarityBase, RSBScheme.lowerMass, if_neg (Nat.ne_of_lt hl)]
    rw [show l = k + 2 - (k + 2 - r + 2 + j) by dsimp [l]; omega,
      show k + 2 - r + (j + 1) = k + 2 - r + 1 + j by omega]

theorem section4TVarianceQ_stationarityBase_endpoint {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) :
    section4TVarianceQ (section4StationarityBase s r hr0 hr) β h (r + 1) (s.m r)
      (β ^ 2 * (s.q (r + 1) - s.q r)) = section4TVarianceQ s β h r (s.m (r - 1)) 0 := by
  have H := section4VarianceQ_stationarityBase_endpoint s β hr0 hr (j := r - 1) le_rfl
    (0 : Fin 1 → ℝ) (fun _ => h)
  simpa only [section4TVarianceQ, Nat.add_sub_cancel, show r - 1 + 1 = r by omega] using H

/-- The opposite inequality in Proposition 4.7, for a nonterminal mass. It
uses an actual fixed-level competitor and covers the initial overlap zero. -/
theorem section4_endpointQ_le_overlap_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hq : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4TVarianceQ s β h r (s.m (r - 1)) 0 ≤ s.q r := by
  let b := section4StationarityBase s r hr0 hr
  have hmass : b.m (r + 1 - 1) = s.m (r - 1) := by
    simp [b, section4StationarityBase, RSBScheme.lowerMass]
  have hqbase : b.q = s.q := rfl
  have hd := hasDerivWithinAt_section4Phi_overlap b β h (r := r + 1) (by omega) (by omega)
    (m := s.m r) ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
    (hmass ▸ hm.le) (u := s.q r) ⟨le_rfl, hq.le⟩
  rw [hmass, hqbase, section4TVarianceQ_stationarityBase_endpoint s β h hr0 hr] at hd
  have H := derivative_nonneg_of_min_at_left hq
    (fun u hu => section4Phi_stationarityBase_min s β h hr0 hr hmin hu) hd
  have hc : 0 < β ^ 2 * (s.m r - s.m (r - 1)) / 2 :=
    div_pos (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hm)) (by norm_num)
  nlinarith

/-- Proposition 4.7 for nonterminal levels. At boundary overlap zero or one
only the available inward direction is needed; all other overlaps require
strict neighbors. The compulsory last mass is not covered by this reduction. -/
theorem section4TVarianceQ_zero_eq_overlap_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r := by
  have hQ := section4TVarianceQ_mem_Icc s β h r (m := s.m (r - 1))
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ 0
  apply le_antisymm
  · rcases hright with hright | hright
    · exact section4_endpointQ_le_overlap_of_min s β h hr0 hr hβ hm hright hmin
    · simpa only [hright] using hQ.2
  · rcases hleft with hleft | hleft
    · exact section4_overlap_le_endpointQ_of_min s β h hr0 (by omega) hβ hm hleft hmin
    · simpa only [hleft] using hQ.1

/-- The paper's endpoint identity `U'(0)=q_r`, stated as an inward derivative
of the genuine function U. This also makes sense for a degenerate interval. -/
theorem hasDerivWithinAt_section4U_zero_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    HasDerivWithinAt (section4U s β h r) (s.q r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) 0 := by
  have H := hasDerivWithinAt_section4U s β h hr0 (by omega)
    (hm.trans_le (s.m_le_one (by omega))) (v := 0)
    ⟨le_rfl, mul_nonneg (sq_nonneg β)
      (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩
  rwa [section4TVarianceQ_zero_eq_overlap_of_min s β h hr0 hr hβ hm hleft hright hmin] at H

/-- The upper-overlap derivative vanishing in Proposition 4.8 follows from
the proved fixed-level stationarity, not from a supplied stationarity premise. -/
theorem hasDerivWithinAt_section4FirstVariation_upper_zero_of_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r)
    (hleft : s.q (r - 1) < s.q r ∨ s.q r = 0)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    HasDerivWithinAt (section4FirstVariation s β h r) 0
      (Set.Icc (s.q (r - 1)) (s.q r)) (s.q r) := by
  have H := hasDerivWithinAt_section4FirstVariation_overlap s β h hr0 (by omega)
    (hm.trans_le (s.m_le_one (by omega))) (u := s.q r)
    ⟨s.q_mono' r (by omega) (r - 1) (by omega), le_rfl⟩
  simpa only [sub_self, mul_zero,
    section4TVarianceQ_zero_eq_overlap_of_min s β h hr0 hr hβ hm hleft hright hmin] using H

/-- Numerical inward derivative in (4.54) when the physical interval has
positive length, so derivative uniqueness is justified. -/
theorem derivWithin_section4U_zero_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    derivWithin (section4U s β h r)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) 0 = s.q r := by
  have ha : 0 < β ^ 2 * (s.q r - s.q (r - 1)) :=
    mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hleft)
  exact (hasDerivWithinAt_section4U_zero_of_min s β h hr0 hr hβ hm (Or.inl hleft)
    hright hmin).derivWithin (uniqueDiffOn_Icc ha 0 ⟨le_rfl, ha.le⟩)

/-- Numerical vanishing of the inward derivative `f'(q_r)` in Proposition
4.8 on a positive-length interval. -/
theorem derivWithin_section4FirstVariation_upper_zero_of_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hleft : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    derivWithin (section4FirstVariation s β h r)
      (Set.Icc (s.q (r - 1)) (s.q r)) (s.q r) = 0 :=
  (hasDerivWithinAt_section4FirstVariation_upper_zero_of_min s β h hr0 hr hβ hm
    (Or.inl hleft) hright hmin).derivWithin (uniqueDiffOn_Icc hleft _ ⟨hleft.le, le_rfl⟩)

end SpinGlass.Targets
