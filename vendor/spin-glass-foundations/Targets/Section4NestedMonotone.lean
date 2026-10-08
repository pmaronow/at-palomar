module

public import Targets.Section4SplitMonotone
public import Targets.TalagrandSection5Zero

@[expose] public section

/-!
# Split-variance comparison through the actual Section 4 recursion

The split-variance comparison is propagated through the unchanged outer levels
of `section4T`. Order preservation reuses the existing N-site Parisi-step theorem
via its one-coordinate specialization. No endpoint derivative is assumed.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem one_coordinate_growth {A : ℝ → ℝ} (hA : HasLinearGrowth A)
    (hmeas : Measurable A) : GuerraGrowth (fun x : Fin 1 → ℝ => A (x 0)) := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  refine ⟨hmeas.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
  intro x
  simpa [l1] using hb (x 0)

/-- The scalar order-preservation adapter to the existing N-site theorem. -/
theorem parisiStep_mono_of_growth {A B : ℝ → ℝ} {m v : ℝ} (hm : 0 ≤ m)
    (hA : HasLinearGrowth A) (hmeasA : Measurable A)
    (hB : HasLinearGrowth B) (hmeasB : Measurable B)
    (hAB : ∀ x, A x ≤ B x) (x : ℝ) : parisiStep m v A x ≤ parisiStep m v B x := by
  have H := parisiStepPi_mono_growth (v := v) hm (one_coordinate_growth hA hmeasA)
    (one_coordinate_growth hB hmeasB) (fun y => hAB (y 0)) (fun _ => x)
  have hAs : parisiStepPi 1 m v (fun y => A (y 0)) (fun _ => x) = parisiStep m v A x := by
    simpa using parisiStepPi_sum (n := 1) m v hA hmeasA (fun _ => x)
  have hBs : parisiStepPi 1 m v (fun y => B (y 0)) (fun _ => x) = parisiStep m v B x := by
    simpa using parisiStepPi_sum (n := 1) m v hB hmeasB (fun _ => x)
  rwa [hAs, hBs] at H

/-- The two steps at the inserted level are exactly the split transform whose
variance derivative was proved in (4.11). -/
theorem section4Cascade_split {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m v : ℝ) :
    scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
      (fun j => section5Variance s β r (k + 2 - j) v) (k + 2 - r + 2) =
      parisiStep (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
        (parisiStep m v (parisiF s β (k + 2 - r))) := by
  rw [show k + 2 - r + 2 = (k + 2 - r + 1) + 1 by omega,
    scalarFieldCascade, section4Cascade_inserted s β (by omega)]
  have hi : k + 2 - (k + 2 - r + 1) = r - 1 := by omega
  have hprev : r - 1 < r := by omega
  have hne : r - 1 ≠ r := by omega
  have hng : ¬r < r - 1 := by omega
  have hnext : r - 1 + 1 = r := by omega
  rw [hi]
  simp only [section4Mass, section5Variance, if_pos hprev, if_neg hng,
    if_neg hne, if_pos hnext]

/-- Monotonicity survives each actual outer scalar level after the split. -/
theorem section4Cascade_monotoneOn {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m)
    {j : ℕ} (hj : j ≤ r - 1) (x : ℝ) :
    MonotoneOn (fun v => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) x)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  induction j generalizing x with
  | zero =>
    simp only [Nat.add_zero, section4Cascade_split s β hr0 hr]
    exact monotoneOn_split_parisiF s β (k + 2 - r) hm
      (s.m_nonneg (by omega)) hmm _ x
  | succ j ih =>
    intro v hv w hw hvw
    dsimp only
    rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
      scalarFieldCascade, scalarFieldCascade]
    have hp : k + 2 - (k + 2 - r + 2 + j) < r := by omega
    have hpn : k + 2 - (k + 2 - r + 2 + j) ≠ r := by omega
    have hpn' : ¬r < k + 2 - (k + 2 - r + 2 + j) := by omega
    have hpn'' : k + 2 - (k + 2 - r + 2 + j) + 1 ≠ r := by omega
    simp only [section4Mass, section5Variance, if_pos hp, if_neg hpn,
      if_neg hpn', if_neg hpn'']
    have hAv := scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j)
    have hAw := scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) w) (k + 2 - r + 2 + j)
    exact parisiStep_mono_of_growth (m := s.m (k + 2 - (k + 2 - r + 2 + j)))
      (s.m_nonneg (by omega)) hAv.2.1 hAv.1 hAw.2.1 hAw.1
      (fun y => ih (by omega) y hv hw hvw) x

/-- Monotonicity of the actual full Section 4 scalar function, including the
split-variance endpoints and every outer zero-mass level. -/
theorem monotoneOn_section4T {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) :
    MonotoneOn (section4T s β h r m) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  have H := section4Cascade_monotoneOn s β hr0 hr hm hmm (j := r - 1) le_rfl h
  have hi : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  simpa only [section4T, hi] using! H

/-- Continuity of the full scalar recursion on the closed split interval is
inherited from the already checked paired recursion and its zero-lambda identity. -/
theorem continuousOn_section4T {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) :
    ContinuousOn (section4T s β h r m) (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
  have H := splitScalarCascade_good (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j)) (k + 3 - r) (k + 3)
  have hc : Continuous (fun v => section5V s β h r m v 0) := by
    simpa only [section5V, Function.comp_def] using! H.contF.comp
      (show Continuous (fun v : ℝ => (v, (0 : ℝ), (h, h))) by fun_prop)
  apply (hc.div_const 2).continuousOn.congr
  intro v hv
  dsimp only
  rw [section5V_zero_eq_two_section4T s β h hr0 hr hm hv]
  ring

/-- At zero split variance the inserted mass is irrelevant, even if it is zero
or outside the admissible mass range. -/
theorem section4T_zero_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m : ℝ) :
    section4T s β h r m 0 = parisiF s β (k + 2) h := by
  have he {j : ℕ} (hj : j ≤ r - 1) :
      scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) 0) (k + 2 - r + 2 + j) =
      scalarFieldCascade (fun l => section4Mass s r (s.m (r - 1)) (k + 2 - l))
        (fun l => section5Variance s β r (k + 2 - l) 0) (k + 2 - r + 2 + j) := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, section4Cascade_split s β hr0 hr]
      congr 1
      funext x
      simp only [parisiStep_zero_var]
    | succ j ih =>
      rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
        scalarFieldCascade, scalarFieldCascade, ih (by omega)]
      have hp : k + 2 - (k + 2 - r + 2 + j) < r := by omega
      simp only [section4Mass, if_pos hp]
  have hi : k + 2 - r + 2 + (r - 1) = k + 3 := by omega
  have heT : section4T s β h r m 0 = section4T s β h r (s.m (r - 1)) 0 := by
    simpa only [section4T, hi] using congrFun (he (j := r - 1) le_rfl) h
  rw [heT]
  apply section4T_baseline s β h hr0 hr
  exact ⟨le_refl 0, mul_nonneg (sq_nonneg β)
    (sub_nonneg.mpr (s.q_mono' r (by omega) (r - 1) (by omega)))⟩

/-- The original scalar value is the lower endpoint of the full split-variance
comparison for an increased inserted mass. -/
theorem parisiF_le_section4T {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    parisiF s β (k + 2) h ≤ section4T s β h r m v := by
  rw [← section4T_zero_variance s β h hr0 hr m]
  exact monotoneOn_section4T s β h hr0 hr hm hmm
    ⟨le_refl 0, hv.1.trans hv.2⟩ hv hv.1

end SpinGlass.Targets
