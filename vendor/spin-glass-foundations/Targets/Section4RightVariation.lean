module

public import Targets.TalagrandRightZero
public import Targets.Section4NestedMonotone

@[expose] public section

/-!
# Variance comparison for the actual dual Section 4 recursion

The right split is the existing two-step transform reflected by `v ↦ a-v`,
with inner mass `m_r` and outer mass `m`. Thus the checked (4.11) and its
closed-interval comparison apply without new Gaussian calculus. The resulting
antimonotonicity propagates through every unchanged outer level of the actual
`section4RightT`, including the final interval ending at overlap 1.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The dual split derivative is the reflected (4.11). Inner and outer masses
are written explicitly to avoid exchanging the two logarithmic transforms. -/
theorem hasDerivAt_right_split_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m m' : ℝ} (hm' : m' ∈ Set.Icc 0 1) (a x : ℝ) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => parisiStep m w (parisiStep m' (a - w) (parisiF s β j)) x)
      ((m - m') / 2 * ∫ z,
        (stepD1 (parisiF s β j) (parisiFDeriv s β j) m' (a - v)
          (x + Real.sqrt v * z)) ^ 2 *
        tiltWeight m v (parisiStep m' (a - v) (parisiF s β j)) x z ∂(gaussianReal 0 1)) v := by
  have H := (hasDerivAt_split_parisiF s β j hm' m a x
    (v := a - v) (by constructor <;> linarith [hv.1, hv.2])).comp v
      ((hasDerivAt_id v).const_sub a)
  simp only [Function.comp_def, sub_sub_cancel] at H
  apply H.congr_deriv
  ring

/-- Closed-interval antimonotonicity follows by reflection of the existing
closed-interval monotonicity theorem, so no endpoint derivative is assumed. -/
theorem antitoneOn_right_split_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m m' : ℝ} (hm' : m' ∈ Set.Icc 0 1) (hm : 0 ≤ m) (hmm : m ≤ m') (a x : ℝ) :
    AntitoneOn (fun v => parisiStep m v (parisiStep m' (a - v) (parisiF s β j)) x)
      (Set.Icc 0 a) := by
  intro v hv w hw hvw
  have hmono := monotoneOn_split_parisiF s β j hm' hm hmm a x
  have H := hmono
    (a := a - w) (b := a - v)
    (by constructor <;> linarith [hw.1, hw.2])
    (by constructor <;> linarith [hv.1, hv.2]) (by linarith)
  simpa only [sub_sub_cancel] using H

/-- The actual two split levels in the dual recursion. -/
theorem section4RightCascade_split {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m v : ℝ) :
    scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
      (fun j => section5RightVariance s β r (k + 2 - j) v) (k + 1 - r + 2) =
      parisiStep m v (parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
        (parisiF s β (k + 1 - r))) := by
  rw [show k + 1 - r + 2 = (k + 1 - r + 1) + 1 by omega,
    scalarFieldCascade, scalarFieldCascade, section4RightCascade_prefix s β hr m v le_rfl]
  have hi : k + 2 - (k + 1 - r + 1) = r := by omega
  have hi' : k + 2 - (k + 1 - r) = r + 1 := by omega
  simp only [hi, hi', section4Mass, section5RightVariance, lt_self_iff_false,
    if_false, if_true, if_neg (show ¬r + 1 < r by omega),
    if_neg (show r + 1 ≠ r by omega), Nat.add_sub_cancel]

/-- The reflected derivative for the actual two-level prefix of the right
construction. This is not yet the derivative through its remaining outer levels. -/
theorem hasDerivAt_section4RightCascade_split {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m x : ℝ) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    HasDerivAt (fun w => scalarFieldCascade (fun j => section4Mass s r m (k + 2 - j))
        (fun j => section5RightVariance s β r (k + 2 - j) w) (k + 1 - r + 2) x)
      ((m - s.m r) / 2 * ∫ z,
        (stepD1 (parisiF s β (k + 1 - r)) (parisiFDeriv s β (k + 1 - r))
          (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v) (x + Real.sqrt v * z)) ^ 2 *
        tiltWeight m v (parisiStep (s.m r) (β ^ 2 * (s.q (r + 1) - s.q r) - v)
          (parisiF s β (k + 1 - r))) x z ∂(gaussianReal 0 1)) v := by
  simp only [section4RightCascade_split s β hr]
  exact hasDerivAt_right_split_parisiF s β (k + 1 - r)
    ⟨s.m_nonneg hr, s.m_le_one hr⟩ _ x hv

/-- Each fixed outer level preserves the reversed comparison. -/
theorem section4RightCascade_antitoneOn {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r)
    {j : ℕ} (hj : j ≤ r) (x : ℝ) :
    AntitoneOn (fun v => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j) x)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) := by
  induction j generalizing x with
  | zero =>
    simp only [Nat.add_zero, section4RightCascade_split s β hr]
    exact antitoneOn_right_split_parisiF s β (k + 1 - r)
      ⟨s.m_nonneg hr, s.m_le_one hr⟩ hm hmm _ x
  | succ j ih =>
    intro v hv w hw hvw
    dsimp only
    rw [show k + 1 - r + 2 + (j + 1) = (k + 1 - r + 2 + j) + 1 by omega,
      scalarFieldCascade, scalarFieldCascade]
    have hp : k + 2 - (k + 1 - r + 2 + j) < r := by omega
    simp only [section4Mass, section5RightVariance, if_pos hp]
    have hAv := scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) v) (k + 1 - r + 2 + j)
    have hAw := scalarFieldCascade_props (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5RightVariance s β r (k + 2 - l) w) (k + 1 - r + 2 + j)
    exact parisiStep_mono_of_growth (m := s.m (k + 2 - (k + 1 - r + 2 + j)))
      (s.m_nonneg (by omega)) hAw.2.1 hAw.1 hAv.2.1 hAv.1
      (fun y => ih (by omega) y hv hw hvw) x

/-- The full actual dual scalar recursion is antitone in the split variance,
including both endpoints and the final overlap interval. -/
theorem antitoneOn_section4RightT {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) :
    AntitoneOn (section4RightT s β h r m)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) := by
  have H := section4RightCascade_antitoneOn s β hr hm hmm (j := r) le_rfl h
  simpa only [section4RightT, show k + 1 - r + 2 + r = k + 3 by omega] using! H

/-- Continuity of the actual full dual recursion is inherited from the paired
zero-coupling identity, with no endpoint differentiability hypothesis. -/
theorem continuousOn_section4RightT {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) :
    ContinuousOn (section4RightT s β h r m)
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) := by
  have H := splitScalarCascade_good (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightVariance_continuous s β r (k + 2 - j)) (k + 2 - r) (k + 3)
  have hc : Continuous (fun v => section5RightV s β h r m v 0) := by
    simpa only [section5RightV, Function.comp_def] using! H.contF.comp
      (show Continuous (fun v : ℝ => (v, (0 : ℝ), (h, h))) by fun_prop)
  apply (hc.div_const 2).continuousOn.congr
  intro v hv
  dsimp only
  rw [section5RightV_zero_eq_two_section4RightT s β h hr hm hv]
  ring

/-- At zero split variance the newly inserted scalar mass has no effect. -/
theorem section4RightT_zero_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (m : ℝ) :
    section4RightT s β h r m 0 = parisiF s β (k + 2) h := by
  have he {j : ℕ} (hj : j ≤ r) :
      scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) 0) (k + 1 - r + 2 + j) =
      scalarFieldCascade (fun l => section4Mass s r (s.m r) (k + 2 - l))
        (fun l => section5RightVariance s β r (k + 2 - l) 0) (k + 1 - r + 2 + j) := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, section4RightCascade_split s β hr]
      funext x
      simp only [parisiStep_zero_var]
    | succ j ih =>
      rw [show k + 1 - r + 2 + (j + 1) = (k + 1 - r + 2 + j) + 1 by omega,
        scalarFieldCascade, scalarFieldCascade, ih (by omega)]
      have hp : k + 2 - (k + 1 - r + 2 + j) < r := by omega
      simp only [section4Mass, if_pos hp]
  have heT : section4RightT s β h r m 0 = section4RightT s β h r (s.m r) 0 := by
    simpa only [section4RightT, show k + 1 - r + 2 + r = k + 3 by omega]
      using congrFun (he (j := r) le_rfl) h
  rw [heT]
  exact section4RightT_baseline s β h hr ⟨le_rfl,
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono r hr))⟩

/-- Decreasing the mass on the lower split interval can only decrease the
actual dual scalar value, with an endpoint-safe proof. -/
theorem section4RightT_le_parisiF {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (hmm : m ≤ s.m r) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :
    section4RightT s β h r m v ≤ parisiF s β (k + 2) h := by
  rw [← section4RightT_zero_variance s β h hr m]
  exact antitoneOn_section4RightT s β h hr hm hmm
    ⟨le_rfl, hv.1.trans hv.2⟩ hv hv.1

end SpinGlass.Targets
