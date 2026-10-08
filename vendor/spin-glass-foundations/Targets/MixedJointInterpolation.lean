module

public import Targets.MixedNestedVariance
public import Targets.MixedCascadeContinuity
public import Targets.CoupledJointInterpolation

@[expose] public section

/-!
# Joint differentiation of the genuine mixed interpolation

Finite variance comparisons furnish anchored domination. The existing proved
joint Gaussian log-Laplace theorem then differentiates the time and both fields
together. A zero variance is permitted when it is locally constant; no
partial-to-joint differentiability inference is used.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem mixedLevelHeatBound_nonneg (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m : ℕ → ℝ) (l : ℕ) : 0 ≤ mixedLevelHeatBound n mode m l := by
  unfold mixedLevelHeatBound
  cases mode l <;> unfold constrainedLinearHeatBound <;> positivity

theorem mixedConstrainedCascade_variance_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l j : ℕ) (x y : Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |mixedVectorCascade n mode m (Function.update v l a) (constrainedPairFieldBase n U u)
        (l + 1 + j) x y -
      mixedVectorCascade n mode m (Function.update v l b) (constrainedPairFieldBase n U u)
        (l + 1 + j) x y| ≤ mixedLevelHeatBound n mode m l * |a - b| := by
  let F := fun z => mixedVectorCascade n mode m (Function.update v l z)
    (constrainedPairFieldBase n U u) (l + 1 + j) x y
  have H := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := F) (C := mixedLevelHeatBound n mode m l)
    (fun z hz => (hasDerivAt_mixedConstrainedCascade_variance U u mode m v hm hv l j x y hz).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using
      mixedConstrainedCascade_variance_deriv_abs_le U u mode m v hm hv l j x y hz) hb ha
  simpa only [Real.norm_eq_abs] using H

theorem mixedVectorCascade_congr_variance (mode : ℕ → Section5GaussianMode)
    (m v v' : ℕ → ℝ) (j : ℕ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (he : ∀ l < j, v l = v' l) :
    mixedVectorCascade n mode m v F j = mixedVectorCascade n mode m v' F j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mixedVectorCascade, he j (by omega), ih (fun l hl => he l (by omega))]

theorem mixedConstrainedCascade_variances_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v v' : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (hv' : ∀ i, 0 ≤ v' i)
    (j : ℕ) (hface : ∀ l < j, v l = v' l ∨ (0 < v l ∧ 0 < v' l)) (x y : Fin n → ℝ) :
    |mixedVectorCascade n mode m v' (constrainedPairFieldBase n U u) j x y -
      mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y| ≤
      ∑ l ∈ Finset.range j, mixedLevelHeatBound n mode m l * |v' l - v l| := by
  classical
  let V (i l : ℕ) := if l < i then v' l else v l
  let F (w : ℕ → ℝ) := mixedVectorCascade n mode m w (constrainedPairFieldBase n U u) j x y
  have hV (i l : ℕ) : 0 ≤ V i l := by
    dsimp [V]
    split_ifs <;> first | exact hv' l | exact hv l
  have H {i : ℕ} (hi : i ≤ j) : |F (V i) - F v| ≤
      ∑ l ∈ Finset.range i, mixedLevelHeatBound n mode m l * |v' l - v l| := by
    induction i with
    | zero => simp [V]
    | succ i ih =>
      have hstep : |F (V (i + 1)) - F (V i)| ≤ mixedLevelHeatBound n mode m i * |v' i - v i| := by
        have hleft : V (i + 1) = Function.update (V i) i (v' i) := by
          funext l
          by_cases hl : l = i
          · subst l; simp [V]
          · simp only [Function.update_of_ne hl, V,
              show (l < i + 1) = (l < i) by apply propext; omega]
        have hright : V i = Function.update (V i) i (v i) := by
          symm
          apply Function.update_eq_self_iff.mpr
          simp [V]
        rcases hface i (by omega) with he | hp
        · rw [hleft, ← he, ← hright]
          simp
        · have H := mixedConstrainedCascade_variance_dist_le U u mode m (V i) hm (hV i)
            i (j - (i + 1)) x y hp.2 hp.1
          have hj : i + 1 + (j - (i + 1)) = j := by omega
          rw [hj, ← hleft, ← hright] at H
          exact H
      rw [Finset.sum_range_succ]
      exact (abs_sub_le (F (V (i + 1))) (F (V i)) (F v)).trans (by linarith [ih (by omega)])
  have he : F (V j) = F v' := congrFun (congrFun
    (mixedVectorCascade_congr_variance mode m (V j) v' j (constrainedPairFieldBase n U u)
      (fun l hl => by simp [V, hl])) x) y
  simpa only [he] using H (i := j) le_rfl

theorem mixedConstrainedCascade_fields_dist_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y x' y' : Fin n → ℝ) :
    |mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y -
      mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x' y'| ≤
      l1 (x - x') + l1 (y - y') := by
  have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun a _ => (hasDerivAt_mixedCascadeSpatialLine U u mode m v hm hv j
      (x - x') (y - y') x' y' a).hasDerivWithinAt)
    (C := l1 (x - x') + l1 (y - y'))
    (fun a _ => by
      simpa only [Real.norm_eq_abs, mixedCascadeSpatialFirst] using
        (mixedConstrainedCascadeD_field_abs_le U u mode m v hm hv j
          (x - x') (y - y') (x' + a • (x - x')) (y' + a • (y - y'))))
  simpa only [zero_smul, one_smul, add_zero, show x' + (x - x') = x by abel,
    show y' + (y - y') = y by abel, Real.norm_eq_abs] using H

theorem mixedConstrainedCascade_joint_dist_le (U U' : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v v' : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (hv' : ∀ i, 0 ≤ v' i)
    (j : ℕ) (hface : ∀ l < j, v l = v' l ∨ (0 < v l ∧ 0 < v' l)) (x y x' y' : Fin n → ℝ) :
    |mixedVectorCascade n mode m v' (constrainedPairFieldBase n U' u) j x' y' -
      mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y| ≤
      2 * Fintype.card (Config n) * ‖U' - U‖ +
        (∑ l ∈ Finset.range j, mixedLevelHeatBound n mode m l * |v' l - v l|) +
        l1 (x' - x) + l1 (y' - y) := by
  have h1 := mixedConstrainedList_disorder_dist_le mode m v' (List.range j).reverse
    (fun i _ => hm i) (fun i _ => hv' i) U' U u x' y'
  simp only [← mixedVectorCascade_eq_list] at h1
  have h2 := mixedConstrainedCascade_variances_dist_le U u mode m v v' hm hv hv' j hface x' y'
  have h3 := mixedConstrainedCascade_fields_dist_le U u mode m v hm hv j x' y' x y
  have h4 := abs_sub_le
    (mixedVectorCascade n mode m v' (constrainedPairFieldBase n U' u) j x' y')
    (mixedVectorCascade n mode m v' (constrainedPairFieldBase n U u) j x' y')
    (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y)
  have h5 := abs_sub_le
    (mixedVectorCascade n mode m v' (constrainedPairFieldBase n U u) j x' y')
    (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x' y')
    (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y)
  nlinarith [uAbs_le_card_mul_norm n (U' - U)]

theorem mixedConstrainedCascade_path_anchored_bound
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w) (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ a in 𝓝 w, ∀ x y : Fin n → ℝ,
      |mixedVectorCascade n mode m (fun l => v l a) (constrainedPairFieldBase n (U a) u) j x y -
        mixedVectorCascade n mode m (fun l => v l w) (constrainedPairFieldBase n (U w) u) j x y| ≤ K * |a - w| := by
  classical
  obtain ⟨CU, hCU, hbU⟩ := hU.isBigO_sub.exists_pos
  have hvl (l : Fin j) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ a in 𝓝 w, |v l a - v l w| ≤ C * |a - w| := by
    obtain ⟨C, hC, hb⟩ := (hv l l.isLt).isBigO_sub.exists_pos
    exact ⟨C, hC, by simpa only [Real.norm_eq_abs] using hb.bound⟩
  choose Cv hCv hbv using hvl
  have hf (l : Fin j) : ∀ᶠ a in 𝓝 w, v l w = v l a ∨ (0 < v l w ∧ 0 < v l a) := by
    rcases hface l l.isLt with hp | hz
    · filter_upwards [(hv l l.isLt).continuousAt.eventually (lt_mem_nhds hp)] with a ha
      exact Or.inr ⟨hp, ha⟩
    · filter_upwards [hz] with a ha
      exact Or.inl (hz.self_of_nhds.trans ha.symm)
  let K := 2 * Fintype.card (Config n) * CU + ∑ l : Fin j, mixedLevelHeatBound n mode m l * Cv l
  refine ⟨K, add_nonneg (by positivity) (Finset.sum_nonneg fun l _ =>
    mul_nonneg (mixedLevelHeatBound_nonneg n mode m l) (hCv l).le), ?_⟩
  filter_upwards [hbU.bound, Filter.eventually_all.mpr hbv, Filter.eventually_all.mpr hf, hnonneg] with a haU hav haf han
  intro x y
  have H := mixedConstrainedCascade_joint_dist_le (U w) (U a) u mode m
    (fun l => v l w) (fun l => v l a) hm hnonneg.self_of_nhds han j
    (fun l hl => haf ⟨l, hl⟩) x y x y
  simp only [sub_self, l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at H
  rw [← Fin.sum_univ_eq_sum_range] at H
  have hsum : (∑ l : Fin j, mixedLevelHeatBound n mode m l * |v l a - v l w|) ≤
      (∑ l : Fin j, mixedLevelHeatBound n mode m l * Cv l) * |a - w| := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hav l) (mixedLevelHeatBound_nonneg n mode m l)
  change ‖U a - U w‖ ≤ CU * ‖a - w‖ at haU
  rw [Real.norm_eq_abs] at haU
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_left haU (show 0 ≤ 2 * (Fintype.card (Config n) : ℝ) by positivity)]

/-- Genuine joint time-and-fields differentiability for every mixed order and
every active variance face. Locally fixed zero levels are included. -/
theorem differentiableAt_mixedConstrainedCascade_joint
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w) (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : CoupledJointField n =>
      mixedVectorCascade n mode m (fun l => v l q.1)
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y) := by
  induction j generalizing x y with
  | zero => exact differentiableAt_constrainedPairFieldBase_joint u hU x y
  | succ j ih =>
    let F : CoupledJointField n → ℝ := fun q => mixedVectorCascade n mode m (fun l => v l q.1)
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
    have hvj (l : ℕ) (hl : l < j) := hv l (show l < j + 1 by omega)
    have hfj (l : ℕ) (hl : l < j) := hface l (show l < j + 1 by omega)
    have hFd (x y : Fin n → ℝ) : DifferentiableAt ℝ F (w, x, y) := ih hvj hfj x y
    have hFm : ∀ᶠ a in 𝓝 w,
        Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)) := by
      filter_upwards [hnonneg] with a ha
      exact (mixedConstrainedCascade_growth (U a) u mode m (fun l => v l a) hm ha j).measurable
    have hFg : CoupledGrowth (fun x y => F (w, x, y)) :=
      mixedConstrainedCascade_growth (U w) u mode m (fun l => v l w) hm hnonneg.self_of_nhds j
    have hFs (x y x' y' : Fin n → ℝ) : |F (w, x, y) - F (w, x', y')| ≤
        l1 (x - x') + l1 (y - y') :=
      mixedConstrainedCascade_fields_dist_le (U w) u mode m (fun l => v l w) hm
        hnonneg.self_of_nhds j x y x' y'
    obtain ⟨K, hK, hKbound⟩ := mixedConstrainedCascade_path_anchored_bound U u mode m v hm j hU hvj hnonneg hfj
    have hb : DifferentiableAt ℝ (fun a => Real.sqrt (v j a)) w := by
      rcases hface j (by omega) with hp | hz
      · exact (Real.hasDerivAt_sqrt hp.ne').differentiableAt.comp w (hv j (by omega))
      · apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hz] with a ha
        simp [ha]
    have H {p : ℕ} (A B : Fin p → Fin n → ℝ) :=
      differentiableAt_jointGaussianStep F hb (m j) A B hFd hFm hFg hFs hK hKbound x y
    change DifferentiableAt ℝ (fun q : CoupledJointField n =>
      mixedVectorStep n (mode j) (m j) (v j q.1) (fun x y => F (q.1, x, y)) q.2.1 q.2.2) (w, x, y)
    cases he : mode j with
    | independent =>
      have H' := H (independentLeftDirection n) (independentRightDirection n)
      simp only [jointGaussianStep_eq_linearStep, coupledLinearStep_independent] at H'
      apply H'.congr_of_eventuallyEq
      filter_upwards [(continuous_fst.tendsto (w, x, y)).eventually hnonneg] with q hq
      exact congrFun (congrFun
        (mixedVectorStep_independent_eq (m j) (v j q.1)
          (mixedConstrainedCascade_growth (U q.1) u mode m (fun l => v l q.1) hm hq j)) q.2.1) q.2.2
    | shared =>
      have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
      simpa only [jointGaussianStep_eq_linearStep, coupledLinearStep_shared, mixedVectorStep_shared_eq] using H'
    | opposite =>
      have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -Pi.single i 1)
      simpa only [jointGaussianStep_eq_linearStep, coupledLinearStep_opposite] using H'

/-- The actual simultaneously varying mixed cascade has the proved time
component of its joint Fréchet derivative. -/
theorem hasDerivAt_mixedConstrainedCascade_path_fderiv
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {w : ℝ}
    (hU : DifferentiableAt ℝ U w) (hv : ∀ l < j, DifferentiableAt ℝ (v l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) (x y : Fin n → ℝ) :
    HasDerivAt (fun a => mixedVectorCascade n mode m (fun l => v l a)
      (constrainedPairFieldBase n (U a) u) j x y)
      ((fderiv ℝ (fun q : CoupledJointField n => mixedVectorCascade n mode m (fun l => v l q.1)
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y)) (1, 0, 0)) w := by
  exact (differentiableAt_mixedConstrainedCascade_joint U u mode m v hm j hU hv hnonneg hface x y).hasFDerivAt.comp_hasDerivAt w
    ((hasDerivAt_id w).prodMk ((hasDerivAt_const w x).prodMk (hasDerivAt_const w y)))

end SpinGlass.Targets
