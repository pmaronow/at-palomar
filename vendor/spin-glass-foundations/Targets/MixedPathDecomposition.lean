module

public import Targets.MixedJointInterpolation
public import Targets.MixedDisorderInterpolation
public import Targets.CoupledPathDecomposition

@[expose] public section

/-!
# Explicit differentiation of the actual simultaneous mixed path

Independent finite disorder/variance parameters are differentiated using the
existing Gaussian Fréchet theorem. Restriction to the active variance face
then identifies the derivative with the actual disorder direction and original
level heat contributions. Zero coordinates are masked to constants, so no
derivative at a varying zero variance is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

section MultiParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P]

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
theorem mixedConstrainedCascade_multi_anchored_bound
    (U : P → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {p : P}
    (hU : DifferentiableAt ℝ U p) (hv : ∀ l < j, DifferentiableAt ℝ (v l) p)
    (hnonneg : ∀ᶠ a in 𝓝 p, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l p ∨ (v l =ᶠ[𝓝 p] fun _ => 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ a in 𝓝 p, ∀ x y : Fin n → ℝ,
      |mixedVectorCascade n mode m (fun l => v l a) (constrainedPairFieldBase n (U a) u) j x y -
        mixedVectorCascade n mode m (fun l => v l p) (constrainedPairFieldBase n (U p) u) j x y| ≤
        K * ‖a - p‖ := by
  classical
  obtain ⟨CU, hCU, hbU⟩ := hU.isBigO_sub.exists_pos
  have hvl (l : Fin j) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ a in 𝓝 p, |v l a - v l p| ≤ C * ‖a - p‖ := by
    obtain ⟨C, hC, hb⟩ := (hv l l.isLt).isBigO_sub.exists_pos
    exact ⟨C, hC, by simpa only [Real.norm_eq_abs] using hb.bound⟩
  choose Cv hCv hbv using hvl
  have hf (l : Fin j) : ∀ᶠ a in 𝓝 p,
      v l p = v l a ∨ (0 < v l p ∧ 0 < v l a) := by
    rcases hface l l.isLt with hp | hz
    · filter_upwards [(hv l l.isLt).continuousAt.eventually (lt_mem_nhds hp)] with a ha
      exact Or.inr ⟨hp, ha⟩
    · filter_upwards [hz] with a ha
      exact Or.inl (hz.self_of_nhds.trans ha.symm)
  let K := 2 * Fintype.card (Config n) * CU + ∑ l : Fin j, mixedLevelHeatBound n mode m l * Cv l
  refine ⟨K, add_nonneg (by positivity) (Finset.sum_nonneg fun l _ =>
    mul_nonneg (mixedLevelHeatBound_nonneg n mode m l) (hCv l).le), ?_⟩
  filter_upwards [hbU.bound, Filter.eventually_all.mpr hbv,
    Filter.eventually_all.mpr hf, hnonneg] with a haU hav haf han
  intro x y
  have H := mixedConstrainedCascade_joint_dist_le (U p) (U a) u mode m
    (fun l => v l p) (fun l => v l a) hm hnonneg.self_of_nhds han j
    (fun l hl => haf ⟨l, hl⟩) x y x y
  simp only [sub_self, l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at H
  rw [← Fin.sum_univ_eq_sum_range] at H
  have hsum : (∑ l : Fin j, mixedLevelHeatBound n mode m l * |v l a - v l p|) ≤
      (∑ l : Fin j, mixedLevelHeatBound n mode m l * Cv l) * ‖a - p‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hav l) (mixedLevelHeatBound_nonneg n mode m l)
  change ‖U a - U p‖ ≤ CU * ‖a - p‖ at haU
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_left haU
    (show 0 ≤ 2 * (Fintype.card (Config n) : ℝ) by positivity)]

/-- Genuine finite-dimensional parameter differentiability, with arbitrary
mixed mode order. The Gaussian analytic theorem is reused unchanged. -/
theorem differentiableAt_mixedConstrainedCascade_multi
    (U : P → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {p : P}
    (hU : DifferentiableAt ℝ U p) (hv : ∀ l < j, DifferentiableAt ℝ (v l) p)
    (hnonneg : ∀ᶠ a in 𝓝 p, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l p ∨ (v l =ᶠ[𝓝 p] fun _ => 0)) (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : P × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      mixedVectorCascade n mode m (fun l => v l q.1)
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (p, x, y) := by
  induction j generalizing x y with
  | zero =>
    have hmap : DifferentiableAt ℝ (fun q : ParamFields P n => (U q.1, q.2)) (p, x, y) :=
      (hU.comp (p, x, y) differentiableAt_fst).prodMk differentiableAt_snd
    have ht : DifferentiableAt ℝ
        (fun q : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
          constrainedPairFieldBase n q.1 u q.2.1 q.2.2) (U p, x, y) :=
      ((contDiff_constrainedPairFieldBase_joint u).differentiable (by simp)).differentiableAt
    simpa only [Function.comp_def, mixedVectorCascade] using ht.comp (p, x, y) hmap
  | succ j ih =>
    let F : ParamFields P n → ℝ := fun q => mixedVectorCascade n mode m (fun l => v l q.1)
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
    have hvj (l : ℕ) (hl : l < j) := hv l (show l < j + 1 by omega)
    have hfj (l : ℕ) (hl : l < j) := hface l (show l < j + 1 by omega)
    have hFd (x y : Fin n → ℝ) : DifferentiableAt ℝ F (p, x, y) := ih hvj hfj x y
    have hFm : ∀ᶠ a in 𝓝 p,
        Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)) := by
      filter_upwards [hnonneg] with a ha
      exact (mixedConstrainedCascade_growth (U a) u mode m (fun l => v l a) hm ha j).measurable
    have hFg : CoupledGrowth (fun x y => F (p, x, y)) :=
      mixedConstrainedCascade_growth (U p) u mode m (fun l => v l p) hm hnonneg.self_of_nhds j
    have hFs (x y x' y' : Fin n → ℝ) : |F (p, x, y) - F (p, x', y')| ≤
        l1 (x - x') + l1 (y - y') :=
      mixedConstrainedCascade_fields_dist_le (U p) u mode m (fun l => v l p) hm
        hnonneg.self_of_nhds j x y x' y'
    obtain ⟨K, hK, hKbound⟩ := mixedConstrainedCascade_multi_anchored_bound U u mode m v hm j hU hvj hnonneg hfj
    have hb : DifferentiableAt ℝ (fun a => Real.sqrt (v j a)) p := by
      rcases hface j (by omega) with hp | hz
      · exact (Real.hasDerivAt_sqrt hp.ne').differentiableAt.comp p (hv j (by omega))
      · apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hz] with a ha
        simp [ha]
    have H {r : ℕ} (A B : Fin r → Fin n → ℝ) :=
      differentiableAt_multiGaussianStep F hb (m j) A B hFd hFm hFg hFs hK hKbound x y
    change DifferentiableAt ℝ (fun q : ParamFields P n =>
      mixedVectorStep n (mode j) (m j) (v j q.1) (fun x y => F (q.1, x, y)) q.2.1 q.2.2) (p, x, y)
    cases mode j with
    | independent =>
      have H' := H (independentLeftDirection n) (independentRightDirection n)
      simp only [multiGaussianStep_eq_linearStep, coupledLinearStep_independent] at H'
      apply H'.congr_of_eventuallyEq
      filter_upwards [(continuous_fst.tendsto (p, x, y)).eventually hnonneg] with q hq
      exact congrFun (congrFun
        (mixedVectorStep_independent_eq (m j) (v j q.1)
          (mixedConstrainedCascade_growth (U q.1) u mode m (fun l => v l q.1) hm hq j)) q.2.1) q.2.2
    | shared =>
      have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
      simpa only [multiGaussianStep_eq_linearStep, coupledLinearStep_shared, mixedVectorStep_shared_eq] using H'
    | opposite =>
      have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -Pi.single i 1)
      simpa only [multiGaussianStep_eq_linearStep, coupledLinearStep_opposite] using H'

end MultiParameter

noncomputable def mixedFaceCascade (u : ℝ) (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (j : ℕ) (x y : Fin n → ℝ) (p : EnergySpace n × (Fin j → ℝ)) : ℝ :=
  mixedVectorCascade n mode m (faceVariance j v p.2) (constrainedPairFieldBase n p.1 u) j x y

private theorem mixedFaceCascade_base (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (hv : ∀ l, 0 ≤ v l)
    (j : ℕ) (x y : Fin n → ℝ) :
    mixedFaceCascade u mode m v j x y (U, fun l => v l) =
      mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y := by
  dsimp only [mixedFaceCascade]
  rw [mixedVectorCascade_congr_variance mode m _ v j _ (faceVariance_base j v hv)]

/-- Actual differentiability in independent disorder and active-variance
coordinates. Inactive coordinates are fixed before differentiation. -/
theorem differentiableAt_mixedConstrainedCascade_activeFace
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (j : ℕ) (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (mixedFaceCascade u mode m v j x y) (U, fun l => v l) := by
  classical
  let p : EnergySpace n × (Fin j → ℝ) := (U, fun l => v l)
  have hdiff (l : ℕ) : DifferentiableAt ℝ
      (fun q : EnergySpace n × (Fin j → ℝ) => faceVariance j v q.2 l) p := by
    by_cases hl : l < j
    · by_cases hp : 0 < v l
      · simp only [faceVariance, dif_pos hl, if_pos hp]
        have hc : DifferentiableAt ℝ (fun c : Fin j → ℝ => c ⟨l, hl⟩) p.2 := by fun_prop
        exact hc.comp p differentiableAt_snd
      · simp only [faceVariance, dif_pos hl, if_neg hp]
        exact differentiableAt_const 0
    · simp only [faceVariance, dif_neg hl]
      exact differentiableAt_const 0
  have hpos (l : Fin j) : ∀ᶠ q : EnergySpace n × (Fin j → ℝ) in 𝓝 p,
      0 < v l → 0 ≤ q.2 l := by
    by_cases hp : 0 < v l
    · filter_upwards [((continuous_apply l).comp continuous_snd).continuousAt.eventually
        (lt_mem_nhds hp)] with q hq
      exact fun _ => hq.le
    · exact Filter.Eventually.of_forall fun _ h => (hp h).elim
  have hn : ∀ᶠ q : EnergySpace n × (Fin j → ℝ) in 𝓝 p,
      ∀ l, 0 ≤ faceVariance j v q.2 l := by
    filter_upwards [Filter.eventually_all.mpr hpos] with q hq
    intro l
    by_cases hl : l < j
    · simp only [faceVariance, dif_pos hl]
      split_ifs with hp
      · exact hq ⟨l, hl⟩ hp
      · exact le_rfl
    · simp [faceVariance, hl]
  have hf (l : ℕ) (hl : l < j) :
      0 < faceVariance j v p.2 l ∨
        (fun q : EnergySpace n × (Fin j → ℝ) => faceVariance j v q.2 l) =ᶠ[𝓝 p] fun _ => 0 := by
    by_cases hp : 0 < v l
    · exact Or.inl (by simpa only [p, faceVariance_base j v hv l hl] using hp)
    · exact Or.inr (Filter.Eventually.of_forall fun q => by simp [faceVariance, hl, hp])
  have H := differentiableAt_mixedConstrainedCascade_multi
    (fun q : EnergySpace n × (Fin j → ℝ) => q.1) u mode m
    (fun l q => faceVariance j v q.2 l) hm j differentiableAt_fst (fun l _ => hdiff l) hn hf x y
  have hc : DifferentiableAt ℝ
      (fun a : EnergySpace n × (Fin j → ℝ) => (a, x, y)) p := by fun_prop
  simpa only [Function.comp_def, mixedFaceCascade, p] using! H.comp p hc

private theorem mixedFaceCascade_disorder_fderiv
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (j : ℕ) (x y : Fin n → ℝ) :
    fderiv ℝ (mixedFaceCascade u mode m v j x y) (U, fun l => v l) (V, 0) =
      mixedConstrainedDirection mode m v j U V u x y := by
  have H := (differentiableAt_mixedConstrainedCascade_activeFace U u mode m v hm hv j x y).hasFDerivAt
  have hc : HasDerivAt
      (fun a : ℝ => (U + a • V, fun l : Fin j => v l)) (V, 0) 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) U).add ((hasDerivAt_id (0 : ℝ)).smul_const V)).prodMk
      (hasDerivAt_const (0 : ℝ) (fun l : Fin j => v l))
  have H' : HasFDerivAt (mixedFaceCascade u mode m v j x y)
      (fderiv ℝ (mixedFaceCascade u mode m v j x y) (U, fun l => v l))
      (U + (0 : ℝ) • V, fun l => v l) := by simpa using H
  have HH := H'.comp_hasDerivAt 0 hc
  simp only [Function.comp_def, mixedFaceCascade_base _ u mode m v hv j x y] at HH
  have HD := hasDerivAt_mixedConstrainedCascade U V u mode m v hm hv j x y 0
  simp only [zero_smul, add_zero] at HD
  exact HH.unique HD

private theorem mixedFaceCascade_variance_fderiv
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (j : ℕ) (x y : Fin n → ℝ) (l : Fin j) :
    fderiv ℝ (mixedFaceCascade u mode m v j x y) (U, fun i => v i) (0, Pi.single l 1) =
      if 0 < v l then mixedLevelVarianceD U u mode m v l (j - (l + 1)) (v l) x y else 0 := by
  classical
  have H := (differentiableAt_mixedConstrainedCascade_activeFace U u mode m v hm hv j x y).hasFDerivAt
  have hc := (hasDerivAt_const (v l) U).prodMk (hasDerivAt_update (fun i : Fin j => v i) l (v l))
  have H' : HasFDerivAt (mixedFaceCascade u mode m v j x y)
      (fderiv ℝ (mixedFaceCascade u mode m v j x y) (U, fun i => v i))
      (U, Function.update (fun i : Fin j => v i) l (v l)) := by simpa using H
  have HH := H'.comp_hasDerivAt (v l) hc
  by_cases hp : 0 < v l
  · rw [if_pos hp]
    have he (a : ℝ) : mixedFaceCascade u mode m v j x y
        (U, Function.update (fun i : Fin j => v i) l a) =
        mixedVectorCascade n mode m (Function.update v (l : ℕ) a)
          (constrainedPairFieldBase n U u) j x y := by
      dsimp only [mixedFaceCascade]
      rw [mixedVectorCascade_congr_variance mode m _ (Function.update v (l : ℕ) a) j _
        (fun k hk => by simpa only [if_pos hp] using faceVariance_update j v hv l a k hk)]
    simp only [Function.comp_def, he] at HH
    have HD := hasDerivAt_mixedConstrainedCascade_variance U u mode m v hm hv l (j - (l + 1)) x y hp
    have hd : l + 1 + (j - (l + 1)) = j := by omega
    rw [hd] at HD
    exact HH.unique HD
  · rw [if_neg hp]
    have he (a : ℝ) : mixedFaceCascade u mode m v j x y
        (U, Function.update (fun i : Fin j => v i) l a) =
        mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j x y := by
      dsimp only [mixedFaceCascade]
      rw [mixedVectorCascade_congr_variance mode m _ v j _
        (fun k hk => by simpa only [if_neg hp] using faceVariance_update j v hv l a k hk)]
    simp only [Function.comp_def, he] at HH
    exact HH.unique (hasDerivAt_const (v l) _)

private theorem mixedFaceCascade_fderiv_decomposition
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (j : ℕ) (x y : Fin n → ℝ) (c : Fin j → ℝ) :
    fderiv ℝ (mixedFaceCascade u mode m v j x y) (U, fun i => v i) (V, c) =
      mixedConstrainedDirection mode m v j U V u x y +
        ∑ l : Fin j, c l *
          (if 0 < v l then mixedLevelVarianceD U u mode m v l (j - (l + 1)) (v l) x y else 0) := by
  classical
  have he : (V, c) = (V, 0) + ∑ l : Fin j, c l • ((0 : EnergySpace n), Pi.single l 1) := by
    simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero,
      Prod.mk_add_mk, add_zero, zero_add]
    exact congrArg (fun a => (V, a)) (pi_eq_sum_univ' c)
  rw [he, map_add, map_sum, mixedFaceCascade_disorder_fderiv U V u mode m v hm hv j x y]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, mixedFaceCascade_variance_fderiv U u mode m v hm hv j x y l, smul_eq_mul]

/-- The genuine mixed simultaneous derivative equals its actual disorder
direction plus the active original-level heat contributions. Inactive zero
coordinates contribute zero and require no boundary variance derivative. -/
theorem hasDerivAt_mixedConstrainedCascade_path_decomposition
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {w : ℝ} {U' : EnergySpace n} {v' : ℕ → ℝ}
    (hU : HasDerivAt U U' w) (hv : ∀ l < j, HasDerivAt (v l) (v' l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) (x y : Fin n → ℝ) :
    HasDerivAt (fun a => mixedVectorCascade n mode m (fun l => v l a)
      (constrainedPairFieldBase n (U a) u) j x y)
      (mixedConstrainedDirection mode m (fun l => v l w) j (U w) U' u x y +
        ∑ l : Fin j, v' l *
          (if 0 < v l w then mixedLevelVarianceD (U w) u mode m (fun i => v i w)
            l (j - (l + 1)) (v l w) x y else 0)) w := by
  classical
  have hbase : ∀ l, 0 ≤ v l w := hnonneg.self_of_nhds
  let p (a : ℝ) : EnergySpace n × (Fin j → ℝ) := (U a, fun l => v l a)
  have hp : HasDerivAt p (U', fun l => v' l) w := hU.prodMk (hasDerivAt_pi.mpr fun l => hv l l.isLt)
  have H := (differentiableAt_mixedConstrainedCascade_activeFace (U w) u mode m
    (fun l => v l w) hm hbase j x y).hasFDerivAt.comp_hasDerivAt w hp
  rw [mixedFaceCascade_fderiv_decomposition (U w) U' u mode m (fun l => v l w) hm hbase j x y] at H
  have he (l : Fin j) : ∀ᶠ a in 𝓝 w,
      faceVariance j (fun i => v i w) (fun i => v i a) l = v l a := by
    rcases hface l l.isLt with hl | hz
    · exact Filter.Eventually.of_forall fun a => by simp [faceVariance, l.isLt, hl]
    · have hn : ¬ 0 < v l w := by rw [hz.self_of_nhds]; exact lt_irrefl 0
      filter_upwards [hz] with a ha
      simp [faceVariance, l.isLt, hn, ha]
  apply H.congr_of_eventuallyEq
  filter_upwards [Filter.eventually_all.mpr he] with a ha
  dsimp only [Function.comp_def, p, mixedFaceCascade]
  exact congrFun (congrFun (mixedVectorCascade_congr_variance mode m _ _ j
    (constrainedPairFieldBase n (U a) u) (fun l hl => (ha ⟨l, hl⟩).symm)) x) y

/-- Identification of the already proved joint time component with the
explicit disorder-plus-heat formula used in Gaussian path averaging. -/
theorem mixedConstrainedCascade_path_fderiv_eq_decomposition
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l) (j : ℕ) {w : ℝ} {U' : EnergySpace n} {v' : ℕ → ℝ}
    (hU : HasDerivAt U U' w) (hv : ∀ l < j, HasDerivAt (v l) (v' l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0)) (x y : Fin n → ℝ) :
    (fderiv ℝ (fun q : CoupledJointField n => mixedVectorCascade n mode m (fun l => v l q.1)
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y)) (1, 0, 0) =
      mixedConstrainedDirection mode m (fun l => v l w) j (U w) U' u x y +
        ∑ l : Fin j, v' l *
          (if 0 < v l w then mixedLevelVarianceD (U w) u mode m (fun i => v i w)
            l (j - (l + 1)) (v l w) x y else 0) :=
  (hasDerivAt_mixedConstrainedCascade_path_fderiv U u mode m v hm j hU.differentiableAt
    (fun l hl => (hv l hl).differentiableAt) hnonneg hface x y).unique
      (hasDerivAt_mixedConstrainedCascade_path_decomposition U u mode m v hm j hU hv hnonneg hface x y)

end SpinGlass.Targets
