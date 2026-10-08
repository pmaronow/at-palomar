module

public import Targets.CoupledJointInterpolation

@[expose] public section

/-!
# Decomposing the actual simultaneous interpolation derivative

Independent finite parameters are justified by direct dominated Fréchet
differentiation, reusing the already checked Gaussian log-Laplace rule and
actual cascade comparison bounds. Inactive zero-variance coordinates stay
fixed. No independence-of-parameters differentiability is assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

section MultiParameter

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P]

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
/-- The actual cascade has a field-uniform anchored bound for finite-dimensional
parameter changes. Fixed zero faces do not require variance differentiation. -/
theorem constrainedFieldCascade_multi_anchored_bound
    (U : P → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {p : P}
    (hU : DifferentiableAt ℝ U p)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) p)
    (hnonneg : ∀ᶠ a in 𝓝 p, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l p ∨ (v l =ᶠ[𝓝 p] fun _ => 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ a in 𝓝 p, ∀ x y : Fin n → ℝ,
      |coupledFieldCascade n m (fun l => v l a) d (constrainedPairFieldBase n (U a) u) j x y -
        coupledFieldCascade n m (fun l => v l p) d (constrainedPairFieldBase n (U p) u) j x y| ≤
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
  let K := 2 * Fintype.card (Config n) * CU +
    ∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l
  refine ⟨K, add_nonneg (by positivity) (Finset.sum_nonneg fun l _ =>
    mul_nonneg (constrainedLevelHeatBound_nonneg n m d l) (hCv l).le), ?_⟩
  filter_upwards [hbU.bound, Filter.eventually_all.mpr hbv,
    Filter.eventually_all.mpr hf, hnonneg] with a haU hav haf han
  intro x y
  have H := constrainedFieldCascade_joint_dist_le (U p) (U a) u m
    (fun l => v l p) (fun l => v l a) hm hnonneg.self_of_nhds han d j
    (fun l hl => haf ⟨l, hl⟩) x y x y
  simp only [sub_self, l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] at H
  rw [← Fin.sum_univ_eq_sum_range] at H
  have hsum : (∑ l : Fin j, constrainedLevelHeatBound n m d l * |v l a - v l p|) ≤
      (∑ l : Fin j, constrainedLevelHeatBound n m d l * Cv l) * ‖a - p‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hav l)
        (constrainedLevelHeatBound_nonneg n m d l)
  change ‖U a - U p‖ ≤ CU * ‖a - p‖ at haU
  dsimp [K]
  nlinarith [mul_le_mul_of_nonneg_left haU
    (show 0 ≤ 2 * (Fintype.card (Config n) : ℝ) by positivity)]

abbrev ParamFields (P : Type*) (n : ℕ) := P × ((Fin n → ℝ) × (Fin n → ℝ))

noncomputable def paramShift {r : ℕ} (b : P → ℝ)
    (A B : Fin r → Fin n → ℝ) (q : ParamFields P n) (z : Fin r → ℝ) : ParamFields P n :=
  q + b q.1 • (0, pairedFieldLinear A z, pairedFieldLinear B z)

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
private theorem paramShift_eq {r : ℕ} (b : P → ℝ)
    (A B : Fin r → Fin n → ℝ) (q : ParamFields P n) (z : Fin r → ℝ) :
    paramShift b A B q z =
      (q.1, q.2.1 + b q.1 • pairedFieldLinear A z, q.2.2 + b q.1 • pairedFieldLinear B z) := by
  ext <;> simp [paramShift]

private noncomputable def paramShiftD {r : ℕ} (b' : P →L[ℝ] ℝ)
    (A B : Fin r → Fin n → ℝ) (z : Fin r → ℝ) :
    ParamFields P n →L[ℝ] ParamFields P n :=
  ContinuousLinearMap.id ℝ _ +
    (b'.comp (ContinuousLinearMap.fst ℝ P ((Fin n → ℝ) × (Fin n → ℝ)))).smulRight
      (0, pairedFieldLinear A z, pairedFieldLinear B z)

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
private theorem hasFDerivAt_paramShift {r : ℕ} {b : P → ℝ} {b' : P →L[ℝ] ℝ} {p : P}
    (hb : HasFDerivAt b b' p) (A B : Fin r → Fin n → ℝ)
    (x y : Fin n → ℝ) (z : Fin r → ℝ) :
    HasFDerivAt (fun q => paramShift b A B q z) (paramShiftD b' A B z) (p, x, y) :=
  (hasFDerivAt_id (𝕜 := ℝ) (p, x, y)).add
    ((hb.comp (p, x, y) (ContinuousLinearMap.fst ℝ P
      ((Fin n → ℝ) × (Fin n → ℝ))).hasFDerivAt).smul_const
        (0, pairedFieldLinear A z, pairedFieldLinear B z))

private theorem measurable_paramShiftD {r : ℕ} (b' : P →L[ℝ] ℝ)
    (A B : Fin r → Fin n → ℝ) : Measurable (paramShiftD b' A B) :=
  measurable_const.add (((ContinuousLinearMap.smulRightL ℝ (ParamFields P n) (ParamFields P n)
    (b'.comp (ContinuousLinearMap.fst ℝ P ((Fin n → ℝ) × (Fin n → ℝ))))).continuous.measurable).comp
      (measurable_const.prodMk ((measurable_pairedFieldLinear A).prodMk (measurable_pairedFieldLinear B))))

private theorem l1_norm_bound (x : Fin n → ℝ) : l1 x ≤ n * ‖x‖ := by
  simpa only [l1, Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm x

private theorem l1_smul_bound (c : ℝ) (x : Fin n → ℝ) : l1 (c • x) = |c| * l1 x :=
  l1_const_smul c x

theorem differentiableAt_multiGaussianStep {r : ℕ}
    (F : ParamFields P n → ℝ) {b : P → ℝ} {p : P} (hb : DifferentiableAt ℝ b p)
    (mass : ℝ) (A B : Fin r → Fin n → ℝ)
    (hFdiff : ∀ x y, DifferentiableAt ℝ F (p, x, y))
    (hFmeas : ∀ᶠ a in 𝓝 p, Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)))
    (hFgrowth : CoupledGrowth (fun x y => F (p, x, y)))
    (hspace : ∀ x y x' y', |F (p, x, y) - F (p, x', y')| ≤ l1 (x - x') + l1 (y - y'))
    {K : ℝ} (hK : 0 ≤ K)
    (hparam : ∀ᶠ a in 𝓝 p, ∀ x y, |F (a, x, y) - F (p, x, y)| ≤ K * ‖a - p‖)
    (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q => parisiStepPi r mass 1
      (fun z => F (paramShift b A B q z)) 0) (p, x, y) := by
  classical
  let q : ParamFields P n := (p, x, y)
  obtain ⟨Cb, hCb, hbb⟩ := hb.isBigO_sub.exists_pos
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hzbound (z : Fin r → ℝ) : l1 (pairedFieldLinear A z) + l1 (pairedFieldLinear B z) ≤ L * l1 z := by
    dsimp [L]
    rw [Finset.sum_add_distrib]
    nlinarith [l1_pairedFieldLinear_le A z, l1_pairedFieldLinear_le B z]
  let s := {q' : ParamFields P n |
      Measurable (fun a : (Fin n → ℝ) × (Fin n → ℝ) => F (q'.1, a)) ∧
      (∀ x y, |F (q'.1, x, y) - F (p, x, y)| ≤ K * ‖q'.1 - p‖) ∧
      |b q'.1 - b p| ≤ Cb * ‖q'.1 - p‖ ∧ ‖q' - q‖ < 1}
  have hs : s ∈ 𝓝 q := by
    have ht := (continuous_fst.tendsto q).eventually (hFmeas.and (hparam.and hbb.bound))
    filter_upwards [ht, Metric.ball_mem_nhds q zero_lt_one] with q' hq' hball
    exact ⟨hq'.1, hq'.2.1, by simpa only [Real.norm_eq_abs] using hq'.2.2,
      by simpa only [Metric.mem_ball, dist_eq_norm] using hball⟩
  have hdist (q' : ParamFields P n) (hq' : q' ∈ s) (z : Fin r → ℝ) :
      |F (paramShift b A B q' z) - F (paramShift b A B q z)| ≤
        (K + 2 * n + Cb * L * l1 z) * ‖q' - q‖ := by
    have ht : ‖q'.1 - p‖ ≤ ‖q' - q‖ := norm_fst_le (q' - q)
    have hx : l1 (q'.2.1 - x) ≤ n * ‖q' - q‖ := (l1_norm_bound _).trans
      (mul_le_mul_of_nonneg_left ((norm_fst_le (q' - q).2).trans (norm_snd_le (q' - q))) (by positivity))
    have hy : l1 (q'.2.2 - y) ≤ n * ‖q' - q‖ := (l1_norm_bound _).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le (q' - q).2).trans (norm_snd_le (q' - q))) (by positivity))
    have hcoef : |b q'.1 - b p| ≤ Cb * ‖q' - q‖ := hq'.2.2.1.trans
      (mul_le_mul_of_nonneg_left ht hCb.le)
    have hxp := l1_add_le (q'.2.1 - x) ((b q'.1 - b p) • pairedFieldLinear A z)
    have hyp := l1_add_le (q'.2.2 - y) ((b q'.1 - b p) • pairedFieldLinear B z)
    rw [l1_smul_bound] at hxp hyp
    have hsp := hspace (q'.2.1 + b q'.1 • pairedFieldLinear A z)
      (q'.2.2 + b q'.1 • pairedFieldLinear B z)
      (x + b p • pairedFieldLinear A z) (y + b p • pairedFieldLinear B z)
    have hex (a a' Z : Fin n → ℝ) : a' + b q'.1 • Z - (a + b p • Z) =
        (a' - a) + (b q'.1 - b p) • Z := by module
    rw [hex, hex] at hsp
    have htri := abs_sub_le
      (F (q'.1, q'.2.1 + b q'.1 • pairedFieldLinear A z, q'.2.2 + b q'.1 • pairedFieldLinear B z))
      (F (p, q'.2.1 + b q'.1 • pairedFieldLinear A z, q'.2.2 + b q'.1 • pairedFieldLinear B z))
      (F (p, x + b p • pairedFieldLinear A z, y + b p • pairedFieldLinear B z))
    have hp := hq'.2.1 (q'.2.1 + b q'.1 • pairedFieldLinear A z)
      (q'.2.2 + b q'.1 • pairedFieldLinear B z)
    have hprod := mul_le_mul hcoef (hzbound z)
      (add_nonneg (l1_nonneg _) (l1_nonneg _)) (mul_nonneg hCb.le (norm_nonneg _))
    rw [paramShift_eq, paramShift_eq]
    dsimp only [q] at *
    nlinarith [mul_le_mul_of_nonneg_left ht hK]
  let G (q' : ParamFields P n) (z : Fin r → ℝ) := F (paramShift b A B q' z)
  let D (z : Fin r → ℝ) :=
    (fderiv ℝ F (paramShift b A B q z)).comp (paramShiftD (fderiv ℝ b p) A B z)
  have hD (z : Fin r → ℝ) : HasFDerivAt (fun q' => G q' z) (D z) q := by
    have H := (hFdiff (x + b p • pairedFieldLinear A z) (y + b p • pairedFieldLinear B z)).hasFDerivAt
    have H' : HasFDerivAt F (fderiv ℝ F (paramShift b A B q z)) (paramShift b A B q z) := by
      simpa only [paramShift_eq, q] using! H
    exact H'.comp q (hasFDerivAt_paramShift hb.hasFDerivAt A B x y z)
  have hmshift (q' : ParamFields P n) : Measurable (paramShift b A B q') := by
    change Measurable (fun z => q' + b q'.1 • (0, pairedFieldLinear A z, pairedFieldLinear B z))
    exact measurable_const.add ((measurable_const.prodMk
      ((measurable_pairedFieldLinear A).prodMk (measurable_pairedFieldLinear B))).const_smul (b q'.1))
  have hDm : Measurable D := by
    have hc : Continuous (fun Q : (ParamFields P n →L[ℝ] ℝ) ×
        (ParamFields P n →L[ℝ] ParamFields P n) => Q.1.comp Q.2) :=
      ((ContinuousLinearMap.compL ℝ (ParamFields P n) (ParamFields P n) ℝ).continuous.comp
        continuous_fst).clm_apply continuous_snd
    exact hc.measurable.comp (((measurable_fderiv ℝ F).comp (hmshift q)).prodMk
      (measurable_paramShiftD _ A B))
  obtain ⟨C, L0, hL0, hg⟩ := hFgrowth.bound
  have hg0 (z : Fin r → ℝ) : |G q z| ≤ C + L0 * (l1 x + l1 y) +
      (L0 * |b p| * L) * l1 z := by
    have hx := l1_add_le x (b p • pairedFieldLinear A z)
    have hy := l1_add_le y (b p • pairedFieldLinear B z)
    rw [l1_smul_bound] at hx hy
    have hprod := mul_le_mul_of_nonneg_left (hzbound z) (mul_nonneg hL0 (abs_nonneg (b p)))
    have H := hg (x + b p • pairedFieldLinear A z) (y + b p • pairedFieldLinear B z)
    simp only [G, paramShift_eq, q]
    nlinarith
  apply (hasFDerivAt_gaussianLogLaplace hs mass hD
    (fun q' hq' => ?_) hDm.aestronglyMeasurable
    (C := C + L0 * (l1 x + l1 y) + (K + 2 * n))
    (L := L0 * |b p| * L + Cb * L) (A := K + 2 * n) (B := Cb * L)
    (by positivity) (by positivity) (by positivity) (fun q' hq' z => ?_) hdist).differentiableAt
  · simp only [G, paramShift_eq]
    exact hq'.1.comp ((measurable_const.add ((measurable_pairedFieldLinear A).const_smul (b q'.1))).prodMk
      (measurable_const.add ((measurable_pairedFieldLinear B).const_smul (b q'.1))))
  · have H := abs_sub_le (G q' z) (G q z) 0
    simp only [sub_zero] at H
    have hd := hdist q' hq' z
    have hprod := mul_le_mul_of_nonneg_left hq'.2.2.2.le
      (show 0 ≤ K + 2 * (n : ℝ) + Cb * L * l1 z by positivity)
    nlinarith [hg0 z]

omit [FiniteDimensional ℝ P] [MeasurableSpace P] [BorelSpace P] in
theorem multiGaussianStep_eq_linearStep {r : ℕ}
    (F : ParamFields P n → ℝ) (mass : ℝ) (v : P → ℝ)
    (A B : Fin r → Fin n → ℝ) (q : ParamFields P n) :
    parisiStepPi r mass 1 (fun z => F (paramShift (fun a => Real.sqrt (v a)) A B q z)) 0 =
      coupledLinearStep mass (v q.1) A B (fun x y => F (q.1, x, y)) q.2.1 q.2.2 := by
  simp only [coupledLinearStep, parisiStepPi, Real.sqrt_one, Pi.zero_apply, zero_add,
    one_mul, paramShift_eq, pairedFieldLinear_const_mul]

set_option maxHeartbeats 1200000 in
/-- Genuine finite-dimensional parameter differentiability of the actual
constrained cascade, including locally fixed zero-variance faces. -/
theorem differentiableAt_constrainedFieldCascade_multi
    (U : P → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ) {p : P}
    (hU : DifferentiableAt ℝ U p)
    (hv : ∀ l < j, DifferentiableAt ℝ (v l) p)
    (hnonneg : ∀ᶠ a in 𝓝 p, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l p ∨ (v l =ᶠ[𝓝 p] fun _ => 0))
    (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (fun q : P × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      coupledFieldCascade n m (fun l => v l q.1) d
        (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (p, x, y) := by
  induction j generalizing x y with
  | zero =>
    have hmap : DifferentiableAt ℝ (fun q : ParamFields P n => (U q.1, q.2)) (p, x, y) :=
      (hU.comp (p, x, y) differentiableAt_fst).prodMk differentiableAt_snd
    have ht : DifferentiableAt ℝ
        (fun q : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
          constrainedPairFieldBase n q.1 u q.2.1 q.2.2) (U p, x, y) :=
      ((contDiff_constrainedPairFieldBase_joint u).differentiable (by simp)).differentiableAt
    simpa only [Function.comp_def, coupledFieldCascade] using ht.comp (p, x, y) hmap
  | succ j ih =>
    let F : ParamFields P n → ℝ := fun q => coupledFieldCascade n m (fun l => v l q.1) d
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2
    have hvj (l : ℕ) (hl : l < j) := hv l (show l < j + 1 by omega)
    have hfj (l : ℕ) (hl : l < j) := hface l (show l < j + 1 by omega)
    have hFd (x y : Fin n → ℝ) : DifferentiableAt ℝ F (p, x, y) := ih hvj hfj x y
    have hFm : ∀ᶠ a in 𝓝 p,
        Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => F (a, q)) := by
      filter_upwards [hnonneg] with a ha
      exact (constrainedPairFieldCascade_growth (U a) u m (fun l => v l a) hm ha d j).measurable
    have hFg : CoupledGrowth (fun x y => F (p, x, y)) :=
      constrainedPairFieldCascade_growth (U p) u m (fun l => v l p) hm hnonneg.self_of_nhds d j
    have hFs (x y x' y' : Fin n → ℝ) : |F (p, x, y) - F (p, x', y')| ≤
        l1 (x - x') + l1 (y - y') :=
      constrainedFieldCascade_fields_dist_le (U p) u m (fun l => v l p) hm
        hnonneg.self_of_nhds d j x y x' y'
    obtain ⟨K, hK, hKbound⟩ := constrainedFieldCascade_multi_anchored_bound U u m v hm d j hU hvj hnonneg hfj
    have hb : DifferentiableAt ℝ (fun a => Real.sqrt (v j a)) p := by
      rcases hface j (by omega) with hp | hz
      · exact (Real.hasDerivAt_sqrt hp.ne').differentiableAt.comp p (hv j (by omega))
      · apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hz] with a ha
        simp [ha]
    have H {r : ℕ} (A B : Fin r → Fin n → ℝ) :=
      differentiableAt_multiGaussianStep F hb (m j) A B hFd hFm hFg hFs hK hKbound x y
    by_cases hj : j < d
    · have H' := H (independentLeftDirection n) (independentRightDirection n)
      simp only [multiGaussianStep_eq_linearStep, coupledLinearStep_independent] at H'
      simpa only [coupledFieldCascade, if_pos hj] using H'
    · have H' := H (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
      simp only [multiGaussianStep_eq_linearStep, coupledLinearStep_shared] at H'
      simpa only [coupledFieldCascade, if_neg hj] using H'

end MultiParameter

/-! Independent coordinates on the active variance face. -/

noncomputable def faceVariance (j : ℕ) (v : ℕ → ℝ)
    (c : Fin j → ℝ) (l : ℕ) : ℝ :=
  if hl : l < j then if 0 < v l then c ⟨l, hl⟩ else 0 else 0

theorem faceVariance_base (j : ℕ) (v : ℕ → ℝ) (hv : ∀ l, 0 ≤ v l)
    (l : ℕ) (hl : l < j) : faceVariance j v (fun i => v i) l = v l := by
  simp only [faceVariance, dif_pos hl]
  split_ifs with hp
  · rfl
  · exact (le_antisymm (le_of_not_gt hp) (hv l)).symm

noncomputable def faceCascade (u : ℝ) (m v : ℕ → ℝ) (d j : ℕ)
    (x y : Fin n → ℝ) (p : EnergySpace n × (Fin j → ℝ)) : ℝ :=
  coupledFieldCascade n m (faceVariance j v p.2) d
    (constrainedPairFieldBase n p.1 u) j x y

private theorem faceCascade_base (U : EnergySpace n) (u : ℝ) (m v : ℕ → ℝ)
    (hv : ∀ l, 0 ≤ v l) (d j : ℕ) (x y : Fin n → ℝ) :
    faceCascade u m v d j x y (U, fun l => v l) =
      coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y := by
  dsimp only [faceCascade]
  rw [coupledFieldCascade_congr_variance m _ v d j _ (faceVariance_base j v hv)]

/-- Independent disorder/active-variance differentiability is proved, not
assumed. Zero coordinates are masked to constants before taking a derivative. -/
theorem differentiableAt_constrainedFieldCascade_activeFace
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    DifferentiableAt ℝ (faceCascade u m v d j x y) (U, fun l => v l) := by
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
  have H := differentiableAt_constrainedFieldCascade_multi
    (fun q : EnergySpace n × (Fin j → ℝ) => q.1) u m
    (fun l q => faceVariance j v q.2 l) hm d j differentiableAt_fst
    (fun l _ => hdiff l) hn hf x y
  have hc : DifferentiableAt ℝ
      (fun a : EnergySpace n × (Fin j → ℝ) => (a, x, y)) p := by fun_prop
  simpa only [Function.comp_def, faceCascade, p] using! H.comp p hc

private theorem faceCascade_disorder_fderiv
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    fderiv ℝ (faceCascade u m v d j x y) (U, fun l => v l) (V, 0) =
      constrainedPairFieldCascadeDirection m v d j U V u x y := by
  have H := (differentiableAt_constrainedFieldCascade_activeFace U u m v hm hv d j x y).hasFDerivAt
  have hc : HasDerivAt
      (fun a : ℝ => (U + a • V, fun l : Fin j => v l)) (V, 0) 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) U).add ((hasDerivAt_id (0 : ℝ)).smul_const V)).prodMk
      (hasDerivAt_const (0 : ℝ) (fun l : Fin j => v l))
  have H' : HasFDerivAt (faceCascade u m v d j x y)
      (fderiv ℝ (faceCascade u m v d j x y) (U, fun l => v l))
      (U + (0 : ℝ) • V, fun l => v l) := by simpa using H
  have HH := H'.comp_hasDerivAt 0 hc
  simp only [Function.comp_def, faceCascade_base _ u m v hv d j x y] at HH
  have HD := hasDerivAt_constrainedPairFieldCascade U V u m v hm hv d j x y 0
  simp only [zero_smul, add_zero] at HD
  exact HH.unique HD

theorem faceVariance_update (j : ℕ) (v : ℕ → ℝ) (hv : ∀ l, 0 ≤ v l)
    (l : Fin j) (a : ℝ) (k : ℕ) (hk : k < j) :
    faceVariance j v (Function.update (fun i : Fin j => v i) l a) k =
      if 0 < v l then Function.update v (l : ℕ) a k else v k := by
  classical
  by_cases hkl : k = l
  · subst k
    simp only [faceVariance, dif_pos l.isLt, Function.update_self]
    split_ifs with hp
    · rfl
    · exact (le_antisymm (le_of_not_gt hp) (hv l)).symm
  · have hfin : (⟨k, hk⟩ : Fin j) ≠ l := fun h => hkl (congrArg Fin.val h)
    simp only [faceVariance, dif_pos hk, Function.update_of_ne hfin,
      Function.update_of_ne hkl]
    split_ifs <;> first | rfl | exact (le_antisymm (by linarith) (hv k)).symm

private theorem faceCascade_variance_fderiv
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) (l : Fin j) :
    fderiv ℝ (faceCascade u m v d j x y) (U, fun i => v i) (0, Pi.single l 1) =
      if 0 < v l then constrainedLevelVarianceD U u m v d l (j - (l + 1)) (v l) x y else 0 := by
  classical
  have H := (differentiableAt_constrainedFieldCascade_activeFace U u m v hm hv d j x y).hasFDerivAt
  have hc := (hasDerivAt_const (v l) U).prodMk (hasDerivAt_update (fun i : Fin j => v i) l (v l))
  have H' : HasFDerivAt (faceCascade u m v d j x y)
      (fderiv ℝ (faceCascade u m v d j x y) (U, fun i => v i))
      (U, Function.update (fun i : Fin j => v i) l (v l)) := by simpa using H
  have HH := H'.comp_hasDerivAt (v l) hc
  by_cases hp : 0 < v l
  · rw [if_pos hp]
    have he (a : ℝ) : faceCascade u m v d j x y
        (U, Function.update (fun i : Fin j => v i) l a) =
        coupledFieldCascade n m (Function.update v (l : ℕ) a) d
          (constrainedPairFieldBase n U u) j x y := by
      dsimp only [faceCascade]
      rw [coupledFieldCascade_congr_variance m _ (Function.update v (l : ℕ) a) d j _
        (fun k hk => by simpa only [if_pos hp] using faceVariance_update j v hv l a k hk)]
    simp only [Function.comp_def, he] at HH
    have HD := hasDerivAt_constrainedFieldCascade_variance U u m v hm hv d l (j - (l + 1)) x y hp
    have hd : l + 1 + (j - (l + 1)) = j := by omega
    rw [hd] at HD
    exact HH.unique HD
  · rw [if_neg hp]
    have he (a : ℝ) : faceCascade u m v d j x y
        (U, Function.update (fun i : Fin j => v i) l a) =
        coupledFieldCascade n m v d (constrainedPairFieldBase n U u) j x y := by
      dsimp only [faceCascade]
      rw [coupledFieldCascade_congr_variance m _ v d j _
        (fun k hk => by simpa only [if_neg hp] using faceVariance_update j v hv l a k hk)]
    simp only [Function.comp_def, he] at HH
    exact HH.unique (hasDerivAt_const (v l) _)

private theorem faceCascade_fderiv_decomposition
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) (c : Fin j → ℝ) :
    fderiv ℝ (faceCascade u m v d j x y) (U, fun i => v i) (V, c) =
      constrainedPairFieldCascadeDirection m v d j U V u x y +
        ∑ l : Fin j, c l *
          (if 0 < v l then constrainedLevelVarianceD U u m v d l (j - (l + 1)) (v l) x y else 0) := by
  classical
  have he : (V, c) = (V, 0) + ∑ l : Fin j, c l • ((0 : EnergySpace n), Pi.single l 1) := by
    simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero,
      Prod.mk_add_mk, add_zero, zero_add]
    exact congrArg (fun a => (V, a)) (pi_eq_sum_univ' c)
  rw [he, map_add, map_sum, faceCascade_disorder_fderiv U V u m v hm hv d j x y]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, faceCascade_variance_fderiv U u m v hm hv d j x y l, smul_eq_mul]

/-- The genuine simultaneous path derivative is the actual disorder direction
plus the finite sum of the individual level heat derivatives. A zero visited
variance must be locally fixed; it contributes zero and no derivative at the
boundary of the variance domain is assumed. -/
theorem hasDerivAt_constrainedFieldCascade_path_decomposition
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ)
    {w : ℝ} {U' : EnergySpace n} {v' : ℕ → ℝ}
    (hU : HasDerivAt U U' w)
    (hv : ∀ l < j, HasDerivAt (v l) (v' l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasDerivAt (fun a => coupledFieldCascade n m (fun l => v l a) d
      (constrainedPairFieldBase n (U a) u) j x y)
      (constrainedPairFieldCascadeDirection m (fun l => v l w) d j (U w) U' u x y +
        ∑ l : Fin j, v' l *
          (if 0 < v l w then constrainedLevelVarianceD (U w) u m (fun i => v i w)
            d l (j - (l + 1)) (v l w) x y else 0)) w := by
  classical
  have hbase : ∀ l, 0 ≤ v l w := hnonneg.self_of_nhds
  let p (a : ℝ) : EnergySpace n × (Fin j → ℝ) := (U a, fun l => v l a)
  have hp : HasDerivAt p (U', fun l => v' l) w :=
    hU.prodMk (hasDerivAt_pi.mpr fun l => hv l l.isLt)
  have H := (differentiableAt_constrainedFieldCascade_activeFace (U w) u m
    (fun l => v l w) hm hbase d j x y).hasFDerivAt.comp_hasDerivAt w hp
  rw [faceCascade_fderiv_decomposition (U w) U' u m (fun l => v l w) hm hbase d j x y] at H
  have he (l : Fin j) : ∀ᶠ a in 𝓝 w,
      faceVariance j (fun i => v i w) (fun i => v i a) l = v l a := by
    rcases hface l l.isLt with hl | hz
    · exact Filter.Eventually.of_forall fun a => by simp [faceVariance, l.isLt, hl]
    · have hn : ¬ 0 < v l w := by rw [hz.self_of_nhds]; exact lt_irrefl 0
      filter_upwards [hz] with a ha
      simp [faceVariance, l.isLt, hn, ha]
  apply H.congr_of_eventuallyEq
  filter_upwards [Filter.eventually_all.mpr he] with a ha
  dsimp only [Function.comp_def, p, faceCascade]
  exact congrFun (congrFun (coupledFieldCascade_congr_variance m _ _ d j
    (constrainedPairFieldBase n (U a) u) (fun l hl => (ha ⟨l, hl⟩).symm)) x) y

/-- Identification of the time component used by Gaussian path averaging with
the explicit disorder-plus-variance decomposition. -/
theorem constrainedFieldCascade_path_fderiv_eq_decomposition
    (U : ℝ → EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (d j : ℕ)
    {w : ℝ} {U' : EnergySpace n} {v' : ℕ → ℝ}
    (hU : HasDerivAt U U' w)
    (hv : ∀ l < j, HasDerivAt (v l) (v' l) w)
    (hnonneg : ∀ᶠ a in 𝓝 w, ∀ l, 0 ≤ v l a)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    (fderiv ℝ (fun q : CoupledJointField n => coupledFieldCascade n m (fun l => v l q.1) d
      (constrainedPairFieldBase n (U q.1) u) j q.2.1 q.2.2) (w, x, y)) (1, 0, 0) =
      constrainedPairFieldCascadeDirection m (fun l => v l w) d j (U w) U' u x y +
        ∑ l : Fin j, v' l *
          (if 0 < v l w then constrainedLevelVarianceD (U w) u m (fun i => v i w)
            d l (j - (l + 1)) (v l w) x y else 0) :=
  (hasDerivAt_constrainedFieldCascade_path_fderiv U u m v hm d j hU.differentiableAt
    (fun l hl => (hv l hl).differentiableAt) hnonneg hface x y).unique
      (hasDerivAt_constrainedFieldCascade_path_decomposition U u m v hm d j hU hv hnonneg hface x y)

end SpinGlass.Targets
