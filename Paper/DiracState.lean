module

public import Paper.Hyperbolic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

@[expose] public section

/-!
# Pathwise state equation for a Dirac Parisi measure

For a continuous noise path `W`, subtracting the additive term `β W` from the
post-interface state reduces the equation to an ordinary differential equation.
The bounded globally Lipschitz tanh drift gives existence on the full finite
time interval and pathwise uniqueness, using Picard–Lindelöf.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Topology

namespace Paper

/-- The pathwise drift after the additive noise is subtracted. -/
def diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * Real.tanh (y + β * W t)

private theorem diracState_continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)

/-- The nonlinear drift is globally Lipschitz in the state, with constant `β²`. -/
theorem lipschitzWith_diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzWith ⟨β ^ 2, sq_nonneg β⟩ (diracNoiseDrift β W t) := by
  have hd (y : ℝ) : HasDerivAt (diracNoiseDrift β W t)
      (β ^ 2 * sech (y + β * W t) ^ 2) y :=
    ((hasDerivAt_tanh (y + β * W t)).comp_add_const y (β * W t)).const_mul (β ^ 2)
  apply lipschitzWith_of_nnnorm_deriv_le (fun y => (hd y).differentiableAt)
  intro y
  rw [(hd y).deriv]
  change ‖β ^ 2 * sech (y + β * W t) ^ 2‖ ≤ β ^ 2
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β),
    Real.norm_of_nonneg (sq_nonneg (sech (y + β * W t)))]
  exact mul_le_of_le_one_right (sq_nonneg β) (sech_sq_le_one _)

/-- The drift is bounded by `β²`, uniformly in the noise path and state. -/
theorem norm_diracNoiseDrift_le (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) :
    ‖diracNoiseDrift β W t y‖ ≤ β ^ 2 := by
  unfold diracNoiseDrift
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (sq_nonneg β) (Real.abs_tanh_lt_one _).le

/-- A continuous noise path gives a jointly continuous pathwise drift. -/
theorem continuous_diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (fun p : ℝ × ℝ => diracNoiseDrift β W p.1 p.2) :=
  (diracState_continuous_tanh.comp
    (continuous_snd.add ((hW.comp continuous_fst).const_mul β))).const_mul (β ^ 2)

/-- A pathwise solution of the drift ODE on the post-interface interval. -/
structure IsDiracNoiseSolution (β h q : ℝ) (W Y : ℝ → ℝ) : Prop where
  initial : Y q = h
  hasDerivWithinAt : ∀ t ∈ Icc q (1 : ℝ),
    HasDerivWithinAt Y (diracNoiseDrift β W t (Y t)) (Icc q (1 : ℝ)) t

namespace IsDiracNoiseSolution

variable {β h q : ℝ} {W Y Z : ℝ → ℝ}

/-- Every pathwise ODE solution is continuous on its interval. -/
theorem continuousOn (hY : IsDiracNoiseSolution β h q W Y) :
    ContinuousOn Y (Icc q (1 : ℝ)) :=
  HasDerivWithinAt.continuousOn hY.hasDerivWithinAt

/-- The drift ODE is the actual integral equation. -/
theorem integral_equation (hY : IsDiracNoiseSolution β h q W Y)
    (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    Y t = h + ∫ s in q..t, β ^ 2 * Real.tanh (Y s + β * W s) := by
  have hsub : uIcc q t ⊆ Icc q (1 : ℝ) := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hf : ContinuousOn (Function.uncurry (diracNoiseDrift β W))
      (uIcc q t ×ˢ (univ : Set ℝ)) :=
    (continuous_diracNoiseDrift β W hW).continuousOn
  have hd : ∀ s ∈ uIcc q t,
      HasDerivWithinAt Y (diracNoiseDrift β W s (Y s)) (uIcc q t) s :=
    fun s hs => (hY.hasDerivWithinAt s (hsub hs)).mono hsub
  have he := ODE.picard_eq_of_hasDerivAt hf hd (fun _ _ => mem_univ _)
  simpa only [ODE.picard_apply, hY.initial, diracNoiseDrift] using he.symm

/-- Pathwise uniqueness on the full post-interface interval. -/
theorem eqOn (hY : IsDiracNoiseSolution β h q W Y)
    (hZ : IsDiracNoiseSolution β h q W Z) : EqOn Y Z (Icc q (1 : ℝ)) := by
  refine ODE_solution_unique (fun t => lipschitzWith_diracNoiseDrift β W t)
    hY.continuousOn ?_ hZ.continuousOn ?_ ?_
  · intro t ht
    exact (hY.hasDerivWithinAt t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact (hZ.hasDerivWithinAt t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  · rw [hY.initial, hZ.initial]

end IsDiracNoiseSolution

/-- Boundedness of the tanh drift lets the Picard–Lindelöf existence interval
cover all of `[q,1]`, with no small-time restriction. -/
theorem exists_diracNoiseSolution (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    ∃ Y : ℝ → ℝ, IsDiracNoiseSolution β h q W Y := by
  let L : ℝ≥0 := ⟨β ^ 2, sq_nonneg β⟩
  let a : ℝ≥0 := ⟨β ^ 2 * (1 - q), mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq)⟩
  let t₀ : Icc q (1 : ℝ) := ⟨q, le_rfl, hq⟩
  have hf : IsPicardLindelof (diracNoiseDrift β W) t₀ h a 0 L L := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (lipschitzWith_diracNoiseDrift β W t).lipschitzOnWith
    · intro y _
      exact ((continuous_diracNoiseDrift β W hW).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · intro t _ y _
      exact norm_diracNoiseDrift_le β W t y
    · dsimp [L, a, t₀]
      simp only [sub_self, sub_zero, max_eq_left (sub_nonneg.mpr hq)]
      rfl
  obtain ⟨Y, hy0, hy⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Y, hy0, hy⟩

/-- The state part before and after the interface, reconstructed from the drift correction. -/
def diracStateFromCorrection (β h q : ℝ) (W Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ q then h + β * W t else Y t + β * W t

/-- The post-interface integral equation is the additive-noise state equation. -/
theorem IsDiracNoiseSolution.state_integral_equation
    {β h q : ℝ} {W Y : ℝ → ℝ} (hY : IsDiracNoiseSolution β h q W Y)
    (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    diracStateFromCorrection β h q W Y t = h + β * W t +
      ∫ s in q..t, β ^ 2 * Real.tanh (diracStateFromCorrection β h q W Y s) := by
  have hstate (s : ℝ) (hs : s ∈ Icc q (1 : ℝ)) :
      diracStateFromCorrection β h q W Y s = Y s + β * W s := by
    unfold diracStateFromCorrection
    split_ifs with hs'
    · have he : s = q := le_antisymm hs' hs.1
      subst s
      rw [hY.initial]
    · rfl
  rw [hstate t ht, hY.integral_equation hW ht]
  have he : (∫ s in q..t, β ^ 2 * Real.tanh (Y s + β * W s)) =
      ∫ s in q..t, β ^ 2 * Real.tanh (diracStateFromCorrection β h q W Y s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hstate s]
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  rw [he]
  ring

/-- A selected pathwise solution exists for every continuous noise path. -/
def diracNoiseSolution (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) : ℝ → ℝ :=
  Classical.choose (exists_diracNoiseSolution β h q hq W hW)

theorem diracNoiseSolution_spec (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsDiracNoiseSolution β h q W (diracNoiseSolution β h q hq W hW) :=
  Classical.choose_spec (exists_diracNoiseSolution β h q hq W hW)

/-- Constant extension of the correction outside `[q,1]`; it is globally continuous. -/
def diracCorrection (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) : ℝ :=
  diracNoiseSolution β h q hq W hW (projIcc q 1 hq t)

theorem diracCorrection_eq (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    diracCorrection β h q hq W hW t = diracNoiseSolution β h q hq W hW t := by
  simp only [diracCorrection, projIcc_of_mem hq ht]

theorem continuous_diracCorrection (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (diracCorrection β h q hq W hW) :=
  (diracNoiseSolution_spec β h q hq W hW).continuousOn.domRestrict.comp continuous_projIcc

/-- The actual continuous additive-noise state path for the Dirac coefficient. -/
def diracState (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) : ℝ → ℝ :=
  diracStateFromCorrection β h q W (diracCorrection β h q hq W hW)

theorem continuous_diracState (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) : Continuous (diracState β h q hq W hW) := by
  unfold diracState diracStateFromCorrection
  apply Continuous.if_le (continuous_const.add (hW.const_mul β))
    ((continuous_diracCorrection β h q hq W hW).add (hW.const_mul β))
    continuous_id continuous_const
  intro t ht
  dsimp at ht
  subst t
  change h + β * W q = diracCorrection β h q hq W hW q + β * W q
  rw [diracCorrection_eq β h q hq W hW ⟨le_rfl, hq⟩,
    (diracNoiseSolution_spec β h q hq W hW).initial]

/-- The state starts at `h` for noise starting at zero and a nonnegative interface. -/
theorem diracState_initial (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) :
    diracState β h q hq.2 W hW 0 = h := by
  simp [diracState, diracStateFromCorrection, hq.1, hW0]

/-- Exact state equation before the interface. -/
theorem diracState_before (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ≤ q) :
    diracState β h q hq W hW t = h + β * W t := by
  simp [diracState, diracStateFromCorrection, ht]

/-- The selected correction still solves the original ODE on its interval. -/
theorem diracCorrection_spec (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsDiracNoiseSolution β h q W (diracCorrection β h q hq W hW) := by
  have hy := diracNoiseSolution_spec β h q hq W hW
  refine ⟨?_, ?_⟩
  · rw [diracCorrection_eq β h q hq W hW ⟨le_rfl, hq⟩, hy.initial]
  · intro t ht
    rw [diracCorrection_eq β h q hq W hW ht]
    exact (hy.hasDerivWithinAt t ht).congr_of_mem
      (fun s hs => diracCorrection_eq β h q hq W hW hs) ht

/-- Exact post-interface state integral equation with additive continuous noise. -/
theorem diracState_after (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    diracState β h q hq W hW t = h + β * W t +
      ∫ s in q..t, β ^ 2 * Real.tanh (diracState β h q hq W hW s) :=
  (diracCorrection_spec β h q hq W hW).state_integral_equation hW ht

/-- The tanh function is globally one-Lipschitz. -/
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh := by
  have hc : (⟨(1 : ℝ) ^ 2, sq_nonneg (1 : ℝ)⟩ : ℝ≥0) = 1 :=
    Subtype.ext (by norm_num)
  have hl := lipschitzWith_diracNoiseDrift 1 (fun _ => 0) 0
  rw [hc] at hl
  have he : diracNoiseDrift 1 (fun _ => 0) 0 = Real.tanh := by
    funext y
    simp [diracNoiseDrift]
  rwa [he] at hl

/-- The pathwise drift depends Lipschitz-continuously on the noise value. -/
theorem dist_diracNoiseDrift_noise_le (β : ℝ) (W V : ℝ → ℝ) (t y : ℝ) :
    dist (diracNoiseDrift β W t y) (diracNoiseDrift β V t y) ≤
      β ^ 2 * |β| * dist (W t) (V t) := by
  have ht := lipschitzWith_tanh.dist_le_mul (y + β * W t) (y + β * V t)
  norm_num only [NNReal.coe_one, one_mul] at ht
  rw [diracNoiseDrift, diracNoiseDrift, dist_eq_norm, ← mul_sub,
    norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  calc
    β ^ 2 * ‖Real.tanh (y + β * W t) - Real.tanh (y + β * V t)‖ ≤
        β ^ 2 * dist (y + β * W t) (y + β * V t) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg β)
    _ = β ^ 2 * |β| * dist (W t) (V t) := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Real.norm_eq_abs]
      rw [dist_eq_norm]
      ring

/-- Uniform perturbations of the noise give a quantitative Grönwall bound. -/
theorem IsDiracNoiseSolution.noise_dependence
    {β h q : ℝ} {W V Y Z : ℝ → ℝ}
    (hY : IsDiracNoiseSolution β h q W Y)
    (hZ : IsDiracNoiseSolution β h q V Z) {D : ℝ}
    (hD : ∀ t ∈ Icc q (1 : ℝ), dist (W t) (V t) ≤ D)
    {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    dist (Y t) (Z t) ≤ gronwallBound 0 (β ^ 2) (β ^ 2 * |β| * D) (t - q) := by
  have hy' : ∀ s ∈ Ico q (1 : ℝ),
      HasDerivWithinAt Y (diracNoiseDrift β W s (Y s)) (Ici s) s :=
    fun s hs => (hY.hasDerivWithinAt s (mem_Icc_of_Ico hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hz' : ∀ s ∈ Ico q (1 : ℝ),
      HasDerivWithinAt Z (diracNoiseDrift β V s (Z s)) (Ici s) s :=
    fun s hs => (hZ.hasDerivWithinAt s (mem_Icc_of_Ico hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hb : ∀ s ∈ Ico q (1 : ℝ),
      dist (diracNoiseDrift β V s (Z s)) (diracNoiseDrift β W s (Z s)) ≤
        β ^ 2 * |β| * D := by
    intro s hs
    rw [dist_comm]
    exact (dist_diracNoiseDrift_noise_le β W V s (Z s)).trans
      (mul_le_mul_of_nonneg_left (hD s (mem_Icc_of_Ico hs)) (by positivity))
  have hi : dist (Y q) (Z q) ≤ (0 : ℝ) := by rw [hY.initial, hZ.initial, dist_self]
  have hout := dist_le_of_approx_trajectories_ODE (εf := (0 : ℝ))
    (εg := β ^ 2 * |β| * D)
    (fun s => lipschitzWith_diracNoiseDrift β W s)
    hY.continuousOn hy' (fun _ _ => by simp) hZ.continuousOn hz' hb hi t ht
  change dist (Y t) (Z t) ≤
    gronwallBound 0 (β ^ 2) (0 + β ^ 2 * |β| * D) (t - q) at hout
  simpa only [zero_add] using hout

/-- Causality: solutions agree up to a time whenever the noise paths agree up to that time. -/
theorem IsDiracNoiseSolution.causal
    {β h q r : ℝ} {W V Y Z : ℝ → ℝ}
    (hY : IsDiracNoiseSolution β h q W Y)
    (hZ : IsDiracNoiseSolution β h q V Z) (hr : r ≤ 1)
    (hnoise : EqOn W V (Icc q r)) : EqOn Y Z (Icc q r) := by
  have hsub : Icc q r ⊆ Icc q (1 : ℝ) := Icc_subset_Icc_right hr
  refine ODE_solution_unique (fun t => lipschitzWith_diracNoiseDrift β W t)
    (hY.continuousOn.mono hsub) ?_ (hZ.continuousOn.mono hsub) ?_ ?_
  · intro t ht
    exact ((hY.hasDerivWithinAt t (hsub (mem_Icc_of_Ico ht))).mono hsub).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    have hd := ((hZ.hasDerivWithinAt t (hsub (mem_Icc_of_Ico ht))).mono hsub).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    simpa only [diracNoiseDrift, hnoise (mem_Icc_of_Ico ht)] using hd
  · rw [hY.initial, hZ.initial]

/-- Noise dependence constant on the full post-interface interval. -/
def diracCorrectionConstant (β q : ℝ) : ℝ :=
  gronwallBound 0 (β ^ 2) (β ^ 2 * |β|) (1 - q)

theorem diracCorrectionConstant_nonneg (β q : ℝ) (hq : q ≤ 1) :
    0 ≤ diracCorrectionConstant β q := by
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (show 0 ≤ 1 - q from sub_nonneg.mpr hq)
  simpa [diracCorrectionConstant, gronwallBound_x0] using hm

private theorem gronwallBound_scale_zero (K ε D x : ℝ) :
    gronwallBound 0 K (ε * D) x = gronwallBound 0 K ε x * D := by
  unfold gronwallBound
  split_ifs <;> simp only [zero_add, zero_mul, div_eq_mul_inv] <;> ring

/-- Extend a compact continuous noise path constantly beyond its endpoints. -/
def compactNoiseExtension (a b : ℝ) (hab : a ≤ b) (w : C(Icc a b, ℝ)) : ℝ → ℝ :=
  fun t => w (projIcc a b hab t)

theorem continuous_compactNoiseExtension (a b : ℝ) (hab : a ≤ b)
    (w : C(Icc a b, ℝ)) : Continuous (compactNoiseExtension a b hab w) :=
  w.continuous.comp continuous_projIcc

/-- The correction as a continuous map on the post-interface time interval. -/
def diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) (w : C(Icc q (1 : ℝ), ℝ)) :
    C(Icc q (1 : ℝ), ℝ) :=
  ⟨fun t => diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w) t,
    (continuous_diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
      (continuous_compactNoiseExtension q 1 hq w)).comp continuous_subtype_val⟩

/-- Picard–Lindelöf selection defines a globally Lipschitz map of the noise path. -/
theorem lipschitzWith_diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) :
    LipschitzWith ⟨diracCorrectionConstant β q, diracCorrectionConstant_nonneg β q hq⟩
      (diracCorrectionPath β h q hq) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  apply (ContinuousMap.dist_le (mul_nonneg (diracCorrectionConstant_nonneg β q hq)
    (dist_nonneg : 0 ≤ dist w v))).mpr
  intro t
  have hd : ∀ s ∈ Icc q (1 : ℝ),
      dist (compactNoiseExtension q 1 hq w s) (compactNoiseExtension q 1 hq v s) ≤
        dist w v := fun s _ => ContinuousMap.dist_apply_le_dist (projIcc q 1 hq s)
  have hb := (diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w)).noise_dependence
    (diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq v)
      (continuous_compactNoiseExtension q 1 hq v)) hd t.property
  rw [gronwallBound_scale_zero] at hb
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (sub_le_sub_right t.property.2 q)
  exact hb.trans (mul_le_mul_of_nonneg_right hm dist_nonneg)

/-- The correction is Borel measurable as a function of the entire compact noise path. -/
theorem measurable_diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) :
    Measurable (diracCorrectionPath β h q hq) :=
  (lipschitzWith_diracCorrectionPath β h q hq).continuous.measurable

/-- Uniform version of the perturbation estimate. -/
theorem IsDiracNoiseSolution.uniform_noise_dependence
    {β h q : ℝ} {W V Y Z : ℝ → ℝ}
    (hY : IsDiracNoiseSolution β h q W Y)
    (hZ : IsDiracNoiseSolution β h q V Z) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ t ∈ Icc q (1 : ℝ), dist (W t) (V t) ≤ D)
    {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    dist (Y t) (Z t) ≤ diracCorrectionConstant β q * D := by
  have hb := hY.noise_dependence hZ hD ht
  rw [gronwallBound_scale_zero] at hb
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (sub_le_sub_right ht.2 q)
  exact hb.trans (mul_le_mul_of_nonneg_right hm hD0)

/-- The entire continuous state path is a function of the continuous noise path. -/
def diracStatePath (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (w : C(Icc (0 : ℝ) 1, ℝ)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => diracState β h q hq.2 (compactNoiseExtension 0 1 zero_le_one w)
    (continuous_compactNoiseExtension 0 1 zero_le_one w) t,
    (continuous_diracState β h q hq.2 (compactNoiseExtension 0 1 zero_le_one w)
      (continuous_compactNoiseExtension 0 1 zero_le_one w)).comp continuous_subtype_val⟩

/-- The state map is globally Lipschitz for the uniform norm on continuous paths. -/
theorem lipschitzWith_diracStatePath (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    LipschitzWith ⟨|β| + diracCorrectionConstant β q,
      add_nonneg (abs_nonneg β) (diracCorrectionConstant_nonneg β q hq.2)⟩
      (diracStatePath β h q hq) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  apply (ContinuousMap.dist_le (mul_nonneg
    (add_nonneg (abs_nonneg β) (diracCorrectionConstant_nonneg β q hq.2)) dist_nonneg)).mpr
  intro t
  let W := compactNoiseExtension 0 1 zero_le_one w
  let V := compactNoiseExtension 0 1 zero_le_one v
  have hW : Continuous W := continuous_compactNoiseExtension 0 1 zero_le_one w
  have hV : Continuous V := continuous_compactNoiseExtension 0 1 zero_le_one v
  have hnoise (s : ℝ) : dist (W s) (V s) ≤ dist w v :=
    ContinuousMap.dist_apply_le_dist (projIcc 0 1 zero_le_one s)
  have hlinear : dist (β * W t) (β * V t) ≤ |β| * dist w v := by
    rw [dist_eq_norm, ← mul_sub, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hnoise t) (abs_nonneg β)
  change dist (diracState β h q hq.2 W hW t) (diracState β h q hq.2 V hV t) ≤
    (|β| + diracCorrectionConstant β q) * dist w v
  by_cases ht : (t : ℝ) ≤ q
  · rw [diracState_before β h q hq.2 W hW ht,
      diracState_before β h q hq.2 V hV ht, dist_add_left]
    exact hlinear.trans (by nlinarith [diracCorrectionConstant_nonneg β q hq.2,
      (dist_nonneg : 0 ≤ dist w v)])
  · have htq : (t : ℝ) ∈ Icc q (1 : ℝ) := ⟨(lt_of_not_ge ht).le, t.property.2⟩
    have hc := (diracCorrection_spec β h q hq.2 W hW).uniform_noise_dependence
      (diracCorrection_spec β h q hq.2 V hV) dist_nonneg (fun s _ => hnoise s) htq
    simp only [diracState, diracStateFromCorrection, ite_eq_right ht]
    exact (dist_add_add_le _ _ _ _).trans (by nlinarith)

/-- The actual state is Borel measurable in the noise path. -/
theorem measurable_diracStatePath (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    Measurable (diracStatePath β h q hq) :=
  (lipschitzWith_diracStatePath β h q hq).continuous.measurable

/-- Any measurable continuous-path noise yields a measurable continuous-path state. -/
theorem measurable_random_diracStatePath {Ω : Type*} [MeasurableSpace Ω]
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {W : Ω → C(Icc (0 : ℝ) 1, ℝ)} (hW : Measurable W) :
    Measurable (fun ω => diracStatePath β h q hq (W ω)) :=
  (measurable_diracStatePath β h q hq).comp hW

/-- The actual state depends only on the past of the noise. -/
theorem diracState_causal {β h q r : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    {W V : ℝ → ℝ} (hW : Continuous W) (hV : Continuous V) (hr : r ≤ 1)
    (hnoise : EqOn W V (Icc (0 : ℝ) r)) :
    EqOn (diracState β h q hq.2 W hW) (diracState β h q hq.2 V hV) (Icc (0 : ℝ) r) := by
  intro t ht
  by_cases htq : t ≤ q
  · rw [diracState_before β h q hq.2 W hW htq,
      diracState_before β h q hq.2 V hV htq, hnoise ht]
  · have hc := (diracCorrection_spec β h q hq.2 W hW).causal
      (diracCorrection_spec β h q hq.2 V hV) hr
      (fun s hs => hnoise ⟨hq.1.trans hs.1, hs.2⟩)
    simp only [diracState, diracStateFromCorrection, ite_eq_right htq]
    rw [hc ⟨(lt_of_not_ge htq).le, ht.2⟩, hnoise ht]

/-- Restrict a continuous noise path to its history up to time `t`. -/
def diracNoisePast (t : Icc (0 : ℝ) 1) (w : C(Icc (0 : ℝ) 1, ℝ)) :
    C(Icc (0 : ℝ) (t : ℝ), ℝ) :=
  ⟨fun s => w ⟨s, s.property.1, s.property.2.trans t.property.2⟩,
    w.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Extend a noise history constantly to the full state time interval. -/
def diracPastExtensionPath (t : Icc (0 : ℝ) 1)
    (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun s => compactNoiseExtension 0 t t.property.1 w s,
    (continuous_compactNoiseExtension 0 t t.property.1 w).comp continuous_subtype_val⟩

theorem lipschitzWith_diracPastExtensionPath (t : Icc (0 : ℝ) 1) :
    LipschitzWith 1 (diracPastExtensionPath t) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  norm_num only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (f := w) (g := v) (projIcc (0 : ℝ) (t : ℝ) t.property.1 (s : ℝ))

/-- Compute the state at time `t` solely from the continuous noise history. -/
def diracEndpointFromPast (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) 1) (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : ℝ :=
  diracStatePath β h q hq (diracPastExtensionPath t w) t

theorem measurable_diracEndpointFromPast (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) 1) : Measurable (diracEndpointFromPast β h q hq t) :=
  ((ContinuousMap.measurable_eval t).comp (measurable_diracStatePath β h q hq)).comp
    (lipschitzWith_diracPastExtensionPath t).continuous.measurable

/-- Exact factorization through the past of the noise, rather than just an informal
nonanticipation statement. -/
theorem diracStatePath_eval_eq_fromPast (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) 1) (w : C(Icc (0 : ℝ) 1, ℝ)) :
    diracStatePath β h q hq w t =
      diracEndpointFromPast β h q hq t (diracNoisePast t w) := by
  let W := compactNoiseExtension 0 1 zero_le_one w
  let v := diracPastExtensionPath t (diracNoisePast t w)
  let V := compactNoiseExtension 0 1 zero_le_one v
  have hW : Continuous W := continuous_compactNoiseExtension 0 1 zero_le_one w
  have hV : Continuous V := continuous_compactNoiseExtension 0 1 zero_le_one v
  have hnoise : EqOn W V (Icc (0 : ℝ) (t : ℝ)) := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans t.property.2⟩
    dsimp [W, V, v, compactNoiseExtension, diracPastExtensionPath, diracNoisePast]
    simp only [projIcc_of_mem zero_le_one hs1]
    change w ⟨s, hs1⟩ = w ⟨(projIcc (0 : ℝ) (t : ℝ) t.property.1 (s : ℝ) : ℝ), _⟩
    simp only [projIcc_of_mem t.property.1 hs]
  exact diracState_causal hq hW hV t.property.2 hnoise ⟨t.property.1, le_rfl⟩

/-- Adaptedness principle: state evaluation is measurable for any sigma algebra
that makes the noise history measurable. -/
theorem measurable_diracState_eval_of_measurable_past
    {Ω : Type*} [MeasurableSpace Ω] (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) 1) (W : Ω → C(Icc (0 : ℝ) 1, ℝ))
    (hW : Measurable (fun ω => diracNoisePast t (W ω))) :
    Measurable (fun ω => diracStatePath β h q hq (W ω) t) := by
  have he : (fun ω => diracStatePath β h q hq (W ω) t) =
      fun ω => diracEndpointFromPast β h q hq t (diracNoisePast t (W ω)) :=
    funext (fun ω => diracStatePath_eval_eq_fromPast β h q hq t (W ω))
  rw [he]
  exact (measurable_diracEndpointFromPast β h q hq t).comp hW

/-- The continuous integral formulation of the actual additive-noise equation. -/
structure IsDiracStateSolution (β h q : ℝ) (W X : ℝ → ℝ) : Prop where
  continuous : Continuous X
  before : ∀ t ∈ Icc (0 : ℝ) q, X t = h + β * W t
  after : ∀ t ∈ Icc q (1 : ℝ),
    X t = h + β * W t + ∫ s in q..t, β ^ 2 * Real.tanh (X s)

/-- The state constructed by Picard–Lindelöf satisfies the genuine integral equation. -/
theorem diracState_spec (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsDiracStateSolution β h q W (diracState β h q hq.2 W hW) :=
  ⟨continuous_diracState β h q hq.2 W hW,
    fun _ ht => diracState_before β h q hq.2 W hW ht.2,
    fun _ ht => diracState_after β h q hq.2 W hW ht⟩

/-- Subtracting the additive noise from any integral-equation solution recovers
an ODE solution; no differentiability of the noise is assumed. -/
theorem IsDiracStateSolution.noiseCorrection
    {β h q : ℝ} {W X : ℝ → ℝ} (hX : IsDiracStateSolution β h q W X)
    (hq : q ≤ 1) : IsDiracNoiseSolution β h q W (fun t => X t - β * W t) := by
  have hf : Continuous (fun s => β ^ 2 * Real.tanh (X s)) :=
    (diracState_continuous_tanh.comp hX.continuous).const_mul (β ^ 2)
  have he (t : ℝ) (ht : t ∈ Icc q (1 : ℝ)) :
      X t - β * W t = h + ∫ s in q..t, β ^ 2 * Real.tanh (X s) := by
    rw [hX.after t ht]
    ring
  refine ⟨?_, ?_⟩
  · rw [he q ⟨le_rfl, hq⟩, intervalIntegral.integral_same, add_zero]
  · intro t ht
    have hd := (intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable q t) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt).const_add h
    have hout := hd.hasDerivWithinAt.congr_of_mem he ht
    convert hout using 1
    unfold diracNoiseDrift
    congr 2
    ring

/-- Pathwise uniqueness among continuous integral-equation solutions. -/
theorem IsDiracStateSolution.eqOn
    {β h q : ℝ} {W X Z : ℝ → ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hX : IsDiracStateSolution β h q W X) (hZ : IsDiracStateSolution β h q W Z) :
    EqOn X Z (Icc (0 : ℝ) 1) := by
  have hc := (hX.noiseCorrection hq.2).eqOn (hZ.noiseCorrection hq.2)
  intro t ht
  by_cases htq : t ≤ q
  · rw [hX.before t ⟨ht.1, htq⟩, hZ.before t ⟨ht.1, htq⟩]
  · have he := hc ⟨(lt_of_not_ge htq).le, ht.2⟩
    dsimp only at he
    linarith

/-- The natural filtration of a measurable continuous-path driver. -/
def diracNoiseFiltration {Ω : Type*} [MeasurableSpace Ω]
    (W : Ω → C(Icc (0 : ℝ) 1, ℝ)) (hW : Measurable W) :
    Filtration (Icc (0 : ℝ) 1) (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (fun t ω => W ω t)
    (fun t => ((ContinuousMap.measurable_eval t).comp hW).stronglyMeasurable)

/-- The constructed state is adapted to the natural filtration of its noise. -/
theorem adapted_diracStatePath {Ω : Type*} [MeasurableSpace Ω]
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (W : Ω → C(Icc (0 : ℝ) 1, ℝ)) (hW : Measurable W) :
    Adapted (diracNoiseFiltration W hW) (fun t ω => diracStatePath β h q hq (W ω) t) := by
  intro t
  let mt : MeasurableSpace Ω := diracNoiseFiltration W hW t
  letI : MeasurableSpace Ω := mt
  apply measurable_diracState_eval_of_measurable_past β h q hq t W
  rw [ContinuousMap.measurable_iff_eval]
  intro s
  let i : Icc (0 : ℝ) 1 := ⟨s, s.property.1, s.property.2.trans t.property.2⟩
  have hi : i ≤ t := s.property.2
  have hm : Measurable (fun ω => W ω i) := by
    apply measurable_iff_comap_le.mpr
    change MeasurableSpace.comap (fun ω => W ω i) inferInstance ≤ mt
    exact le_iSup₂_of_le i hi le_rfl
  exact hm

end Paper
