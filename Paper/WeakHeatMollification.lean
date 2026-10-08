module

public import Paper.ParisiTerminalWeak
public import Paper.HeatMaximum
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

/-! # Genuine space-time mollification of the weak backward heat equation -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff Convolution

namespace Paper

noncomputable def planeMollify (f g : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g

theorem planeMollify_eq_integral (f g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    planeMollify f g p = ∫ q, f q * g (p - q) := rfl

theorem contDiff_planeMollify (f g : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (planeMollify f g) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hg

theorem parisiTestT_planeMollify (f g : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    parisiTestT (planeMollify f g) = planeMollify f (parisiTestT g) := by
  funext p
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf (hg.of_le (by simp)) p
  rw [parisiTestT_eq_fderiv _ (contDiff_planeMollify f g hf hg hc)]
  change (fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p) (1, 0) = _
  rw [hd.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hc.fderiv ℝ)
    (hg.continuous_fderiv (by simp)) p (1, 0)]
  simp_rw [← parisiTestT_eq_fderiv g hg]
  rfl

theorem parisiTestX_planeMollify (f g : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    parisiTestX (planeMollify f g) = planeMollify f (parisiTestX g) := by
  funext p
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf (hg.of_le (by simp)) p
  rw [parisiTestX_eq_fderiv _ (contDiff_planeMollify f g hf hg hc)]
  change (fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p) (0, 1) = _
  rw [hd.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hc.fderiv ℝ)
    (hg.continuous_fderiv (by simp)) p (0, 1)]
  simp_rw [← parisiTestX_eq_fderiv g hg]
  rfl

theorem parisiTestXX_planeMollify (f g : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    parisiTestXX (planeMollify f g) = planeMollify f (parisiTestXX g) := by
  unfold parisiTestXX
  rw [parisiTestX_planeMollify f g hf hg hc]
  change parisiTestX (planeMollify f (parisiTestX g)) = planeMollify f (parisiTestXX g)
  rw [parisiTestX_planeMollify f (parisiTestX g) hf (contDiff_parisiTestX g hg)
    (hasCompactSupport_parisiTestX g hg hc)]
  rfl

noncomputable def reflectedKernel (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ → ℝ :=
  fun q => g (p - q)

theorem contDiff_reflectedKernel (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (reflectedKernel g p) := hg.comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_reflectedKernel (g : ℝ × ℝ → ℝ)
    (hc : HasCompactSupport g) (p : ℝ × ℝ) : HasCompactSupport (reflectedKernel g p) :=
  hc.comp_homeomorph (Homeomorph.subLeft p)

theorem parisiTestT_reflectedKernel (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (p q : ℝ × ℝ) :
    parisiTestT (reflectedKernel g p) q = -parisiTestT g (p - q) := by
  have hd := (hasDerivAt_parisiTestT g hg (p.1 - q.1) (p.2 - q.2)).comp q.1
    ((hasDerivAt_const q.1 p.1).sub (hasDerivAt_id q.1))
  change deriv (fun t => g (p.1 - t, p.2 - q.2)) q.1 = -parisiTestT g (p - q)
  rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.ext rfl rfl]
  simpa only [Function.comp_def, mul_neg, mul_one, sub_zero, zero_sub] using hd.deriv

theorem parisiTestX_reflectedKernel (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (p q : ℝ × ℝ) :
    parisiTestX (reflectedKernel g p) q = -parisiTestX g (p - q) := by
  have hd := (hasDerivAt_parisiTestX g hg (p.1 - q.1) (p.2 - q.2)).comp q.2
    ((hasDerivAt_const q.2 p.2).sub (hasDerivAt_id q.2))
  change deriv (fun x => g (p.1 - q.1, p.2 - x)) q.2 = -parisiTestX g (p - q)
  rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.ext rfl rfl]
  simpa only [Function.comp_def, mul_neg, mul_one, sub_zero, zero_sub] using hd.deriv

theorem parisiTestXX_reflectedKernel (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (p q : ℝ × ℝ) :
    parisiTestXX (reflectedKernel g p) q = parisiTestXX g (p - q) := by
  have hd := (hasDerivAt_parisiTestXX g hg (p.1 - q.1) (p.2 - q.2)).comp q.2
    ((hasDerivAt_const q.2 p.2).sub (hasDerivAt_id q.2))
  have he : (fun y => parisiTestX (reflectedKernel g p) (q.1, y)) =
      fun y => -parisiTestX g (p.1 - q.1, p.2 - y) := by
    funext y
    exact parisiTestX_reflectedKernel g hg p (q.1, y)
  unfold parisiTestXX
  rw [he]
  convert hd.neg.deriv using 1
  · rfl
  · simp only [mul_neg, mul_one, zero_sub, neg_neg, parisiTestXX,
      Prod.fst_sub, Prod.snd_sub]

theorem tsupport_reflectedKernel_positive (g : ℝ × ℝ → ℝ)
    (_hg : Continuous g) (p : ℝ × ℝ) (r : ℝ)
    (hsupp : tsupport g ⊆ Metric.closedBall 0 r) (hp : r < p.1) :
    tsupport (reflectedKernel g p) ⊆ {q : ℝ × ℝ | 0 < q.1} := by
  intro q hq
  have hmem : p - q ∈ tsupport g := by
    have hh := tsupport_comp_subset_preimage g (show Continuous (fun q : ℝ × ℝ => p - q) by fun_prop)
    exact hh hq
  have hnorm : ‖p - q‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hsupp hmem
  have hfst : |p.1 - q.1| ≤ r := by
    have hh : |p.1 - q.1| ≤ ‖p - q‖ := by
      simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (p - q)
    exact hh.trans hnorm
  have hh := (abs_le.mp hfst).2
  change 0 < q.1
  linarith

/-- A compact space-time convolution of an actual weak heat solution
satisfies the classical heat equation wherever the translated test stays
inside positive times. -/
theorem planeMollify_backwardHeat_equation (β : ℝ) (f g : ℝ × ℝ → ℝ)
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ q, f q * parisiAdjointSource β φ q) = 0)
    (r : ℝ) (hsupp : tsupport g ⊆ Metric.closedBall 0 r)
    (p : ℝ × ℝ) (hp : r < p.1) :
    parisiTestT (planeMollify f g) p + β ^ 2 / 2 * parisiTestXX (planeMollify f g) p = 0 := by
  have he := hweak (reflectedKernel g p) (contDiff_reflectedKernel g hg p)
    (hasCompactSupport_reflectedKernel g hc p)
    (tsupport_reflectedKernel_positive g hg.continuous p r hsupp hp)
  have hiT := (hasCompactSupport_parisiTestT g hg hc).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf (continuous_parisiTestT g hg) p
  have hiXX := (hasCompactSupport_parisiTestXX g hg hc).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf (continuous_parisiTestXX g hg) p
  have hiT' : Integrable (fun q => f q * parisiTestT g (p - q)) := hiT
  have hiXX' : Integrable (fun q => f q * parisiTestXX g (p - q)) := hiXX
  rw [parisiTestT_planeMollify f g hf hg hc, parisiTestXX_planeMollify f g hf hg hc,
    planeMollify_eq_integral, planeMollify_eq_integral, ← integral_const_mul,
    ← integral_add hiT' (hiXX'.const_mul _)]
  convert he using 1
  apply integral_congr_ae
  exact .of_forall fun q => by
    unfold parisiAdjointSource
    dsimp only
    rw [parisiTestT_reflectedKernel g hg,
      parisiTestXX_reflectedKernel g hg]
    ring

theorem planeMollify_zero_after (f g : ℝ × ℝ → ℝ) (r b : ℝ)
    (hsupp : tsupport g ⊆ Metric.closedBall 0 r)
    (hzero : ∀ q : ℝ × ℝ, b ≤ q.1 → f q = 0)
    (p : ℝ × ℝ) (hp : b + r ≤ p.1) : planeMollify f g p = 0 := by
  rw [planeMollify_eq_integral]
  apply integral_eq_zero_of_ae
  exact .of_forall fun q => by
    change f q * g (p - q) = 0
    by_cases hgq : g (p - q) = 0
    · simp only [hgq, mul_zero]
    · have hmem : p - q ∈ tsupport g := subset_closure hgq
      have hnorm : ‖p - q‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hsupp hmem
      have hfst : |p.1 - q.1| ≤ r := by
        have hh : |p.1 - q.1| ≤ ‖p - q‖ := by
          simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (p - q)
        exact hh.trans hnorm
      rw [hzero q (by have hh := (abs_le.mp hfst).2; linarith), zero_mul]

theorem norm_planeMollify_linearGrowth_le (f g : ℝ × ℝ → ℝ)
    (hg : Continuous g) (hc : HasCompactSupport g) (r A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hsupp : tsupport g ⊆ Metric.closedBall 0 r)
    (hmass : (∫ q, ‖g q‖) = 1)
    (hb : ∀ q : ℝ × ℝ, ‖f q‖ ≤ A + L * ‖q.2‖) (p : ℝ × ℝ) :
    ‖planeMollify f g p‖ ≤ (A + L * r) + L * ‖p.2‖ := by
  have hgi : Integrable (fun q => ‖g (p - q)‖) :=
    (hg.integrable_of_hasCompactSupport hc).norm.comp_sub_left p
  have hC : 0 ≤ A + L * (‖p.2‖ + r) := by positivity
  have hbound : ∀ q : ℝ × ℝ, ‖f q * g (p - q)‖ ≤
      (A + L * (‖p.2‖ + r)) * ‖g (p - q)‖ := by
    intro q
    by_cases hz : g (p - q) = 0
    · simpa only [hz, mul_zero, norm_zero] using (le_refl (0 : ℝ))
    · have hnorm : ‖p - q‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hsupp (subset_closure hz)
      have hx : ‖q.2‖ ≤ ‖p.2‖ + r := by
        have hh : ‖q.2‖ ≤ ‖p.2‖ + ‖(p - q).2‖ := by
          calc
            _ = ‖p.2 - (p - q).2‖ := by congr 1; simp only [Prod.snd_sub]; ring
            _ ≤ _ := norm_sub_le _ _
        exact hh.trans (add_le_add (le_refl _) ((norm_snd_le (p - q)).trans hnorm))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb q).trans
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hx hL))) (norm_nonneg _)
  have h := norm_integral_le_of_norm_le (f := fun q => f q * g (p - q))
    (hgi.const_mul (A + L * (‖p.2‖ + r))) (.of_forall hbound)
  rw [integral_const_mul, integral_sub_left_eq_self (fun q => ‖g q‖) volume p, hmass, mul_one] at h
  exact h.trans_eq (by ring)

noncomputable def weakHeatPlaneBump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := (1 / (n + 1 : ℝ)) / 2
  rOut := 1 / (n + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith

theorem weakHeatPlaneBump_rOut_tendsto :
    Tendsto (fun n => (weakHeatPlaneBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem planeMollify_bump_tendsto (f : ℝ × ℝ → ℝ) (hf : Continuous f) (p : ℝ × ℝ) :
    Tendsto (fun n => planeMollify f ((weakHeatPlaneBump n).normed volume) p)
      atTop (𝓝 (f p)) := by
  have hl := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) weakHeatPlaneBump_rOut_tendsto hf p
  have hsym : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    rfl
  apply hl.congr
  intro n
  unfold planeMollify
  rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) hsym]
  rfl

/-- Uniqueness of a continuous linear-growth weak heat solution extended
by zero beyond its terminal time.  The proof derives the classical equation
for genuine compact space-time mollifications and passes to their limit. -/
theorem global_weak_backwardHeat_eq_zero (β : ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hb : ∀ p : ℝ × ℝ, ‖f p‖ ≤ A + L * ‖p.2‖)
    (hzero : ∀ p : ℝ × ℝ, 1 ≤ p.1 → f p = 0)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ q, f q * parisiAdjointSource β φ q) = 0)
    (p : ℝ × ℝ) (hp : p.1 ∈ Ioc (0 : ℝ) 1) : f p = 0 := by
  have hloc : LocallyIntegrable f (volume : Measure (ℝ × ℝ)) := hf.locallyIntegrable
  have hev : ∀ᶠ n in atTop,
      planeMollify f ((weakHeatPlaneBump n).normed volume) p = 0 := by
    have hsmall := weakHeatPlaneBump_rOut_tendsto.eventually
      (eventually_lt_nhds (show 0 < p.1 / 2 by linarith [hp.1]))
    filter_upwards [hsmall] with n hn
    let g := (weakHeatPlaneBump n).normed volume
    let r := (weakHeatPlaneBump n).rOut
    have hr : 0 < r := (weakHeatPlaneBump n).rOut_pos
    have hg : ContDiff ℝ ∞ g := (weakHeatPlaneBump n).contDiff_normed
    have hc : HasCompactSupport g := (weakHeatPlaneBump n).hasCompactSupport_normed
    have hs : tsupport g ⊆ Metric.closedBall 0 r := by
      rw [(weakHeatPlaneBump n).tsupport_normed_eq]
    have hmass : (∫ q, ‖g q‖) = 1 := by
      change (∫ q, ‖(weakHeatPlaneBump n).normed volume q‖) = 1
      simp_rw [Real.norm_of_nonneg ((weakHeatPlaneBump n).nonneg_normed _)]
      exact (weakHeatPlaneBump n).integral_normed (μ := volume)
    have hsmooth := contDiff_planeMollify f g hloc hg hc
    have hxx (t x : ℝ) : DifferentiableAt ℝ
        (deriv (fun y => planeMollify f g (t, y))) x := by
      change DifferentiableAt ℝ (fun y => parisiTestX (planeMollify f g) (t, y)) x
      exact (hasDerivAt_parisiTestXX _ hsmooth t x).differentiableAt
    have heq := classical_backwardHeat_eq_zero_of_linearGrowth
      (β ^ 2 / 2) (p.1 / 2) (1 + 2 * r) (A + L * r) L
      (by positivity) (by dsimp [r] at *; linarith [hp.2])
      (by positivity) hL (planeMollify f g) hsmooth.continuous.continuousOn
      (fun t _ x => (hasDerivAt_parisiTestT _ hsmooth t x).differentiableAt)
      (fun t _ x => (hasDerivAt_parisiTestX _ hsmooth t x).differentiableAt)
      (fun t _ x => hxx t x)
      (fun t ht x => planeMollify_backwardHeat_equation β f g hloc hg hc hweak
        r hs (t, x) (by dsimp [r] at *; linarith [ht.1]))
      (fun t _ x => norm_planeMollify_linearGrowth_le f g hg.continuous hc r A L
        hA hL hr.le hs hmass hb (t, x))
      (fun x => planeMollify_zero_after f g r 1 hs hzero (1 + 2 * r, x)
        (by dsimp; linarith))
    exact heq p ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, mem_univ _⟩
  have hl := planeMollify_bump_tendsto f hf p
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))

end Paper
