module

public import Paper.GaussianHeat
public import Paper.ParisiPDE
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! # The backward heat identity for time-dependent tests

Derivative exchange is proved against the actual standard Gaussian measure.
The space-time derivative is assembled from the proved time and variance
partials. Bounded smooth compactly supported tests satisfy the regularity
hypotheses by the test-regularity lemmas.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

noncomputable def gaussianTestAverage (φ : ℝ × ℝ → ℝ) (x t ell : ℝ) : ℝ :=
  gaussianExpectation (fun z => φ (t, x + Real.sqrt ell * z))

theorem continuous_gaussianTestAverage (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ)
    (M : ℝ) (hb : ∀ p, ‖φ p‖ ≤ M) (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => gaussianTestAverage φ x p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => M)
  · intro p
    exact (hφ.comp (by fun_prop : Continuous (fun z : ℝ =>
      (p.1, x + Real.sqrt p.2 * z)))).aestronglyMeasurable
  · intro p
    exact .of_forall fun z => hb _
  · exact integrable_const M
  · exact .of_forall fun z => hφ.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1, x + Real.sqrt p.2 * z)))

theorem integrable_gaussianTestAverage_integrand (φ : ℝ × ℝ → ℝ) (hφ : Continuous φ)
    (M : ℝ) (hb : ∀ p, ‖φ p‖ ≤ M) (x t ell : ℝ) :
    Integrable (fun z => φ (t, x + Real.sqrt ell * z)) (gaussianReal 0 1) := by
  apply (integrable_const M).mono'
    (hφ.comp (by fun_prop : Continuous (fun z : ℝ =>
      (t, x + Real.sqrt ell * z)))).aestronglyMeasurable
  exact .of_forall fun z => hb _

theorem hasDerivAt_gaussianTestAverage_time (φ dT : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hdT : Continuous dT) (M L : ℝ)
    (hφb : ∀ p, ‖φ p‖ ≤ M) (hdTb : ∀ p, ‖dT p‖ ≤ L)
    (hT : ∀ t y, HasDerivAt (fun r => φ (r, y)) (dT (t, y)) t)
    (x t ell : ℝ) :
    HasDerivAt (fun r => gaussianTestAverage φ x r ell)
      (gaussianTestAverage dT x t ell) t := by
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable
      (fun z => φ (r, x + Real.sqrt ell * z)) (gaussianReal 0 1) :=
    .of_forall fun r => (hφ.comp (by fun_prop : Continuous
      (fun z : ℝ => (r, x + Real.sqrt ell * z)))).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun z => dT (t, x + Real.sqrt ell * z))
      (gaussianReal 0 1) :=
    (hdT.comp (by fun_prop : Continuous (fun z : ℝ =>
      (t, x + Real.sqrt ell * z)))).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r z => φ (r, x + Real.sqrt ell * z))
    (F' := fun r z => dT (r, x + Real.sqrt ell * z))
    (s := univ) (bound := fun _ => L) (by simp) hmeas
    (integrable_gaussianTestAverage_integrand φ hφ M hφb x t ell) hdm
    (.of_forall fun z r _ => hdTb _) (integrable_const L)
    (.of_forall fun z r _ => hT r _)).2

theorem hasDerivAt_gaussianTestAverage_variance (φ dX dXX : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hdX : Continuous dX) (hdXX : Continuous dXX) (M L K : ℝ)
    (hφb : ∀ p, ‖φ p‖ ≤ M) (hdXb : ∀ p, ‖dX p‖ ≤ L) (hdXXb : ∀ p, ‖dXX p‖ ≤ K)
    (hX : ∀ t y, HasDerivAt (fun z => φ (t, z)) (dX (t, y)) y)
    (hXX : ∀ t y, HasDerivAt (fun z => dX (t, z)) (dXX (t, y)) y)
    (x t ell : ℝ) (hell : 0 < ell) :
    HasDerivAt (gaussianTestAverage φ x t)
      ((1 / 2 : ℝ) * gaussianTestAverage dXX x t ell) ell := by
  exact hasDerivAt_gaussian_variance (fun y => φ (t, y)) (fun y => dX (t, y))
    (fun y => dXX (t, y)) x ell L K hell
    (hφ.comp (by fun_prop)) (hdX.comp (by fun_prop)) (hdXX.comp (by fun_prop))
    (integrable_gaussianTestAverage_integrand φ hφ M hφb x t ell)
    (hX t) (hXX t) (fun y => hdXb _) (fun y => hdXXb _)

theorem hasDerivAt_gaussianTestAverage_backward (φ dT dX dXX : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hdT : Continuous dT) (hdX : Continuous dX) (hdXX : Continuous dXX)
    (M L J K : ℝ) (hφb : ∀ p, ‖φ p‖ ≤ M) (hdTb : ∀ p, ‖dT p‖ ≤ L)
    (hdXb : ∀ p, ‖dX p‖ ≤ J) (hdXXb : ∀ p, ‖dXX p‖ ≤ K)
    (hT : ∀ t y, HasDerivAt (fun r => φ (r, y)) (dT (t, y)) t)
    (hX : ∀ t y, HasDerivAt (fun z => φ (t, z)) (dX (t, y)) y)
    (hXX : ∀ t y, HasDerivAt (fun z => dX (t, z)) (dXX (t, y)) y)
    (β s t x : ℝ) (hell : 0 < β ^ 2 * (s - t)) :
    HasDerivAt (fun r => gaussianTestAverage φ x r (β ^ 2 * (s - r)))
      (gaussianTestAverage dT x t (β ^ 2 * (s - t)) -
        β ^ 2 / 2 * gaussianTestAverage dXX x t (β ^ 2 * (s - t))) t := by
  let ell := β ^ 2 * (s - t)
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, ell), 0 < p.2 :=
    continuous_snd.continuousAt.tendsto.eventually (eventually_gt_nhds hell)
  have hfd : HasStrictFDerivAt (fun p : ℝ × ℝ => gaussianTestAverage φ x p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (gaussianTestAverage dT x t ell)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) *
          gaussianTestAverage dXX x t ell))) (t, ell) := by
    apply hasStrictFDerivAt_uncurry_coprod
      (u := (t, ell))
      (f := fun t ell => gaussianTestAverage φ x t ell)
      (f₁ := fun t ell => ContinuousLinearMap.toSpanSingleton ℝ (gaussianTestAverage dT x t ell))
      (f₂ := fun t ell => ContinuousLinearMap.toSpanSingleton ℝ
        ((1 / 2 : ℝ) * gaussianTestAverage dXX x t ell))
    · exact .of_forall fun p => (hasDerivAt_gaussianTestAverage_time φ dT hφ hdT M L
        hφb hdTb hT x p.1 p.2).hasFDerivAt
    · filter_upwards [hpos] with p hp
      exact (hasDerivAt_gaussianTestAverage_variance φ dX dXX hφ hdX hdXX M J K
        hφb hdXb hdXXb hX hXX x p.1 p.2 hp).hasFDerivAt
    · exact ((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp
        (continuous_gaussianTestAverage dT hdT L hdTb x)).continuousAt
    · exact ((ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp
        (continuous_const.mul (continuous_gaussianTestAverage dXX hdXX K hdXXb x))).continuousAt
  have hdell : HasDerivAt (fun r : ℝ => β ^ 2 * (s - r)) (-β ^ 2) t := by
    convert ((hasDerivAt_id t).const_sub s).const_mul (β ^ 2) using 1
    · ext r
      rfl
    · ring
  have hc := hfd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hdell)
  convert hc using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, one_mul]
    dsimp [ell]
    ring

theorem gaussianTestAverage_adjointSource (dT dXX : ℝ × ℝ → ℝ)
    (hdT : Continuous dT) (hdXX : Continuous dXX) (L K : ℝ)
    (hdTb : ∀ p, ‖dT p‖ ≤ L) (hdXXb : ∀ p, ‖dXX p‖ ≤ K)
    (c x t ell : ℝ) :
    gaussianTestAverage (fun p => -dT p + c * dXX p) x t ell =
      -gaussianTestAverage dT x t ell + c * gaussianTestAverage dXX x t ell := by
  have he := integral_add
    (integrable_gaussianTestAverage_integrand dT hdT L hdTb x t ell).neg
    ((integrable_gaussianTestAverage_integrand dXX hdXX K hdXXb x t ell).const_mul c)
  simpa only [gaussianTestAverage, gaussianExpectation, Pi.neg_apply,
    integral_neg, integral_const_mul] using he

/-- Integrating the adjoint heat generator along its true backward heat
evolution leaves only the endpoint tests. No heat-equation assumption is used. -/
theorem integral_heat_adjointSource (φ dT dX dXX : ℝ × ℝ → ℝ)
    (hφ : Continuous φ) (hdT : Continuous dT) (hdX : Continuous dX) (hdXX : Continuous dXX)
    (M L J K : ℝ) (hφb : ∀ p, ‖φ p‖ ≤ M) (hdTb : ∀ p, ‖dT p‖ ≤ L)
    (hdXb : ∀ p, ‖dX p‖ ≤ J) (hdXXb : ∀ p, ‖dXX p‖ ≤ K)
    (hT : ∀ t y, HasDerivAt (fun r => φ (r, y)) (dT (t, y)) t)
    (hX : ∀ t y, HasDerivAt (fun z => φ (t, z)) (dX (t, y)) y)
    (hXX : ∀ t y, HasDerivAt (fun z => dX (t, z)) (dXX (t, y)) y)
    (β s x : ℝ) (hβ : β ≠ 0) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, heatSemigroup (β ^ 2 * (s - t))
      (fun y => -dT (t, y) + β ^ 2 / 2 * dXX (t, y)) x) =
        -φ (s, x) + heatSemigroup (β ^ 2 * s) (fun y => φ (0, y)) x := by
  let ψ : ℝ × ℝ → ℝ := fun p => -dT p + β ^ 2 / 2 * dXX p
  have hψ : Continuous ψ := hdT.neg.add (continuous_const.mul hdXX)
  have hψb : ∀ p, ‖ψ p‖ ≤ L + ‖β ^ 2 / 2‖ * K := by
    intro p
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa only [norm_neg] using hdTb p)
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hdXXb p) (norm_nonneg _)))
  have havgφ := (continuous_gaussianTestAverage φ hφ M hφb x).comp
    (show Continuous (fun t : ℝ => (t, β ^ 2 * (s - t))) by fun_prop)
  have havgψ := (continuous_gaussianTestAverage ψ hψ
    (L + ‖β ^ 2 / 2‖ * K) hψb x).comp
    (show Continuous (fun t : ℝ => (t, β ^ 2 * (s - t))) by fun_prop)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    havgφ.neg.continuousOn (f' := fun t => gaussianTestAverage ψ x t (β ^ 2 * (s - t)))
    (fun t ht => by
      have hell : 0 < β ^ 2 * (s - t) :=
        mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr ht.2)
      have hd := (hasDerivAt_gaussianTestAverage_backward φ dT dX dXX hφ hdT hdX hdXX
        M L J K hφb hdTb hdXb hdXXb hT hX hXX β s t x hell).neg
      rw [gaussianTestAverage_adjointSource dT dXX hdT hdXX L K hdTb hdXXb] 
      convert hd using 1
      · ext r
        rfl
      · ring)
    (havgψ.intervalIntegrable 0 s)
  simpa [gaussianTestAverage, ψ, heatSemigroup, gaussianExpectation] using he

end Paper
