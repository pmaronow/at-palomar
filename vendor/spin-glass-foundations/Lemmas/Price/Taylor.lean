module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-!
# A second-order Taylor estimate with a modulus-of-continuity remainder

The single analytic estimate that drives the proof of Price's theorem: if the second derivative
of `h` varies by at most `ε₀` along the segment `[x, x + v]`, then the second-order Taylor
polynomial of `h` at `x` approximates `h (x + v)` to within `ε₀ * ‖v‖ ^ 2`.
-/

namespace PriceFourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hessian of `h` at `x`, as a continuous bilinear map. -/
noncomputable def hess (h : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ h) x

theorem continuous_fderiv_of_contDiff_two {h : E → ℝ} (hC : ContDiff ℝ 2 h) :
    Continuous (fderiv ℝ h) := hC.continuous_fderiv (by norm_num)

theorem continuous_hess {h : E → ℝ} (hC : ContDiff ℝ 2 h) : Continuous (hess h) := by
  unfold hess
  exact (hC.fderiv_right (m := 1) le_rfl).continuous_fderiv (by norm_num)

theorem hasFDerivAt_fderiv_apply {h : E → ℝ} (hC : ContDiff ℝ 2 h) (v : E) (y : E) :
    HasFDerivAt (fun z => (fderiv ℝ h z) v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (hess h y)) y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) y :=
    (hC.fderiv_right (m := 1) le_rfl).differentiable (by norm_num) y
  exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hd.hasFDerivAt

theorem hasDerivAt_line {h : E → ℝ} (hC : ContDiff ℝ 2 h) (x v : E) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ((fderiv ℝ h (x + θ • v)) v) θ := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v θ := by
    simpa using ((hasDerivAt_id θ).smul_const v).const_add x
  exact (hC.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ h1

theorem hasDerivAt_line_deriv {h : E → ℝ} (hC : ContDiff ℝ 2 h) (x v : E) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => (fderiv ℝ h (x + s • v)) v) ((hess h (x + θ • v) v) v) θ := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v θ := by
    simpa using ((hasDerivAt_id θ).smul_const v).const_add x
  exact (hasFDerivAt_fderiv_apply hC v (x + θ • v)).comp_hasDerivAt θ h1

/-- Second-order Taylor estimate. -/
theorem taylor_two_bound {h : E → ℝ} (hC : ContDiff ℝ 2 h) (x v : E) {ε₀ : ℝ}
    (hb : ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 → ‖hess h (x + θ • v) - hess h x‖ ≤ ε₀) :
    |h (x + v) - h x - fderiv ℝ h x v - (1 / 2) * (hess h x v) v| ≤ ε₀ * ‖v‖ ^ 2 := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  set c : ℝ := (hess h x v) v with hc
  set b : ℝ := fderiv ℝ h x v with hbdef
  -- the second derivative of the one-dimensional restriction
  set g2 : ℝ → ℝ := fun θ => (hess h (x + θ • v) v) v - (1 : ℝ) • c with hg2
  set g1 : ℝ → ℝ :=
    (fun θ => (fderiv ℝ h (x + θ • v)) v) - (fun _ => b) - (fun θ => id θ • c) with hg1
  set g : ℝ → ℝ :=
    (fun θ => h (x + θ • v)) - (fun _ => h x) - (fun θ => id θ • b)
      - (fun θ => (θ ^ 2 / 2) • c) with hg
  have hg2bound : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖g2 θ‖ ≤ ε₀ * ‖v‖ ^ 2 := by
    intro θ hθ
    have h1 : g2 θ = ((hess h (x + θ • v) - hess h x) v) v := by
      simp [hg2, hc]
    rw [h1]
    calc ‖((hess h (x + θ • v) - hess h x) v) v‖
        ≤ ‖(hess h (x + θ • v) - hess h x) v‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖hess h (x + θ • v) - hess h x‖ * ‖v‖) * ‖v‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε₀ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hb θ hθ) (norm_nonneg v)) (norm_nonneg v)
      _ = ε₀ * ‖v‖ ^ 2 := by ring
  have hg1deriv : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g1 (g2 θ) (Set.Icc (0 : ℝ) 1) θ := by
    intro θ _
    have h1 : HasDerivAt (fun s : ℝ => (fderiv ℝ h (x + s • v)) v)
        ((hess h (x + θ • v) v) v) θ := hasDerivAt_line_deriv hC x v θ
    have h2 : HasDerivAt g1
        ((hess h (x + θ • v) v) v - (1 : ℝ) • c) θ := by
      exact (h1.sub_const b).sub ((hasDerivAt_id θ).smul_const c)
    exact h2.hasDerivWithinAt
  have hg1zero : g1 0 = 0 := by simp [hg1, hbdef]
  have hg1bound : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖g1 θ‖ ≤ ε₀ * ‖v‖ ^ 2 := by
    intro θ hθ
    have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg1deriv hg2bound (Set.left_mem_Icc.2 zero_le_one) hθ
    rw [hg1zero, sub_zero] at this
    calc ‖g1 θ‖ ≤ ε₀ * ‖v‖ ^ 2 * ‖θ - 0‖ := this
      _ ≤ ε₀ * ‖v‖ ^ 2 := by
          have h0 : ‖θ - (0 : ℝ)‖ ≤ 1 := by
            rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hθ.1]
            exact hθ.2
          have hnn : 0 ≤ ε₀ * ‖v‖ ^ 2 := by
            have hε : (0 : ℝ) ≤ ε₀ :=
              (norm_nonneg (hess h (x + (0 : ℝ) • v) - hess h x)).trans (hb 0 (by simp))
            positivity
          nlinarith [norm_nonneg (θ - (0:ℝ))]
  have hgderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g (g1 θ) (Set.Icc (0 : ℝ) 1) θ := by
    intro θ _
    have h1 : HasDerivAt (fun s : ℝ => h (x + s • v)) ((fderiv ℝ h (x + θ • v)) v) θ :=
      hasDerivAt_line hC x v θ
    have h2 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • c) (θ • c) θ := by
      have : HasDerivAt (fun s : ℝ => s ^ 2 / 2) θ θ := by
        simpa using ((hasDerivAt_pow 2 θ).div_const 2)
      exact this.smul_const c
    have h3 : HasDerivAt g ((fderiv ℝ h (x + θ • v)) v - (1 : ℝ) • b - θ • c) θ := by
      exact ((h1.sub_const (h x)).sub ((hasDerivAt_id θ).smul_const b)).sub h2
    simpa [hg1] using h3.hasDerivWithinAt
  have hgzero : g 0 = 0 := by simp [hg]
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hgderiv hg1bound (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  rw [hgzero, sub_zero] at this
  have hone : g 1 = h (x + v) - h x - fderiv ℝ h x v - (1 / 2) * (hess h x v) v := by
    simp [hg, hbdef, hc, smul_eq_mul]
  rw [hone] at this
  simpa using this

end PriceFourier
