module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Tactic

@[expose] public section

/-! # Constructive spatial derivative limits

A common Lipschitz modulus for the derivatives makes their finite-difference
approximation uniform. Consequently, convergence of bounded continuous
functions identifies a bounded continuous derivative limit, jointly in any
additional topological parameters. No subsequence or differentiability of the
limit is assumed.
-/

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace Paper

theorem abs_derivative_sub_forward_slope_le {f d : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ x, HasDerivAt f (d x) x) (hL : LipschitzWith C d)
    (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |d x - (f (x + δ) - f x) / δ| ≤ (C : ℝ) * δ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  obtain ⟨y, hy, heq⟩ := exists_hasDerivAt_eq_slope f d
    (show x < x + δ by linarith) hc.continuousOn (fun y _ => hd y)
  have hdist := hL.dist_le_mul x y
  simp only [Real.dist_eq] at hdist
  have hxy : |x - y| ≤ δ := abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hsl : d y = (f (x + δ) - f x) / δ := by simpa only [add_sub_cancel_left] using heq
  rw [← hsl]
  exact hdist.trans (mul_le_mul_of_nonneg_left hxy C.property)

theorem abs_derivatives_sub_le_of_uniform_bound {f g d e : ℝ → ℝ}
    {C : ℝ≥0} {M : ℝ} (hd : ∀ x, HasDerivAt f (d x) x)
    (he : ∀ x, HasDerivAt g (e x) x) (hdL : LipschitzWith C d)
    (heL : LipschitzWith C e) (hM : ∀ x, |f x - g x| ≤ M)
    (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |d x - e x| ≤ 2 * (C : ℝ) * δ + 2 * M / δ := by
  let S := (f (x + δ) - f x) / δ
  let T := (g (x + δ) - g x) / δ
  have hdS := abs_derivative_sub_forward_slope_le hd hdL x hδ
  have heT := abs_derivative_sub_forward_slope_le he heL x hδ
  have hST : |S - T| ≤ 2 * M / δ := by
    dsimp only [S, T]
    rw [← sub_div, abs_div, abs_of_pos hδ]
    apply (div_le_div_iff_of_pos_right hδ).mpr
    rw [show f (x + δ) - f x - (g (x + δ) - g x) =
      (f (x + δ) - g (x + δ)) - (f x - g x) by ring]
    exact (abs_sub _ _).trans (by linarith [hM (x + δ), hM x])
  have H := (abs_add_le (d x - S) (S - T)).trans
    (add_le_add (le_refl _) hST)
  have H' := abs_add_le (d x - S + (S - T)) (T - e x)
  rw [show d x - S + (S - T) = d x - T by ring] at H H'
  rw [show d x - T + (T - e x) = d x - e x by ring] at H'
  have heT' : |T - e x| ≤ (C : ℝ) * δ := by simpa only [abs_sub_comm] using heT
  dsimp only [S, T] at H H'
  linarith

theorem norm_spatialDerivatives_sub_le {P : Type*} [TopologicalSpace P]
    (f g d e : (P × ℝ) →ᵇ ℝ) {C : ℝ≥0}
    (hd : ∀ p x, HasDerivAt (fun y => f (p, y)) (d (p, x)) x)
    (he : ∀ p x, HasDerivAt (fun y => g (p, y)) (e (p, x)) x)
    (hdL : ∀ p, LipschitzWith C (fun x => d (p, x)))
    (heL : ∀ p, LipschitzWith C (fun x => e (p, x)))
    {δ : ℝ} (hδ : 0 < δ) :
    ‖d - e‖ ≤ 2 * (C : ℝ) * δ + 2 * ‖f - g‖ / δ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro z
  simp only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs]
  apply abs_derivatives_sub_le_of_uniform_bound (hd z.1) (he z.1)
    (hdL z.1) (heL z.1) (δ := δ) ?_ z.2 hδ
  intro x
  simpa only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] using
    (f - g).norm_coe_le_norm (z.1, x)

/-- Uniform convergence and a shared derivative modulus give a Cauchy
sequence of actual spatial derivatives in the complete BCF space. -/
theorem cauchySeq_spatialDerivatives {P : Type*} [TopologicalSpace P]
    (f d : ℕ → (P × ℝ) →ᵇ ℝ) {C : ℝ≥0}
    (hd : ∀ n p x, HasDerivAt (fun y => f n (p, y)) (d n (p, x)) x)
    (hL : ∀ n p, LipschitzWith C (fun x => d n (p, x)))
    (hf : CauchySeq f) : CauchySeq d := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (C : ℝ))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε * δ / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hfn := hN m hm n hn
  rw [dist_eq_norm] at hfn ⊢
  have hterm : 2 * ‖f m - f n‖ / δ < ε / 2 := by
    apply (div_lt_iff₀ hδ).mpr
    nlinarith
  exact (norm_spatialDerivatives_sub_le (f m) (f n) (d m) (d n)
    (hd m) (hd n) (hL m) (hL n) hδ).trans_lt (by linarith)

/-- Derivative completeness, jointly in arbitrary additional parameters.
The limit is genuinely differentiated, rather than supplied as a premise. -/
theorem spatialDerivative_of_bcf_tendsto {P : Type*} [TopologicalSpace P]
    (f d : ℕ → (P × ℝ) →ᵇ ℝ) {F : (P × ℝ) →ᵇ ℝ} {C : ℝ≥0}
    (hd : ∀ n p x, HasDerivAt (fun y => f n (p, y)) (d n (p, x)) x)
    (hL : ∀ n p, LipschitzWith C (fun x => d n (p, x)))
    (hf : Tendsto f atTop (𝓝 F)) :
    ∃ D : (P × ℝ) →ᵇ ℝ, Tendsto d atTop (𝓝 D) ∧
      (∀ p, LipschitzWith C (fun x => D (p, x))) ∧
      ∀ p x, HasDerivAt (fun y => F (p, y)) (D (p, x)) x := by
  obtain ⟨D, hD⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_spatialDerivatives f d hd hL hf.cauchySeq)
  have hDu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hD
  have hFu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf
  refine ⟨D, hD, ?_, ?_⟩
  · intro p
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hDu.tendsto_at (p, x)).dist (hDu.tendsto_at (p, y)))
      (Eventually.of_forall fun n => (hL n p).dist_le_mul x y)
  · intro p x
    exact hasDerivAt_of_tendstoUniformly (hDu.comp (fun y => (p, y)))
      (Eventually.of_forall fun n y => hd n p y)
      (fun y => hFu.tendsto_at (p, y)) x

end Paper
