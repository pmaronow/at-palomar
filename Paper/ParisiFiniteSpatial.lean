module

public import Paper.ParisiSpatialBounds
public import Paper.ParisiFiniteGlue
public import Paper.DerivativeCompactness

@[expose] public section

/-! # Actual finite-to-measure spatial derivative limits

The glued finite Gaussian recursion has a bounded continuous Hessian with a
uniform spatial Lipschitz modulus. Its convergence and the differentiation
of a limiting gradient follow from the concrete finite recursion, without
assuming a derivative or Hessian for the limiting probability measure.
-/

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace Paper
open SpinGlass SpinGlass.Targets

theorem lipschitzWith_parisiFiniteHessianAux {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (t : ℝ) :
    LipschitzWith 14 (parisiFiniteHessianAux s β j t) := by
  induction j with
  | zero =>
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun x => (hasDerivAt_parisiFSecond s β 0 x).differentiableAt)
    intro x
    change ‖deriv (parisiFSecond s β 0) x‖ ≤ (14 : ℝ)
    rw [(hasDerivAt_parisiFSecond s β 0 x).deriv, Real.norm_eq_abs]
    exact (abs_parisiFThird_le_six s β 0 x).trans (by norm_num)
  | succ j ih =>
    by_cases ht : t ≤ s.q (k + 2 - j)
    · simpa only [parisiFiniteHessianAux, ite_eq_left ht] using
        lipschitzWith_parisiSlabHessian s β j
          ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ (s.q (k + 2 - j)) t
    · simpa only [parisiFiniteHessianAux, ite_eq_right ht] using ih

theorem parisiFiniteHessianAux_ge_exp_neg_two {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (t x : ℝ) :
    Real.exp (-2 * parisiFinitePotentialAux s β j t x) ≤
      parisiFiniteHessianAux s β j t x := by
  induction j with
  | zero =>
    simpa only [parisiFinitePotentialAux, parisiFiniteHessianAux,
      iteratedDeriv_two_finiteParisi] using finiteParisi_second_ge_exp_neg_two k s β 0 x
  | succ j ih =>
    by_cases ht : t ≤ s.q (k + 2 - j)
    · simpa only [parisiFinitePotentialAux, parisiFiniteHessianAux, ite_eq_left ht] using
        parisiSlabHessian_ge_exp_neg_two s β j
          ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ (s.q (k + 2 - j)) t x
    · simpa only [parisiFinitePotentialAux, parisiFiniteHessianAux, ite_eq_right ht] using ih

noncomputable def parisiFiniteHessian {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  parisiFiniteHessianAux s β (k + 2) (max 0 (min 1 p.1)) p.2

theorem continuous_parisiFiniteHessian {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    Continuous (parisiFiniteHessian s β) :=
  (continuous_parisiFiniteAux s β le_rfl).2.2.comp
    (show Continuous (fun p : ℝ × ℝ => (max 0 (min 1 p.1), p.2)) by fun_prop)

theorem norm_parisiFiniteHessian_le_one {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : ‖parisiFiniteHessian s β p‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact (parisiFiniteAux_C2 s β (k + 2) (max 0 (min 1 p.1))).abs_second_le_one p.2

noncomputable def parisiFiniteHessianBCF {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (parisiFiniteHessian s β)
    (continuous_parisiFiniteHessian s β) 1 (norm_parisiFiniteHessian_le_one s β)

theorem norm_parisiFiniteHessianBCF_le_one {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ‖parisiFiniteHessianBCF s β‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _

theorem hasDerivAt_parisiFiniteGradient_spatial {k : ℕ} (s : RSBScheme k)
    (β t x : ℝ) :
    HasDerivAt (fun y => parisiFiniteGradient s β (t, y))
      (parisiFiniteHessian s β (t, x)) x :=
  (parisiFiniteAux_C2 s β (k + 2) (max 0 (min 1 t))).2.1 x

theorem lipschitzWith_parisiFiniteHessian {k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    LipschitzWith 14 (fun x => parisiFiniteHessian s β (t, x)) :=
  lipschitzWith_parisiFiniteHessianAux s β (k + 2) (max 0 (min 1 t))

theorem parisiFiniteHessian_ge_exp_neg_two {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℝ × ℝ) : Real.exp (-2 * parisiFinitePotential s β p) ≤
      parisiFiniteHessian s β p :=
  parisiFiniteHessianAux_ge_exp_neg_two s β (k + 2) (max 0 (min 1 p.1)) p.2

theorem parisiFiniteHessian_add_gradient_sq_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (p : ℝ × ℝ) :
    parisiFiniteHessian s β p + (parisiFiniteGradient s β p) ^ 2 ≤ 1 := by
  have h := (parisiFiniteAux_C2 s β (k + 2) (max 0 (min 1 p.1))).2.2.2 p.2
  change parisiFiniteHessian s β p ≤ 1 - (parisiFiniteGradient s β p) ^ 2 at h
  linarith

/-- A uniform limit of actual finite gradients has an actual, jointly
continuous bounded Hessian. Its derivative and curvature constraints are
derived from the finite recursion. -/
theorem finiteParisiGradient_limit_derivative (k : ℕ → ℕ)
    (s : ∀ n, RSBScheme (k n)) (β : ℝ) {V : (ℝ × ℝ) →ᵇ ℝ}
    (hV : Tendsto (fun n => parisiFiniteGradientBCF (s n) β) atTop (𝓝 V)) :
    ∃ H : (ℝ × ℝ) →ᵇ ℝ,
      Tendsto (fun n => parisiFiniteHessianBCF (s n) β) atTop (𝓝 H) ∧
      ‖H‖ ≤ 1 ∧ (∀ t, LipschitzWith 14 (fun x => H (t, x))) ∧
      (∀ t x, HasDerivAt (fun y => V (t, y)) (H (t, x)) x) ∧
      ∀ p, H p + (V p) ^ 2 ≤ 1 := by
  obtain ⟨H, hH, hHL, hHD⟩ := spatialDerivative_of_bcf_tendsto
    (fun n => parisiFiniteGradientBCF (s n) β)
    (fun n => parisiFiniteHessianBCF (s n) β)
    (fun n => hasDerivAt_parisiFiniteGradient_spatial (s n) β)
    (fun n => lipschitzWith_parisiFiniteHessian (s n) β) hV
  have hHu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hH
  have hVu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hV
  refine ⟨H, hH, ?_, hHL, hHD, ?_⟩
  · exact le_of_tendsto hH.norm (Eventually.of_forall fun n =>
      norm_parisiFiniteHessianBCF_le_one (s n) β)
  · intro p
    exact le_of_tendsto ((hHu.tendsto_at p).add ((hVu.tendsto_at p).pow 2))
      (Eventually.of_forall fun n => parisiFiniteHessian_add_gradient_sq_le_one (s n) β p)

theorem finiteParisiHessian_limit_pos (k : ℕ → ℕ) (s : ∀ n, RSBScheme (k n))
    (β : ℝ) {H : (ℝ × ℝ) →ᵇ ℝ}
    (hH : Tendsto (fun n => parisiFiniteHessianBCF (s n) β) atTop (𝓝 H))
    (p : ℝ × ℝ) {u : ℝ}
    (hu : Tendsto (fun n => parisiFinitePotential (s n) β p) atTop (𝓝 u)) :
    Real.exp (-2 * u) ≤ H p ∧ 0 < H p := by
  have hHu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hH
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hu.const_mul (-2))
  have hlow : Real.exp (-2 * u) ≤ H p := le_of_tendsto_of_tendsto hexp (hHu.tendsto_at p)
    (Eventually.of_forall fun n => parisiFiniteHessian_ge_exp_neg_two (s n) β p)
  exact ⟨hlow, (Real.exp_pos _).trans_le hlow⟩

end Paper
