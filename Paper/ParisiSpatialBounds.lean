module

public import Targets.ParisiFourthUniform
public import Targets.ParisiStrictConvexity
public import Paper.Hyperbolic
public import Paper.ParisiFiniteStep

@[expose] public section

/-! # Actual finite Parisi spatial bounds

The finite recursion and its Gaussian steps are the verified concrete vendor
definitions. Bounds below identify their genuine derivatives; no finite-step
invariance or differentiability property is assumed for the final recursion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open SpinGlass SpinGlass.Targets
open scoped Topology ContDiff

namespace Paper

theorem deriv_finiteParisi (k : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    deriv (parisiF s β j) = parisiFDeriv s β j := by
  funext x
  exact (parisiF_C2_props s β j).1.1 x |>.deriv

theorem deriv_finiteParisi_gradient (k : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    deriv (parisiFDeriv s β j) = parisiFSecond s β j := by
  funext x
  exact (parisiF_C2_props s β j).1.2.1 x |>.deriv

theorem iteratedDeriv_two_finiteParisi (k : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    iteratedDeriv 2 (parisiF s β j) = parisiFSecond s β j := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_finiteParisi,
    deriv_finiteParisi_gradient]

theorem iteratedDeriv_three_finiteParisi (k : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    iteratedDeriv 3 (parisiF s β j) = parisiFThird s β j := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ,
    iteratedDeriv_two_finiteParisi]
  funext x
  exact (hasDerivAt_parisiFSecond s β j x).deriv

theorem iteratedDeriv_four_finiteParisi (k : ℕ) (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    iteratedDeriv 4 (parisiF s β j) = parisiFFourth s β j := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ,
    iteratedDeriv_three_finiteParisi]
  funext x
  exact (hasDerivAt_parisiFThird s β j x).deriv

/-- The coupled Hessian invariant is proved for every actual finite Parisi
level, including zero masses and zero variances. -/
theorem finiteParisi_second_add_gradient_sq_le_one (k : ℕ) (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv 2 (parisiF s β j) x + (deriv (parisiF s β j) x) ^ 2 ≤ 1 := by
  rw [iteratedDeriv_two_finiteParisi, deriv_finiteParisi]
  have h := (parisiF_C2_props s β j).1.2.2.2 x
  linarith

/-- First through fourth spatial derivative bounds are independent of the
number of levels, their locations, and the inverse temperature. -/
theorem finiteParisi_spatial_bounds (k : ℕ) (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (x : ℝ) :
    |deriv (parisiF s β j) x| ≤ 1 ∧
      0 < iteratedDeriv 2 (parisiF s β j) x ∧
      iteratedDeriv 2 (parisiF s β j) x ≤ 1 ∧
      |iteratedDeriv 3 (parisiF s β j) x| ≤ 6 ∧
      |iteratedDeriv 4 (parisiF s β j) x| ≤ 43 := by
  rw [deriv_finiteParisi, iteratedDeriv_two_finiteParisi,
    iteratedDeriv_three_finiteParisi, iteratedDeriv_four_finiteParisi]
  refine ⟨(parisiF_C2_props s β j).1.abs_first_le_one x, parisiFSecond_pos s β j x,
    ?_, abs_parisiFThird_le_six s β j x, abs_parisiFFourth_le_43 s β j x⟩
  exact le_trans (le_abs_self _) ((parisiF_C2_props s β j).1.abs_second_le_one x)

/-- A quantitative Hessian lower invariant for one actual Gaussian step.
Unlike mere strict positivity, this lower bound survives uniform limits. -/
theorem stepD2_ge_exp_neg_two {A A' A'' : ℝ → ℝ} {m v : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hA : HasLinearGrowth A)
    (hC2 : HasParisiC2 A A' A'') (hAm : Measurable A)
    (hA'm : Measurable A') (hA''m : Measurable A'')
    (hlower : ∀ y, Real.exp (-2 * A y) ≤ A'' y) (x : ℝ) :
    Real.exp (-2 * parisiStep m v A x) ≤ stepD2 A A' A'' m v x := by
  let M : ℝ := ∫ z, A (x + Real.sqrt v * z) ∂gaussianReal 0 1
  let B : ℝ := parisiStep m v A x
  have hAi := integrable_of_hasLinearGrowth hA hAm x v
  have hmean : M ≤ B := by
    rcases hm.1.eq_or_lt with hmzero | hmpos
    · simp [B, M, parisiStep, ← hmzero]
    · have h := SpinGlass.integral_le_inv_mul_log_integral_exp hmpos hAi
        (integrable_exp_mul_of_hasLinearGrowth hA hAm m x v)
      simpa only [B, M, parisiStep, ite_eq_right hmpos.ne'] using h
  have hEpos : 0 < tiltE A m v x := tiltE_pos hA hAm x
  have hEeq : tiltE A m v x = Real.exp (m * B) := by
    by_cases hmzero : m = 0
    · simp [tiltE, hmzero]
    · have hexp : m * B = Real.log (tiltE A m v x) := by
        dsimp only [B, parisiStep]
        rw [ite_eq_right hmzero]
        unfold tiltE
        field_simp
      rw [hexp, Real.exp_log hEpos]
  have hJ := exp_integral_le_integral_exp (hAi.const_mul (m - 2))
    (integrable_exp_mul_of_hasLinearGrowth hA hAm (m - 2) x v)
  rw [integral_const_mul] at hJ
  have hQlower : Real.exp ((m - 2) * B) ≤ tiltQ A A'' m v x := by
    calc
      Real.exp ((m - 2) * B) ≤ Real.exp ((m - 2) * M) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hmean (by linarith [hm.2])
      _ ≤ ∫ z, Real.exp ((m - 2) * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1 := hJ
      _ ≤ tiltQ A A'' m v x := by
        apply integral_mono
          (integrable_exp_mul_of_hasLinearGrowth hA hAm (m - 2) x v)
          (integrable_tiltQ hC2.abs_second_le_one hA hAm hA''m x)
        intro z
        dsimp only
        rw [show (m - 2) * A (x + Real.sqrt v * z) =
          (-2 * A (x + Real.sqrt v * z)) + m * A (x + Real.sqrt v * z) by ring,
          Real.exp_add]
        exact mul_le_mul_of_nonneg_right (hlower _) (Real.exp_pos _).le
  have hquot : Real.exp (-2 * B) ≤ tiltQ A A'' m v x / tiltE A m v x := by
    apply (le_div_iff₀ hEpos).mpr
    calc
      Real.exp (-2 * B) * tiltE A m v x = Real.exp ((m - 2) * B) := by
        rw [hEeq, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := hQlower
  have hCS := sq_integral_mul_le hC2.abs_first_le_one hA hAm hA'm (m := m) (v := v) x
  change (tiltP A A' m v x) ^ 2 ≤ tiltR A A' m v x * tiltE A m v x at hCS
  have hvar : 0 ≤ tiltR A A' m v x / tiltE A m v x -
      (tiltP A A' m v x / tiltE A m v x) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) hEpos]
    nlinarith [mul_le_mul_of_nonneg_right hCS hEpos.le]
  exact hquot.trans (le_add_of_nonneg_right (mul_nonneg hm.1 hvar))

/-- Every genuine finite Parisi level has a quantitative Hessian lower
bound. This prevents loss of strict positivity in a measure-approximation
limit once the actual derivatives have been identified. -/
theorem finiteParisi_second_ge_exp_neg_two (k : ℕ) (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (x : ℝ) :
    Real.exp (-2 * parisiF s β j x) ≤ iteratedDeriv 2 (parisiF s β j) x := by
  rw [iteratedDeriv_two_finiteParisi]
  induction j generalizing x with
  | zero =>
    change Real.exp (-2 * Real.log (Real.cosh x)) ≤
      1 - (Real.sinh x / Real.cosh x) ^ 2
    have heq : Real.exp (-2 * Real.log (Real.cosh x)) =
        1 - (Real.sinh x / Real.cosh x) ^ 2 := by
      rw [show -2 * Real.log (Real.cosh x) =
          -(Real.log (Real.cosh x) + Real.log (Real.cosh x)) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log (Real.cosh_pos x)]
      field_simp [ne_of_gt (Real.cosh_pos x)]
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    exact heq.le
  | succ j ih =>
    exact stepD2_ge_exp_neg_two
      ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
      (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
      (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1
      (parisiF_C2_props s β j).2.2 ih x

/-- Genuine third spatial derivative of a finite, possibly partial, slab. -/
noncomputable def parisiSlabThird {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m b t x : ℝ) : ℝ :=
  stepD3Uniform (parisiF s β j) (parisiFDeriv s β j)
    (parisiFSecond s β j) (parisiFThird s β j) m (β ^ 2 * (b - t)) x

/-- Genuine fourth spatial derivative of a finite, possibly partial, slab. -/
noncomputable def parisiSlabFourth {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m b t x : ℝ) : ℝ :=
  stepD4Uniform (parisiF s β j) (parisiFDeriv s β j)
    (parisiFSecond s β j) (parisiFThird s β j) (parisiFFourth s β j)
    m (β ^ 2 * (b - t)) x

theorem hasDerivAt_parisiSlabHessian_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) :
    HasDerivAt (parisiSlabHessian s β j m b t)
      (parisiSlabThird s β j m b t x) x :=
  hasDerivAt_stepD2_uniform (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_C2_props s β j).2.2
    (continuous_parisiFThird s β j).measurable
    (hasDerivAt_parisiFSecond s β j) (abs_parisiFThird_le_six s β j)
    m (β ^ 2 * (b - t)) x

theorem hasDerivAt_parisiSlabThird_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    HasDerivAt (parisiSlabThird s β j m b t)
      (parisiSlabFourth s β j m b t x) x :=
  hasDerivAt_stepD3Uniform (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_C2_props s β j).2.2
    (continuous_parisiFThird s β j).measurable
    (continuous_parisiFFourth s β j).measurable
    (hasDerivAt_parisiFSecond s β j) (hasDerivAt_parisiFThird s β j)
    (abs_parisiFThird_le_six s β j) (abs_parisiFFourth_le_43 s β j) hm
    (β ^ 2 * (b - t)) x

theorem parisiSlabHessian_ge_exp_neg_two {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    Real.exp (-2 * parisiSlabPotential s β j m b t x) ≤
      parisiSlabHessian s β j m b t x := by
  apply stepD2_ge_exp_neg_two hm (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_measurable s β j)
    (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2
  intro y
  simpa only [iteratedDeriv_two_finiteParisi] using
    finiteParisi_second_ge_exp_neg_two k s β j y

theorem parisiSlabHessian_pos {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    0 < parisiSlabHessian s β j m b t x :=
  (Real.exp_pos _).trans_le (parisiSlabHessian_ge_exp_neg_two s β j hm b t x)

theorem abs_parisiSlabThird_le_fourteen {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    |parisiSlabThird s β j m b t x| ≤ 14 := by
  simpa only [parisiSlabThird, show (6 : ℝ) + 8 = 14 by norm_num] using
    abs_stepD3Uniform_le (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_C2_props s β j).2.2
    (abs_parisiFThird_le_six s β j) hm (β ^ 2 * (b - t)) x

theorem abs_parisiSlabFourth_le_143 {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    |parisiSlabFourth s β j m b t x| ≤ 143 := by
  simpa only [parisiSlabFourth, show (43 : ℝ) + 8 * 6 + 52 = 143 by norm_num] using
    abs_stepD4Uniform_le (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_C2_props s β j).2.2
    (abs_parisiFThird_le_six s β j) (abs_parisiFFourth_le_43 s β j)
    hm (β ^ 2 * (b - t)) x

/-- Uniform spatial equicontinuity of the actual finite gradients. -/
theorem lipschitzWith_parisiSlabGradient {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t : ℝ) :
    LipschitzWith 1 (parisiSlabGradient s β j m b t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiSlabGradient_spatial s β j m b t x).differentiableAt)
  intro x
  change ‖deriv (parisiSlabGradient s β j m b t) x‖ ≤ (1 : ℝ)
  rw [(hasDerivAt_parisiSlabGradient_spatial s β j m b t x).deriv,
    Real.norm_eq_abs]
  exact (parisiSlab_C2 s β j hm b t).abs_second_le_one x

/-- The third derivative bound gives a depth-independent Hessian modulus. -/
theorem lipschitzWith_parisiSlabHessian {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t : ℝ) :
    LipschitzWith 14 (parisiSlabHessian s β j m b t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiSlabHessian_spatial s β j m b t x).differentiableAt)
  intro x
  change ‖deriv (parisiSlabHessian s β j m b t) x‖ ≤ (14 : ℝ)
  rw [(hasDerivAt_parisiSlabHessian_spatial s β j m b t x).deriv,
    Real.norm_eq_abs]
  exact abs_parisiSlabThird_le_fourteen s β j hm b t x

/-- The fourth derivative bound gives a depth-independent third-derivative modulus. -/
theorem lipschitzWith_parisiSlabThird {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t : ℝ) :
    LipschitzWith 143 (parisiSlabThird s β j m b t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiSlabThird_spatial s β j hm b t x).differentiableAt)
  intro x
  change ‖deriv (parisiSlabThird s β j m b t) x‖ ≤ (143 : ℝ)
  rw [(hasDerivAt_parisiSlabThird_spatial s β j hm b t x).deriv,
    Real.norm_eq_abs]
  exact abs_parisiSlabFourth_le_143 s β j hm b t x

/-- The strict Hessian lower bound survives converging actual finite slabs;
only the two concrete convergence assertions are needed. -/
theorem parisiSlabHessian_limit_pos (k : ℕ → ℕ) (s : ∀ n, RSBScheme (k n))
    (β : ℝ) (j : ℕ → ℕ) (m b : ℕ → ℝ) (t x : ℝ)
    (hm : ∀ n, m n ∈ Icc (0 : ℝ) 1) {u q : ℝ}
    (hu : Tendsto (fun n => parisiSlabPotential (s n) β (j n) (m n) (b n) t x)
      atTop (𝓝 u))
    (hq : Tendsto (fun n => parisiSlabHessian (s n) β (j n) (m n) (b n) t x)
      atTop (𝓝 q)) : Real.exp (-2 * u) ≤ q ∧ 0 < q := by
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hu.const_mul (-2))
  have hlow : Real.exp (-2 * u) ≤ q :=
    le_of_tendsto_of_tendsto hexp hq (Eventually.of_forall fun n =>
      parisiSlabHessian_ge_exp_neg_two (s n) β (j n) (hm n) (b n) t x)
  exact ⟨hlow, (Real.exp_pos _).trans_le hlow⟩

end Paper
