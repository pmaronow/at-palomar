module

public import Paper.ParisiSpatialBounds
public import Paper.HJBVerification

@[expose] public section

/-! # Genuine finite-slab gradient time equation -/

open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open SpinGlass SpinGlass.Targets
open scoped Topology ContDiff

namespace Paper

theorem hasDerivAt_parisiSlabGradient_time {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b x : ℝ) {t : ℝ} (ht : t < b) :
    HasDerivAt (fun r => parisiSlabGradient s β j m b r x)
      (-(β ^ 2 / 2) * (parisiSlabThird s β j m b t x +
        2 * m * parisiSlabGradient s β j m b t x * parisiSlabHessian s β j m b t x)) t := by
  have hv : 0 < β ^ 2 * (b - t) := mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr ht)
  have hd := hasDerivAt_stepD1_parisiF_variance s β j m x hv
  have h3 := stepD3_eq_stepD3Uniform (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (continuous_parisiFSecond s β j)
    (continuous_parisiFThird s β j).measurable (hasDerivAt_parisiFSecond s β j)
    (abs_parisiFThird_le_six s β j) hm hv x
  have h3' : parisiSlabThird s β j m b t x =
      2 * stepD1Variance (parisiF s β j) (parisiFDeriv s β j)
        (parisiFSecond s β j) m (β ^ 2 * (b - t)) x -
      2 * m * parisiSlabGradient s β j m b t x * parisiSlabHessian s β j m b t x := h3.symm
  convert! hd.comp t (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul (β ^ 2)) using 1
  · dsimp only [parisiSlabThird, parisiSlabGradient, parisiSlabHessian] at h3' ⊢
    rw [h3']
    ring

theorem continuous_parisiSlabThird {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b : ℝ) :
    Continuous (fun p : ℝ × ℝ => parisiSlabThird s β j m b p.1 p.2) := by
  have hc := continuous_stepD3Uniform_variance_spatial (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (continuous_parisiFSecond s β j)
    (continuous_parisiFThird s β j) (abs_parisiFThird_le_six s β j) hm
  exact hc.comp (show Continuous (fun p : ℝ × ℝ => (β ^ 2 * (b - p.1), p.2)) by fun_prop)

noncomputable def hjbSlabGradientTest {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m b c δ t x : ℝ) : ℝ :=
  parisiSlabGradient s β j m b (hjbTimeCap c δ t) x

theorem hjbSlabGradientTest_hasDerivAt_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    HasDerivAt (hjbSlabGradientTest s β j m b c δ t)
      (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x) x :=
  hasDerivAt_parisiSlabGradient_spatial s β j m b _ x

theorem deriv_hjbSlabGradientTest_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    deriv (hjbSlabGradientTest s β j m b c δ t) x =
      parisiSlabHessian s β j m b (hjbTimeCap c δ t) x :=
  (hjbSlabGradientTest_hasDerivAt_spatial s β j m b c δ t x).deriv

theorem deriv_hjbSlabGradientTest_spatial_second {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    deriv (deriv (hjbSlabGradientTest s β j m b c δ t)) x =
      parisiSlabThird s β j m b (hjbTimeCap c δ t) x := by
  rw [show deriv (hjbSlabGradientTest s β j m b c δ t) =
    parisiSlabHessian s β j m b (hjbTimeCap c δ t) from
      funext (deriv_hjbSlabGradientTest_spatial s β j m b c δ t)]
  exact (hasDerivAt_parisiSlabHessian_spatial s β j m b _ x).deriv

theorem hasDerivAt_hjbSlabGradientTest_time {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b) (t x : ℝ) :
    HasDerivAt (fun r => hjbSlabGradientTest s β j m b c δ r x)
      (hjbTimeCapD c δ t * (-(β ^ 2 / 2)) *
        (parisiSlabThird s β j m b (hjbTimeCap c δ t) x +
          2 * m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x *
            parisiSlabHessian s β j m b (hjbTimeCap c δ t) x)) t := by
  have hd := (hasDerivAt_parisiSlabGradient_time s β hβ j hm b x
    ((hjbTimeCap_lt c hδ t).trans_le hb)).comp t (hasDerivAt_hjbTimeCap c hδ t)
  convert! hd using 1
  ring

theorem continuous_hjbSlabGradientTest {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => hjbSlabGradientTest s β j m b c δ p.1 p.2) :=
  (continuous_parisiSlab s β j hm b).2.1.comp
    (((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd)

theorem contDiff_hjbSlabGradientTest_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ t : ℝ) :
    ContDiff ℝ 2 (hjbSlabGradientTest s β j m b c δ t) := by
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) _
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hjbSlabGradientTest_hasDerivAt_spatial s β j m b c δ t x).differentiableAt,
    by simp, ?_⟩
  rw [show deriv (hjbSlabGradientTest s β j m b c δ t) =
    parisiSlabHessian s β j m b (hjbTimeCap c δ t) from
      funext (deriv_hjbSlabGradientTest_spatial s β j m b c δ t), contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_parisiSlabHessian_spatial s β j m b _ x).differentiableAt, ?_⟩
  rw [show deriv (parisiSlabHessian s β j m b (hjbTimeCap c δ t)) =
    parisiSlabThird s β j m b (hjbTimeCap c δ t) from
      funext (fun x => (hasDerivAt_parisiSlabHessian_spatial s β j m b _ x).deriv)]
  exact (continuous_parisiSlabThird s β j hm b).comp (continuous_const.prodMk continuous_id)

theorem continuous_hjbSlabGradientTest_spaceDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) p.1 p.2) := by
  simp only [itoSpaceDerivative, deriv_hjbSlabGradientTest_spatial]
  exact (continuous_parisiSlab s β j hm b).2.2.comp
    (((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd)

theorem continuous_hjbSlabGradientTest_spaceSecondDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) p.1 p.2) := by
  simp only [itoSpaceSecondDerivative, deriv_hjbSlabGradientTest_spatial_second]
  exact (continuous_parisiSlabThird s β j hm b).comp
    (((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd)

theorem continuous_hjbSlabGradientTest_timeDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b) :
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (hjbSlabGradientTest s β j m b c δ) p.1 p.2) := by
  simp only [itoTimeDerivative, (hasDerivAt_hjbSlabGradientTest_time s β hβ j hm b c hδ hb _ _).deriv]
  have hcmap : Continuous (fun p : ℝ × ℝ => (hjbTimeCap c δ p.1, p.2)) :=
    ((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd
  exact (((continuous_hjbTimeCapD c δ).comp continuous_fst).mul continuous_const).mul
    (((continuous_parisiSlabThird s β j hm b).comp hcmap).add
      ((((continuous_parisiSlab s β j hm.1 b).2.1.comp hcmap).const_mul (2 * m)).mul
        ((continuous_parisiSlab s β j hm.1 b).2.2.comp hcmap)))

theorem norm_hjbSlabGradientTest_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ t x : ℝ) :
    ‖hjbSlabGradientTest s β j m b c δ t x‖ ≤ 1 := by
  rw [hjbSlabGradientTest, Real.norm_eq_abs]
  exact abs_parisiSlabGradient_le_one s β j hm b _ x

theorem norm_hjbSlabGradientTest_spaceDerivative_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ t x : ℝ) :
    ‖itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) t x‖ ≤ 1 := by
  simp only [itoSpaceDerivative, deriv_hjbSlabGradientTest_spatial, Real.norm_eq_abs]
  rw [abs_of_nonneg (parisiSlabHessian_pos s β j hm b _ x).le]
  have h := parisiSlabHessian_add_sq_le_one s β j hm b (hjbTimeCap c δ t) x
  nlinarith [sq_nonneg (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x)]

theorem norm_hjbSlabGradientTest_spaceSecondDerivative_le_fourteen {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ t x : ℝ) :
    ‖itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) t x‖ ≤ 14 := by
  simp only [itoSpaceSecondDerivative, deriv_hjbSlabGradientTest_spatial_second, Real.norm_eq_abs]
  exact abs_parisiSlabThird_le_fourteen s β j hm b _ x

/-- On the unchanged portion of the cap the actual gradient PDE cancels
the diffusion term. This isolates precisely the control/CDF error. -/
theorem hjbSlabGradientTest_drift_eq {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b)
    (t x a A : ℝ) (ht : t ≤ c) :
    itoTimeDerivative (hjbSlabGradientTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) t x * (β ^ 2 * a * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) t x * β ^ 2 =
      β ^ 2 * parisiSlabHessian s β j m b t x *
        (a * A - m * parisiSlabGradient s β j m b t x) := by
  simp only [itoTimeDerivative, itoSpaceDerivative, itoSpaceSecondDerivative,
    (hasDerivAt_hjbSlabGradientTest_time s β hβ j hm b c hδ hb t x).deriv,
    deriv_hjbSlabGradientTest_spatial, deriv_hjbSlabGradientTest_spatial_second,
    hjbTimeCap_of_le c δ t ht, hjbTimeCapD, ite_eq_left ht]
  ring

end Paper
