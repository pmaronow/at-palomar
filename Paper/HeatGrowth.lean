module

public import Paper.HeatAdjoint
public import Paper.ParisiPDE

@[expose] public section

/-! # Heat adjoints and first moments for linearly growing data

The terminal datum `log cosh` is unbounded.  These estimates justify its
spatial Fubini steps using the first absolute Gaussian moment, rather than
silently imposing a bounded terminal datum.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

theorem integrable_linearGrowth_gaussian (x : ℝ) (v : ℝ≥0)
    (f : ℝ → ℝ) (hf : Measurable f) (A L : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ A + L * ‖y‖) : Integrable f (gaussianReal x v) := by
  have hid : Integrable (fun y : ℝ => y) (gaussianReal x v) :=
    (memLp_id_gaussianReal (μ := x) (v := v) 1).integrable (by norm_num)
  exact ((integrable_const A).add (hid.norm.const_mul L)).mono'
    hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem heatSemigroup_norm_id_le (ell : ℝ) (_hell : 0 ≤ ell) (x : ℝ) :
    heatSemigroup ell (fun y : ℝ => ‖y‖) x ≤
      ‖x‖ + Real.sqrt ell * gaussianAbsMoment := by
  have hi : Integrable (fun z : ℝ => x + Real.sqrt ell * z) (gaussianReal 0 1) :=
    (integrable_const x).add (integrable_standardGaussian_id.const_mul (Real.sqrt ell))
  have henv : Integrable (fun z : ℝ => ‖x‖ + Real.sqrt ell * ‖z‖)
      (gaussianReal 0 1) :=
    (integrable_const ‖x‖).add
      (integrable_standardGaussian_id.norm.const_mul (Real.sqrt ell))
  have hle := integral_mono hi.norm henv (fun z => by
    calc
      ‖x + Real.sqrt ell * z‖ ≤ ‖x‖ + ‖Real.sqrt ell * z‖ := norm_add_le _ _
      _ = ‖x‖ + Real.sqrt ell * ‖z‖ := by
        rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg ell)])
  rw [integral_add (integrable_const ‖x‖)
    (integrable_standardGaussian_id.norm.const_mul (Real.sqrt ell)),
    integral_const_mul] at hle
  simpa only [heatSemigroup, gaussianAbsMoment, gaussianExpectation,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using hle

theorem heatKernel_linearGrowth_integrable (ell : ℝ) (hell : 0 < ell)
    (g f : ℝ → ℝ) (hg : Integrable g)
    (hgw : Integrable (fun x : ℝ => ‖x‖ * ‖g x‖))
    (hf : Measurable f) (A L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x, ‖f x‖ ≤ A + L * ‖x‖) :
    Integrable (fun p : ℝ × ℝ =>
      heatKernel ell.toNNReal p.1 p.2 * g p.1 * f p.2) (volume.prod volume) := by
  have hv : ell.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hell).ne'
  have hrow (x : ℝ) : Integrable (fun y => heatKernel ell.toNNReal x y * f y) := by
    simpa only [heatKernel_eq_gaussianPDFReal] using
      integrable_gaussian_density_mul x ell.toNNReal hv f
        (integrable_linearGrowth_gaussian x ell.toNNReal f hf A L hb)
  have hrowNorm (x : ℝ) : Integrable (fun y => heatKernel ell.toNNReal x y * ‖y‖) := by
    simpa only [heatKernel_eq_gaussianPDFReal] using
      integrable_gaussian_density_mul x ell.toNNReal hv (fun y : ℝ => ‖y‖)
        ((memLp_id_gaussianReal (μ := x) (v := ell.toNNReal) 1).integrable
          (by norm_num)).norm
  have hrowOne (x : ℝ) : Integrable (heatKernel ell.toNNReal x) :=
    by
      change Integrable (fun y => heatKernel ell.toNNReal x y)
      simp_rw [heatKernel_eq_gaussianPDFReal]
      exact integrable_gaussianPDFReal x ell.toNNReal
  have hbound (x : ℝ) :
      (∫ y, ‖heatKernel ell.toNNReal x y * g x * f y‖) ≤
        ‖g x‖ * (A + L * (‖x‖ + Real.sqrt ell * gaussianAbsMoment)) := by
    calc
      _ = ‖g x‖ * ∫ y, heatKernel ell.toNNReal x y * ‖f y‖ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (heatKernel_nonneg _ _ _)]
        ring
      _ ≤ ‖g x‖ * ∫ y, heatKernel ell.toNNReal x y * (A + L * ‖y‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply integral_mono
        · simpa only [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg _ _ _)] using
            (hrow x).norm
        · exact ((hrowOne x).mul_const A).add ((hrowNorm x).const_mul L) |>.congr
            (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
        · intro y
          exact mul_le_mul_of_nonneg_left (hb y) (heatKernel_nonneg _ _ _)
      _ = ‖g x‖ * (A + L * heatSemigroup ell (fun y : ℝ => ‖y‖) x) := by
        rw [heatSemigroup_eq_kernelAverage ell hell (fun y : ℝ => ‖y‖)
          (by fun_prop)]
        unfold kernelAverage
        simp_rw [mul_add, mul_left_comm _ L, integral_add
          ((hrowOne x).mul_const A) ((hrowNorm x).const_mul L),
          integral_mul_const, integral_const_mul, integral_heatKernel_eq_one _ hv, one_mul]
        ring
      _ ≤ _ := by
        gcongr
        exact heatSemigroup_norm_id_le ell hell.le x
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      heatKernel ell.toNNReal p.1 p.2 * g p.1 * f p.2) (volume.prod volume) :=
    (((measurable_heatKernel _).aestronglyMeasurable.mul
      hg.aestronglyMeasurable.comp_fst).mul (hf.comp measurable_snd).aestronglyMeasurable)
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards with x
    exact ((hrow x).mul_const (g x)).congr
      (Filter.Eventually.of_forall fun y => by ring)
  · have henv : Integrable (fun x : ℝ =>
        ‖g x‖ * (A + L * (‖x‖ + Real.sqrt ell * gaussianAbsMoment))) := by
      convert (hg.norm.const_mul (A + L * Real.sqrt ell * gaussianAbsMoment)).add
        (hgw.const_mul L) using 1
      ext x
      simp only [Pi.add_apply]
      ring
    apply henv.mono' hm.norm.integral_prod_right'
    filter_upwards with x
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using
      hbound x

/-- Self-adjointness with the linear-growth datum justified by the test's
first absolute moment. -/
theorem heatSemigroup_adjoint_linearGrowth (ell : ℝ) (hell : 0 ≤ ell)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hgi : Integrable g) (hgw : Integrable (fun x : ℝ => ‖x‖ * ‖g x‖))
    (A L : ℝ) (hL : 0 ≤ L) (hb : ∀ x, ‖f x‖ ≤ A + L * ‖x‖) :
    (∫ x, heatSemigroup ell f x * g x) = ∫ x, f x * heatSemigroup ell g x := by
  rcases eq_or_lt_of_le hell with he | he
  · subst ell
    simp [heatSemigroup, gaussianExpectation]
  · have hc := heatKernel_linearGrowth_integrable ell he g f hgi hgw hf A L hL hb
    have hr : Integrable (fun p : ℝ × ℝ =>
        heatKernel ell.toNNReal p.1 p.2 * f p.1 * g p.2) (volume.prod volume) := by
      apply hc.swap.congr
      filter_upwards with p
      change heatKernel ell.toNNReal p.2 p.1 * g p.2 * f p.1 = _
      rw [heatKernel_symm _ p.2 p.1]
      ring
    simp_rw [heatSemigroup_eq_kernelAverage ell he f hf,
      heatSemigroup_eq_kernelAverage ell he g hg, mul_comm _ (g _)]
    rw [← kernel_cross_integral _ g f hc, ← kernel_cross_integral _ f g hr]
    calc
      _ = ∫ p : ℝ × ℝ, heatKernel ell.toNNReal p.1 p.2 * g p.2 * f p.1
          ∂volume.prod volume :=
        (symmetric_kernel_cross_swap _ g f (heatKernel_symm _)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with p
        ring

/-- Heat convolution preserves first absolute spatial moments. -/
theorem heatSemigroup_firstMoment (ell : ℝ) (hell : 0 ≤ ell)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hgw : Integrable (fun x : ℝ => ‖x‖ * ‖g x‖)) :
    Integrable (fun x : ℝ => ‖x‖ * heatSemigroup ell g x) ∧
      (∫ x : ℝ, ‖x‖ * ‖heatSemigroup ell g x‖) ≤
        (∫ x : ℝ, ‖x‖ * ‖g x‖) +
          Real.sqrt ell * gaussianAbsMoment * (∫ x : ℝ, ‖g x‖) := by
  rcases eq_or_lt_of_le hell with he | he
  · subst ell
    have hi : Integrable (fun x : ℝ => ‖x‖ * g x) := by
      apply hgw.mono' (continuous_norm.measurable.aestronglyMeasurable.mul
        hgm.aestronglyMeasurable)
      filter_upwards with x
      change ‖‖x‖ * g x‖ ≤ ‖x‖ * ‖g x‖
      simp only [norm_mul, norm_norm, le_refl]
    simpa [heatSemigroup, gaussianExpectation] using And.intro hi (le_refl
      (∫ x : ℝ, ‖x‖ * ‖g x‖))
  · have hc := heatKernel_linearGrowth_integrable ell he g (fun y : ℝ => ‖y‖)
      hg hgw (by fun_prop) 0 1 (by norm_num) (fun y => by simp)
    have hs : Integrable (fun p : ℝ × ℝ =>
        heatKernel ell.toNNReal p.1 p.2 * ‖p.1‖ * g p.2) (volume.prod volume) := by
      apply hc.swap.congr
      filter_upwards with p
      change heatKernel ell.toNNReal p.2 p.1 * g p.2 * ‖p.1‖ = _
      rw [heatKernel_symm _ p.2 p.1]
      ring
    have hi : Integrable (fun x : ℝ => ‖x‖ * heatSemigroup ell g x) := by
      apply hs.integral_prod_left.congr
      filter_upwards with x
      rw [heatSemigroup_eq_kernelAverage ell he g hgm]
      unfold kernelAverage
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    have hcn : Integrable (fun p : ℝ × ℝ =>
        heatKernel ell.toNNReal p.1 p.2 * ‖g p.1‖ * ‖p.2‖)
        (volume.prod volume) := by
      simpa only [norm_mul, norm_norm,
        Real.norm_of_nonneg (heatKernel_nonneg _ _ _)] using hc.norm
    have henv : Integrable (fun x : ℝ =>
        ‖g x‖ * (‖x‖ + Real.sqrt ell * gaussianAbsMoment)) := by
      convert hgw.add (hg.norm.mul_const (Real.sqrt ell * gaussianAbsMoment)) using 1
      ext x
      simp only [Pi.add_apply]
      ring
    have hk : Integrable (fun x : ℝ => ‖g x‖ *
        kernelAverage (μ := volume) (heatKernel ell.toNNReal) (fun y : ℝ => ‖y‖) x) := by
      apply hcn.integral_prod_left.congr
      filter_upwards with x
      unfold kernelAverage
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    refine ⟨hi, ?_⟩
    calc
      (∫ x : ℝ, ‖x‖ * ‖heatSemigroup ell g x‖) =
          ∫ x : ℝ, ‖‖x‖ * heatSemigroup ell g x‖ := by
        simp only [norm_mul, norm_norm]
      _ ≤ ∫ x : ℝ, ∫ y : ℝ,
          ‖heatKernel ell.toNNReal x y * ‖x‖ * g y‖ := by
        apply integral_mono hi.norm hs.integral_norm_prod_left
        intro x
        change ‖‖x‖ * heatSemigroup ell g x‖ ≤
          ∫ y : ℝ, ‖heatKernel ell.toNNReal x y * ‖x‖ * g y‖
        rw [heatSemigroup_eq_kernelAverage ell he g hgm]
        unfold kernelAverage
        rw [← integral_const_mul]
        convert norm_integral_le_integral_norm
          (fun y => heatKernel ell.toNNReal x y * ‖x‖ * g y) using 1
        congr 1
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ = ∫ p : ℝ × ℝ, ‖heatKernel ell.toNNReal p.1 p.2 * ‖p.1‖ * g p.2‖
          ∂volume.prod volume := (integral_prod _ hs.norm).symm
      _ = ∫ p : ℝ × ℝ, heatKernel ell.toNNReal p.1 p.2 * ‖g p.1‖ * ‖p.2‖
          ∂volume.prod volume := by
        rw [← integral_prod_swap]
        apply integral_congr_ae
        filter_upwards with p
        simp only [Prod.swap, norm_mul, norm_norm,
          Real.norm_of_nonneg (heatKernel_nonneg _ _ _)]
        rw [heatKernel_symm _ p.2 p.1]
        ring
      _ = ∫ x : ℝ, ‖g x‖ * kernelAverage (μ := volume)
          (heatKernel ell.toNNReal) (fun y : ℝ => ‖y‖) x :=
        kernel_cross_integral (μ := volume) (heatKernel ell.toNNReal)
          (fun x : ℝ => ‖g x‖) (fun y : ℝ => ‖y‖) hcn
      _ ≤ ∫ x : ℝ, ‖g x‖ * (‖x‖ + Real.sqrt ell * gaussianAbsMoment) := by
        apply integral_mono hk henv
        intro x
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [← heatSemigroup_eq_kernelAverage ell he (fun y : ℝ => ‖y‖) (by fun_prop)]
        exact heatSemigroup_norm_id_le ell he.le x
      _ = _ := by
        calc
          _ = ∫ x : ℝ, ‖x‖ * ‖g x‖ +
              (Real.sqrt ell * gaussianAbsMoment) * ‖g x‖ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = _ := by
            rw [integral_add hgw (hg.norm.const_mul _), integral_const_mul]

end Paper
