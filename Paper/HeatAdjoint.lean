module

public import Paper.DoobHeat
public import Paper.GaussianPositivity

@[expose] public section

/-! # Self-adjointness of the concrete Gaussian heat operator

The bounded observable and integrable test give absolute integrability on
the product space. Symmetry then supplies the reverse order of integration.
These identities are the spatial adjoint step in distributional heat testing.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

theorem heatSemigroup_eq_kernelAverage (ell : ℝ) (hell : 0 < ell)
    (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    heatSemigroup ell f x = kernelAverage (μ := volume) (heatKernel ell.toNNReal) f x := by
  have hv : ell.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hell).ne'
  rw [kernelAverage_heatKernel_eq_gaussian_integral ell.toNNReal hv f x]
  exact gaussianExpectation_shift_eq_integral x ell hell.le f hf

theorem symmetric_kernel_integrable_adjoint {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] (φ : α → α → ℝ) (g f : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y) (hφmeas : Measurable (fun p : α × α => φ p.1 p.2))
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1) (hsym : ∀ x y, φ x y = φ y x)
    (hg : Integrable g μ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x, g x * kernelAverage (μ := μ) φ f x ∂μ) =
      ∫ x, f x * kernelAverage (μ := μ) φ g x ∂μ := by
  have hc : Integrable (fun p : α × α => φ p.1 p.2 * g p.1 * f p.2) (μ.prod μ) :=
    (kernel_pair_integrable φ g f hφ hφmeas hmass hg hf M hb).2
  have hr : Integrable (fun p : α × α => φ p.1 p.2 * f p.1 * g p.2) (μ.prod μ) := by
    apply hc.swap.congr
    filter_upwards with p
    change φ p.2 p.1 * g p.2 * f p.1 = φ p.1 p.2 * f p.1 * g p.2
    rw [hsym p.2 p.1]
    ring
  rw [← kernel_cross_integral φ g f hc, ← kernel_cross_integral φ f g hr]
  calc
    _ = ∫ p : α × α, φ p.1 p.2 * g p.2 * f p.1 ∂μ.prod μ :=
      (symmetric_kernel_cross_swap φ g f hsym).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      ring

/-- The actual Gaussian heat operator is self-adjoint against Lebesgue
measure, including its variance-zero identity operator. -/
theorem heatSemigroup_adjoint (ell : ℝ) (hell : 0 ≤ ell)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hgi : Integrable g) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x, heatSemigroup ell f x * g x) = ∫ x, f x * heatSemigroup ell g x := by
  rcases eq_or_lt_of_le hell with he | he
  · subst ell
    simp [heatSemigroup, gaussianExpectation]
  · simp_rw [heatSemigroup_eq_kernelAverage ell he f hf,
      heatSemigroup_eq_kernelAverage ell he g hg, mul_comm _ (g _)]
    exact symmetric_kernel_integrable_adjoint (heatKernel ell.toNNReal) g f
      (heatKernel_nonneg _) (measurable_heatKernel _)
      (integral_heatKernel_eq_one _ (Real.toNNReal_pos.mpr he).ne')
      (heatKernel_symm _) hgi hf M hb

theorem integrable_kernelAverage_heatKernel (v : ℝ≥0) (hv : v ≠ 0)
    (g : ℝ → ℝ) (hg : Integrable g) :
    Integrable (kernelAverage (μ := volume) (heatKernel v) g) := by
  have hw := kernel_weight_integrable (heatKernel v) g (heatKernel_nonneg v)
    (measurable_heatKernel v) (integral_heatKernel_eq_one v hv) hg
  have hr : Integrable (fun p : ℝ × ℝ => heatKernel v p.1 p.2 * g p.2)
      (volume.prod volume) := by
    apply hw.swap.congr
    filter_upwards with p
    change heatKernel v p.2 p.1 * g p.2 = heatKernel v p.1 p.2 * g p.2
    rw [heatKernel_symm v p.2 p.1]
  exact hr.integral_prod_left

theorem integral_kernelAverage_heatKernel (v : ℝ≥0) (hv : v ≠ 0)
    (g : ℝ → ℝ) (hg : Integrable g) :
    (∫ x, kernelAverage (μ := volume) (heatKernel v) g x) = ∫ x, g x := by
  have hw := kernel_weight_integrable (heatKernel v) g (heatKernel_nonneg v)
    (measurable_heatKernel v) (integral_heatKernel_eq_one v hv) hg
  have hr : Integrable (fun p : ℝ × ℝ => heatKernel v p.1 p.2 * g p.2)
      (volume.prod volume) := by
    apply hw.swap.congr
    filter_upwards with p
    change heatKernel v p.2 p.1 * g p.2 = heatKernel v p.1 p.2 * g p.2
    rw [heatKernel_symm v p.2 p.1]
  unfold kernelAverage
  rw [← integral_prod _ hr]
  calc
    _ = ∫ p : ℝ × ℝ, heatKernel v p.2 p.1 * g p.1 ∂volume.prod volume := by
      exact (integral_prod_swap (μ := volume) (ν := volume)
        (fun p : ℝ × ℝ => heatKernel v p.1 p.2 * g p.2)).symm
    _ = ∫ p : ℝ × ℝ, heatKernel v p.1 p.2 * g p.1 ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [heatKernel_symm v p.2 p.1]
    _ = _ := by
      rw [integral_prod _ hw]
      simp_rw [integral_mul_const, integral_heatKernel_eq_one v hv, one_mul]

theorem integrable_heatSemigroup_volume (ell : ℝ) (hell : 0 ≤ ell)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) :
    Integrable (heatSemigroup ell g) := by
  rcases eq_or_lt_of_le hell with he | he
  · subst ell
    have heq : heatSemigroup 0 g = g := by
      ext x
      simp [heatSemigroup, gaussianExpectation]
    rwa [heq]
  · have heq : heatSemigroup ell g = kernelAverage (μ := volume) (heatKernel ell.toNNReal) g :=
      funext (heatSemigroup_eq_kernelAverage ell he g hgm)
    rw [heq]
    exact integrable_kernelAverage_heatKernel _ (Real.toNNReal_pos.mpr he).ne' g hg

theorem integral_heatSemigroup_volume (ell : ℝ) (hell : 0 ≤ ell)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) :
    (∫ x, heatSemigroup ell g x) = ∫ x, g x := by
  rcases eq_or_lt_of_le hell with he | he
  · subst ell
    simp [heatSemigroup, gaussianExpectation]
  · simp_rw [heatSemigroup_eq_kernelAverage ell he g hgm]
    exact integral_kernelAverage_heatKernel _ (Real.toNNReal_pos.mpr he).ne' g hg

/-- Absolute spatial integrability is preserved with a contraction bound. -/
theorem integral_norm_heatSemigroup_le (ell : ℝ) (hell : 0 ≤ ell)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) :
    (∫ x, ‖heatSemigroup ell g x‖) ≤ ∫ x, ‖g x‖ := by
  have hm : Measurable (fun x => ‖g x‖) := hgm.norm
  rw [← integral_heatSemigroup_volume ell hell (fun x => ‖g x‖) hm hg.norm]
  apply integral_mono (integrable_heatSemigroup_volume ell hell g hgm hg).norm
    (integrable_heatSemigroup_volume ell hell (fun x => ‖g x‖) hm hg.norm)
  intro x
  exact norm_integral_le_integral_norm _

end Paper
