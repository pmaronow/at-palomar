module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Symmetric Markov kernels and the contraction in Proposition 5.5

This file proves the paper's double-integral identity for genuine Bochner
integrals. It separates the universal measure-theoretic step from the analytic
verification that the Gaussian kernel and the paper's functions satisfy the
hypotheses. Product integrability is explicit, rather than implicit in a
formal use of Fubini's theorem.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Paper

section Kernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- Integration against a real-valued kernel. -/
def kernelAverage (φ : α → α → ℝ) (k : α → ℝ) (x : α) : ℝ :=
  ∫ y, φ x y * k y ∂μ

/-- The diagonal term collapses because each row of the kernel has mass one. -/
theorem kernel_diagonal_integral
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hdiag : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ)) :
    (∫ z : α × α, φ z.1 z.2 * w z.1 * k z.1 ∂μ.prod μ) =
      ∫ x, w x * k x ∂μ := by
  rw [integral_prod _ hdiag]
  simp_rw [mul_assoc, integral_mul_const, hmass, one_mul]

/-- Fubini identifies the cross term with the kernel average. -/
theorem kernel_cross_integral
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ)) :
    (∫ z : α × α, φ z.1 z.2 * w z.1 * k z.2 ∂μ.prod μ) =
      ∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ := by
  rw [integral_prod _ hcross]
  apply integral_congr_ae
  filter_upwards with x
  calc
    (∫ y, φ x y * w x * k y ∂μ) = ∫ y, w x * (φ x y * k y) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = w x * kernelAverage (μ := μ) φ k x := by
      rw [integral_const_mul]
      rfl

/-- Swapping coordinates preserves the cross-term integral of a symmetric kernel. -/
theorem symmetric_kernel_cross_swap
    (φ : α → α → ℝ) (w k : α → ℝ) (hsym : ∀ x y, φ x y = φ y x) :
    (∫ z : α × α, φ z.1 z.2 * w z.2 * k z.1 ∂μ.prod μ) =
      ∫ z : α × α, φ z.1 z.2 * w z.1 * k z.2 ∂μ.prod μ := by
  calc
    _ = ∫ z : α × α,
        (fun p : α × α => φ p.1 p.2 * w p.1 * k p.2) z.swap ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with z
      change φ z.1 z.2 * w z.2 * k z.1 = φ z.2 z.1 * w z.2 * k z.1
      rw [hsym z.1 z.2]
    _ = _ := integral_prod_swap (μ := μ) (ν := μ)
      (fun p : α × α => φ p.1 p.2 * w p.1 * k p.2)

/-- Swapping coordinates preserves the diagonal-term integral of a symmetric kernel. -/
theorem symmetric_kernel_diagonal_swap
    (φ : α → α → ℝ) (w k : α → ℝ) (hsym : ∀ x y, φ x y = φ y x) :
    (∫ z : α × α, φ z.1 z.2 * w z.2 * k z.2 ∂μ.prod μ) =
      ∫ z : α × α, φ z.1 z.2 * w z.1 * k z.1 ∂μ.prod μ := by
  calc
    _ = ∫ z : α × α,
        (fun p : α × α => φ p.1 p.2 * w p.1 * k p.1) z.swap ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with z
      change φ z.1 z.2 * w z.2 * k z.2 = φ z.2 z.1 * w z.2 * k z.2
      rw [hsym z.1 z.2]
    _ = _ := integral_prod_swap (μ := μ) (ν := μ)
      (fun p : α × α => φ p.1 p.2 * w p.1 * k p.1)

/-- The exact symmetrized double-integral identity used in Proposition 5.5.

Only two product integrability hypotheses are needed: symmetry supplies the
other two terms in the expansion. -/
theorem symmetric_kernel_difference_identity
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hsym : ∀ x y, φ x y = φ y x)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hdiag : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ))
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ)) :
    (∫ x, w x * k x ∂μ) - (∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ) =
      (1 / 2 : ℝ) * ∫ z : α × α,
        φ z.1 z.2 * (w z.1 - w z.2) * (k z.1 - k z.2) ∂μ.prod μ := by
  have hdiag' : Integrable
      (fun z : α × α => φ z.1 z.2 * w z.2 * k z.2) (μ.prod μ) := by
    convert hdiag.swap using 1
    ext z
    change φ z.1 z.2 * w z.2 * k z.2 = φ z.2 z.1 * w z.2 * k z.2
    rw [hsym z.1 z.2]
  have hcross' : Integrable
      (fun z : α × α => φ z.1 z.2 * w z.2 * k z.1) (μ.prod μ) := by
    convert hcross.swap using 1
    ext z
    change φ z.1 z.2 * w z.2 * k z.1 = φ z.2 z.1 * w z.2 * k z.1
    rw [hsym z.1 z.2]
  have hexpand :
      (fun z : α × α => φ z.1 z.2 * (w z.1 - w z.2) * (k z.1 - k z.2)) =
      ((fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) -
        (fun z => φ z.1 z.2 * w z.1 * k z.2) -
        (fun z => φ z.1 z.2 * w z.2 * k z.1) +
        (fun z => φ z.1 z.2 * w z.2 * k z.2)) := by
    ext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hexpand, integral_add' ((hdiag.sub hcross).sub hcross') hdiag',
    integral_sub' (hdiag.sub hcross) hcross', integral_sub' hdiag hcross,
    symmetric_kernel_cross_swap φ w k hsym,
    symmetric_kernel_diagonal_swap φ w k hsym,
    kernel_diagonal_integral φ w k hmass hdiag,
    kernel_cross_integral φ w k hcross]
  ring

/-- The double-difference integrand is integrable whenever the two basic
terms in the symmetric identity are integrable. -/
theorem symmetric_kernel_difference_integrable
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hsym : ∀ x y, φ x y = φ y x)
    (hdiag : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ))
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ)) :
    Integrable (fun z : α × α =>
      φ z.1 z.2 * (w z.1 - w z.2) * (k z.1 - k z.2)) (μ.prod μ) := by
  have hdiag' : Integrable
      (fun z : α × α => φ z.1 z.2 * w z.2 * k z.2) (μ.prod μ) := by
    convert hdiag.swap using 1
    ext z
    change φ z.1 z.2 * w z.2 * k z.2 = φ z.2 z.1 * w z.2 * k z.2
    rw [hsym z.1 z.2]
  have hcross' : Integrable
      (fun z : α × α => φ z.1 z.2 * w z.2 * k z.1) (μ.prod μ) := by
    convert hcross.swap using 1
    ext z
    change φ z.1 z.2 * w z.2 * k z.1 = φ z.2 z.1 * w z.2 * k z.1
    rw [hsym z.1 z.2]
  convert ((hdiag.sub hcross).sub hcross').add hdiag' using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The same Fubini identity in the paper's iterated-integral notation. -/
theorem symmetric_kernel_double_integral_identity
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hsym : ∀ x y, φ x y = φ y x)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hdiag : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ))
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ)) :
    (∫ x, w x * k x ∂μ) - (∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y,
        φ x y * (w x - w y) * (k x - k y) ∂μ ∂μ := by
  rw [← integral_prod _ (symmetric_kernel_difference_integrable φ w k hsym hdiag hcross)]
  exact symmetric_kernel_difference_identity φ w k hsym hmass hdiag hcross

/-- A nonnegative symmetric Markov kernel contracts the pairing of two
co-monotone functions. This is the measure-theoretic core of Proposition 5.5. -/
theorem symmetric_kernel_contraction
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y)
    (hsym : ∀ x y, φ x y = φ y x)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hdiag : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ))
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ))
    (hco : ∀ x y, 0 ≤ (w x - w y) * (k x - k y)) :
    (∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ) ≤ ∫ x, w x * k x ∂μ := by
  have hdiff := symmetric_kernel_difference_identity φ w k hsym hmass hdiag hcross
  have hnonneg : 0 ≤ ∫ z : α × α,
      φ z.1 z.2 * (w z.1 - w z.2) * (k z.1 - k z.2) ∂μ.prod μ := by
    apply integral_nonneg
    intro z
    change 0 ≤ φ z.1 z.2 * (w z.1 - w z.2) * (k z.1 - k z.2)
    rw [mul_assoc]
    exact mul_nonneg (hφ z.1 z.2) (hco z.1 z.2)
  linarith

/-- A normalized nonnegative measurable kernel transports an integrable weight
into an integrable function on the product space. The normalization itself
forces integrability of every kernel row. -/
theorem kernel_weight_integrable
    (φ : α → α → ℝ) (w : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y)
    (hφmeas : Measurable (fun z : α × α => φ z.1 z.2))
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hw : Integrable w μ) :
    Integrable (fun z : α × α => φ z.1 z.2 * w z.1) (μ.prod μ) := by
  have hrow (x : α) : Integrable (φ x) μ := by
    by_contra h
    have hzero := integral_undef h
    have hone := hmass x
    rw [hzero] at hone
    norm_num at hone
  apply (integrable_prod_iff
    (hφmeas.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_fst)).2
  constructor
  · filter_upwards with x
    exact (hrow x).mul_const (w x)
  · convert hw.norm using 1
    ext x
    calc
      (∫ y, ‖φ x y * w x‖ ∂μ) = ∫ y, φ x y * ‖w x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [norm_mul, Real.norm_of_nonneg (hφ x y)]
      _ = ‖w x‖ := by rw [integral_mul_const, hmass, one_mul]

/-- The paper's absolute convergence assertion: an integrable weight and a
bounded measurable test function make both terms of Fubini's identity
integrable. -/
theorem kernel_pair_integrable
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y)
    (hφmeas : Measurable (fun z : α × α => φ z.1 z.2))
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hw : Integrable w μ) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C) :
    Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.1) (μ.prod μ) ∧
      Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ) := by
  have hweight := kernel_weight_integrable φ w hφ hφmeas hmass hw
  constructor
  · exact hweight.mul_bdd (hk.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hbound z.1)
  · exact hweight.mul_bdd (hk.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hbound z.2)

/-- Contraction with the analytic assumptions in the paper: the weight is
integrable and the test function is bounded and measurable. -/
theorem symmetric_kernel_contraction_of_integrable_bounded
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y)
    (hφmeas : Measurable (fun z : α × α => φ z.1 z.2))
    (hsym : ∀ x y, φ x y = φ y x)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hw : Integrable w μ) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C)
    (hco : ∀ x y, 0 ≤ (w x - w y) * (k x - k y)) :
    (∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ) ≤ ∫ x, w x * k x ∂μ := by
  obtain ⟨hdiag, hcross⟩ := kernel_pair_integrable φ w k hφ hφmeas hmass hw hk C hbound
  exact symmetric_kernel_contraction φ w k hφ hsym hmass hdiag hcross hco

/-- Multiplying the contraction by the positive Doob-transform factor
produces the exponential decay estimate used in equation (5.10). -/
theorem symmetric_kernel_exponential_decay
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hφ : ∀ x y, 0 ≤ φ x y)
    (hφmeas : Measurable (fun z : α × α => φ z.1 z.2))
    (hsym : ∀ x y, φ x y = φ y x)
    (hmass : ∀ x, ∫ y, φ x y ∂μ = 1)
    (hw : Integrable w μ) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C)
    (hco : ∀ x y, 0 ≤ (w x - w y) * (k x - k y)) (lam : ℝ) :
    Real.exp (-lam / 2) * (∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ) ≤
      Real.exp (-lam / 2) * (∫ x, w x * k x ∂μ) := by
  exact mul_le_mul_of_nonneg_left
    (symmetric_kernel_contraction_of_integrable_bounded φ w k hφ hφmeas hsym hmass
      hw hk C hbound hco) (Real.exp_pos _).le

end Kernel

section Gaussian

open ProbabilityTheory

/-- The Gaussian heat kernel with variance `v`. The Markov normalization is
valid for `v ≠ 0`; the paper handles time zero separately. -/
def heatKernel (v : ℝ≥0) (x y : ℝ) : ℝ :=
  gaussianPDFReal 0 v (x - y)

/-- The centered difference form equals the Gaussian density with mean `x`. -/
theorem heatKernel_eq_gaussianPDFReal (v : ℝ≥0) (x y : ℝ) :
    heatKernel v x y = gaussianPDFReal x v y := by
  unfold heatKernel gaussianPDFReal
  simp only [sub_zero]
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

/-- The Gaussian heat kernel is nonnegative. -/
theorem heatKernel_nonneg (v : ℝ≥0) (x y : ℝ) : 0 ≤ heatKernel v x y :=
  gaussianPDFReal_nonneg 0 v (x - y)

/-- Joint measurability of the Gaussian heat kernel. -/
theorem measurable_heatKernel (v : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => heatKernel v z.1 z.2) :=
  (measurable_gaussianPDFReal 0 v).comp (measurable_fst.sub measurable_snd)

/-- Symmetry of the Gaussian heat kernel. -/
theorem heatKernel_symm (v : ℝ≥0) (x y : ℝ) :
    heatKernel v x y = heatKernel v y x := by
  unfold heatKernel gaussianPDFReal
  simp only [sub_zero]
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]

/-- Each positive-variance Gaussian heat-kernel row integrates to one. -/
theorem integral_heatKernel_eq_one (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    (∫ y, heatKernel v x y) = 1 := by
  simp_rw [heatKernel_eq_gaussianPDFReal]
  exact integral_gaussianPDFReal_eq_one x hv

/-- The paper's exact Gaussian double-integral identity, with absolute
convergence proved from the stated integrability and boundedness assumptions. -/
theorem gaussian_heat_double_integral_identity
    (v : ℝ≥0) (hv : v ≠ 0) (w k : ℝ → ℝ)
    (hw : Integrable w) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C) :
    (∫ x, w x * k x) - (∫ x, w x * kernelAverage (μ := volume) (heatKernel v) k x) =
      (1 / 2 : ℝ) * ∫ x, ∫ y,
        gaussianPDFReal 0 v (x - y) * (w x - w y) * (k x - k y) := by
  obtain ⟨hdiag, hcross⟩ := kernel_pair_integrable (μ := volume) (heatKernel v) w k
    (heatKernel_nonneg v) (measurable_heatKernel v) (integral_heatKernel_eq_one v hv)
    hw hk C hbound
  exact symmetric_kernel_double_integral_identity (heatKernel v) w k
    (heatKernel_symm v) (integral_heatKernel_eq_one v hv) hdiag hcross

/-- Gaussian heat convolution contracts an integrable weight paired with a
bounded measurable co-monotone function. -/
theorem gaussian_heat_contraction
    (v : ℝ≥0) (hv : v ≠ 0) (w k : ℝ → ℝ)
    (hw : Integrable w) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C)
    (hco : ∀ x y, 0 ≤ (w x - w y) * (k x - k y)) :
    (∫ x, w x * kernelAverage (μ := volume) (heatKernel v) k x) ≤ ∫ x, w x * k x := by
  exact symmetric_kernel_contraction_of_integrable_bounded (heatKernel v) w k
    (heatKernel_nonneg v) (measurable_heatKernel v) (heatKernel_symm v)
    (integral_heatKernel_eq_one v hv) hw hk C hbound hco

/-- The Gaussian heat-convolution estimate including the exact exponential
factor of the paper's Doob transform. -/
theorem gaussian_heat_exponential_decay
    (v : ℝ≥0) (hv : v ≠ 0) (w k : ℝ → ℝ)
    (hw : Integrable w) (hk : Measurable k)
    (C : ℝ) (hbound : ∀ x, ‖k x‖ ≤ C)
    (hco : ∀ x y, 0 ≤ (w x - w y) * (k x - k y)) :
    Real.exp (-(v : ℝ) / 2) *
        (∫ x, w x * kernelAverage (μ := volume) (heatKernel v) k x) ≤
      Real.exp (-(v : ℝ) / 2) * (∫ x, w x * k x) := by
  exact mul_le_mul_of_nonneg_left (gaussian_heat_contraction v hv w k hw hk C hbound hco)
    (Real.exp_pos _).le

end Gaussian

/-- Two functions decreasing with absolute value are co-monotone on the whole
real line. In the paper, these are the even functions `w` and `sech³`. -/
theorem comonotone_of_decreasing_abs
    (w k : ℝ → ℝ)
    (hw : ∀ x y, |x| ≤ |y| → w y ≤ w x)
    (hk : ∀ x y, |x| ≤ |y| → k y ≤ k x) :
    ∀ x y, 0 ≤ (w x - w y) * (k x - k y) := by
  intro x y
  rcases le_total |x| |y| with h | h
  · exact mul_nonneg (sub_nonneg.mpr (hw x y h)) (sub_nonneg.mpr (hk x y h))
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (hw y x h)) (sub_nonpos.mpr (hk y x h))

end Paper
