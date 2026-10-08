module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Determining finite real measures from their cosine and sine integrals. -/
noncomputable section
open MeasureTheory
namespace Paper

theorem integrable_fourier_exponential (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ξ * x : ℝ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · fun_prop
  · filter_upwards [] with x
    exact (Complex.norm_exp_ofReal_mul_I (ξ * x)).le

/-- Finite real measures are determined by their cosine and sine integrals. -/
theorem measure_eq_of_cos_sin_integrals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : ∀ ξ : ℝ, (∫ x, Real.cos (ξ * x) ∂μ) = ∫ x, Real.cos (ξ * x) ∂ν)
    (hs : ∀ ξ : ℝ, (∫ x, Real.sin (ξ * x) ∂μ) = ∫ x, Real.sin (ξ * x) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext ξ
  apply Complex.ext
  · have hμ := integral_re (integrable_fourier_exponential μ ξ)
    have hν := integral_re (integrable_fourier_exponential ν ξ)
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).re ∂μ) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂μ).re at hμ
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).re ∂ν) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂ν).re at hν
    simp only [Complex.exp_ofReal_mul_I_re] at hμ hν
    rw [charFun_apply_real, charFun_apply_real]
    simpa only [← Complex.ofReal_mul] using hμ.symm.trans ((hc ξ).trans hν)
  · have hμ := integral_im (integrable_fourier_exponential μ ξ)
    have hν := integral_im (integrable_fourier_exponential ν ξ)
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).im ∂μ) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂μ).im at hμ
    change (∫ x, (Complex.exp ((ξ * x : ℝ) * Complex.I)).im ∂ν) =
      (∫ x, Complex.exp ((ξ * x : ℝ) * Complex.I) ∂ν).im at hν
    simp only [Complex.exp_ofReal_mul_I_im] at hμ hν
    rw [charFun_apply_real, charFun_apply_real]
    simpa only [← Complex.ofReal_mul] using hμ.symm.trans ((hs ξ).trans hν)

end Paper
