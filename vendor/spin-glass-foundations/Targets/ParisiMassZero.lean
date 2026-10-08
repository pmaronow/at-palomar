module

/-
# The mass-zero extension of the actual scalar Parisi transform

The apparent singularity at mass zero is the divided difference of a cumulant
generating function. Mathlib's analytic divided-difference theorem gives the
analytic extension, and its CGF derivative formula gives half the variance.
No interchange of a singular quotient and a Gaussian integral is postulated.
-/
public import Targets.ParisiMassDerivative
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The expectation branch at mass zero is exactly the continuous divided
difference of the actual cumulant generating function. -/
theorem parisiStep_eq_dslope_cgf {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    (fun m => parisiStep m v A x) =
      dslope (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) 0 := by
  funext m
  by_cases hm : m = 0
  · subst m
    have hmem : (0 : ℝ) ∈ interior (integrableExpSet
        (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
      rw [parisiStep_integrableExpSet hA hmeas, interior_univ]
      trivial
    simp [parisiStep, deriv_cgf_zero hmem]
  · rw [dslope_of_ne _ hm]
    simp [slope, vsub_eq_sub, cgf, mgf, parisiStep, hm]

/-- Analyticity in the mass includes the actual expectation at zero. -/
theorem analyticAt_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x m : ℝ) :
    AnalyticAt ℝ (fun a => parisiStep a v A x) m := by
  have hmem (a : ℝ) : a ∈ interior (integrableExpSet
      (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
    rw [parisiStep_integrableExpSet hA hmeas, interior_univ]
    trivial
  by_cases hm : m = 0
  · subst m
    rw [parisiStep_eq_dslope_cgf hA hmeas v x]
    obtain ⟨p, hp⟩ := analyticAt_cgf (hmem 0)
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · apply ((analyticAt_cgf (hmem m)).div analyticAt_id hm).congr
    filter_upwards [eventually_ne_nhds hm] with a ha
    simp [parisiStep, ha, cgf, mgf, div_eq_mul_inv, mul_comm]

/-- At zero mass the true mass derivative is half the centered second moment. -/
theorem hasDerivAt_parisiStep_mass_zero {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    HasDerivAt (fun m => parisiStep m v A x)
      ((∫ z, (A (x + Real.sqrt v * z) - parisiStep 0 v A x) ^ 2
        ∂(gaussianReal 0 1)) / 2) 0 := by
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet
      (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
    rw [parisiStep_integrableExpSet hA hmeas, interior_univ]
    trivial
  have H := (analyticAt_cgf hmem).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.deriv
  have Hd : deriv (dslope (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) 0) 0 =
      iteratedDeriv 2 (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) 0 / 2 := by
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using! H
  apply (analyticAt_parisiStep_mass hA hmeas v x 0).differentiableAt.hasDerivAt.congr_deriv
  rw [parisiStep_eq_dslope_cgf hA hmeas v x, Hd, iteratedDeriv_two_cgf_eq_integral hmem]
  simp [deriv_cgf_zero hmem, parisiStep]

/-- The actual scalar transform is differentiable for every real mass. -/
theorem differentiable_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    Differentiable ℝ (fun m => parisiStep m v A x) :=
  fun m => (analyticAt_parisiStep_mass hA hmeas v x m).differentiableAt

/-- The entropy sign and the mass-zero variance formula cover every real mass. -/
theorem deriv_parisiStep_mass_nonneg_all {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x m : ℝ) :
    0 ≤ deriv (fun a => parisiStep a v A x) m := by
  by_cases hm : m = 0
  · subst m
    rw [(hasDerivAt_parisiStep_mass_zero hA hmeas v x).deriv]
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  · exact deriv_parisiStep_mass_nonneg hA hmeas hm v x

/-- Global mass monotonicity includes both sides of zero and zero itself. -/
theorem monotone_parisiStep_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hmeas : Measurable A) (v x : ℝ) :
    Monotone (fun m => parisiStep m v A x) := by
  exact monotone_of_deriv_nonneg (differentiable_parisiStep_mass hA hmeas v x)
    (deriv_parisiStep_mass_nonneg_all hA hmeas v x)

/-- In particular the missing zero-mass case is covered for every actual Parisi input. -/
theorem hasDerivAt_parisiStep_parisiF_mass_zero {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (v x : ℝ) :
    HasDerivAt (fun m => parisiStep m v (parisiF s β j) x)
      ((∫ z, (parisiF s β j (x + Real.sqrt v * z) -
        parisiStep 0 v (parisiF s β j) x) ^ 2 ∂(gaussianReal 0 1)) / 2) 0 :=
  hasDerivAt_parisiStep_mass_zero (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) v x

end SpinGlass.Targets
