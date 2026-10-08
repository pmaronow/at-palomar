module

public import Paper.Gaussian
public import Paper.Variational
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Concrete Parisi measures and replica-symmetric functional

`ParisiMeasure` is the actual type of probability measures on `[0,1]`.
The functional is parameterized by a potential `u`; this file does not claim
that an arbitrary supplied potential is the weak Parisi PDE solution.
-/

open Set MeasureTheory

namespace Paper

abbrev Overlap := Set.Icc (0 : ℝ) 1
abbrev ParisiMeasure := ProbabilityMeasure Overlap

/-- The replica-symmetric measure supported at the real overlap `q`. -/
noncomputable def diracOverlap (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) : ParisiMeasure :=
  (Measure.dirac (⟨q, hq⟩ : Overlap)).toProbabilityMeasure

/-- The real cumulative mass of a probability measure on `[0,1]`. -/
noncomputable def parisiCDF (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ((μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s}).toReal

theorem parisiCDF_nonneg (μ : ParisiMeasure) (s : ℝ) : 0 ≤ parisiCDF μ s :=
  ENNReal.toReal_nonneg

/-- The cumulative masses are monotone because the threshold sets are nested. -/
theorem parisiCDF_monotone (μ : ParisiMeasure) : Monotone (parisiCDF μ) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) _)
  exact measure_mono (fun x hx => hx.trans hst)

/-- Probability mass bounds the CDF by one. -/
theorem parisiCDF_le_one (μ : ParisiMeasure) (s : ℝ) : parisiCDF μ s ≤ 1 := by
  have hle : (μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s} ≤ 1 := by
    calc
      (μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s} ≤ (μ : Measure Overlap) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  simpa only [parisiCDF, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle

/-- The correction integrand is genuinely integrable for every Parisi measure. -/
theorem parisiCorrection_intervalIntegrable (μ : ParisiMeasure) (a b : ℝ) :
    IntervalIntegrable (fun s => s * parisiCDF μ s) volume a b := by
  have hc : IntervalIntegrable (parisiCDF μ) volume a b :=
    (parisiCDF_monotone μ).intervalIntegrable
  simpa only [id_eq, mul_comm] using hc.mul_continuousOn (continuous_id.continuousOn)

@[simp] theorem parisiCDF_dirac (q s : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    parisiCDF (diracOverlap q hq) s = if q ≤ s then 1 else 0 := by
  by_cases hqs : q ≤ s
  · simp [parisiCDF, diracOverlap, hqs]
  · simp [parisiCDF, diracOverlap, hqs]

/-- The actual topological support of the replica-symmetric probability measure. -/
theorem support_diracOverlap (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    ((diracOverlap q hq : ParisiMeasure) : Measure Overlap).support =
      {⟨q, hq⟩} := by
  change (Measure.dirac (⟨q, hq⟩ : Overlap)).support = {⟨q, hq⟩}
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_singleton
    exact (mem_ae_dirac_iff (measurableSet_singleton _)).mpr (by simp)
  · intro x hx
    have heq : x = (⟨q, hq⟩ : Overlap) := Set.mem_singleton_iff.mp hx
    subst x
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    norm_num

/-- The actual Parisi functional of the supplied potential family. -/
noncomputable def parisiFunctional (β h : ℝ) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (μ : ParisiMeasure) : ℝ :=
  Real.log 2 + u μ 0 h - β ^ 2 / 2 * ∫ s in 0..1, s * parisiCDF μ s

/-- The CDF correction for a Dirac measure is the integral from `q` to `1`. -/
theorem dirac_cdf_integral {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, s * parisiCDF (diracOverlap q hq) s) = (1 - q ^ 2) / 2 := by
  let f : ℝ → ℝ := fun s => s * parisiCDF (diracOverlap q hq) s
  have heq0 : EqOn f (fun _ => (0 : ℝ)) (uIoo 0 q) := by
    intro s hs
    rw [uIoo_of_le hq.1] at hs
    simp [f, parisiCDF_dirac, not_le_of_gt hs.2]
  have heq1 : EqOn f (fun s => s) (uIoo q 1) := by
    intro s hs
    rw [uIoo_of_le hq.2] at hs
    simp [f, parisiCDF_dirac, hs.1.le]
  have hInt0 : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_congr_uIoo heq0).mpr intervalIntegrable_const
  have hInt1 : IntervalIntegrable f volume q 1 :=
    (intervalIntegrable_congr_uIoo heq1).mpr (continuous_id.intervalIntegrable q 1)
  have h0 : (∫ s in (0 : ℝ)..q, f s) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo heq0]
    simp
  have h1 : (∫ s in q..(1 : ℝ), f s) = (1 - q ^ 2) / 2 := by
    rw [intervalIntegral.integral_congr_uIoo heq1, integral_id]
    norm_num
  have hadd := intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1
  change (∫ s in (0 : ℝ)..1, f s) = (1 - q ^ 2) / 2
  rw [h0, h1, zero_add] at hadd
  exact hadd.symm

/-- Exact value of the correction term in the Parisi functional for `δ_q`. -/
theorem dirac_correction_integral {β q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    β ^ 2 / 2 * (∫ s in (0 : ℝ)..1, s * parisiCDF (diracOverlap q hq) s) =
      β ^ 2 / 4 * (1 - q ^ 2) := by
  rw [dirac_cdf_integral hq]
  ring

/-- Explicit hard-side potential; identifying it with a weak solution would
require the separate PDE existence/uniqueness argument. -/
noncomputable def rsHardPotential (β t x : ℝ) : ℝ :=
  β ^ 2 / 2 * (1 - t) + Real.log (Real.cosh x)

/-- Explicit soft-side Gaussian potential. -/
noncomputable def rsSoftPotential (β q t x : ℝ) : ℝ :=
  β ^ 2 / 2 * (1 - q) + gaussianExpectation
    (fun z => Real.log (Real.cosh (x + β * Real.sqrt (q - t) * z)))

/-- The Gaussian expectation in the soft explicit formula is integrable. -/
theorem rsSoftPotential_integrable (β q t x : ℝ) :
    Integrable (fun z => Real.log (Real.cosh (x + β * Real.sqrt (q - t) * z)))
      (ProbabilityTheory.gaussianReal 0 1) := by
  exact integrable_gaussian_logcosh_affine x (β * Real.sqrt (q - t))

/-- The two explicit potential formulas agree at the interface. -/
theorem rsPotential_interface (β q x : ℝ) :
    rsSoftPotential β q q x = rsHardPotential β q x := by
  simp [rsSoftPotential, rsHardPotential]

@[simp] theorem rsHardPotential_terminal (β x : ℝ) :
    rsHardPotential β 1 x = Real.log (Real.cosh x) := by
  simp [rsHardPotential]

lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))

/-- The hard-side spatial derivative is the actual `tanh`. -/
theorem hasDerivAt_rsHardPotential_spatial (β t x : ℝ) :
    HasDerivAt (rsHardPotential β t) (Real.tanh x) x := by
  exact (hasDerivAt_log_cosh x).const_add (β ^ 2 / 2 * (1 - t))

@[simp] theorem deriv_rsHardPotential_spatial (β t x : ℝ) :
    deriv (rsHardPotential β t) x = Real.tanh x :=
  (hasDerivAt_rsHardPotential_spatial β t x).deriv

@[simp] theorem deriv2_rsHardPotential_spatial (β t x : ℝ) :
    deriv (deriv (rsHardPotential β t)) x = sech x ^ 2 := by
  have heq : deriv (rsHardPotential β t) = Real.tanh := by
    funext y
    exact deriv_rsHardPotential_spatial β t y
  rw [heq, deriv_tanh]

/-- The hard-side time derivative is the constant `-β²/2`. -/
theorem hasDerivAt_rsHardPotential_time (β t x : ℝ) :
    HasDerivAt (fun s => rsHardPotential β s x) (-(β ^ 2 / 2)) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).const_mul
    (β ^ 2 / 2)).add_const (Real.log (Real.cosh x)) using 1 <;> simp [rsHardPotential]

@[simp] theorem deriv_rsHardPotential_time (β t x : ℝ) :
    deriv (fun s => rsHardPotential β s x) t = -(β ^ 2 / 2) :=
  (hasDerivAt_rsHardPotential_time β t x).deriv

/-- Direct verification of the classical hard-side Parisi PDE, for the
explicit function itself. No weak-solution identification is assumed. -/
theorem rsHardPotential_PDE (β t x : ℝ) :
    deriv (fun s => rsHardPotential β s x) t + β ^ 2 / 2 *
      (deriv (deriv (rsHardPotential β t)) x + (deriv (rsHardPotential β t) x) ^ 2) = 0 := by
  rw [deriv_rsHardPotential_time, deriv2_rsHardPotential_spatial,
    deriv_rsHardPotential_spatial, add_comm (sech x ^ 2), tanh_sq_add_sech_sq]
  ring

/-- The hard formula satisfies the actual `δ_q` coefficient version of the PDE. -/
theorem rsHardPotential_dirac_PDE {β q t x : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (ht : q ≤ t) :
    deriv (fun s => rsHardPotential β s x) t + β ^ 2 / 2 *
      (deriv (deriv (rsHardPotential β t)) x +
        parisiCDF (diracOverlap q hq) t * (deriv (rsHardPotential β t) x) ^ 2) = 0 := by
  have hCDF : parisiCDF (diracOverlap q hq) t = 1 := by simp [ht]
  rw [hCDF, one_mul]
  exact rsHardPotential_PDE β t x

/-- The functional at a Dirac measure has the paper's RS value, provided the
supplied potential has the explicit value at time zero. -/
theorem parisiFunctional_dirac_eq_rsFreeEnergy {β h q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (u : ParisiMeasure → ℝ → ℝ → ℝ)
    (hu0 : u (diracOverlap q hq) 0 h = β ^ 2 / 2 * (1 - q) +
      gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z)))) :
    parisiFunctional β h u (diracOverlap q hq) = rsFreeEnergy β h q := by
  unfold parisiFunctional rsFreeEnergy
  rw [hu0, dirac_correction_integral hq]
  ring

/-- The soft explicit formula supplies exactly the required time-zero value. -/
theorem rsSoftPotential_zero (β h q : ℝ) :
    rsSoftPotential β q 0 h = β ^ 2 / 2 * (1 - q) +
      gaussianExpectation (fun z => Real.log (Real.cosh (gaussianField β h q z))) := by
  unfold rsSoftPotential gaussianField
  simp only [sub_zero]
  congr 2
  funext z
  rw [add_comm]

end Paper
