module

public import Paper.ParisiFiniteMild
public import Paper.ParisiSchemeMeasure

@[expose] public section

/-! Genuine mild equations for arbitrary finite schemes represented by actual
atomic measures. The general CDF-adapter lemmas below are proved from the
explicit Gaussian slabs; their atomic-measure applications discharge every
CDF premise using the constructed probability law. -/

open Set MeasureTheory ProbabilityTheory Real Filter Topology

namespace Paper

open SpinGlass SpinGlass.Targets

theorem hasDerivWithinAt_parisiFiniteGaussianEvolution_right_of_CDF
    {k : ℕ} (s : RSBScheme k) (ν : ParisiMeasure)
    (hCDF : ∀ p : ℕ, p ≤ k + 1 → ∀ t ∈ Ico (s.q p) (s.q (p + 1)), parisiCDF ν t = s.m p)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ)
    {r : ℝ} (hrt : t < r) (hr : r ∈ Ico 0 1) :
    HasDerivWithinAt (parisiFiniteGaussianEvolution s β t x)
      (-(β ^ 2 / 2) * parisiHeatSource β ν
        (parisiFiniteGradient s β) t x r) (Ioi r) r := by
  obtain ⟨p, hp, hcell, hq⟩ := exists_parisiFinite_right_cell s hr
  have hcell' : r ∈ Icc (s.q p) (s.q (p + 1)) := ⟨hcell.1, hcell.2.le⟩
  have he (v : ℝ) (hv : v ∈ Icc (s.q p) (s.q (p + 1))) :
      parisiFiniteGaussianEvolution s β t x v =
        parisiSlabGaussianEvolution s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x v := by
    apply integral_congr_ae
    filter_upwards with z
    exact parisiFinitePotential_eq_slab s β (by omega) hq hv _
  have hev : parisiFiniteGaussianEvolution s β t x =ᶠ[𝓝[Ioi r] r]
      parisiSlabGaussianEvolution s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x := by
    have hav : ∀ᶠ v in 𝓝[Ioi r] r, v < s.q (p + 1) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcell.2)
    filter_upwards [self_mem_nhdsWithin, hav] with v hv hvb
    exact he v ⟨hcell.1.trans hv.le, hvb.le⟩
  have hm : s.m p ∈ Icc 0 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hd := (hasDerivAt_parisiSlabGaussianEvolution s β hβ (k + 1 - p) hm
    (s.q (p + 1)) t x ⟨hrt, hcell.2⟩).hasDerivWithinAt.congr_of_eventuallyEq hev (he r hcell')
  have hsource : parisiHeatSource β ν (parisiFiniteGradient s β) t x r =
      s.m p * parisiSlabGaussianSource s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x r := by
    unfold parisiHeatSource
    rw [hCDF p hp r hcell]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [parisiFiniteGradient_eq_slab s β (by omega) hq hcell']
  change HasDerivWithinAt (parisiFiniteGaussianEvolution s β t x)
    (-(β ^ 2 / 2) * parisiHeatSource β ν
      (parisiFiniteGradient s β) t x r) (Ioi r) r
  rw [hsource]
  simpa only [mul_assoc] using hd

theorem parisiFinitePotential_mild_of_CDF {k : ℕ} (s : RSBScheme k) (ν : ParisiMeasure)
    (hCDF : ∀ p : ℕ, p ≤ k + 1 → ∀ t ∈ Ico (s.q p) (s.q (p + 1)), parisiCDF ν t = s.m p)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFinitePotential s β (t, x) =
      heatSemigroup (β ^ 2 * (b - t))
        (fun y => parisiFinitePotential s β (b, y)) x +
      parisiDuhamelCorrection β ν
        (parisiFiniteGradient s β) b t x := by
  have hE := continuous_parisiFiniteGaussianEvolution s β t x
  have hI := parisiHeatSource_intervalIntegrable β ν
    (parisiFiniteGradient s β) (continuous_parisiFiniteGradient s β).measurable 1
    (norm_parisiFiniteGradient_le_one s β) t x t b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2 hE.continuousOn
    (fun r hr => hasDerivWithinAt_parisiFiniteGaussianEvolution_right_of_CDF s ν hCDF β hβ t x hr.1
      ⟨ht.1.trans hr.1.le, hr.2.trans_le hb.2⟩)
    (hI.const_mul (-(β ^ 2 / 2)))
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hi : parisiFiniteGaussianEvolution s β t x t = parisiFinitePotential s β (t, x) := by
    simp [parisiFiniteGaussianEvolution, heatSemigroup, gaussianExpectation]
  rw [hi] at hFTC
  change parisiFinitePotential s β (t, x) = parisiFiniteGaussianEvolution s β t x b +
    β ^ 2 / 2 * ∫ r in t..b, parisiHeatSource β ν
      (parisiFiniteGradient s β) t x r
  linarith

theorem parisiFiniteGradient_mild_of_CDF {k : ℕ} (s : RSBScheme k) (ν : ParisiMeasure)
    (hCDF : ∀ p : ℕ, p ≤ k + 1 → ∀ t ∈ Ico (s.q p) (s.q (p + 1)), parisiCDF ν t = s.m p)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFiniteGradient s β (t, x) =
      heatSemigroup (β ^ 2 * (b - t))
        (fun y => parisiFiniteGradient s β (b, y)) x +
      parisiGradientCorrection β ν
        (parisiFiniteGradient s β) b t x := by
  have hcU : Continuous (fun y : ℝ => parisiFinitePotential s β (b, y)) :=
    (continuous_parisiFinitePotential s β).comp (continuous_const.prodMk continuous_id)
  have hcG : Continuous (fun y : ℝ => parisiFiniteGradient s β (b, y)) :=
    (continuous_parisiFiniteGradient s β).comp (continuous_const.prodMk continuous_id)
  have hheat := hasDerivAt_integral_gaussian_shift_bounded (parisiFinitePotential_growth s β b)
    hcU.measurable hcG.measurable (hasDerivAt_parisiFinitePotential_spatial s β b)
    (fun y => by simpa only [Real.norm_eq_abs] using norm_parisiFiniteGradient_le_one s β (b, y))
    (β ^ 2 * (b - t)) x
  have hcorr := hasDerivAt_parisiDuhamelCorrection_spatial β ν
    (parisiFiniteGradient s β) (continuous_parisiFiniteGradient s β).measurable 1
    (norm_parisiFiniteGradient_le_one s β) b t x ht.2 hβ
  have he : (fun y => parisiFinitePotential s β (t, y)) = fun y =>
      heatSemigroup (β ^ 2 * (b - t)) (fun z => parisiFinitePotential s β (b, z)) y +
      parisiDuhamelCorrection β ν (parisiFiniteGradient s β) b t y :=
    funext (parisiFinitePotential_mild_of_CDF s ν hCDF β hβ hb ht)
  have hd := hheat.add hcorr
  change HasDerivAt (fun y => heatSemigroup (β ^ 2 * (b - t))
      (fun z => parisiFinitePotential s β (b, z)) y +
      parisiDuhamelCorrection β ν (parisiFiniteGradient s β) b t y)
    (heatSemigroup (β ^ 2 * (b - t)) (fun y => parisiFiniteGradient s β (b, y)) x +
      parisiGradientCorrection β ν (parisiFiniteGradient s β) b t x) x at hd
  rw [← he] at hd
  exact (hasDerivAt_parisiFinitePotential_spatial s β t x).unique hd

theorem parisiSchemePotential_mild {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFinitePotential s β (t, x) =
      heatSemigroup (β ^ 2 * (b - t)) (fun y => parisiFinitePotential s β (b, y)) x +
      parisiDuhamelCorrection β (parisiSchemeMeasure s) (parisiFiniteGradient s β) b t x :=
  parisiFinitePotential_mild_of_CDF s (parisiSchemeMeasure s)
    (fun _ hp _ ht => parisiCDF_scheme_cell s hp ht) β hβ hb ht x

theorem parisiSchemeGradient_mild {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFiniteGradient s β (t, x) =
      heatSemigroup (β ^ 2 * (b - t)) (fun y => parisiFiniteGradient s β (b, y)) x +
      parisiGradientCorrection β (parisiSchemeMeasure s) (parisiFiniteGradient s β) b t x :=
  parisiFiniteGradient_mild_of_CDF s (parisiSchemeMeasure s)
    (fun _ hp _ ht => parisiCDF_scheme_cell s hp ht) β hβ hb ht x

end Paper
