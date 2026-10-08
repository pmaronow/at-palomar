module

public import Paper.ParisiFiniteCells
public import Paper.ParisiMildDerivative

@[expose] public section

/-! The genuine finite-grid potential satisfies Duhamel on every physical
time slab.  Right derivatives at CDF jumps are sufficient for the FTC.
Spatial differentiation gives the actual local gradient fixed-point equation. -/

open Set MeasureTheory ProbabilityTheory Real Filter Topology

namespace Paper

open SpinGlass SpinGlass.Targets

theorem parisiFinitePotential_lipschitz {k : ℕ} (s : RSBScheme k) (β t x y : ℝ) :
    |parisiFinitePotential s β (t, x) - parisiFinitePotential s β (t, y)| ≤ |x - y| := by
  simpa only [Real.norm_eq_abs, one_mul] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => parisiFinitePotential s β (t, x))
    (f' := fun x => parisiFiniteGradient s β (t, x)) (s := univ) (C := 1)
    (fun z _ => (hasDerivAt_parisiFinitePotential_spatial s β t z).hasDerivWithinAt)
    (fun z _ => norm_parisiFiniteGradient_le_one s β (t, z))
    convex_univ (mem_univ y) (mem_univ x)

theorem parisiFinitePotential_growth {k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    HasLinearGrowth (fun x => parisiFinitePotential s β (t, x)) := by
  refine ⟨|parisiFinitePotential s β (t, 0)|, 1, abs_nonneg _, zero_le_one, ?_⟩
  intro x
  have hLip := parisiFinitePotential_lipschitz s β t x 0
  have htri := abs_add_le (parisiFinitePotential s β (t, x) - parisiFinitePotential s β (t, 0))
    (parisiFinitePotential s β (t, 0))
  simp only [sub_add_cancel] at htri
  simp only [one_mul, sub_zero] at *
  linarith

noncomputable def parisiFiniteGaussianEvolution {k : ℕ} (s : RSBScheme k)
    (β t x r : ℝ) : ℝ :=
  heatSemigroup (β ^ 2 * (r - t)) (fun y => parisiFinitePotential s β (r, y)) x

theorem continuous_parisiFiniteGaussianEvolution {k : ℕ} (s : RSBScheme k)
    (β t x : ℝ) : Continuous (parisiFiniteGaussianEvolution s β t x) := by
  have hc := continuous_parisiFinitePotential s β
  have hlocal : ∀ v₀ : ℝ, ∃ δ C c : ℝ, 0 < δ ∧ 0 ≤ c ∧
      ∀ v ∈ Metric.ball v₀ δ, ∀ w,
        |parisiFinitePotential s β (v, w)| ≤ C * Real.exp (c * |w|) := by
    intro v₀
    have hc0 : Continuous (fun v : ℝ => |parisiFinitePotential s β (v, 0)|) :=
      (hc.comp (continuous_id.prodMk continuous_const)).abs
    have hev : ∀ᶠ v in 𝓝 v₀, |parisiFinitePotential s β (v, 0)| <
        |parisiFinitePotential s β (v₀, 0)| + 1 :=
      (hc0.tendsto v₀).eventually (isOpen_Iio.mem_nhds (lt_add_one _))
    obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ, |parisiFinitePotential s β (v₀, 0)| + 2, 1, hδ, zero_le_one, ?_⟩
    intro v hv w
    have hh := (hb hv).le
    have he1 := Real.one_le_exp (abs_nonneg w)
    have he2 := Real.add_one_le_exp |w|
    have hmule := mul_le_mul_of_nonneg_left he1
      (by positivity : 0 ≤ |parisiFinitePotential s β (v₀, 0)| + 1)
    have hLip := parisiFinitePotential_lipschitz s β v w 0
    have htri := abs_add_le (parisiFinitePotential s β (v, w) - parisiFinitePotential s β (v, 0))
      (parisiFinitePotential s β (v, 0))
    simp only [sub_add_cancel] at htri
    simp only [sub_zero] at hLip
    simp only [one_mul]
    nlinarith [Real.exp_pos |w|]
  have hconv := ColeHopfFoundation.ProbabilityTheory.continuous_integral_comp_curve
    (Ψ := fun v w => parisiFinitePotential s β (v, w))
    (s := fun v => Real.sqrt (β ^ 2 * (v - t)))
    hc (by fun_prop) (fun _ => Real.sqrt_nonneg _) hlocal
  exact hconv.comp (continuous_const.prodMk continuous_id)

theorem hasDerivWithinAt_parisiFiniteGaussianEvolution_right
    (μ : ParisiMeasure) (n : ℕ) (β : ℝ) (hβ : β ≠ 0) (t x : ℝ)
    {r : ℝ} (hrt : t < r) (hr : r ∈ Ico 0 1) :
    HasDerivWithinAt (parisiFiniteGaussianEvolution (parisiGridRSBScheme μ n) β t x)
      (-(β ^ 2 / 2) * parisiHeatSource β (parisiGridMeasure μ n)
        (parisiFiniteGradient (parisiGridRSBScheme μ n) β) t x r) (Ioi r) r := by
  let s := parisiGridRSBScheme μ n
  obtain ⟨p, hp0, hp, hcell, hq⟩ := exists_parisiGrid_right_cell μ n hr
  have hcell' : r ∈ Icc (s.q p) (s.q (p + 1)) := ⟨hcell.1, hcell.2.le⟩
  have he (v : ℝ) (hv : v ∈ Icc (s.q p) (s.q (p + 1))) :
      parisiFiniteGaussianEvolution s β t x v =
        parisiSlabGaussianEvolution s β (n + 2 - p) (s.m p) (s.q (p + 1)) t x v := by
    apply integral_congr_ae
    filter_upwards with z
    exact parisiFinitePotential_eq_slab s β (by omega) hq hv _
  have hev : parisiFiniteGaussianEvolution s β t x =ᶠ[𝓝[Ioi r] r]
      parisiSlabGaussianEvolution s β (n + 2 - p) (s.m p) (s.q (p + 1)) t x := by
    have hav : ∀ᶠ v in 𝓝[Ioi r] r, v < s.q (p + 1) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcell.2)
    filter_upwards [self_mem_nhdsWithin, hav] with v hv hvb
    exact he v ⟨hcell.1.trans hv.le, hvb.le⟩
  have hm : s.m p ∈ Icc 0 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hd := (hasDerivAt_parisiSlabGaussianEvolution s β hβ (n + 2 - p) hm
    (s.q (p + 1)) t x ⟨hrt, hcell.2⟩).hasDerivWithinAt.congr_of_eventuallyEq hev (he r hcell')
  have hsource : parisiHeatSource β (parisiGridMeasure μ n) (parisiFiniteGradient s β) t x r =
      s.m p * parisiSlabGaussianSource s β (n + 2 - p) (s.m p) (s.q (p + 1)) t x r := by
    unfold parisiHeatSource
    rw [parisiCDF_grid_eq_scheme_mass μ n p hp0 hp hcell]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    rw [parisiFiniteGradient_eq_slab s β (by omega) hq hcell']
  change HasDerivWithinAt (parisiFiniteGaussianEvolution s β t x)
    (-(β ^ 2 / 2) * parisiHeatSource β (parisiGridMeasure μ n)
      (parisiFiniteGradient s β) t x r) (Ioi r) r
  rw [hsource]
  simpa only [mul_assoc] using hd

theorem parisiFinitePotential_mild (μ : ParisiMeasure) (n : ℕ)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFinitePotential (parisiGridRSBScheme μ n) β (t, x) =
      heatSemigroup (β ^ 2 * (b - t))
        (fun y => parisiFinitePotential (parisiGridRSBScheme μ n) β (b, y)) x +
      parisiDuhamelCorrection β (parisiGridMeasure μ n)
        (parisiFiniteGradient (parisiGridRSBScheme μ n) β) b t x := by
  let s := parisiGridRSBScheme μ n
  have hE := continuous_parisiFiniteGaussianEvolution s β t x
  have hI := parisiHeatSource_intervalIntegrable β (parisiGridMeasure μ n)
    (parisiFiniteGradient s β) (continuous_parisiFiniteGradient s β).measurable 1
    (norm_parisiFiniteGradient_le_one s β) t x t b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2 hE.continuousOn
    (fun r hr => hasDerivWithinAt_parisiFiniteGaussianEvolution_right μ n β hβ t x hr.1
      ⟨ht.1.trans hr.1.le, hr.2.trans_le hb.2⟩)
    (hI.const_mul (-(β ^ 2 / 2)))
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hi : parisiFiniteGaussianEvolution s β t x t = parisiFinitePotential s β (t, x) := by
    simp [parisiFiniteGaussianEvolution, heatSemigroup, gaussianExpectation]
  rw [hi] at hFTC
  change parisiFinitePotential s β (t, x) = parisiFiniteGaussianEvolution s β t x b +
    β ^ 2 / 2 * ∫ r in t..b, parisiHeatSource β (parisiGridMeasure μ n)
      (parisiFiniteGradient s β) t x r
  linarith

theorem parisiFiniteGradient_mild (μ : ParisiMeasure) (n : ℕ)
    (β : ℝ) (hβ : β ≠ 0) {b t : ℝ} (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 b) (x : ℝ) :
    parisiFiniteGradient (parisiGridRSBScheme μ n) β (t, x) =
      heatSemigroup (β ^ 2 * (b - t))
        (fun y => parisiFiniteGradient (parisiGridRSBScheme μ n) β (b, y)) x +
      parisiGradientCorrection β (parisiGridMeasure μ n)
        (parisiFiniteGradient (parisiGridRSBScheme μ n) β) b t x := by
  let s := parisiGridRSBScheme μ n
  have hcU : Continuous (fun y : ℝ => parisiFinitePotential s β (b, y)) :=
    (continuous_parisiFinitePotential s β).comp (continuous_const.prodMk continuous_id)
  have hcG : Continuous (fun y : ℝ => parisiFiniteGradient s β (b, y)) :=
    (continuous_parisiFiniteGradient s β).comp (continuous_const.prodMk continuous_id)
  have hheat := hasDerivAt_integral_gaussian_shift_bounded (parisiFinitePotential_growth s β b)
    hcU.measurable hcG.measurable (hasDerivAt_parisiFinitePotential_spatial s β b)
    (fun y => by simpa only [Real.norm_eq_abs] using norm_parisiFiniteGradient_le_one s β (b, y))
    (β ^ 2 * (b - t)) x
  have hcorr := hasDerivAt_parisiDuhamelCorrection_spatial β (parisiGridMeasure μ n)
    (parisiFiniteGradient s β) (continuous_parisiFiniteGradient s β).measurable 1
    (norm_parisiFiniteGradient_le_one s β) b t x ht.2 hβ
  have he : (fun y => parisiFinitePotential s β (t, y)) = fun y =>
      heatSemigroup (β ^ 2 * (b - t)) (fun z => parisiFinitePotential s β (b, z)) y +
      parisiDuhamelCorrection β (parisiGridMeasure μ n) (parisiFiniteGradient s β) b t y :=
    funext (parisiFinitePotential_mild μ n β hβ hb ht)
  have hd := hheat.add hcorr
  change HasDerivAt (fun y => heatSemigroup (β ^ 2 * (b - t))
      (fun z => parisiFinitePotential s β (b, z)) y +
      parisiDuhamelCorrection β (parisiGridMeasure μ n) (parisiFiniteGradient s β) b t y)
    (heatSemigroup (β ^ 2 * (b - t)) (fun y => parisiFiniteGradient s β (b, y)) x +
      parisiGradientCorrection β (parisiGridMeasure μ n) (parisiFiniteGradient s β) b t x) x at hd
  rw [← he] at hd
  exact (hasDerivAt_parisiFinitePotential_spatial s β t x).unique hd

end Paper
