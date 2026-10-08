module

public import Paper.ParisiWeakUniqueness
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Spatial Lipschitz regularity from the paper's genuine weak gradient. -/
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap Metric
open scoped Topology ContDiff Convolution NNReal
namespace Paper

/-- Continuous extension of a strip potential by clamping only time. -/
def parisiClampPotential (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u (max 0 (min 1 p.1), p.2)

theorem continuous_parisiClampPotential (u : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ)) :
    Continuous (parisiClampPotential u) := by
  apply hu.comp_continuous (by fun_prop)
  intro p
  exact ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, mem_univ _⟩

theorem parisiClampPotential_eq (u : ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (0 : ℝ) 1) : parisiClampPotential u p = u p := by
  simp only [parisiClampPotential, min_eq_right hp.2, max_eq_right hp.1, Prod.mk.eta]

theorem parisiSpaceTime_eq_restrict_volume :
    parisiSpaceTime = volume.restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  rw [parisiSpaceTime, Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]

/-- Moving a compact test from a strip integral to full-plane Lebesgue measure. -/
theorem integral_parisiSpaceTime_eq_volume_of_support (f : ℝ × ℝ → ℝ)
    (hf : Function.support f ⊆ Icc (0 : ℝ) 1 ×ˢ univ) :
    (∫ p, f p ∂parisiSpaceTime) = ∫ p, f p := by
  rw [parisiSpaceTime_eq_restrict_volume]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => Function.notMem_support.mp (fun hs => hp (hf hs)))

/-- Reflected smooth mollifier used as the actual distributional test. -/
def reflectedParisiTest (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ → ℝ :=
  fun y => φ (p - y)

theorem contDiff_reflectedParisiTest (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (p : ℝ × ℝ) : ContDiff ℝ ∞ (reflectedParisiTest φ p) :=
  hφ.comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_reflectedParisiTest (φ : ℝ × ℝ → ℝ)
    (hc : HasCompactSupport φ) (p : ℝ × ℝ) :
    HasCompactSupport (reflectedParisiTest φ p) := by
  exact hc.comp_homeomorph (Homeomorph.subLeft p)

theorem parisiTestX_reflected (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (p y : ℝ × ℝ) :
    parisiTestX (reflectedParisiTest φ p) y = -fderiv ℝ φ (p - y) (0, 1) := by
  have hd := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt y.2
    ((hasDerivAt_const y.2 p).sub
      ((hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)))
  simpa only [reflectedParisiTest, parisiTestX, Function.comp_def, Pi.sub_def,
    id_eq, Prod.mk.eta, zero_sub, map_neg] using hd.deriv

/-- Spatial smoothing is an actual compact convolution of the continuous
extension, not a supplied differentiable representative. -/
def parisiSpatialMollification (u φ : ℝ × ℝ → ℝ) (t x : ℝ) : ℝ :=
  (parisiClampPotential u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ) (t, x)

theorem hasDerivAt_parisiSpatialMollification (u φ : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (t x : ℝ) :
    HasDerivAt (parisiSpatialMollification u φ t)
      (∫ y, parisiClampPotential u y * fderiv ℝ φ ((t, x) - y) (0, 1)) x := by
  have hl := (continuous_parisiClampPotential u hu).locallyIntegrable (μ := volume)
  have hd := (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hl (hφ.of_le (by simp)) (t, x)).comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  rw [convolution_precompR_apply _ hl (hc.fderiv ℝ)
    (hφ.continuous_fderiv (by simp))] at hd
  exact hd

/-- The convolution derivative equals the actual weak-gradient average.
All distributional-test and support hypotheses concern explicit functions. -/
theorem parisiSpatialMollification_derivative_eq_weakAverage
    (u v φ : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (p : ℝ × ℝ)
    (hs : tsupport (reflectedParisiTest φ p) ⊆
      {y : ℝ × ℝ | 0 < y.1 ∧ y.1 < 1}) :
    (∫ y, parisiClampPotential u y * fderiv ℝ φ (p - y) (0, 1)) =
      ∫ y, v y * reflectedParisiTest φ p y ∂parisiSpaceTime := by
  let ψ := reflectedParisiTest φ p
  have hψ := contDiff_reflectedParisiTest φ hφ p
  have hψc := hasCompactSupport_reflectedParisiTest φ hc p
  have huC := continuous_parisiClampPotential u hu
  have hxc := hasCompactSupport_parisiTestX ψ hψ hψc
  have hix : Integrable (fun y => parisiClampPotential u y * parisiTestX ψ y) volume :=
    (huC.mul (continuous_parisiTestX ψ hψ)).integrable_of_hasCompactSupport hxc.mul_left
  have hEq : (fun y => u y * parisiTestX ψ y) =ᵐ[parisiSpaceTime]
      (fun y => parisiClampPotential u y * parisiTestX ψ y) := by
    rw [parisiSpaceTime_eq_restrict_volume]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with y hy
    rw [parisiClampPotential_eq u hy.1]
  have hixs : Integrable (fun y => u y * parisiTestX ψ y) parisiSpaceTime := by
    have hi : Integrable (fun y => parisiClampPotential u y * parisiTestX ψ y)
        (volume.restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) := hix.restrict
    rw [← parisiSpaceTime_eq_restrict_volume] at hi
    exact hi.congr hEq.symm
  obtain ⟨hweakInt, hweakEq⟩ := hw ψ hψ hψc hs
  have hiv : Integrable (fun y => v y * ψ y) parisiSpaceTime := by
    exact (hweakInt.sub hixs).congr (.of_forall fun y => by
      simp only [Pi.sub_apply]; ring)
  rw [integral_add hixs hiv] at hweakEq
  have hfull : (∫ y, u y * parisiTestX ψ y ∂parisiSpaceTime) =
      -(∫ y, parisiClampPotential u y * fderiv ℝ φ (p - y) (0, 1)) := by
    rw [integral_congr_ae hEq]
    rw [integral_parisiSpaceTime_eq_volume_of_support _]
    · simp_rw [ψ, parisiTestX_reflected φ hφ p, mul_neg]
      exact integral_neg _
    · intro y hy
      have hx : y ∈ Function.support (parisiTestX ψ) := by
        exact (Function.support_mul_subset_right _ _ hy)
      have hy' := hs ((tsupport_parisiTestX_subset ψ hψ) (subset_closure hx))
      exact ⟨⟨hy'.1.le, hy'.2.le⟩, mem_univ _⟩
  rw [hfull] at hweakEq
  linarith

theorem integral_reflectedParisiTest (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (∫ y, reflectedParisiTest φ p y) = ∫ y, φ y := by
  unfold reflectedParisiTest
  simp_rw [sub_eq_add_neg]
  rw [integral_neg_eq_self (fun y => φ (p + y)), integral_add_left_eq_self]

/-- A nonnegative normalized mollifier inherits the actual essential
gradient bound, despite the potential having only a weak derivative. -/
theorem norm_deriv_parisiSpatialMollification_le
    (u v φ : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hn : ∀ y, 0 ≤ φ y) (hm : (∫ y, φ y) = 1)
    (M : ℝ≥0) (hb : ∀ᵐ y ∂parisiSpaceTime, ‖v y‖ ≤ M)
    (t x : ℝ) (hs : tsupport (reflectedParisiTest φ (t, x)) ⊆
      {y : ℝ × ℝ | 0 < y.1 ∧ y.1 < 1}) :
    ‖deriv (parisiSpatialMollification u φ t) x‖ ≤ M := by
  rw [(hasDerivAt_parisiSpatialMollification u φ hu hφ hc t x).deriv,
    parisiSpatialMollification_derivative_eq_weakAverage u v φ hu hw hφ hc (t, x) hs]
  let ψ := reflectedParisiTest φ (t, x)
  have hψc := hasCompactSupport_reflectedParisiTest φ hc (t, x)
  have hψi : Integrable ψ volume :=
    (contDiff_reflectedParisiTest φ hφ (t, x)).continuous.integrable_of_hasCompactSupport hψc
  have hψis : Integrable ψ parisiSpaceTime := by
    rw [parisiSpaceTime_eq_restrict_volume]
    exact hψi.restrict
  have hψmass : (∫ y, ψ y ∂parisiSpaceTime) = 1 := by
    rw [integral_parisiSpaceTime_eq_volume_of_support _]
    · exact (integral_reflectedParisiTest φ (t, x)).trans hm
    · intro y hy
      have hys := hs (subset_closure hy)
      exact ⟨⟨hys.1.le, hys.2.le⟩, mem_univ _⟩
  have hbound := norm_integral_le_of_norm_le (f := fun y => v y * ψ y)
    (hψis.const_mul (M : ℝ))
    (by
      filter_upwards [hb] with y hy
      have hψn : 0 ≤ ψ y := hn _
      rw [norm_mul, Real.norm_of_nonneg hψn]
      exact mul_le_mul_of_nonneg_right hy hψn)
  simpa only [integral_const_mul, hψmass, mul_one] using hbound

/-- An explicit sequence of smooth nonnegative unit-mass plane mollifiers. -/
def parisiPlaneBump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := (1 / (n + 1 : ℝ)) / 2
  rOut := 1 / (n + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith

theorem parisiPlaneBump_rOut_tendsto :
    Tendsto (fun n => (parisiPlaneBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The translated support remains in the open strip whenever the bump
radius is smaller than both distances to its time boundaries. -/
theorem tsupport_reflected_planeBump_subset (φ : ContDiffBump (0 : ℝ × ℝ))
    (t x : ℝ) (hleft : φ.rOut < t) (hright : φ.rOut < 1 - t) :
    tsupport (reflectedParisiTest (φ.normed volume) (t, x)) ⊆
      {y : ℝ × ℝ | 0 < y.1 ∧ y.1 < 1} := by
  have hc : tsupport (reflectedParisiTest (φ.normed volume) (t, x)) ⊆
      closedBall (t, x) φ.rOut := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    have hφ : (t, x) - y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq] at hφ
    have hn : ‖(t, x) - y‖ < φ.rOut := by
      simpa only [mem_ball, dist_zero_right] using hφ
    rw [mem_closedBall, dist_eq_norm_sub']
    exact hn.le
  intro y hy
  have hn : ‖(t, x) - y‖ ≤ φ.rOut := by
    simpa only [mem_closedBall, dist_eq_norm_sub'] using hc hy
  have htime : |t - y.1| ≤ φ.rOut := by
    have hh := (_root_.norm_fst_le ((t, x) - y)).trans hn
    simpa only [Prod.fst_sub, Real.norm_eq_abs] using hh
  rcases abs_le.mp htime with ⟨hl, hr⟩
  constructor <;> linarith

/-- Every compact mollification of a genuine bounded weak gradient is
spatially Lipschitz on each time line wholly inside the strip. -/
theorem lipschitzWith_parisiSpatialMollification
    (u v : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (M : ℝ≥0)
    (hb : ∀ᵐ y ∂parisiSpaceTime, ‖v y‖ ≤ M)
    (φ : ContDiffBump (0 : ℝ × ℝ)) (t : ℝ)
    (hleft : φ.rOut < t) (hright : φ.rOut < 1 - t) :
    LipschitzWith M (parisiSpatialMollification u (φ.normed volume) t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_parisiSpatialMollification u _ hu φ.contDiff_normed
      φ.hasCompactSupport_normed t x).differentiableAt
  · intro x
    apply NNReal.coe_le_coe.mp
    exact norm_deriv_parisiSpatialMollification_le u v _ hu hw φ.contDiff_normed
      φ.hasCompactSupport_normed φ.nonneg_normed φ.integral_normed M hb t x
      (tsupport_reflected_planeBump_subset φ t x hleft hright)

theorem parisiSpatialMollification_tendsto (u : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ)) (t x : ℝ) :
    Tendsto (fun n => parisiSpatialMollification u ((parisiPlaneBump n).normed volume) t x)
      atTop (𝓝 (parisiClampPotential u (t, x))) := by
  have hl := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) parisiPlaneBump_rOut_tendsto (continuous_parisiClampPotential u hu) (t, x)
  have hsym : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    rfl
  apply hl.congr
  intro n
  unfold parisiSpatialMollification
  rw [convolution_symm (ContinuousLinearMap.mul ℝ ℝ) hsym]
  rfl

/-- The weak spatial gradient bound controls every continuous interior
spatial section, obtained as the limit of genuine smooth mollifications. -/
theorem lipschitzWith_parisiWeakGradient_interior
    (u v : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (M : ℝ≥0)
    (hb : ∀ᵐ y ∂parisiSpaceTime, ‖v y‖ ≤ M)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    LipschitzWith M (fun x => u (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := parisiSpatialMollification_tendsto u hu t x
  have hy := parisiSpatialMollification_tendsto u hu t y
  rw [parisiClampPotential_eq u ⟨ht.1.le, ht.2.le⟩] at hx hy
  apply le_of_tendsto (hx.dist hy)
  have hl := parisiPlaneBump_rOut_tendsto.eventually (eventually_lt_nhds ht.1)
  have hr := parisiPlaneBump_rOut_tendsto.eventually
    (eventually_lt_nhds (sub_pos.mpr ht.2))
  filter_upwards [hl, hr] with n hnleft hnright
  exact (lipschitzWith_parisiSpatialMollification u v hu hw M hb
    (parisiPlaneBump n) t hnleft hnright).dist_le_mul x y

/-- Spatial Lipschitz regularity on the full closed time strip follows from
continuity of the potential, including both time-boundary traces. -/
theorem lipschitzWith_parisiWeakGradient
    (u v : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (M : ℝ≥0)
    (hb : ∀ᵐ y ∂parisiSpaceTime, ‖v y‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    LipschitzWith M (fun x => u (t, x)) := by
  let S : Set ℝ := {r | ∀ x y : ℝ,
    dist (parisiClampPotential u (r, x)) (parisiClampPotential u (r, y)) ≤ M * dist x y}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_le _ continuous_const
    exact ((continuous_parisiClampPotential u hu).comp (by fun_prop)).dist
      ((continuous_parisiClampPotential u hu).comp (by fun_prop))
  have hsub : Ioo (0 : ℝ) 1 ⊆ S := by
    intro r hr x y
    rw [parisiClampPotential_eq u ⟨hr.1.le, hr.2.le⟩,
      parisiClampPotential_eq u ⟨hr.1.le, hr.2.le⟩]
    exact (lipschitzWith_parisiWeakGradient_interior u v hu hw M hb hr).dist_le_mul x y
  have hclosed : Icc (0 : ℝ) 1 ⊆ S := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact hS.closure_subset_iff.mpr hsub
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he := hclosed ht x y
  simpa only [parisiClampPotential_eq u (p := (t, x)) ht,
    parisiClampPotential_eq u (p := (t, y)) ht] using he

/-- Uniform linear growth is derived from the distributional gradient
bound and the continuous zero-space section on the compact time interval. -/
theorem parisiWeakGradient_uniform_linear_growth
    (u v : ℝ × ℝ → ℝ)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (hw : IsParisiWeakGradient u v) (M : ℝ≥0)
    (hb : ∀ᵐ y ∂parisiSpaceTime, ‖v y‖ ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      ‖u (t, x)‖ ≤ A + M * ‖x‖ := by
  have hbase : Continuous (fun t : ℝ => parisiClampPotential u (t, 0)) :=
    (continuous_parisiClampPotential u hu).comp (by fun_prop)
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hbase.continuousOn
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro t ht x
  have hzero : ‖u (t, 0)‖ ≤ max A 0 := by
    have he := (hA t ht).trans (le_max_left A 0)
    simpa only [parisiClampPotential_eq u (p := (t, 0)) ht] using he
  have hdiff : ‖u (t, x) - u (t, 0)‖ ≤ M * ‖x‖ := by
    simpa only [dist_eq_norm, sub_zero] using
      (lipschitzWith_parisiWeakGradient u v hu hw M hb ht).dist_le_mul x 0
  calc
    ‖u (t, x)‖ = ‖(u (t, x) - u (t, 0)) + u (t, 0)‖ := by congr 1; ring
    _ ≤ ‖u (t, x) - u (t, 0)‖ + ‖u (t, 0)‖ := norm_add_le _ _
    _ ≤ M * ‖x‖ + max A 0 := add_le_add hdiff hzero
    _ = max A 0 + M * ‖x‖ := add_comm _ _

/-- Every member of the paper's original weak terminal-value class has
uniform spatial Lipschitz sections; no classical spatial derivative is added. -/
theorem IsParisiWeakSolution.spatial_lipschitz {β : ℝ} {μ : ParisiMeasure}
    {u v : ℝ × ℝ → ℝ} (huv : IsParisiWeakSolution β μ u v) :
    ∃ M : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) 1, LipschitzWith M (fun x => u (t, x)) := by
  obtain ⟨K, hK⟩ := huv.bounded_gradient
  refine ⟨K.toNNReal, fun t ht => lipschitzWith_parisiWeakGradient u v
    huv.continuous_potential huv.weak_gradient K.toNNReal ?_ ht⟩
  filter_upwards [hK] with p hp
  exact hp.trans (Real.le_coe_toNNReal K)

/-- Uniform linear growth is a theorem of the paper's weak class, rather
than an extra uniqueness assumption. -/
theorem IsParisiWeakSolution.uniform_linear_growth {β : ℝ} {μ : ParisiMeasure}
    {u v : ℝ × ℝ → ℝ} (huv : IsParisiWeakSolution β μ u v) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      ‖u (t, x)‖ ≤ A + L * ‖x‖ := by
  obtain ⟨K, hK⟩ := huv.bounded_gradient
  have hbound : ∀ᵐ p ∂parisiSpaceTime, ‖v p‖ ≤ K.toNNReal := by
    filter_upwards [hK] with p hp
    exact hp.trans (Real.le_coe_toNNReal K)
  obtain ⟨A, hA, hg⟩ := parisiWeakGradient_uniform_linear_growth u v
    huv.continuous_potential huv.weak_gradient K.toNNReal hbound
  exact ⟨A, K.toNNReal, hA, K.toNNReal.coe_nonneg, hg⟩

end Paper
