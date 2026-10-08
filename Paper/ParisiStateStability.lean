module

public import Paper.ParisiControlledState
public import Paper.ParisiItoState
public import Paper.ParisiMeasureStability
public import Paper.ParisiMixContinuity
public import Paper.ParisiCurvature

@[expose] public section

/-! Actual same-driver state stability and admissible optimal feedback controls. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology NNReal
namespace Paper

@[simp] theorem coe_parisiDriftConstant (β : ℝ) :
    (parisiDriftConstant β : ℝ) = β ^ 2 := rfl

theorem exists_parisiStateStabilityIndex (β : ℝ) :
    ∃ n : ℕ, (β ^ 2) ^ n / n.factorial < 1 := by
  exact (FloorSemiring.tendsto_pow_div_factorial_atTop (β ^ 2)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists

def parisiStateStabilityIndex (β : ℝ) : ℕ :=
  Classical.choose (exists_parisiStateStabilityIndex β)

theorem parisiStateStabilityIndex_spec (β : ℝ) :
    (β ^ 2) ^ parisiStateStabilityIndex β / (parisiStateStabilityIndex β).factorial < 1 :=
  Classical.choose_spec (exists_parisiStateStabilityIndex β)

/-- A finite deterministic sensitivity constant depending only on beta. -/
def parisiStateStabilityConstant (β : ℝ) : ℝ :=
  IntegralPicard.sensitivity (parisiDriftConstant β) 1 (parisiStateStabilityIndex β) /
    (1 - (β ^ 2) ^ parisiStateStabilityIndex β / (parisiStateStabilityIndex β).factorial) * β ^ 2

theorem parisiStateStabilityConstant_nonneg (β : ℝ) :
    0 ≤ parisiStateStabilityConstant β := by
  unfold parisiStateStabilityConstant
  exact mul_nonneg (div_nonneg
    (IntegralPicard.sensitivity_nonneg (K := parisiDriftConstant β) zero_le_one _)
    (sub_pos.mpr (parisiStateStabilityIndex_spec β)).le) (sq_nonneg β)

/-- The actual CDF and gradient perturbations control the measurable drift
uniformly, without any Gaussian law premise. -/
theorem parisiNoiseDrift_measure_gradient_dist_le (β : ℝ) (μ ν : ParisiMeasure)
    (v w : ℝ → ℝ → ℝ) (hwbound : ∀ t x, ‖w t x‖ ≤ 1)
    (D E : ℝ) (_hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgrad : ∀ t x, ‖v t x - w t x‖ ≤ D)
    (hCDF : ∀ t, ‖parisiCDF μ t - parisiCDF ν t‖ ≤ E)
    (W : ℝ → ℝ) (t y : ℝ) :
    dist (parisiNoiseDrift β μ v W t y) (parisiNoiseDrift β ν w W t y) ≤
      β ^ 2 * (D + E) := by
  rw [dist_eq_norm]
  have he : parisiNoiseDrift β μ v W t y - parisiNoiseDrift β ν w W t y =
      β ^ 2 * (parisiCDF μ t * (v t (y + β * W t) - w t (y + β * W t)) +
        (parisiCDF μ t - parisiCDF ν t) * w t (y + β * W t)) := by
    unfold parisiNoiseDrift
    ring
  rw [he, norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have hc : ‖parisiCDF μ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    exact parisiCDF_le_one μ t
  simpa only [one_mul, mul_one] using add_le_add
    (mul_le_mul hc (hgrad t _) (norm_nonneg _) (by norm_num))
    (mul_le_mul (hCDF t) (hwbound t _) (norm_nonneg _) hE)

section Stability
variable (β h : ℝ) (μ ν : ParisiMeasure) (v w : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hw : Continuous (Function.uncurry w))
    (hvbound : ∀ t x, ‖v t x‖ ≤ 1) (hwbound : ∀ t x, ‖w t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t)) (hwlip : ∀ t, LipschitzWith 1 (w t))
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgrad : ∀ t x, ‖v t x - w t x‖ ≤ D)
    (hCDF : ∀ t, ‖parisiCDF μ t - parisiCDF ν t‖ ≤ E)

include hD hE hgrad hCDF

/-- Uniform path stability of the actual integral Picard states under a
simultaneous measure and gradient perturbation, using exactly the same noise. -/
theorem parisiStatePath_measure_gradient_dist_le (W : C(Icc (0 : ℝ) 1, ℝ)) :
    dist (parisiStatePath β h μ v hv hvbound hvlip 1 zero_le_one W)
      (parisiStatePath β h ν w hw hwbound hwlip 1 zero_le_one W) ≤
      parisiStateStabilityConstant β * (D + E) := by
  let noise := parisiNoiseExtension zero_le_one W
  have hnoise := continuous_parisiNoiseExtension zero_le_one W
  let hf := isBoundedMeasurableDrift_parisiNoiseDrift β μ v hv hvbound hvlip noise hnoise
  let hg := isBoundedMeasurableDrift_parisiNoiseDrift β ν w hw hwbound hwlip noise hnoise
  have hbound := IntegralPicard.solution_drift_dist_le (h := h) zero_le_one hf hg
    (β ^ 2 * (D + E)) (mul_nonneg (sq_nonneg β) (add_nonneg hD hE))
    (parisiNoiseDrift_measure_gradient_dist_le β μ ν v w hwbound D E hD hE hgrad hCDF noise)
    (parisiStateStabilityIndex β) (by
      simpa only [coe_parisiDriftConstant, mul_one] using parisiStateStabilityIndex_spec β)
  apply (ContinuousMap.dist_le (mul_nonneg (parisiStateStabilityConstant_nonneg β)
    (add_nonneg hD hE))).mpr
  intro t
  change dist ((IntegralPicard.solution (h := h) zero_le_one hf) t + β * W t)
    ((IntegralPicard.solution (h := h) zero_le_one hg) t + β * W t) ≤ _
  rw [dist_add_right]
  have heval : dist ((IntegralPicard.solution (h := h) zero_le_one hf) t)
      ((IntegralPicard.solution (h := h) zero_le_one hg) t) ≤
      dist (IntegralPicard.solution (h := h) zero_le_one hf)
        (IntegralPicard.solution (h := h) zero_le_one hg) :=
    ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap _)
      (g := ODE.FunSpace.toContinuousMap _) t
  apply (heval.trans hbound).trans_eq
  unfold parisiStateStabilityConstant
  simp only [coe_parisiDriftConstant, mul_one]
  ring

theorem canonicalParisiState_measure_gradient_dist_le (omega : BrownianSample)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (canonicalParisiStateReal β h μ v hv hvbound hvlip omega t)
      (canonicalParisiStateReal β h ν w hw hwbound hwlip omega t) ≤
      parisiStateStabilityConstant β * (D + E) := by
  have he := (ContinuousMap.dist_apply_le_dist
    (f := parisiStatePath β h μ v hv hvbound hvlip 1 zero_le_one (canonicalBrownianPath omega))
    (g := parisiStatePath β h ν w hw hwbound hwlip 1 zero_le_one (canonicalBrownianPath omega))
    (⟨t, ht⟩ : Icc (0 : ℝ) 1)).trans
      (parisiStatePath_measure_gradient_dist_le β h μ ν v w hv hw hvbound hwbound hvlip hwlip
        D E hD hE hgrad hCDF (canonicalBrownianPath omega))
  simpa only [parisiStatePath_apply, canonicalParisiStateReal] using he

/-- The global Itô extensions preserve the same state difference after the
physical horizon because both use exactly the same Brownian noise. -/
theorem canonicalParisiItoState_measure_gradient_dist_le (t : ℝ≥0) (omega : BrownianSample) :
    dist (canonicalParisiItoState β h μ v hv hvbound hvlip t omega)
      (canonicalParisiItoState β h ν w hw hwbound hwlip t omega) ≤
      parisiStateStabilityConstant β * (D + E) := by
  unfold canonicalParisiItoState
  rw [dist_add_right]
  exact canonicalParisiState_measure_gradient_dist_le β h μ ν v w hv hw hvbound hwbound
    hvlip hwlip D E hD hE hgrad hCDF omega
    ⟨le_min t.coe_nonneg zero_le_one, min_le_right _ _⟩

end Stability

section Feedback
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hb : ∀ t x, ‖v t x‖ ≤ 1)
    (hl : ∀ t, LipschitzWith 1 (v t))

/-- The actual bounded feedback control, frozen outside the physical time
interval but obtained from the constructed state on that interval. -/
def canonicalParisiFeedbackNNReal (t : ℝ≥0) (omega : BrownianSample) : ℝ :=
  let r := (min (t : ℝ) 1).toNNReal
  v r (canonicalParisiItoState β h μ v hv hb hl r omega)

def canonicalParisiFeedbackControl : ℝ → BrownianSample → ℝ :=
  parisiControlFromNNReal (canonicalParisiFeedbackNNReal β h μ v hv hb hl)

theorem continuous_canonicalParisiFeedbackNNReal (omega : BrownianSample) :
    Continuous (fun t => canonicalParisiFeedbackNNReal β h μ v hv hb hl t omega) := by
  have hr : Continuous (fun t : ℝ≥0 => (min (t : ℝ) 1).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_subtype_val.min continuous_const)
  exact hv.comp ((continuous_subtype_val.comp hr).prodMk
    ((continuous_canonicalParisiItoState β h μ v hv hb hl omega).comp hr))

theorem stronglyAdapted_canonicalParisiFeedbackNNReal :
    StronglyAdapted canonicalBrownianFiltration (canonicalParisiFeedbackNNReal β h μ v hv hb hl) := by
  intro t
  let r := (min (t : ℝ) 1).toNNReal
  have hr : r ≤ t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (le_min t.coe_nonneg zero_le_one)]
    exact min_le_left _ _
  exact hv.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk
    ((stronglyAdapted_canonicalParisiItoState β h μ v hv hb hl r).mono
      (canonicalBrownianFiltration.mono hr)))

theorem isParisiAdmissibleControl_canonicalParisiFeedbackControl :
    IsParisiAdmissibleControl (canonicalParisiFeedbackControl β h μ v hv hb hl) := by
  apply isParisiAdmissibleControl_fromNNReal
  · exact continuous_canonicalParisiFeedbackNNReal β h μ v hv hb hl
  · exact stronglyAdapted_canonicalParisiFeedbackNNReal β h μ v hv hb hl
  · intro t omega
    exact hb _ _

/-- The actual feedback control produces precisely the actual canonical
Parisi state, proved from the two genuine integral decompositions. -/
theorem canonicalParisiControlledState_feedback_eq (t : ℝ≥0) (omega : BrownianSample) :
    canonicalParisiControlledState β h μ (canonicalParisiFeedbackControl β h μ v hv hb hl) t omega =
      canonicalParisiItoState β h μ v hv hb hl t omega := by
  have he : canonicalParisiControlDrift β μ (canonicalParisiFeedbackControl β h μ v hv hb hl) =
      canonicalParisiItoDrift β h μ v hv hb hl := by
    funext s omega
    unfold canonicalParisiControlDrift canonicalParisiItoDrift
    by_cases hs : (s : ℝ) ≤ 1
    · simp only [ite_eq_left hs, canonicalParisiFeedbackControl, parisiControlFromNNReal,
        canonicalParisiFeedbackNNReal, Real.toNNReal_coe, min_eq_left hs]
    · simp only [ite_eq_right hs]
  rw [canonicalParisiControlledState, he]
  have hs := canonicalParisiItoState_decomposition β h μ v hv hb hl t omega
  rw [canonicalParisiItoState_zero] at hs
  exact hs.symm

end Feedback

section FeedbackStability
variable (β h : ℝ) (μ ν : ParisiMeasure) (v w : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hw : Continuous (Function.uncurry w))
    (hvbound : ∀ t x, ‖v t x‖ ≤ 1) (hwbound : ∀ t x, ‖w t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t)) (hwlip : ∀ t, LipschitzWith 1 (w t))
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgrad : ∀ t x, ‖v t x - w t x‖ ≤ D)
    (hCDF : ∀ t, ‖parisiCDF μ t - parisiCDF ν t‖ ≤ E)
include hD hE hgrad hCDF

/-- Actual optimal feedback controls vary uniformly on all sample paths.
The estimate uses the proved spatial Lipschitz constant and actual state stability. -/
theorem canonicalParisiFeedbackControl_dist_le (t : ℝ) (omega : BrownianSample) :
    dist (canonicalParisiFeedbackControl β h μ v hv hvbound hvlip t omega)
      (canonicalParisiFeedbackControl β h ν w hw hwbound hwlip t omega) ≤
      D + parisiStateStabilityConstant β * (D + E) := by
  let r := (min (t.toNNReal : ℝ) 1).toNNReal
  let X := canonicalParisiItoState β h μ v hv hvbound hvlip r omega
  let Y := canonicalParisiItoState β h ν w hw hwbound hwlip r omega
  change dist (v r X) (w r Y) ≤ _
  have hs : dist X Y ≤ parisiStateStabilityConstant β * (D + E) :=
    canonicalParisiItoState_measure_gradient_dist_le β h μ ν v w hv hw hvbound hwbound
      hvlip hwlip D E hD hE hgrad hCDF r omega
  have hl := (hvlip r).dist_le_mul X Y
  simp only [NNReal.coe_one, one_mul] at hl
  have hg : dist (v r Y) (w r Y) ≤ D := by simpa only [dist_eq_norm] using hgrad r Y
  exact (dist_triangle _ (v r Y) _).trans ((add_le_add (hl.trans hs) hg).trans_eq (add_comm _ _))

end FeedbackStability

/-- A deterministic global mixing constant for the actual constructed PDE
gradient. Its existence was proved by propagating a finite backward mesh. -/
def parisiGradientMixConstant (β : ℝ) : ℝ :=
  Classical.choose (exists_parisiGradientBCF_mix_bound β)

theorem parisiGradientMixConstant_nonneg (β : ℝ) :
    0 ≤ parisiGradientMixConstant β :=
  (Classical.choose_spec (exists_parisiGradientBCF_mix_bound β)).1

theorem norm_parisiGradient_mix_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) :
    ‖parisiGradient β μ p - parisiGradient β (parisiMix μ ν ε) p‖ ≤
      parisiGradientMixConstant β * ε := by
  exact (norm_parisiSlabExtend_sub_le (by norm_num)
    (parisiGradientBCF β μ) (parisiGradientBCF β (parisiMix μ ν ε)) p).trans
    ((Classical.choose_spec (exists_parisiGradientBCF_mix_bound β)).2 μ ν ε hε)

/-- The actual feedback control selected by the globally constructed weak
Parisi PDE solution. Continuity, boundedness and spatial Lipschitz regularity
are all proved for that solution, including at beta zero. -/
def selectedParisiFeedbackControl (β h : ℝ) (μ : ParisiMeasure) :
    ℝ → BrownianSample → ℝ :=
  canonicalParisiFeedbackControl β h μ (fun t x => parisiGradient β μ (t, x))
    (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t, x))
    (lipschitzWith_parisiGradient_all β μ)

theorem isParisiAdmissibleControl_selectedParisiFeedbackControl (β h : ℝ)
    (μ : ParisiMeasure) :
    IsParisiAdmissibleControl (selectedParisiFeedbackControl β h μ) :=
  isParisiAdmissibleControl_canonicalParisiFeedbackControl β h μ _ _ _ _

/-- Actual same-Brownian state stability for the PDE-selected gradients
along a probability mixture. The bound is uniform in time and sample path. -/
theorem canonicalParisiItoState_actual_mix_dist_le (β h : ℝ) (μ ν : ParisiMeasure)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (t : ℝ≥0) (omega : BrownianSample) :
    dist (canonicalParisiItoState β h μ (fun s x => parisiGradient β μ (s, x))
      (continuous_parisiGradient β μ) (fun s x => norm_parisiGradient_le_one β μ (s, x))
      (lipschitzWith_parisiGradient_all β μ) t omega)
    (canonicalParisiItoState β h (parisiMix μ ν ε)
      (fun s x => parisiGradient β (parisiMix μ ν ε) (s, x))
      (continuous_parisiGradient β (parisiMix μ ν ε))
      (fun s x => norm_parisiGradient_le_one β (parisiMix μ ν ε) (s, x))
      (lipschitzWith_parisiGradient_all β (parisiMix μ ν ε)) t omega) ≤
      parisiStateStabilityConstant β * (parisiGradientMixConstant β + 1) * ε := by
  have hb := canonicalParisiItoState_measure_gradient_dist_le β h μ (parisiMix μ ν ε)
    (fun s x => parisiGradient β μ (s, x))
    (fun s x => parisiGradient β (parisiMix μ ν ε) (s, x))
    (continuous_parisiGradient β μ) (continuous_parisiGradient β (parisiMix μ ν ε))
    (fun s x => norm_parisiGradient_le_one β μ (s, x))
    (fun s x => norm_parisiGradient_le_one β (parisiMix μ ν ε) (s, x))
    (lipschitzWith_parisiGradient_all β μ) (lipschitzWith_parisiGradient_all β (parisiMix μ ν ε))
    (parisiGradientMixConstant β * ε) ε
    (mul_nonneg (parisiGradientMixConstant_nonneg β) hε.1) hε.1
    (fun s x => norm_parisiGradient_mix_sub_le β μ ν ε hε (s, x))
    (fun s => by simpa only [norm_sub_rev] using norm_parisiCDF_mix_sub_le μ ν ε hε s)
    t omega
  exact hb.trans_eq (by ring)

def parisiFeedbackMixConstant (β : ℝ) : ℝ :=
  parisiGradientMixConstant β +
    parisiStateStabilityConstant β * (parisiGradientMixConstant β + 1)

theorem parisiFeedbackMixConstant_nonneg (β : ℝ) :
    0 ≤ parisiFeedbackMixConstant β := by
  exact add_nonneg (parisiGradientMixConstant_nonneg β)
    (mul_nonneg (parisiStateStabilityConstant_nonneg β)
      (add_nonneg (parisiGradientMixConstant_nonneg β) zero_le_one))

/-- Uniform convergence of the actual PDE-optimal feedback controls along
an actual probability mixture, on every Brownian sample path. -/
theorem selectedParisiFeedbackControl_mix_dist_le (β h : ℝ) (μ ν : ParisiMeasure)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (t : ℝ) (omega : BrownianSample) :
    dist (selectedParisiFeedbackControl β h μ t omega)
      (selectedParisiFeedbackControl β h (parisiMix μ ν ε) t omega) ≤
      parisiFeedbackMixConstant β * ε := by
  have hb := canonicalParisiFeedbackControl_dist_le β h μ (parisiMix μ ν ε)
    (fun s x => parisiGradient β μ (s, x))
    (fun s x => parisiGradient β (parisiMix μ ν ε) (s, x))
    (continuous_parisiGradient β μ) (continuous_parisiGradient β (parisiMix μ ν ε))
    (fun s x => norm_parisiGradient_le_one β μ (s, x))
    (fun s x => norm_parisiGradient_le_one β (parisiMix μ ν ε) (s, x))
    (lipschitzWith_parisiGradient_all β μ) (lipschitzWith_parisiGradient_all β (parisiMix μ ν ε))
    (parisiGradientMixConstant β * ε) ε
    (mul_nonneg (parisiGradientMixConstant_nonneg β) hε.1) hε.1
    (fun s x => norm_parisiGradient_mix_sub_le β μ ν ε hε (s, x))
    (fun s => by simpa only [norm_sub_rev] using norm_parisiCDF_mix_sub_le μ ν ε hε s)
    t omega
  exact hb.trans_eq (by unfold parisiFeedbackMixConstant; ring)

theorem continuousWithinAt_selectedParisiFeedbackControl_mix (β h : ℝ)
    (μ ν : ParisiMeasure) (t : ℝ) (omega : BrownianSample) :
    ContinuousWithinAt
      (fun ε => selectedParisiFeedbackControl β h (parisiMix μ ν ε) t omega)
      (Icc (0 : ℝ) 1) 0 := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [parisiMix_zero]
  apply squeeze_zero' (.of_forall fun ε => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [dist_eq_norm, norm_sub_rev] using
      selectedParisiFeedbackControl_mix_dist_le β h μ ν ε hε t omega
  · simpa using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => parisiFeedbackMixConstant β) (𝓝[Icc (0 : ℝ) 1] 0)
      (𝓝 (parisiFeedbackMixConstant β))).mul nhdsWithin_le_nhds

end Paper
