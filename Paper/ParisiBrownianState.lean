module

public import Paper.ParisiState
public import Paper.CanonicalBrownian
public import StochasticCalculus.UniformPartitionSums

@[expose] public section

/-!
# The actual general Parisi state driven by canonical Brownian motion

Only analytic properties of the supplied gradient are assumed. The process is
constructed from the genuine pathwise integral Picard solution, and its global
nonnegative-time extension retains Brownian noise while freezing drift after
one. It has the exact characteristics needed for Itô's theorem.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
section State
variable (β h : ℝ) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvbound : ∀ t x, ‖v t x‖ ≤ 1)
    (hvlip : ∀ t, LipschitzWith 1 (v t))

def canonicalParisiStateReal (ω : BrownianSample) : ℝ → ℝ :=
  parisiStateReal β h μ v hv hvbound hvlip 1 zero_le_one
    (parisiNoiseExtension zero_le_one (canonicalBrownianPath ω))
    (continuous_parisiNoiseExtension zero_le_one (canonicalBrownianPath ω))

def canonicalParisiStatePath (ω : BrownianSample) : C(Icc (0 : ℝ) 1, ℝ) :=
  parisiStatePath β h μ v hv hvbound hvlip 1 zero_le_one (canonicalBrownianPath ω)

theorem continuous_canonicalParisiStateReal (ω : BrownianSample) :
    Continuous (canonicalParisiStateReal β h μ v hv hvbound hvlip ω) :=
  continuous_parisiStateReal β h μ v hv hvbound hvlip 1 zero_le_one _ _

theorem measurable_canonicalParisiStatePath :
    Measurable (canonicalParisiStatePath β h μ v hv hvbound hvlip) :=
  (measurable_parisiStatePath β h μ v hv hvbound hvlip 1 zero_le_one).comp
    measurable_canonicalBrownianPath

@[simp] theorem canonicalParisiState_initial (ω : BrownianSample) :
    canonicalParisiStateReal β h μ v hv hvbound hvlip ω 0 = h := by
  apply parisiStateReal_initial
  simp [parisiNoiseExtension, canonicalBrownianPath]

theorem canonicalParisiState_integral_equation (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    canonicalParisiStateReal β h μ v hv hvbound hvlip ω t = h + β * canonicalBrownian t.toNNReal ω +
      ∫ s in 0..t, β ^ 2 * parisiCDF μ s * v s (canonicalParisiStateReal β h μ v hv hvbound hvlip ω s) := by
  have he := parisiStateReal_integral_equation β h μ v hv hvbound hvlip 1 zero_le_one
    (parisiNoiseExtension zero_le_one (canonicalBrownianPath ω))
    (continuous_parisiNoiseExtension zero_le_one (canonicalBrownianPath ω)) ht
  simpa only [canonicalParisiStateReal, parisiNoiseExtension, projIcc_of_mem zero_le_one ht,
    canonicalBrownianPath, ContinuousMap.coe_mk, Subtype.coe_mk] using he

/-- Extend the actual state by retaining noise and freezing its correction after one. -/
def canonicalParisiItoState (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalParisiStateReal β h μ v hv hvbound hvlip ω (min (t : ℝ) 1) +
    β * (canonicalBrownian t ω - canonicalBrownian (min (t : ℝ) 1).toNNReal ω)

def canonicalParisiItoDrift (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  if (t : ℝ) ≤ 1 then β ^ 2 * parisiCDF μ t *
    v t (canonicalParisiItoState β h μ v hv hvbound hvlip t ω) else 0

theorem canonicalParisiItoState_eq {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) (ω : BrownianSample) :
    canonicalParisiItoState β h μ v hv hvbound hvlip t ω =
      canonicalParisiStateReal β h μ v hv hvbound hvlip ω t := by
  simp [canonicalParisiItoState, min_eq_left ht]

@[simp] theorem canonicalParisiItoState_zero (ω : BrownianSample) :
    canonicalParisiItoState β h μ v hv hvbound hvlip 0 ω = h := by
  rw [canonicalParisiItoState_eq β h μ v hv hvbound hvlip (by norm_num)]
  exact canonicalParisiState_initial β h μ v hv hvbound hvlip ω

theorem continuous_canonicalParisiItoState (ω : BrownianSample) :
    Continuous (fun t => canonicalParisiItoState β h μ v hv hvbound hvlip t ω) := by
  have hm : Continuous (fun t : ℝ≥0 => min (t : ℝ) 1) := continuous_subtype_val.min continuous_const
  exact ((continuous_canonicalParisiStateReal β h μ v hv hvbound hvlip ω).comp hm).add
    (((continuous_canonicalBrownian ω).sub
      ((continuous_canonicalBrownian ω).comp (continuous_real_toNNReal.comp hm))).const_mul β)

/-- Strong adaptedness to the actual Brownian driver's natural filtration. -/
theorem stronglyAdapted_canonicalParisiItoState :
    StronglyAdapted (Filtration.natural canonicalBrownian
      (fun t => (measurable_canonicalBrownian t).stronglyMeasurable))
      (canonicalParisiItoState β h μ v hv hvbound hvlip) := by
  intro t
  let F := Filtration.natural canonicalBrownian
    (fun t => (measurable_canonicalBrownian t).stronglyMeasurable)
  let mt : MeasurableSpace BrownianSample := F t
  letI : MeasurableSpace BrownianSample := mt
  have hB (s : ℝ≥0) (hs : s ≤ t) : Measurable (canonicalBrownian s) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup₂_of_le s hs le_rfl
  let r : Icc (0 : ℝ) 1 := ⟨min (t : ℝ) 1, le_min t.coe_nonneg zero_le_one, min_le_right _ _⟩
  have hr : (r : ℝ).toNNReal ≤ t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ r.property.1]
    exact min_le_left _ _
  have hX : Measurable (fun ω => canonicalParisiStateReal β h μ v hv hvbound hvlip ω r) := by
    have he (ω : BrownianSample) : canonicalParisiStateReal β h μ v hv hvbound hvlip ω r =
        parisiStatePath β h μ v hv hvbound hvlip 1 zero_le_one (canonicalBrownianPath ω) r :=
      (parisiStatePath_apply β h μ v hv hvbound hvlip 1 zero_le_one (canonicalBrownianPath ω) r).symm
    simp_rw [he]
    apply measurable_parisiState_eval_of_measurable_past β h μ v hv hvbound hvlip 1 zero_le_one r canonicalBrownianPath
    rw [ContinuousMap.measurable_iff_eval]
    intro s
    apply hB s.1.toNNReal
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ s.property.1]
    exact s.property.2.trans (min_le_left _ _)
  exact (hX.add ((hB t le_rfl).sub (hB _ hr) |>.const_mul β)).stronglyMeasurable

theorem measurable_canonicalParisiItoState :
    Measurable (Function.uncurry (canonicalParisiItoState β h μ v hv hvbound hvlip)) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (continuous_canonicalParisiItoState β h μ v hv hvbound hvlip)
  intro t
  exact ((stronglyAdapted_canonicalParisiItoState β h μ v hv hvbound hvlip t).measurable).mono
    (Filtration.le _ t) le_rfl

theorem measurable_canonicalParisiItoDrift :
    Measurable (Function.uncurry (canonicalParisiItoDrift β h μ v hv hvbound hvlip)) := by
  unfold canonicalParisiItoDrift Function.uncurry
  apply Measurable.ite
  · exact measurableSet_le measurable_fst.coe_nnreal_real measurable_const
  · exact ((measurable_const.mul ((parisiCDF_monotone μ).measurable.comp measurable_fst.coe_nnreal_real)).mul
      (hv.measurable.comp (measurable_fst.coe_nnreal_real.prodMk
        (measurable_canonicalParisiItoState β h μ v hv hvbound hvlip))))
  · exact measurable_const

theorem norm_canonicalParisiItoDrift_le (t : ℝ≥0) (ω : BrownianSample) :
    ‖canonicalParisiItoDrift β h μ v hv hvbound hvlip t ω‖ ≤ β ^ 2 := by
  unfold canonicalParisiItoDrift
  split_ifs
  · rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg β),
      Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    calc
      _ ≤ β ^ 2 * 1 * 1 := by gcongr; exact parisiCDF_le_one μ t; exact hvbound t _
      _ = _ := by ring
  · simpa only [norm_zero] using sq_nonneg β

theorem integrableOn_canonicalParisiItoDrift (t : ℝ≥0) (ω : BrownianSample) :
    IntegrableOn (fun s : ℝ => canonicalParisiItoDrift β h μ v hv hvbound hvlip s.toNNReal ω)
      (Icc (0 : ℝ) (t : ℝ)) := by
  apply (integrableOn_const (isCompact_Icc.measure_ne_top) (C := β ^ 2)).mono'
  · exact ((measurable_canonicalParisiItoDrift β h μ v hv hvbound hvlip).comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun s => norm_canonicalParisiItoDrift_le β h μ v hv hvbound hvlip s.toNNReal ω)

/-- Exact integrated drift, with no regularity imposed on the CDF. -/
theorem integratedDrift_canonicalParisiItoDrift (t : ℝ≥0) (ω : BrownianSample) :
    StochasticCalculus.integratedDrift (canonicalParisiItoDrift β h μ v hv hvbound hvlip) t ω =
      ∫ s in 0..min (t : ℝ) 1, β ^ 2 * parisiCDF μ s *
        v s (canonicalParisiStateReal β h μ v hv hvbound hvlip ω s) := by
  unfold StochasticCalculus.integratedDrift
  have he : (∫ s in Icc (0 : ℝ) (t : ℝ), canonicalParisiItoDrift β h μ v hv hvbound hvlip s.toNNReal ω) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), (Icc (0 : ℝ) 1).indicator
        (fun s => β ^ 2 * parisiCDF μ s * v s (canonicalParisiStateReal β h μ v hv hvbound hvlip ω s)) s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    unfold canonicalParisiItoDrift
    rw [Real.coe_toNNReal s hs.1]
    by_cases hs1 : s ≤ 1
    · rw [ite_eq_left hs1, indicator_of_mem (show s ∈ Icc (0 : ℝ) 1 from ⟨hs.1, hs1⟩),
        canonicalParisiItoState_eq β h μ v hv hvbound hvlip
          (by simpa only [Real.coe_toNNReal s hs.1] using hs1)]
      simp only [Real.coe_toNNReal s hs.1]
    · rw [ite_eq_right hs1, indicator_of_notMem (show s ∉ Icc (0 : ℝ) 1 from fun hx => hs1 hx.2)]
  rw [he, setIntegral_indicator measurableSet_Icc, Icc_inter_Icc, max_self,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_min t.coe_nonneg zero_le_one)]

/-- The actual state has the characteristic decomposition required by genuine Itô calculus. -/
theorem canonicalParisiItoState_decomposition (t : ℝ≥0) (ω : BrownianSample) :
    canonicalParisiItoState β h μ v hv hvbound hvlip t ω =
      canonicalParisiItoState β h μ v hv hvbound hvlip 0 ω +
      StochasticCalculus.integratedDrift (canonicalParisiItoDrift β h μ v hv hvbound hvlip) t ω +
      β * canonicalBrownian t ω := by
  rw [canonicalParisiItoState_zero, integratedDrift_canonicalParisiItoDrift]
  unfold canonicalParisiItoState
  rw [canonicalParisiState_integral_equation β h μ v hv hvbound hvlip ω
    ⟨le_min t.coe_nonneg zero_le_one, min_le_right _ _⟩]
  ring
end State
end Paper
