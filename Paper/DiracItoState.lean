module

public import Paper.DiracBrownianState
public import StochasticCalculus.UniformPartitionSums

@[expose] public section

/-!
# Global-time extension of the actual Dirac state

The drift is frozen after time one while the Brownian noise continues. This
extension satisfies the characteristic decomposition required by the genuine
Itô calculus library on every nonnegative time horizon.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- Freeze the ODE correction after one, while retaining the actual Brownian noise. -/
def canonicalDiracItoState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalDiracStateReal β h q hq ω (min (t : ℝ) 1) +
    β * (canonicalBrownian t ω - canonicalBrownian (min (t : ℝ) 1).toNNReal ω)

/-- The true drift of the global extension, cut off outside `[q,1]`. -/
def canonicalDiracItoDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  if q ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 then
    β ^ 2 * Real.tanh (canonicalDiracItoState β h q hq t ω) else 0

/-- Exact agreement with the actual physical state up to time one. -/
theorem canonicalDiracItoState_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) (ω : BrownianSample) :
    canonicalDiracItoState β h q hq t ω = canonicalDiracStateReal β h q hq ω t := by
  simp [canonicalDiracItoState, min_eq_left ht]

@[simp] theorem canonicalDiracItoState_zero (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : canonicalDiracItoState β h q hq 0 ω = h := by
  rw [canonicalDiracItoState_eq β h q hq (by norm_num)]
  simpa only [NNReal.coe_zero] using canonicalDiracState_initial β h q hq ω

/-- Every sample path of the global state is continuous. -/
theorem continuous_canonicalDiracItoState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : Continuous (fun t => canonicalDiracItoState β h q hq t ω) := by
  have hm : Continuous (fun t : ℝ≥0 => min (t : ℝ) 1) := continuous_subtype_val.min continuous_const
  exact ((continuous_canonicalDiracStateReal β h q hq ω).comp hm).add
    (((continuous_canonicalBrownian ω).sub
      ((continuous_canonicalBrownian ω).comp (continuous_real_toNNReal.comp hm))).const_mul β)

/-- The global state is strongly adapted to the actual Brownian driver's natural filtration. -/
theorem stronglyAdapted_canonicalDiracItoState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    StronglyAdapted (Filtration.natural canonicalBrownian
      (fun t => (measurable_canonicalBrownian t).stronglyMeasurable))
      (canonicalDiracItoState β h q hq) := by
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
  have hX : Measurable (fun ω => canonicalDiracStateReal β h q hq ω r) := by
    change Measurable (fun ω => diracStatePath β h q hq (canonicalBrownianPath ω) r)
    apply measurable_diracState_eval_of_measurable_past β h q hq r canonicalBrownianPath
    rw [ContinuousMap.measurable_iff_eval]
    intro s
    apply hB s.1.toNNReal
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ s.property.1]
    exact s.property.2.trans (min_le_left _ _)
  exact (hX.add ((hB t le_rfl).sub (hB _ hr) |>.const_mul β)).stronglyMeasurable

/-- Joint measurability of the actual state in time and sample. -/
theorem measurable_canonicalDiracItoState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    Measurable (Function.uncurry (canonicalDiracItoState β h q hq)) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (continuous_canonicalDiracItoState β h q hq)
  intro t
  exact ((stronglyAdapted_canonicalDiracItoState β h q hq t).measurable).mono
    (Filtration.le _ t) le_rfl

/-- Joint measurability of the bounded drift. -/
theorem measurable_canonicalDiracItoDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    Measurable (Function.uncurry (canonicalDiracItoDrift β h q hq)) := by
  unfold canonicalDiracItoDrift Function.uncurry
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_fst.coe_nnreal_real).inter
      (measurableSet_le measurable_fst.coe_nnreal_real measurable_const)
  · exact (((continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt )).measurable).comp (measurable_canonicalDiracItoState β h q hq)).const_mul _
  · exact measurable_const

/-- The true drift is bounded uniformly on every path and time horizon. -/
theorem norm_canonicalDiracItoDrift_le (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) : ‖canonicalDiracItoDrift β h q hq t ω‖ ≤ β ^ 2 := by
  unfold canonicalDiracItoDrift
  split_ifs
  · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (sq_nonneg β) (Real.abs_tanh_lt_one _).le
  · simpa only [norm_zero] using sq_nonneg β

/-- Pathwise drift integrability on every horizon, as required by Itô characteristics. -/
theorem integrableOn_canonicalDiracItoDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) :
    IntegrableOn (fun s : ℝ => canonicalDiracItoDrift β h q hq s.toNNReal ω)
      (Icc (0 : ℝ) (t : ℝ)) := by
  apply (integrableOn_const (isCompact_Icc.measure_ne_top) (C := β ^ 2)).mono'
  · exact ((measurable_canonicalDiracItoDrift β h q hq).comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with s
    exact norm_canonicalDiracItoDrift_le β h q hq s.toNNReal ω

/-- The integrated drift is exactly the physical post-interface drift integral. -/
theorem integratedDrift_canonicalDiracItoDrift (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) :
    StochasticCalculus.integratedDrift (canonicalDiracItoDrift β h q hq) t ω =
      if q ≤ (t : ℝ) then
        ∫ s in q..min (t : ℝ) 1, β ^ 2 * Real.tanh (canonicalDiracStateReal β h q hq ω s)
      else 0 := by
  unfold StochasticCalculus.integratedDrift
  have he : (∫ s in Icc (0 : ℝ) (t : ℝ), canonicalDiracItoDrift β h q hq s.toNNReal ω) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), (Icc q (1 : ℝ)).indicator
        (fun s => β ^ 2 * Real.tanh (canonicalDiracStateReal β h q hq ω s)) s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    unfold canonicalDiracItoDrift
    rw [Real.coe_toNNReal s hs.1]
    by_cases hsq : s ∈ Icc q (1 : ℝ)
    · rw [ite_eq_left (show q ≤ s ∧ s ≤ 1 from hsq), indicator_of_mem hsq,
        canonicalDiracItoState_eq β h q hq (by simpa only [Real.coe_toNNReal s hs.1] using hsq.2)]
      simp only [Real.coe_toNNReal s hs.1]
    · rw [ite_eq_right (show ¬(q ≤ s ∧ s ≤ 1) from hsq), indicator_of_notMem hsq]
  rw [he, setIntegral_indicator measurableSet_Icc]
  by_cases ht : q ≤ (t : ℝ)
  · rw [ite_eq_left ht]
    have hm : q ≤ min (t : ℝ) 1 := le_min ht hq.2
    have hs : Icc (0 : ℝ) (t : ℝ) ∩ Icc q (1 : ℝ) = Icc q (min (t : ℝ) 1) := by
      rw [Icc_inter_Icc]
      change Icc (max 0 q) (min (t : ℝ) 1) = Icc q (min (t : ℝ) 1)
      rw [max_eq_right hq.1]
    rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm]
  · rw [ite_eq_right ht]
    have hs : Icc (0 : ℝ) (t : ℝ) ∩ Icc q (1 : ℝ) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact ht (hs.2.1.trans hs.1.2)
    rw [hs, setIntegral_empty]

/-- The actual global state has the characteristic decomposition for Itô's theorem. -/
theorem canonicalDiracItoState_decomposition (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ω : BrownianSample) :
    canonicalDiracItoState β h q hq t ω = canonicalDiracItoState β h q hq 0 ω +
      StochasticCalculus.integratedDrift (canonicalDiracItoDrift β h q hq) t ω +
      β * canonicalBrownian t ω := by
  rw [canonicalDiracItoState_zero, integratedDrift_canonicalDiracItoDrift]
  unfold canonicalDiracItoState
  by_cases ht : q ≤ (t : ℝ)
  · rw [ite_eq_left ht, canonicalDiracState_after β h q hq ω
      ⟨le_min ht hq.2, min_le_right _ _⟩]
    ring
  · rw [ite_eq_right ht, canonicalDiracState_before β h q hq ω
      ⟨le_min t.coe_nonneg zero_le_one, (min_le_left _ _).trans (lt_of_not_ge ht).le⟩]
    ring

end Paper
