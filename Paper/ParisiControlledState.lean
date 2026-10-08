module

public import Paper.DiracShift
public import Paper.ParisiControlConvexity
public import Paper.ItoStateIntegrability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Actual bounded adapted controls and their Brownian controlled states. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper

/-- Concrete regularity and adaptedness of the control, not characteristics
or verification conclusions of the resulting state. -/
structure IsParisiAdmissibleControl (A : ℝ → BrownianSample → ℝ) : Prop where
  continuous_paths : ∀ omega, Continuous (fun s => A s omega)
  adapted : StronglyAdapted canonicalBrownianFiltration (fun s omega => A s omega)
  measurable : Measurable (Function.uncurry A)
  bounded : ∀ s omega, ‖A s omega‖ ≤ 1

def canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (t : ℝ≥0) (omega : BrownianSample) : ℝ :=
  if (t : ℝ) ≤ 1 then β ^ 2 * parisiCDF μ t * A t omega else 0

def canonicalParisiControlledState (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (t : ℝ≥0) (omega : BrownianSample) : ℝ :=
  h + integratedDrift (canonicalParisiControlDrift β μ A) t omega +
    β * canonicalBrownian t omega

theorem measurable_canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Measurable (Function.uncurry (canonicalParisiControlDrift β μ A)) := by
  unfold canonicalParisiControlDrift Function.uncurry
  apply Measurable.ite
  · exact measurableSet_le measurable_fst.coe_nnreal_real measurable_const
  · exact (measurable_const.mul ((parisiCDF_measurable μ).comp measurable_fst.coe_nnreal_real)).mul
      (hA.measurable.comp (measurable_fst.coe_nnreal_real.prodMk measurable_snd))
  · exact measurable_const

theorem norm_canonicalParisiControlDrift_le (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (t : ℝ≥0) (omega : BrownianSample) :
    ‖canonicalParisiControlDrift β μ A t omega‖ ≤ β ^ 2 := by
  unfold canonicalParisiControlDrift
  split_ifs
  · rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg β),
      Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
    calc
      _ ≤ β ^ 2 * 1 * 1 := by gcongr; exact parisiCDF_le_one μ t; exact hA.bounded t omega
      _ = _ := by ring
  · simpa only [norm_zero] using sq_nonneg β

theorem intervalIntegrable_canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (a b : ℝ) (omega : BrownianSample) :
    IntervalIntegrable (fun s : ℝ => canonicalParisiControlDrift β μ A s.toNNReal omega)
      volume a b := by
  apply (intervalIntegrable_const (c := β ^ 2)).mono_fun'
  · exact ((measurable_canonicalParisiControlDrift β μ A hA).comp
      (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  · exact .of_forall (fun s => norm_canonicalParisiControlDrift_le β μ A hA s.toNNReal omega)

theorem integratedDrift_canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (t : ℝ≥0) (omega : BrownianSample) :
    integratedDrift (canonicalParisiControlDrift β μ A) t omega =
      β ^ 2 * ∫ s in 0..min (t : ℝ) 1, parisiCDF μ s * A s omega := by
  unfold integratedDrift
  have he : (∫ s in Icc (0 : ℝ) (t : ℝ), canonicalParisiControlDrift β μ A s.toNNReal omega) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), (Icc (0 : ℝ) 1).indicator
        (fun s => β ^ 2 * (parisiCDF μ s * A s omega)) s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    unfold canonicalParisiControlDrift
    rw [Real.coe_toNNReal s hs.1]
    by_cases hs1 : s ≤ 1
    · rw [ite_eq_left hs1, indicator_of_mem (show s ∈ Icc (0 : ℝ) 1 from ⟨hs.1, hs1⟩)]
      ring
    · rw [ite_eq_right hs1, indicator_of_notMem (show s ∉ Icc (0 : ℝ) 1 from fun hx => hs1 hx.2)]
  rw [he, setIntegral_indicator measurableSet_Icc, Icc_inter_Icc, max_self,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_min t.coe_nonneg zero_le_one),
    intervalIntegral.integral_const_mul]

@[simp] theorem canonicalParisiControlledState_zero (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (omega : BrownianSample) :
    canonicalParisiControlledState β h μ A 0 omega = h := by
  simp [canonicalParisiControlledState, integratedDrift]

theorem canonicalParisiControlledState_terminal (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (omega : BrownianSample) :
    canonicalParisiControlledState β h μ A 1 omega = h + β * canonicalBrownian 1 omega +
      parisiControlDrift β μ A omega := by
  rw [canonicalParisiControlledState, integratedDrift_canonicalParisiControlDrift]
  simp only [NNReal.coe_one, min_self, parisiControlDrift]
  ring

theorem continuous_canonicalParisiControlledState (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A)
    (omega : BrownianSample) : Continuous (fun t => canonicalParisiControlledState β h μ A t omega) := by
  have hprim := intervalIntegral.continuous_primitive
    (fun a b => intervalIntegrable_canonicalParisiControlDrift β μ A hA a b omega) (0 : ℝ)
  have hi : Continuous (fun t : ℝ≥0 => integratedDrift (canonicalParisiControlDrift β μ A) t omega) := by
    have he (t : ℝ≥0) : integratedDrift (canonicalParisiControlDrift β μ A) t omega =
        ∫ s in 0..(t : ℝ), canonicalParisiControlDrift β μ A s.toNNReal omega := by
      rw [integratedDrift, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le t.coe_nonneg]
    simp_rw [he]
    exact hprim.comp continuous_subtype_val
  exact (continuous_const.add hi).add ((continuous_canonicalBrownian omega).const_mul β)

/-- Continuous adapted controls are progressively measurable. Multiplication
by the measurable CDF and the deterministic cutoff preserves this property. -/
theorem isStronglyProgressive_canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    IsStronglyProgressive canonicalBrownianFiltration (canonicalParisiControlDrift β μ A) := by
  have hp := hA.adapted.isStronglyProgressive_of_continuous
    (fun omega => (hA.continuous_paths omega).comp continuous_subtype_val)
  intro t
  let : MeasurableSpace BrownianSample := canonicalBrownianFiltration t
  have htime : Measurable (fun p : Iic t × BrownianSample => ((p.1 : ℝ≥0) : ℝ)) :=
    measurable_fst.subtype_coe.coe_nnreal_real
  have hAt : Measurable (fun p : Iic t × BrownianSample => A (p.1 : ℝ≥0) p.2) :=
    (hp t).measurable
  apply Measurable.stronglyMeasurable
  unfold canonicalParisiControlDrift
  apply Measurable.ite
  · exact measurableSet_le htime measurable_const
  · exact (measurable_const.mul ((parisiCDF_measurable μ).comp htime)).mul hAt
  · exact measurable_const

/-- Adaptedness of the time integral is proved from progressive measurability
on the past; it is not assumed as a state characteristic. -/
theorem stronglyAdapted_integrated_canonicalParisiControlDrift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    StronglyAdapted canonicalBrownianFiltration (integratedDrift (canonicalParisiControlDrift β μ A)) := by
  have hp := isStronglyProgressive_canonicalParisiControlDrift β μ A hA
  intro t
  let : MeasurableSpace BrownianSample := canonicalBrownianFiltration t
  let clamp : ℝ≥0 → Iic t := fun s => ⟨min s t, by exact min_le_right s t⟩
  have hclamp : Measurable clamp := by
    apply Measurable.subtype_mk
    exact measurable_id.min measurable_const
  have hm : Measurable (Function.uncurry (fun s omega =>
      canonicalParisiControlDrift β μ A (min s t) omega)) :=
    (hp t).measurable.comp ((hclamp.comp measurable_fst).prodMk measurable_snd)
  have hi := stronglyMeasurable_integratedDrift hm t
  convert hi using 1
  funext omega
  unfold integratedDrift
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hst : s.toNNReal ≤ t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal s hs.1]
    exact hs.2
  dsimp only
  rw [min_eq_left hst]

theorem stronglyAdapted_canonicalParisiControlledState (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    StronglyAdapted canonicalBrownianFiltration (canonicalParisiControlledState β h μ A) := by
  intro t
  exact (stronglyMeasurable_const.add
    (stronglyAdapted_integrated_canonicalParisiControlDrift β μ A hA t)).add
    ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_canonicalBrownian s).stronglyMeasurable) t).const_mul β)

theorem measurable_canonicalParisiControlledState (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Measurable (Function.uncurry (canonicalParisiControlledState β h μ A)) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (continuous_canonicalParisiControlledState β h μ A hA)
  intro t
  exact ((stronglyAdapted_canonicalParisiControlledState β h μ A hA t).mono
    (canonicalBrownianFiltration.le t)).measurable

/-- Exact characteristic decomposition for the actual controlled state. -/
theorem canonicalParisiControlledState_decomposition (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (t : ℝ≥0) (omega : BrownianSample) :
    canonicalParisiControlledState β h μ A t omega =
      canonicalParisiControlledState β h μ A 0 omega +
      integratedDrift (canonicalParisiControlDrift β μ A) t omega +
      canonicalDiracShiftMartingale β 0 t omega := by
  rw [canonicalParisiControlledState_zero]
  simp only [canonicalParisiControlledState,
    canonicalDiracShiftMartingale, zero_add, canonicalBrownian_zero, sub_zero]

/-- All stochastic characteristics are instantiated on the constructed
canonical Wiener space, for every admissible bounded adapted control. -/
theorem boundedDriftItoCharacteristics_canonicalParisiControlledState
    (β h : ℝ) (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ)
    (hA : IsParisiAdmissibleControl A) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure canonicalBrownianFiltration
      (canonicalParisiControlledState β h μ A) (canonicalParisiControlDrift β μ A)
      (canonicalDiracShiftMartingale β 0) β := by
  refine ⟨continuous_canonicalParisiControlledState β h μ A hA,
    stronglyAdapted_canonicalParisiControlledState β h μ A hA,
    measurable_canonicalParisiControlDrift β μ A hA, ?_,
    canonicalParisiControlledState_decomposition β h μ A, ?_,
    memLp_canonicalDiracShiftMartingale β 0, ?_⟩
  · refine ⟨(β ^ 2).toNNReal, ?_⟩
    intro s omega
    rw [Real.coe_toNNReal _ (sq_nonneg β)]
    exact norm_canonicalParisiControlDrift_le β μ A hA s omega
  · have hF : canonicalBrownianShiftFiltration 0 = canonicalBrownianFiltration := by
      apply Filtration.ext
      funext t
      change canonicalBrownianFiltration (0 + t) = canonicalBrownianFiltration t
      rw [zero_add]
    simpa only [hF] using martingale_canonicalDiracShiftMartingale β 0
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale β 0 T r using 1
    ext omega
    simp [integral_const, Measure.real, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul,
      ENNReal.toReal_min, mul_comm]

/-- Absolute integrability of every state endpoint follows from actual
bounded drift and the actual Brownian second moment. -/
theorem integrable_canonicalParisiControlledState
    (β h : ℝ) (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ)
    (hA : IsParisiAdmissibleControl A) (t : ℝ≥0) :
    Integrable (canonicalParisiControlledState β h μ A t) canonicalBrownianMeasure := by
  apply (boundedDriftItoCharacteristics_canonicalParisiControlledState β h μ A hA).integrable_state
  have he : canonicalParisiControlledState β h μ A 0 = (fun _ => h) :=
    funext (canonicalParisiControlledState_zero β h μ A)
  rw [he]
  exact integrable_const h

/-- Any continuous endpoint observable with at most linear growth is
integrable along the actual controlled state. -/
theorem integrable_canonicalParisiControlledState_observable
    (β h : ℝ) (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ)
    (hA : IsParisiAdmissibleControl A) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Continuous f) (C L : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ C + L * ‖x‖) :
    Integrable (fun omega => f (canonicalParisiControlledState β h μ A t omega))
      canonicalBrownianMeasure := by
  exact ((integrable_const C).add
    ((integrable_canonicalParisiControlledState β h μ A hA t).norm.const_mul L)).mono'
    (hf.comp_aestronglyMeasurable
      (((stronglyAdapted_canonicalParisiControlledState β h μ A hA t).mono
        (canonicalBrownianFiltration.le t)).aestronglyMeasurable))
    (.of_forall fun omega => hb _)

/-- A real-time control from an actual nonnegative-time adapted process.
This keeps the HJB functional's real-time integral interface. -/
def parisiControlFromNNReal (A : ℝ≥0 → BrownianSample → ℝ) : ℝ → BrownianSample → ℝ :=
  fun s omega => A s.toNNReal omega

theorem isParisiAdmissibleControl_fromNNReal (A : ℝ≥0 → BrownianSample → ℝ)
    (hcont : ∀ omega, Continuous (fun s => A s omega))
    (hadapt : StronglyAdapted canonicalBrownianFiltration A)
    (hbound : ∀ s omega, ‖A s omega‖ ≤ 1) :
    IsParisiAdmissibleControl (parisiControlFromNNReal A) := by
  have hmeas : Measurable (Function.uncurry A) := by
    apply measurable_uncurry_of_continuous_of_measurable hcont
    intro t
    exact ((hadapt t).mono (canonicalBrownianFiltration.le t)).measurable
  refine ⟨fun omega => (hcont omega).comp continuous_real_toNNReal, ?_, ?_, ?_⟩
  · simpa only [parisiControlFromNNReal, Real.toNNReal_coe] using hadapt
  · exact hmeas.comp (measurable_real_toNNReal.comp measurable_fst |>.prodMk measurable_snd)
  · intro s omega
    exact hbound s.toNNReal omega

end Paper
