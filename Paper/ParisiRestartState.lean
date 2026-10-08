module

public import Paper.ParisiStateStability

@[expose] public section

/-! Actual fresh-Brownian restart states at arbitrary physical times.
Collapsing overlaps before the restart time transports their cumulative mass
to elapsed time zero; the existing genuine Picard construction then applies.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper

def parisiRestartOverlap (a : ℝ) (ha : 0 ≤ a) (q : Overlap) : Overlap :=
  ⟨max ((q : ℝ) - a) 0, le_max_right _ _,
    max_le (by linarith [q.property.2]) zero_le_one⟩

theorem continuous_parisiRestartOverlap (a : ℝ) (ha : 0 ≤ a) :
    Continuous (parisiRestartOverlap a ha) :=
  ((continuous_subtype_val.sub continuous_const).max continuous_const).subtype_mk _

def parisiRestartMeasure (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) : ParisiMeasure :=
  μ.map (parisiRestartOverlap a ha)

/-- The exact CDF of the actual overlap pushforward, including all atoms at
or before the restart time. No distributional representation is assumed. -/
theorem parisiCDF_restart (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ) (hr : 0 ≤ r) :
    parisiCDF (parisiRestartMeasure μ a ha) r = parisiCDF μ (a + r) := by
  have hS : MeasurableSet {q : Overlap | (q : ℝ) ≤ r} :=
    (isClosed_le continuous_subtype_val continuous_const).measurableSet
  unfold parisiCDF parisiRestartMeasure
  rw [ProbabilityMeasure.map_apply' μ (continuous_parisiRestartOverlap a ha).measurable.aemeasurable hS]
  congr 1
  congr 1
  ext q
  change max ((q : ℝ) - a) 0 ≤ r ↔ (q : ℝ) ≤ a + r
  rw [max_le_iff]
  constructor
  · intro h
    linarith [h.1]
  · intro h
    exact ⟨by linarith, hr⟩

def parisiRestartGradient (β : ℝ) (μ : ParisiMeasure) (a : ℝ) : ℝ → ℝ → ℝ :=
  fun r y => parisiGradient β μ (a + r, y)

theorem continuous_parisiRestartGradient (β : ℝ) (μ : ParisiMeasure) (a : ℝ) :
    Continuous (Function.uncurry (parisiRestartGradient β μ a)) :=
  (continuous_parisiGradient β μ).comp ((continuous_const.add continuous_fst).prodMk continuous_snd)

theorem norm_parisiRestartGradient_le_one (β : ℝ) (μ : ParisiMeasure) (a r y : ℝ) :
    ‖parisiRestartGradient β μ a r y‖ ≤ 1 := norm_parisiGradient_le_one β μ (a + r, y)

theorem lipschitzWith_parisiRestartGradient (β : ℝ) (μ : ParisiMeasure) (a r : ℝ) :
    LipschitzWith 1 (parisiRestartGradient β μ a r) :=
  lipschitzWith_parisiGradient_all β μ (a + r)

def canonicalParisiRestartState (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    ℝ≥0 → BrownianSample → ℝ :=
  canonicalParisiItoState β x (parisiRestartMeasure μ a ha) (parisiRestartGradient β μ a)
    (continuous_parisiRestartGradient β μ a) (norm_parisiRestartGradient_le_one β μ a)
    (lipschitzWith_parisiRestartGradient β μ a)

def canonicalParisiRestartDrift (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    ℝ≥0 → BrownianSample → ℝ :=
  canonicalParisiItoDrift β x (parisiRestartMeasure μ a ha) (parisiRestartGradient β μ a)
    (continuous_parisiRestartGradient β μ a) (norm_parisiRestartGradient_le_one β μ a)
    (lipschitzWith_parisiRestartGradient β μ a)

@[simp] theorem canonicalParisiRestartState_zero (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (omega : BrownianSample) :
    canonicalParisiRestartState β x μ a ha 0 omega = x :=
  canonicalParisiItoState_zero β x _ _ _ _ _ omega

theorem boundedDriftItoCharacteristics_canonicalParisiRestartState
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure canonicalBrownianFiltration
      (canonicalParisiRestartState β x μ a ha) (canonicalParisiRestartDrift β x μ a ha)
      (canonicalDiracShiftMartingale β 0) β :=
  boundedDriftItoCharacteristics_canonicalParisiState β x _ _ _ _ _

theorem continuous_canonicalParisiRestartState (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (omega : BrownianSample) :
    Continuous (fun r => canonicalParisiRestartState β x μ a ha r omega) :=
  continuous_canonicalParisiItoState β x _ _ _ _ _ omega

theorem measurable_canonicalParisiRestartState (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) :
    Measurable (Function.uncurry (canonicalParisiRestartState β x μ a ha)) :=
  measurable_canonicalParisiItoState β x _ _ _ _ _

theorem stronglyAdapted_canonicalParisiRestartState (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) :
    StronglyAdapted canonicalBrownianFiltration (canonicalParisiRestartState β x μ a ha) :=
  stronglyAdapted_canonicalParisiItoState β x _ _ _ _ _

theorem integrable_canonicalParisiRestartState (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (r : ℝ≥0) :
    Integrable (canonicalParisiRestartState β x μ a ha r) canonicalBrownianMeasure :=
  integrable_canonicalParisiItoState β x _ _ _ _ _ r

theorem canonicalParisiRestartDrift_eq (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (r : ℝ≥0) (hr : (r : ℝ) ≤ 1) (omega : BrownianSample) :
    canonicalParisiRestartDrift β x μ a ha r omega = β ^ 2 * parisiCDF μ (a + r) *
      parisiGradient β μ (a + r, canonicalParisiRestartState β x μ a ha r omega) := by
  unfold canonicalParisiRestartDrift canonicalParisiItoDrift
  rw [ite_eq_left hr, parisiCDF_restart μ a ha r r.coe_nonneg]
  rfl

/-- The actual relative-time optimal feedback, expressed at elapsed time.
It evaluates the original PDE gradient at the shifted physical time. -/
def canonicalParisiRestartControl (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ) (omega : BrownianSample) : ℝ :=
  parisiGradient β μ (a + r, canonicalParisiRestartState β x μ a ha r.toNNReal omega)

theorem isParisiAdmissibleControl_canonicalParisiRestartControl
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) :
    IsParisiAdmissibleControl (canonicalParisiRestartControl β x μ a ha) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro omega
    exact (continuous_parisiGradient β μ).comp ((continuous_const.add continuous_id).prodMk
      ((continuous_canonicalParisiRestartState β x μ a ha omega).comp continuous_real_toNNReal))
  · intro r
    change StronglyMeasurable[canonicalBrownianFiltration r]
      (fun omega => parisiGradient β μ (a + r,
        canonicalParisiRestartState β x μ a ha (r : ℝ).toNNReal omega))
    rw [Real.toNNReal_coe]
    exact (continuous_parisiGradient β μ).comp_stronglyMeasurable
      (stronglyMeasurable_const.prodMk (stronglyAdapted_canonicalParisiRestartState β x μ a ha r))
  · have hstate : Measurable (fun p : ℝ × BrownianSample =>
        canonicalParisiRestartState β x μ a ha p.1.toNNReal p.2) :=
      (measurable_canonicalParisiRestartState β x μ a ha).comp
        (f := fun p : ℝ × BrownianSample => (p.1.toNNReal, p.2))
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    exact (continuous_parisiGradient β μ).measurable.comp
      ((measurable_const.add measurable_fst).prodMk hstate)
  · intro r omega
    exact norm_parisiGradient_le_one β μ _

/-- The drift identity required by relative-time HJB verification, at
every time in the entire physical restart horizon. -/
theorem canonicalParisiRestartDrift_eq_control (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (1 - a))
    (omega : BrownianSample) :
    canonicalParisiRestartDrift β x μ a ha.1 r.toNNReal omega =
      β ^ 2 * parisiCDF μ (a + r) * canonicalParisiRestartControl β x μ a ha.1 r omega := by
  rw [canonicalParisiRestartDrift_eq β x μ a ha.1 r.toNNReal
    (by rw [Real.coe_toNNReal _ hr.1]; linarith [ha.1, hr.2]), Real.coe_toNNReal _ hr.1]
  rfl

/-- CDF transport inside the actual elapsed-time integral. -/
theorem integral_parisiCDF_restart_mul (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (b : ℝ) (hb : 0 ≤ b) (f : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..b, parisiCDF (parisiRestartMeasure μ a ha) r * f r) =
      ∫ r in (0 : ℝ)..b, parisiCDF μ (a + r) * f r := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hb] at hr
  dsimp only
  rw [parisiCDF_restart μ a ha r hr.1]

/-- The actual controlled restart state for any admissible control. -/
def canonicalParisiRestartControlledState (β x : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (A : ℝ → BrownianSample → ℝ) : ℝ≥0 → BrownianSample → ℝ :=
  canonicalParisiControlledState β x (parisiRestartMeasure μ a ha) A

def canonicalParisiRestartControlledDrift (β : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (A : ℝ → BrownianSample → ℝ) : ℝ≥0 → BrownianSample → ℝ :=
  canonicalParisiControlDrift β (parisiRestartMeasure μ a ha) A

theorem boundedDriftItoCharacteristics_canonicalParisiRestartControlledState
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure canonicalBrownianFiltration
      (canonicalParisiRestartControlledState β x μ a ha A)
      (canonicalParisiRestartControlledDrift β μ a ha A) (canonicalDiracShiftMartingale β 0) β :=
  boundedDriftItoCharacteristics_canonicalParisiControlledState β x _ A hA

@[simp] theorem canonicalParisiRestartControlledState_zero
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (A : ℝ → BrownianSample → ℝ) (omega : BrownianSample) :
    canonicalParisiRestartControlledState β x μ a ha A 0 omega = x :=
  canonicalParisiControlledState_zero β x _ A omega

theorem canonicalParisiRestartControlledDrift_eq (β : ℝ) (μ : ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) (1 - a)) (omega : BrownianSample) :
    canonicalParisiRestartControlledDrift β μ a ha.1 A r.toNNReal omega =
      β ^ 2 * parisiCDF μ (a + r) * A r omega := by
  unfold canonicalParisiRestartControlledDrift canonicalParisiControlDrift
  rw [Real.coe_toNNReal _ hr.1, ite_eq_left (by linarith [ha.1, hr.2] : r ≤ 1),
    parisiCDF_restart μ a ha.1 r hr.1]

theorem canonicalParisiRestartControlledState_integral_equation
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (A : ℝ → BrownianSample → ℝ) (r : ℝ≥0) (hr : (r : ℝ) ≤ 1) (omega : BrownianSample) :
    canonicalParisiRestartControlledState β x μ a ha A r omega = x + β * canonicalBrownian r omega +
      β ^ 2 * ∫ s in (0 : ℝ)..(r : ℝ), parisiCDF μ (a + s) * A s omega := by
  unfold canonicalParisiRestartControlledState canonicalParisiControlledState
  rw [integratedDrift_canonicalParisiControlDrift, min_eq_left hr,
    integral_parisiCDF_restart_mul μ a ha r r.coe_nonneg]
  ring

theorem integrable_canonicalParisiRestartControlledState
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) (r : ℝ≥0) :
    Integrable (canonicalParisiRestartControlledState β x μ a ha A r) canonicalBrownianMeasure :=
  integrable_canonicalParisiControlledState β x _ A hA r

/-- The shifted PDE feedback is an actual admissible control and its
controlled state is exactly the genuine restarted Picard state. -/
theorem canonicalParisiRestartControlledState_optimal_eq
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ≥0) (omega : BrownianSample) :
    canonicalParisiRestartControlledState β x μ a ha
      (canonicalParisiRestartControl β x μ a ha) r omega =
      canonicalParisiRestartState β x μ a ha r omega := by
  have he : canonicalParisiControlDrift β (parisiRestartMeasure μ a ha)
      (canonicalParisiRestartControl β x μ a ha) = canonicalParisiRestartDrift β x μ a ha := by
    funext s omega
    unfold canonicalParisiControlDrift canonicalParisiRestartDrift canonicalParisiItoDrift
    by_cases hs : (s : ℝ) ≤ 1
    · simp only [ite_eq_left hs, canonicalParisiRestartControl, Real.toNNReal_coe]
      rfl
    · simp only [ite_eq_right hs]
  unfold canonicalParisiRestartControlledState canonicalParisiControlledState
  rw [he]
  have hs := canonicalParisiItoState_decomposition β x (parisiRestartMeasure μ a ha)
    (parisiRestartGradient β μ a) (continuous_parisiRestartGradient β μ a)
    (norm_parisiRestartGradient_le_one β μ a) (lipschitzWith_parisiRestartGradient β μ a) r omega
  rw [canonicalParisiItoState_zero] at hs
  exact hs.symm

theorem canonicalParisiRestartState_integral_equation
    (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r : ℝ≥0) (hr : (r : ℝ) ≤ 1) (omega : BrownianSample) :
    canonicalParisiRestartState β x μ a ha r omega = x + β * canonicalBrownian r omega +
      β ^ 2 * ∫ s in (0 : ℝ)..(r : ℝ), parisiCDF μ (a + s) *
        parisiGradient β μ (a + s, canonicalParisiRestartState β x μ a ha s.toNNReal omega) := by
  rw [← canonicalParisiRestartControlledState_optimal_eq β x μ a ha r omega]
  exact canonicalParisiRestartControlledState_integral_equation β x μ a ha
    (canonicalParisiRestartControl β x μ a ha) r hr omega

end Paper
