module

public import Paper.ParisiControlStability
public import Paper.ParisiSelectedMoment
public import Paper.JTFubini
public import Paper.ParisiSelectedGFubini

@[expose] public section

/-! Deterministic Fubini bridge for the actual optimal-control derivative.
The terminal pairing identity is isolated explicitly; the actual gradient
martingale proves it in the stochastic application. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

/-- The bounded measurable time/sample Fubini interchange used below. -/
theorem integral_weighted_control_intervalIntegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ → ℝ) (hc : Measurable c) (hcb : ∀ s, ‖c s‖ ≤ 1)
    (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1)
    (g : Ω → ℝ) (hg : Measurable g) (hgb : ∀ omega, ‖g omega‖ ≤ 1) :
    (∫ omega, g omega * (∫ s in (0 : ℝ)..1, c s * A s omega) ∂P) =
      ∫ s in (0 : ℝ)..1, c s * (∫ omega, g omega * A s omega ∂P) := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure τ := isFiniteMeasure_restrict.mpr (by
    simp only [Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_ne_top)
  let f : Ω → ℝ → ℝ := fun omega s => g omega * (c s * A s omega)
  have hm : Measurable (Function.uncurry f) :=
    (hg.comp measurable_fst).mul ((hc.comp measurable_snd).mul (hA.comp measurable_swap))
  have hi : Integrable (Function.uncurry f) (P.prod τ) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact .of_forall fun p => by
      change ‖g p.1 * (c p.2 * A p.2 p.1)‖ ≤ 1
      rw [norm_mul, norm_mul]
      have hx : ‖c p.2‖ * ‖A p.2 p.1‖ ≤ 1 :=
        (mul_le_mul (hcb p.2) (hb p.2 p.1) (norm_nonneg _) zero_le_one).trans_eq (by ring)
      exact (mul_le_mul (hgb p.1) hx
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (by ring)
  calc
    _ = ∫ omega, ∫ s, f omega s ∂τ ∂P := by
      apply integral_congr_ae
      exact .of_forall fun omega => by
        dsimp [f, τ]
        rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]
    _ = ∫ s, ∫ omega, f omega s ∂P ∂τ := integral_integral_swap hi
    _ = _ := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      apply integral_congr_ae
      exact .of_forall fun s => by
        dsimp only [f]
        simp_rw [show ∀ omega, g omega * (c s * A s omega) =
          c s * (g omega * A s omega) by intro omega; ring]
        rw [integral_const_mul]

theorem integral_parisiControlDrift_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s omega, ‖A s omega‖ ≤ 1)
    (g : Ω → ℝ) (hg : Measurable g) (hgb : ∀ omega, ‖g omega‖ ≤ 1) :
    (∫ omega, g omega * parisiControlDrift β μ A omega ∂P) =
      β ^ 2 * ∫ s in (0 : ℝ)..1, parisiCDF μ s *
        (∫ omega, g omega * A s omega ∂P) := by
  unfold parisiControlDrift
  simp_rw [show ∀ omega, g omega * (β ^ 2 *
      (∫ s in (0 : ℝ)..1, parisiCDF μ s * A s omega)) =
      β ^ 2 * (g omega * (∫ s in (0 : ℝ)..1, parisiCDF μ s * A s omega)) by
        intro omega; ring]
  rw [integral_const_mul]
  congr 1
  apply integral_weighted_control_intervalIntegral P _ (parisiCDF_measurable μ) _ A hA hb g hg hgb
  intro s
  rw [Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
  exact parisiCDF_le_one μ s

theorem integral_parisiControlCost_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℝ) (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s omega, ‖A s omega‖ ≤ 1) :
    (∫ omega, parisiControlCost β μ A omega ∂P) =
      β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, parisiCDF μ s *
        (∫ omega, A s omega ^ 2 ∂P) := by
  unfold parisiControlCost
  rw [integral_const_mul]
  congr 1
  have hf := integral_weighted_control_intervalIntegral P (parisiCDF μ)
    (parisiCDF_measurable μ) (fun s => by
      rw [Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
      exact parisiCDF_le_one μ s)
    (fun s omega => A s omega ^ 2) (hA.pow_const 2)
    (fun s omega => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hb s omega))
    (fun _ => 1) measurable_const (fun _ => by norm_num)
  simpa only [one_mul] using hf

theorem parisiControlSecondMoment_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ParisiMeasure) (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A)) (hb : ∀ s omega, ‖A s omega‖ ≤ 1) :
    IntervalIntegrable (fun s => parisiCDF μ s * (∫ omega, A s omega ^ 2 ∂P))
      volume (0 : ℝ) 1 := by
  have hm : Measurable (fun s => ∫ omega, A s omega ^ 2 ∂P) :=
    (hA.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((parisiCDF_measurable μ).mul hm).aestronglyMeasurable
  exact .of_forall fun s => by
    have hn : ‖∫ omega, A s omega ^ 2 ∂P‖ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const (μ := P)
        (f := fun omega => A s omega ^ 2) (C := 1) (.of_forall fun omega => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hb s omega))
    change ‖parisiCDF μ s * (∫ omega, A s omega ^ 2 ∂P)‖ ≤ 1
    rw [norm_mul, Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
    exact (mul_le_mul (parisiCDF_le_one μ s) hn (norm_nonneg _) zero_le_one).trans_eq (by ring)

/-- Only the terminal pairing is left explicit. Every measurable/Fubini
and absolute-integrability hypothesis follows from the actual control bound. -/
theorem integral_parisiAffineControlDerivative_zero_of_terminal_pairing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B)
    (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1) (μ ν : ParisiMeasure)
    (hpair : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ omega, Real.tanh (h + β * B omega + parisiControlDrift β μ A omega) *
        A s omega ∂P) = ∫ omega, A s omega ^ 2 ∂P) :
    (∫ omega, parisiAffineControlDerivative β h B A μ ν 0 omega ∂P) =
      β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, (parisiCDF ν s - parisiCDF μ s) *
        (∫ omega, A s omega ^ 2 ∂P) := by
  let g := fun omega => Real.tanh (h + β * B omega + parisiControlDrift β μ A omega)
  have hg : Measurable g := gaussian_continuous_tanh.measurable.comp
    ((measurable_const.add (hB.const_mul β)).add (measurable_parisiControlDrift β μ A hA))
  have hgb : ∀ omega, ‖g omega‖ ≤ 1 := fun omega => by
    simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one _).le
  have hid (η : ParisiMeasure) : Integrable (fun omega => g omega * parisiControlDrift β η A omega) P := by
    apply (integrable_const (β ^ 2)).mono'
      (hg.mul (measurable_parisiControlDrift β η A hA)).aestronglyMeasurable
    exact .of_forall fun omega => by
      change ‖g omega * parisiControlDrift β η A omega‖ ≤ β ^ 2
      rw [norm_mul]
      exact (mul_le_mul (hgb omega) (parisiControlDrift_norm_le β η A hb omega)
        (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hic (η : ParisiMeasure) : Integrable (parisiControlCost β η A) P :=
    (integrable_const (β ^ 2 / 2)).mono'
      (measurable_parisiControlCost β η A hA).aestronglyMeasurable
      (.of_forall fun omega => parisiControlCost_norm_le β η A hb omega)
  have he : (fun omega => parisiAffineControlDerivative β h B A μ ν 0 omega) =
      (fun omega => (g omega * parisiControlDrift β ν A omega -
        g omega * parisiControlDrift β μ A omega) -
        (parisiControlCost β ν A omega - parisiControlCost β μ A omega)) := by
    funext omega
    dsimp [parisiAffineControlDerivative, g]
    simp only [zero_mul, add_zero]
    ring
  have hidiff : Integrable (fun omega => g omega * parisiControlDrift β ν A omega -
      g omega * parisiControlDrift β μ A omega) P := (hid ν).sub (hid μ)
  have hicdiff : Integrable (fun omega => parisiControlCost β ν A omega -
      parisiControlCost β μ A omega) P := (hic ν).sub (hic μ)
  rw [he, integral_sub hidiff hicdiff,
    integral_sub (hid ν) (hid μ), integral_sub (hic ν) (hic μ),
    integral_parisiControlDrift_mul P β ν A hA hb g hg hgb,
    integral_parisiControlDrift_mul P β μ A hA hb g hg hgb,
    integral_parisiControlCost_eq P β ν A hA hb, integral_parisiControlCost_eq P β μ A hA hb]
  have hp (η : ParisiMeasure) :
      (∫ s in (0 : ℝ)..1, parisiCDF η s * (∫ omega, g omega * A s omega ∂P)) =
      ∫ s in (0 : ℝ)..1, parisiCDF η s * (∫ omega, A s omega ^ 2 ∂P) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    dsimp only [g]
    rw [hpair s hs]
  rw [hp ν, hp μ]
  have him := parisiControlSecondMoment_intervalIntegrable P μ A hA hb
  have hin := parisiControlSecondMoment_intervalIntegrable P ν A hA hb
  rw [show (fun s => (parisiCDF ν s - parisiCDF μ s) * (∫ omega, A s omega ^ 2 ∂P)) =
    (fun s => parisiCDF ν s * (∫ omega, A s omega ^ 2 ∂P) -
      parisiCDF μ s * (∫ omega, A s omega ^ 2 ∂P)) by funext s; ring,
    intervalIntegral.integral_sub hin him]
  ring

/-- On the physical time strip the actual feedback equals the constructed
PDE gradient evaluated at its actual Brownian state. -/
theorem selectedParisiFeedbackControl_apply (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (omega : BrownianSample) :
    selectedParisiFeedbackControl β h μ s omega =
      parisiGradient β μ (s, selectedParisiStateReal β h hβ μ omega s) := by
  unfold selectedParisiFeedbackControl canonicalParisiFeedbackControl
    parisiControlFromNNReal canonicalParisiFeedbackNNReal
  rw [Real.coe_toNNReal _ hs.1, min_eq_left hs.2]
  change parisiGradient β μ ((s.toNNReal : ℝ), selectedParisiItoState β h hβ μ s.toNNReal omega) = _
  rw [selectedParisiItoState_eq β h hβ μ
    (by simpa only [Real.coe_toNNReal _ hs.1] using hs.2) omega]
  rw [Real.coe_toNNReal _ hs.1]

theorem selectedParisiFeedbackControl_secondMoment_eq (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ omega, selectedParisiFeedbackControl β h μ s omega ^ 2 ∂canonicalBrownianMeasure) =
      selectedParisiSecondMoment β h hβ μ s := by
  unfold selectedParisiSecondMoment
  apply integral_congr_ae
  exact .of_forall fun omega => by
    dsimp only
    rw [selectedParisiFeedbackControl_apply β h hβ μ s hs omega]

/-- The exact terminal endpoint in the fixed-control payoff is the actual
PDE-selected state, by equality of their genuine integral decompositions. -/
theorem selectedParisiFeedbackControl_terminal_state_eq (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (omega : BrownianSample) :
    h + β * canonicalBrownian 1 omega +
      parisiControlDrift β μ (selectedParisiFeedbackControl β h μ) omega =
      selectedParisiStateReal β h hβ μ omega 1 := by
  rw [← canonicalParisiControlledState_terminal]
  unfold selectedParisiFeedbackControl
  rw [canonicalParisiControlledState_feedback_eq β h μ
    (fun t x => parisiGradient β μ (t, x)) (continuous_parisiGradient β μ)
    (fun t x => norm_parisiGradient_le_one β μ (t, x))
    (lipschitzWith_parisiGradient_all β μ),
    canonicalParisiItoState_eq β h μ
      (fun t x => parisiGradient β μ (t, x)) (continuous_parisiGradient β μ)
      (fun t x => norm_parisiGradient_le_one β μ (t, x))
      (lipschitzWith_parisiGradient_all β μ) (by norm_num)]
  rfl

/-- The full deterministic bridge for the actual PDE feedback. The sole
premise is the terminal pairing subsequently supplied by the actual
gradient martingale; all Fubini and moment identifications are proved. -/
theorem integral_selectedParisiControlDerivative_of_terminal_pairing
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure)
    (hpair : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ omega, Real.tanh (h + β * canonicalBrownian 1 omega +
        parisiControlDrift β μ (selectedParisiFeedbackControl β h μ) omega) *
        selectedParisiFeedbackControl β h μ s omega ∂canonicalBrownianMeasure) =
      ∫ omega, selectedParisiFeedbackControl β h μ s omega ^ 2 ∂canonicalBrownianMeasure) :
    (∫ omega, parisiAffineControlDerivative β h (canonicalBrownian 1)
      (selectedParisiFeedbackControl β h μ) μ ν 0 omega ∂canonicalBrownianMeasure) =
      β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, (parisiCDF ν s - parisiCDF μ s) *
        selectedParisiSecondMoment β h hβ μ s := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl β h μ
  rw [integral_parisiAffineControlDerivative_zero_of_terminal_pairing canonicalBrownianMeasure
    β h (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    (selectedParisiFeedbackControl β h μ) hA.measurable hA.bounded μ ν hpair]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  dsimp only
  rw [selectedParisiFeedbackControl_secondMoment_eq β h hβ μ s hs]

theorem integral_selectedParisiControlDerivative_sub_correction_of_terminal_pairing
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure)
    (hpair : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ omega, Real.tanh (h + β * canonicalBrownian 1 omega +
        parisiControlDrift β μ (selectedParisiFeedbackControl β h μ) omega) *
        selectedParisiFeedbackControl β h μ s omega ∂canonicalBrownianMeasure) =
      ∫ omega, selectedParisiFeedbackControl β h μ s omega ^ 2 ∂canonicalBrownianMeasure) :
    (∫ omega, parisiAffineControlDerivative β h (canonicalBrownian 1)
      (selectedParisiFeedbackControl β h μ) μ ν 0 omega ∂canonicalBrownianMeasure) -
      β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
        ∫ s in (0 : ℝ)..1, s * parisiCDF μ s) =
      (∫ q : Overlap, selectedParisiG β h hβ μ q ∂(ν : Measure Overlap)) -
        ∫ q : Overlap, selectedParisiG β h hβ μ q ∂(μ : Measure Overlap) := by
  rw [integral_selectedParisiControlDerivative_of_terminal_pairing β h hβ μ ν hpair]
  exact (integral_selectedParisiG_sub_eq_moment_correction β h hβ μ ν).symm

end Paper
