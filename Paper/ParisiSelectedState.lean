module

public import Paper.ParisiCurvature
public import Paper.ParisiBrownianState
public import Paper.Variational
public import Paper.ParisiItoState

@[expose] public section

/-!
# The canonical Brownian state for the actual constructed PDE gradient

The analytic hypotheses of the general pathwise Picard construction are
discharged from the actual Parisi solution's continuity, sharp gradient bound,
and actual Hessian bound. No supplied gradient or Lipschitz premise remains.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace Paper

theorem lipschitzWith_parisiGradient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) :
    LipschitzWith 1 (fun x => parisiGradient β μ (t, x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_parisiGradient_spatial β hβ μ t x).differentiableAt)
  intro x
  rw [(hasDerivAt_parisiGradient_spatial β hβ μ t x).deriv]
  change ‖parisiHessianBCF β hβ μ (t, x)‖ ≤ (1 : ℝ)
  exact (parisiHessianBCF β hβ μ).norm_coe_le_norm _ |>.trans
    (norm_parisiHessianBCF_le_one β hβ μ)

/-- The genuine canonical Brownian state driven by the actual weak PDE solution. -/
def selectedParisiStateReal (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (ω : BrownianSample) : ℝ → ℝ :=
  canonicalParisiStateReal β h μ (fun t x => parisiGradient β μ (t, x))
    (continuous_parisiGradient β μ)
    (fun t x => norm_parisiGradient_le_one β μ (t, x))
    (lipschitzWith_parisiGradient β hβ μ) ω

theorem continuous_selectedParisiStateReal (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (ω : BrownianSample) :
    Continuous (selectedParisiStateReal β h hβ μ ω) :=
  continuous_canonicalParisiStateReal β h μ _ _ _ _ ω

@[simp] theorem selectedParisiState_initial (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (ω : BrownianSample) :
    selectedParisiStateReal β h hβ μ ω 0 = h :=
  canonicalParisiState_initial β h μ _ _ _ _ ω

theorem selectedParisiState_integral_equation (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (ω : BrownianSample) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedParisiStateReal β h hβ μ ω t = h + β * canonicalBrownian t.toNNReal ω +
      ∫ s in 0..t, β ^ 2 * parisiCDF μ s *
        parisiGradient β μ (s, selectedParisiStateReal β h hβ μ ω s) :=
  canonicalParisiState_integral_equation β h μ _ _ _ _ ω ht

/-- The actual squared-gradient expectation in the general Parisi variation. -/
def selectedParisiSecondMoment (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) : ℝ :=
  ∫ ω, parisiGradient β μ (t, selectedParisiStateReal β h hβ μ ω t) ^ 2
    ∂canonicalBrownianMeasure

/-- The variational observable formed from the actual PDE solution and state. -/
def selectedParisiG (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (t : ℝ) : ℝ :=
  parisiG β (selectedParisiSecondMoment β h hβ μ) t

/-- The actual selected state with frozen drift after the physical time strip. -/
def selectedParisiItoState (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalParisiItoState β h μ (fun s x => parisiGradient β μ (s, x))
    (continuous_parisiGradient β μ) (fun s x => norm_parisiGradient_le_one β μ (s, x))
    (lipschitzWith_parisiGradient β hβ μ) t ω

def selectedParisiItoDrift (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  canonicalParisiItoDrift β h μ (fun s x => parisiGradient β μ (s, x))
    (continuous_parisiGradient β μ) (fun s x => norm_parisiGradient_le_one β μ (s, x))
    (lipschitzWith_parisiGradient β hβ μ) t ω

theorem selectedParisiItoState_eq (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) (ω : BrownianSample) :
    selectedParisiItoState β h hβ μ t ω = selectedParisiStateReal β h hβ μ ω t :=
  canonicalParisiItoState_eq β h μ _ _ _ _ ht ω

/-- Genuine Itô characteristics for the actual PDE-selected state. -/
theorem boundedDriftItoCharacteristics_selectedParisiState (β h : ℝ)
    (hβ : β ≠ 0) (μ : ParisiMeasure) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure
      canonicalBrownianFiltration (selectedParisiItoState β h hβ μ)
      (selectedParisiItoDrift β h hβ μ) (canonicalDiracShiftMartingale β 0) β :=
  boundedDriftItoCharacteristics_canonicalParisiState β h μ _ _ _ _

theorem integrable_selectedParisiItoState (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (T : ℝ≥0) :
    Integrable (selectedParisiItoState β h hβ μ T) canonicalBrownianMeasure :=
  integrable_canonicalParisiItoState β h μ _ _ _ _ T

end Paper
