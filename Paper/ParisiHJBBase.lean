module

public import Paper.ParisiSelectedState
public import Paper.HJBControlCost
public import Paper.ParisiStateStability

@[expose] public section

/-! Actual selected feedback controls and the uniform grid-gradient error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Paper

/-- The admissible control chosen from the genuinely constructed PDE solution. -/
def selectedParisiControl (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ℝ → BrownianSample → ℝ :=
  canonicalParisiFeedbackControl β h μ (fun t x => parisiGradient β μ (t, x))
    (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t, x))
    (lipschitzWith_parisiGradient β hβ μ)

theorem isParisiAdmissibleControl_selectedParisiControl (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) : IsParisiAdmissibleControl (selectedParisiControl β h hβ μ) :=
  isParisiAdmissibleControl_canonicalParisiFeedbackControl β h μ _ _ _ _

theorem canonicalParisiControlledState_selected_eq (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ≥0) (sample : BrownianSample) :
    canonicalParisiControlledState β h μ (selectedParisiControl β h hβ μ) t sample =
      selectedParisiItoState β h hβ μ t sample :=
  canonicalParisiControlledState_feedback_eq β h μ _ _ _ _ t sample

theorem selectedParisiControl_eq_gradient (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (sample : BrownianSample) :
    selectedParisiControl β h hβ μ t sample = parisiGradient β μ
      (t, canonicalParisiControlledState β h μ (selectedParisiControl β h hβ μ) t.toNNReal sample) := by
  rw [canonicalParisiControlledState_selected_eq]
  unfold selectedParisiControl canonicalParisiFeedbackControl parisiControlFromNNReal
    canonicalParisiFeedbackNNReal
  simp only [Real.coe_toNNReal _ ht.1, min_eq_left ht.2, Real.toNNReal_coe]
  rfl

/-- The actual uniform error of the rounded finite-grid gradient. -/
def parisiHJBGradientError (β : ℝ) (μ : ParisiMeasure) (n : ℕ) : ℝ :=
  ‖parisiFiniteGradientBCF (parisiGridRSBScheme μ n) β -
    parisiGlobalExtendBCF (parisiGradientBCF β μ)‖

theorem parisiHJBGradientError_nonneg (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    0 ≤ parisiHJBGradientError β μ n := norm_nonneg _

theorem parisiHJBGradientError_bound (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (t x : ℝ) :
    ‖parisiGradient β μ (t, x) - parisiFiniteGradient (parisiGridRSBScheme μ n) β (t, x)‖ ≤
      parisiHJBGradientError β μ n := by
  rw [norm_sub_rev]
  exact (parisiFiniteGradientBCF (parisiGridRSBScheme μ n) β -
    parisiGlobalExtendBCF (parisiGradientBCF β μ)).norm_coe_le_norm (t, x)

theorem tendsto_parisiHJBGradientError (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Tendsto (parisiHJBGradientError β μ) atTop (𝓝 0) := by
  change Tendsto (fun n => ‖parisiFiniteGradientBCF (parisiGridRSBScheme μ n) β -
    parisiGlobalExtendBCF (parisiGradientBCF β μ)‖) atTop (𝓝 0)
  have hh := ((tendsto_actual_finiteParisiGradient β hβ μ).sub_const
    (parisiGlobalExtendBCF (parisiGradientBCF β μ))).norm
  simpa only [sub_self, norm_zero, parisiHJBGradientError] using hh

/-- The actual control objective is exactly the terminal state payoff,
including its genuine running cost. -/
theorem parisiControlObjective_eq_statePayoff (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ =
      ∫ sample, Real.log (Real.cosh (canonicalParisiControlledState β h μ A 1 sample)) -
        (∫ r in (0 : ℝ)..1, β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2) ∂canonicalBrownianMeasure := by
  unfold parisiControlObjective parisiControlPayoff
  apply integral_congr_ae
  exact .of_forall fun sample => by
    dsimp only
    rw [canonicalParisiControlledState_terminal]
    congr 1
    unfold parisiControlCost
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    ring

lemma integrable_hjb_canonicalBrownian_one :
    Integrable (canonicalBrownian 1) canonicalBrownianMeasure := by
  have hh := (memLp_canonicalDiracShiftMartingale (1 : ℝ) 0 1).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have he : canonicalDiracShiftMartingale 1 0 1 = canonicalBrownian 1 := by
    funext sample
    simp only [canonicalDiracShiftMartingale, canonicalBrownian_zero, zero_add, sub_zero, one_mul]
  rw [he] at hh
  exact hh

end Paper
