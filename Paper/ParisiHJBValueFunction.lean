module

public import Paper.ParisiHJBTime

@[expose] public section

/-! # The actual all-time Parisi HJB value function

The optimization uses concrete bounded continuous adapted controls on a fresh
canonical Brownian space. The endpoint and cost are explicit elapsed-time
integrals of the original measure's shifted CDF. The actual restarted PDE
feedback attains the supremum, including at the terminal time.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter
open scoped NNReal Topology
namespace Paper

/-- Literal elapsed-time running cost for the original measure. -/
def parisiTimeControlCost (β : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (A : ℝ → BrownianSample → ℝ) (sample : BrownianSample) : ℝ :=
  ∫ r in (0 : ℝ)..(1 - a), β ^ 2 / 2 * parisiCDF μ (a + r) * A r sample ^ 2

/-- Literal fresh-Brownian controlled endpoint. -/
def parisiTimeControlEndpoint (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (A : ℝ → BrownianSample → ℝ) (sample : BrownianSample) : ℝ :=
  x + β * canonicalBrownian (1 - a).toNNReal sample +
    β ^ 2 * ∫ r in (0 : ℝ)..(1 - a), parisiCDF μ (a + r) * A r sample

/-- The actual control objective, with no supplied state or law. -/
def parisiTimeControlObjective (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (A : ℝ → BrownianSample → ℝ) : ℝ :=
  ∫ sample, Real.log (Real.cosh (parisiTimeControlEndpoint β x μ a A sample)) -
    parisiTimeControlCost β μ a A sample ∂canonicalBrownianMeasure

lemma parisiTimeControlEndpoint_eq_state (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ) (sample : BrownianSample) :
    parisiTimeControlEndpoint β x μ a A sample =
      canonicalParisiRestartControlledState β x μ a ha.1 A (1 - a).toNNReal sample := by
  have hH : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
  rw [canonicalParisiRestartControlledState_integral_equation β x μ a ha.1 A
    (1 - a).toNNReal (by rw [Real.coe_toNNReal _ hH]; linarith [ha.1]) sample,
    Real.coe_toNNReal _ hH]
  rfl

lemma parisiTimeControlCost_eq_restart (β : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ) (sample : BrownianSample) :
    parisiTimeControlCost β μ a A sample =
      ∫ r in (0 : ℝ)..(1 - a), parisiInstantControlCost β (parisiRestartMeasure μ a ha.1) A r sample := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (sub_nonneg.mpr ha.2)] at hr
  dsimp only [parisiInstantControlCost]
  rw [parisiCDF_restart μ a ha.1 r hr.1]

lemma integrable_parisiTimeControlCost (β : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (parisiTimeControlCost β μ a A) canonicalBrownianMeasure := by
  have hi := integrable_parisiInstantControlCost_integral canonicalBrownianMeasure β
    (parisiRestartMeasure μ a ha.1) A hA.measurable hA.bounded 0 (1 - a) (sub_nonneg.mpr ha.2)
  exact hi.congr (.of_forall fun sample => (parisiTimeControlCost_eq_restart β μ a ha A sample).symm)

lemma integrable_parisiTimeControl_terminal (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (fun sample => Real.log (Real.cosh (parisiTimeControlEndpoint β x μ a A sample)))
      canonicalBrownianMeasure := by
  have hi := integrable_canonicalParisiControlledState_observable β x (parisiRestartMeasure μ a ha.1)
    A hA (1 - a).toNNReal (fun y => Real.log (Real.cosh y))
    (Real.continuous_cosh.log (fun y => (Real.cosh_pos y).ne')) 0 1
    (fun y => by simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_logcosh_le_abs y)
  exact hi.congr (.of_forall fun sample =>
    congrArg (fun y => Real.log (Real.cosh y))
      (parisiTimeControlEndpoint_eq_state β x μ a ha A sample).symm)

lemma parisiTimeControlObjective_eq_statePayoff (β x : ℝ) (μ : ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    parisiTimeControlObjective β x μ a A =
      (∫ sample, Real.log (Real.cosh (canonicalParisiRestartControlledState β x μ a ha.1 A (1 - a).toNNReal sample))
        ∂canonicalBrownianMeasure) - hjbExpectedCost canonicalBrownianMeasure
          (parisiInstantControlCost β (parisiRestartMeasure μ a ha.1) A) 0 (1 - a) := by
  unfold parisiTimeControlObjective
  rw [integral_sub (integrable_parisiTimeControl_terminal β x μ a ha A hA)
    (integrable_parisiTimeControlCost β μ a ha A hA)]
  congr 1
  · apply integral_congr_ae
    exact .of_forall fun sample => congrArg (fun y => Real.log (Real.cosh y))
      (parisiTimeControlEndpoint_eq_state β x μ a ha A sample)
  · apply integral_congr_ae
    exact .of_forall fun sample => parisiTimeControlCost_eq_restart β μ a ha A sample

/-- Every actual admissible fresh-Brownian control is below the PDE value. -/
theorem parisiTimeControlObjective_le_potential (β x : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    parisiTimeControlObjective β x μ a A ≤ parisiPotential β μ (a, x) := by
  rw [parisiTimeControlObjective_eq_statePayoff β x μ a ha A hA]
  have hh := parisiTime_control_upper
    (boundedDriftItoCharacteristics_canonicalParisiRestartControlledState β x μ a ha.1 A hA)
    hβ (parisiRestartMeasure μ a ha.1) μ a ha
    (fun r hr => parisiCDF_restart μ a ha.1 r hr.1) A hA.measurable hA.bounded
    (fun sample r hr => by
      rw [canonicalParisiRestartControlledDrift_eq β μ a ha A r hr sample,
        parisiCDF_restart μ a ha.1 r hr.1])
    (integrable_canonicalParisiRestartControlledState β x μ a ha.1 A hA 0)
  simpa only [canonicalParisiRestartControlledState_zero, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using hh

/-- The genuine shifted PDE feedback attains the value at every time and field. -/
theorem parisiTimeControlObjective_feedback_eq_potential (β x : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    parisiTimeControlObjective β x μ a (canonicalParisiRestartControl β x μ a ha.1) =
      parisiPotential β μ (a, x) := by
  let A := canonicalParisiRestartControl β x μ a ha.1
  have hA := isParisiAdmissibleControl_canonicalParisiRestartControl β x μ a ha.1
  rw [parisiTimeControlObjective_eq_statePayoff β x μ a ha A hA]
  have hh := parisiTime_feedback_value
    (boundedDriftItoCharacteristics_canonicalParisiRestartControlledState β x μ a ha.1 A hA)
    hβ (parisiRestartMeasure μ a ha.1) μ a ha
    (fun r hr => parisiCDF_restart μ a ha.1 r hr.1) A hA.measurable hA.bounded
    (fun sample r hr => by
      rw [canonicalParisiRestartControlledDrift_eq β μ a ha A r hr sample,
        parisiCDF_restart μ a ha.1 r hr.1])
    (integrable_canonicalParisiRestartControlledState β x μ a ha.1 A hA 0)
    (fun sample r _ => by
      change parisiGradient β μ (a + r, canonicalParisiRestartState β x μ a ha.1 r.toNNReal sample) =
        parisiGradient β μ (a + r, canonicalParisiRestartControlledState β x μ a ha.1
          (canonicalParisiRestartControl β x μ a ha.1) r.toNNReal sample)
      rw [canonicalParisiRestartControlledState_optimal_eq])
  simpa only [canonicalParisiRestartControlledState_zero, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using hh

/-- A concrete attained control representation, including the terminal time. -/
theorem parisiPotential_all_time_control_representation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    ∃ A : ℝ → BrownianSample → ℝ, IsParisiAdmissibleControl A ∧
      parisiTimeControlObjective β x μ a A = parisiPotential β μ (a, x) ∧
      ∀ C, IsParisiAdmissibleControl C → parisiTimeControlObjective β x μ a C ≤ parisiPotential β μ (a, x) := by
  exact ⟨canonicalParisiRestartControl β x μ a ha.1,
    isParisiAdmissibleControl_canonicalParisiRestartControl β x μ a ha.1,
    parisiTimeControlObjective_feedback_eq_potential β x hβ μ a ha,
    fun C hC => parisiTimeControlObjective_le_potential β x hβ μ a ha C hC⟩

/-- The literal set of attainable values for bounded continuous adapted
controls driven by a fresh canonical Brownian motion. -/
def parisiTimeControlValues (β x : ℝ) (μ : ParisiMeasure) (a : ℝ) : Set ℝ :=
  {z | ∃ A : ℝ → BrownianSample → ℝ, IsParisiAdmissibleControl A ∧
    z = parisiTimeControlObjective β x μ a A}

/-- The all-time PDE value is an attained maximum of the actual control set. -/
theorem parisiPotential_isGreatest_controlValues (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    IsGreatest (parisiTimeControlValues β x μ a) (parisiPotential β μ (a, x)) := by
  constructor
  · exact ⟨canonicalParisiRestartControl β x μ a ha.1,
      isParisiAdmissibleControl_canonicalParisiRestartControl β x μ a ha.1,
      (parisiTimeControlObjective_feedback_eq_potential β x hβ μ a ha).symm⟩
  · rintro z ⟨A, hA, rfl⟩
    exact parisiTimeControlObjective_le_potential β x hβ μ a ha A hA

/-- Literal all-time HJB value-function identity, including the terminal
time. The supremum is attained by the genuine restarted PDE feedback. -/
theorem parisiPotential_eq_sup_controlValues (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    parisiPotential β μ (a, x) = sSup (parisiTimeControlValues β x μ a) := by
  have hmax := parisiPotential_isGreatest_controlValues β hβ μ a ha x
  exact (hmax.isLUB.csSup_eq ⟨_, hmax.1⟩).symm

/-- The maximizer's explicitly integrated endpoint is the genuine restarted
Picard state, rather than a separately supplied process. -/
theorem parisiTimeControlEndpoint_feedback_eq_restartState (β x : ℝ)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (sample : BrownianSample) :
    parisiTimeControlEndpoint β x μ a (canonicalParisiRestartControl β x μ a ha.1) sample =
      canonicalParisiRestartState β x μ a ha.1 (1 - a).toNNReal sample := by
  rw [parisiTimeControlEndpoint_eq_state β x μ a ha,
    canonicalParisiRestartControlledState_optimal_eq]

/-- The literal all-time HJB statement: the PDE potential is the supremum
of actual elapsed-time control objectives, attained by its restarted feedback. -/
theorem parisiPotential_all_time_HJB (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ∀ (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1), ∀ x : ℝ,
      parisiPotential β μ (a, x) = sSup (parisiTimeControlValues β x μ a) ∧
      IsParisiAdmissibleControl (canonicalParisiRestartControl β x μ a ha.1) ∧
      parisiTimeControlObjective β x μ a
        (canonicalParisiRestartControl β x μ a ha.1) = parisiPotential β μ (a, x) := by
  intro a ha x
  exact ⟨parisiPotential_eq_sup_controlValues β hβ μ a ha x,
    isParisiAdmissibleControl_canonicalParisiRestartControl β x μ a ha.1,
    parisiTimeControlObjective_feedback_eq_potential β x hβ μ a ha⟩

end Paper
