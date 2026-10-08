module

public import Paper.ParisiHJBLimit
public import Paper.HJBGrid
public import Paper.ParisiSpatialSmooth

@[expose] public section

/-! Actual HJB control representation and measure convexity of the constructed
Parisi PDE functional. All finite-grid verification and analytic approximation
bounds are discharged on the canonical Brownian space. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Paper

lemma integrable_parisiHJB_terminal (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (fun sample => Real.log (Real.cosh (canonicalParisiControlledState β h μ A 1 sample)))
      canonicalBrownianMeasure := by
  apply integrable_canonicalParisiControlledState_observable β h μ A hA 1
    (fun x => Real.log (Real.cosh x))
    ((Real.continuous_cosh).log (fun x => (Real.cosh_pos x).ne')) 0 1
  intro x
  simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_logcosh_le_abs x

lemma parisiControlObjective_eq_separate_statePayoff (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ =
      (∫ sample, Real.log (Real.cosh (canonicalParisiControlledState β h μ A 1 sample)) ∂canonicalBrownianMeasure) -
        (∫ sample, (∫ r in (0 : ℝ)..1, β ^ 2 / 2 * parisiCDF μ r * A r sample ^ 2) ∂canonicalBrownianMeasure) := by
  rw [parisiControlObjective_eq_statePayoff,
    integral_sub (integrable_parisiHJB_terminal β h μ A hA)
      (hjb_actual_cost_integrable β μ A hA 0 1 (by norm_num))]

lemma parisiControlObjective_eq_itoPayoff (β h : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ =
      (∫ sample, Real.log (Real.cosh (canonicalParisiControlledState β h μ A 1 sample)) ∂canonicalBrownianMeasure) -
        (∫ sample, parisiControlCost β μ A sample ∂canonicalBrownianMeasure) := by
  rw [parisiControlObjective_eq_separate_statePayoff β h μ A hA]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun sample => parisiInstantControlCost_integral_eq_cost β μ A sample

lemma hjb_canonical_control_drift (β : ℝ) (μ : ParisiMeasure)
    (A : ℝ → BrownianSample → ℝ) (sample : BrownianSample) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    canonicalParisiControlDrift β μ A r.toNNReal sample = β ^ 2 * parisiCDF μ r * A r sample := by
  simp only [canonicalParisiControlDrift, Real.coe_toNNReal r hr.1, ite_eq_left hr.2]

/-- Every actual admissible control lies below the constructed PDE value. -/
theorem parisiControlObjective_le_potential (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (A : ℝ → BrownianSample → ℝ) (hA : IsParisiAdmissibleControl A) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ ≤
      parisiPotential β μ (0, h) := by
  apply parisiControlObjective_upper_of_grid β h hβ μ A
  intro n
  have hh := hjbGrid_control_upper
    (boundedDriftItoCharacteristics_canonicalParisiControlledState β h μ A hA)
    hβ μ μ n A hA.measurable hA.bounded
    (fun sample r hr => hjb_canonical_control_drift β μ A sample hr)
    (integrable_canonicalParisiControlledState β h μ A hA 0)
  rw [← parisiControlObjective_eq_itoPayoff β h μ A hA] at hh
  simpa only [canonicalParisiControlledState_zero, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using hh

/-- The actual PDE feedback attains its value; no supplied Itô, law, or
verification hypothesis remains. -/
theorem parisiControlObjective_selected_eq_potential (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1)
      (selectedParisiControl β h hβ μ) μ = parisiPotential β μ (0, h) := by
  let A := selectedParisiControl β h hβ μ
  have hA : IsParisiAdmissibleControl A := isParisiAdmissibleControl_selectedParisiControl β h hβ μ
  apply le_antisymm (parisiControlObjective_le_potential β h hβ μ A hA)
  apply parisiControlObjective_lower_of_grid β h hβ μ A
  intro n
  have hclose : ∀ sample, ∀ r ∈ Icc (0 : ℝ) 1,
      ‖A r sample - parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (r, canonicalParisiControlledState β h μ A r.toNNReal sample)‖ ≤ parisiHJBGradientError β μ n := by
    intro sample r hr
    dsimp only [A]
    rw [selectedParisiControl_eq_gradient β h hβ μ hr sample]
    exact parisiHJBGradientError_bound β μ n r _
  have hh := (hjbGrid_control_error_bounds
    (boundedDriftItoCharacteristics_canonicalParisiControlledState β h μ A hA)
    hβ μ μ n A hA.measurable hA.bounded
    (fun sample r hr => hjb_canonical_control_drift β μ A sample hr)
    (integrable_canonicalParisiControlledState β h μ A hA 0)
    (parisiHJBGradientError_nonneg β μ n) hclose).2
  rw [← parisiControlObjective_eq_itoPayoff β h μ A hA] at hh
  simpa only [canonicalParisiControlledState_zero, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul] using hh

/-- The actual bounded adapted control representation, with an attained maximum. -/
theorem parisiPotential_control_representation (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    (∀ A : ℝ → BrownianSample → ℝ, IsParisiAdmissibleControl A →
      parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ ≤
        parisiPotential β μ (0, h)) ∧
    ∃ A : ℝ → BrownianSample → ℝ, IsParisiAdmissibleControl A ∧
      parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ =
        parisiPotential β μ (0, h) := by
  exact ⟨parisiControlObjective_le_potential β h hβ μ,
    selectedParisiControl β h hβ μ, isParisiAdmissibleControl_selectedParisiControl β h hβ μ,
    parisiControlObjective_selected_eq_potential β h hβ μ⟩

/-- Measure convexity of the actual constructed PDE potential. -/
theorem parisiPotential_initial_mix_le (β h : ℝ) (μ ν : ParisiMeasure)
    (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    parisiPotential β (parisiMix μ ν theta) (0, h) ≤
      (1 - theta) * parisiPotential β μ (0, h) + theta * parisiPotential β ν (0, h) := by
  by_cases hβ : β = 0
  · subst β
    simp only [parisiPotential_zero]
    nlinarith
  · let gamma := parisiMix μ ν theta
    let A := selectedParisiControl β h hβ gamma
    have hA : IsParisiAdmissibleControl A := isParisiAdmissibleControl_selectedParisiControl β h hβ gamma
    have hfixed := parisiControlObjective_mix_le_of_bounded canonicalBrownianMeasure β h
      (canonicalBrownian 1) (measurable_canonicalBrownian 1) integrable_hjb_canonicalBrownian_one
      A hA.measurable hA.bounded μ ν theta htheta
    have hopt := parisiControlObjective_selected_eq_potential β h hβ gamma
    have hμ := parisiControlObjective_le_potential β h hβ μ A hA
    have hν := parisiControlObjective_le_potential β h hβ ν A hA
    calc
      _ = parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A gamma := hopt.symm
      _ ≤ (1 - theta) * parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A μ +
          theta * parisiControlObjective canonicalBrownianMeasure β h (canonicalBrownian 1) A ν := hfixed
      _ ≤ _ := by gcongr <;> linarith [htheta.1, htheta.2]

/-- Proposition 2.3: the literal functional of the actual constructed PDE
solution is convex in its probability measure argument. -/
theorem parisiPDEFunctional_mix_le (β h : ℝ) (μ ν : ParisiMeasure)
    (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) 1) :
    parisiPDEFunctional β h (parisiMix μ ν theta) ≤
      (1 - theta) * parisiPDEFunctional β h μ + theta * parisiPDEFunctional β h ν := by
  have hp := parisiPotential_initial_mix_le β h μ ν theta htheta
  unfold parisiPDEFunctional parisiFunctional
  rw [parisiCorrection_integral_mix μ ν theta htheta]
  nlinarith

end Paper
