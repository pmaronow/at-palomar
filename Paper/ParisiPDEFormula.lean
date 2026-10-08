module

public import Paper.ParisiSchemeMild
public import Paper.ParisiSolutionUniqueness
public import Paper.ParisiCorrectionStability
public import Paper.PhysicalParisiFormula

@[expose] public section

/-!
# The Parisi formula with the actual arbitrary-measure weak PDE functional

Every finite scheme is represented by its explicitly constructed atomic
probability law. Its genuine mild gradient equals the constructed PDE gradient
by uniqueness. Conversely the actual grid potentials and CDF corrections
converge for every probability measure. Thus the discrete variational infimum
in the audited Talagrand theorem equals the infimum of the actual weak PDE
functional, without identifying these two definitions by fiat.

This establishes the paper's Theorem 2.2 for its physical finite SK model.
-/

open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

namespace Paper

open SpinGlass SpinGlass.Targets

theorem parisiSchemeGradient_eq_actual {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    parisiGradient β (parisiSchemeMeasure s) = parisiFiniteGradient s β := by
  have hmild : IsParisiMildOnEverySlab β (parisiSchemeMeasure s) (parisiFiniteStripGradient s β) := by
    intro b hb t ht x
    simp_rw [parisiFiniteStripGradient_extend]
    exact parisiSchemeGradient_mild s β hβ hb ht x
  have he := parisiGradientBCF_eq_of_everySlab β (parisiSchemeMeasure s)
    (parisiFiniteStripGradient s β) (norm_parisiFiniteStripGradient_le_one s β) hmild
    (fun x => by rw [parisiFiniteStripGradient_extend]; exact parisiFiniteGradient_terminal s β x)
  rw [parisiGradient, ← he, parisiFiniteStripGradient_extend]

theorem parisiSchemePotential_eq_actual {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc 0 1) :
    parisiPotential β (parisiSchemeMeasure s) (t, x) = parisiFinitePotential s β (t, x) := by
  rw [parisiPotential_eq_duhamel β (parisiSchemeMeasure s) t x ht.2,
    parisiSchemeGradient_eq_actual s β hβ]
  have he := parisiSchemePotential_mild s β hβ (b := 1) ⟨by norm_num, le_rfl⟩ ht x
  simp_rw [parisiFinitePotential_terminal] at he
  exact he.symm

theorem parisiPDEFunctional_scheme {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (h : ℝ) :
    parisiPDEFunctional β h (parisiSchemeMeasure s) = SpinGlass.Targets.parisiFunctional s β h := by
  unfold parisiPDEFunctional Paper.parisiFunctional
  dsimp only
  rw [parisiSchemePotential_eq_actual s β hβ 0 h ⟨le_rfl, by norm_num⟩,
    parisiFinitePotential_initial, parisiScheme_correction_eq]
  rfl

theorem parisiGrid_correction_eq (μ : ParisiMeasure) (n : ℕ) (β : ℝ) :
    β ^ 2 / 2 * (∫ t in (0 : ℝ)..1, t * parisiCDF (parisiGridMeasure μ n) t) =
      β ^ 2 / 4 * ∑ p ∈ Finset.range (n + 2),
        (parisiGridRSBScheme μ n).m (p + 1) *
          ((parisiGridRSBScheme μ n).q (p + 2) ^ 2 - (parisiGridRSBScheme μ n).q (p + 1) ^ 2) := by
  have he : (∫ t in (0 : ℝ)..1, t * parisiCDF (parisiGridMeasure μ n) t) =
      ∫ t in (0 : ℝ)..1, t * parisiCDF (parisiSchemeMeasure (parisiGridRSBScheme μ n)) t := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    obtain ⟨p, hp0, hp, hcell, _⟩ := exists_parisiGrid_right_cell μ n ⟨ht.1.le, ht.2⟩
    dsimp only
    rw [parisiCDF_grid_eq_scheme_mass μ n p hp0 hp hcell,
      parisiCDF_scheme_cell (parisiGridRSBScheme μ n) (by omega) hcell]
  rw [he]
  exact parisiScheme_correction_eq (parisiGridRSBScheme μ n) β

theorem parisiFiniteFunctional_grid (μ : ParisiMeasure) (n : ℕ) (β h : ℝ) :
    SpinGlass.Targets.parisiFunctional (parisiGridRSBScheme μ n) β h =
      Real.log 2 + parisiFinitePotential (parisiGridRSBScheme μ n) β (0, h) -
        β ^ 2 / 2 * ∫ t in (0 : ℝ)..1, t * parisiCDF (parisiGridMeasure μ n) t := by
  rw [parisiFinitePotential_initial, parisiGrid_correction_eq]
  rfl

theorem tendsto_parisiFiniteFunctional_grid (β : ℝ) (hβ : β ≠ 0) (h : ℝ) (μ : ParisiMeasure) :
    Tendsto (fun n => SpinGlass.Targets.parisiFunctional (parisiGridRSBScheme μ n) β h)
      atTop (𝓝 (parisiPDEFunctional β h μ)) := by
  simp_rw [parisiFiniteFunctional_grid]
  have hpot := tendsto_actual_finiteParisiPotential β hβ μ 0 h ⟨le_rfl, by norm_num⟩
  have hcor := tendsto_parisiCorrection_grid β μ
  exact (tendsto_const_nhds.add hpot).sub hcor

theorem parisiValue_le_parisiPDEFunctional (β : ℝ) (hβ : β ≠ 0) (h : ℝ) (μ : ParisiMeasure) :
    SpinGlass.Targets.parisiValue β h ≤ parisiPDEFunctional β h μ :=
  ge_of_tendsto (tendsto_parisiFiniteFunctional_grid β hβ h μ)
    (.of_forall fun n => SpinGlass.Targets.parisiValue_le (parisiGridRSBScheme μ n) β h)

/-- The infimum of the functional formed from the constructed weak PDE potential. -/
noncomputable def parisiPDEValue (β h : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ μ : ParisiMeasure, r = parisiPDEFunctional β h μ}

theorem parisiPDESet_nonempty (β h : ℝ) :
    ({r : ℝ | ∃ μ : ParisiMeasure, r = parisiPDEFunctional β h μ}).Nonempty :=
  ⟨_, diracOverlap 0 ⟨le_rfl, by norm_num⟩, rfl⟩

theorem bddBelow_parisiPDESet (β : ℝ) (hβ : β ≠ 0) (h : ℝ) :
    BddBelow {r : ℝ | ∃ μ : ParisiMeasure, r = parisiPDEFunctional β h μ} := by
  refine ⟨SpinGlass.Targets.parisiValue β h, ?_⟩
  rintro r ⟨μ, rfl⟩
  exact parisiValue_le_parisiPDEFunctional β hβ h μ

theorem parisiPDEValue_eq_finiteStep (β : ℝ) (hβ : β ≠ 0) (h : ℝ) :
    parisiPDEValue β h = SpinGlass.Targets.parisiValue β h := by
  apply le_antisymm
  · apply le_csInf (SpinGlass.Targets.parisiSet_nonempty β h)
    rintro r ⟨k, s, rfl⟩
    have he := parisiPDEFunctional_scheme s β hβ h
    exact (csInf_le (bddBelow_parisiPDESet β hβ h)
      (show ∃ μ : ParisiMeasure, SpinGlass.Targets.parisiFunctional s β h = parisiPDEFunctional β h μ from
        ⟨parisiSchemeMeasure s, he.symm⟩))
  · exact le_csInf (parisiPDESet_nonempty β h) (by
      rintro r ⟨μ, rfl⟩
      exact parisiValue_le_parisiPDEFunctional β hβ h μ)

/-- The paper's Theorem 2.2 for the physical product-Gaussian SK Hamiltonian,
with the actual probability-measure weak PDE functional. -/
theorem physicalParisiFormula (β h : ℝ) (hβ : 0 < β) :
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (parisiPDEValue β h)) := by
  rw [parisiPDEValue_eq_finiteStep β hβ.ne' h]
  exact physicalParisiFormula_finiteStep β h hβ

end Paper
