module

public import Paper.ParisiFiniteApproximation

@[expose] public section

/-! # The constructed potential for each actual Parisi probability measure

The selectors choose the proved uniform limit of the genuine Cole--Hopf
grid gradients. No existence or smoothness axiom enters their definition.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

noncomputable def parisiTanhStripGradient : ParisiSlabGradient 0 1 :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => Real.tanh p.2)
    (gaussian_continuous_tanh.comp continuous_snd) 1
    (fun p => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one p.2).le)

theorem exists_parisiGradientBCF (β : ℝ) (μ : ParisiMeasure) :
    ∃ V : ParisiSlabGradient 0 1, ‖V‖ ≤ 1 ∧
      parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
        gaussian_continuous_tanh
        (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le) V = V ∧
      (β ≠ 0 → Tendsto (parisiGridGradientApproximation β μ) atTop (𝓝 V)) := by
  by_cases hβ : β = 0
  · subst β
    refine ⟨parisiTanhStripGradient,
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _, ?_, ?_⟩
    · apply BoundedContinuousFunction.ext
      intro p
      change parisiSlabGradientValue 0 μ (by norm_num : (0 : ℝ) ≤ 1)
        Real.tanh parisiTanhStripGradient p = Real.tanh p.2
      simp [parisiSlabGradientValue, parisiNormalizedGradientCorrection,
        heatSemigroup, gaussianExpectation]
    · intro h
      exact (h rfl).elim
  · obtain ⟨V, hlim, hV, hfix⟩ := exists_actual_globalParisiGradient β hβ μ
    exact ⟨V, hV, hfix, fun _ => hlim⟩

noncomputable def parisiGradientBCF (β : ℝ) (μ : ParisiMeasure) : ParisiSlabGradient 0 1 :=
  Classical.choose (exists_parisiGradientBCF β μ)

theorem norm_parisiGradientBCF_le_one (β : ℝ) (μ : ParisiMeasure) :
    ‖parisiGradientBCF β μ‖ ≤ 1 := (Classical.choose_spec (exists_parisiGradientBCF β μ)).1

theorem parisiGradientBCF_fixedPoint (β : ℝ) (μ : ParisiMeasure) :
    parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
      gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      (parisiGradientBCF β μ) = parisiGradientBCF β μ :=
  (Classical.choose_spec (exists_parisiGradientBCF β μ)).2.1

theorem tendsto_parisiGridGradient (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Tendsto (parisiGridGradientApproximation β μ) atTop (𝓝 (parisiGradientBCF β μ)) :=
  (Classical.choose_spec (exists_parisiGradientBCF β μ)).2.2 hβ

noncomputable def parisiGradient (β : ℝ) (μ : ParisiMeasure) : ℝ × ℝ → ℝ :=
  parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (parisiGradientBCF β μ)

theorem continuous_parisiGradient (β : ℝ) (μ : ParisiMeasure) : Continuous (parisiGradient β μ) :=
  continuous_parisiSlabExtend (by norm_num) _

theorem norm_parisiGradient_le_one (β : ℝ) (μ : ParisiMeasure) (p : ℝ × ℝ) :
    ‖parisiGradient β μ p‖ ≤ 1 :=
  (norm_parisiSlabExtend_le (by norm_num) _ p).trans (norm_parisiGradientBCF_le_one β μ)

theorem parisiGradient_equation (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiGradient β μ (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
      parisiGradientCorrection β μ (parisiGradient β μ) 1 t x := by
  have h := localParisiGradient_equation β μ (by norm_num : (0 : ℝ) ≤ 1)
    Real.tanh gaussian_continuous_tanh
    (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
    (parisiGradientBCF β μ) (parisiGradientBCF_fixedPoint β μ) (⟨t, ht⟩, x)
  simpa only [parisiGradient, parisiSlabExtend, projIcc_of_mem _ ht] using h

noncomputable def parisiPotential (β : ℝ) (μ : ParisiMeasure) : ℝ × ℝ → ℝ :=
  parisiContinuousPotential β μ (parisiGradient β μ)

theorem continuous_parisiPotential (β : ℝ) (μ : ParisiMeasure) : Continuous (parisiPotential β μ) :=
  continuous_parisiContinuousPotential β μ _ (continuous_parisiGradient β μ) 1
    (norm_parisiGradient_le_one β μ)

theorem parisiPotential_eq_duhamel (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ≤ 1) :
    parisiPotential β μ (t, x) = parisiDuhamelPotential β μ (parisiGradient β μ) t x :=
  parisiContinuousPotential_eq β μ _ t x ht

theorem parisiPotential_isWeakSolution (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    IsParisiWeakSolution β μ (parisiPotential β μ) (parisiGradient β μ) :=
  isParisiWeakSolution_of_boundedContinuous_mildGradient β hβ μ _
    (continuous_parisiGradient β μ) 1 (norm_parisiGradient_le_one β μ)
    (fun t ht x => parisiGradient_equation β μ t x ht)

theorem hasDerivAt_parisiPotential_spatial (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => parisiPotential β μ (t, y)) (parisiGradient β μ (t, x)) x := by
  have hd := hasDerivAt_parisiDuhamelPotential_spatial β μ (parisiGradient β μ)
    (continuous_parisiGradient β μ).measurable 1 (norm_parisiGradient_le_one β μ) t x ht.2 hβ
  rw [← parisiGradient_equation β μ t x ht] at hd
  exact hd.congr_of_eventuallyEq (.of_forall fun y => parisiPotential_eq_duhamel β μ t y ht.2)

theorem parisiPotential_terminal (β : ℝ) (μ : ParisiMeasure) (x : ℝ) :
    parisiPotential β μ (1, x) = Real.log (Real.cosh x) := by
  rw [parisiPotential_eq_duhamel β μ 1 x le_rfl, parisiDuhamelPotential_terminal]

theorem tendsto_actual_finiteParisiGradient (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Tendsto (fun n => parisiFiniteGradientBCF (parisiGridRSBScheme μ n) β) atTop
      (𝓝 (parisiGlobalExtendBCF (parisiGradientBCF β μ))) :=
  tendsto_parisiFiniteGradientBCF_of_strip (tendsto_parisiGridGradient β hβ μ)

theorem tendsto_actual_finiteParisiPotential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => parisiFinitePotential (parisiGridRSBScheme μ n) β (t, x)) atTop
      (𝓝 (parisiPotential β μ (t, x))) := by
  simp_rw [parisiFinitePotential_eq_duhamel_grid β hβ μ _ t x ht]
  rw [parisiPotential_eq_duhamel β μ t x ht.2]
  exact tendsto_parisiDuhamelPotential_grid β μ _ (norm_parisiGradientBCF_le_one β μ)
    (tendsto_parisiGridGradient β hβ μ) t x ht

/-- The functional now uses the proved weak-PDE potential of the actual measure. -/
noncomputable def parisiPDEFunctional (β h : ℝ) (μ : ParisiMeasure) : ℝ :=
  parisiFunctional β h (fun ν t x => parisiPotential β ν (t, x)) μ

end Paper
