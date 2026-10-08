module

public import Paper.ParisiSolution

@[expose] public section

/-!
# Random-initial-value limits for the actual Parisi potentials

The spatial unit-gradient bound gives integrability at any integrable random
starting value. Actual uniform finite-grid error bounds then justify passing
expectations to the selected arbitrary-measure potential, at every physical
starting time.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

theorem parisiPotential_spatial_norm_sub_le (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a x y : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    ‖parisiPotential β μ (a, x) - parisiPotential β μ (a, y)‖ ≤ ‖x - y‖ := by
  simpa only [one_mul] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => parisiPotential β μ (a, x))
    (f' := fun x => parisiGradient β μ (a, x)) (s := univ) (C := 1)
    (fun z _ => (hasDerivAt_parisiPotential_spatial β hβ μ a z ha).hasDerivWithinAt)
    (fun z _ => norm_parisiGradient_le_one β μ (a, z))
    convex_univ (mem_univ y) (mem_univ x)

section RandomInitial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integrable_parisiPotential_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    Integrable (fun sample => parisiPotential β μ (a, Y sample)) P := by
  apply (hY.norm.add (integrable_const ‖parisiPotential β μ (a, 0)‖)).mono'
  · exact (continuous_parisiPotential β μ).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hY.aestronglyMeasurable)
  · exact .of_forall fun sample => by
      have hs := parisiPotential_spatial_norm_sub_le β hβ μ a (Y sample) 0 ha
      have ht := norm_add_le (parisiPotential β μ (a, Y sample) -
        parisiPotential β μ (a, 0)) (parisiPotential β μ (a, 0))
      simp only [sub_zero, sub_add_cancel] at hs ht
      exact ht.trans (add_le_add hs (le_refl _))

theorem integrable_parisiFinitePotential_time (β : ℝ) (_hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) (a : ℝ) (_ha : a ∈ Icc (0 : ℝ) 1)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    Integrable (fun sample => parisiFinitePotential (parisiGridRSBScheme μ n) β
      (a, Y sample)) P := by
  apply (hY.norm.add (integrable_const
    ‖parisiFinitePotential (parisiGridRSBScheme μ n) β (a, 0)‖)).mono'
  · exact (continuous_parisiFinitePotential (parisiGridRSBScheme μ n) β).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hY.aestronglyMeasurable)
  · exact .of_forall fun sample => by
      have hs := parisiFinitePotential_lipschitz (parisiGridRSBScheme μ n) β a (Y sample) 0
      have ht := norm_add_le (parisiFinitePotential (parisiGridRSBScheme μ n) β (a, Y sample) -
        parisiFinitePotential (parisiGridRSBScheme μ n) β (a, 0))
        (parisiFinitePotential (parisiGridRSBScheme μ n) β (a, 0))
      simp only [sub_zero, sub_add_cancel] at hs ht
      simp only [Real.norm_eq_abs] at ht ⊢
      exact ht.trans (add_le_add hs (le_refl _))

theorem norm_integral_finiteParisiPotential_time_sub_le (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    ‖(∫ sample, parisiFinitePotential (parisiGridRSBScheme μ n) β (a, Y sample) ∂P) -
      ∫ sample, parisiPotential β μ (a, Y sample) ∂P‖ ≤
      β ^ 2 * ‖parisiGradientBCF β μ - parisiGridGradientApproximation β μ n‖ +
        β ^ 2 / 2 * (1 / (n + 1 : ℕ)) := by
  rw [← integral_sub (integrable_parisiFinitePotential_time β hβ μ n a ha Y hY)
    (integrable_parisiPotential_time β hβ μ a ha Y hY)]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := P)
    (.of_forall fun sample => by
      rw [norm_sub_rev, parisiFinitePotential_eq_duhamel_grid β hβ μ n a (Y sample) ha,
        parisiPotential_eq_duhamel β μ a (Y sample) ha.2]
      exact norm_parisiDuhamelPotential_grid_sub_le β μ (parisiGradientBCF β μ)
        (norm_parisiGradientBCF_le_one β μ) n a (Y sample) ha)

theorem tendsto_integral_finiteParisiPotential_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    Tendsto (fun n => ∫ sample, parisiFinitePotential (parisiGridRSBScheme μ n) β
      (a, Y sample) ∂P) atTop (𝓝 (∫ sample, parisiPotential β μ (a, Y sample) ∂P)) := by
  have hg : Tendsto (fun n => ‖parisiGradientBCF β μ - parisiGridGradientApproximation β μ n‖)
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => parisiGradientBCF β μ) atTop
      (𝓝 (parisiGradientBCF β μ)) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using
      (hc.sub (tendsto_parisiGridGradient β hβ μ)).norm
  have hm : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he := (hg.const_mul (β ^ 2)).add (hm.const_mul (β ^ 2 / 2))
  simp only [mul_zero, add_zero] at he
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [he.eventually (eventually_lt_nhds hε)] with n hn
  rw [dist_eq_norm]
  exact (norm_integral_finiteParisiPotential_time_sub_le β hβ μ n a ha Y hY).trans_lt hn

end RandomInitial
end Paper
