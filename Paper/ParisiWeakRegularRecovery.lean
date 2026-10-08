module

public import Paper.ParisiWeakRecovery
public import Paper.HeatSourceCongruence
public import Paper.BoundedHeatSourceRegularity

@[expose] public section

/-! # Actual continuous mild gradients recovered from the original weak class

This module isolates the passage from regularity of the concrete bounded
source integrals to regularity of every original weak solution.  The
regularity of those Gaussian operators is proved independently.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem continuous_parisiTerminalGradient (β : ℝ) :
    Continuous (fun p : ℝ × ℝ => heatSemigroup (β ^ 2 * (1 - p.1)) Real.tanh p.2) := by
  apply continuous_of_dominated (μ := gaussianReal 0 1)
    (F := fun (p : ℝ × ℝ) z => Real.tanh (p.2 + Real.sqrt (β ^ 2 * (1 - p.1)) * z))
    (bound := fun _ => (1 : ℝ))
  · intro p
    exact (gaussian_continuous_tanh.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact .of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one _).le)
  · exact integrable_const _
  · exact .of_forall fun z => gaussian_continuous_tanh.comp (by fun_prop)

theorem IsParisiWeakSolution.exists_continuous_mildGradient_of_source_regular
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hV : Continuous (boundedVolterraPotential β (parisiNonlinearity μ v)))
    (hG : ContinuousOn (boundedVolterraGradient β (parisiNonlinearity μ v))
      (Icc (0 : ℝ) 1 ×ˢ univ)) :
    ∃ (g : ℝ × ℝ → ℝ) (K : ℝ), Continuous g ∧ (∀ p, ‖g p‖ ≤ K) ∧
      v =ᵐ[parisiSpaceTime] g ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, u (t, x) = parisiDuhamelPotential β μ g t x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        g (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
          parisiGradientCorrection β μ g 1 t x) := by
  let F := parisiNonlinearity μ v
  have hFm : Measurable F := parisiNonlinearity_measurable μ v hv
  have hFb : ∀ p, ‖F p‖ ≤ R ^ 2 := norm_parisiNonlinearity_le μ v R hb
  let raw : ℝ × ℝ → ℝ := fun p =>
    heatSemigroup (β ^ 2 * (1 - p.1)) Real.tanh p.2 + β ^ 2 / 2 * boundedVolterraGradient β F p
  let g := parisiClampPotential raw
  let N := 2 * R ^ 2 * gaussianAbsMoment / |β|
  let K := 1 + β ^ 2 / 2 * N
  have hmoment := gaussianAbsMoment_nonneg
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hraw : ContinuousOn raw (Icc (0 : ℝ) 1 ×ˢ univ) :=
    (continuous_parisiTerminalGradient β).continuousOn.add (continuousOn_const.mul hG)
  have hgc : Continuous g := continuous_parisiClampPotential raw hraw
  have hrawb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖raw (t, x)‖ ≤ K := by
    intro t ht x
    have hroot : Real.sqrt (1 - t) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (show 1 - t ≤ 1 by linarith [ht.1])
    have hgrad : ‖boundedVolterraGradient β F (t, x)‖ ≤ N :=
      (norm_boundedVolterraGradient_le β F hFm (R ^ 2) hFb t x ht).trans
        (by change N * Real.sqrt (1 - t) ≤ N; simpa using mul_le_mul_of_nonneg_left hroot hN)
    calc
      _ ≤ ‖heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x‖ +
        ‖β ^ 2 / 2 * boundedVolterraGradient β F (t, x)‖ := norm_add_le _ _
      _ ≤ K := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
        exact add_le_add (norm_heatSemigroup_le _ Real.tanh 1
          (fun y => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le) x)
          (mul_le_mul_of_nonneg_left hgrad (by positivity))
  have hgb : ∀ p, ‖g p‖ ≤ K := by
    intro p
    exact hrawb (max 0 (min 1 p.1))
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ p.2
  have hue := huv.eq_heatVolterra_of_continuous_source hβ hv R hb hV
  have hd : ∀ t x, HasDerivAt (fun y => parisiClampPotential u (t, y)) (g (t, x)) x := by
    intro t x
    let ct := max 0 (min 1 t)
    have hct : ct ∈ Icc (0 : ℝ) 1 :=
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hefun : (fun y => parisiClampPotential u (t, y)) =
        fun y => parisiTerminalHeat β (ct, y) + β ^ 2 / 2 * boundedVolterraPotential β F (ct, y) := by
      funext y
      exact hue (ct, y) ⟨hct, mem_univ _⟩
    rw [hefun]
    exact (hasDerivAt_heatSemigroup_logcosh_spatial (β ^ 2 * (1 - ct)) x).add
      ((hasDerivAt_boundedVolterraPotential_spatial β hβ F hFm (R ^ 2) hFb ct x hct).const_mul _)
  have hgw : IsParisiWeakGradient (parisiClampPotential u) g :=
    isParisiWeakGradient_of_hasDerivAt _ _
      (continuous_parisiClampPotential u huv.continuous_potential) hgc (fun t _ x => hd t x)
  have hvae : v =ᵐ[parisiSpaceTime] g := by
    have huclamp : u =ᵐ[parisiSpaceTime] parisiClampPotential u := by
      filter_upwards [ae_parisiSpaceTime_openStrip] with p hp
      exact (parisiClampPotential_eq u ⟨hp.1.le, hp.2.le⟩).symm
    exact parisiWeakGradient_ae_unique _ v g
      (huv.weak_gradient.congr_potential huclamp) hgw hv.aestronglyMeasurable hgc.aestronglyMeasurable
      R K (.of_forall hb) (.of_forall hgb)
  have hFae : F =ᵐ[parisiSpaceTime] parisiNonlinearity μ g := by
    filter_upwards [hvae] with p hp
    simp only [F, parisiNonlinearity, hp]
  have huD : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, u (t, x) = parisiDuhamelPotential β μ g t x := by
    intro t ht x
    rw [hue (t, x) ⟨ht, mem_univ _⟩,
      boundedVolterraPotential_congr_ae β hβ F (parisiNonlinearity μ g) hFm
        (parisiNonlinearity_measurable μ g hgc.measurable) hFae,
      ← parisiContinuousPotential_eq_terminalVolterra β μ g t x ht,
      parisiContinuousPotential_eq β μ g t x ht.2]
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      g (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
        parisiGradientCorrection β μ g 1 t x := by
    intro t ht x
    have hefun : (fun y => parisiClampPotential u (t, y)) = parisiDuhamelPotential β μ g t := by
      funext y
      rw [parisiClampPotential_eq u (p := (t, y)) ht]
      exact huD t ht y
    have hdx := hd t x
    rw [hefun] at hdx
    exact hdx.unique (hasDerivAt_parisiDuhamelPotential_spatial β μ g hgc.measurable
      K hgb t x ht.2 hβ)
  exact ⟨g, K, hgc, hgb, hvae, huD, heq⟩

end Paper
