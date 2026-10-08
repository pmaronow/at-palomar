module

public import Paper.ParisiWeakUniqueness

@[expose] public section

/-! # Bounded measurable representatives of genuine weak gradients -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem IsParisiWeakGradient.congr_potential {u U v : ℝ × ℝ → ℝ}
    (hu : IsParisiWeakGradient u v) (he : u =ᵐ[parisiSpaceTime] U) :
    IsParisiWeakGradient U v := by
  intro φ hφ hc hs
  obtain ⟨hi, hz⟩ := hu φ hφ hc hs
  have heq : (fun p => u p * parisiTestX φ p + v p * φ p) =ᵐ[parisiSpaceTime]
      (fun p => U p * parisiTestX φ p + v p * φ p) := by
    filter_upwards [he] with p hp
    rw [hp]
  exact ⟨hi.congr heq, (integral_congr_ae heq).symm.trans hz⟩

theorem IsParisiWeakGradient.congr_gradient {u v w : ℝ × ℝ → ℝ}
    (hv : IsParisiWeakGradient u v) (he : v =ᵐ[parisiSpaceTime] w) :
    IsParisiWeakGradient u w := by
  intro φ hφ hc hs
  obtain ⟨hi, hz⟩ := hv φ hφ hc hs
  have heq : (fun p => u p * parisiTestX φ p + v p * φ p) =ᵐ[parisiSpaceTime]
      (fun p => u p * parisiTestX φ p + w p * φ p) := by
    filter_upwards [he] with p hp
    rw [hp]
  exact ⟨hi.congr heq, (integral_congr_ae heq).symm.trans hz⟩

theorem IsParisiWeakSolution.congr_gradient {β : ℝ} {μ : ParisiMeasure}
    {u v w : ℝ × ℝ → ℝ} (hv : IsParisiWeakSolution β μ u v)
    (he : v =ᵐ[parisiSpaceTime] w) : IsParisiWeakSolution β μ u w := by
  refine ⟨hv.continuous_potential, hv.measurable_gradient.congr he, ?_,
    hv.weak_gradient.congr_gradient he, hv.terminal, ?_⟩
  · obtain ⟨M, hM⟩ := hv.bounded_gradient
    refine ⟨M, ?_⟩
    filter_upwards [hM, he] with p hp hpe
    simpa only [← hpe] using hp
  · intro φ hφ hc hs
    obtain ⟨hi, ht, hz⟩ := hv.equation φ hφ hc hs
    have heq : (fun p => -u p * parisiTestT φ p + β ^ 2 / 2 *
        (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)) =ᵐ[parisiSpaceTime]
        (fun p => -u p * parisiTestT φ p + β ^ 2 / 2 *
        (u p * parisiTestXX φ p + parisiCDF μ p.1 * w p ^ 2 * φ p)) := by
      filter_upwards [he] with p hp
      rw [hp]
    exact ⟨hi.congr heq, ht, by rw [← integral_congr_ae heq]; exact hz⟩

theorem IsParisiWeakSolution.congr_potential_on {β : ℝ} {μ : ParisiMeasure}
    {u U v : ℝ × ℝ → ℝ} (huv : IsParisiWeakSolution β μ u v)
    (hU : ContinuousOn U (Icc (0 : ℝ) 1 ×ˢ univ))
    (he : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, u p = U p) :
    IsParisiWeakSolution β μ U v := by
  have hae : u =ᵐ[parisiSpaceTime] U := by
    filter_upwards [ae_parisiSpaceTime_openStrip] with p hp
    exact he p ⟨⟨hp.1.le, hp.2.le⟩, mem_univ _⟩
  refine ⟨hU, huv.measurable_gradient, huv.bounded_gradient,
    huv.weak_gradient.congr_potential hae, ?_, ?_⟩
  · intro x
    rw [← he (1, x) ⟨⟨by norm_num, le_rfl⟩, mem_univ _⟩]
    exact huv.terminal x
  · intro φ hφ hc hs
    obtain ⟨hi, ht, hz⟩ := huv.equation φ hφ hc hs
    have heq : (fun p => -u p * parisiTestT φ p + β ^ 2 / 2 *
        (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)) =ᵐ[parisiSpaceTime]
        (fun p => -U p * parisiTestT φ p + β ^ 2 / 2 *
        (U p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)) := by
      filter_upwards [hae] with p hp
      rw [hp]
    exact ⟨hi.congr heq, ht, by rw [← integral_congr_ae heq]; exact hz⟩

/-- Essential bounds admit a globally measurable, everywhere bounded
representative.  All equations of the original solution are retained. -/
theorem IsParisiWeakSolution.exists_bounded_measurable_representative
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (hv : IsParisiWeakSolution β μ u v) :
    ∃ (M : ℝ) (w : ℝ × ℝ → ℝ), 0 ≤ M ∧ Measurable w ∧
      (∀ p, ‖w p‖ ≤ M) ∧ v =ᵐ[parisiSpaceTime] w ∧
      IsParisiWeakSolution β μ u w := by
  classical
  obtain ⟨K, hK⟩ := hv.bounded_gradient
  let M := max K 0
  let z := hv.measurable_gradient.mk v
  let w : ℝ × ℝ → ℝ := fun p => if ‖z p‖ ≤ M then z p else 0
  have hz : Measurable z := hv.measurable_gradient.measurable_mk
  have hw : Measurable w := hz.ite (measurableSet_le hz.norm measurable_const) measurable_const
  have hb : ∀ p, ‖w p‖ ≤ M := by
    intro p
    dsimp only [w]
    split_ifs with hp
    · exact hp
    · simpa only [norm_zero] using (le_max_right K 0)
  have he : v =ᵐ[parisiSpaceTime] w := by
    filter_upwards [hv.measurable_gradient.ae_eq_mk, hK] with p hp hpk
    change v p = z p at hp
    change v p = if ‖z p‖ ≤ M then z p else 0
    rw [if_pos (by rw [← hp]; exact hpk.trans (le_max_left K 0))]
    exact hp
  exact ⟨M, w, le_max_right K 0, hw, hb, he, hv.congr_gradient he⟩

end Paper
