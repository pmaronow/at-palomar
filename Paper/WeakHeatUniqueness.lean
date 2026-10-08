module

public import Paper.WeakHeatMollification
public import Paper.ParisiWeakLipschitz

@[expose] public section

/-! # Linear weak heat uniqueness in the actual continuous growth class -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem parisiAdjointSource_eq_zero_of_notMem_tsupport (β : ℝ)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (p : ℝ × ℝ)
    (hp : p ∉ tsupport φ) : parisiAdjointSource β φ p = 0 := by
  have hT : parisiTestT φ p = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (tsupport_parisiTestT_subset φ hφ h))
  have hXX : parisiTestXX φ p = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (tsupport_parisiTestXX_subset φ hφ h))
  simp only [parisiAdjointSource, hT, hXX, neg_zero, mul_zero, add_zero]

/-- The original weak strip identity extends across the zero terminal
trace to the full positive-time plane. -/
theorem parisiClampPotential_weak_heat (β : ℝ) (w : ℝ × ℝ → ℝ)
    (hterminal : ∀ x, w (1, x) = 0)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ q, w q * parisiAdjointSource β φ q ∂parisiSpaceTime) = 0) :
    ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ q, parisiClampPotential w q * parisiAdjointSource β φ q) = 0 := by
  intro φ hφ hc hs
  have hsupport : Function.support
      (fun q => parisiClampPotential w q * parisiAdjointSource β φ q) ⊆
      Icc (0 : ℝ) 1 ×ˢ univ := by
    intro q hq
    have htime : q.1 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · by_contra hneg
        have hout : q ∉ tsupport φ := fun h => (not_lt_of_ge (le_of_not_ge hneg)) (hs h)
        exact hq (by
          change parisiClampPotential w q * parisiAdjointSource β φ q = 0
          rw [parisiAdjointSource_eq_zero_of_notMem_tsupport β φ hφ q hout, mul_zero])
      · by_contra hlate
        have hq1 : 1 ≤ q.1 := (lt_of_not_ge hlate).le
        have hz : parisiClampPotential w q = 0 := by
          simp only [parisiClampPotential, min_eq_left hq1, max_eq_right zero_le_one]
          exact hterminal q.2
        exact hq (by
          change parisiClampPotential w q * parisiAdjointSource β φ q = 0
          rw [hz, zero_mul])
    exact ⟨htime, mem_univ _⟩
  rw [← integral_parisiSpaceTime_eq_volume_of_support _ hsupport]
  calc
    _ = ∫ q, w q * parisiAdjointSource β φ q ∂parisiSpaceTime := by
      apply integral_congr_ae
      filter_upwards [ae_parisiSpaceTime_openStrip] with q hq
      rw [parisiClampPotential_eq w ⟨hq.1.le, hq.2.le⟩]
    _ = 0 := hweak φ hφ hc hs

/-- A continuous weak backward heat solution with zero terminal trace
and uniform linear growth is zero everywhere on its closed strip.
Weakness is the original tested integral identity, with no classical
derivative or extra differentiability premise. -/
theorem weak_backwardHeat_eq_zero_of_linearGrowth (β : ℝ) (w : ℝ × ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1 ×ˢ univ))
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖w (t, x)‖ ≤ A + L * ‖x‖)
    (hterminal : ∀ x, w (1, x) = 0)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ q, w q * parisiAdjointSource β φ q ∂parisiSpaceTime) = 0) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ, w p = 0 := by
  have hcont := continuous_parisiClampPotential w hw
  have hbound : ∀ p : ℝ × ℝ, ‖parisiClampPotential w p‖ ≤ A + L * ‖p.2‖ := by
    intro p
    apply hb (max 0 (min 1 p.1))
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hzero : ∀ p : ℝ × ℝ, 1 ≤ p.1 → parisiClampPotential w p = 0 := by
    intro p hp
    simp only [parisiClampPotential, min_eq_left hp, max_eq_right zero_le_one]
    exact hterminal p.2
  have hinterior : ∀ p : ℝ × ℝ, p.1 ∈ Ioc (0 : ℝ) 1 → parisiClampPotential w p = 0 :=
    global_weak_backwardHeat_eq_zero β _ hcont A L hA hL hbound hzero
      (parisiClampPotential_weak_heat β w hterminal hweak)
  have hclosed : IsClosed {p : ℝ × ℝ | parisiClampPotential w p = 0} :=
    isClosed_eq hcont continuous_const
  have hinc : Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ) ⊆
      {p : ℝ × ℝ | parisiClampPotential w p = 0} := by
    intro p hp
    exact hinterior p ⟨hp.1.1, hp.1.2.le⟩
  have hall : Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) ⊆
      {p : ℝ × ℝ | parisiClampPotential w p = 0} := by
    have he := hclosed.closure_subset_iff.mpr hinc
    simpa only [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_univ] using he
  intro p hp
  have hh := hall hp
  change parisiClampPotential w p = 0 at hh
  simpa only [parisiClampPotential_eq w hp.1] using hh

end Paper
