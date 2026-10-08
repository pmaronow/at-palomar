module

public import Paper.ParisiDiracIdentification
public import Paper.ParisiSpatialSmooth

@[expose] public section

/-! # The actual Dirac solution is classical away from its interface

The paper's unnumbered C^{1,2} assertion means continuous first time and first
two spatial partial derivatives on each open piece. The actual selected PDE
potential has these properties. Its spatial derivatives are already continuous
across q; a classical time derivative across q is not asserted.
At the physical endpoints, derivatives are within the closed time strip.
The selected extension is clamped outside that strip.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Paper

theorem hasDerivAt_parisiPotential_dirac_time_soft (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) q) (x : ℝ) :
    HasDerivAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2) * parisiHessian β (diracOverlap q hq) (t, x)) t := by
  rw [parisiHessian_dirac_soft β q hβ hq t x ⟨ht.1.le, ht.2.le⟩]
  apply (hasDerivAt_rsSoftPotential_time hβ ht.2).congr_of_eventuallyEq
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
  intro s hs
  exact parisiPotential_dirac_soft β q hβ hq s x ⟨hs.1.le, hs.2.le⟩

theorem hasDerivAt_parisiPotential_dirac_time_hard (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo q (1 : ℝ)) (x : ℝ) :
    HasDerivAt (fun s => parisiPotential β (diracOverlap q hq) (s, x)) (-(β ^ 2 / 2)) t := by
  apply (hasDerivAt_rsHardPotential_time β t x).congr_of_eventuallyEq
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
  intro s hs
  exact parisiPotential_dirac_hard β q hβ hq s x ⟨hs.1.le, hs.2.le⟩

theorem hasDerivWithinAt_parisiPotential_dirac_time_soft (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) q) (x : ℝ) :
    HasDerivWithinAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2) * parisiHessian β (diracOverlap q hq) (t, x)) (Icc 0 1) t := by
  rw [parisiHessian_dirac_soft β q hβ hq t x ⟨ht.1, ht.2.le⟩]
  apply (hasDerivAt_rsSoftPotential_time hβ ht.2).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsq
    exact parisiPotential_dirac_soft β q hβ hq s x ⟨hs.1, hsq.le⟩
  · exact ⟨ht.1, ht.2.le.trans hq.2⟩

theorem hasDerivWithinAt_parisiPotential_dirac_time_hard (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioc q (1 : ℝ)) (x : ℝ) :
    HasDerivWithinAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2)) (Icc 0 1) t := by
  apply (hasDerivAt_rsHardPotential_time β t x).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1)] with s hs hqs
    exact parisiPotential_dirac_hard β q hβ hq s x ⟨hqs.le, hs.2⟩
  · exact ⟨hq.1.trans ht.1.le, ht.2⟩

/-- Classical C^{1,2} regularity expressed by the actual partial derivatives.
Spatial C-infinity is a strengthening of the two required spatial orders. -/
structure DiracClassicalRegularityTarget (β q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) : Prop where
  potential_continuous : Continuous (parisiPotential β (diracOverlap q hq))
  spatial_smooth : ∀ t ∈ Icc (0 : ℝ) 1,
    ContDiff ℝ ∞ (fun x => parisiPotential β (diracOverlap q hq) (t, x))
  gradient_continuous : Continuous (parisiGradient β (diracOverlap q hq))
  hessian_continuous : Continuous (parisiHessian β (diracOverlap q hq))
  soft_time_derivative : ∀ t ∈ Ioo (0 : ℝ) q, ∀ x,
    HasDerivAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2) * parisiHessian β (diracOverlap q hq) (t, x)) t
  hard_time_derivative : ∀ t ∈ Ioo q (1 : ℝ), ∀ x,
      HasDerivAt (fun s => parisiPotential β (diracOverlap q hq) (s, x)) (-(β ^ 2 / 2)) t
  soft_time_derivative_within_strip : ∀ t ∈ Ico (0 : ℝ) q, ∀ x,
    HasDerivWithinAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2) * parisiHessian β (diracOverlap q hq) (t, x)) (Icc 0 1) t
  hard_time_derivative_within_strip : ∀ t ∈ Ioc q (1 : ℝ), ∀ x,
    HasDerivWithinAt (fun s => parisiPotential β (diracOverlap q hq) (s, x))
      (-(β ^ 2 / 2)) (Icc 0 1) t
  soft_time_derivative_continuous : ContinuousOn
    (fun p : ℝ × ℝ => deriv (fun s => parisiPotential β (diracOverlap q hq) (s, p.2)) p.1)
    {p | p.1 ∈ Ioo (0 : ℝ) q}
  hard_time_derivative_continuous : ContinuousOn
    (fun p : ℝ × ℝ => deriv (fun s => parisiPotential β (diracOverlap q hq) (s, p.2)) p.1)
    {p | p.1 ∈ Ioo q (1 : ℝ)}

theorem parisiDirac_classical_regular (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) : DiracClassicalRegularityTarget β q hq := by
  refine ⟨continuous_parisiPotential β (diracOverlap q hq),
    contDiff_parisiPotential_spatial β (diracOverlap q hq),
    continuous_parisiGradient β (diracOverlap q hq),
    continuous_parisiHessian β hβ.ne' (diracOverlap q hq),
    fun _ ht x => hasDerivAt_parisiPotential_dirac_time_soft β q hβ hq ht x,
    fun _ ht x => hasDerivAt_parisiPotential_dirac_time_hard β q hβ hq ht x,
    fun _ ht x => hasDerivWithinAt_parisiPotential_dirac_time_soft β q hβ hq ht x,
    fun _ ht x => hasDerivWithinAt_parisiPotential_dirac_time_hard β q hβ hq ht x, ?_, ?_⟩
  · apply ((continuous_parisiHessian β hβ.ne' (diracOverlap q hq)).const_mul (-(β ^ 2 / 2)))
      |>.continuousOn.congr
    intro p hp
    exact (hasDerivAt_parisiPotential_dirac_time_soft β q hβ hq hp p.2).deriv
  · apply continuousOn_const.congr
    intro p hp
    exact (hasDerivAt_parisiPotential_dirac_time_hard β q hβ hq hp p.2).deriv

end Paper
