module

public import Targets.Section5InterleavedPressure
public import Targets.Section5InterleavedContinuity
public import Targets.Section5InterleavedStrict
public import Targets.Section5InterleavedNegative

@[expose] public section

/-!
# Transport of the actual mixed interpolation bound

Closed-interval continuity and the proved interior derivative estimate give
the original constrained free-energy bound. The scalar deficit is unchanged:
it is chosen before the system size and Gaussian disorder. The final trial
interval and remaining first-physical-level cases are not asserted here.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The actual mixed comparison between the original free energy and the
zero-time endpoint, with no endpoint differentiability assumption. -/
theorem section5InterleavedInterpolation_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r j : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      section5InterleavedInterpolation n s β h sk.U r j t u 0 -
        2 * t * parisiCorrection s β := by
  have hc := continuousOn_section5InterleavedInterpolation s β h sk.hU r hj ht hu
  have hd : DifferentiableOn ℝ (section5InterleavedInterpolation n s β h sk.U r j t u)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro w hw
    exact (hasDerivAt_section5InterleavedInterpolation_replica hn s β h sk r hj0 hj ht hu hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (section5InterleavedInterpolation n s β h sk.U r j t u) w ≤
        -(2 * t * parisiCorrection s β) := by
    rw [interior_Icc]
    exact fun w hw => deriv_section5InterleavedInterpolation_le hn s β h sk r hj0 hj ht hu hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5InterleavedInterpolation_one n s β h sk.U hr0 hr j ht.2 u] at H
  simp only [sub_zero, mul_one] at H
  linarith

/-- The actual scalar deficit survives transport to the original free
energy and the original comparison function `ψ`, not `φ`. -/
theorem constrainedPhi_le_guerraPsi_sub_interleavedDeficit
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r j : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t - section5InterleavedScalarDeficit s β h r j t u := by
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have H := section5InterleavedInterpolation_endpoint_bound hn s β h sk hr0 hr hj0 hj ht hu
  have H0 := section5InterleavedInterpolation_zero_le_sub_deficit hn s β h sk.U r hj ht hu
    ⟨σ, τ, hστ⟩
  dsimp only [guerraPsi]
  linarith

/-- Left outside-neighbor strict improvement, with the positive deficit
fixed before all system sizes and Gaussian disorders. -/
theorem exists_constrainedPhi_interleaved_gap_left_outside
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - |u|)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_left_outside s β h ht hr hj0
      hjr hu hm hbv hcv)
  · intro n hn sk hatt
    exact constrainedPhi_le_guerraPsi_sub_interleavedDeficit hn s β h sk (by omega) hr
      hj0 (by omega) ht hu hatt

/-- Right outside-neighbor strict improvement with the same uniform-in-size
quantifier order; only the two witness variances must be positive. -/
theorem exists_constrainedPhi_interleaved_gap_right_outside
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hr0 : 1 ≤ r) (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1)))) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_right_outside s β h ht hj
      hrj hu hm hbv hcv)
  · intro n hn sk hatt
    exact constrainedPhi_le_guerraPsi_sub_interleavedDeficit hn s β h sk hr0 (by omega)
      (by omega) hj ht hu hatt

/-- All negative overlaps in the current trial range, including breakpoints
and zero first overlap, for physical levels at least two. -/
theorem exists_constrainedPhi_interleaved_gap_negative
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_negative s β h hβ ht hr0 hj0 hj
      hm hq huneg hu)
  · intro n hn sk hatt
    exact constrainedPhi_le_guerraPsi_sub_interleavedDeficit hn s β h sk (by omega) hr
      hj0 hj ⟨ht.1.le, ht.2.le⟩ hu hatt

/-- Negative overlaps beyond the first overlap at physical level one, when
the first frozen shared field is nondegenerate. -/
theorem exists_constrainedPhi_interleaved_gap_negative_first
    (s : RSBScheme k) (β h : ℝ) {j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hj0 : 2 ≤ j) (hj : j ≤ k + 1)
    (hm : 0 < s.m 1) (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2)
    (huneg : u < 0) (hu1 : s.q 1 < |u|)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h 1 j t u ∧
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 1) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h 1 j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_negative_of_q1_pos s β h hβ ht
      (r := 1) le_rfl hj0 hj hm hq1 hq huneg hu1 hu)
  · intro n hn sk hatt
    simpa only [show k + 2 - 1 = k + 1 by omega] using
      constrainedPhi_le_guerraPsi_sub_interleavedDeficit hn s β h sk (r := 1) le_rfl
        (by omega) (by omega) hj ⟨ht.1.le, ht.2.le⟩ hu hatt

end SpinGlass.Targets
