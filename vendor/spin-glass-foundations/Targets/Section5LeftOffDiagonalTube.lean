module

public import Targets.Section5LeftOffDiagonalInterpolation
public import Targets.Section5PhysicalNeighborWitness
public import Targets.Section5CompactTube

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The scalar deficit supplied by the direct left off-diagonal comparison.
The last term is the explicit cost of transporting the trial overlap `v` to
the constrained overlap `u`. -/
noncomputable def section5LeftOffDiagonalDeficit
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ : ℝ)
    (t u v : ℝ) : ℝ :=
  2 * guerraPsi s β h t -
    (2 * Real.log 2 + section5V s β h r m
      (t * (β ^ 2 * (s.q r - v))) ℓ - ℓ * u -
      t * (2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 *
          (s.q r ^ 2 - v ^ 2))) +
      t * (β ^ 2 / 2) * (u - v) ^ 2)

theorem section5LeftOffDiagonalDeficit_diag
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ t v : ℝ) :
    section5LeftOffDiagonalDeficit s β h r m ℓ t v v =
      section5LeftComparisonDeficit s β h r m ℓ (t, v) := by
  simp [section5LeftOffDiagonalDeficit, section5LeftComparisonDeficit,
    section5LeftComparison]

theorem continuous_section5LeftOffDiagonalDeficit
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    {m : ℝ} (hm : 0 ≤ m) (ℓ v : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      section5LeftOffDiagonalDeficit s β h r m ℓ z.1 z.2 v) := by
  have HV := (continuous_section5V_variance_lambda s β h hr hm).comp
    (show Continuous (fun z : ℝ × ℝ =>
      (z.1 * (β ^ 2 * (s.q r - v)), ℓ)) by fun_prop)
  have HG : Continuous (fun z : ℝ × ℝ => 2 * guerraPsi s β h z.1) := by
    unfold guerraPsi
    fun_prop
  unfold section5LeftOffDiagonalDeficit
  have Hlin : Continuous (fun z : ℝ × ℝ =>
      2 * Real.log 2 + section5V s β h r m
        (z.1 * (β ^ 2 * (s.q r - v))) ℓ - ℓ * z.2 -
      z.1 * (2 * parisiCorrection s β +
        (m - s.m (r - 1)) * (β ^ 2 / 2 *
          (s.q r ^ 2 - v ^ 2)))) := by
    fun_prop
  have HQ : Continuous (fun z : ℝ × ℝ =>
      z.1 * (β ^ 2 / 2) * (z.2 - v) ^ 2) := by fun_prop
  exact HG.sub (Hlin.add HQ)

/-- A strict scalar witness at the physical left endpoint gives a uniform
two-sided constrained-overlap tube. -/
theorem exists_uniform_constrainedPhi_left_physical_tube
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v t₀ : ℝ}
    (hv : v ∈ Icc (s.q (r - 1)) (s.q r)) (ht₀ : t₀ < 1)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ,
        0 < section5LeftOffDiagonalDeficit s β h r m ℓ t v v) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u - v| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let I : Type := {m : ℝ // m ∈ Icc (s.m (r - 1) / 2) (s.m r)} × ℝ
  let f : I → (ℝ × ℝ) → ℝ := fun i z =>
    section5LeftOffDiagonalDeficit s β h r i.1.1 i.2 z.1 z.2 v
  have hf : ∀ i : I, Continuous (f i) := by
    intro i
    exact continuous_section5LeftOffDiagonalDeficit s β h hr
      ((div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans i.1.2.1)
      i.2 v
  have hpos : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ i : I, 0 < f i (t, v) := by
    intro t ht
    obtain ⟨m, hm, ℓ, H⟩ := hboundary t ht
    exact ⟨(⟨m, hm⟩, ℓ), H⟩
  obtain ⟨ρ, hρ, δ, hδ, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Icc (0 : ℝ) t₀)
      isCompact_Icc f hf v hpos
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro t ht u hu n hn sk hatt
  obtain ⟨i, hi⟩ := Htube t ht u hu
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have Hactual := section5InterpolationOffDiagonal_endpoint_bound hn s β h sk
    hr0 hr (m := i.1.1) (t := t) (u := u) (v := v) (ℓ := i.2)
      i.1.2 ⟨ht.1, ht.2.trans ht₀.le⟩ hv
  dsimp [f, section5LeftOffDiagonalDeficit] at hi
  dsimp only [guerraPsi] at hi ⊢
  linarith

/- The initial breakpoint is covered on both signs: the scalar witness is
obtained at `u=v=0`, and the direct quadratic mismatch term transports it to
negative constrained overlaps as well. -/
theorem exists_uniform_constrainedPhi_initial_left_two_sided
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ L : ℝ} (ht₀ : t₀ < 1) (hL : 0 ≤ L)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hLip : ∀ v ∈ Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤
          L * |v - w|)
    (hq1 : 0 < s.q 1) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
    s β h (r := 1) (by omega) (by omega) hβ hm
      (Or.inl (by simpa only [s.q_zero] using hq1)) hright hmin
  obtain ⟨hcL, e, he, he_small, hR⟩ := section5Initial_curvature_data
    s β h ε hβ hm hq1 hright (t₀ := t₀) hL hmin hnear hsmall hLip
  have hboundary : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∃ m ∈ Icc (s.m (1 - 1) / 2) (s.m 1), ∃ ℓ,
        0 < section5LeftOffDiagonalDeficit s β h 1 m ℓ t 0 0 := by
    intro t ht
    have hslope := section5LeftSlope_initial_ge_of_endpoint_curvature s β h
      ht ht₀ he ⟨by simp [s.q_zero], hq1.le⟩ hQ hR he_small
    have hsneq : section5LeftSlope s β h 1 t 0 ≠ 0 := by
      have hc : 0 < (1 - t₀) / 2 * s.q 1 :=
        mul_pos (div_pos (sub_pos.mpr ht₀) (by norm_num)) hq1
      intro hz
      rw [hz] at hslope
      linarith
    obtain ⟨ℓ, Hℓ⟩ := exists_section5LeftComparison_witness_of_slope_ne
      s β h (r := 1) (by omega) (by omega)
      ⟨ht.1, ht.2.trans ht₀.le⟩
      ⟨by simp [s.q_zero], hq1.le⟩ hsneq
    refine ⟨s.m 0, ?_, ℓ, ?_⟩
    · constructor
      · simpa [s.m_zero] using
          (div_nonneg (s.m_nonneg (p := 0) (by omega)) (by norm_num))
      · exact hm.le
    simpa only [Nat.sub_self] using
      (section5LeftOffDiagonalDeficit_diag s β h 1 (s.m 0) ℓ t 0).symm ▸ Hℓ
  obtain ⟨ρ, hρ, δ, hδ, H⟩ := exists_uniform_constrainedPhi_left_physical_tube
    (Ω := Ω) s β h (r := 1) (hr0 := by omega) (hr := by omega)
      (v := 0) (t₀ := t₀) (by simp [s.q_zero, hq1.le]) ht₀ hboundary
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro t ht u hu n hn sk hatt
  simpa only [show k + 2 - 1 = k + 1 by omega] using
    H t ht u (by simpa only [sub_zero] using hu) hn sk hatt

/- The ordinary positive-mass physical neighbor uses the existing scalar
mass-or-lambda witness; the direct left interpolation makes its tube
two-sided without any sign restriction on the constrained overlap. -/
theorem exists_uniform_constrainedPhi_physical_left_two_sided
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 2 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u - s.q (r - 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hboundary : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∃ m ∈ Icc (s.m (r - 1) / 2) (s.m r), ∃ ℓ,
        0 < section5LeftOffDiagonalDeficit s β h r m ℓ t
          (s.q (r - 1)) (s.q (r - 1)) := by
    intro t ht
    obtain ⟨m, hm, ℓ, Hℓ⟩ := exists_section5LeftComparison_witness_at_physical_neighbor
      s β h ε hr0 hr hβ hmass hq hright ht ht₀ hmin hnear hsmall hfar
    refine ⟨m, hm, ℓ, ?_⟩
    simpa using
      (section5LeftOffDiagonalDeficit_diag s β h r m ℓ t
        (s.q (r - 1))).symm ▸ Hℓ
  exact exists_uniform_constrainedPhi_left_physical_tube s β h
    (show 1 ≤ r by omega) hr (v := s.q (r - 1)) (t₀ := t₀)
    ⟨le_rfl, hq.le⟩ ht₀ hboundary

end SpinGlass.Targets
