module

public import Targets.Section5InterpolationBound
public import Targets.Section4RightMassDerivative
public import Targets.Section4StationarityInterior

@[expose] public section

/-!
# Actual right-interval gain from increasing the inserted mass

The right endpoint bound allows the inserted scalar mass to range up to twice
the original mass. A negative derivative of the corrected scalar potential at
the original mass therefore yields a strict gain, including when that mass is
one. The chosen mass and positive deficit depend only on the scalar data, not
the system size or disorder. No identity between variable-mass left and right
families is used.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

private theorem right_mass_overlap_attainable {u : ℝ}
    [Nonempty (AT.ConstrainedPair n u)] :
    ∃ σ τ : Config n, overlap n σ τ = u := by
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  exact ⟨p.1.1, p.1.2, p.2⟩

/-- Exact scalar mass variation transported to the actual right constrained
free energy. The admissible interval extends above baseline mass one. -/
theorem constrainedPhi_le_two_guerraPsi_right_mass_variation
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t +
        2 * (section4RightT s β h r m (t * (β ^ 2 * (u - s.q r))) -
          section4RightT s β h r (s.m r) (t * (β ^ 2 * (u - s.q r)))) -
        t * (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2)) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hv := section5RightSplitVariance_mem s β ht hu
  have H := section5RightInterpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  have H0 := section5RightInterpolation_zero_le hn s β h sk.U hr hm0 ht hu
    right_mass_overlap_attainable 0
  rw [section5RightV_zero_eq_two_section4RightT s β h hr hm0 hv] at H0
  rw [section4RightT_baseline s β h hr hv]
  simp only [zero_mul, sub_zero] at H0
  unfold guerraPsi
  nlinarith

/-- A genuinely negative corrected right mass derivative gives an admissible
mass increase with strictly smaller corrected scalar potential. This only uses
differentiability at the baseline; no quantitative mass Taylor estimate is
assumed. -/
theorem exists_section5RightMass_improvement
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    (hmpos : 0 < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hD : section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
      t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) < 0) :
    ∃ m ∈ Set.Icc (s.m r) (2 * s.m r),
      2 * (section4RightT s β h r m (t * (β ^ 2 * (u - s.q r))) -
        section4RightT s β h r (s.m r) (t * (β ^ 2 * (u - s.q r)))) -
      t * (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2)) < 0 := by
  let v := t * (β ^ 2 * (u - s.q r))
  let c := t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2)
  let f := fun m => 2 * section4RightT s β h r m v - (m - s.m r) * c
  have hv : 0 ≤ v := (section5RightSplitVariance_mem s β ht hu).1
  have hd : HasDerivAt f (section4RightU s β h r v - c) (s.m r) := by
    convert ((hasDerivAt_section4RightT_mass_baseline s β h hr hv).const_mul 2).sub
      (((hasDerivAt_id (s.m r)).sub_const (s.m r)).mul_const c) using 1 <;>
      first | rfl | ring
  by_contra! H
  have hmin : ∀ m ∈ Set.Icc (s.m r) (2 * s.m r), f (s.m r) ≤ f m := by
    intro m hm
    have HH := H m hm
    dsimp [f, v, c]
    nlinarith
  have Hnonneg := derivative_nonneg_of_min_at_left (by linarith : s.m r < 2 * s.m r)
    hmin hd.hasDerivWithinAt
  exact (not_le_of_gt hD) Hnonneg

/-- A negative actual corrected mass derivative gives a positive right
constrained-free-energy deficit chosen before the system size and disorder.
The endpoint mass one is covered by increasing the auxiliary scalar mass. -/
theorem exists_constrainedPhi_right_mass_gap_uniform_in_size
    (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hmpos : 0 < s.m r) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hD : section4RightU s β h r (t * (β ^ 2 * (u - s.q r))) -
      t * (β ^ 2 / 2) * (u ^ 2 - s.q r ^ 2) < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} (_hn : 0 < n)
      (sk : SKDisorder (Ω := Ω) n β h), Nonempty (AT.ConstrainedPair n u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  obtain ⟨m, hm, hgain⟩ := exists_section5RightMass_improvement s β h hr hmpos ht hu hD
  let d := 2 * (section4RightT s β h r m (t * (β ^ 2 * (u - s.q r))) -
      section4RightT s β h r (s.m r) (t * (β ^ 2 * (u - s.q r)))) -
    t * (m - s.m r) * (β ^ 2 / 2 * (u ^ 2 - s.q r ^ 2))
  refine ⟨-d, neg_pos.mpr hgain, ?_⟩
  intro n hn sk hpair
  letI := hpair
  have hm' : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r) :=
    ⟨(s.m_mono' r hr (r - 1) (by omega)).trans hm.1, hm.2⟩
  have H := constrainedPhi_le_two_guerraPsi_right_mass_variation hn s β h sk hr0 hr hm' ht hu
  dsimp [d]
  linarith

end SpinGlass.Targets
