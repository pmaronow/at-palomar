module

public import Targets.Section5InterpolationBound
public import Targets.Section5LambdaUPrime
public import Targets.Section4QuantitativeOptimality
public import Targets.Section4Concavity

@[expose] public section

/-!
# Strict improvement of the actual left constrained free energy

The second-interpolation bound is combined with the proved lambda and mass
variations. All bounds below concern the actual constrained free energy and
the baseline `2 * guerraPsi`, not merely the time-zero auxiliary transform.
The final result implements the positive-baseline, far-left argument of
Talagrand's Proposition 5.5 with an explicit smallness condition. It does not
assert the uniform local quadratic bound or cover the initial mass-zero case.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

private theorem overlap_attainable {u : ℝ} [Nonempty (AT.ConstrainedPair n u)] :
    ∃ σ τ : Config n, overlap n σ τ = u := by
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  exact ⟨p.1.1, p.1.2, p.2⟩

/-- The optimized lambda gain transported to the actual constrained free
energy. Both time endpoints and baseline mass zero are included. -/
theorem constrainedPhi_le_two_guerraPsi_sub_factor_sq
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (section4TVarianceQ s β h r (s.m (r - 1))
          (t * (β ^ 2 * (s.q r - u))) - u) ^ 2 / 2 := by
  have hm0 := s.m_nonneg (p := r - 1) (by omega)
  have hm : s.m (r - 1) ∈ Set.Icc (s.m (r - 1) / 2) (s.m r) :=
    ⟨by linarith, s.m_mono' r hr (r - 1) (by omega)⟩
  have H := section5Interpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  have H0 := section5Interpolation_zero_lambda_gain_Q hn s β h sk.U hr0 hr ht hu
    overlap_attainable
  simp only [sub_self, zero_mul, add_zero] at H
  unfold guerraPsi
  linarith

/-- A nonzero actual lambda slope error gives strict improvement below
`2 ψ(t)`, without an optimality or stationarity assumption. -/
theorem constrainedPhi_lt_two_guerraPsi_of_factor_ne
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hQ : section4TVarianceQ s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) ≠ u) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  have H := constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk hr0 hr ht hu
  have Hpos := sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)
  linarith

/-- The full mass Taylor estimate transported through the second
interpolation. The allowed mass interval includes decreases from a positive
baseline, as required by Proposition 5.5. -/
theorem constrainedPhi_le_two_guerraPsi_mass_taylor
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t +
        (section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
          t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)) * (m - s.m (r - 1)) +
        2 * section4MassSecondBound (β ^ 2) * (m - s.m (r - 1)) ^ 2 := by
  have ha : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hm0 : 0 ≤ m := (by linarith [ha.1, hm.1])
  have hb : m ∈ Set.Icc (0 : ℝ) 1 := ⟨hm0, hm.2.trans (s.m_le_one hr)⟩
  have hv := section5SplitVariance_mem s β ht hu
  have H := section5Interpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  have H0 := section5Interpolation_zero_le hn s β h sk.U hr0 hr hm0 ht hu
    overlap_attainable 0
  rw [section5V_zero_eq_two_section4T s β h hr0 hr hm0 hv] at H0
  simp only [zero_mul, sub_zero] at H0
  have HT := (abs_le.mp (section4T_mass_taylor_bound s β h hr ha hb hv)).2
  rw [(hasDerivAt_section4T_mass_baseline s β h hr0 hr hv).deriv,
    section4T_baseline s β h hr0 hr hv] at HT
  unfold guerraPsi
  nlinarith only [H, H0, HT]

/-- A positive mass slope gives an explicit improvement by decreasing a
positive baseline mass. The deficit is independent of the system size and
disorder realization; the perturbation stays in the actual admissible interval. -/
theorem constrainedPhi_le_two_guerraPsi_sub_mass_gain
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hD : 0 < section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
      t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)) :
    let D := section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
      t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t -
      D / 2 * min (s.m (r - 1) / 2) (D / (4 * (section4MassSecondBound (β ^ 2) + 1))) := by
  let a := s.m (r - 1)
  let C := section4MassSecondBound (β ^ 2)
  let D := section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
    t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)
  let δ := min (a / 2) (D / (4 * (C + 1)))
  have hC : 0 ≤ C := section4MassSecondBound_nonneg _
  have hden : 0 < 4 * (C + 1) := by positivity
  have hδ : 0 < δ := lt_min (by dsimp [a]; linarith) (div_pos hD hden)
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδD : 4 * (C + 1) * δ ≤ D := by
    have H := (le_div_iff₀ hden).mp (min_le_right (a / 2) (D / (4 * (C + 1))))
    simpa only [mul_comm] using H
  have hm : a - δ ∈ Set.Icc (s.m (r - 1) / 2) (s.m r) := by
    have ha : a ≤ s.m r := s.m_mono' r hr (r - 1) (by omega)
    change a / 2 ≤ a - δ ∧ a - δ ≤ s.m r
    constructor <;> linarith
  have H := constrainedPhi_le_two_guerraPsi_mass_taylor hn s β h sk hr0 hr hm ht hu
  change constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
    2 * guerraPsi s β h t + D * (a - δ - a) + 2 * C * (a - δ - a) ^ 2 at H
  have HC := mul_le_mul_of_nonneg_right hδD hδ.le
  change constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - D / 2 * δ
  nlinarith only [H, HC, sq_nonneg δ]

/-- Strict improvement from the explicit positive mass deficit. The initial
mass-zero interval is deliberately excluded from this downward variation. -/
theorem constrainedPhi_lt_two_guerraPsi_of_mass_slope_pos
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hD : 0 < section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
      t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  have H := constrainedPhi_le_two_guerraPsi_sub_mass_gain hn s β h sk hr0 hr hmpos ht hu hD
  have hden : 0 < 4 * (section4MassSecondBound (β ^ 2) + 1) := by
    linarith [section4MassSecondBound_nonneg (β ^ 2)]
  exact H.trans_lt (sub_lt_self _ (mul_pos (div_pos hD (by norm_num))
    (lt_min (by linarith) (div_pos hD hden))))

/-- The far-left strict bound of Proposition 5.5, with its smallness condition
stated explicitly. The first-variation bound is deduced from actual fixed-level
and near-global optimality. A positive baseline is essential here; the initial
mass-zero interval requires the separate argument in the paper. -/
theorem constrainedPhi_lt_two_guerraPsi_of_left_gap
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (s.q r - u) ^ 2) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u < 2 * guerraPsi s β h t := by
  by_cases hQ : section4TVarianceQ s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) = u
  · have hf := section4FirstVariation_lower_bound s β h ε hr0 hr hgap hu hmin hnear
    have hm : s.m (r - 1) < 1 := hgap.trans_le (s.m_le_one hr)
    have H := section4U_interpolation_slope_lower_bound_of_factor_eq s β h hr0 hr hm
      hu ht hQ (by simpa only [neg_mul] using hf)
    apply constrainedPhi_lt_two_guerraPsi_of_mass_slope_pos hn s β h sk hr0 hr hmpos ht hu
    linarith
  · exact constrainedPhi_lt_two_guerraPsi_of_factor_ne hn s β h sk hr0 hr ht hu hQ

/-- The far-left deficit is chosen before the system size and the SK disorder.
Pointwise strict inequalities alone would not justify the later uniform-in-size
argument; this statement retains the explicit scalar deficit. -/
theorem exists_constrainedPhi_left_gap_uniform_in_size
    (s : RSBScheme k) (β h ε : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (hmpos : 0 < s.m (r - 1)) (hgap : s.m (r - 1) < s.m r)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : 2 * section4OptimalityBound β * Real.sqrt ε <
      (1 - t) * (β ^ 2 / 2) * (s.q r - u) ^ 2) :
    ∃ c > 0, ∀ {n : ℕ} (_hn : 0 < n) (sk : SKDisorder (Ω := Ω) n β h),
      Nonempty (AT.ConstrainedPair n u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - c := by
  by_cases hQ : section4TVarianceQ s β h r (s.m (r - 1))
      (t * (β ^ 2 * (s.q r - u))) = u
  · let D := section4U s β h r (t * (β ^ 2 * (s.q r - u))) -
      t * (β ^ 2 / 2) * (s.q r ^ 2 - u ^ 2)
    have hf := section4FirstVariation_lower_bound s β h ε hr0 hr hgap hu hmin hnear
    have H := section4U_interpolation_slope_lower_bound_of_factor_eq s β h hr0 hr
      (hgap.trans_le (s.m_le_one hr)) hu ht hQ (by simpa only [neg_mul] using hf)
    have hD : 0 < D := by dsimp [D]; linarith
    let δ := min (s.m (r - 1) / 2) (D / (4 * (section4MassSecondBound (β ^ 2) + 1)))
    have hden : 0 < 4 * (section4MassSecondBound (β ^ 2) + 1) := by
      linarith [section4MassSecondBound_nonneg (β ^ 2)]
    have hδ : 0 < δ := lt_min (by linarith) (div_pos hD hden)
    refine ⟨D / 2 * δ, mul_pos (div_pos hD (by norm_num)) hδ, ?_⟩
    intro n hn sk hpair
    letI := hpair
    exact constrainedPhi_le_two_guerraPsi_sub_mass_gain hn s β h sk hr0 hr hmpos ht hu hD
  · refine ⟨(section4TVarianceQ s β h r (s.m (r - 1))
        (t * (β ^ 2 * (s.q r - u))) - u) ^ 2 / 2,
      div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hQ)) (by norm_num), ?_⟩
    intro n hn sk hpair
    letI := hpair
    exact constrainedPhi_le_two_guerraPsi_sub_factor_sq hn s β h sk hr0 hr ht hu

end SpinGlass.Targets
