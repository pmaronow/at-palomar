module

public import Targets.Section4TerminalFactors
public import Targets.Section5RightPressureGain
public import Targets.Section5TerminalLambda

@[expose] public section

/-!
# The local right overlap estimate of Proposition 5.2

The reflected next-level factor has positive variance derivative. Its actual
lambda slope therefore has derivative `t β² R - 1`, as on the left interval.
The proved universal Lipschitz estimate, endpoint stationarity and endpoint
curvature give the local negative slope and its quadratic pressure gain.
Redundant terminal padding extends these statements to every physical level,
including the possibly nontrivial interval `[q_(k+1),1]`.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The right lambda slope expressed through the reflected actual factor. -/
noncomputable def section5RightSlope {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (t u : ℝ) : ℝ :=
  section4RightQ s β h r (t * (β ^ 2 * (u - s.q r))) - u

private theorem right_split_mem {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    t * (β ^ 2 * (u - s.q r)) ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) := by
  constructor
  · exact mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1))
  · exact (mul_le_of_le_one_left (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hu.1)) ht.2).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hu.2 _) (sq_nonneg β))

/-- The actual right slope has its inward derivative at both overlap
endpoints, including time zero and degenerate physical variance intervals. -/
theorem hasDerivWithinAt_section5RightSlope {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) :
    HasDerivWithinAt (section5RightSlope s β h r t)
      (t * β ^ 2 * section4RightR s β h r (t * (β ^ 2 * (u - s.q r))) - 1)
      (Set.Icc (s.q r) (s.q (r + 1))) u := by
  have hmap : Set.MapsTo (fun z => t * (β ^ 2 * (z - s.q r)))
      (Set.Icc (s.q r) (s.q (r + 1)))
      (Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r))) :=
    fun z hz => right_split_mem s β ht hz
  have H := (hasDerivWithinAt_section4RightQ_all_levels s β h hr (hmap hu)).comp u
    ((((hasDerivAt_id u).sub_const (s.q r)).const_mul (β ^ 2)).const_mul t).hasDerivWithinAt hmap
  unfold section5RightSlope
  convert! H.sub ((hasDerivAt_id u).hasDerivWithinAt) using 1
  ring

/-- The right local slope estimate in Proposition 5.2. Only the endpoint
stationarity and curvature inequalities remain inputs; the full-interval
Hessian Lipschitz estimate is already proved with the universal constant 535. -/
theorem section5RightSlope_le_local_of_endpoint_curvature
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ} (hr : r ≤ k + 1)
    {t t₀ u e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hQ : section4RightQ s β h r 0 = s.q r)
    (hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : 535 * β ^ 4 * (u - s.q r) ≤ (1 - t₀) / 4) :
    section5RightSlope s β h r t u ≤ -(1 - t₀) / 2 * (u - s.q r) := by
  have ht1 : t ∈ Set.Icc 0 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hsub : Set.Icc (s.q r) u ⊆ Set.Icc (s.q r) (s.q (r + 1)) :=
    Set.Icc_subset_Icc le_rfl hu.2
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    ⟨le_rfl, mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (hu.1.trans hu.2))⟩
  have hderiv (z : ℝ) (hz : z ∈ Set.Icc (s.q r) u) :
      HasDerivWithinAt (section5RightSlope s β h r t)
        (t * β ^ 2 * section4RightR s β h r (t * (β ^ 2 * (z - s.q r))) - 1)
        (Set.Icc (s.q r) u) z :=
    (hasDerivWithinAt_section5RightSlope s β h hr ht1 (hsub hz)).mono hsub
  have hbound (z : ℝ) (hz : z ∈ Set.Icc (s.q r) u) :
      t * β ^ 2 * section4RightR s β h r (t * (β ^ 2 * (z - s.q r))) - 1 ≤
        -(1 - t₀) / 2 := by
    have hv := right_split_mem s β ht1 (hsub hz)
    have hvle : t * (β ^ 2 * (z - s.q r)) ≤ β ^ 2 * (u - s.q r) :=
      (mul_le_of_le_one_left (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.1)) ht1.2).trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2 _) (sq_nonneg β))
    have H := (abs_le.mp (section4RightR_lipschitz_uniform_all_levels s β h hr hv hzero)).2
    rw [sub_zero, abs_of_nonneg hv.1] at H
    have HL := mul_le_mul_of_nonneg_left hvle (by norm_num : (0 : ℝ) ≤ 535)
    have HR : section4RightR s β h r (t * (β ^ 2 * (z - s.q r))) ≤
        section4RightR s β h r 0 + 535 * β ^ 2 * (u - s.q r) := by
      nlinarith only [H, HL]
    have Hscaled := mul_le_mul_of_nonneg_left HR (mul_nonneg ht.1 (sq_nonneg β))
    have Hbase := mul_le_mul_of_nonneg_left hR ht.1
    have He := mul_le_of_le_one_left he ht1.2
    have Hlocal := mul_le_of_le_one_left
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 535)
        (by positivity : 0 ≤ β ^ 4)) (sub_nonneg.mpr hu.1)) ht1.2
    nlinarith only [Hscaled, Hbase, He, Hlocal, ht.2, he_small, hu_small]
  have hc : ContinuousOn (section5RightSlope s β h r t) (Set.Icc (s.q r) u) :=
    fun z hz => (hderiv z hz).continuousWithinAt
  have hd : DifferentiableOn ℝ (section5RightSlope s β h r t) (interior (Set.Icc (s.q r) u)) := by
    rw [interior_Icc]
    exact fun z hz => ((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt
      (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
  have HB : ∀ z ∈ interior (Set.Icc (s.q r) u), deriv (section5RightSlope s β h r t) z ≤
      -(1 - t₀) / 2 := by
    rw [interior_Icc]
    intro z hz
    rw [((hderiv z ⟨hz.1.le, hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2)).deriv]
    exact hbound z ⟨hz.1.le, hz.2.le⟩
  have H := (convex_Icc (s.q r) u).image_sub_le_mul_sub_of_deriv_le hc hd HB
    (s.q r) ⟨le_rfl, hu.1⟩ u ⟨hu.1, le_rfl⟩ hu.1
  have Hzero : section5RightSlope s β h r t (s.q r) = 0 := by
    simp only [section5RightSlope, sub_self, mul_zero, hQ]
  rwa [Hzero, sub_zero] at H

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The actual right lambda optimization expressed through the reflected
factor. This transports a proved derivative identity, not an assumed bridge. -/
theorem constrainedPhi_le_two_guerraPsi_sub_right_factor_sq
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t - (section5RightSlope s β h r t u) ^ 2 / 2 := by
  have H := constrainedPhi_le_guerraPsi_right_lambda_gain hn s β h sk hr0 (by omega) ht hu
  rw [deriv_section5RightV_zero_eq_Q_all_levels s β h hr (right_split_mem s β ht hu)] at H
  exact H

/-- Proposition 5.2's local quadratic gain for the actual constrained free
energy, conditional only on endpoint stationarity and endpoint curvature.
All factor differentiation, regularity, lambda identities and interpolation
are proved; the estimate holds at time zero and both overlap endpoints. -/
theorem constrainedPhi_local_right_of_endpoint_curvature
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {t t₀ u e : ℝ}
    (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)]
    (hQ : section4RightQ s β h r 0 = s.q r)
    (hR : β ^ 2 * section4RightR s β h r 0 ≤ 1 + e)
    (he_small : e ≤ (1 - t₀) / 4)
    (hu_small : 535 * β ^ 4 * (u - s.q r) ≤ (1 - t₀) / 4) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / 8 * (u - s.q r) ^ 2 := by
  have Hslope := section5RightSlope_le_local_of_endpoint_curvature s β h hr ht ht₀ he
    hu hQ hR he_small hu_small
  have H := constrainedPhi_le_two_guerraPsi_sub_right_factor_sq hn s β h sk hr0 hr
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  have Hnonneg : 0 ≤ (1 - t₀) / 2 * (u - s.q r) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num)) (sub_nonneg.mpr hu.1)
  have Hneg : (1 - t₀) / 2 * (u - s.q r) ≤ -section5RightSlope s β h r t u := by
    linarith only [Hslope]
  have Hsquare := mul_self_le_mul_self Hnonneg Hneg
  nlinarith only [H, Hsquare]

end SpinGlass.Targets
