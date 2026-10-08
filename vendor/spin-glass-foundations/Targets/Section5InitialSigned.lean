module

public import Targets.Section5SignedInitialConditioning
public import Targets.Section5RetainedSignedSlope
public import Targets.Section5LeftUniform

@[expose] public section

/-!
# Proposition 5.4: the negative initial overlap interval

The exact second-replica reflection and conditioning bridge transports the
retained-field zero-time gain to the original constrained free energy.
The endpoint curvature input comes from the original minimizing scheme,
with the same explicit beta-only smallness constant as Proposition 5.3.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The signed initial estimate for the actual constrained free energy from
the actual initial endpoint curvature data. The point `u=0` is included. -/
theorem constrainedPhi_initial_signed_of_endpoint_curvature
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t t₀ u e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)]
    (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / 8 * u ^ 2 := by
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have Hzero := section5SignedInitialFieldEndpoint_quantitative_gain hn s β h ht ht₀ hu
    ⟨p.1.1, p.1.2, p.2⟩ he he_small hR
  have H := section5SignedInitialInterpolation_endpoint_bound hn s β h sk
    ⟨ht.1, ht.2.trans ht₀.le⟩ hu
  unfold guerraPsi
  linarith only [Hzero, H]

/-- Proposition 5.4 in the exact-covariance SK setting, quantitatively:
the original fixed-level and near-global minimality assumptions supply all
curvature data. No signed interpolation or derivative identity is assumed. -/
theorem constrainedPhi_initial_signed_uniform
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Ico (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t - (1 - t₀) ^ 2 / 8 * u ^ 2 := by
  have hq : 0 < s.q 1 := by linarith [hu.1, hu.2]
  obtain ⟨_, e, he, he_small, hR⟩ := section5Initial_curvature_data s β h ε hβ hm hq
    hright (by norm_num : (0 : ℝ) ≤ 535) hmin hnear hsmall
    (fun v hv w hw => section4THessianSquare_lipschitz_uniform s β h (r := 1) le_rfl
      (by omega) (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hv)
      (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hw))
  exact constrainedPhi_initial_signed_of_endpoint_curvature hn s β h sk ht ht₀
    ⟨hu.1, hu.2.le⟩ he he_small hR

/-- Talagrand's strict conclusion in Proposition 5.4. The explicit deficit
above is positive at every negative attainable initial overlap. -/
theorem constrainedPhi_initial_signed_lt
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Ico (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 1) t u < 2 * guerraPsi s β h t := by
  have H := constrainedPhi_initial_signed_uniform hn s β h ε sk hβ hm hright
    ht ht₀ hu hmin hnear hsmall
  have hd : 0 < (1 - t₀) ^ 2 / 8 * u ^ 2 :=
    mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num))
      (sq_pos_of_ne_zero (ne_of_lt hu.2))
  exact H.trans_lt (sub_lt_self _ hd)

end SpinGlass.Targets
