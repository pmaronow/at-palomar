module

public import Paper.DiracConditionalLaw
public import Paper.DiracSoftMoment
public import Paper.SoftMomentStrict
public import Paper.MomentEndpoints

@[expose] public section

/-! Physical RS moments and variational signs on the constructed Brownian state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Paper

/-- Actual post-interface squared-magnetization expectation. -/
def physicalHardSecondMoment (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) : ℝ :=
  ∫ ω, Real.tanh (canonicalDiracStateReal β h q hq ω t) ^ 2 ∂canonicalBrownianMeasure

/-- Actual post-interface fourth-sech expectation. -/
def physicalHardFourthMoment (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) : ℝ :=
  ∫ ω, sech (canonicalDiracStateReal β h q hq ω t) ^ 4 ∂canonicalBrownianMeasure

theorem physicalHardSecondMoment_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    physicalHardSecondMoment β h q hq t = hardSecondMoment β h q t := by
  have hl := (hasLaw_canonicalDiracState_after β h q hq ht).integral_comp
    ((gaussian_continuous_tanh.pow 2).measurable.aestronglyMeasurable)
  simp only [Function.comp_apply, Pi.pow_apply] at hl
  unfold physicalHardSecondMoment
  rw [hl, integral_gaussianDoobMarginal_bounded β h q t.toNNReal
    (fun y => Real.tanh y ^ 2) (gaussian_continuous_tanh.pow 2).measurable 1
    (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact tanh_sq_le_one y)]
  rw [Real.coe_toNNReal t (hq.1.trans ht.1)]
  rfl

theorem physicalHardFourthMoment_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    physicalHardFourthMoment β h q hq t = hardFourthMoment β h q t := by
  have hl := (hasLaw_canonicalDiracState_after β h q hq ht).integral_comp
    ((continuous_sech.pow 4).measurable.aestronglyMeasurable)
  simp only [Function.comp_apply, Pi.pow_apply] at hl
  unfold physicalHardFourthMoment
  rw [hl, integral_gaussianDoobMarginal_bounded β h q t.toNNReal
    (fun y => sech y ^ 4) (continuous_sech.pow 4).measurable 1
    (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos y).le 4)]
      exact pow_le_one₀ (sech_pos y).le (sech_le_one y))]
  rw [Real.coe_toNNReal t (hq.1.trans ht.1)]
  rfl

/-- The explicit RS potential from the paper, assembled at its interface. -/
def explicitRSPotential (β q t x : ℝ) : ℝ :=
  if t ≤ q then rsSoftPotential β q t x else rsHardPotential β t x

/-- Its actual spatial gradient, assembled from the two proved formulas. -/
def explicitRSGradient (β q t x : ℝ) : ℝ :=
  if t ≤ q then rsSoftDx β q t x else Real.tanh x

theorem deriv_explicitRSPotential (β q t x : ℝ) :
    deriv (explicitRSPotential β q t) x = explicitRSGradient β q t x := by
  by_cases ht : t ≤ q
  · have he : explicitRSPotential β q t = rsSoftPotential β q t :=
      funext fun x => by simp [explicitRSPotential, ht]
    rw [he]
    simp only [explicitRSGradient, ite_eq_left ht]
    exact deriv_rsSoftPotential_spatial β q t x
  · have he : explicitRSPotential β q t = rsHardPotential β t :=
      funext fun x => by simp [explicitRSPotential, ht]
    rw [he]
    simp only [explicitRSGradient, ite_eq_right ht]
    exact deriv_rsHardPotential_spatial β t x

/-- Squared spatial gradient of the explicit RS potential along the actual
Brownian state; this is the paper's stochastic observable `f`. -/
def physicalRSSecondMoment (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) : ℝ :=
  ∫ ω, explicitRSGradient β q t (canonicalDiracStateReal β h q hq ω t) ^ 2
    ∂canonicalBrownianMeasure

theorem physicalRSSecondMoment_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (hβ : 0 ≤ β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    physicalRSSecondMoment β h q hq t = rsSecondMoment β h q t := by
  by_cases hsoft : t ≤ q
  · simp only [physicalRSSecondMoment, explicitRSGradient, hsoft, ite_eq_left]
    rw [diracSoftMoment_eq β h q hq hβ ⟨ht.1, hsoft⟩]
    exact (rsSecondMoment_eq_soft hsoft).symm
  · simp only [physicalRSSecondMoment, explicitRSGradient, hsoft, ite_eq_right]
    change physicalHardSecondMoment β h q hq t = _
    rw [physicalHardSecondMoment_eq β h q hq ⟨(lt_of_not_ge hsoft).le, ht.2⟩]
    exact (rsSecondMoment_eq_hard (lt_of_not_ge hsoft)).symm

/-- Proposition 5.2 for the actual Brownian state. -/
theorem physicalRSSecondMoment_right_sign {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc q (1 : ℝ)) : physicalRSSecondMoment β h q hq t ≤ t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1, ht.2⟩]
  exact rsSecondMoment_right_sign hβ hh hq hfixed hAT ht

theorem physicalRSSecondMoment_right_strict {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Ioc q (1 : ℝ)) : physicalRSSecondMoment β h q hq t < t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1.le, ht.2⟩]
  exact rsSecondMoment_right_strict hβ hh hq hfixed hAT ht

theorem physicalRSSecondMoment_left_sign {β h q t : ℝ}
    (hβ : 0 ≤ β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) q) : t ≤ physicalRSSecondMoment β h q hq t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ ⟨ht.1, ht.2.trans hq.2⟩]
  exact rsSecondMoment_left_sign hβ ht hfixed hAT

theorem physicalRSSecondMoment_left_strict {β h q t : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Ico (0 : ℝ) q) : t < physicalRSSecondMoment β h q hq t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ.le ⟨ht.1, ht.2.le.trans hq.2⟩]
  exact rsSecondMoment_left_strict hβ ht hfixed hAT

/-- The paper's variational observable formed with the actual stochastic
state and spatial gradient of the explicit RS potential. -/
def physicalRSParisiG (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) : ℝ :=
  parisiG β (physicalRSSecondMoment β h q hq) t

theorem physicalRSParisiG_eq (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hβ : 0 ≤ β)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    physicalRSParisiG β h q hq t = rsParisiG β h q t := by
  unfold physicalRSParisiG rsParisiG parisiG
  apply intervalIntegral.integral_congr
  intro s hs
  have hsub : uIcc t (1 : ℝ) ⊆ Icc (0 : ℝ) 1 :=
    (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) 1)).uIcc_subset ht ⟨zero_le_one, le_rfl⟩
  dsimp only
  rw [physicalRSSecondMoment_eq β h q hq hβ (hsub hs)]

theorem physicalRSParisiG_minimum {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, physicalRSParisiG β h q hq q ≤ physicalRSParisiG β h q hq t := by
  intro t ht
  rw [physicalRSParisiG_eq β h q hq hβ.le hq, physicalRSParisiG_eq β h q hq hβ.le ht]
  exact rsParisiG_minimum hβ hh hq hfixed hAT t ht

theorem physicalRSParisiG_unique_minimum {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    physicalRSParisiG β h q hq t = physicalRSParisiG β h q hq q ↔ t = q := by
  rw [physicalRSParisiG_eq β h q hq hβ.le ht, physicalRSParisiG_eq β h q hq hβ.le hq]
  exact rsParisiG_eq_minimum_iff hβ hh hq hfixed hAT ht


/-- Proposition 5.2 with exactly the small-variance and fixed-point inputs;
no AT assumption is needed in this regime. -/
theorem physicalRSSecondMoment_right_of_small_variance {β h q t : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hsmall : β ^ 2 * (1 - q) ≤ 1)
    (ht : t ∈ Icc q (1 : ℝ)) : physicalRSSecondMoment β h q hq t ≤ t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1, ht.2⟩,
    rsSecondMoment_eq_hard_of_le hq.1 ht.1]
  rcases ht.1.eq_or_lt with he | he
  · subst t
    exact (hardSecondMoment_initial_fixed hq.1 hfixed).le
  · exact (hardSecondMoment_lt_time_of_small_variance hβ hq hfixed hsmall t ⟨he, ht.2⟩).le

/-- Proposition 5.5's strict inequality for the genuine Brownian state under
the paper's explicit small-field hypothesis. -/
theorem physicalRSSecondMoment_right_strict_of_small_field {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (hfield : h ≤ β ^ 2 * q) (ht : t ∈ Ioc q (1 : ℝ)) :
    physicalRSSecondMoment β h q hq t < t := by
  rw [physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1.le, ht.2⟩,
    rsSecondMoment_eq_hard ht.1]
  exact hardSecondMoment_lt_time_of_small_field hβ hh hq hfixed hAT hfield t ht

/-- The actual fourth moment obeys the exact exponential envelope used in
Proposition 5.4 and Proposition 5.5. -/
theorem physicalHardFourthMoment_exponential_decay {β h q t : ℝ}
    (hβ : β ≠ 0) (hq : q ∈ Icc (0 : ℝ) 1) (hqpos : 0 < q)
    (hh : 0 ≤ h) (hfield : h ≤ β ^ 2 * q) (ht : t ∈ Icc q (1 : ℝ)) :
    β ^ 2 * physicalHardFourthMoment β h q hq t ≤
      atParameter β h q * Real.exp (-(β ^ 2 * (t - q)) / 2) := by
  rw [physicalHardFourthMoment_eq β h q hq ht]
  exact hardFourthMoment_exponential_decay hβ hqpos hh hfield ht.1

/-- The actual second moment's right derivative at the interface is the
literal AT parameter, including the equality boundary of the AT condition. -/
theorem hasDerivWithinAt_physicalHardSecondMoment_interface
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hqone : q < 1) :
    HasDerivWithinAt (physicalHardSecondMoment β h q hq) (atParameter β h q) (Ici q) q := by
  have he := hasDerivWithinAt_physicalMoment_interface (β := β) (h := h) hqone
    (fun t ht => physicalHardSecondMoment_eq β h q hq ht)
  simpa only [hardFourthMoment_initial hq.1] using he

/-- The actual second moment's left derivative at the terminal endpoint. -/
theorem hasDerivWithinAt_physicalHardSecondMoment_terminal
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hqone : q < 1) :
    HasDerivWithinAt (physicalHardSecondMoment β h q hq)
      (β ^ 2 * physicalHardFourthMoment β h q hq 1) (Iic 1) 1 := by
  rw [physicalHardFourthMoment_eq β h q hq ⟨hq.2, le_rfl⟩]
  exact hasDerivWithinAt_physicalMoment_terminal hqone
    (fun t ht => physicalHardSecondMoment_eq β h q hq ht)

/-- Interior derivative identity for the genuine physical second moment. -/
theorem hasDerivAt_physicalHardSecondMoment
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo q (1 : ℝ)) :
    HasDerivAt (physicalHardSecondMoment β h q hq)
      (β ^ 2 * physicalHardFourthMoment β h q hq t) t := by
  rw [physicalHardFourthMoment_eq β h q hq ⟨ht.1.le, ht.2.le⟩]
  apply (hasDerivAt_hardSecondMoment β h q ht.1).congr_of_eventuallyEq
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
  exact fun s hs => physicalHardSecondMoment_eq β h q hq ⟨hs.1.le, hs.2.le⟩

end Paper
