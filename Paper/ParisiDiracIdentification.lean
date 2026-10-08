module

public import Paper.ParisiPDEFormula
public import Paper.PhysicalMoments
public import Paper.ParisiBrownianState
public import Paper.ParisiSelectedState

@[expose] public section

/-!
# Identification of the actual general Parisi solution at a Dirac measure

The exact zero-step RSB scheme has the actual law `δ_q`. Its continuous-time
Cole--Hopf recursion is the paper's explicit soft/hard potential. Bounded mild
uniqueness therefore identifies the constructed arbitrary-measure PDE selector
with these formulas, without assuming general weak uniqueness.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal Topology

namespace Paper
open SpinGlass SpinGlass.Targets

theorem parisiSchemeMeasure_rsScheme (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    parisiSchemeMeasure (rsScheme q hq.1 hq.2) = diracOverlap q hq := by
  apply ProbabilityMeasure.toMeasure_injective
  change parisiSchemeRawMeasure (rsScheme q hq.1 hq.2) = Measure.dirac (⟨q, hq⟩ : Overlap)
  simp [parisiSchemeRawMeasure, rsScheme, parisiSchemeAtom]

theorem parisiStep_one_logcosh (v x : ℝ) (hv : 0 ≤ v) :
    parisiStep 1 v (fun y => Real.log (Real.cosh y)) x =
      Real.log (Real.cosh x) + v / 2 := by
  rw [parisiStep, ite_eq_right one_ne_zero]
  have he : ∀ z : ℝ, Real.exp (1 * Real.log (Real.cosh (x + Real.sqrt v * z))) =
      Real.cosh (x + Real.sqrt v * z) := fun z => by
    rw [one_mul, Real.exp_log (Real.cosh_pos _)]
  rw [integral_congr_ae (.of_forall he), integral_cosh_add_mul_stdGaussian,
    Real.sq_sqrt hv, Real.log_mul (Real.cosh_pos x).ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem parisiF_rsScheme_one (β q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    parisiF (rsScheme q hq.1 hq.2) β 1 =
      fun x => Real.log (Real.cosh x) + β ^ 2 * (1 - q) / 2 := by
  funext x
  simpa [parisiF, rsScheme] using
    parisiStep_one_logcosh (β ^ 2 * (1 - q)) x
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq.2))

theorem parisiFinitePotential_rsScheme (β q : ℝ) (hβ : 0 ≤ β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiFinitePotential (rsScheme q hq.1 hq.2) β (t, x) =
      explicitRSPotential β q t x := by
  rw [parisiFinitePotential]
  simp only [min_eq_right ht.2, max_eq_right ht.1]
  change (if t ≤ q then parisiStep 0 (β ^ 2 * (q - t))
    (parisiF (rsScheme q hq.1 hq.2) β 1) x
    else if t ≤ 1 then parisiStep 1 (β ^ 2 * (1 - t))
      (fun y => Real.log (Real.cosh y)) x else Real.log (Real.cosh x)) = _
  by_cases htq : t ≤ q
  · rw [ite_eq_left htq]
    rw [parisiF_rsScheme_one β q hq, parisiStep, ite_eq_left rfl]
    rw [integral_add (integrable_gaussian_logcosh_affine x (Real.sqrt (β ^ 2 * (q - t))))
      (integrable_const _)]
    simp only [integral_const]
    rw [explicitRSPotential, ite_eq_left htq, rsSoftPotential_eq_variance β q t x hβ]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
      gaussianExpectation]
    ring
  · rw [ite_eq_right htq, ite_eq_left ht.2]
    rw [parisiStep_one_logcosh (β ^ 2 * (1 - t)) x
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2))]
    simp only [explicitRSPotential, ite_eq_right htq, rsHardPotential]
    ring

/-- Proposition 3.1: the paper's explicit formula is the actual constructed
arbitrary-measure weak PDE potential at the Dirac law. -/
theorem parisiPotential_dirac_eq_explicit (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiPotential β (diracOverlap q hq) (t, x) = explicitRSPotential β q t x := by
  rw [← parisiSchemeMeasure_rsScheme q hq,
    parisiSchemePotential_eq_actual _ β hβ.ne' t x ht]
  exact parisiFinitePotential_rsScheme β q hβ.le hq t x ht

theorem parisiGradient_dirac_eq_explicit (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiGradient β (diracOverlap q hq) (t, x) = explicitRSGradient β q t x := by
  have he : (fun y => parisiPotential β (diracOverlap q hq) (t, y)) =
      explicitRSPotential β q t :=
    funext (fun y => parisiPotential_dirac_eq_explicit β q hβ hq t y ht)
  rw [← (hasDerivAt_parisiPotential_spatial β hβ.ne' (diracOverlap q hq) t x ht).deriv,
    he, deriv_explicitRSPotential]

theorem parisiPotential_dirac_soft (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    parisiPotential β (diracOverlap q hq) (t, x) = rsSoftPotential β q t x := by
  rw [parisiPotential_dirac_eq_explicit β q hβ hq t x ⟨ht.1, ht.2.trans hq.2⟩,
    explicitRSPotential, ite_eq_left ht.2]

theorem parisiPotential_dirac_hard (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc q (1 : ℝ)) :
    parisiPotential β (diracOverlap q hq) (t, x) = rsHardPotential β t x := by
  rw [parisiPotential_dirac_eq_explicit β q hβ hq t x ⟨hq.1.trans ht.1, ht.2⟩]
  rcases ht.1.eq_or_lt with he | he
  · subst t
    simp [explicitRSPotential, rsPotential_interface]
  · simp [explicitRSPotential, not_le.mpr he]

theorem parisiGradient_dirac_soft (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    parisiGradient β (diracOverlap q hq) (t, x) = rsSoftDx β q t x := by
  rw [parisiGradient_dirac_eq_explicit β q hβ hq t x ⟨ht.1, ht.2.trans hq.2⟩,
    explicitRSGradient, ite_eq_left ht.2]

theorem parisiGradient_dirac_hard (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc q (1 : ℝ)) :
    parisiGradient β (diracOverlap q hq) (t, x) = Real.tanh x := by
  rw [parisiGradient_dirac_eq_explicit β q hβ hq t x ⟨hq.1.trans ht.1, ht.2⟩]
  rcases ht.1.eq_or_lt with he | he
  · subst t
    simp [explicitRSGradient]
  · simp [explicitRSGradient, not_le.mpr he]

theorem parisiHessian_dirac_soft (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    parisiHessian β (diracOverlap q hq) (t, x) = rsSoftDxx β q t x := by
  unfold parisiHessian
  have he : (fun y => parisiGradient β (diracOverlap q hq) (t, y)) = rsSoftDx β q t :=
    funext (fun y => parisiGradient_dirac_soft β q hβ hq t y ht)
  rw [he, (hasDerivAt_rsSoftDx_spatial β q t x).deriv]

/-- The hard-side second derivative in Proposition 3.1 belongs to the actual
general Parisi selector, including the interface and terminal endpoint. -/
theorem parisiHessian_dirac_hard (β q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t x : ℝ) (ht : t ∈ Icc q (1 : ℝ)) :
    parisiHessian β (diracOverlap q hq) (t, x) = sech x ^ 2 := by
  unfold parisiHessian
  have he : (fun y => parisiGradient β (diracOverlap q hq) (t, y)) = Real.tanh :=
    funext (fun y => parisiGradient_dirac_hard β q hβ hq t y ht)
  rw [he, deriv_tanh]

/-- The actual general PDE functional at `δ_q` equals the paper's RS value. -/
theorem parisiPDEFunctional_dirac_eq_rsFreeEnergy (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) :
    parisiPDEFunctional β h (diracOverlap q hq) = rsFreeEnergy β h q := by
  apply parisiFunctional_dirac_eq_rsFreeEnergy hq
  rw [parisiPotential_dirac_soft β q hβ hq 0 h ⟨le_rfl, hq.1⟩]
  exact rsSoftPotential_zero β h q

/-- The existing Dirac strong state also satisfies the actual general-CDF
integral equation, with its actual identified PDE gradient. -/
theorem canonicalDiracState_general_equation (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    canonicalDiracStateReal β h q hq ω t = h + β * canonicalDiracNoise ω t +
      ∫ s in 0..t, β ^ 2 * parisiCDF (diracOverlap q hq) s *
        parisiGradient β (diracOverlap q hq) (s, canonicalDiracStateReal β h q hq ω s) := by
  let X := canonicalDiracStateReal β h q hq ω
  let f := fun s => β ^ 2 * parisiCDF (diracOverlap q hq) s *
    parisiGradient β (diracOverlap q hq) (s, X s)
  have hzero {b : ℝ} (hb : b ∈ Icc (0 : ℝ) q) :
      EqOn f (fun _ => (0 : ℝ)) (uIoo 0 b) := by
    rw [uIoo_of_le hb.1]
    intro s hs
    simp [f, parisiCDF_dirac, not_le.mpr (hs.2.trans_le hb.2)]
  by_cases htq : t ≤ q
  · have hi : (∫ s in (0 : ℝ)..t, f s) = 0 := by
      rw [intervalIntegral.integral_congr_uIoo (hzero ⟨ht.1, htq⟩)]
      simp
    change X t = h + β * canonicalDiracNoise ω t + ∫ s in 0..t, f s
    rw [hi, add_zero]
    exact (canonicalDiracState_spec β h q hq ω).before t ⟨ht.1, htq⟩
  · have htq' : q ≤ t := (lt_of_not_ge htq).le
    have heq : EqOn f (fun s => β ^ 2 * Real.tanh (X s)) (uIoo q t) := by
      rw [uIoo_of_le htq']
      intro s hs
      dsimp only [f]
      rw [parisiCDF_dirac, ite_eq_left hs.1.le,
        parisiGradient_dirac_hard β q hβ hq s (X s) ⟨hs.1.le, hs.2.le.trans ht.2⟩,
        mul_one]
    have hcont : Continuous (fun s => β ^ 2 * Real.tanh (X s)) :=
      (gaussian_continuous_tanh.comp (continuous_canonicalDiracStateReal β h q hq ω)).const_mul _
    have hi0 : IntervalIntegrable f volume 0 q :=
      (intervalIntegrable_congr_uIoo (hzero ⟨hq.1, le_rfl⟩)).mpr intervalIntegrable_const
    have hi1 : IntervalIntegrable f volume q t :=
      (intervalIntegrable_congr_uIoo heq).mpr (hcont.intervalIntegrable q t)
    have hi : (∫ s in (0 : ℝ)..t, f s) = ∫ s in q..t, β ^ 2 * Real.tanh (X s) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
        intervalIntegral.integral_congr_uIoo (hzero ⟨hq.1, le_rfl⟩)]
      simp only [intervalIntegral.integral_zero, zero_add]
      exact intervalIntegral.integral_congr_uIoo heq
    change X t = h + β * canonicalDiracNoise ω t + ∫ s in 0..t, f s
    rw [hi]
    exact (canonicalDiracState_spec β h q hq ω).after t ⟨htq', ht.2⟩

/-- Proposition 3.1's state is exactly the canonical general Parisi state,
path by path, with the actual arbitrary-measure PDE selector. -/
theorem selectedParisiState_dirac_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t =
      canonicalDiracStateReal β h q hq ω t := by
  have he := parisiStateReal_unique β h (diracOverlap q hq)
    (fun s x => parisiGradient β (diracOverlap q hq) (s, x))
    (continuous_parisiGradient β (diracOverlap q hq))
    (fun s x => norm_parisiGradient_le_one β (diracOverlap q hq) (s, x))
    (lipschitzWith_parisiGradient β hβ.ne' (diracOverlap q hq))
    1 zero_le_one (canonicalDiracNoise ω) (continuous_canonicalDiracNoise ω)
    (canonicalDiracStateReal β h q hq ω) (continuous_canonicalDiracStateReal β h q hq ω)
    (fun s hs => canonicalDiracState_general_equation β h q hβ hq ω hs)
  exact (he ht).symm

theorem selectedParisiState_dirac_before (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) q) :
    selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t =
      h + β * canonicalBrownian t.toNNReal ω := by
  rw [selectedParisiState_dirac_eq β h q hβ hq ω ⟨ht.1, ht.2.trans hq.2⟩]
  exact canonicalDiracState_before β h q hq ω ht

theorem selectedParisiState_dirac_after (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (ω : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc q (1 : ℝ)) :
    selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t =
      h + β * canonicalBrownian t.toNNReal ω +
        ∫ s in q..t, β ^ 2 * Real.tanh
          (selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω s) := by
  rw [selectedParisiState_dirac_eq β h q hβ hq ω ⟨hq.1.trans ht.1, ht.2⟩,
    canonicalDiracState_after β h q hq ω ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 :=
    (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) 1)).uIcc_subset hq
      ⟨hq.1.trans ht.1, ht.2⟩ hs
  dsimp only
  rw [selectedParisiState_dirac_eq β h q hβ hq ω hs']

/-- The actual general Parisi state at the interface has the paper's exact
shifted Gaussian law, obtained from its driftless Brownian segment. -/
theorem hasLaw_selectedParisiState_dirac_interface (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) :
    HasLaw (fun ω => selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q)
      (gaussianReal h (β ^ 2 * q).toNNReal) canonicalBrownianMeasure := by
  have he : (fun ω => selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q) =
      fun ω => canonicalDiracStateReal β h q hq ω q :=
    funext (fun ω => selectedParisiState_dirac_eq β h q hβ hq ω hq)
  rw [he]
  exact hasLaw_canonicalDiracState_before β h q hq ⟨hq.1, le_rfl⟩

theorem selectedParisiSecondMoment_dirac_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t =
      physicalRSSecondMoment β h q hq t := by
  unfold selectedParisiSecondMoment physicalRSSecondMoment
  apply integral_congr_ae
  exact .of_forall (fun ω => by
    dsimp only
    rw [selectedParisiState_dirac_eq β h q hβ hq ω ht,
      parisiGradient_dirac_eq_explicit β q hβ hq t _ ht])

theorem selectedParisiG_dirac_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedParisiG β h hβ.ne' (diracOverlap q hq) t = rsParisiG β h q t := by
  rw [← physicalRSParisiG_eq β h q hq hβ.le ht]
  unfold selectedParisiG physicalRSParisiG parisiG
  apply intervalIntegral.integral_congr
  intro s hs
  have hsub : uIcc t (1 : ℝ) ⊆ Icc (0 : ℝ) 1 :=
    (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) 1)).uIcc_subset ht ⟨zero_le_one, le_rfl⟩
  dsimp only
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq (hsub hs)]

/-- Proposition 6.1 expressed with the actual general-measure PDE/state
observable, rather than a separately supplied RS formula. -/
theorem selectedParisiG_dirac_minimum {β h q : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      selectedParisiG β h hβ.ne' (diracOverlap q hq) q ≤
        selectedParisiG β h hβ.ne' (diracOverlap q hq) t := by
  intro t ht
  rw [selectedParisiG_dirac_eq β h q hβ hq hq, selectedParisiG_dirac_eq β h q hβ hq ht]
  exact rsParisiG_minimum hβ hh hq hfixed hAT t ht

theorem selectedParisiG_dirac_eq_minimum_iff {β h q t : ℝ}
    (hβ : 0 < β) (hh : 0 < h) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hAT : atParameter β h q ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedParisiG β h hβ.ne' (diracOverlap q hq) t =
      selectedParisiG β h hβ.ne' (diracOverlap q hq) q ↔ t = q := by
  rw [selectedParisiG_dirac_eq β h q hβ hq ht, selectedParisiG_dirac_eq β h q hβ hq hq]
  exact rsParisiG_eq_minimum_iff hβ hh hq hfixed hAT ht

end Paper
