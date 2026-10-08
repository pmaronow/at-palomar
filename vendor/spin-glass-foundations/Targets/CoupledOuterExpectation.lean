module

/-
# The outer zero-mass average and the pressure gap

This connects standard-coordinate expectations to the constrained pressure and
to the replica measures of Lemma 2.7. The last step is shared and has mass zero;
the hypothesis `d ≤ k + 1` expresses precisely that restriction.
-/
public import Targets.CoupledGaussianLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}

noncomputable def coupledOuterField (s : RSBScheme k) (β : ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (β ^ 2 * s.q 1) * z i

theorem measurable_coupledGap (s : RSBScheme k) (β h t u : ℝ) (d j : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) => coupledGap n s β p.1 h t u d j p.2) := by
  have hC := measurable_coupledCascade_joint s β d j (A := fun U => constrainedBase n U h t u)
    (measurable_constrainedBase_joint h t u)
  have hA := measurable_coupledCascade_joint s β d j (A := fun U => coupledBase n U h t)
    (measurable_coupledBase_joint h t)
  exact (hC.sub hA).comp (f := fun p : EnergySpace n × (Fin n → ℝ) => (p.1, (p.2, p.2)))
    (by fun_prop)

/-- The final pressure step is exactly the shared outer-field expectation. -/
theorem coupledCascade_top_eq_integral (s : RSBScheme k) (β : ℝ) (d : ℕ) (hd : d ≤ k + 1)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledCascade n s β d A (k + 2) 0 0 =
      ∫ z, coupledCascade n s β d A (k + 1) (coupledOuterField s β z) (coupledOuterField s β z)
        ∂piGauss n := by
  rw [show k + 2 = (k + 1) + 1 by omega, coupledCascade, if_neg (by omega)]
  simp only [Nat.sub_self, show k + 2 - (k + 1) = 1 by omega, s.m_zero, s.q_zero,
    sub_zero, one_mul, sharedStepPi, zero_div, parisiStepPi, ite_true, Pi.zero_apply, zero_add]
  rfl

theorem coupledObservable_top_eq_integral (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h t : ℝ) (d : ℕ) (hd : d ≤ k + 1) (K : Config n → Config n → ℝ) :
    coupledObservable n s β U h t d K (k + 2) 0 0 =
      ∫ z, coupledObservable n s β U h t d K (k + 1)
        (coupledOuterField s β z) (coupledOuterField s β z) ∂piGauss n := by
  rw [show k + 2 = (k + 1) + 1 by omega, coupledObservable, if_neg (by omega)]
  simp only [Nat.sub_self, show k + 2 - (k + 1) = 1 by omega, s.m_zero, s.q_zero,
    sub_zero, one_mul, sharedTiltAvg, sharedTiltWeightPi, zero_div, tiltWeightPi, ite_true,
    mul_one, Pi.zero_apply, zero_add]
  rfl

theorem CoupledGrowth.integrable_outer {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (s : RSBScheme k) (β : ℝ) :
    Integrable (fun z => A (coupledOuterField s β z) (coupledOuterField s β z)) (piGauss n) := by
  have H := hA.shared_shift 0 0
  obtain ⟨C, D, hD, hb⟩ := H.bound
  have hi := integrable_shift_pi (v := β ^ 2 * s.q 1) hD hb H.measurable 0
  change Integrable (fun z => A (fun i => Real.sqrt (β ^ 2 * s.q 1) * z i)
    (fun i => Real.sqrt (β ^ 2 * s.q 1) * z i)) (piGauss n)
  simpa only [Pi.zero_apply, zero_add] using hi

theorem coupledGap_top_eq_integral (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    coupledGap n s β U h t u d (k + 2) 0 =
      ∫ z, coupledGap n s β U h t u d (k + 1) (coupledOuterField s β z) ∂piGauss n := by
  unfold coupledGap
  rw [coupledCascade_top_eq_integral s β d hd, coupledCascade_top_eq_integral s β d hd]
  exact (integral_sub
    (((constrainedBase_growth U h u ht hu).cascade s β d (k + 1)).integrable_outer s β)
    (((coupledBase_growth n U h ht).cascade s β d (k + 1)).integrable_outer s β)).symm

theorem integrable_coupledGap_outer (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    Integrable (fun p : Ω × (Fin n → ℝ) =>
      coupledGap n s β (sk.U p.1) h t u d j (coupledOuterField s β p.2))
      ((ℙ : Measure Ω).prod (piGauss n)) := by
  have hF := (measurable_coupledGap s β h t u d j).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) => (p.1, coupledOuterField s β p.2))
    (by unfold coupledOuterField; fun_prop)
  exact (integrable_coupledGaussian_pair_iff sk hF).mp
    (integrable_gaussianCoupledGap sk s hn ht u hu d j)

theorem integral_gaussianCoupledGap_eq (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, gaussianCoupledGap sk s t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ ω, coupledGap n s β (sk.U ω) h t u d (k + 2) 0 ∂ℙ := by
  have hF := (measurable_coupledGap s β h t u d (k + 1)).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) => (p.1, coupledOuterField s β p.2))
    (by unfold coupledOuterField; fun_prop)
  have he := integral_coupledGaussian_pair sk hF
  change (∫ z, gaussianCoupledGap sk s t u d (k + 1) z
    ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) = _ at he
  rw [he]
  dsimp only [Function.comp_def]
  rw [integral_prod _ (integrable_coupledGap_outer sk s hn ht u hu d (k + 1))]
  apply integral_congr_ae
  filter_upwards with ω
  exact (coupledGap_top_eq_integral s β (sk.U ω) h u ht hu d hd).symm

theorem integrable_coupledGap_top (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    Integrable (fun ω => coupledGap n s β (sk.U ω) h t u d (k + 2) 0) ℙ := by
  have H := (integrable_coupledGap_outer sk s hn ht u hu d (k + 1)).integral_prod_left
  simpa only [← coupledGap_top_eq_integral s β _ h u ht hu d hd] using H

/-- The unrestricted top pressure is integrable in the abstract Gaussian disorder. -/
theorem integrable_coupledCascade_top (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) :
    Integrable (fun ω => coupledCascade n s β d (coupledBase n (sk.U ω) h t) (k + 2) 0 0) ℙ := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc n s β h (k + 2)
  have hi : Integrable (fun ω => cascadeT n s β 1 (guerraBase n (sk.U ω) h t) (k + 2) 0) ℙ := by
    refine ((integrable_const a).add
      ((PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian sk.hU).const_mul
        (Fintype.card (Config n)))).mono'
      ((measurable_cascade_top_U s β h t).comp sk.hU.repr_measurable).aestronglyMeasurable ?_
    filter_upwards with ω
    have hb := (hprops (sk.U ω)).2.1 t ht 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hb
    rw [Real.norm_eq_abs]
    exact hb.trans (add_le_add_right (uAbs_le_card_mul_norm n (sk.U ω)) a)
  simpa only [coupledCascade_diag n s β _ h ht] using hi.const_mul 2

theorem integrable_constrainedCascade_top (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    Integrable (fun ω => coupledCascade n s β d (constrainedBase n (sk.U ω) h t u) (k + 2) 0 0) ℙ := by
  have H := (integrable_coupledGap_top sk s hn ht u hu d hd).add
    (integrable_coupledCascade_top sk s ht d)
  simpa only [Pi.add_def, coupledGap, sub_add_cancel] using H

/-- The mean hypothesis in Lemma 2.6 is exactly the pressure gap in Proposition 2.5. -/
theorem gaussianCoupledGap_mean_eq (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, gaussianCoupledGap sk s t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      n * (constrainedPhi n s β h sk.U d t u - 2 * guerraPhi n s β h sk.U t) := by
  rw [integral_gaussianCoupledGap_eq sk s hn ht u hu d hd]
  simp only [coupledGap]
  rw [integral_sub (integrable_constrainedCascade_top sk s hn ht u hu d hd)
    (integrable_coupledCascade_top sk s ht d), ← coupledPhi_eq_two_guerraPhi n s β h sk.U d ht]
  unfold constrainedPhi coupledPhi
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

theorem integral_gaussianCoupledEvent_eq (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, gaussianCoupledEvent sk s t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ ω, coupledObservable n s β (sk.U ω) h t d (overlapEvent n u) (k + 2) 0 0 ∂ℙ := by
  have hF := (measurable_coupledObservable_joint s β h t d (overlapEvent n u) (k + 1)).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) =>
      (p.1, (coupledOuterField s β p.2, coupledOuterField s β p.2)))
    (by unfold coupledOuterField; fun_prop)
  have hi := (integrable_coupledGaussian_pair_iff sk hF).mp
    (integrable_gaussianCoupledEvent sk s hs ht u hu d)
  have he := integral_coupledGaussian_pair sk hF
  change (∫ z, gaussianCoupledEvent sk s t u d z
    ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) = _ at he
  rw [he, integral_prod _ hi]
  dsimp only [Function.comp_def]
  simp_rw [← coupledObservable_top_eq_integral s β _ h t d hd (overlapEvent n u)]

theorem gaussianCoupledEvent_mean_eq (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, gaussianCoupledEvent sk s t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      guerraReplicaMeasure n s β h sk.U t d (overlapEvent n u) :=
  (integral_gaussianCoupledEvent_eq sk s hs ⟨ht.1.le, ht.2.le⟩ u hu d hd).trans
    (coupledObservable_eq_replicaMeasure n s β h sk.U ht d (by omega) (overlapEvent n u))

end SpinGlass.Targets
