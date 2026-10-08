module

public import Targets.Section4VarianceFactor
public import Targets.CoupledPathContinuity
public import Targets.ParisiJointMassContinuity

@[expose] public section

/-!
# Continuity of the actual normalized Section 4 factor

Bounded observables pass continuously through normalized Gaussian tilts,
including zero mass. The potential's compact-path growth is the already
checked `CoupledContinuousOn` bound.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] {n : ℕ}

/-- Fixed Gaussian log-Laplace normalization preserves bounded-observable
continuity. The common exponential envelope is supplied by linear growth. -/
theorem continuousOn_normalized_gaussianMean
    {S : Set P} {F G : P → (Fin n → ℝ) → ℝ} {C D : ℝ} (_hD : 0 ≤ D)
    (hFm : ∀ p ∈ S, Measurable (F p))
    (hFb : ∀ p ∈ S, ∀ z, |F p z| ≤ C + D * l1 z)
    (hFc : ∀ z, ContinuousOn (fun p => F p z) S)
    (hGm : ∀ p ∈ S, Measurable (G p))
    (hGb : ∀ p ∈ S, ∀ z, |G p z| ≤ 1)
    (hGc : ∀ z, ContinuousOn (fun p => G p z) S) (m : ℝ) :
    ContinuousOn (fun p =>
      (∫ z, G p z * Real.exp (m * F p z) ∂piGauss n) /
        ∫ z, Real.exp (m * F p z) ∂piGauss n) S := by
  let b := fun z : Fin n → ℝ => Real.exp (|m| * C) * Real.exp ((|m| * D) * l1 z)
  have hb (p : P) (hp : p ∈ S) (z : Fin n → ℝ) : Real.exp (m * F p z) ≤ b z := by
    dsimp [b]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have H := mul_le_mul_of_nonneg_left (hFb p hp z) (abs_nonneg m)
    have H' : m * F p z ≤ |m| * |F p z| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have hbi : Integrable b (piGauss n) := (integrable_exp_l1 _).const_mul _
  have hden : ContinuousOn (fun p => ∫ z, Real.exp (m * F p z) ∂piGauss n) S := by
    apply continuousOn_of_dominated (bound := b)
    · intro p hp; exact ((hFm p hp).const_mul m).exp.aestronglyMeasurable
    · intro p hp
      exact Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb p hp z
    · exact hbi
    · exact Eventually.of_forall fun z => Real.continuous_exp.comp_continuousOn ((hFc z).const_mul m)
  have hnum : ContinuousOn (fun p => ∫ z, G p z * Real.exp (m * F p z) ∂piGauss n) S := by
    apply continuousOn_of_dominated (bound := b)
    · intro p hp; exact ((hGm p hp).mul ((hFm p hp).const_mul m).exp).aestronglyMeasurable
    · intro p hp
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_left (Real.exp_pos _).le (hGb p hp z)).trans (hb p hp z)
    · exact hbi
    · exact Eventually.of_forall fun z => (hGc z).mul
        (Real.continuous_exp.comp_continuousOn ((hFc z).const_mul m))
  apply hnum.div hden
  intro p hp
  have hi : Integrable (fun z => Real.exp (m * F p z)) (piGauss n) :=
    hbi.mono' (((hFm p hp).const_mul m).exp.aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb p hp z)
  exact (integral_exp_pos hi).ne'

/-- A bounded continuous observable passes through an actual moving-variance
tilt. Both fields and the potential may depend on the compact parameter. -/
theorem continuousOn_pairedSecondMean_paths
    {F G : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) (hS : IsCompact S)
    (hGm : ∀ p ∈ S, Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => G p q.1 q.2))
    (hGb : ∀ p ∈ S, ∀ x y, |G p x y| ≤ 1)
    (hGc : ∀ x y : P → Fin n → ℝ, ContinuousOn x S → ContinuousOn y S →
      ContinuousOn (fun p => G p (x p) (y p)) S)
    (m : ℝ) (v : P → ℝ) (hvc : ContinuousOn v S)
    (x y : P → Fin n → ℝ) (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun p => pairedSecondMean m (v p) (F p) (G p) (x p) (y p)) S := by
  obtain ⟨C, D, hD, hFb⟩ := hF.growth
  obtain ⟨V, hV⟩ := hS.bddAbove_image hvc
  have hxy : ContinuousOn (fun p => l1 (x p) + l1 (y p)) S := by unfold l1; fun_prop
  obtain ⟨X, hX⟩ := hS.bddAbove_image hxy
  let Fs := fun (p : P) (z : Fin n → ℝ) => F p (x p) (fun i => y p i + Real.sqrt (v p) * z i)
  let Gs := fun (p : P) (z : Fin n → ℝ) => G p (x p) (fun i => y p i + Real.sqrt (v p) * z i)
  have hFsm (p : P) (hp : p ∈ S) : Measurable (Fs p) :=
    (hF.measurable p hp).comp (measurable_const.prodMk (measurable_shift (v p) (y p)))
  have hGsm (p : P) (hp : p ∈ S) : Measurable (Gs p) :=
    (hGm p hp).comp (measurable_const.prodMk (measurable_shift (v p) (y p)))
  have hFsb (p : P) (hp : p ∈ S) (z : Fin n → ℝ) :
      |Fs p z| ≤ (C + D * X) + (D * Real.sqrt V) * l1 z := by
    have H := hFb p hp (x p) (fun i => y p i + Real.sqrt (v p) * z i)
    have HS := l1_shift_le (v p) (y p) z
    have HX := hX (Set.mem_image_of_mem _ hp)
    have HV := Real.sqrt_le_sqrt (hV (Set.mem_image_of_mem _ hp))
    change |Fs p z| ≤ _ at H
    nlinarith [mul_le_mul_of_nonneg_left HS hD,
      mul_le_mul_of_nonneg_left HX hD,
      mul_le_mul_of_nonneg_left HV (mul_nonneg hD (l1_nonneg z))]
  have hFsc (z : Fin n → ℝ) : ContinuousOn (fun p => Fs p z) S := by
    apply hF.continuous x _ hx
    fun_prop
  have hGsc (z : Fin n → ℝ) : ContinuousOn (fun p => Gs p z) S := by
    apply hGc x _ hx
    fun_prop
  have H := continuousOn_normalized_gaussianMean (mul_nonneg hD (Real.sqrt_nonneg _))
    hFsm hFsb hFsc hGsm (fun p hp z => hGb p hp _ _) hGsc m
  simp only [pairedSecondMean, pairedTiltMean, tiltWeightPi] at ⊢
  by_cases hm : m = 0
  · simpa only [hm, if_true, zero_mul, Real.exp_zero, mul_one, integral_const,
      probReal_univ, smul_eq_mul, div_one, Fs, Gs] using H
  · simpa only [if_neg hm, ← mul_div_assoc, integral_div, Fs, Gs] using H

/-- Reuse the finite-direction continuity rule for a scalar step, with the
first field only a dummy coordinate. -/
theorem CoupledContinuousOn.scalarStep
    {A : P → ℝ → ℝ} {S : Set P}
    (hA : CoupledContinuousOn (fun p (_ y : Fin 1 → ℝ) => A p (y 0)) S)
    (hS : IsCompact S) (hAg : ∀ p ∈ S, HasLinearGrowth (A p))
    (hAm : ∀ p ∈ S, Measurable (A p)) {m : ℝ} (hm : 0 ≤ m)
    {v : P → ℝ} (hvc : ContinuousOn v S) (hv : ∀ p ∈ S, 0 ≤ v p) :
    CoupledContinuousOn (fun p (_ y : Fin 1 → ℝ) => parisiStep m (v p) (A p) (y 0)) S := by
  have he (p : P) (hp : p ∈ S) (x y : Fin 1 → ℝ) :
      coupledLinearStep m (v p) (fun (_ : Fin 1) => (0 : Fin 1 → ℝ))
        (fun i : Fin 1 => Pi.single i 1) (fun _ y => A p (y 0)) x y =
      parisiStep m (v p) (A p) (y 0) := by
    have H := parisiStepPi_sum (n := 1) m (v p) (hAg p hp) (hAm p hp) y
    simp only [Fin.sum_univ_one] at H
    rw [← H]
    simp only [coupledLinearStep, pairedFieldLinear_coordinates, parisiStepPi,
      Pi.add_apply, Pi.zero_apply, zero_add]
  have H := hA.linearStep hS (fun (_ : Fin 1) => (0 : Fin 1 → ℝ))
    (fun i : Fin 1 => Pi.single i 1) hm hvc hv
  obtain ⟨C, D, hD, hb⟩ := H.growth
  refine ⟨?_, ⟨C, D, hD, ?_⟩, ?_⟩
  · intro p hp
    simpa only [he p hp] using H.measurable p hp
  · intro p hp x y
    simpa only [he p hp] using hb p hp x y
  · intro x y hx hy
    exact (H.continuous x y hx hy).congr (fun p hp => (he p hp (x p) (y p)).symm)

omit [FirstCountableTopology P] in
private theorem coupledContinuousOn_of_scalar_paths {A : P → ℝ → ℝ} {S : Set P}
    (hS : IsCompact S) (hAm : ∀ p ∈ S, Measurable (A p))
    (hL : ∀ p ∈ S, ∀ x y, |A p x - A p y| ≤ |x - y|)
    (hc : ∀ x : P → ℝ, ContinuousOn x S → ContinuousOn (fun p => A p (x p)) S) :
    CoupledContinuousOn (fun p (_ y : Fin 1 → ℝ) => A p (y 0)) S := by
  obtain ⟨C, hC⟩ := hS.bddAbove_image (hc (fun _ => 0) continuousOn_const).abs
  refine ⟨fun p hp => (hAm p hp).comp ((measurable_pi_apply 0).comp measurable_snd),
    ⟨C, 1, zero_le_one, ?_⟩, ?_⟩
  · intro p hp x y
    have H := hL p hp (y 0) 0
    have HC := hC (Set.mem_image_of_mem _ hp)
    have HT := abs_sub_le (A p (y 0)) (A p 0) 0
    simp only [sub_zero, l1, Fin.sum_univ_one, one_mul] at H HT ⊢
    linarith [abs_nonneg (x 0)]
  · intro x y hx hy
    exact hc (fun p => y p 0) ((continuous_apply 0).comp_continuousOn hy)

private theorem section4_inner_continuous {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (a : ℝ) :
    CoupledContinuousOn
      (fun p : ℝ × ℝ => fun (_ y : Fin 1 → ℝ) =>
        parisiStep p.1 p.2 (parisiF s β (k + 2 - r)) (y 0))
      (Set.Icc 0 1 ×ˢ Set.Icc 0 a) := by
  apply coupledContinuousOn_of_scalar_paths (isCompact_Icc.prod isCompact_Icc)
  · intro p _; exact measurable_parisiStep (parisiF_measurable s β _) p.1 p.2
  · intro p _ x y
    simpa only [one_mul] using parisiStep_lipschitz (m := p.1) (v := p.2) (L := 1)
      (fun x y => by simpa only [one_mul] using parisiF_lipschitz s β (k + 2 - r) x y)
      (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _) x y
  · intro x hx
    exact (continuousOn_parisiStep_parisiF_joint s β (k + 2 - r)).comp
      (continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk hx))
      (fun p hp => ⟨hp.1, hp.2.1, Set.mem_univ _⟩)

/-- Joint mass/variance continuity propagates through the actual potential and
the actual bounded squared-slope observable, all the way to the root. -/
theorem section4VarianceQ_continuous_paths {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {j : ℕ} (hj : j ≤ r - 1) :
    let S := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))
    CoupledContinuousOn
      (fun p : ℝ × ℝ => fun (_ y : Fin 1 → ℝ) =>
        scalarFieldCascade (fun l => section4Mass s r p.1 (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) p.2) (k + 2 - r + 2 + j) (y 0)) S ∧
    (∀ x y : (ℝ × ℝ) → Fin 1 → ℝ, ContinuousOn x S → ContinuousOn y S →
      ContinuousOn (fun p => section4VarianceQ s β r p.1 j p.2 (x p) (y p)) S) := by
  dsimp only
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  let S := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 a
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  induction j with
  | zero =>
    have hB := section4_inner_continuous s β r a
    have hBg (p : ℝ × ℝ) (_ : p ∈ S) :=
      hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β (k + 2 - r))
        (parisiF_measurable s β _) p.1 p.2
    have hBm (p : ℝ × ℝ) (_ : p ∈ S) :=
      measurable_parisiStep (parisiF_measurable s β (k + 2 - r)) p.1 p.2
    constructor
    · simpa only [Nat.add_zero, section4Cascade_split s β hr0 hr, Pi.sub_apply, a] using!
        hB.scalarStep hS hBg hBm (s.m_nonneg (p := r - 1) (by omega))
          (continuous_const.sub continuous_snd).continuousOn (fun p hp => sub_nonneg.mpr hp.2.2)
    · intro x y hx hy
      simp only [section4VarianceQ]
      apply continuousOn_pairedSecondMean_paths hB hS
      · intro p _
        exact (((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1
          p.1 p.2).pow_const 2).comp ((measurable_pi_apply 0).comp measurable_snd))
      · intro p hp x y
        have H := hasParisiC2_parisiStep_nonneg (v := p.2) hp.1.1 hp.1.2
          (parisiF_C2_props s β (k + 2 - r)).1
          (parisiF_hasLinearGrowth s β _) (parisiF_measurable s β _)
          (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [H.abs_first_le_one (y 0), sq_abs
          (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) p.1 p.2 (y 0)),
          abs_nonneg (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) p.1 p.2 (y 0))]
      · intro xx yy hxx hyy
        exact ((continuousOn_stepD1_parisiF_joint s β (k + 2 - r)).comp
          (continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk
            ((continuous_apply 0).comp_continuousOn hyy)))
          (fun p hp => ⟨hp.1, hp.2.1, Set.mem_univ _⟩)).pow 2
      · exact (continuous_const.sub continuous_snd).continuousOn
      · exact hx
      · exact hy
  | succ j ih =>
    obtain ⟨hF, hQ⟩ := ih (by omega)
    let l := k + 2 - (k + 2 - r + 2 + j)
    have hl : l < r := by dsimp [l]; omega
    have hle : l ≤ k + 1 := by omega
    have hl1 : l + 1 ≠ r := by dsimp [l]; omega
    have hvar : 0 ≤ β ^ 2 * (s.q (l + 1) - s.q l) :=
      mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_mono l (by omega)))
    constructor
    · have H := hF.scalarStep hS
        (fun p _ => (scalarFieldCascade_props _ _ _).2.1)
        (fun p _ => (scalarFieldCascade_props _ _ _).1) (s.m_nonneg hle)
        (v := fun _ => β ^ 2 * (s.q (l + 1) - s.q l)) continuousOn_const (fun _ _ => hvar)
      have he :
          (fun p : ℝ × ℝ => fun (_ y : Fin 1 → ℝ) =>
            scalarFieldCascade (fun l => section4Mass s r p.1 (k + 2 - l))
              (fun l => section5Variance s β r (k + 2 - l) p.2) (k + 2 - r + 2 + (j + 1)) (y 0)) =
          (fun p : ℝ × ℝ => fun (_ y : Fin 1 → ℝ) =>
            parisiStep (s.m l) (β ^ 2 * (s.q (l + 1) - s.q l))
              (scalarFieldCascade (fun l => section4Mass s r p.1 (k + 2 - l))
                (fun l => section5Variance s β r (k + 2 - l) p.2) (k + 2 - r + 2 + j)) (y 0)) := by
        funext p x y
        rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
          scalarFieldCascade]
        change parisiStep (section4Mass s r p.1 l) (section5Variance s β r l p.2) _ _ = _
        simp only [section4Mass, if_pos hl, section5Variance,
          if_neg (Nat.ne_of_lt hl), if_neg (not_lt.mpr hl.le), if_neg hl1]
      rw [he]
      exact H
    · intro x y hx hy
      exact continuousOn_pairedSecondMean_paths hF hS
        (fun p _ => measurable_section4VarianceQ s β r p.1 j p.2)
        (fun p hp xx yy => by
          have H := section4VarianceQ_mem_Icc s β r hp.1 j p.2 xx yy
          simpa only [abs_of_nonneg H.1] using H.2) hQ (s.m l)
        (fun _ => β ^ 2 * (s.q (l + 1) - s.q l)) continuousOn_const x y hx hy

/-- The actual normalized factor is jointly continuous on the closed admissible
mass/variance rectangle. In particular, mass zero and all variance endpoints
are included; no mass gap is divided out. -/
theorem continuousOn_section4TVarianceQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    ContinuousOn (fun p : ℝ × ℝ => section4TVarianceQ s β h r p.1 p.2)
      (Set.Icc 0 1 ×ˢ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :=
  (section4VarianceQ_continuous_paths s β hr0 hr (j := r - 1) le_rfl).2
    (fun _ => 0) (fun _ _ => h) continuousOn_const continuousOn_const

/-- Mass continuity includes both endpoint masses and is not obtained by
dividing the variance derivative by its vanishing coefficient. -/
theorem continuousOn_section4TVarianceQ_mass {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ContinuousOn (fun m => section4TVarianceQ s β h r m v) (Set.Icc 0 1) :=
  (continuousOn_section4TVarianceQ s β h hr0 hr).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ hm => ⟨hm, hv⟩)

/-- Variance continuity of the actual normalized factor includes the complete
closed split interval, also at the baseline mass zero. -/
theorem continuousOn_section4TVarianceQ_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc 0 1) :
    ContinuousOn (section4TVarianceQ s β h r m)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :=
  (continuousOn_section4TVarianceQ s β h hr0 hr).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ hv => ⟨hm, hv⟩)

/-- Unlike the earlier strict-gap argument, actual continuity now proves the
normalized factor itself integrable even at equal masses. -/
theorem intervalIntegrable_section4TVarianceQ_closed {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc 0 1) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    IntervalIntegrable (section4TVarianceQ s β h r m) volume v w :=
  ((continuousOn_section4TVarianceQ_variance s β h hr0 hr hm).mono
    (Set.uIcc_subset_Icc hv hw)).intervalIntegrable

end SpinGlass.Targets
