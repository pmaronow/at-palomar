module

public import Targets.CoupledCascadeVariance
public import Targets.CoupledCovariance

@[expose] public section

/-!
# Actual constrained replica weights inside the paired cascade

The terminal Gibbs probabilities are transported through the same normalized
Gaussian tilts as the genuine first derivatives. Their positivity, normalization,
and moment identities are proved at every depth, without imposing a replica
interpretation as a hypothesis on a derivative.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

set_option autoImplicit false

namespace SpinGlass.Targets

variable {n : ℕ}

theorem pairedTiltMean_const {A : (Fin n → ℝ) → ℝ}
    (hA : GuerraGrowth A) (m v c : ℝ) (x : Fin n → ℝ) :
    pairedTiltMean m v A (fun _ => c) x = c := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  rw [pairedTiltMean, integral_const_mul, tiltWeightPi_integral_one hD hb hA.measurable, mul_one]

theorem pairedTiltMean_nonneg {A G : (Fin n → ℝ) → ℝ}
    (hA : GuerraGrowth A) (hG : ∀ x, 0 ≤ G x) (m v : ℝ) (x : Fin n → ℝ) :
    0 ≤ pairedTiltMean m v A G x := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  exact integral_nonneg fun z => mul_nonneg (hG _)
    (tiltWeightPi_nonneg hD hb hA.measurable x z)

private theorem outerSecondGrowth {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (y : Fin n → ℝ) :
    GuerraGrowth (fun x => parisiStepPi n m v (A x) y) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨(measurable_secondStepPi hA.measurable m v).comp
    (measurable_id.prodMk measurable_const), C + D * l1 y + stepK n m v D, D, hD, ?_⟩
  intro x
  have H := parisiStepPi_abs_le (C := C + D * l1 x) hm hv hD
    (fun z => by nlinarith [hb x z]) (hA.section_right x).measurable y
  nlinarith

private theorem sharedDifferenceGrowth {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    GuerraGrowth (fun z => A (x - y + z) z) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨hA.measurable.comp (f := fun z => (x - y + z, z)) (by fun_prop),
    C + D * l1 (x - y), 2 * D, by positivity, ?_⟩
  intro z
  nlinarith [hb (x - y + z) z, l1_add_le (x - y) z]

theorem pairedIndependentMean_measurable_bound
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B m v : ℝ}
    (hA : CoupledGrowth A)
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (hb : ∀ x y, |G x y| ≤ B) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => pairedIndependentMean m v A G p.1 p.2) ∧
      ∀ x y, |pairedIndependentMean m v A G x y| ≤ B := by
  refine ⟨?_, fun x y => ?_⟩
  · have H := (measurable_pairedSecondMean
      (A := fun y x => parisiStepPi n m v (A x) y)
      (G := fun y x => pairedSecondMean m v A G x y)
      ((measurable_secondStepPi hA.measurable m v).comp measurable_swap)
      ((measurable_pairedSecondMean hA.measurable hG m v).comp measurable_swap) m v).comp measurable_swap
    exact H
  · exact pairedTiltMean_abs_le (outerSecondGrowth hA hm hv y)
      ((measurable_pairedSecondMean hA.measurable hG m v).comp
        (measurable_id.prodMk measurable_const))
      (fun z => pairedTiltMean_abs_le (hA.section_right z)
        (hG.comp (measurable_const.prodMk measurable_id)) (hb z) y) x

theorem pairedSharedMean_measurable_bound
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ℝ}
    (hA : CoupledGrowth A)
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (hb : ∀ x y, |G x y| ≤ B) (m v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => pairedSharedMean m v A G p.1 p.2) ∧
      ∀ x y, |pairedSharedMean m v A G x y| ≤ B := by
  refine ⟨?_, fun x y => ?_⟩
  · exact (measurable_pairedSecondMean
      (hA.measurable.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + p.2, p.2)) (by fun_prop))
      (hG.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 + p.2, p.2)) (by fun_prop)) m v).comp
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2)) (by fun_prop)
  · exact pairedTiltMean_abs_le (sharedDifferenceGrowth hA x y)
      (hG.comp (f := fun z => (x - y + z, z)) (by fun_prop))
      (fun z => hb (x - y + z) z) y

/-- Every bounded measurable terminal observable remains bounded and measurable
under the actual derivative transport; no observable regularity is assumed. -/
theorem coupledFieldCascadeD_measurable_bound
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ℝ}
    (hA : CoupledGrowth A)
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (hb : ∀ x y, |G x y| ≤ B)
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (d j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => coupledFieldCascadeD m v d A G j p.1 p.2) ∧
      ∀ x y, |coupledFieldCascadeD m v d A G j x y| ≤ B := by
  induction j with
  | zero => exact ⟨hG, hb⟩
  | succ j ih =>
    simp only [coupledFieldCascadeD]
    split_ifs
    · exact pairedIndependentMean_measurable_bound (hA.fieldCascade m v hm hv d j)
        ih.1 ih.2 (hm j) (hv j)
    · exact pairedSharedMean_measurable_bound (hA.fieldCascade m v hm hv d j)
        ih.1 ih.2 (m j) (v j)

theorem coupledFieldCascadeD_nonneg
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (hG : ∀ x y, 0 ≤ G x y)
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (d j : ℕ) (x y : Fin n → ℝ) :
    0 ≤ coupledFieldCascadeD m v d A G j x y := by
  induction j generalizing x y with
  | zero => exact hG x y
  | succ j ih =>
    have hAj := hA.fieldCascade m v hm hv d j
    simp only [coupledFieldCascadeD]
    split_ifs
    · exact pairedTiltMean_nonneg (outerSecondGrowth hAj (hm j) (hv j) y)
        (fun z => pairedTiltMean_nonneg (hAj.section_right z) (ih z) (m j) (v j) y) (m j) (v j) x
    · exact pairedTiltMean_nonneg (sharedDifferenceGrowth hAj x y)
        (fun z => ih (x - y + z) z) (m j) (v j) y

theorem coupledFieldCascadeD_const
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (c : ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD m v d A (fun _ _ => c) j x y = c := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he : coupledFieldCascadeD m v d A (fun _ _ => c) j = fun _ _ => c :=
      funext fun x => funext fun y => ih x y
    have hAj := hA.fieldCascade m v hm hv d j
    simp only [coupledFieldCascadeD, he]
    split_ifs
    · simp only [pairedIndependentMean, pairedSecondMean,
        pairedTiltMean_const (hAj.section_right _)]
      exact pairedTiltMean_const (outerSecondGrowth hAj (hm j) (hv j) y) _ _ _ _
    · exact pairedTiltMean_const (sharedDifferenceGrowth hAj x y) _ _ _ _

/-- Finite linearity for bounded terminal observables under the full actual
paired transport. -/
theorem coupledFieldCascadeD_sum {ι : Type*} [Fintype ι]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : ι → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ι → ℝ}
    (hA : CoupledGrowth A)
    (hG : ∀ i, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G i p.1 p.2))
    (hb : ∀ i x y, |G i x y| ≤ B i) (c : ι → ℝ)
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD m v d A (fun x y => ∑ i, c i * G i x y) j x y =
      ∑ i, c i * coupledFieldCascadeD m v d A (G i) j x y := by
  classical
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he : coupledFieldCascadeD m v d A (fun x y => ∑ i, c i * G i x y) j =
        fun x y => ∑ i, c i * coupledFieldCascadeD m v d A (G i) j x y :=
      funext fun x => funext fun y => ih x y
    have hp (i : ι) := coupledFieldCascadeD_measurable_bound hA (hG i) (hb i) m v hm hv d j
    simp only [coupledFieldCascadeD, he]
    split_ifs
    · exact pairedIndependentMean_sum (hA.fieldCascade m v hm hv d j)
        (fun i => (hp i).1) (fun i => (hp i).2) c (hm j) (hv j) x y
    · exact pairedSharedMean_sum (hA.fieldCascade m v hm hv d j)
        (fun i => (hp i).1) (fun i => (hp i).2) c (m j) (v j) x y

/-- Actual constrained Gibbs coordinates transported from the terminal through
all visited paired levels. -/
noncomputable def constrainedCascadeGibbs (m v : ℕ → ℝ) (d j : ℕ)
    (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) (p : AT.ConstrainedPair n u) : ℝ :=
  coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
    (fun x y => constrainedPairGibbs n U u x y p) j x y

theorem measurable_constrainedPairGibbs_fields (U : EnergySpace n) (u : ℝ)
    (p : AT.ConstrainedPair n u) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => constrainedPairGibbs n U u q.1 q.2 p) := by
  classical
  unfold constrainedPairGibbs AT.gtStateGibbs AT.gtStatePartition pairFieldPotential
  fun_prop

private theorem constrainedPairGibbs_abs_le_one (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (p : AT.ConstrainedPair n u) (x y : Fin n → ℝ) :
    |constrainedPairGibbs n U u x y p| ≤ 1 := by
  rw [abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
  exact AT.gtStateGibbs_le_one _ _ _

theorem constrainedCascadeGibbs_measurable_bound
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (p : AT.ConstrainedPair n u) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => constrainedCascadeGibbs m v d j U u q.1 q.2 p) ∧
      ∀ x y, |constrainedCascadeGibbs m v d j U u x y p| ≤ 1 :=
  coupledFieldCascadeD_measurable_bound (constrainedPairFieldCascade_growth U u m v hm hv d 0)
    (measurable_constrainedPairGibbs_fields U u p) (constrainedPairGibbs_abs_le_one U u p)
    m v hm hv d j

theorem constrainedCascadeGibbs_nonneg
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) (p : AT.ConstrainedPair n u) :
    0 ≤ constrainedCascadeGibbs m v d j U u x y p :=
  coupledFieldCascadeD_nonneg (constrainedPairFieldCascade_growth U u m v hm hv d 0)
    (fun x y => constrainedPairGibbs_nonneg n U u x y p) m v hm hv d j x y

/-- Transport of an actual terminal Gibbs mean is the same mean under the
transported constrained probabilities. -/
theorem constrainedCascadeGibbs_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (f : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p) j x y =
      ∑ p, constrainedCascadeGibbs m v d j U u x y p * f p := by
  simpa only [mul_comm, constrainedCascadeGibbs, coupledFieldCascade] using
    coupledFieldCascadeD_sum (constrainedPairFieldCascade_growth U u m v hm hv d 0)
      (measurable_constrainedPairGibbs_fields U u) (constrainedPairGibbs_abs_le_one U u)
      f m v hm hv d j x y

theorem sum_constrainedCascadeGibbs
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    ∑ p, constrainedCascadeGibbs m v d j U u x y p = 1 := by
  have H := constrainedCascadeGibbs_moment U u m v hm hv d j (fun _ => 1) x y
  simp only [mul_one, sum_constrainedPairGibbs] at H
  have HC := coupledFieldCascadeD_const (constrainedPairFieldCascade_growth U u m v hm hv d 0)
    m v hm hv d j 1 x y
  simp only [coupledFieldCascade] at HC
  exact H.symm.trans HC

/-- The genuine full-depth disorder derivative is a moment of the actual
normalized constrained replica probabilities. -/
theorem constrainedPairFieldCascadeDirection_eq_replica
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    constrainedPairFieldCascadeDirection m v d j U V u x y =
      ∑ p, constrainedCascadeGibbs m v d j U u x y p * (V p.1.1 + V p.1.2) :=
  constrainedCascadeGibbs_moment U u m v hm hv d j _ x y

/-- The actual separate-field first derivative is a spin moment under the same
replica probabilities, not a different auxiliary family. -/
theorem constrainedPairCascadeSpatialFirst_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (A B x y : Fin n → ℝ) :
    constrainedPairCascadeSpatialFirst m v d j U u A B x y =
      ∑ p, constrainedCascadeGibbs m v d j U u x y p * pairFieldPotential n u A B p := by
  rw [constrainedPairCascadeSpatialFirst_eq U u m v hm hv d j]
  exact constrainedCascadeGibbs_moment U u m v hm hv d j _ x y

/-- Finite contraction of two means; this is the product-replica term in a
tilted covariance. No probabilistic assumptions are needed for this algebra. -/
theorem sum_mean_product_contraction {I S : Type*} [Fintype I] [Fintype S]
    (c : I → ℝ) (P : S → ℝ) (V W : I → S → ℝ) :
    (∑ i, c i * (∑ p, P p * V i p) * (∑ q, P q * W i q)) =
      ∑ p, ∑ q, P p * P q * (∑ i, c i * V i p * W i q) := by
  classical
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

section SKContraction

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The squared actual disorder first derivatives contract to the four squared
cross-overlaps of the actual transported constrained replicas. -/
theorem constrainedCascadeDirection_SK_square
    (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      (constrainedPairFieldCascadeDirection m v d j U (sk.hU.w i) u x y) ^ 2) =
      n * ∑ p, ∑ q, constrainedCascadeGibbs m v d j U u x y p *
        constrainedCascadeGibbs m v d j U u x y q * pairSKCovariance β p.1 q.1 := by
  simp only [constrainedPairFieldCascadeDirection_eq_replica U _ u m v hm hv d j x y,
    pow_two, ← mul_assoc]
  rw [sum_mean_product_contraction]
  simp_rw [pairSKCovariance_spectral_sum β h sk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end SKContraction

/-- Finite field-direction contraction under the same actual constrained
probabilities as the disorder trace. -/
theorem constrainedCascadeSpatialFirst_square {I : Type*} [Fintype I]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (c : I → ℝ) (A B : I → Fin n → ℝ) (x y : Fin n → ℝ) :
    (∑ i, c i * (constrainedPairCascadeSpatialFirst m v d j U u (A i) (B i) x y) ^ 2) =
      ∑ p, ∑ q, constrainedCascadeGibbs m v d j U u x y p *
        constrainedCascadeGibbs m v d j U u x y q *
        (∑ i, c i * pairFieldPotential n u (A i) (B i) p * pairFieldPotential n u (A i) (B i) q) := by
  simp only [constrainedPairCascadeSpatialFirst_eq_replica U u m v hm hv d j _ _ x y,
    pow_two, ← mul_assoc]
  exact sum_mean_product_contraction _ _ _ _

/-- Independent first-field squares yield the two diagonal replica overlaps. -/
theorem constrainedCascadeSpatialFirst_independent_square
    (hn : 0 < n) (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : Fin n, (
      (constrainedPairCascadeSpatialFirst m v d j U u (Pi.single i 1) 0 x y) ^ 2 +
      (constrainedPairCascadeSpatialFirst m v d j U u 0 (Pi.single i 1) x y) ^ 2)) =
      n * ∑ p, ∑ q, constrainedCascadeGibbs m v d j U u x y p *
        constrainedCascadeGibbs m v d j U u x y q *
        (AT.pairOverlapMatrix p.1 q.1 0 0 + AT.pairOverlapMatrix p.1 q.1 1 1) := by
  have HL := constrainedCascadeSpatialFirst_square U u m v hm hv d j (fun _ : Fin n => 1)
    (fun i => Pi.single i 1) (fun _ => 0) x y
  have HR := constrainedCascadeSpatialFirst_square U u m v hm hv d j (fun _ : Fin n => 1)
    (fun _ => 0) (fun i => Pi.single i 1) x y
  simp only [one_mul, pairFieldPotential_left_single, pairFieldPotential_right_single] at HL HR
  rw [Finset.sum_add_distrib, HL, HR, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← mul_add, ← Finset.sum_add_distrib, independent_pair_spin_contraction hn]
  ring

/-- Shared or anti-shared first-field squares yield all four linear overlaps,
including the signed cross terms. -/
theorem constrainedCascadeSpatialFirst_shared_square
    (hn : 0 < n) (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (d j : ℕ) {e : ℝ} (he : e ^ 2 = 1) (x y : Fin n → ℝ) :
    (∑ i : Fin n,
      (constrainedPairCascadeSpatialFirst m v d j U u (Pi.single i 1) (e • Pi.single i 1) x y) ^ 2) =
      n * ∑ p, ∑ q, constrainedCascadeGibbs m v d j U u x y p *
        constrainedCascadeGibbs m v d j U u x y q *
        (AT.pairOverlapMatrix p.1 q.1 0 0 + AT.pairOverlapMatrix p.1 q.1 1 1 +
          e * (AT.pairOverlapMatrix p.1 q.1 0 1 + AT.pairOverlapMatrix p.1 q.1 1 0)) := by
  have H := constrainedCascadeSpatialFirst_square U u m v hm hv d j (fun _ : Fin n => 1)
    (fun i => Pi.single i 1) (fun i => e • Pi.single i 1) x y
  simp only [one_mul, pairFieldPotential_shared_single] at H
  rw [H]
  simp only [shared_pair_spin_contraction hn he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Restarting at an original level preserves the exact subsequent potentials
and the independent/shared split. This is an identity of the actual recursion. -/
theorem coupledFieldCascade_add_levels
    (m v : ℕ → ℝ) (d l r : ℕ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledFieldCascade n (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d A l) r = coupledFieldCascade n m v d A (l + r) := by
  induction r with
  | zero => simp only [coupledFieldCascade, Nat.add_zero]
  | succ r ih =>
    have he : (r < d - l) ↔ (l + r < d) := by omega
    simp only [coupledFieldCascade, ih, he]
    rfl

/-- Two conditionally independent constrained replicas split after `l` inner
levels, and their product weights are transported through `r` remaining outer
levels of the actual same cascade. -/
noncomputable def constrainedCascadeReplica (m v : ℕ → ℝ) (d l r : ℕ)
    (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) : ℝ :=
  coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
    (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
    (fun x y => constrainedCascadeGibbs m v d l U u x y p *
      constrainedCascadeGibbs m v d l U u x y q) r x y

private theorem replica_product_props
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l : ℕ) (p : AT.ConstrainedPair n u × AT.ConstrainedPair n u) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      constrainedCascadeGibbs m v d l U u z.1 z.2 p.1 *
      constrainedCascadeGibbs m v d l U u z.1 z.2 p.2) ∧
      ∀ x y, |constrainedCascadeGibbs m v d l U u x y p.1 *
        constrainedCascadeGibbs m v d l U u x y p.2| ≤ 1 := by
  have h1 := constrainedCascadeGibbs_measurable_bound U u m v hm hv d l p.1
  have h2 := constrainedCascadeGibbs_measurable_bound U u m v hm hv d l p.2
  refine ⟨h1.1.mul h2.1, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_one₀ (h1.2 x y) (abs_nonneg _) (h2.2 x y)

theorem constrainedCascadeReplica_measurable_bound
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (p q : AT.ConstrainedPair n u) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => constrainedCascadeReplica m v d l r U u z.1 z.2 p q) ∧
      ∀ x y, |constrainedCascadeReplica m v d l r U u x y p q| ≤ 1 :=
  coupledFieldCascadeD_measurable_bound (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (replica_product_props U u m v hm hv d l (p, q)).1
    (replica_product_props U u m v hm hv d l (p, q)).2
    _ _ (fun i => hm (l + i)) (fun i => hv (l + i)) (d - l) r

theorem constrainedCascadeReplica_nonneg
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    0 ≤ constrainedCascadeReplica m v d l r U u x y p q :=
  coupledFieldCascadeD_nonneg (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (fun x y => mul_nonneg (constrainedCascadeGibbs_nonneg U u m v hm hv d l x y p)
      (constrainedCascadeGibbs_nonneg U u m v hm hv d l x y q))
    _ _ (fun i => hm (l + i)) (fun i => hv (l + i)) (d - l) r x y

/-- The split-level replica family exactly represents transport of the product
of the actual inner Gibbs means. -/
theorem constrainedCascadeReplica_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (f : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
      (fun x y => ∑ p, ∑ q, constrainedCascadeGibbs m v d l U u x y p *
        constrainedCascadeGibbs m v d l U u x y q * f p q) r x y =
      ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q * f p q := by
  have H := coupledFieldCascadeD_sum (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (fun p => (replica_product_props U u m v hm hv d l p).1)
    (fun p => (replica_product_props U u m v hm hv d l p).2)
    (fun p => f p.1 p.2) (fun i => m (l + i)) (fun i => v (l + i))
    (fun i => hm (l + i)) (fun i => hv (l + i)) (d - l) r x y
  simpa only [Fintype.sum_prod_type, mul_comm, constrainedCascadeReplica] using H

theorem sum_constrainedCascadeReplica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q = 1 := by
  have H := constrainedCascadeReplica_moment U u m v hm hv d l r (fun _ _ => 1) x y
  simp only [mul_one, ← Finset.mul_sum, sum_constrainedCascadeGibbs U u m v hm hv,
    mul_one] at H
  have HC := coupledFieldCascadeD_const (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (fun i => m (l + i)) (fun i => v (l + i)) (fun i => hm (l + i)) (fun i => hv (l + i))
    (d - l) r 1 x y
  exact H.symm.trans HC

/-- A product is taken before outer transport. This is the distinction between
the split-level replica weights and a product of fully averaged probabilities. -/
theorem constrainedCascadeReplica_product_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
      (fun x y => (∑ p, constrainedCascadeGibbs m v d l U u x y p * f p) *
        (∑ q, constrainedCascadeGibbs m v d l U u x y q * g q)) r x y =
      ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q * f p * g q := by
  have he (x y : Fin n → ℝ) :
      (∑ p, constrainedCascadeGibbs m v d l U u x y p * f p) *
        (∑ q, constrainedCascadeGibbs m v d l U u x y q * g q) =
      ∑ p, ∑ q, constrainedCascadeGibbs m v d l U u x y p *
        constrainedCascadeGibbs m v d l U u x y q * (f p * g q) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  simpa only [mul_assoc] using constrainedCascadeReplica_moment U u m v hm hv d l r
    (fun p q => f p * g q) x y

/-- Products of the genuine inner disorder first derivatives, transported
through all remaining outer levels, have the actual split-level replica law. -/
theorem constrainedCascadeReplica_disorder_product
    (U V W : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
      (fun x y => constrainedPairFieldCascadeDirection m v d l U V u x y *
        constrainedPairFieldCascadeDirection m v d l U W u x y) r x y =
      ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q *
        (V p.1.1 + V p.1.2) * (W q.1.1 + W q.1.2) := by
  simp only [constrainedPairFieldCascadeDirection_eq_replica U _ u m v hm hv d l]
  exact constrainedCascadeReplica_product_moment U u m v hm hv d l r _ _ x y

/-- The same split-level replica law represents products of genuine spatial
first derivatives in arbitrary separate-replica directions. -/
theorem constrainedCascadeReplica_spatial_product
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (A B C D x y : Fin n → ℝ) :
    coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
      (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
      (fun x y => constrainedPairCascadeSpatialFirst m v d l U u A B x y *
        constrainedPairCascadeSpatialFirst m v d l U u C D x y) r x y =
      ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q *
        pairFieldPotential n u A B p * pairFieldPotential n u C D q := by
  simp only [constrainedPairCascadeSpatialFirst_eq_replica U u m v hm hv d l]
  exact constrainedCascadeReplica_product_moment U u m v hm hv d l r _ _ x y

end SpinGlass.Targets
