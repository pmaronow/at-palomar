module

public import Targets.Section5SignedInitialInterpolation
public import Targets.Section5ConditionedInitialInterpolation
public import Targets.Section5SignedCascadeFlip

@[expose] public section

/-!
# Conditioning the signed initial interpolation on its frozen field

Both outer masses are zero, so their Gaussian expectations commute by Fubini.
The original positive frozen field is retained and later conditioned upon;
second-replica reflection also reflects its external field.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n k : ℕ}

private theorem negative_coordinates (z : Fin n → ℝ) :
    pairedFieldLinear (fun i : Fin n => -(Pi.single i 1)) z = -z := by
  classical
  ext i
  simp [pairedFieldLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

private theorem signed_zero_step (c : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 c (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1)) F x y =
      ∫ z, F (fun i => x i + Real.sqrt c * z i)
        (fun i => y i - Real.sqrt c * z i) ∂piGauss n := by
  simp only [coupledLinearStep, parisiStepPi, ↓reduceIte, Pi.zero_apply, zero_add,
    pairedFieldLinear_coordinates, negative_coordinates]
  rfl

private theorem integrable_signed_shared_shift
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (b c : ℝ) (x y : Fin n → ℝ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      F (fun i => x i + Real.sqrt c * z.1 i + Real.sqrt b * z.2 i)
        (fun i => y i - Real.sqrt c * z.1 i + Real.sqrt b * z.2 i))
      ((piGauss n).prod (piGauss n)) := by
  obtain ⟨C, D, hD, hb⟩ := hF.bound
  let B := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    C + D * (l1 x + l1 y) +
      (2 * D * Real.sqrt c) * l1 z.1 + (2 * D * Real.sqrt b) * l1 z.2
  have hi : Integrable B ((piGauss n).prod (piGauss n)) :=
    ((integrable_const _).add ((integrable_l1.comp_fst (piGauss n)).const_mul _)).add
      ((integrable_l1.comp_snd (piGauss n)).const_mul _)
  have hmeas : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun i => x i + Real.sqrt c * z.1 i + Real.sqrt b * z.2 i,
       fun i => y i - Real.sqrt c * z.1 i + Real.sqrt b * z.2 i)) := by fun_prop
  refine hi.mono ((hF.measurable.comp hmeas).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply (hb _ _).trans
  apply le_trans _ (le_abs_self (B z))
  have hx := l1_shift_le c x z.1
  have hy := l1_shift_le c y (-z.1)
  simp only [Pi.neg_apply, mul_neg, ← sub_eq_add_neg, l1_neg] at hy
  have hx' := l1_shift_le b (fun i => x i + Real.sqrt c * z.1 i) z.2
  have hy' := l1_shift_le b (fun i => y i - Real.sqrt c * z.1 i) z.2
  dsimp [B]
  nlinarith

/-- The actual anti-shared and positively shared mass-zero means commute.
This remains valid when either variance is zero. -/
theorem coupledLinearStep_zero_signed_shared_commute
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (b c : ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 c (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1)) (sharedStepPi n 0 b F) x y =
      ∫ z, coupledLinearStep 0 c (fun i : Fin n => Pi.single i 1)
        (fun i : Fin n => -(Pi.single i 1)) F
        (fun i => x i + Real.sqrt b * z i)
        (fun i => y i + Real.sqrt b * z i) ∂piGauss n := by
  simp only [signed_zero_step, sharedStepPi, parisiStepPi, zero_div, ↓reduceIte,
    Pi.zero_apply, zero_add]
  rw [integral_integral_swap (integrable_signed_shared_shift hF b c x y)]
  congr 1
  funext z
  congr 1
  funext z'
  congr 1 <;> ext i <;> dsimp <;> ring

/-- Joint disorder/field continuity of the actual fixed-variance cascade,
including fixed zero-variance coordinates. -/
theorem continuous_constrainedPairFieldCascade_joint
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    Continuous (fun q : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      coupledFieldCascade n m v d (constrainedPairFieldBase n q.1 u) j q.2.1 q.2.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨U, x, y⟩
  exact (differentiableAt_constrainedFieldCascade_multi
    (fun U : EnergySpace n => U) u m (fun l _ => v l) hm d j
    differentiableAt_id (fun _ _ => differentiableAt_const _)
    (Eventually.of_forall fun _ => hv)
    (fun l _ => (hv l).eq_or_lt.elim
      (fun he => Or.inr (Eventually.of_forall fun _ => he.symm)) Or.inl) x y).continuousAt

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Gaussian disorder and an independent frozen field may be integrated in
either order. The domination comes from the actual cascade's depth-preserving
disorder stability and affine field growth. -/
theorem integrable_constrainedPairFieldCascade_frozen_pair
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) (a b : ℝ)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ)
    (x : Fin n → ℝ) :
    Integrable (fun p : Ω × (Fin n → ℝ) => coupledFieldCascade n m v d
      (constrainedPairFieldBase n (a • Z p.1) u) j
      (fun i => x i + Real.sqrt b * p.2 i)
      (fun i => -(x i + Real.sqrt b * p.2 i)))
      ((ℙ : Measure Ω).prod (piGauss n)) := by
  obtain ⟨C, D, hD, hb⟩ := (constrainedPairFieldCascade_growth (0 : EnergySpace n)
    u m v hm hv d j).bound
  let B := fun p : Ω × (Fin n → ℝ) =>
    C + 2 * D * l1 x + (2 * D * Real.sqrt b) * l1 p.2 +
      (2 * Fintype.card (Config n) * |a|) * ‖Z p.1‖
  have hi : Integrable B ((ℙ : Measure Ω).prod (piGauss n)) :=
    ((integrable_const _).add ((integrable_l1.comp_snd (ℙ : Measure Ω)).const_mul _)).add
      (((integrable_norm_of_gaussian hZ).comp_fst (piGauss n)).const_mul _)
  have hfields : Measurable (fun p : Ω × (Fin n → ℝ) =>
      (fun i => x i + Real.sqrt b * p.2 i,
       fun i => -(x i + Real.sqrt b * p.2 i))) := by fun_prop
  have hmeas := (continuous_constrainedPairFieldCascade_joint u m v hm hv d j).measurable.comp
    (((hZ.repr_measurable.comp measurable_fst).const_smul a).prodMk hfields)
  refine hi.mono hmeas.aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply le_trans _ (le_abs_self (B p))
  let z := fun i => x i + Real.sqrt b * p.2 i
  have hd := constrainedPairFieldCascade_disorder_dist_le (a • Z p.1) 0
    u m v hm hv d j z (-z)
  have hnorm := uAbs_le_card_mul_norm n (a • Z p.1)
  simp only [sub_zero, norm_smul, Real.norm_eq_abs] at hd hnorm
  have hf := hb z (-z)
  rw [l1_neg] at hf
  have hl := l1_shift_le b x p.2
  have hh := abs_add_le
    (coupledFieldCascade n m v d (constrainedPairFieldBase n (a • Z p.1) u) j z (-z) -
      coupledFieldCascade n m v d (constrainedPairFieldBase n 0 u) j z (-z))
    (coupledFieldCascade n m v d (constrainedPairFieldBase n 0 u) j z (-z))
  rw [sub_add_cancel] at hh
  dsimp [B]
  change |coupledFieldCascade n m v d (constrainedPairFieldBase n (a • Z p.1) u) j
    z (-z)| ≤ _
  change l1 z ≤ _ at hl
  nlinarith [mul_le_mul_of_nonneg_left hl hD]

/-- Exact conditioning identity for the original signed/frozen path. The
second physical field is reflected together with the second replica. -/
theorem section5SignedInitialInterpolation_eq_conditioned_average
    (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    (hw : w ∈ Set.Icc 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    section5SignedInitialInterpolation n s β h sk.U t u w =
      ∫ z, section5ConditionedInitialInterpolation n s β sk.U t (-u)
        (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
        (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) w ∂piGauss n := by
  letI := constrainedPair_nonempty_neg (n := n) u
  have hun : -u ∈ Set.Icc 0 (s.q 1) := by constructor <;> linarith [hu.1, hu.2]
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5InterpolationVariance s β t (-u) 1 (k + 2 - j) w
  let V' := fun j => section5ConditionedInitialVariance s β t (-u) (k + 2 - j) w
  let b := (1 - t) * (β ^ 2 * s.q 1)
  have hm (j) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hv (j) : 0 ≤ V j :=
    (section5SignedInitial_variances_nonneg s β ht hu hw).2.2 _ (by omega)
  have hv' (j) : 0 ≤ V' j :=
    section5ConditionedInitialVariance_nonneg s β (by omega) ht hun hw
  let G := fun (ω : Ω) (z : Fin n → ℝ) => coupledFieldCascade n M V' (k + 2)
    (constrainedPairFieldBase n (Real.sqrt (w * t) • sk.U ω) (-u)) (k + 3)
    (fun i => h + Real.sqrt b * z i) (fun i => -(h + Real.sqrt b * z i))
  have hi : Integrable (fun p : Ω × (Fin n → ℝ) => G p.1 p.2)
      ((ℙ : Measure Ω).prod (piGauss n)) :=
    integrable_constrainedPairFieldCascade_frozen_pair sk.hU (Real.sqrt (w * t)) b
      (-u) M V' hm hv' (k + 2) (k + 3) (fun _ => h)
  have he : section5SignedInitialInterpolation n s β h sk.U t u w =
      (1 / (n : ℝ)) * ∫ ω, ∫ z, G ω z ∂piGauss n ∂ℙ := by
    unfold section5SignedInitialInterpolation
    congr 1
    apply integral_congr_ae
    filter_upwards [skDisorder_even_ae β h sk] with ω hω
    have hscaled : ∀ σ, (Real.sqrt (w * t) • sk.U ω) (configFlip n σ) =
        (Real.sqrt (w * t) • sk.U ω) σ := by
      intro σ
      simpa only [PiLp.smul_apply, smul_eq_mul] using
        congrArg (fun z => Real.sqrt (w * t) * z) (hω σ)
    rw [section5SignedInitialOuter, coupledLinearStep_shared, mul_zero,
      coupledLinearStep_zero_signed_shared_commute
        (constrainedPairFieldCascade_growth (Real.sqrt (w * t) • sk.U ω) u M V hm hv
          (k + 2) (k + 2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z =>
      section5SignedInitial_anti_prefix_eq_conditioned s β t u w
        (Real.sqrt (w * t) • sk.U ω) hscaled
        (fun i => h + Real.sqrt b * z i) (fun i => h + Real.sqrt b * z i)
  rw [he, integral_integral_swap hi, ← integral_const_mul]
  rfl

/-- Integrability of the actual conditioned free energy in its frozen field.
This is a consequence of the genuine joint Gaussian bound above. -/
theorem integrable_section5ConditionedInitialInterpolation_frozen
    (s : RSBScheme k) (β h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {t u w : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 (s.q 1))
    (hw : w ∈ Set.Icc 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    Integrable (fun z => section5ConditionedInitialInterpolation n s β Z t u
      (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
      (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) w) (piGauss n) := by
  exact (integrable_constrainedPairFieldCascade_frozen_pair hZ (Real.sqrt (w * t))
    ((1 - t) * (β ^ 2 * s.q 1)) u
    (fun j => section5Mass s 1 0 (k + 2 - j))
    (fun j => section5ConditionedInitialVariance s β t u (k + 2 - j) w)
    (fun _ => section5Mass_nonneg s (by omega) le_rfl (by omega))
    (fun _ => section5ConditionedInitialVariance_nonneg s β (by omega) ht hu hw)
    (k + 2) (k + 3) (fun _ => h)).integral_prod_right.const_mul (1 / (n : ℝ))

/-- The signed interpolation reaches the original constrained free energy
with the original correction. It follows by conditioning and exact reflection,
not by assuming a signed pressure derivative or changing the external field. -/
theorem section5SignedInitialInterpolation_endpoint_bound
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      section5SignedInitialFieldEndpoint n s β h t u - t * (2 * parisiCorrection s β) := by
  letI := constrainedPair_nonempty_neg (n := n) u
  have hun : -u ∈ Set.Icc 0 (s.q 1) := by constructor <;> linarith [hu.1, hu.2]
  have hi0 := integrable_section5ConditionedInitialInterpolation_frozen s β h sk.hU ht hun
    (w := 0) ⟨le_rfl, zero_le_one⟩
  have hi1 := integrable_section5ConditionedInitialInterpolation_frozen s β h sk.hU ht hun
    (w := 1) ⟨zero_le_one, le_rfl⟩
  rw [← section5SignedInitialInterpolation_one n s β h sk.U u ht.2,
    ← section5SignedInitialInterpolation_zero n s β h sk.U t u,
    section5SignedInitialInterpolation_eq_conditioned_average s β h sk ht hu
      (w := 1) ⟨zero_le_one, le_rfl⟩,
    section5SignedInitialInterpolation_eq_conditioned_average s β h sk ht hu
      (w := 0) ⟨le_rfl, zero_le_one⟩]
  calc
    _ ≤ ∫ z, section5ConditionedInitialInterpolation n s β sk.U t (-u)
        (fun i => h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)
        (fun i => -(h + Real.sqrt ((1 - t) * (β ^ 2 * s.q 1)) * z i)) 0 -
          t * (2 * parisiCorrection s β) ∂piGauss n :=
      integral_mono hi1 (hi0.sub (integrable_const _)) fun z =>
        section5ConditionedInitialInterpolation_endpoint_bound hn s β h sk ht hun _ _
    _ = _ := by rw [integral_sub hi0 (integrable_const _)]; simp

end SpinGlass.Targets
