module

public import Targets.Section5SignedInitialInterpolation
public import Targets.Section5RetainedSignedInitialLambda

@[expose] public section

/-!
# Scalar transport of the genuine signed initial zero-time endpoint

The original positive frozen field is retained throughout. The constrained
terminal comparison passes through the independent prefix and both signed
mass-zero Gaussian means, followed by the existing finite-site tensorization.
No signed second-interpolation derivative inequality is assumed here.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem signed_linear_mono {n p : ℕ} {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledGrowth G) (hFG : ∀ x y, F x y ≤ G x y)
    (A B : Fin p → Fin n → ℝ) (v : ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 v A B F x y ≤ coupledLinearStep 0 v A B G x y :=
  parisiStepPi_mono_growth le_rfl (hF.linear_input A B x y) (hG.linear_input A B x y)
    (fun _ => hFG _ _) 0

private theorem signed_linear_const_add {n p : ℕ}
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (A B : Fin p → Fin n → ℝ) (c v : ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 v A B (fun x y => c + F x y) x y =
      c + coupledLinearStep 0 v A B F x y :=
  parisiStepPi_const_add_growth c 0 v (hF.linear_input A B x y) 0

private theorem negative_linear_eq_vector {n : ℕ} (v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep 0 v (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1)) F =
      AT.gtVectorStep n 0 (Real.sqrt v) (-Real.sqrt v) F := by
  have hn (z : Fin n → ℝ) :
      pairedFieldLinear (fun i : Fin n => -(Pi.single i 1)) z = -z := by
    ext i
    simp [pairedFieldLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  funext x y
  simp only [coupledLinearStep, pairedFieldLinear_coordinates, hn, parisiStepPi,
    AT.gtVectorStep, ↓reduceIte, Pi.zero_apply, zero_add,
    neg_mul, GeneralizedLatala.gaussianProduct]
  rfl

private theorem retained_signed_vector_eq_sum {n k : ℕ} (s : RSBScheme k)
    (β v b c ℓ : ℝ)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1)) (x y : Fin n → ℝ) :
    coupledLinearStep 0 c (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1))
      (sharedStepPi n 0 b
        (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
          (fun j => section5Variance s β 1 (k + 2 - j) v) (k + 2)
          (fun x y => ∑ i, coupledSite ℓ (x i) (y i)) (k + 2))) x y =
      ∑ i, section5RetainedSignedInitialCascade s β b c v ℓ (x i, y i) := by
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5Variance s β 1 (k + 2 - j)
  have hm (j : ℕ) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hvc (j : ℕ) : Continuous (V j) := section5Variance_continuous s β 1 _
  have hvp (j : ℕ) : 0 ≤ V j v :=
    section5Variance_nonneg s β (by omega) (by omega)
      (by simpa only [s.q_zero, sub_zero] using hv)
  have hgood := splitScalarCascade_good M V hm hvc (k + 2) (k + 2)
  have he := fun x y => coupledFieldCascade_eq_sum n M V hm hvc
    (k + 2) (k + 2) v hvp ℓ x y
  change coupledLinearStep 0 c _ _ (sharedStepPi n 0 b
    (coupledFieldCascade n M (fun j => V j v) (k + 2)
      (fun x y => ∑ i, coupledSite ℓ (x i) (y i)) (k + 2))) x y = _
  rw [show coupledFieldCascade n M (fun j => V j v) (k + 2)
      (fun x y => ∑ i, coupledSite ℓ (x i) (y i)) (k + 2) =
      (fun x y => ∑ i, splitScalarCascade M V (k + 2) (k + 2) v ℓ (x i, y i)) from
    funext fun x => funext (he x)]
  have hpos := fun x y => gtVectorStep_sum_good hgood n le_rfl
    (fun _ => Real.sqrt b) (fun _ => Real.sqrt b) v ℓ x y
  rw [show sharedStepPi n 0 b
      (fun x y => ∑ i, splitScalarCascade M V (k + 2) (k + 2) v ℓ (x i, y i)) =
      (fun x y => ∑ i, section5RetainedInitialPrefix s β b v ℓ (x i, y i)) from by
    funext x y
    simpa only [sharedStepPi_eq_gtVectorStep, zero_div,
      section5RetainedInitialPrefix, section5SignedInitialPrefix, M, V] using hpos x y]
  rw [negative_linear_eq_vector]
  exact gtVectorStep_sum_good
    (finiteStep_good hgood le_rfl continuous_const continuous_const) n le_rfl
      (fun _ => Real.sqrt c) (fun _ => -Real.sqrt c) v ℓ x y

/-- The actual field-only endpoint is bounded by the retained-field scalar
lambda family, with the precise free-energy normalization. -/
theorem section5SignedInitialFieldEndpoint_le {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5SignedInitialFieldEndpoint n s β h t u ≤
      2 * Real.log 2 + section5RetainedSignedInitialV s β h
        (t * (β ^ 2 * (s.q 1 + u))) ((1 - t) * (β ^ 2 * s.q 1))
        (t * (β ^ 2 * (-u))) ℓ - ℓ * u := by
  let v := t * (β ^ 2 * (s.q 1 + u))
  let b := (1 - t) * (β ^ 2 * s.q 1)
  let c := t * (β ^ 2 * (-u))
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5Variance s β 1 (k + 2 - j) v
  let C := (n : ℝ) * (2 * Real.log 2) - ℓ * n * u
  let F := constrainedBase n (0 : EnergySpace n) 0 0 u
  let G := fun x y : Fin n → ℝ => ∑ i, coupledSite ℓ (x i) (y i)
  have hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1) := by
    have H := section5SplitVariance_mem s β (r := 1) ht
      (u := -u) (by simpa only [Nat.sub_self, s.q_zero] using
        (show -u ∈ Set.Icc 0 (s.q 1) by constructor <;> linarith [hu.1, hu.2]))
    simpa only [Nat.sub_self, s.q_zero, sub_zero, sub_neg_eq_add] using H
  have hb : 0 ≤ b := (section5SignedInitial_variances_nonneg s β ht hu
    (w := 0) ⟨le_rfl, by norm_num⟩).1
  have hm (j : ℕ) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hV (j : ℕ) : 0 ≤ V j :=
    section5Variance_nonneg s β (by omega) (by omega)
      (by simpa only [s.q_zero, sub_zero] using hv)
  have hF : CoupledGrowth F := constrainedBase_growth (0 : EnergySpace n) 0 u
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hu'
  have hG : CoupledGrowth G := coupledSite_sum_growth n ℓ
  have hFC := hF.fieldCascade M V hm hV (k + 2) (k + 2)
  have hGC := hG.fieldCascade M V hm hV (k + 2) (k + 2)
  have hp (x y : Fin n → ℝ) :
      coupledFieldCascade n M V (k + 2) F (k + 2) x y ≤
        C + coupledFieldCascade n M V (k + 2) G (k + 2) x y := by
    have H := coupledFieldCascade_mono M V hm hV (k + 2) (k + 2) hF (hG.const_add C)
      (fun x y => by
        have H := constrainedBase_time_zero_le hn (0 : EnergySpace n) 0 u ℓ hu' x y
        simp only [add_zero] at H
        convert H using 1
        dsimp [F, G, C]
        ring) x y
    rwa [coupledFieldCascade_const_add M V hm hV (k + 2) (k + 2) C hG] at H
  have hp' (x y : Fin n → ℝ) :
      sharedStepPi n 0 b (coupledFieldCascade n M V (k + 2) F (k + 2)) x y ≤
        C + sharedStepPi n 0 b (coupledFieldCascade n M V (k + 2) G (k + 2)) x y := by
    have H := sharedStepPi_mono (v := b) le_rfl hFC (hGC.const_add C) hp x y
    rwa [sharedStepPi_const_add C 0 b hGC] at H
  have H := signed_linear_mono (hFC.sharedStep le_rfl hb)
    ((hGC.sharedStep le_rfl hb).const_add C) hp'
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1)) c
    (fun _ => h) (fun _ => h)
  rw [signed_linear_const_add (hGC.sharedStep le_rfl hb),
    retained_signed_vector_eq_sum s β v b c ℓ hv] at H
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hnR.le)
  change (n : ℝ)⁻¹ * _ ≤ _ at H'
  have he : section5SignedInitialFieldEndpoint n s β h t u =
      (n : ℝ)⁻¹ * coupledLinearStep 0 c
        (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1))
        (sharedStepPi n 0 b (coupledFieldCascade n M V (k + 2) F (k + 2)))
        (fun _ => h) (fun _ => h) := by
    simp only [section5SignedInitialFieldEndpoint, section5SignedInitialOuter,
      sub_zero, one_mul, coupledLinearStep_shared, mul_zero,
      constrainedPairFieldBase_zero, one_div, v, b, c, M, V, F]
  rw [he]
  convert H' using 1
  dsimp [C, section5RetainedSignedInitialV, v, b, c]
  field_simp
  ring

/-- The zero-time interpolation bound uses the actual retained-field family,
without changing the external field or assuming the missing pressure transport. -/
theorem section5SignedInitialInterpolation_zero_le {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n) {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (-s.q 1) 0)
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5SignedInitialInterpolation n s β h U t u 0 ≤
      2 * Real.log 2 + section5RetainedSignedInitialV s β h
        (t * (β ^ 2 * (s.q 1 + u))) ((1 - t) * (β ^ 2 * s.q 1))
        (t * (β ^ 2 * (-u))) ℓ - ℓ * u := by
  rw [section5SignedInitialInterpolation_zero]
  exact section5SignedInitialFieldEndpoint_le hn s β h ht hu hu' ℓ

end SpinGlass.Targets
