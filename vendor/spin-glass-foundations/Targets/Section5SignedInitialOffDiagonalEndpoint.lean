module

public import Targets.Section5SignedInitialOffDiagonal
public import Targets.Section5SignedInitialEndpoint
public import Targets.Section5RetainedSignedSlope
public import Targets.Section5InitialSigned

@[expose] public section

/-!
# Scalar endpoint for the signed initial off-diagonal path

The constrained overlap `u` and covariance/trial overlap `v` are separated.
This gives a majorant that remains valid on both sides of `u = -q₁` while
the trial path is frozen at `v = -q₁`.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def section5SignedInitialFieldEndpointOffDiagonal {k : ℕ}
    (n : ℕ) (s : RSBScheme k) (β h t u v : ℝ) : ℝ :=
  (1 / (n : ℝ)) * section5SignedInitialOuter n s β t v 0
    (coupledFieldCascade n (fun j => section5Mass s 1 0 (k + 2 - j))
      (fun j => section5Variance s β 1 (k + 2 - j)
        (t * (β ^ 2 * (s.q 1 + v))))
      (k + 2) (constrainedPairFieldBase n 0 u) (k + 2))
    (fun _ => h) (fun _ => h)

theorem section5SignedInitialInterpolationOffDiagonal_zero
    {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0) [Nonempty (AT.ConstrainedPair n u)] :
    section5SignedInitialInterpolationOffDiagonal n s β h sk.U t u v 0 =
      section5SignedInitialFieldEndpointOffDiagonal n s β h t u v := by
  rw [← section5SignedInitialInterpolationOffDiagonal_eq_direct s β h sk
    ht hu hv (w := 0) ⟨le_rfl, zero_le_one⟩]
  simp only [section5SignedInitialInterpolationOffDiagonalDirect, zero_mul,
    Real.sqrt_zero, zero_smul, section5InterpolationVariance_zero,
    sub_neg_eq_add, integral_const, probReal_univ, smul_eq_mul, one_mul,
    section5SignedInitialFieldEndpointOffDiagonal]

private theorem offdiag_signed_linear_mono {n p : ℕ}
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledGrowth G) (hFG : ∀ x y, F x y ≤ G x y)
    (A B : Fin p → Fin n → ℝ) (v : ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 v A B F x y ≤ coupledLinearStep 0 v A B G x y :=
  parisiStepPi_mono_growth le_rfl (hF.linear_input A B x y) (hG.linear_input A B x y)
    (fun _ => hFG _ _) 0

private theorem offdiag_signed_linear_const_add {n p : ℕ}
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (A B : Fin p → Fin n → ℝ) (c v : ℝ) (x y : Fin n → ℝ) :
    coupledLinearStep 0 v A B (fun x y => c + F x y) x y =
      c + coupledLinearStep 0 v A B F x y :=
  parisiStepPi_const_add_growth c 0 v (hF.linear_input A B x y) 0

private theorem offdiag_negative_linear_eq_vector {n : ℕ} (v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledLinearStep 0 v (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => -(Pi.single i 1)) F =
      AT.gtVectorStep n 0 (Real.sqrt v) (-Real.sqrt v) F := by
  have hn (z : Fin n → ℝ) :
      pairedFieldLinear (fun i : Fin n => -(Pi.single i 1)) z = -z := by
    ext i
    simp [pairedFieldLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
  funext x y
  simp only [coupledLinearStep, pairedFieldLinear_coordinates, hn, parisiStepPi,
    AT.gtVectorStep, ↓reduceIte, Pi.zero_apply, zero_add, neg_mul,
    GeneralizedLatala.gaussianProduct]
  rfl

private theorem offdiag_retained_signed_vector_eq_sum {n k : ℕ}
    (s : RSBScheme k) (β v b c ℓ : ℝ)
    (hv : v ∈ Icc 0 (β ^ 2 * s.q 1)) (x y : Fin n → ℝ) :
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
  rw [offdiag_negative_linear_eq_vector]
  exact gtVectorStep_sum_good
    (finiteStep_good hgood le_rfl continuous_const continuous_const) n le_rfl
      (fun _ => Real.sqrt c) (fun _ => -Real.sqrt c) v ℓ x y

/-- Scalar Lagrange majorant for the separated signed endpoint. -/
theorem section5SignedInitialFieldEndpointOffDiagonal_le {n k : ℕ} (hn : 0 < n)
    (s : RSBScheme k) (β h : ℝ) {t u v : ℝ}
    (ht : t ∈ Icc 0 1) (hu : u ∈ Icc (-1 : ℝ) 0)
    (hv : v ∈ Icc (-s.q 1) 0)
    (hu' : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5SignedInitialFieldEndpointOffDiagonal n s β h t u v ≤
      2 * Real.log 2 + section5RetainedSignedInitialV s β h
        (t * (β ^ 2 * (s.q 1 + v))) ((1 - t) * (β ^ 2 * s.q 1))
        (t * (β ^ 2 * (-v))) ℓ - ℓ * u := by
  let a := t * (β ^ 2 * (s.q 1 + v))
  let b := (1 - t) * (β ^ 2 * s.q 1)
  let c := t * (β ^ 2 * (-v))
  let M := fun j => section5Mass s 1 0 (k + 2 - j)
  let V := fun j => section5Variance s β 1 (k + 2 - j) a
  let C := (n : ℝ) * (2 * Real.log 2) - ℓ * n * u
  let F := constrainedBase n (0 : EnergySpace n) 0 0 u
  let G := fun x y : Fin n → ℝ => ∑ i, coupledSite ℓ (x i) (y i)
  have ha : a ∈ Icc 0 (β ^ 2 * s.q 1) := by
    have H := section5SplitVariance_mem s β (r := 1) ht
      (u := -v) (by simpa only [Nat.sub_self, s.q_zero] using
        (show -v ∈ Icc 0 (s.q 1) by constructor <;> linarith [hv.1, hv.2]))
    simpa only [Nat.sub_self, s.q_zero, sub_zero, sub_neg_eq_add, a] using H
  have hb : 0 ≤ b := mul_nonneg (sub_nonneg.mpr ht.2)
    (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega)))
  have hm (j : ℕ) : 0 ≤ M j := section5Mass_nonneg s (by omega) le_rfl (by omega)
  have hV (j : ℕ) : 0 ≤ V j :=
    section5Variance_nonneg s β (by omega) (by omega)
      (by simpa only [s.q_zero, sub_zero] using ha)
  have hF : CoupledGrowth F := constrainedBase_growth (0 : EnergySpace n) 0 u
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) hu'
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
  have H := offdiag_signed_linear_mono (hFC.sharedStep le_rfl hb)
    ((hGC.sharedStep le_rfl hb).const_add C) hp'
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1)) c
    (fun _ => h) (fun _ => h)
  rw [offdiag_signed_linear_const_add (hGC.sharedStep le_rfl hb),
    offdiag_retained_signed_vector_eq_sum s β a b c ℓ ha] at H
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hnR.le)
  change (n : ℝ)⁻¹ * _ ≤ _ at H'
  have he : section5SignedInitialFieldEndpointOffDiagonal n s β h t u v =
      (n : ℝ)⁻¹ * coupledLinearStep 0 c
        (fun i : Fin n => Pi.single i 1) (fun i : Fin n => -(Pi.single i 1))
        (sharedStepPi n 0 b (coupledFieldCascade n M V (k + 2) F (k + 2)))
        (fun _ => h) (fun _ => h) := by
    simp only [section5SignedInitialFieldEndpointOffDiagonal, section5SignedInitialOuter,
      sub_zero, one_mul, coupledLinearStep_shared, mul_zero,
      constrainedPairFieldBase_zero, one_div, a, b, c, M, V, F]
  rw [he]
  convert H' using 1
  dsimp [C, section5RetainedSignedInitialV, a, b, c]
  field_simp
  ring

/-- The canonical lambda choice in the unit-curvature estimate is uniformly
bounded when the target overlap lies in `[-1,1]`. -/
theorem section5RetainedSignedInitialV_lambda_gain_bounded {k : ℕ}
    (s : RSBScheme k) (β h v b c u : ℝ) (hu : |u| ≤ 1) :
    ∃ ℓ : ℝ, |ℓ| ≤ 2 ∧
      section5RetainedSignedInitialV s β h v b c ℓ - ℓ * u ≤
        section5RetainedSignedInitialV s β h v b c 0 -
          (deriv (section5RetainedSignedInitialV s β h v b c) 0 - u) ^ 2 / 2 := by
  let f := section5RetainedSignedInitialV s β h v b c
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hasDerivAt_section5RetainedSignedInitialV s β h v b c x).differentiableAt.hasDerivAt
  have he (x : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    obtain ⟨e, he, _⟩ := section5RetainedSignedInitialV_second_derivative s β h v b c x
    exact he.differentiableAt.hasDerivAt
  have H := quadratic_upper_of_second_le_one hd he (fun x => by
    obtain ⟨e, he, _, hb⟩ := section5RetainedSignedInitialV_second_derivative
      s β h v b c x
    rwa [he.deriv]) (u - deriv f 0)
  have hderiv : |deriv f 0| ≤ 1 := by
    rw [(hasDerivAt_section5RetainedSignedInitialV s β h v b c 0).deriv]
    exact (section5RetainedSignedInitial_unitCurvature s β b c).triple.good.bddD v 0 (h, h)
  refine ⟨u - deriv f 0, ?_, ?_⟩
  · calc
      |u - deriv f 0| ≤ |u| + |deriv f 0| := abs_sub _ _
      _ ≤ 2 := by linarith
  · change f (u - deriv f 0) - (u - deriv f 0) * u ≤
      f 0 - (deriv f 0 - u) ^ 2 / 2
    nlinarith

/-- Quantitative scalar witness at the signed breakpoint, with a uniform
lambda bound used to transport the constraint across that breakpoint. -/
theorem exists_bounded_section5RetainedSignedInitial_breakpoint_gain {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {t t₀ e : ℝ}
    (ht : t ∈ Icc 0 t₀) (ht₀ : t₀ < 1)
    (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    ∃ ℓ : ℝ, |ℓ| ≤ 2 ∧
      section5RetainedSignedInitialV s β h 0
          ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1)) ℓ -
          ℓ * (-s.q 1) ≤
        2 * parisiF s β (k + 2) h -
          (1 - t₀) ^ 2 / 8 * (s.q 1) ^ 2 := by
  let f := section5RetainedSignedInitialV s β h 0
    ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1))
  have hu : -s.q 1 ∈ Icc (-s.q 1) 0 :=
    ⟨le_rfl, neg_nonpos.mpr (s.q_nonneg (by omega))⟩
  have Hs := section5RetainedSignedInitialV_slope_lower_bound s β h
    ht ht₀ hu he he_small hR
  obtain ⟨ℓ, hℓ, Hℓ⟩ := section5RetainedSignedInitialV_lambda_gain_bounded
    s β h 0 ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1))
      (-s.q 1) (by
        rw [abs_neg, abs_of_nonneg (s.q_nonneg (by omega))]
        exact s.q_le_one (by omega))
  have Hz := section5RetainedSignedInitialV_zero s β h
    (v := 0) (b := (1 - t) * (β ^ 2 * s.q 1))
    (c := t * (β ^ 2 * s.q 1)) (by norm_num)
    (mul_nonneg (sub_nonneg.mpr (ht.2.trans ht₀.le))
      (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))))
    (mul_nonneg ht.1 (mul_nonneg (sq_nonneg β) (s.q_nonneg (by omega))))
    (by ring)
  simp only [add_neg_cancel, neg_neg, mul_zero] at Hs
  rw [Hz] at Hℓ
  have Hsq := mul_self_le_mul_self
    (mul_nonneg (div_nonneg (sub_nonneg.mpr ht₀.le) (by norm_num))
      (s.q_nonneg (p := 1) (by omega))) Hs
  refine ⟨ℓ, hℓ, ?_⟩
  nlinarith only [Hℓ, Hsq]

/-- A uniform constrained-pressure tube crossing the signed breakpoint
`u = -q₁`.  The trial covariance stays fixed at `v = -q₁`; only the explicit
linear lambda term and quadratic off-diagonal mismatch change. -/
theorem exists_uniform_constrainedPhi_signed_initial_breakpoint_tube
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (hq1 : 0 < s.q 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 0,
      |u - (-s.q 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  obtain ⟨_, e, he, he_small, hR⟩ := section5Initial_curvature_data
    s β h ε hβ hm hq1 hright (t₀ := t₀) (by norm_num : (0 : ℝ) ≤ 535)
      hmin hnear hsmall
      (fun v hv w hw => section4THessianSquare_lipschitz_uniform
        s β h (r := 1) le_rfl (by omega)
        (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hv)
        (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hw))
  let D : ℝ := (1 - t₀) ^ 2 / 8 * (s.q 1) ^ 2
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (div_pos (sq_pos_of_pos (sub_pos.mpr ht₀)) (by norm_num))
      (sq_pos_of_pos hq1)
  let ρ : ℝ := min 1 (D / (4 * (1 + β ^ 2)))
  have hden : 0 < 4 * (1 + β ^ 2) := mul_pos (by norm_num) (by positivity)
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hD hden)
  refine ⟨ρ, hρ, D / 4, div_pos hD (by norm_num), ?_⟩
  intro t ht u hu hutube n hn sk hatt
  obtain ⟨ℓ, hℓ, Hℓ⟩ := exists_bounded_section5RetainedSignedInitial_breakpoint_gain
    s β h ht ht₀ he he_small hR
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have hv : -s.q 1 ∈ Icc (-s.q 1) 0 :=
    ⟨le_rfl, neg_nonpos.mpr hq1.le⟩
  have Hend := section5SignedInitialInterpolationOffDiagonal_endpoint_bound
    hn s β h sk ht1 hu hv
  rw [section5SignedInitialInterpolationOffDiagonal_zero s β h sk ht1 hu hv] at Hend
  have Hscalar := section5SignedInitialFieldEndpointOffDiagonal_le
    hn s β h ht1 hu hv ⟨σ, τ, hστ⟩ ℓ
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρD : ρ ≤ D / (4 * (1 + β ^ 2)) := min_le_right _ _
  have hlinabs : |ℓ * (u - (-s.q 1))| ≤ 2 * ρ := by
    rw [abs_mul]
    exact (mul_le_mul hℓ hutube (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hlin : -(ℓ * (u - (-s.q 1))) ≤ 2 * ρ :=
    (by
      have H := le_abs_self (-(ℓ * (u - (-s.q 1))))
      rw [abs_neg] at H
      exact H.trans hlinabs)
  have hmis : t * (β ^ 2 / 2) * (u - -s.q 1) ^ 2 ≤
      (β ^ 2 / 2) * ρ := by
    have htupper : t ≤ 1 := ht1.2
    have hsq : (u - -s.q 1) ^ 2 ≤ ρ ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hρ.le).mpr hutube
    have hc : 0 ≤ β ^ 2 / 2 := div_nonneg (sq_nonneg β) (by norm_num)
    have htc : t * (β ^ 2 / 2) ≤ β ^ 2 / 2 :=
      mul_le_of_le_one_left hc htupper
    have H1 : t * (β ^ 2 / 2) * (u - -s.q 1) ^ 2 ≤
        (β ^ 2 / 2) * ρ ^ 2 := by
      exact (mul_le_mul_of_nonneg_right htc (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsq hc)
    have hrhosq : ρ ^ 2 ≤ ρ := by nlinarith
    exact H1.trans (mul_le_mul_of_nonneg_left hrhosq hc)
  have herr : 2 * ρ + (β ^ 2 / 2) * ρ ≤ 5 * D / 8 := by
    have hnon : 0 ≤ 1 + β ^ 2 := by positivity
    have Hρ : 4 * (1 + β ^ 2) * ρ ≤ D := by
      exact (mul_le_mul_of_nonneg_left hρD hden.le).trans_eq (by field_simp)
    nlinarith [sq_nonneg β]
  unfold guerraPsi at ⊢
  have Htransport :
      section5RetainedSignedInitialV s β h 0
          ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1)) ℓ - ℓ * u ≤
        2 * parisiF s β (k + 2) h - D + 2 * ρ := by
    change section5RetainedSignedInitialV s β h 0
        ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1)) ℓ -
          ℓ * (-s.q 1) ≤ 2 * parisiF s β (k + 2) h - D at Hℓ
    have hid :
        section5RetainedSignedInitialV s β h 0
            ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1)) ℓ - ℓ * u =
          (section5RetainedSignedInitialV s β h 0
            ((1 - t) * (β ^ 2 * s.q 1)) (t * (β ^ 2 * s.q 1)) ℓ -
              ℓ * (-s.q 1)) - ℓ * (u - (-s.q 1)) := by ring
    rw [hid]
    linarith [Hℓ, hlin]
  simp only [add_neg_cancel, neg_neg, mul_zero] at Hscalar
  linarith

end SpinGlass.Targets
