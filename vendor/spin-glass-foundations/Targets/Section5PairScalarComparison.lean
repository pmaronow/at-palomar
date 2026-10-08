module

public import Targets.Section4NestedMonotone
public import Targets.CoupledFiniteStep
public import Targets.GaussianCauchySchwarzEquality

@[expose] public section

/-!
# Talagrand's one-step paired-versus-scalar comparison

The masses below are the raw masses of `AT.gtScalarStep`, not the doubled
mass parameter of `sharedStepPi`. Gaussian Cauchy--Schwarz therefore replaces
`m` by `2*m` in a shared scalar step. Every non-strict result includes mass zero.
-/

open MeasureTheory ProbabilityTheory Real Filter

namespace SpinGlass.Targets

private theorem linearGrowth_add {A B : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hB : HasLinearGrowth B) :
    HasLinearGrowth (fun x => A x + B x) := by
  obtain ⟨C, L, hC, hL, hA⟩ := hA
  obtain ⟨D, K, hD, hK, hB⟩ := hB
  refine ⟨C+D, L+K, by positivity, by positivity, fun x => ?_⟩
  calc
    |A x+B x| ≤ |A x|+|B x| := abs_add_le _ _
    _ ≤ C+D+(L+K)*|x| := by linarith [hA x, hB x]

private theorem linearGrowth_affine {G : ℝ → ℝ} (hG : HasLinearGrowth G)
    (x a : ℝ) : HasLinearGrowth (fun z => G (x+a*z)) := by
  obtain ⟨C, L, hC, hL, hG⟩ := hG
  refine ⟨C+L*|x|, L*|a|, by positivity, by positivity, fun z => ?_⟩
  have H : |x+a*z| ≤ |x| + |a| * |z| := by simpa [abs_mul] using abs_add_le x (a*z)
  exact (hG _).trans (by nlinarith)

/-- Gaussian Cauchy--Schwarz for scalar log means, with the genuine zero-mass
expectation retained. No convexity of the inputs is needed for this bound. -/
theorem parisiStep_add_le_double_mass {A B : ℝ → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hB : HasLinearGrowth B) (hBm : Measurable B) (v x : ℝ) :
    parisiStep m v (fun z => A z+B z) x ≤
      parisiStep (2*m) v A x+parisiStep (2*m) v B x := by
  by_cases hm0 : m=0
  · subst m
    simp only [parisiStep, ↓reduceIte, mul_zero]
    rw [integral_add (integrable_of_hasLinearGrowth hA hAm x v)
      (integrable_of_hasLinearGrowth hB hBm x v)]
  have hmpos : 0<m := lt_of_le_of_ne hm (Ne.symm hm0)
  let f := fun z => Real.exp (m*A (x+Real.sqrt v*z))
  let g := fun z => Real.exp (m*B (x+Real.sqrt v*z))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hfsq : Integrable (fun z => f z^2) (gaussianReal 0 1) := by
    convert integrable_exp_mul_of_hasLinearGrowth hA hAm (2*m) x v using 1
    funext z
    simp only [f, ← Real.exp_nat_mul]
    congr 1; ring
  have hgsq : Integrable (fun z => g z^2) (gaussianReal 0 1) := by
    convert integrable_exp_mul_of_hasLinearGrowth hB hBm (2*m) x v using 1
    funext z
    simp only [g, ← Real.exp_nat_mul]
    congr 1; ring
  have hf2 : MemLp f 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hfsq
  have hg2 : MemLp g 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgsq
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := gaussianReal 0 1) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall (fun z => (Real.exp_pos (m*A (x+Real.sqrt v*z))).le))
    (Eventually.of_forall (fun z => (Real.exp_pos (m*B (x+Real.sqrt v*z))).le))
    (by simpa using hf2) (by simpa using hg2)
  have he (a : ℝ) : (Real.exp (m*a))^2 = Real.exp ((2*m)*a) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, he, ← Real.exp_add,
    ← mul_add] at H
  have hAp : 0 < ∫ z, Real.exp ((2*m)*A (x+Real.sqrt v*z)) ∂gaussianReal 0 1 :=
    smoothing_integral_pos hA hAm x
  have hBp : 0 < ∫ z, Real.exp ((2*m)*B (x+Real.sqrt v*z)) ∂gaussianReal 0 1 :=
    smoothing_integral_pos hB hBm x
  have hABp : 0 < ∫ z, Real.exp (m*(A (x+Real.sqrt v*z)+B (x+Real.sqrt v*z)))
      ∂gaussianReal 0 1 := smoothing_integral_pos (linearGrowth_add hA hB) (hAm.add hBm) x
  have Hlog := Real.log_le_log hABp H
  rw [Real.log_mul (Real.sqrt_pos.2 hAp).ne' (Real.sqrt_pos.2 hBp).ne',
    Real.log_sqrt hAp.le, Real.log_sqrt hBp.le] at Hlog
  have hm2 : 2*m ≠ 0 := mul_ne_zero (by norm_num) hm0
  simp only [parisiStep, if_neg hm0, if_neg hm2]
  have Hmul := mul_le_mul_of_nonneg_left Hlog (le_of_lt (one_div_pos.mpr hmpos))
  exact Hmul.trans_eq (by ring)

private theorem integral_lt_of_ae_lt_probability {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hlt : ∀ᵐ z ∂μ, f z<g z) :
    (∫ z, f z ∂μ)<∫ z, g z ∂μ := by
  refine lt_of_le_of_ne (integral_mono_ae hf hg (hlt.mono fun _ h => h.le)) ?_
  intro he
  have heq := (integral_eq_iff_of_ae_le hf hg (hlt.mono fun _ h => h.le)).1 he
  obtain ⟨z, hz, hz'⟩ := (hlt.and heq).exists
  exact (ne_of_lt hz) hz'

/-- Strict scalar order is preserved by every nonnegative mass, including zero.
The strict input is only almost everywhere under the actual shifted Gaussian. -/
theorem parisiStep_lt_of_ae_lt {A B : ℝ → ℝ} {m v x : ℝ}
    (hm : 0 ≤ m) (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hB : HasLinearGrowth B) (hBm : Measurable B)
    (hAB : ∀ᵐ z ∂gaussianReal 0 1, A (x+Real.sqrt v*z)<B (x+Real.sqrt v*z)) :
    parisiStep m v A x < parisiStep m v B x := by
  by_cases hm0 : m=0
  · simpa only [parisiStep, if_pos hm0] using
      integral_lt_of_ae_lt_probability (integrable_of_hasLinearGrowth hA hAm x v)
        (integrable_of_hasLinearGrowth hB hBm x v) hAB
  have hmpos : 0<m := lt_of_le_of_ne hm (Ne.symm hm0)
  simp only [parisiStep, if_neg hm0]
  apply mul_lt_mul_of_pos_left _ (one_div_pos.mpr hmpos)
  apply Real.log_lt_log (smoothing_integral_pos hA hAm x)
  exact integral_lt_of_ae_lt_probability (integrable_exp_mul_of_hasLinearGrowth hA hAm m x v)
    (integrable_exp_mul_of_hasLinearGrowth hB hBm m x v)
    (hAB.mono fun _ hz => Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hz hmpos))

theorem gtScalarStep_eq_parisiStep_shift (m a b : ℝ) (D : ℝ → ℝ → ℝ) (x y : ℝ) :
    AT.gtScalarStep m a b D x y =
      parisiStep m 1 (fun z => D (x+a*z) (y+b*z)) 0 := by
  simp only [AT.gtScalarStep, AT.standardGaussianExpectation, parisiStep,
    Real.sqrt_one, one_mul, zero_add]

/-- A strict input comparison survives any single signed Gaussian step.
Integrability is discharged by explicit linear growth of the two shifted inputs. -/
theorem gtScalarStep_lt_of_ae_lt {m a b x y : ℝ} {D E : ℝ → ℝ → ℝ}
    (hm : 0 ≤ m)
    (hD : HasLinearGrowth (fun z => D (x+a*z) (y+b*z)))
    (hDm : Measurable (fun z => D (x+a*z) (y+b*z)))
    (hE : HasLinearGrowth (fun z => E (x+a*z) (y+b*z)))
    (hEm : Measurable (fun z => E (x+a*z) (y+b*z)))
    (hDE : ∀ᵐ z ∂gaussianReal 0 1, D (x+a*z) (y+b*z)<E (x+a*z) (y+b*z)) :
    AT.gtScalarStep m a b D x y < AT.gtScalarStep m a b E x y := by
  rw [gtScalarStep_eq_parisiStep_shift, gtScalarStep_eq_parisiStep_shift]
  exact parisiStep_lt_of_ae_lt hm hD hDm hE hEm (by simpa using hDE)

/-- Lemma 5.10(b), with the actual raw shared mass and both degenerate faces. -/
theorem gtScalarStep_shared_le {m v x y : ℝ} {D : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hm : 0 ≤ m)
    (hD : HasLinearGrowth (fun z => D (x+Real.sqrt v*z) (y+Real.sqrt v*z)))
    (hDm : Measurable (fun z => D (x+Real.sqrt v*z) (y+Real.sqrt v*z)))
    (hG : HasLinearGrowth G) (hGm : Measurable G)
    (hDG : ∀ x y, D x y ≤ G x+G y) :
    AT.gtScalarStep m (Real.sqrt v) (Real.sqrt v) D x y ≤
      parisiStep (2*m) v G x+parisiStep (2*m) v G y := by
  rw [gtScalarStep_eq_parisiStep_shift]
  have hx := linearGrowth_affine hG x (Real.sqrt v)
  have hy := linearGrowth_affine hG y (Real.sqrt v)
  have hxm : Measurable (fun z => G (x+Real.sqrt v*z)) := hGm.comp (by fun_prop)
  have hym : Measurable (fun z => G (y+Real.sqrt v*z)) := hGm.comp (by fun_prop)
  apply (parisiStep_mono_of_growth hm hD hDm (linearGrowth_add hx hy)
    (hxm.add hym) (fun z => hDG _ _) 0).trans
  simpa only [parisiStep, Real.sqrt_one, one_mul, zero_add] using
    parisiStep_add_le_double_mass hm hx hxm hy hym 1 0

private theorem gaussian_integral_neg {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z, f (-z) ∂gaussianReal 0 1) = ∫ z, f z ∂gaussianReal 0 1 := by
  have hmap : Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) = gaussianReal 0 1 :=
    by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  calc
    _ = ∫ z, f z ∂Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) := by
      rw [integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
    _ = _ := by rw [hmap]

private theorem parisiStep_negative_shift (m v y : ℝ) {G : ℝ → ℝ}
    (hGm : Measurable G) :
    parisiStep m 1 (fun z => G (y+(-Real.sqrt v)*z)) 0 = parisiStep m v G y := by
  have h (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ z, f (y+(-Real.sqrt v)*z) ∂gaussianReal 0 1) =
        ∫ z, f (y+Real.sqrt v*z) ∂gaussianReal 0 1 := by
    simpa only [mul_neg, neg_mul] using
      gaussian_integral_neg (f := fun z => f (y+Real.sqrt v*z)) (hf.comp (by fun_prop))
  simp only [parisiStep, Real.sqrt_one, one_mul, zero_add]
  split_ifs
  · exact h G hGm
  · rw [h (fun z => Real.exp (m*G z)) ((hGm.const_mul m).exp)]

/-- Lemma 5.10(c). The non-strict opposite-field comparison does not require
evenness of `G`: Gaussian reflection suffices for the second marginal. -/
theorem gtScalarStep_opposite_le {m v x y : ℝ} {D : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hm : 0 ≤ m)
    (hD : HasLinearGrowth (fun z => D (x+Real.sqrt v*z) (y+(-Real.sqrt v)*z)))
    (hDm : Measurable (fun z => D (x+Real.sqrt v*z) (y+(-Real.sqrt v)*z)))
    (hG : HasLinearGrowth G) (hGm : Measurable G)
    (hDG : ∀ x y, D x y ≤ G x+G y) :
    AT.gtScalarStep m (Real.sqrt v) (-Real.sqrt v) D x y ≤
      parisiStep (2*m) v G x+parisiStep (2*m) v G y := by
  rw [gtScalarStep_eq_parisiStep_shift]
  have hx := linearGrowth_affine hG x (Real.sqrt v)
  have hy := linearGrowth_affine hG y (-Real.sqrt v)
  have hxm : Measurable (fun z => G (x+Real.sqrt v*z)) := hGm.comp (by fun_prop)
  have hym : Measurable (fun z => G (y+(-Real.sqrt v)*z)) := hGm.comp (by fun_prop)
  apply (parisiStep_mono_of_growth hm hD hDm (linearGrowth_add hx hy)
    (hxm.add hym) (fun z => hDG _ _) 0).trans
  have H := parisiStep_add_le_double_mass hm hx hxm hy hym 1 0
  rw [parisiStep_negative_shift (2*m) v y hGm] at H
  simpa only [parisiStep, Real.sqrt_one, one_mul, zero_add] using H

private theorem scalarGuerraGrowth {G : ℝ → ℝ} (hG : HasLinearGrowth G)
    (hGm : Measurable G) : GuerraGrowth (fun z : Fin 1 → ℝ => G (z 0)) := by
  obtain ⟨C, L, _, hL, hG⟩ := hG
  exact ⟨hGm.comp (measurable_pi_apply 0), C, L, hL, fun z => by simpa [l1] using hG (z 0)⟩

private theorem scalarCoupledGrowth_add {G : ℝ → ℝ} (hG : HasLinearGrowth G)
    (hGm : Measurable G) :
    CoupledGrowth (fun x y : Fin 1 → ℝ => G (x 0)+G (y 0)) := by
  obtain ⟨C, L, _, hL, hG⟩ := hG
  refine ⟨(hGm.comp ((measurable_pi_apply 0).comp measurable_fst)).add
    (hGm.comp ((measurable_pi_apply 0).comp measurable_snd)), 2*C, L, hL, fun x y => ?_⟩
  simp only [l1, Fin.sum_univ_one]
  exact (abs_add_le _ _).trans (by linarith [hG (x 0), hG (y 0)])

/-- Lemma 5.10(a), using the existing actual independent product-Gaussian
operator at one site. Independence preserves the scalar mass `m`. -/
theorem independentStepPi_one_le_scalar {m v : ℝ} {D : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hm : 0 ≤ m) (hD : CoupledGrowth (fun x y : Fin 1 → ℝ => D (x 0) (y 0)))
    (hG : HasLinearGrowth G) (hGm : Measurable G)
    (hDG : ∀ x y, D x y ≤ G x+G y) (x y : ℝ) :
    independentStepPi 1 m v (fun x y => D (x 0) (y 0)) (fun _ => x) (fun _ => y) ≤
      parisiStep m v G x+parisiStep m v G y := by
  have H := independentStepPi_mono (v := v) hm hD (scalarCoupledGrowth_add hG hGm)
    (fun x y => hDG (x 0) (y 0)) (fun _ => x) (fun _ => y)
  rw [independentStepPi_add m v (scalarGuerraGrowth hG hGm) (scalarGuerraGrowth hG hGm)] at H
  have hx := parisiStepPi_sum (n := 1) m v hG hGm (fun _ => x)
  have hy := parisiStepPi_sum (n := 1) m v hG hGm (fun _ => y)
  simp only [Fin.sum_univ_one] at hx hy
  rwa [hx, hy] at H

/-- Strict order through a genuine independent paired Gaussian step, at every
nonnegative mass. The input comparison is only required almost everywhere. -/
theorem independentStepPi_lt_of_ae_lt {n : ℕ} {m v : ℝ}
    {D E : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hm : 0 ≤ m) (hD : CoupledGrowth D) (hE : CoupledGrowth E)
    (x y : Fin n → ℝ)
    (hDE : ∀ᵐ z ∂(piGauss n).prod (piGauss n),
      D (fun i => x i+Real.sqrt v*z.1 i) (fun i => y i+Real.sqrt v*z.2 i) <
      E (fun i => x i+Real.sqrt v*z.1 i) (fun i => y i+Real.sqrt v*z.2 i)) :
    independentStepPi n m v D x y < independentStepPi n m v E x y := by
  by_cases hm0 : m=0
  · simp only [independentStepPi, if_pos hm0]
    exact integral_lt_of_ae_lt_probability (hD.integrable_shift v x y)
      (hE.integrable_shift v x y) hDE
  have hmpos : 0<m := lt_of_le_of_ne hm (Ne.symm hm0)
  simp only [independentStepPi, if_neg hm0]
  apply mul_lt_mul_of_pos_left _ (one_div_pos.mpr hmpos)
  apply Real.log_lt_log (hD.integral_exp_shift_pos m v x y)
  exact integral_lt_of_ae_lt_probability (hD.integrable_exp_shift m v x y)
    (hE.integrable_exp_shift m v x y)
    (hDE.mono fun _ hz => Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hz hmpos))

private theorem independent_one_ae_off_diagonals {v : ℝ} (hv : 0<v) (x y : ℝ) :
    ∀ᵐ z ∂(piGauss 1).prod (piGauss 1),
      x+Real.sqrt v*z.1 0 ≠ y+Real.sqrt v*z.2 0 ∧
      x+Real.sqrt v*z.1 0 ≠ -(y+Real.sqrt v*z.2 0) := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  apply (Measure.ae_prod_iff_ae_ae ?_).2
  · apply Eventually.of_forall
    intro z₁
    have hne (c : ℝ) : ∀ᵐ z₂ ∂piGauss 1, y+Real.sqrt v*z₂ 0 ≠ c := by
      have H : ∀ᵐ z ∂(piGauss 1).map (Function.eval 0),
          z ≠ (c-y)/Real.sqrt v := by
        rw [piGauss_map_eval]
        exact (gaussianReal 0 1).ae_ne _
      have H' : ∀ᵐ z₂ ∂piGauss 1, z₂ 0 ≠ (c-y)/Real.sqrt v :=
        ae_of_ae_map (measurable_pi_apply 0).aemeasurable H
      filter_upwards [H'] with z₂ hz
      intro he
      apply hz
      apply (eq_div_iff (Real.sqrt_pos.2 hv).ne').2
      linarith
    filter_upwards [hne (x+Real.sqrt v*z₁ 0), hne (-(x+Real.sqrt v*z₁ 0))] with z₂ h₁ h₂
    exact ⟨Ne.symm h₁, fun he => h₂ (by linarith)⟩
  · exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl.inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl

/-- The strict part of Lemma 5.10(a): a positive independent variance spreads
strictness away from the two diagonals to strictness at every starting pair.
This includes zero mass and needs neither continuity nor convexity of `D`. -/
theorem independentStepPi_one_lt_scalar_of_off_diagonals {m v : ℝ}
    {D : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hm : 0 ≤ m) (hv : 0<v)
    (hD : CoupledGrowth (fun x y : Fin 1 → ℝ => D (x 0) (y 0)))
    (hG : HasLinearGrowth G) (hGm : Measurable G)
    (hDG : ∀ x y, x≠y → x≠-y → D x y<G x+G y) (x y : ℝ) :
    independentStepPi 1 m v (fun x y => D (x 0) (y 0)) (fun _ => x) (fun _ => y) <
      parisiStep m v G x+parisiStep m v G y := by
  have H := independentStepPi_lt_of_ae_lt (v := v) hm hD (scalarCoupledGrowth_add hG hGm)
    (fun _ => x) (fun _ => y)
    ((independent_one_ae_off_diagonals hv x y).mono fun z hz => hDG _ _ hz.1 hz.2)
  rw [independentStepPi_add m v (scalarGuerraGrowth hG hGm) (scalarGuerraGrowth hG hGm)] at H
  have hx := parisiStepPi_sum (n := 1) m v hG hGm (fun _ => x)
  have hy := parisiStepPi_sum (n := 1) m v hG hGm (fun _ => y)
  simp only [Fin.sum_univ_one] at hx hy
  rwa [hx, hy] at H

/-- Equality in the scalar Cauchy--Schwarz comparison identifies the two
continuous input profiles up to an additive constant. -/
theorem exists_sub_eq_const_of_parisiStep_add_eq {A B : ℝ → ℝ} {m : ℝ}
    (hm : 0<m) (hA : HasLinearGrowth A) (hAc : Continuous A)
    (hB : HasLinearGrowth B) (hBc : Continuous B)
    (he : parisiStep m 1 (fun z => A z+B z) 0 =
      parisiStep (2*m) 1 A 0+parisiStep (2*m) 1 B 0) :
    ∃ c : ℝ, ∀ z, A z-B z=c := by
  let f := fun z => Real.exp (m*A z)
  let g := fun z => Real.exp (m*B z)
  have hexp (a : ℝ) : (Real.exp (m*a))^2=Real.exp ((2*m)*a) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hf : Integrable (fun z => f z^2) (gaussianReal 0 1) := by
    simpa only [f, hexp, Real.sqrt_one, one_mul, zero_add] using
      integrable_exp_mul_of_hasLinearGrowth hA hAc.measurable (2*m) 0 1
  have hg : Integrable (fun z => g z^2) (gaussianReal 0 1) := by
    simpa only [g, hexp, Real.sqrt_one, one_mul, zero_add] using
      integrable_exp_mul_of_hasLinearGrowth hB hBc.measurable (2*m) 0 1
  have hfg : Integrable (fun z => f z*g z) (gaussianReal 0 1) := by
    simpa only [f, g, ← Real.exp_add, ← mul_add, Real.sqrt_one, one_mul, zero_add] using
      integrable_exp_mul_of_hasLinearGrowth (linearGrowth_add hA hB)
        (hAc.measurable.add hBc.measurable) m 0 1
  have hfpos : 0<∫ z, f z^2 ∂gaussianReal 0 1 := by
    simpa only [f, hexp, Real.sqrt_one, one_mul, zero_add] using
      (smoothing_integral_pos (m := 2*m) (v := 1) hA hAc.measurable 0)
  have hgpos : 0<∫ z, g z^2 ∂gaussianReal 0 1 := by
    simpa only [g, hexp, Real.sqrt_one, one_mul, zero_add] using
      (smoothing_integral_pos (m := 2*m) (v := 1) hB hBc.measurable 0)
  have hfgpos : 0<∫ z, f z*g z ∂gaussianReal 0 1 := by
    simpa only [f, g, ← Real.exp_add, ← mul_add, Real.sqrt_one, one_mul, zero_add] using
      (smoothing_integral_pos (m := m) (v := 1) (linearGrowth_add hA hB)
        (hAc.measurable.add hBc.measurable) 0)
  have hm2 : 2*m≠0 := ne_of_gt (by positivity)
  have he' : (1/m)*Real.log (∫ z, f z*g z ∂gaussianReal 0 1) =
      (1/(2*m))*Real.log (∫ z, f z^2 ∂gaussianReal 0 1)+
      (1/(2*m))*Real.log (∫ z, g z^2 ∂gaussianReal 0 1) := by
    simpa only [parisiStep, if_neg hm.ne', if_neg hm2, Real.sqrt_one, one_mul,
      zero_add, f, g, hexp, ← Real.exp_add, ← mul_add] using he
  have hlogs : 2*Real.log (∫ z, f z*g z ∂gaussianReal 0 1) =
      Real.log (∫ z, f z^2 ∂gaussianReal 0 1)+
        Real.log (∫ z, g z^2 ∂gaussianReal 0 1) := by
    field_simp at he'
    nlinarith
  have hcs : (∫ z, f z*g z ∂gaussianReal 0 1)^2 =
      (∫ z, f z^2 ∂gaussianReal 0 1)*(∫ z, g z^2 ∂gaussianReal 0 1) := by
    apply Real.log_injOn_pos (sq_pos_of_pos hfgpos) (mul_pos hfpos hgpos)
    rw [Real.log_pow, Real.log_mul hfpos.ne' hgpos.ne']
    simpa using hlogs
  obtain ⟨c, hc⟩ := eq_mul_of_gaussian_cauchySchwarz_eq
    (Real.continuous_exp.comp (hAc.const_mul m))
    (Real.continuous_exp.comp (hBc.const_mul m)) (fun z => Real.exp_pos (m*B z))
    hf hg hfg hcs
  have hcpos : 0<c := by
    have H := hc 0
    change Real.exp (m*A 0)=c*Real.exp (m*B 0) at H
    nlinarith [Real.exp_pos (m*A 0), Real.exp_pos (m*B 0)]
  refine ⟨Real.log c/m, fun z => ?_⟩
  have H := congrArg Real.log (hc z)
  change Real.log (Real.exp (m*A z))=Real.log (c*Real.exp (m*B z)) at H
  rw [Real.log_exp, Real.log_mul hcpos.ne' (Real.exp_ne_zero _), Real.log_exp] at H
  apply (eq_div_iff hm.ne').2
  nlinarith

/-- The strict shared comparison in Lemma 5.10(b), in the differentiable
strict-convexity form supplied by the actual scalar cascades. -/
theorem gtScalarStep_shared_lt_of_strictMono_deriv {m v x y : ℝ}
    {D : ℝ → ℝ → ℝ} {G G' : ℝ → ℝ}
    (hm : 0<m) (hv : 0<v)
    (hD : HasLinearGrowth (fun z => D (x+Real.sqrt v*z) (y+Real.sqrt v*z)))
    (hDm : Measurable (fun z => D (x+Real.sqrt v*z) (y+Real.sqrt v*z)))
    (hG : HasLinearGrowth G) (hd : ∀ z, HasDerivAt G (G' z) z)
    (hstrict : StrictMono G') (hDG : ∀ x y, D x y≤G x+G y) (hxy : x≠y) :
    AT.gtScalarStep m (Real.sqrt v) (Real.sqrt v) D x y <
      parisiStep (2*m) v G x+parisiStep (2*m) v G y := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 (fun z => (hd z).continuousAt)
  have hx := linearGrowth_affine hG x (Real.sqrt v)
  have hy := linearGrowth_affine hG y (Real.sqrt v)
  have hxc : Continuous (fun z => G (x+Real.sqrt v*z)) := hGc.comp (by fun_prop)
  have hyc : Continuous (fun z => G (y+Real.sqrt v*z)) := hGc.comp (by fun_prop)
  have hle := parisiStep_add_le_double_mass hm.le hx hxc.measurable hy hyc.measurable 1 0
  have hlt : parisiStep m 1 (fun z => G (x+Real.sqrt v*z)+G (y+Real.sqrt v*z)) 0 <
      parisiStep (2*m) 1 (fun z => G (x+Real.sqrt v*z)) 0+
        parisiStep (2*m) 1 (fun z => G (y+Real.sqrt v*z)) 0 := by
    refine lt_of_le_of_ne hle ?_
    intro he
    obtain ⟨c, hc⟩ := exists_sub_eq_const_of_parisiStep_add_eq hm hx hxc hy hyc he
    apply hxy
    apply eq_of_sub_translate_eq_const_of_strictMono_deriv hd hstrict (c := c)
    intro z
    simpa only [mul_div_cancel₀ _ (Real.sqrt_pos.2 hv).ne'] using hc (z/Real.sqrt v)
  rw [gtScalarStep_eq_parisiStep_shift]
  apply (parisiStep_mono_of_growth hm.le hD hDm (linearGrowth_add hx hy)
    (hxc.measurable.add hyc.measurable) (fun z => hDG _ _) 0).trans_lt
  simpa only [parisiStep, Real.sqrt_one, one_mul, zero_add] using hlt

/-- The strict opposite-field comparison in Lemma 5.10(c). Evenness reflects
the second profile, and strictness can fail only on the anti-diagonal. -/
theorem gtScalarStep_opposite_lt_of_strictMono_deriv {m v x y : ℝ}
    {D : ℝ → ℝ → ℝ} {G G' : ℝ → ℝ}
    (hm : 0<m) (hv : 0<v)
    (hD : HasLinearGrowth (fun z => D (x+Real.sqrt v*z) (y+(-Real.sqrt v)*z)))
    (hDm : Measurable (fun z => D (x+Real.sqrt v*z) (y+(-Real.sqrt v)*z)))
    (hG : HasLinearGrowth G) (hd : ∀ z, HasDerivAt G (G' z) z)
    (hstrict : StrictMono G') (hEven : Function.Even G)
    (hDG : ∀ x y, D x y≤G x+G y) (hxy : x≠-y) :
    AT.gtScalarStep m (Real.sqrt v) (-Real.sqrt v) D x y <
      parisiStep (2*m) v G x+parisiStep (2*m) v G y := by
  have he (z : ℝ) : -(-y+Real.sqrt v*z)=y+(-Real.sqrt v)*z := by ring
  have H := gtScalarStep_shared_lt_of_strictMono_deriv (D := fun a b => D a (-b))
    (x := x) (y := -y) hm hv (by simpa only [he] using hD)
    (by simpa only [he] using hDm) hG hd hstrict
    (fun a b => by simpa only [hEven b] using hDG a (-b)) hxy
  simpa only [AT.gtScalarStep, he, parisiStep_even hEven (2*m) v y] using H

end SpinGlass.Targets
