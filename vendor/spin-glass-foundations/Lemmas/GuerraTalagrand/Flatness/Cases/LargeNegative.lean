module

public import Lemmas.GuerraTalagrand.Flatness.Core
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory NNReal

namespace SpinGlass.AT

/-! ### Large negative overlaps `-1 ≤ v ≤ -q` -/

/-- On the large-negative-overlap branch, the distance to `q` is at most two. -/
lemma sub_sq_le_four_of_negative_overlap
    {q v : ℝ}
    (hq0 : 0 ≤ q)
    (hv : v ∈ Icc (-1 : ℝ) (-q)) :
    (v - q) ^ 2 ≤ 4 := by
  have hv_lower : -1 ≤ v := hv.1
  have hv_upper : v ≤ -q := hv.2
  have hq1 : q ≤ 1 := by
    linarith
  have hdiff_lower : -2 ≤ v - q := by
    linarith
  have hdiff_upper : v - q ≤ 0 := by
    linarith
  have hprod :
      0 ≤ ((v - q) + 2) * (2 - (v - q)) := by
    apply mul_nonneg
    · linarith
    · linarith
  nlinarith

/-- The terminal-zero diagonal step at unit time has an explicit form. -/
lemma flatness_diagonal_one_terminal_zero
    (b x₁ x₂ : ℝ) :
    gtDiagonalStep 1 b (gtTerminal 0) x₁ x₂ =
      b ^ 2
        + Real.log (Real.cosh x₁)
        + Real.log (Real.cosh x₂) := by
  rw [gtDiagonalStep_one_terminal, gtTerminal_zero]
  ring

private lemma flatness_integrable_cosh_affine
    (x a : ℝ) :
    Integrable
      (fun z : ℝ => Real.cosh (x + a * z))
      (gaussianReal 0 1) := by
  have hp :
      Integrable
        (fun z : ℝ => Real.exp (x + a * z))
        (gaussianReal 0 1) := by
    have h :=
      integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : NNReal)) a
    have h' := h.const_mul (Real.exp x)
    convert h' using 1
    funext z
    rw [Real.exp_add]

  have hm :
      Integrable
        (fun z : ℝ => Real.exp (-(x + a * z)))
        (gaussianReal 0 1) := by
    have h :=
      integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : NNReal)) (-a)
    have h' := h.const_mul (Real.exp (-x))
    convert h' using 1
    funext z
    rw [show -(x + a * z) = -x + (-a) * z by ring, Real.exp_add]

  have hadd := hp.add hm
  have hhalf := hadd.const_mul (1 / 2 : ℝ)
  convert hhalf using 1
  funext z
  simp only [Pi.add_apply]
  rw [Real.cosh_eq]
  ring

private lemma flatness_standardGaussian_exp_mul
    (t : ℝ) :
    standardGaussianExpectation
        (fun z : ℝ => Real.exp (t * z)) =
      Real.exp (t ^ 2 / 2) := by
  unfold standardGaussianExpectation
  have h :=
    congrFun
      (mgf_id_gaussianReal
        (μ := 0) (v := (1 : NNReal))) t
  simpa [mgf] using h

private lemma flatness_standardGaussian_cosh
    (x a : ℝ) :
    standardGaussianExpectation
        (fun z : ℝ => Real.cosh (x + a * z)) =
      Real.exp (a ^ 2 / 2) * Real.cosh x := by
  have hp :
      standardGaussianExpectation
          (fun z : ℝ => Real.exp (x + a * z)) =
        Real.exp x * Real.exp (a ^ 2 / 2) := by
    unfold standardGaussianExpectation
    calc
      (∫ z, Real.exp (x + a * z) ∂gaussianReal 0 1) =
          ∫ z, Real.exp x * Real.exp (a * z) ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [← Real.exp_add]
      _ = Real.exp x * ∫ z, Real.exp (a * z) ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
      _ = Real.exp x * Real.exp (a ^ 2 / 2) := by
          change Real.exp x *
          standardGaussianExpectation (fun z => Real.exp (a * z)) = _
          rw [flatness_standardGaussian_exp_mul]

  have hm :
      standardGaussianExpectation
          (fun z : ℝ => Real.exp (-(x + a * z))) =
        Real.exp (-x) * Real.exp (a ^ 2 / 2) := by
    unfold standardGaussianExpectation
    calc
      (∫ z, Real.exp (-(x + a * z)) ∂gaussianReal 0 1) =
          ∫ z, Real.exp (-x) * Real.exp ((-a) * z)
            ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [show -(x + a * z) = -x + (-a) * z by ring, Real.exp_add]
      _ = Real.exp (-x) * ∫ z, Real.exp ((-a) * z) ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
      _ = Real.exp (-x) * Real.exp (a ^ 2 / 2) := by
          change Real.exp (-x) *
          standardGaussianExpectation (fun z => Real.exp ((-a) * z)) = _
          rw [flatness_standardGaussian_exp_mul]
          ring_nf

  have hplus := flatness_integrable_cosh_affine x a
  unfold standardGaussianExpectation at hp hm ⊢
  rw [show
      (fun z : ℝ => Real.cosh (x + a * z)) =
        fun z =>
          (1 / 2 : ℝ) *
            (Real.exp (x + a * z) + Real.exp (-(x + a * z))) by
      funext z
      rw [Real.cosh_eq]
      ring]
  rw [integral_const_mul]

  have hip :
      Integrable
        (fun z : ℝ => Real.exp (x + a * z))
        (gaussianReal 0 1) := by
    have h :=
      integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : NNReal)) a
    have h' := h.const_mul (Real.exp x)
    convert h' using 1
    funext z
    rw [Real.exp_add]

  have him :
      Integrable
        (fun z : ℝ => Real.exp (-(x + a * z)))
        (gaussianReal 0 1) := by
    have h :=
      integrable_exp_mul_gaussianReal
        (μ := 0) (v := (1 : NNReal)) (-a)
    have h' := h.const_mul (Real.exp (-x))
    convert h' using 1
    funext z
    rw [show -(x + a * z) = -x + (-a) * z by ring, Real.exp_add]

  rw [integral_add hip him, hp, hm, Real.cosh_eq]
  ring

private lemma flatness_standardGaussian_cauchy_schwarz
    (f g : ℝ → ℝ)
    (hf : MemLp f 2 (gaussianReal 0 1))
    (hg : MemLp g 2 (gaussianReal 0 1))
    (hf0 : ∀ z, 0 ≤ f z)
    (hg0 : ∀ z, 0 ≤ g z) :
    standardGaussianExpectation (fun z => f z * g z) ≤
      Real.sqrt
          (standardGaussianExpectation (fun z => f z ^ 2)) *
        Real.sqrt
          (standardGaussianExpectation (fun z => g z ^ 2)) := by
  unfold standardGaussianExpectation
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    exact Real.holderConjugate_iff.mpr
      ⟨by norm_num, by norm_num⟩
  have hf' :
      MemLp f (ENNReal.ofReal (2 : ℝ))
        (gaussianReal 0 1) := by
    simpa using hf
  have hg' :
      MemLp g (ENNReal.ofReal (2 : ℝ))
        (gaussianReal 0 1) := by
    simpa using hg
  have h :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := gaussianReal 0 1)
      h22
      (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall hg0)
      hf' hg'
  simpa [Real.sqrt_eq_rpow] using h

lemma flatness_negative_half_step_le
    (a b x₁ x₂ : ℝ) :
    gtRankOneStep (1 / 2) a (-1)
        (gtDiagonalStep 1 b (gtTerminal 0))
        x₁ x₂
      ≤
    b ^ 2 + a ^ 2
      + Real.log (Real.cosh x₁)
      + Real.log (Real.cosh x₂) := by
  let f : ℝ → ℝ := fun z =>
    Real.exp ((1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)))
  let g : ℝ → ℝ := fun z =>
    Real.exp ((1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)))
  have hf_sq (z : ℝ) :
      f z ^ 2 = Real.cosh (x₁ + a * z) := by
    dsimp [f]
    rw [pow_two, ← Real.exp_add]
    rw [show
      (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) =
        Real.log (Real.cosh (x₁ + a * z)) by ring]
    exact Real.exp_log (Real.cosh_pos _)
  have hg_sq (z : ℝ) :
      g z ^ 2 = Real.cosh (x₂ + (-1) * a * z) := by
    dsimp [g]
    rw [pow_two, ← Real.exp_add]
    rw [show
      (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) =
        Real.log (Real.cosh (x₂ + (-1) * a * z) ) by ring]
    exact Real.exp_log (Real.cosh_pos _)
  have hfcont : Continuous f := by
    have hfun : f = fun z => Real.sqrt (Real.cosh (x₁ + a * z)) := by
      funext z
      dsimp [f]
      rw [Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (Real.cosh_pos (x₁ + a * z))]
      congr 1
      ring
    rw [hfun]
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hgcont : Continuous g := by
    have hfun : g = fun z => Real.sqrt (Real.cosh (x₂ + (-1) * a * z)) := by
      funext z
      dsimp [g]
      rw [Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (Real.cosh_pos (x₂ + (-1) * a * z))]
      congr 1
      ring
    rw [hfun]
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hf_sq_int :
      Integrable (fun z => f z ^ 2) (gaussianReal 0 1) := by
    have h := flatness_integrable_cosh_affine x₁ a
    exact h.congr (Filter.Eventually.of_forall fun z => (hf_sq z).symm)
  have hg_sq_int :
      Integrable (fun z => g z ^ 2) (gaussianReal 0 1) := by
    have h := flatness_integrable_cosh_affine x₂ (-a)
    exact h.congr (Filter.Eventually.of_forall fun z => by
      calc
        Real.cosh (x₂ + (-a) * z) =
            Real.cosh (x₂ + (-1) * a * z) := by
              congr 2
              ring
        _ = g z ^ 2 := (hg_sq z).symm)
  have hfmem : MemLp f 2 (gaussianReal 0 1) := by
    exact (memLp_two_iff_integrable_sq hfcont.aestronglyMeasurable).2 hf_sq_int
  have hgmem : MemLp g 2 (gaussianReal 0 1) := by
    exact (memLp_two_iff_integrable_sq hgcont.aestronglyMeasurable).2 hg_sq_int
  have hf0 (z : ℝ) : 0 ≤ f z := by
    dsimp [f]
    positivity
  have hg0 (z : ℝ) : 0 ≤ g z := by
    dsimp [g]
    positivity
  let I : ℝ := standardGaussianExpectation (fun z => f z * g z)
  have hcs :
      I ≤
        Real.sqrt (Real.exp (a ^ 2 / 2) * Real.cosh x₁) *
          Real.sqrt (Real.exp (a ^ 2 / 2) * Real.cosh x₂) := by
    have h := flatness_standardGaussian_cauchy_schwarz f g hfmem hgmem hf0 hg0
    have hfE :
        standardGaussianExpectation (fun z => f z ^ 2) =
          Real.exp (a ^ 2 / 2) * Real.cosh x₁ := by
      calc
        standardGaussianExpectation (fun z => f z ^ 2) =
            standardGaussianExpectation (fun z => Real.cosh (x₁ + a * z)) := by
              apply congrArg standardGaussianExpectation
              funext z
              exact hf_sq z
        _ = Real.exp (a ^ 2 / 2) * Real.cosh x₁ :=
          flatness_standardGaussian_cosh x₁ a
    have hgE :
        standardGaussianExpectation (fun z => g z ^ 2) =
          Real.exp (a ^ 2 / 2) * Real.cosh x₂ := by
      calc
        standardGaussianExpectation (fun z => g z ^ 2) =
            standardGaussianExpectation (fun z => Real.cosh (x₂ + (-a) * z)) := by
              apply congrArg standardGaussianExpectation
              funext z
              rw [hg_sq]
              congr 2
              ring
        _ = Real.exp ((-a) ^ 2 / 2) * Real.cosh x₂ :=
          flatness_standardGaussian_cosh x₂ (-a)
        _ = Real.exp (a ^ 2 / 2) * Real.cosh x₂ := by ring_nf
    simpa [I, hfE, hgE] using h
  let C : ℝ :=
    a ^ 2 + Real.log (Real.cosh x₁) + Real.log (Real.cosh x₂)
  have hR :
      Real.sqrt (Real.exp (a ^ 2 / 2) * Real.cosh x₁) *
          Real.sqrt (Real.exp (a ^ 2 / 2) * Real.cosh x₂) =
        Real.exp (C / 2) := by
    have hA : 0 < Real.exp (a ^ 2 / 2) * Real.cosh x₁ := by positivity
    have hB : 0 < Real.exp (a ^ 2 / 2) * Real.cosh x₂ := by positivity
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB]
    rw [← Real.exp_add]
    congr 1
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x₁).ne']
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x₂).ne']
    rw [Real.log_exp]
    dsimp [C]
    ring
  have hIle : I ≤ Real.exp (C / 2) := by
    rw [← hR]
    exact hcs
  have hIint :
      Integrable (fun z => f z * g z) (gaussianReal 0 1) := by
    have hdom :
        Integrable
          (fun z => (1 / 2 : ℝ) * (f z ^ 2 + g z ^ 2))
          (gaussianReal 0 1) :=
      (hf_sq_int.add hg_sq_int).const_mul (1 / 2 : ℝ)
    refine hdom.mono' (hfcont.mul hgcont).aestronglyMeasurable ?_
    filter_upwards [] with z
    have hs := sq_nonneg (f z - g z)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 z) (hg0 z))]
    nlinarith
  have hIpos : 0 < I := by
    dsimp [I, standardGaussianExpectation]
    rw [integral_pos_iff_support_of_nonneg
      (fun z => mul_nonneg (hf0 z) (hg0 z)) hIint]
    have hsupp : Function.support (fun z => f z * g z) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact mul_ne_zero
        (by dsimp [f]; exact (Real.exp_pos _).ne')
        (by dsimp [g]; exact (Real.exp_pos _).ne')
    rw [hsupp]
    simp
  let J : ℝ :=
    standardGaussianExpectation (fun z =>
      Real.exp ((1 / 2 : ℝ) *
        gtDiagonalStep 1 b (gtTerminal 0)
          (x₁ + a * z) (x₂ + (-1) * a * z)))
  have hJ : J = Real.exp (b ^ 2 / 2) * I := by
    dsimp [J, I, standardGaussianExpectation]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [gtDiagonalStep_one_terminal, gtTerminal_zero]
    dsimp [f, g]
    rw [show
      (1 / 2 : ℝ) *
          (Real.log (Real.cosh (x₁ + a * z)) +
            Real.log (Real.cosh (x₂ + (-1) * a * z)) + b ^ 2) =
        b ^ 2 / 2 +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) by ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  have hJpos : 0 < J := by
    rw [hJ]
    exact mul_pos (Real.exp_pos _) hIpos
  have hJle : J ≤ Real.exp ((b ^ 2 + C) / 2) := by
    rw [hJ]
    calc
      Real.exp (b ^ 2 / 2) * I ≤
          Real.exp (b ^ 2 / 2) * Real.exp (C / 2) := by
            exact mul_le_mul_of_nonneg_left hIle (Real.exp_nonneg _)
      _ = Real.exp ((b ^ 2 + C) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hlog : Real.log J ≤ (b ^ 2 + C) / 2 :=
    (Real.log_le_iff_le_exp hJpos).2 hJle
  have hmain :
      2 * Real.log J ≤
        b ^ 2 + a ^ 2 + Real.log (Real.cosh x₁) + Real.log (Real.cosh x₂) := by
    dsimp [C] at hlog
    nlinarith
  simpa [gtRankOneStep, J] using hmain

private lemma flatness_negative_half_step_lt_of_nontrivial
    (a b x₁ x₂ : ℝ)
    (ha : a ≠ 0)
    (hx : x₁ ≠ -x₂) :
    gtRankOneStep (1 / 2) a (-1)
        (gtDiagonalStep 1 b (gtTerminal 0))
        x₁ x₂
      <
    b ^ 2 + a ^ 2
      + Real.log (Real.cosh x₁)
      + Real.log (Real.cosh x₂) := by
  let f : ℝ → ℝ := fun z =>
    Real.exp ((1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)))
  let g : ℝ → ℝ := fun z =>
    Real.exp ((1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)))
  have hf_sq (z : ℝ) :
      f z ^ 2 = Real.cosh (x₁ + a * z) := by
    dsimp [f]
    rw [pow_two, ← Real.exp_add]
    rw [show
      (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) =
        Real.log (Real.cosh (x₁ + a * z)) by ring]
    exact Real.exp_log (Real.cosh_pos _)
  have hg_sq (z : ℝ) :
      g z ^ 2 = Real.cosh (x₂ + (-1) * a * z) := by
    dsimp [g]
    rw [pow_two, ← Real.exp_add]
    rw [show
      (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) =
        Real.log (Real.cosh (x₂ + (-1) * a * z)) by ring]
    exact Real.exp_log (Real.cosh_pos _)
  have hfcont : Continuous f := by
    have hfun : f = fun z => Real.sqrt (Real.cosh (x₁ + a * z)) := by
      funext z
      dsimp [f]
      rw [Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (Real.cosh_pos (x₁ + a * z))]
      congr 1
      ring
    rw [hfun]
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hgcont : Continuous g := by
    have hfun : g = fun z => Real.sqrt (Real.cosh (x₂ + (-1) * a * z)) := by
      funext z
      dsimp [g]
      rw [Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (Real.cosh_pos (x₂ + (-1) * a * z))]
      congr 1
      ring
    rw [hfun]
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hf_sq_int :
      Integrable (fun z => f z ^ 2) (gaussianReal 0 1) := by
    have h := flatness_integrable_cosh_affine x₁ a
    exact h.congr (Filter.Eventually.of_forall fun z => (hf_sq z).symm)
  have hg_sq_int :
      Integrable (fun z => g z ^ 2) (gaussianReal 0 1) := by
    have h := flatness_integrable_cosh_affine x₂ (-a)
    exact h.congr (Filter.Eventually.of_forall fun z => by
      calc
        Real.cosh (x₂ + (-a) * z) =
            Real.cosh (x₂ + (-1) * a * z) := by
              (congr 2; ring)
        _ = g z ^ 2 := (hg_sq z).symm)
  have hf0 (z : ℝ) : 0 ≤ f z := by
    dsimp [f]
    positivity
  have hg0 (z : ℝ) : 0 ≤ g z := by
    dsimp [g]
    positivity
  have hIint :
      Integrable (fun z => f z * g z) (gaussianReal 0 1) := by
    have hdom :
        Integrable (fun z => (1 / 2 : ℝ) * (f z ^ 2 + g z ^ 2))
          (gaussianReal 0 1) :=
      (hf_sq_int.add hg_sq_int).const_mul (1 / 2 : ℝ)
    refine hdom.mono' (hfcont.mul hgcont).aestronglyMeasurable ?_
    filter_upwards [] with z
    have hs := sq_nonneg (f z - g z)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 z) (hg0 z))]
    nlinarith
  let E₁ : ℝ := Real.exp (a ^ 2 / 2) * Real.cosh x₁
  let E₂ : ℝ := Real.exp (a ^ 2 / 2) * Real.cosh x₂
  have hE₁pos : 0 < E₁ := by
    dsimp [E₁]
    positivity
  have hE₂pos : 0 < E₂ := by
    dsimp [E₂]
    positivity
  have hfE : (∫ z, f z ^ 2 ∂gaussianReal 0 1) = E₁ := by
    change standardGaussianExpectation (fun z => f z ^ 2) = E₁
    calc
      standardGaussianExpectation (fun z => f z ^ 2) =
          standardGaussianExpectation (fun z => Real.cosh (x₁ + a * z)) := by
            apply congrArg standardGaussianExpectation
            funext z
            exact hf_sq z
      _ = Real.exp (a ^ 2 / 2) * Real.cosh x₁ :=
        flatness_standardGaussian_cosh x₁ a
      _ = E₁ := rfl
  have hgE : (∫ z, g z ^ 2 ∂gaussianReal 0 1) = E₂ := by
    change standardGaussianExpectation (fun z => g z ^ 2) = E₂
    calc
      standardGaussianExpectation (fun z => g z ^ 2) =
          standardGaussianExpectation (fun z => Real.cosh (x₂ + (-a) * z)) := by
            apply congrArg standardGaussianExpectation
            funext z
            rw [hg_sq]
            congr 2
            ring
      _ = Real.exp ((-a) ^ 2 / 2) * Real.cosh x₂ :=
        flatness_standardGaussian_cosh x₂ (-a)
      _ = E₂ := by
        dsimp [E₂]
        ring_nf
  let A : ℝ := Real.sqrt E₁
  let B : ℝ := Real.sqrt E₂
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.sqrt_pos.2 hE₁pos
  have hBpos : 0 < B := by
    dsimp [B]
    exact Real.sqrt_pos.2 hE₂pos
  have hA_sq : A ^ 2 = E₁ := by
    dsimp [A]
    exact Real.sq_sqrt hE₁pos.le
  have hB_sq : B ^ 2 = E₂ := by
    dsimp [B]
    exact Real.sq_sqrt hE₂pos.le
  let I : ℝ := ∫ z, f z * g z ∂gaussianReal 0 1
  have hIpos : 0 < I := by
    dsimp [I]
    rw [integral_pos_iff_support_of_nonneg
      (fun z => mul_nonneg (hf0 z) (hg0 z)) hIint]
    have hsupp : Function.support (fun z => f z * g z) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact mul_ne_zero
        (by dsimp [f]; exact (Real.exp_pos _).ne')
        (by dsimp [g]; exact (Real.exp_pos _).ne')
    rw [hsupp]
    simp
  let D : ℝ → ℝ := fun z => B * f z - A * g z
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  have hBf :
      Integrable (fun z => B ^ 2 * f z ^ 2) (gaussianReal 0 1) :=
    hf_sq_int.const_mul (B ^ 2)
  have hcross :
      Integrable (fun z => (2 * A * B) * (f z * g z)) (gaussianReal 0 1) :=
    hIint.const_mul (2 * A * B)
  have hAg :
      Integrable (fun z => A ^ 2 * g z ^ 2) (gaussianReal 0 1) :=
    hg_sq_int.const_mul (A ^ 2)
  have hDsq_int :
      Integrable (fun z => D z ^ 2) (gaussianReal 0 1) := by
    have h := (hBf.sub hcross).add hAg
    exact h.congr (Filter.Eventually.of_forall fun z => by
      dsimp [D]
      ring)
  have hD1ne : D 1 ≠ 0 := by
    intro hD1
    have hlin : B * f 1 = A * g 1 := by
      dsimp [D] at hD1
      linarith
    have hsq := congrArg (fun t : ℝ => t ^ 2) hlin
    rw [mul_pow, mul_pow, hB_sq, hA_sq, hf_sq, hg_sq] at hsq
    have hsq' :
        E₂ * Real.cosh (x₁ + a) = E₁ * Real.cosh (x₂ - a) := by
      simpa [sub_eq_add_neg] using hsq
    have hfactor :
        Real.exp (a ^ 2 / 2) * (Real.cosh x₂ * Real.cosh (x₁ + a)) =
          Real.exp (a ^ 2 / 2) * (Real.cosh x₁ * Real.cosh (x₂ - a)) := by
      simpa [E₁, E₂, mul_assoc] using hsq'
    have hcosh :
        Real.cosh x₂ * Real.cosh (x₁ + a) =
          Real.cosh x₁ * Real.cosh (x₂ - a) := by
      exact mul_left_cancel₀ (Real.exp_ne_zero (a ^ 2 / 2)) hfactor
    have hhyper :
        Real.cosh x₂ * Real.cosh (x₁ + a) -
            Real.cosh x₁ * Real.cosh (x₂ - a) =
          Real.sinh (x₁ + x₂) * Real.sinh a := by
      rw [show x₂ - a = x₂ + (-a) by ring]
      simp_rw [Real.cosh_eq, Real.sinh_eq]
      rw [show -(x₁ + a) = -x₁ + (-a) by ring]
      rw [show -(x₂ + -a) = -x₂ + a by ring]
      rw [show -(x₁ + x₂) = -x₁ + (-x₂) by ring]
      simp_rw [Real.exp_add]
      ring
    have hprod : Real.sinh (x₁ + x₂) * Real.sinh a = 0 := by
      rw [← hhyper, hcosh]
      ring
    rcases mul_eq_zero.mp hprod with hsum | ha'
    · have hsum0 : x₁ + x₂ = 0 := by
        apply Real.sinh_injective
        simpa using hsum
      apply hx
      linarith
    · have ha0 : a = 0 := by
        apply Real.sinh_injective
        simpa using ha'
      exact ha ha0
  have hDpos : 0 < ∫ z, D z ^ 2 ∂gaussianReal 0 1 := by
    letI : (gaussianReal 0 1).IsOpenPosMeasure :=
      (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
    exact integral_pos_of_integrable_nonneg_nonzero
      (μ := gaussianReal 0 1)
      (x := (1 : ℝ))
      (hDcont.pow 2)
      hDsq_int
      (fun z => sq_nonneg (D z))
      (pow_ne_zero 2 hD1ne)
  have hDformula :
      (∫ z, D z ^ 2 ∂gaussianReal 0 1) =
        B ^ 2 * E₁ - (2 * A * B) * I + A ^ 2 * E₂ := by
    let u : ℝ → ℝ := fun z => B ^ 2 * f z ^ 2
    let v : ℝ → ℝ := fun z => (2 * A * B) * (f z * g z)
    let w : ℝ → ℝ := fun z => A ^ 2 * g z ^ 2
    have hu : Integrable u (gaussianReal 0 1) := by
      simpa [u] using hBf
    have hv : Integrable v (gaussianReal 0 1) := by
      simpa [v] using hcross
    have hw : Integrable w (gaussianReal 0 1) := by
      simpa [w] using hAg
    calc
      (∫ z, D z ^ 2 ∂gaussianReal 0 1) =
          ∫ z, (u - v + w) z ∂gaussianReal 0 1 := by
              apply integral_congr_ae
              filter_upwards [] with z
              dsimp [D, u, v, w]
              ring
      _ = (∫ z, (u - v) z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 :=
            integral_add (hu.sub hv) hw
      _ = (∫ z, u z ∂gaussianReal 0 1) -
          (∫ z, v z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 := by
            have huv :
                (∫ z, (u - v) z ∂gaussianReal 0 1) =
                  (∫ z, u z ∂gaussianReal 0 1) -
                    ∫ z, v z ∂gaussianReal 0 1 := by
              simpa only [Pi.sub_apply] using integral_sub hu hv
            rw [huv]
      _ = B ^ 2 * (∫ z, f z ^ 2 ∂gaussianReal 0 1) -
          (2 * A * B) * (∫ z, f z * g z ∂gaussianReal 0 1) +
          A ^ 2 * (∫ z, g z ^ 2 ∂gaussianReal 0 1) := by
            dsimp [u, v, w]
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
      _ = B ^ 2 * E₁ - (2 * A * B) * I + A ^ 2 * E₂ := by
            rw [hfE, hgE]
  have hDformula' :
      (∫ z, D z ^ 2 ∂gaussianReal 0 1) =
        2 * (A * B) ^ 2 - 2 * (A * B) * I := by
    rw [hDformula, ← hA_sq, ← hB_sq]
    ring
  have hABpos : 0 < A * B := mul_pos hApos hBpos
  have hIlt : I < A * B := by
    have h := hDpos
    rw [hDformula'] at h
    nlinarith
  let C : ℝ :=
    a ^ 2 + Real.log (Real.cosh x₁) + Real.log (Real.cosh x₂)
  have hAB : A * B = Real.exp (C / 2) := by
    dsimp [A, B]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [Real.rpow_def_of_pos hE₁pos, Real.rpow_def_of_pos hE₂pos]
    rw [← Real.exp_add]
    congr 1
    dsimp [E₁, E₂, C]
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x₁).ne']
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x₂).ne']
    rw [Real.log_exp]
    ring
  have hIexp : I < Real.exp (C / 2) := by
    rw [← hAB]
    exact hIlt
  let J : ℝ :=
    standardGaussianExpectation (fun z =>
      Real.exp ((1 / 2 : ℝ) *
        gtDiagonalStep 1 b (gtTerminal 0)
          (x₁ + a * z) (x₂ + (-1) * a * z)))
  have hJ : J = Real.exp (b ^ 2 / 2) * I := by
    dsimp [J, I, standardGaussianExpectation]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [gtDiagonalStep_one_terminal, gtTerminal_zero]
    dsimp [f, g]
    rw [show
      (1 / 2 : ℝ) *
          (Real.log (Real.cosh (x₁ + a * z)) +
            Real.log (Real.cosh (x₂ + (-1) * a * z)) + b ^ 2) =
        b ^ 2 / 2 +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₁ + a * z)) +
          (1 / 2 : ℝ) * Real.log (Real.cosh (x₂ + (-1) * a * z)) by ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  have hJpos : 0 < J := by
    rw [hJ]
    exact mul_pos (Real.exp_pos _) hIpos
  have hJlt : J < Real.exp ((b ^ 2 + C) / 2) := by
    rw [hJ]
    calc
      Real.exp (b ^ 2 / 2) * I <
          Real.exp (b ^ 2 / 2) * Real.exp (C / 2) := by
            exact mul_lt_mul_of_pos_left hIexp (Real.exp_pos _)
      _ = Real.exp ((b ^ 2 + C) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hlog : Real.log J < (b ^ 2 + C) / 2 :=
    (Real.log_lt_iff_lt_exp hJpos).2 hJlt
  have hmain :
      2 * Real.log J <
        b ^ 2 + a ^ 2 + Real.log (Real.cosh x₁) + Real.log (Real.cosh x₂) := by
    dsimp [C] at hlog
    nlinarith
  simpa [gtRankOneStep, J] using hmain

private lemma flatness_negative_half_step_eq_iff
    (a b x₁ x₂ : ℝ) :
    gtRankOneStep (1 / 2) a (-1)
        (gtDiagonalStep 1 b (gtTerminal 0))
        x₁ x₂
      =
    b ^ 2 + a ^ 2
      + Real.log (Real.cosh x₁)
      + Real.log (Real.cosh x₂)
    ↔
    a = 0 ∨ x₁ = -x₂ := by
  constructor
  · intro heq
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    by_contra hx
    have hlt := flatness_negative_half_step_lt_of_nontrivial a b x₁ x₂ ha hx
    linarith
  · rintro (ha | hx)
    · subst a
      simp [gtRankOneStep, gtDiagonalStep_one_terminal, gtTerminal_zero,
        standardGaussianExpectation]
      ring
    · have hx₂ : x₂ = -x₁ := by
        linarith
      subst x₂
      let J : ℝ :=
        standardGaussianExpectation (fun z =>
          Real.exp ((1 / 2 : ℝ) *
            gtDiagonalStep 1 b (gtTerminal 0)
              (x₁ + a * z) (-x₁ + (-1) * a * z)))
      have hJ :
          J = Real.exp (b ^ 2 / 2) *
              (Real.exp (a ^ 2 / 2) * Real.cosh x₁) := by
        dsimp [J]
        calc
          standardGaussianExpectation (fun z =>
              Real.exp ((1 / 2 : ℝ) *
                gtDiagonalStep 1 b (gtTerminal 0)
                  (x₁ + a * z) (-x₁ + (-1) * a * z))) =
            standardGaussianExpectation (fun z =>
              Real.exp (b ^ 2 / 2) * Real.cosh (x₁ + a * z)) := by
                apply congrArg standardGaussianExpectation
                funext z
                rw [gtDiagonalStep_one_terminal, gtTerminal_zero]
                have hneg : -x₁ + (-1) * a * z = -(x₁ + a * z) := by
                  ring
                rw [hneg, Real.cosh_neg]
                rw [show
                  (1 / 2 : ℝ) *
                      (Real.log (Real.cosh (x₁ + a * z)) +
                        Real.log (Real.cosh (x₁ + a * z)) + b ^ 2) =
                    b ^ 2 / 2 + Real.log (Real.cosh (x₁ + a * z)) by ring]
                rw [Real.exp_add, Real.exp_log (Real.cosh_pos _)]
          _ = Real.exp (b ^ 2 / 2) *
              standardGaussianExpectation (fun z => Real.cosh (x₁ + a * z)) := by
                unfold standardGaussianExpectation
                rw [integral_const_mul]
          _ = Real.exp (b ^ 2 / 2) *
              (Real.exp (a ^ 2 / 2) * Real.cosh x₁) := by
                rw [flatness_standardGaussian_cosh]
      have hJpos : 0 < J := by
        rw [hJ]
        positivity
      have hmain :
          2 * Real.log J =
            b ^ 2 + a ^ 2 + Real.log (Real.cosh x₁) +
              Real.log (Real.cosh (-x₁)) := by
        rw [hJ]
        rw [Real.log_mul (Real.exp_ne_zero _)
          (mul_ne_zero (Real.exp_ne_zero _) (Real.cosh_pos x₁).ne')]
        rw [Real.log_exp]
        rw [Real.log_mul (Real.exp_ne_zero _) (Real.cosh_pos x₁).ne']
        rw [Real.log_exp, Real.cosh_neg]
        ring
      simpa [gtRankOneStep, J] using hmain

private lemma flatness_log_cosh_nonneg
    (x : ℝ) :
    0 ≤ Real.log (Real.cosh x) := by
  exact Real.log_nonneg (Real.one_le_cosh x)

private lemma flatness_log_cosh_le_abs
    (x : ℝ) :
    Real.log (Real.cosh x) ≤ |x| := by
  have hcosh :
      Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    have h₁ :
        Real.exp x ≤ Real.exp |x| :=
      Real.exp_le_exp.mpr (le_abs_self x)
    have h₂ :
        Real.exp (-x) ≤ Real.exp |x| :=
      Real.exp_le_exp.mpr (neg_le_abs x)
    linarith
  exact
    (Real.log_le_iff_le_exp (Real.cosh_pos x)).2
      hcosh

private lemma flatness_integrable_log_cosh_affine_gaussian
    (h a m : ℝ) (v : ℝ≥0) :
    Integrable
      (fun z : ℝ =>
        Real.log (Real.cosh (h + a * z)))
      (gaussianReal m v) := by
  have hz :
      Integrable
        (fun z : ℝ => |z|)
        (gaussianReal m v) :=
    (GTFrame.expMoments_gaussianReal m v).integrable_abs
  have hdom :
      Integrable
        (fun z : ℝ => |h| + |a| * |z|)
        (gaussianReal m v) :=
    (integrable_const |h|).add
      (hz.const_mul |a|)
  have hc :
      Continuous
        (fun z : ℝ =>
          Real.log (Real.cosh (h + a * z))) := by
    have hcosh :
        Continuous
          (fun z : ℝ =>
            Real.cosh (h + a * z)) := by
      fun_prop
    exact hcosh.log
      (fun z =>
        (Real.cosh_pos (h + a * z)).ne')
  refine hdom.mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with z
  have hbound :
      Real.log (Real.cosh (h + a * z))
        ≤ |h| + |a| * |z| := by
    calc
      Real.log (Real.cosh (h + a * z))
          ≤ |h + a * z| :=
        flatness_log_cosh_le_abs _
      _ ≤ |h| + |a * z| :=
        abs_add_le _ _
      _ = |h| + |a| * |z| := by
        rw [abs_mul]
  have hright :
      0 ≤ |h| + |a| * |z| := by
    positivity
  simpa [
      Real.norm_eq_abs,
      abs_of_nonneg
        (flatness_log_cosh_nonneg (h + a * z)),
      abs_of_nonneg hright] using hbound

private lemma flatness_integrable_log_cosh_two_affine
    (h a b : ℝ) :
    Integrable
      (fun p : ℝ × ℝ =>
        Real.log (Real.cosh (h + a * p.1 + b * p.2)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hz : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (GTFrame.expMoments_gaussianReal 0 1).integrable_abs
  have hz₁ :
      Integrable (fun p : ℝ × ℝ => |p.1|)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hz.comp_fst (gaussianReal 0 1)
  have hz₂ :
      Integrable (fun p : ℝ × ℝ => |p.2|)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hz.comp_snd (gaussianReal 0 1)
  have hdom :
      Integrable
        (fun p : ℝ × ℝ =>
          (|h| + |a| * |p.1|) + |b| * |p.2|)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ((integrable_const |h|).add (hz₁.const_mul |a|)).add
      (hz₂.const_mul |b|)
  have hc :
      Continuous
        (fun p : ℝ × ℝ =>
          Real.log (Real.cosh (h + a * p.1 + b * p.2))) := by
    have hcosh :
        Continuous
          (fun p : ℝ × ℝ => Real.cosh (h + a * p.1 + b * p.2)) := by
      fun_prop
    exact hcosh.log (fun p => (Real.cosh_pos _).ne')
  refine hdom.mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with p
  have hbound :
      Real.log (Real.cosh (h + a * p.1 + b * p.2)) ≤
        (|h| + |a| * |p.1|) + |b| * |p.2| := by
    calc
      Real.log (Real.cosh (h + a * p.1 + b * p.2)) ≤
          |h + a * p.1 + b * p.2| := flatness_log_cosh_le_abs _
      _ ≤ |h + a * p.1| + |b * p.2| := abs_add_le _ _
      _ ≤ (|h| + |a * p.1|) + |b * p.2| := by
        gcongr
        exact abs_add_le _ _
      _ = (|h| + |a| * |p.1|) + |b| * |p.2| := by
        rw [abs_mul, abs_mul]
  have hright : 0 ≤ (|h| + |a| * |p.1|) + |b| * |p.2| := by
    positivity
  simpa [Real.norm_eq_abs,
      abs_of_nonneg (flatness_log_cosh_nonneg _),
      abs_of_nonneg hright] using hbound

private lemma flatness_gaussian_convolution_log_cosh_add_const
    (h k a b c : ℝ)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + b * y)) + k
      ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
    ∫ z, Real.log (Real.cosh (h + c * z)) + k ∂gaussianReal 0 1 := by
  let va : ℝ≥0 := NNReal.mk (a ^ 2) (sq_nonneg a) * 1
  let vb : ℝ≥0 := NNReal.mk (b ^ 2) (sq_nonneg b) * 1
  let vc : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg c) * 1
  have hma : Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1) =
      gaussianReal 0 va := by
    simpa [va] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) a)
  have hmb : Measure.map (fun x : ℝ => b * x) (gaussianReal 0 1) =
      gaussianReal 0 vb := by
    simpa [vb] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) b)
  have hmc : Measure.map (fun x : ℝ => c * x) (gaussianReal 0 1) =
      gaussianReal 0 vc := by
    simpa [vc] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) c)
  have hv : va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]
  have hf :
      Integrable (fun z : ℝ => Real.log (Real.cosh (h + z)) + k)
        (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    simpa using
      (flatness_integrable_log_cosh_affine_gaussian h 1 0 vc).add
        (integrable_const k)
  have hprod :
      Integrable (fun p : ℝ × ℝ => Real.log (Real.cosh (h + (p.1 + p.2))) + k)
        ((gaussianReal 0 va).prod (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hf
    exact (integrable_map_measure hf.1 (by fun_prop)).mp hf
  have houter :
      AEStronglyMeasurable
        (fun x : ℝ => ∫ y, Real.log (Real.cosh (h + (x + y))) + k
          ∂gaussianReal 0 vb)
        (gaussianReal 0 va) := hprod.integral_prod_left.1
  have hinner (x : ℝ) :
      (∫ y, Real.log (Real.cosh (h + a * x + b * y)) + k ∂gaussianReal 0 1) =
        ∫ y, Real.log (Real.cosh (h + a * x + y)) + k ∂gaussianReal 0 vb := by
    have hm : AEStronglyMeasurable
        (fun y : ℝ => Real.log (Real.cosh (h + a * x + y)) + k)
        (Measure.map (fun y : ℝ => b * y) (gaussianReal 0 1)) := by
      apply (Continuous.add _ continuous_const).aestronglyMeasurable
      apply Continuous.log
      · fun_prop
      · intro y
        exact (Real.cosh_pos _).ne'
    rw [← hmb, integral_map (by fun_prop) hm]
  have houter_map :
      (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + y)) + k
        ∂gaussianReal 0 vb ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.log (Real.cosh (h + x + y)) + k
          ∂gaussianReal 0 vb ∂gaussianReal 0 va := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y, Real.log (Real.cosh (h + (x + y))) + k
          ∂gaussianReal 0 vb)
        (Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1)) := by
      simpa [hma] using houter
    rw [← hma]
    simpa only [add_assoc] using (integral_map (by fun_prop) hm).symm
  calc
    (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + b * y)) + k
      ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.log (Real.cosh (h + x + y)) + k
          ∂gaussianReal 0 vb ∂gaussianReal 0 va := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
            exact houter_map
    _ = ∫ z, Real.log (Real.cosh (h + z)) + k
          ∂(gaussianReal 0 va ∗ gaussianReal 0 vb) := by
            simpa only [add_assoc] using (integral_conv hf).symm
    _ = ∫ z, Real.log (Real.cosh (h + z)) + k ∂gaussianReal 0 vc := by
            rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    _ = ∫ z, Real.log (Real.cosh (h + c * z)) + k ∂gaussianReal 0 1 := by
            rw [← hmc, integral_map (by fun_prop)]
            apply (Continuous.add _ continuous_const).aestronglyMeasurable
            apply Continuous.log
            · fun_prop
            · intro z
              exact (Real.cosh_pos _).ne'

private lemma flatness_standardGaussian_log_cosh_neg_scale
    (y c : ℝ) :
    standardGaussianExpectation
        (fun z : ℝ => Real.log (Real.cosh (y + (-c) * z))) =
      standardGaussianExpectation
        (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
  unfold standardGaussianExpectation
  let φ : ℝ → ℝ := fun z => Real.log (Real.cosh (y + c * z))
  have hφcont : Continuous φ := by
    dsimp [φ]
    have hcosh : Continuous (fun z : ℝ => Real.cosh (y + c * z)) := by
      fun_prop
    exact hcosh.log (fun z => (Real.cosh_pos (y + c * z)).ne')
  have hmap :
      Measure.map (fun z : ℝ => -z) (gaussianReal 0 1) =
        gaussianReal 0 1 := by
    simpa using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hm :
      AEStronglyMeasurable φ
        (Measure.map (fun z : ℝ => -z) (gaussianReal 0 1)) := by
    rw [hmap]
    exact hφcont.aestronglyMeasurable
  calc
    (∫ z, Real.log (Real.cosh (y + (-c) * z)) ∂gaussianReal 0 1) =
        ∫ z, φ (-z) ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [φ]
          congr 2
          ring
    _ = ∫ z, φ z ∂(Measure.map (fun z : ℝ => -z) (gaussianReal 0 1)) := by
          exact (integral_map measurable_neg.aemeasurable hm).symm
    _ = ∫ z, φ z ∂gaussianReal 0 1 := by
          rw [hmap]

/--
The negative half-step, viewed as a dummy-parameter family, is a `GoodFam`.
This gives exactly the continuity and linear-growth integrability needed for
the subsequent mass-zero Gaussian average.
-/
private lemma flatness_negative_half_step_goodFam
    (a b : ℝ) :
    ∃ D : Unit → ℝ → ℝ × ℝ → ℝ,
      GTFrame.GoodFam
        (fun (_ : Unit) l (x : ℝ × ℝ) =>
          gtRankOneStep (1 / 2) a (-1)
            (gtDiagonalStep 1 b (gtTerminal l))
            x.1 x.2)
        D := by
  let F0 : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x =>
    gtDiagonalStep 1 b (gtTerminal l) x.1 x.2
  let D0 : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x =>
    GTFrame.fLbaseD l x
  have hbase := GTFrame.goodFam_fLbase (P := Unit)
  have hF0 : GTFrame.GoodFam F0 D0 := by
    refine
      { contF := ?_
        contD := ?_
        hasDeriv := ?_
        lipx := ?_
        bddD := ?_ }
    · have hc :
          Continuous (fun w : Unit × ℝ × (ℝ × ℝ) =>
            GTFrame.fLbase w.2.1 w.2.2 + b ^ 2) :=
        hbase.contF.add continuous_const
      simpa [F0, gtDiagonalStep_one_terminal] using hc
    · simpa [D0] using hbase.contD
    · intro p l x
      simpa [F0, D0, gtDiagonalStep_one_terminal] using
        (hbase.hasDeriv p l x).add_const (b ^ 2)
    · intro p l x y
      simpa [F0, gtDiagonalStep_one_terminal] using hbase.lipx p l x y
    · intro p l x
      simpa [D0] using hbase.bddD p l x
  let α : Unit → ℝ := fun _ => a
  let βdir : Unit → ℝ := fun _ => (-1) * a
  let F1 : Unit → ℝ → ℝ × ℝ → ℝ :=
    GTFrame.stepM (gaussianReal 0 1) (1 / 2) α βdir F0
  let D1 : Unit → ℝ → ℝ × ℝ → ℝ :=
    GTFrame.stepMD (gaussianReal 0 1) (1 / 2) α βdir F0 D0
  have hF1 : GTFrame.GoodFam F1 D1 := by
    exact
      GTFrame.stepM_good
        (GTFrame.expMoments_gaussianReal 0 1)
        hF0
        (by norm_num)
        (by fun_prop)
        (by fun_prop)
  let H : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x =>
    gtRankOneStep (1 / 2) a (-1)
      (gtDiagonalStep 1 b (gtTerminal l)) x.1 x.2
  have hHF : H = F1 := by
    funext p l x
    norm_num [H, F1, F0, α, βdir, GTFrame.stepM, gtRankOneStep,
      standardGaussianExpectation]
  refine ⟨D1, ?_⟩
  change GTFrame.GoodFam H D1
  rw [hHF]
  exact hF1

/--
Strictness survives the mass-zero rank-one step provided the common center
`y` is nonzero.

The pointwise half-step bound is nonnegative everywhere. At the Gaussian
point `z = 0` the two fields are `(y,y)`, so when `y ≠ 0` they are not
opposites and the previously proved half-step inequality is strict there.
Continuity then makes the Gaussian integral of the gap strictly positive.
-/
private lemma flatness_negative_zero_step_lt
    (a b c y : ℝ)
    (ha : a ≠ 0)
    (hy : y ≠ 0) :
    gtRankOneStep 0 c (-1)
        (gtRankOneStep (1 / 2) a (-1)
          (gtDiagonalStep 1 b (gtTerminal 0)))
        y y
      <
    b ^ 2 + a ^ 2 +
      2 * standardGaussianExpectation
        (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
  obtain ⟨Dhalf, hhalfGood⟩ := flatness_negative_half_step_goodFam a b
  let H : ℝ → ℝ := fun z =>
    gtRankOneStep (1 / 2) a (-1)
      (gtDiagonalStep 1 b (gtTerminal 0))
      (y + c * z) (y + (-c) * z)
  let U : ℝ → ℝ := fun z =>
    b ^ 2 + a ^ 2 +
      Real.log (Real.cosh (y + c * z)) +
      Real.log (Real.cosh (y + (-c) * z))
  have hHcont : Continuous H := by
    have h := hhalfGood.cont_shift () 0 c (-c) (y, y)
    simpa [H] using h
  have hHint : Integrable H (gaussianReal 0 1) := by
    have h :=
      hhalfGood.integrable_shift
        (GTFrame.expMoments_gaussianReal 0 1)
        () 0 c (-c) (y, y)
    simpa [H] using h
  have hlog₁ :
      Integrable (fun z : ℝ => Real.log (Real.cosh (y + c * z)))
        (gaussianReal 0 1) :=
    flatness_integrable_log_cosh_affine_gaussian
      y c 0 (1 : NNReal)
  have hlog₂ :
      Integrable (fun z : ℝ => Real.log (Real.cosh (y + (-c) * z)))
        (gaussianReal 0 1) :=
    flatness_integrable_log_cosh_affine_gaussian
      y (-c) 0 (1 : NNReal)
  have hUcont : Continuous U := by
    have hc₁ : Continuous (fun z : ℝ => Real.cosh (y + c * z)) := by
      fun_prop
    have hc₂ : Continuous (fun z : ℝ => Real.cosh (y + (-c) * z)) := by
      fun_prop
    have hl₁ :
        Continuous (fun z : ℝ => Real.log (Real.cosh (y + c * z))) :=
      hc₁.log (fun z => (Real.cosh_pos (y + c * z)).ne')
    have hl₂ :
        Continuous (fun z : ℝ => Real.log (Real.cosh (y + (-c) * z))) :=
      hc₂.log (fun z => (Real.cosh_pos (y + (-c) * z)).ne')
    dsimp [U]
    exact (continuous_const.add hl₁).add hl₂
  have hUint : Integrable U (gaussianReal 0 1) := by
    dsimp [U]
    exact ((integrable_const (b ^ 2 + a ^ 2)).add hlog₁).add hlog₂
  let G : ℝ → ℝ := fun z => U z - H z
  have hGcont : Continuous G := by
    dsimp [G]
    exact hUcont.sub hHcont
  have hGint : Integrable G (gaussianReal 0 1) := by
    dsimp [G]
    exact hUint.sub hHint
  have hGnonneg : ∀ z : ℝ, 0 ≤ G z := by
    intro z
    have hle :=
      flatness_negative_half_step_le
        a b (y + c * z) (y + (-c) * z)
    dsimp [G, U, H]
    linarith
  have hy_not_opposite : y ≠ -y := by
    intro h
    apply hy
    linarith
  have hstrict0 :=
    flatness_negative_half_step_lt_of_nontrivial a b y y ha hy_not_opposite
  have hG0pos : 0 < G 0 := by
    simpa [G, U, H] using (sub_pos.mpr hstrict0)
  have hG0ne : G 0 ≠ 0 := ne_of_gt hG0pos
  have hGpos : 0 < ∫ z, G z ∂gaussianReal 0 1 := by
    letI : (gaussianReal 0 1).IsOpenPosMeasure :=
      (gaussianReal_absolutelyContinuous' 0 (by norm_num)).isOpenPosMeasure
    exact
      integral_pos_of_integrable_nonneg_nonzero
        (μ := gaussianReal 0 1)
        (x := (0 : ℝ))
        hGcont
        hGint
        hGnonneg
        hG0ne
  have hGformula :
      (∫ z, G z ∂gaussianReal 0 1) =
        (∫ z, U z ∂gaussianReal 0 1) -
          (∫ z, H z ∂gaussianReal 0 1) := by
    dsimp [G]
    rw [integral_sub hUint hHint]
  have hHU :
      (∫ z, H z ∂gaussianReal 0 1) <
        ∫ z, U z ∂gaussianReal 0 1 := by
    rw [hGformula] at hGpos
    linarith
  have hsym := flatness_standardGaussian_log_cosh_neg_scale y c
  unfold standardGaussianExpectation at hsym
  have hUeval :
      (∫ z, U z ∂gaussianReal 0 1) =
        b ^ 2 + a ^ 2 +
          2 * standardGaussianExpectation
            (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
    unfold standardGaussianExpectation
    let u : ℝ → ℝ := fun _ => b ^ 2 + a ^ 2
    let v : ℝ → ℝ := fun z => Real.log (Real.cosh (y + c * z))
    let w : ℝ → ℝ := fun z => Real.log (Real.cosh (y + (-c) * z))
    have hu : Integrable u (gaussianReal 0 1) := by
      simp [u]
    have hv : Integrable v (gaussianReal 0 1) := by
      simpa [v] using hlog₁
    have hw : Integrable w (gaussianReal 0 1) := by
      simpa [w] using hlog₂
    have hU : U = u + v + w := by
      funext z
      dsimp [U, u, v, w]
    have huv :
        (∫ z, (u + v) z ∂gaussianReal 0 1) =
          (∫ z, u z ∂gaussianReal 0 1) +
            ∫ z, v z ∂gaussianReal 0 1 := by
      simpa only [Pi.add_apply] using integral_add hu hv
    calc
      (∫ z, U z ∂gaussianReal 0 1) =
          ∫ z, (u + v + w) z ∂gaussianReal 0 1 := by rw [hU]
      _ = (∫ z, (u + v) z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 := by
            simpa only [Pi.add_apply] using integral_add (hu.add hv) hw
      _ = (∫ z, u z ∂gaussianReal 0 1) +
          (∫ z, v z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 := by rw [huv]
      _ = b ^ 2 + a ^ 2 +
          2 * ∫ z, Real.log (Real.cosh (y + c * z)) ∂gaussianReal 0 1 := by
            dsimp [u, v, w]
            simp only [integral_const, probReal_univ, one_smul]
            rw [hsym]
            ring
  have hstep :
      gtRankOneStep 0 c (-1)
          (gtRankOneStep (1 / 2) a (-1)
            (gtDiagonalStep 1 b (gtTerminal 0))) y y =
        ∫ z, H z ∂gaussianReal 0 1 := by
    simp [gtRankOneStep, H, standardGaussianExpectation]
  rw [hstep]
  calc
    (∫ z, H z ∂gaussianReal 0 1) <
        ∫ z, U z ∂gaussianReal 0 1 := hHU
    _ = b ^ 2 + a ^ 2 +
        2 * standardGaussianExpectation
          (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := hUeval

private lemma flatness_negative_zero_step_goodFam
    (a b c : ℝ) :
    ∃ D : Unit → ℝ → ℝ × ℝ → ℝ,
      GTFrame.GoodFam
        (fun (_ : Unit) l (x : ℝ × ℝ) =>
          gtRankOneStep 0 c (-1)
            (gtRankOneStep (1 / 2) a (-1)
              (gtDiagonalStep 1 b (gtTerminal l)))
            x.1 x.2)
        D := by
  obtain ⟨Dhalf, hhalf⟩ := flatness_negative_half_step_goodFam a b
  let Fhalf : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x =>
    gtRankOneStep (1 / 2) a (-1)
      (gtDiagonalStep 1 b (gtTerminal l)) x.1 x.2
  let α : Unit → ℝ := fun _ => c
  let βdir : Unit → ℝ := fun _ => (-1) * c
  let F0 : Unit → ℝ → ℝ × ℝ → ℝ :=
    GTFrame.step0 (gaussianReal 0 1) α βdir Fhalf
  let D0 : Unit → ℝ → ℝ × ℝ → ℝ :=
    GTFrame.step0 (gaussianReal 0 1) α βdir Dhalf
  have hF0 : GTFrame.GoodFam F0 D0 := by
    exact GTFrame.step0_good
      (GTFrame.expMoments_gaussianReal 0 1)
      hhalf
      (by fun_prop)
      (by fun_prop)
  let H : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x =>
    gtRankOneStep 0 c (-1)
      (gtRankOneStep (1 / 2) a (-1)
        (gtDiagonalStep 1 b (gtTerminal l))) x.1 x.2
  have hHF : H = F0 := by
    funext p l x
    norm_num [H, F0, Fhalf, α, βdir, GTFrame.step0, gtRankOneStep,
      standardGaussianExpectation]
  refine ⟨D0, ?_⟩
  change GTFrame.GoodFam H D0
  rw [hHF]
  exact hF0

private lemma flatness_negative_zero_rhs_integrable
    (a b c y : ℝ) :
    Integrable
      (fun z : ℝ =>
        b ^ 2 + a ^ 2 +
          Real.log (Real.cosh (y + c * z)) +
          Real.log (Real.cosh (y + (-c) * z)))
      (gaussianReal 0 1) := by
  have h₁ :=
    flatness_integrable_log_cosh_affine_gaussian
      y c 0 (1 : NNReal)
  have h₂ :=
    flatness_integrable_log_cosh_affine_gaussian
      y (-c) 0 (1 : NNReal)
  exact ((integrable_const (b ^ 2 + a ^ 2)).add h₁).add h₂

private lemma flatness_negative_zero_rhs_integral
    (a b c y : ℝ) :
    (∫ z,
        b ^ 2 + a ^ 2 +
          Real.log (Real.cosh (y + c * z)) +
          Real.log (Real.cosh (y + (-c) * z))
      ∂gaussianReal 0 1) =
    b ^ 2 + a ^ 2 +
      2 * standardGaussianExpectation
        (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
  have h₁ :=
    flatness_integrable_log_cosh_affine_gaussian
      y c 0 (1 : NNReal)
  have h₂ :=
    flatness_integrable_log_cosh_affine_gaussian
      y (-c) 0 (1 : NNReal)
  have hsym :
      (∫ z, Real.log (Real.cosh (y + (-c) * z))
        ∂gaussianReal 0 1) =
      ∫ z, Real.log (Real.cosh (y + c * z))
        ∂gaussianReal 0 1 := by
    simpa [standardGaussianExpectation] using
      flatness_standardGaussian_log_cosh_neg_scale y c
  let u : ℝ → ℝ := fun _ => b ^ 2 + a ^ 2
  let v : ℝ → ℝ := fun z => Real.log (Real.cosh (y + c * z))
  let w : ℝ → ℝ := fun z => Real.log (Real.cosh (y + (-c) * z))
  have hsum :
      (fun z : ℝ =>
        b ^ 2 + a ^ 2 +
          Real.log (Real.cosh (y + c * z)) +
          Real.log (Real.cosh (y + (-c) * z))) = u + v + w := by
    funext z
    rfl
  have hu : Integrable u (gaussianReal 0 1) := by simp [u]
  have hv : Integrable v (gaussianReal 0 1) := by simpa [v] using h₁
  have hw : Integrable w (gaussianReal 0 1) := by simpa [w] using h₂
  have huv :
      (∫ z, (u + v) z ∂gaussianReal 0 1) =
        (∫ z, u z ∂gaussianReal 0 1) +
          ∫ z, v z ∂gaussianReal 0 1 := by
    simpa only [Pi.add_apply] using integral_add hu hv
  rw [hsum]
  calc
    (∫ z, (u + v + w) z ∂gaussianReal 0 1) =
        (∫ z, (u + v) z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 := by
            simpa only [Pi.add_apply] using integral_add (hu.add hv) hw
    _ = (∫ z, u z ∂gaussianReal 0 1) +
          (∫ z, v z ∂gaussianReal 0 1) +
          ∫ z, w z ∂gaussianReal 0 1 := by
            rw [huv]
    _ = b ^ 2 + a ^ 2 +
        2 * standardGaussianExpectation
          (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
            dsimp [u, v, w]
            simp only [integral_const, probReal_univ, one_smul]
            rw [hsym]
            unfold standardGaussianExpectation
            ring

private lemma flatness_negative_zero_step_le
    (a b c y : ℝ) :
    gtRankOneStep 0 c (-1)
        (gtRankOneStep (1 / 2) a (-1)
          (gtDiagonalStep 1 b (gtTerminal 0)))
        y y
      ≤
    b ^ 2 + a ^ 2 +
      2 * standardGaussianExpectation
        (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
  obtain ⟨Dhalf, hhalfGood⟩ := flatness_negative_half_step_goodFam a b
  let H : ℝ → ℝ := fun z =>
    gtRankOneStep (1 / 2) a (-1)
      (gtDiagonalStep 1 b (gtTerminal 0))
      (y + c * z) (y + (-c) * z)
  let U : ℝ → ℝ := fun z =>
    b ^ 2 + a ^ 2 +
      Real.log (Real.cosh (y + c * z)) +
      Real.log (Real.cosh (y + (-c) * z))
  have hHint : Integrable H (gaussianReal 0 1) := by
    have h :=
      hhalfGood.integrable_shift
        (GTFrame.expMoments_gaussianReal 0 1)
        () 0 c (-c) (y, y)
    simpa [H] using h
  have hUint : Integrable U (gaussianReal 0 1) := by
    simpa [U] using flatness_negative_zero_rhs_integrable a b c y
  have hpoint : ∀ z : ℝ, H z ≤ U z := by
    intro z
    have h := flatness_negative_half_step_le
      a b (y + c * z) (y + (-c) * z)
    simpa [H, U] using h
  have hInt :
      (∫ z, H z ∂gaussianReal 0 1) ≤
        ∫ z, U z ∂gaussianReal 0 1 :=
    integral_mono hHint hUint hpoint
  have hstep :
      gtRankOneStep 0 c (-1)
          (gtRankOneStep (1 / 2) a (-1)
            (gtDiagonalStep 1 b (gtTerminal 0))) y y =
        ∫ z, H z ∂gaussianReal 0 1 := by
    simp [gtRankOneStep, H, standardGaussianExpectation]
  rw [hstep]
  calc
    (∫ z, H z ∂gaussianReal 0 1) ≤
        ∫ z, U z ∂gaussianReal 0 1 := hInt
    _ = b ^ 2 + a ^ 2 +
        2 * standardGaussianExpectation
          (fun z : ℝ => Real.log (Real.cosh (y + c * z))) := by
            simpa [U] using flatness_negative_zero_rhs_integral a b c y

private lemma flatness_gtIncrementScale_sq
    {β s lower upper : ℝ}
    (hs : 0 ≤ s)
    (hlu : lower ≤ upper) :
    gtIncrementScale β s lower upper ^ 2 =
      s * β ^ 2 * (upper - lower) := by
  unfold gtIncrementScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hs,
    Real.sq_sqrt (sub_nonneg.mpr hlu)]
  ring

private lemma flatness_gtIncrementScale_ne_zero
    {β s lower upper : ℝ}
    (hβ : 0 < β)
    (hs : 0 < s)
    (hlu : lower < upper) :
    gtIncrementScale β s lower upper ≠ 0 := by
  unfold gtIncrementScale
  exact mul_ne_zero
    (mul_ne_zero hβ.ne' (Real.sqrt_pos.2 hs).ne')
    (Real.sqrt_pos.2 (sub_pos.mpr hlu)).ne'

private lemma flatness_large_negative_semigroup_zero_lt
    {β h q s v : ℝ}
    (hβ : 0 < β)
    (hh : 0 < h)
    (hq0 : 0 < q)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hs0 : 0 < s)
    (hv : v ∈ Icc (-1 : ℝ) (-q))
    (hvq : v < -q) :
    standardGaussianExpectation (fun z =>
      gtSemigroupSolution β q s 0 v 0
        (h + β * Real.sqrt ((1 - s) * q) * z)
        (h + β * Real.sqrt ((1 - s) * q) * z))
      <
    2 * standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
      s * β ^ 2 * (1 - q) := by
  let r : ℝ := |v|
  have hvneg : v < 0 := by linarith
  have hr_eq : r = -v := by
    dsimp [r]
    rw [abs_of_neg hvneg]
  have hqr : q < r := by
    rw [hr_eq]
    linarith
  have hr1 : r ≤ 1 := by
    rw [hr_eq]
    linarith [hv.1]
  have hr0 : 0 < r := lt_trans hq0 hqr
  have hqabs : q ≤ |v| := by simpa [r] using hqr.le
  have habs0 : ¬ |v| ≤ 0 := by simpa [r] using (not_le.mpr hr0)
  have hqzero : ¬ q ≤ (0 : ℝ) := not_le.mpr hq0
  have hsign : gtPathSign v = -1 := by
    simp [gtPathSign, not_le.mpr hvneg]
  let a : ℝ := gtIncrementScale β s q r
  let b : ℝ := gtIncrementScale β s r 1
  let c : ℝ := gtIncrementScale β s 0 q
  let d : ℝ := β * Real.sqrt ((1 - s) * q)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact flatness_gtIncrementScale_ne_zero hβ hs0 hqr
  have ha2 : a ^ 2 = s * β ^ 2 * (r - q) := by
    dsimp [a]
    exact flatness_gtIncrementScale_sq hs.1 hqr.le
  have hb2 : b ^ 2 = s * β ^ 2 * (1 - r) := by
    dsimp [b]
    exact flatness_gtIncrementScale_sq hs.1 hr1
  have hab2 : b ^ 2 + a ^ 2 = s * β ^ 2 * (1 - q) := by
    rw [hb2, ha2]
    ring
  have hc2 : c ^ 2 = s * β ^ 2 * q := by
    dsimp [c]
    simpa using
      (flatness_gtIncrementScale_sq
        (β := β) (s := s) (lower := 0) (upper := q) hs.1 hq0.le)
  have h1sq : 0 ≤ (1 - s) * q := by
    exact mul_nonneg (sub_nonneg.mpr hs.2) hq0.le
  have hd2 : d ^ 2 = (1 - s) * β ^ 2 * q := by
    dsimp [d]
    rw [mul_pow, Real.sq_sqrt h1sq]
    ring
  have hk2 : (β * Real.sqrt q) ^ 2 = d ^ 2 + c ^ 2 := by
    have hk : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
      rw [mul_pow, Real.sq_sqrt hq0.le]
    rw [hk, hd2, hc2]
    ring
  have hsemigroup (y : ℝ) :
      gtSemigroupSolution β q s 0 v 0 y y =
        gtRankOneStep 0 c (-1)
          (gtRankOneStep (1 / 2) a (-1)
            (gtDiagonalStep 1 b (gtTerminal 0))) y y := by
    simp [gtSemigroupSolution, hqabs, habs0, hqzero, hsign, a, b, c, r]
  let L : ℝ → ℝ := fun z =>
    gtRankOneStep 0 c (-1)
      (gtRankOneStep (1 / 2) a (-1)
        (gtDiagonalStep 1 b (gtTerminal 0)))
      (h + d * z) (h + d * z)
  let Q : ℝ → ℝ := fun z =>
    standardGaussianExpectation
      (fun w => Real.log (Real.cosh (h + d * z + c * w)))
  let R : ℝ → ℝ := fun z => b ^ 2 + a ^ 2 + 2 * Q z
  obtain ⟨Dzero, hzeroGood⟩ := flatness_negative_zero_step_goodFam a b c
  have hLint : Integrable L (gaussianReal 0 1) := by
    have h := hzeroGood.integrable_shift
      (GTFrame.expMoments_gaussianReal 0 1)
      () 0 d d (h, h)
    simpa [L] using h
  have hprod := flatness_integrable_log_cosh_two_affine h d c
  have hQint : Integrable Q (gaussianReal 0 1) := by
    have hinner := hprod.integral_prod_left
    simpa [Q, standardGaussianExpectation] using hinner
  have hRint : Integrable R (gaussianReal 0 1) := by
    dsimp [R]
    exact (integrable_const (b ^ 2 + a ^ 2)).add (hQint.const_mul 2)
  have hLR : ∀ z : ℝ, L z ≤ R z := by
    intro z
    have hle := flatness_negative_zero_step_le a b c (h + d * z)
    simpa [L, R, Q] using hle
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  have hyAE : ∀ᵐ z ∂gaussianReal 0 1, h + d * z ≠ 0 := by
    by_cases hd0 : d = 0
    · filter_upwards [] with z
      simp [hd0, hh.ne']
    · have hne := Measure.ae_ne (gaussianReal 0 1) (-h / d)
      filter_upwards [hne] with z hz
      intro hy
      apply hz
      apply (eq_div_iff hd0).2
      nlinarith [hy]
  have hLRstrict : ∀ᵐ z ∂gaussianReal 0 1, L z < R z := by
    filter_upwards [hyAE] with z hy
    have hlt := flatness_negative_zero_step_lt a b c (h + d * z) ha hy
    simpa [L, R, Q] using hlt
  have hIntLe :
      (∫ z, L z ∂gaussianReal 0 1) ≤ ∫ z, R z ∂gaussianReal 0 1 :=
    integral_mono hLint hRint hLR
  have hIntNe :
      (∫ z, L z ∂gaussianReal 0 1) ≠ ∫ z, R z ∂gaussianReal 0 1 := by
    intro heq
    have haeEq : L =ᵐ[gaussianReal 0 1] R :=
      (integral_eq_iff_of_ae_le hLint hRint
        (Filter.Eventually.of_forall hLR)).1 heq
    have hboth : ∀ᵐ z ∂gaussianReal 0 1, L z = R z ∧ L z < R z :=
      haeEq.and hLRstrict
    obtain ⟨z, hzEq, hzLt⟩ := Filter.nonempty_of_mem hboth
    exact (ne_of_lt hzLt) hzEq
  have hInt :
      (∫ z, L z ∂gaussianReal 0 1) < ∫ z, R z ∂gaussianReal 0 1 :=
    lt_of_le_of_ne hIntLe hIntNe
  have hconv :
      (∫ z, standardGaussianExpectation
          (fun w => Real.log (Real.cosh (h + d * z + c * w)))
        ∂gaussianReal 0 1) =
      standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) := by
    have hconv := flatness_gaussian_convolution_log_cosh_add_const
      h 0 d c (β * Real.sqrt q) hk2
    simpa [standardGaussianExpectation] using hconv
  have hReval :
      (∫ z, R z ∂gaussianReal 0 1) =
      2 * standardGaussianExpectation
          (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
        s * β ^ 2 * (1 - q) := by
    dsimp [R]
    rw [integral_add (integrable_const (b ^ 2 + a ^ 2)) (hQint.const_mul 2)]
    rw [integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rw [show
      (∫ z, Q z ∂gaussianReal 0 1) =
        standardGaussianExpectation
          (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) by
      simpa [Q] using hconv]
    rw [hab2]
    ring
  have hLeft :
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) =
        ∫ z, L z ∂gaussianReal 0 1 := by
    unfold standardGaussianExpectation
    apply integral_congr_ae
    filter_upwards [] with z
    have h := hsemigroup (h + d * z)
    simpa [L, d] using h
  rw [hLeft]
  calc
    (∫ z, L z ∂gaussianReal 0 1) < ∫ z, R z ∂gaussianReal 0 1 := hInt
    _ = 2 * standardGaussianExpectation
          (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
        s * β ^ 2 * (1 - q) := hReval

lemma flatness_gtFunctional_zero_lt_two_rsPathValue_large_negative
    {β h q s v : ℝ}
    (hβ : 0 < β)
    (hh : 0 < h)
    (hq : q = rsQ β h)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hs0 : 0 < s)
    (hv : v ∈ Icc (-1 : ℝ) (-q))
    (hvq : v < -q) :
    gtFunctional β h q s 0 v < 2 * rsPathValue β h q s := by
  have hq0 : 0 < q := by
    rw [hq]
    exact rsQ_pos hβ hh
  have hsemigroup :=
    flatness_large_negative_semigroup_zero_lt hβ hh hq0 hs hs0 hv hvq
  unfold gtFunctional
  unfold rsPathValue
  unfold gtCorrection
  simp only [zero_mul, sub_zero]
  nlinarith [hsemigroup]

end SpinGlass.AT
