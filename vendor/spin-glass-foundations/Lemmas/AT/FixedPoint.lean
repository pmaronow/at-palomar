module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Lemmas.GuerraTalagrand.LatalaGuerra

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

set_option autoImplicit false

namespace SpinGlass.AT

/-!
# The replica-symmetric fixed point for the two-spin SK model

This file records existence, uniqueness, and parameter continuity for the
solution of

`q = E[tanh (h + β * sqrt q * Z) ^ 2]`,

where `Z` is standard Gaussian.  All definitions and proofs in this file are
built directly from Mathlib.

The analytic inputs in this file are isolated as named lemmas.  In
particular, `continuous_rsFixedPointRHS` is the dominated-convergence step,
and `rsFixedPoint_unique` is the standard uniqueness theorem for a nonzero
external field.
-/

/-- Expectation with respect to a standard real Gaussian. -/
noncomputable def standardGaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1

/-- Replica-symmetric fixed-point equation. -/
def IsRSFixedPoint (β h q : ℝ) : Prop :=
  q = standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)

private theorem continuous_tanh : Continuous (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- The right-hand side of the replica-symmetric fixed-point equation. -/
noncomputable def rsFixedPointRHS (β h q : ℝ) : ℝ :=
  standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)

/-- Canonical RS parameter, selected as the infimum of the interval-valued
fixed points. -/
noncomputable def rsQ (β h : ℝ) : ℝ :=
  sInf {q : ℝ | q ∈ Set.Icc (0 : ℝ) 1 ∧ IsRSFixedPoint β h q}

/-- Fourth moment at the canonical fixed point. -/
noncomputable def rsR (β h : ℝ) : ℝ :=
  standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt (rsQ β h) * z) ^ 4)

/-- The expectation of the fourth power of the hyperbolic secant. -/
noncomputable def rsA (β h : ℝ) : ℝ :=
  1 - 2 * rsQ β h + rsR β h

/-- The Almeida-Thouless parameter. -/
noncomputable def atParameter (β h : ℝ) : ℝ :=
  β ^ 2 * rsA β h

@[simp] theorem isRSFixedPoint_iff (β h q : ℝ) :
    IsRSFixedPoint β h q ↔ q = rsFixedPointRHS β h q := by
  rfl

/-- The fixed-point map takes values in `[0,1]`. -/
theorem rsFixedPointRHS_mem_Icc (β h q : ℝ) :
    rsFixedPointRHS β h q ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold rsFixedPointRHS standardGaussianExpectation
    exact integral_nonneg fun z => sq_nonneg _
  · unfold rsFixedPointRHS standardGaussianExpectation
    calc
      (∫ z, Real.tanh (h + β * Real.sqrt q * z) ^ 2
          ∂gaussianReal 0 1) ≤
          ∫ _z : ℝ, (1 : ℝ) ∂gaussianReal 0 1 := by
        apply integral_mono
        · apply Integrable.of_bound (C := 1)
          · exact ((continuous_tanh.comp (by fun_prop)).pow 2)
              |>.aestronglyMeasurable
          · filter_upwards [] with z
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact (Real.tanh_sq_lt_one _).le
        · exact integrable_const 1
        · intro z
          exact (Real.tanh_sq_lt_one _).le
      _ = 1 := by simp

/-- Joint continuity of the fixed-point map.  The integrand converges
pointwise and is bounded in absolute value by one, so this is an application
of dominated convergence for the standard Gaussian measure. -/
theorem continuous_rsFixedPointRHS :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      rsFixedPointRHS p.1.1 p.1.2 p.2) := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hmeas : ∀ᶠ p in 𝓝 p₀,
      AEStronglyMeasurable
        (fun z : ℝ => Real.tanh
          (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 2)
        (gaussianReal 0 1) := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ p in 𝓝 p₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 2‖ ≤
        (1 : ℝ) := by
    refine Filter.Eventually.of_forall fun p => ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Real.tanh_sq_lt_one _).le
  have hlim : ∀ᵐ z : ℝ ∂gaussianReal 0 1,
      Tendsto
        (fun p : (ℝ × ℝ) × ℝ =>
          Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 2)
        (𝓝 p₀)
        (𝓝 (Real.tanh
          (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 2)) := by
    refine ae_of_all _ fun z => ?_
    have harg : ContinuousAt
        (fun p : (ℝ × ℝ) × ℝ =>
          p.1.2 + p.1.1 * Real.sqrt p.2 * z) p₀ := by
      fun_prop
    exact ((ContinuousAt.comp (x := p₀)
      (f := fun p : (ℝ × ℝ) × ℝ =>
        p.1.2 + p.1.1 * Real.sqrt p.2 * z)
      (g := Real.tanh) continuous_tanh.continuousAt harg).pow 2).tendsto
  have htend := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 1) (l := 𝓝 p₀)
    (F := fun p : (ℝ × ℝ) × ℝ => fun z : ℝ =>
      Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 2)
    (f := fun z : ℝ => Real.tanh
      (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 2)
    (bound := fun _ : ℝ => (1 : ℝ)) hmeas hbound
      (integrable_const 1) hlim
  change Tendsto
    (fun p : (ℝ × ℝ) × ℝ => ∫ z,
      Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 2
        ∂gaussianReal 0 1)
    (𝓝 p₀)
    (𝓝 (∫ z, Real.tanh
      (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 2
        ∂gaussianReal 0 1))
  exact htend

/-- Fixed-point equations are preserved under simultaneous limits of all
three parameters. -/
theorem isRSFixedPoint_of_tendsto
    {βn hn qn : ℕ → ℝ} {β h q : ℝ}
    (hβ : Tendsto βn atTop (𝓝 β))
    (hh : Tendsto hn atTop (𝓝 h))
    (hq : Tendsto qn atTop (𝓝 q))
    (hfixed : ∀ n, IsRSFixedPoint (βn n) (hn n) (qn n)) :
    IsRSFixedPoint β h q := by
  have hparams : Tendsto
      (fun n => ((βn n, hn n), qn n)) atTop (𝓝 ((β, h), q)) :=
    (hβ.prodMk_nhds hh).prodMk_nhds hq
  have hrhs : Tendsto
      (fun n => rsFixedPointRHS (βn n) (hn n) (qn n)) atTop
      (𝓝 (rsFixedPointRHS β h q)) := by
    simpa [Function.comp_def] using
      continuous_rsFixedPointRHS.continuousAt.tendsto.comp hparams
  rw [isRSFixedPoint_iff]
  exact tendsto_nhds_unique hq
    (hrhs.congr' (Filter.Eventually.of_forall fun n => (hfixed n).symm))

private theorem continuous_rsFixedPointRHS_q (β h : ℝ) :
    Continuous (fun q => rsFixedPointRHS β h q) := by
  have hinner : Continuous (fun q : ℝ => ((β, h), q)) := by
    fun_prop
  simpa [Function.comp_def] using continuous_rsFixedPointRHS.comp hinner

/-- Existence of a solution in `[0,1]`.  Continuity and interval invariance
give this by the intermediate value theorem. -/
theorem rsFixedPoint_exists (β h : ℝ) :
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ IsRSFixedPoint β h q := by
  obtain ⟨q, hq, hfix⟩ := exists_mem_Icc_isFixedPt
    (continuous_rsFixedPointRHS_q β h).continuousOn (by norm_num)
    (rsFixedPointRHS_mem_Icc β h 0).1
    (rsFixedPointRHS_mem_Icc β h 1).2
  exact ⟨q, hq, by simpa [isRSFixedPoint_iff] using hfix.symm⟩

/-- The canonical selection lies in `[0,1]`. -/
theorem rsQ_mem_Icc (β h : ℝ) : rsQ β h ∈ Set.Icc (0 : ℝ) 1 := by
  let S := {q : ℝ | q ∈ Set.Icc (0 : ℝ) 1 ∧ IsRSFixedPoint β h q}
  have hclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_Icc.inter
      (isClosed_eq continuous_id (continuous_rsFixedPointRHS_q β h))
  have hnonempty : S.Nonempty := by
    obtain ⟨q, hq, hfixed⟩ := rsFixedPoint_exists β h
    exact ⟨q, hq, hfixed⟩
  have hbdd : BddBelow S := ⟨0, fun q hq => hq.1.1⟩
  exact (hclosed.csInf_mem hnonempty hbdd).1

/-- Standard uniqueness theorem for the two-spin SK fixed-point equation in
a nonzero external field. -/
theorem rsFixedPoint_unique {β h q₁ q₂ : ℝ} (hh : 0 < h)
    (hq₁ : q₁ ∈ Set.Icc (0 : ℝ) 1) (hfixed₁ : IsRSFixedPoint β h q₁)
    (hq₂ : q₂ ∈ Set.Icc (0 : ℝ) 1) (hfixed₂ : IsRSFixedPoint β h q₂) :
    q₁ = q₂ := by
  by_cases hβ : β = 0
  · subst β
    simp [IsRSFixedPoint, standardGaussianExpectation] at hfixed₁ hfixed₂
    exact hfixed₁.trans hfixed₂.symm
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hq₁pos : 0 < q₁ := by
    by_contra hnot
    have hq₁zero : q₁ = 0 := le_antisymm (le_of_not_gt hnot) hq₁.1
    subst q₁
    simp [IsRSFixedPoint, standardGaussianExpectation] at hfixed₁
    have ht : Real.tanh h ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero (Real.sinh_ne_zero.mpr hh.ne') (Real.cosh_pos h).ne'
    exact ht (sq_eq_zero_iff.mp hfixed₁.symm)
  have hq₂pos : 0 < q₂ := by
    by_contra hnot
    have hq₂zero : q₂ = 0 := le_antisymm (le_of_not_gt hnot) hq₂.1
    subst q₂
    simp [IsRSFixedPoint, standardGaussianExpectation] at hfixed₂
    have ht : Real.tanh h ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero (Real.sinh_ne_zero.mpr hh.ne') (Real.cosh_pos h).ne'
    exact ht (sq_eq_zero_iff.mp hfixed₂.symm)
  have hsqrt₁ : Real.sqrt (β ^ 2 * q₁) = |β| * Real.sqrt q₁ := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have hsqrt₂ : Real.sqrt (β ^ 2 * q₂) = |β| * Real.sqrt q₂ := by
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have heven (q : ℝ) :
      (∫ z, Real.tanh (h + |β| * Real.sqrt q * z) ^ 2 ∂gaussianReal 0 1) =
      ∫ z, Real.tanh (h + β * Real.sqrt q * z) ^ 2 ∂gaussianReal 0 1 := by
    rcases le_total 0 β with hβ0 | hβ0
    · rw [abs_of_nonneg hβ0]
    · rw [abs_of_nonpos hβ0]
      have hcomp := standardGaussian_integral_comp_neg
        (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)
        ((continuous_tanh.comp (by fun_prop)).pow 2)
      simpa only [neg_mul, neg_mul_neg, mul_neg, neg_neg] using hcomp
  have hratio₁ : latalaGuerraRatio h (β ^ 2 * q₁) = 1 / β ^ 2 := by
    have hfp : (∫ z, Real.tanh (h + β * Real.sqrt q₁ * z) ^ 2
        ∂gaussianReal 0 1) = q₁ := by
      simpa [IsRSFixedPoint, standardGaussianExpectation] using hfixed₁.symm
    unfold latalaGuerraRatio latalaGuerraNumerator
    rw [hsqrt₁, heven q₁, hfp]
    field_simp [hβsq.ne', hq₁pos.ne']
  have hratio₂ : latalaGuerraRatio h (β ^ 2 * q₂) = 1 / β ^ 2 := by
    have hfp : (∫ z, Real.tanh (h + β * Real.sqrt q₂ * z) ^ 2
        ∂gaussianReal 0 1) = q₂ := by
      simpa [IsRSFixedPoint, standardGaussianExpectation] using hfixed₂.symm
    unfold latalaGuerraRatio latalaGuerraNumerator
    rw [hsqrt₂, heven q₂, hfp]
    field_simp [hβsq.ne', hq₂pos.ne']
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcontra := latalaGuerraRatio_strictAnti hh
      (mul_pos hβsq hq₁pos) (mul_pos hβsq hq₂pos)
      (mul_lt_mul_of_pos_left hlt hβsq)
    rw [hratio₁, hratio₂] at hcontra
    exact hcontra.false
  · have hcontra := latalaGuerraRatio_strictAnti hh
      (mul_pos hβsq hq₂pos) (mul_pos hβsq hq₁pos)
      (mul_lt_mul_of_pos_left hgt hβsq)
    rw [hratio₂, hratio₁] at hcontra
    exact hcontra.false

/-- For positive external field, the two-spin SK fixed-point equation has
exactly one solution in `[0,1]`. -/
theorem existsUnique_rsFixedPoint (β : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃! q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ IsRSFixedPoint β h q := by
  obtain ⟨q, hq, hfixed⟩ := rsFixedPoint_exists β h
  refine ⟨q, ⟨hq, hfixed⟩, ?_⟩
  intro q' hq'
  exact rsFixedPoint_unique hh hq'.1 hq'.2 hq hfixed

/-- The canonical infimum selection is a fixed point. -/
theorem rsQ_fixedPoint (β h : ℝ) : IsRSFixedPoint β h (rsQ β h) := by
  let S := {q : ℝ | q ∈ Set.Icc (0 : ℝ) 1 ∧ IsRSFixedPoint β h q}
  have hclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_Icc.inter
      (isClosed_eq continuous_id (continuous_rsFixedPointRHS_q β h))
  have hnonempty : S.Nonempty := by
    obtain ⟨q, hq, hfixed⟩ := rsFixedPoint_exists β h
    exact ⟨q, hq, hfixed⟩
  have hbdd : BddBelow S := ⟨0, fun q hq => hq.1.1⟩
  exact (hclosed.csInf_mem hnonempty hbdd).2

/-- The canonical parameter `rsQ` satisfies the fixed-point equation whenever
the external field is positive. -/
theorem rsQ_fixedPoint_of_pos_field {β h : ℝ} (_hh : 0 < h) :
    IsRSFixedPoint β h (rsQ β h) :=
  rsQ_fixedPoint β h

/-- The fixed-point equation written directly for the canonical solution. -/
theorem rsQ_eq_gaussian_tanh_sq {β h : ℝ} (hh : 0 < h) :
    rsQ β h = standardGaussianExpectation
      (fun z => Real.tanh (h + β * Real.sqrt (rsQ β h) * z) ^ 2) := by
  exact rsQ_fixedPoint_of_pos_field hh

/-- Positive external field forces the canonical fixed point to be positive. -/
theorem rsQ_pos {β h : ℝ} (_hβ : 0 < β) (hh : 0 < h) : 0 < rsQ β h := by
  have hqnonneg := (rsQ_mem_Icc β h).1
  apply lt_of_le_of_ne hqnonneg
  intro hqzero
  have hfp := rsQ_fixedPoint_of_pos_field ( β := β) hh
  rw [← hqzero] at hfp
  simp [IsRSFixedPoint, standardGaussianExpectation] at hfp
  have htanh : 0 < Real.tanh h := by
    rw [Real.tanh_eq]
    exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith)))
      (add_pos (Real.exp_pos h) (Real.exp_pos (-h)))
  nlinarith

/-- The canonical fixed point is strictly less than one at positive external
field. -/
theorem rsQ_lt_one {β h : ℝ} (_hβ : 0 < β) (hh : 0 < h) :
    rsQ β h < 1 := by
  have hqle := (rsQ_mem_Icc β h).2
  apply lt_of_le_of_ne hqle
  intro hqone
  have hfp := rsQ_fixedPoint_of_pos_field (β := β) hh
  rw [hqone] at hfp
  let X : ℝ → ℝ := fun z => h + β * z
  let g : ℝ → ℝ := fun z => 1 - Real.tanh (X z) ^ 2
  have hgcont : Continuous g := by
    dsimp [g, X]
    exact continuous_const.sub ((continuous_tanh.comp (by fun_prop)).pow 2)
  have hgnonneg : 0 ≤ g := fun z => by
    dsimp [g]
    exact sub_nonneg.mpr (Real.tanh_sq_lt_one _).le
  have hgint : Integrable g (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact hgcont.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hgnonneg z)]
      dsimp [g]
      nlinarith [sq_nonneg (Real.tanh (X z))]
  have hgpos : 0 < ∫ z, g z ∂gaussianReal 0 1 := by
    rw [integral_pos_iff_support_of_nonneg hgnonneg hgint]
    have hsupp : Function.support g = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (by
        dsimp [g]
        exact sub_pos.mpr (Real.tanh_sq_lt_one _))
    rw [hsupp]
    simp
  have htanhInt : Integrable (fun z => Real.tanh (X z) ^ 2)
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (Real.tanh_sq_lt_one _).le
  have hgzero : ∫ z, g z ∂gaussianReal 0 1 = 0 := by
    have htint : ∫ z, Real.tanh (X z) ^ 2 ∂gaussianReal 0 1 = 1 := by
      simpa [IsRSFixedPoint, standardGaussianExpectation, X] using hfp.symm
    rw [show g = fun z => 1 - Real.tanh (X z) ^ 2 by rfl,
      integral_sub (integrable_const 1) htanhInt, htint]
    norm_num
  linarith

/-- Any `[0,1]`-valued solution is the canonical parameter `rsQ`. -/
theorem eq_rsQ_of_isRSFixedPoint {β h q : ℝ} (hh : 0 < h)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hfixed : IsRSFixedPoint β h q) :
    q = rsQ β h := by
  exact rsFixedPoint_unique hh hq hfixed (rsQ_mem_Icc β h)
    (rsQ_fixedPoint_of_pos_field hh)

/-- Characterization of the unique interval-valued fixed point. -/
theorem isRSFixedPoint_iff_eq_rsQ {β h q : ℝ} (hh : 0 < h)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    IsRSFixedPoint β h q ↔ q = rsQ β h := by
  constructor
  · exact eq_rsQ_of_isRSFixedPoint hh hq
  · rintro rfl
    exact rsQ_fixedPoint_of_pos_field hh

/-- A convergent sequence of `[0,1]`-valued fixed points can only converge to
the canonical fixed point at the limiting positive-field parameters.  This
is the limit-identification step used in the compactness proof of continuity.
-/
theorem tendsto_fixedPoints_eq_rsQ
    {βn hn qn : ℕ → ℝ} {β h q : ℝ}
    (hβ : Tendsto βn atTop (𝓝 β))
    (hhn : Tendsto hn atTop (𝓝 h))
    (hq : Tendsto qn atTop (𝓝 q))
    (hqmem : ∀ n, qn n ∈ Set.Icc (0 : ℝ) 1)
    (hfixed : ∀ n, IsRSFixedPoint (βn n) (hn n) (qn n))
    (hh : 0 < h) :
    q = rsQ β h := by
  have hqclosed : q ∈ Set.Icc (0 : ℝ) 1 := by
    exact isClosed_Icc.mem_of_tendsto hq (Filter.Eventually.of_forall hqmem)
  exact eq_rsQ_of_isRSFixedPoint hh hqclosed
    (isRSFixedPoint_of_tendsto hβ hhn hq hfixed)

/-- Joint continuity of the canonical fixed point at every parameter pair
with positive external field.  The proof uses compactness of `[0,1]`, the
preceding limit-identification lemma, and uniqueness. -/
theorem continuousAt_rsQ {β h : ℝ} (hh : 0 < h) :
    ContinuousAt (fun p : ℝ × ℝ => rsQ p.1 p.2) (β, h) := by
  change Tendsto (fun p : ℝ × ℝ => rsQ p.1 p.2)
    (𝓝 (β, h)) (𝓝 (rsQ β h))
  rw [tendsto_nhds_iff_seq_tendsto]
  intro u hu
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  let x : ℕ → ℝ := fun n => rsQ (u (ns n)).1 (u (ns n)).2
  obtain ⟨q, _hqmem, φ, hφ, hφlim⟩ := isCompact_Icc.tendsto_subseq
    (x := x) (fun n => rsQ_mem_Icc _ _)
  have hpar : Tendsto (fun n => u (ns (φ n))) atTop (𝓝 (β, h)) :=
    hu.comp (hns.comp hφ.tendsto_atTop)
  have hparβ : Tendsto (fun n => (u (ns (φ n))).1) atTop (𝓝 β) :=
    continuous_fst.continuousAt.tendsto.comp hpar
  have hparh : Tendsto (fun n => (u (ns (φ n))).2) atTop (𝓝 h) :=
    continuous_snd.continuousAt.tendsto.comp hpar
  have hqeq : q = rsQ β h := tendsto_fixedPoints_eq_rsQ
    hparβ hparh hφlim
    (fun n => rsQ_mem_Icc _ _)
    (fun n => rsQ_fixedPoint _ _) hh
  refine ⟨φ, ?_⟩
  simpa [x, Function.comp_def, hqeq] using hφlim

/-- Joint continuity of `q(β,h)` on the positive-field parameter domain. -/
theorem continuousOn_rsQ_pos_field :
    ContinuousOn (fun p : ℝ × ℝ => rsQ p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact (continuousAt_rsQ hp).continuousWithinAt

/-- Continuity in inverse temperature for every fixed positive field. -/
theorem continuous_rsQ_in_beta (h : ℝ) (hh : 0 < h) :
    Continuous (fun β : ℝ => rsQ β h) := by
  refine continuous_iff_continuousAt.2 fun β => ?_
  have hinner : ContinuousAt (fun β : ℝ => (β, h)) β := by
    fun_prop
  change Tendsto (fun β : ℝ => rsQ β h) (𝓝 β) (𝓝 (rsQ β h))
  simpa [Function.comp_def] using
    (continuousAt_rsQ (β := β) hh).tendsto.comp hinner.tendsto

/-- Continuity in the external field on `(0,∞)` for every fixed inverse
temperature. -/
theorem continuousOn_rsQ_in_field (β : ℝ) :
    ContinuousOn (fun h : ℝ => rsQ β h) (Set.Ioi 0) := by
  intro h hh
  have hinner : ContinuousAt (fun h : ℝ => (β, h)) h := by
    fun_prop
  exact ContinuousAt.continuousWithinAt <| by
    change Tendsto (fun h : ℝ => rsQ β h) (𝓝 h) (𝓝 (rsQ β h))
    simpa [Function.comp_def] using
      (continuousAt_rsQ (β := β) hh).tendsto.comp hinner.tendsto

/-- Convenience form for obtaining continuity on any parameter set whose
external-field coordinate is positive. -/
theorem continuousOn_rsQ_of_pos_field {K : Set (ℝ × ℝ)}
    (hh : ∀ p ∈ K, 0 < p.2) :
    ContinuousOn (fun p : ℝ × ℝ => rsQ p.1 p.2) K := by
  intro p hp
  exact (continuousAt_rsQ (hh p hp)).continuousWithinAt

/-!
## The fourth moment and the strict AT parameter

The imported definitions `rsR` and `atParameter` represent, respectively,
the parameter `r` and the parameter `α`.  The next identities record their
Gaussian formulas, and the subsequent results establish their continuity and
the uniform consequences on a compact subset of the strict AT region.
-/

/-- The Gaussian fourth-moment map before substituting the canonical fixed
point. -/
noncomputable def rsFourthMomentRHS (β h q : ℝ) : ℝ :=
  standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 4)

/-- The parameter `r` is the fourth Gaussian moment evaluated at `q`. -/
theorem rsR_eq_gaussian_tanh_fourth (β h : ℝ) :
    rsR β h = standardGaussianExpectation
      (fun z => Real.tanh
        (h + β * Real.sqrt (rsQ β h) * z) ^ 4) := by
  rfl

/-- The algebraic formula `α = β² (1 - 2q + r)`. -/
theorem atParameter_eq_beta_sq_mul_one_sub_two_q_add_r (β h : ℝ) :
    atParameter β h = β ^ 2 * (1 - 2 * rsQ β h + rsR β h) := by
  rfl

/-- The algebraic moment `1 - 2q + r` is the Gaussian fourth moment of
`sech`. -/
theorem rsA_eq_gaussian_sech_fourth {β h : ℝ}
    (_hβ : 0 < β) (hh : 0 < h) :
    rsA β h = standardGaussianExpectation (fun z =>
      (Real.cosh (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4) := by
  have hq := rsQ_fixedPoint_of_pos_field (β := β) hh
  unfold IsRSFixedPoint at hq
  unfold standardGaussianExpectation at hq
  unfold rsA rsR standardGaussianExpectation
  let X : ℝ → ℝ := fun z => h + β * √(rsQ β h) * z
  have hInt2 : Integrable (fun z => Real.tanh (X z) ^ 2)
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (continuous_tanh.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  have hInt4 : Integrable (fun z => Real.tanh (X z) ^ 4)
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (continuous_tanh.comp (by fun_prop)).pow 4 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  have hIntConst : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
    integrable_const 1
  have hx : 1 - 2 * rsQ β h +
      (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1) =
      ∫ z, (Real.cosh (X z))⁻¹ ^ 4 ∂gaussianReal 0 1 := by
    calc
      _ = 1 - 2 * (∫ z, Real.tanh (X z) ^ 2 ∂gaussianReal 0 1) +
          (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1) := by
        simpa only [X] using congrArg
          (fun y => 1 - 2 * y +
            (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1)) hq
      _ = ∫ z, (1 - 2 * Real.tanh (X z) ^ 2 + Real.tanh (X z) ^ 4)
          ∂gaussianReal 0 1 := by
        calc
          _ = (∫ z, 1 - 2 * Real.tanh (X z) ^ 2 ∂gaussianReal 0 1) +
              (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1) := by
            rw [integral_sub hIntConst (hInt2.const_mul 2), integral_const_mul]
            simp
          _ = ∫ z, (1 - 2 * Real.tanh (X z) ^ 2) +
              Real.tanh (X z) ^ 4 ∂gaussianReal 0 1 := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add (hIntConst.sub (hInt2.const_mul 2)) hInt4).symm
      _ = _ := integral_congr_ae (ae_of_all _ fun z => by
        change 1 - 2 * Real.tanh (X z) ^ 2 + Real.tanh (X z) ^ 4 =
          (Real.cosh (X z))⁻¹ ^ 4
        rw [Real.tanh_eq_sinh_div_cosh]
        have hc : Real.cosh (X z) ≠ 0 := ne_of_gt (Real.cosh_pos (X z))
        rw [inv_pow]
        field_simp
        nlinarith [Real.cosh_sq (X z)])
  simpa only [X] using hx

/-- The formula `α = β² E[sech⁴(h + β √q Z)]`, with `sech x`
written as `(cosh x)⁻¹`. -/
theorem atParameter_eq_beta_sq_mul_gaussian_sech_fourth {β h : ℝ}
    (hβ : 0 < β) (hh : 0 < h) :
    atParameter β h = β ^ 2 * standardGaussianExpectation (fun z =>
      (Real.cosh (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4) := by
  rw [atParameter, rsA_eq_gaussian_sech_fourth hβ hh]

private theorem continuous_tanh_for_fourth_moment :
    Continuous (fun x : ℝ => Real.tanh x) := by
  simp_rw [Real.tanh_eq]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Joint continuity of the fourth-moment map. -/
theorem continuous_rsFourthMomentRHS :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      rsFourthMomentRHS p.1.1 p.1.2 p.2) := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hmeas : ∀ᶠ p in 𝓝 p₀,
      AEStronglyMeasurable
        (fun z : ℝ => Real.tanh
          (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 4)
        (gaussianReal 0 1) := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact ((continuous_tanh_for_fourth_moment.comp (by fun_prop)).pow 4)
      |>.aestronglyMeasurable
  have hbound : ∀ᶠ p in 𝓝 p₀, ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 4‖ ≤
        (1 : ℝ) := by
    refine Filter.Eventually.of_forall fun p => ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _)
      (le_of_lt (Real.abs_tanh_lt_one _))
  have hlim : ∀ᵐ z : ℝ ∂gaussianReal 0 1,
      Tendsto
        (fun p : (ℝ × ℝ) × ℝ =>
          Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 4)
        (𝓝 p₀)
        (𝓝 (Real.tanh
          (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 4)) := by
    refine ae_of_all _ fun z => ?_
    have harg : ContinuousAt
        (fun p : (ℝ × ℝ) × ℝ =>
          p.1.2 + p.1.1 * Real.sqrt p.2 * z) p₀ := by
      fun_prop
    exact ((ContinuousAt.comp (x := p₀)
      (f := fun p : (ℝ × ℝ) × ℝ =>
        p.1.2 + p.1.1 * Real.sqrt p.2 * z)
      (g := Real.tanh) continuous_tanh_for_fourth_moment.continuousAt
      harg).pow 4).tendsto
  have htend := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 1) (l := 𝓝 p₀)
    (F := fun p : (ℝ × ℝ) × ℝ => fun z : ℝ =>
      Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 4)
    (f := fun z : ℝ => Real.tanh
      (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 4)
    (bound := fun _ : ℝ => (1 : ℝ)) hmeas hbound
      (integrable_const 1) hlim
  change Tendsto
    (fun p : (ℝ × ℝ) × ℝ => ∫ z,
      Real.tanh (p.1.2 + p.1.1 * Real.sqrt p.2 * z) ^ 4
        ∂gaussianReal 0 1)
    (𝓝 p₀)
    (𝓝 (∫ z, Real.tanh
      (p₀.1.2 + p₀.1.1 * Real.sqrt p₀.2 * z) ^ 4
        ∂gaussianReal 0 1))
  exact htend

/-- Joint continuity of `r(β,h)` at positive external field. -/
theorem continuousAt_rsR {β h : ℝ} (hh : 0 < h) :
    ContinuousAt (fun p : ℝ × ℝ => rsR p.1 p.2) (β, h) := by
  have hinner : ContinuousAt
      (fun p : ℝ × ℝ => (p, rsQ p.1 p.2)) (β, h) :=
    continuousAt_id.prodMk (continuousAt_rsQ hh)
  have hcomp : ContinuousAt
      (fun p : ℝ × ℝ =>
        rsFourthMomentRHS p.1 p.2 (rsQ p.1 p.2)) (β, h) := by
    change Tendsto
      (fun p : ℝ × ℝ =>
        rsFourthMomentRHS p.1 p.2 (rsQ p.1 p.2))
      (𝓝 (β, h)) (𝓝 (rsFourthMomentRHS β h (rsQ β h)))
    simpa [Function.comp_def] using
      continuous_rsFourthMomentRHS.continuousAt.tendsto.comp hinner.tendsto
  simpa [Function.comp_def, rsR, rsFourthMomentRHS] using hcomp

/-- Continuity of `r(β,h)` on the positive-field parameter domain. -/
theorem continuousOn_rsR_pos_field :
    ContinuousOn (fun p : ℝ × ℝ => rsR p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact (continuousAt_rsR hp).continuousWithinAt

/-- Joint continuity of `1 - 2q + r` at positive external field. -/
theorem continuousAt_rsA {β h : ℝ} (hh : 0 < h) :
    ContinuousAt (fun p : ℝ × ℝ => rsA p.1 p.2) (β, h) := by
  have hq := continuousAt_rsQ (β := β) hh
  have hr := continuousAt_rsR (β := β) hh
  change ContinuousAt
    (fun p : ℝ × ℝ => 1 - 2 * rsQ p.1 p.2 + rsR p.1 p.2) (β, h)
  fun_prop

/-- Continuity of `1 - 2q + r` on the positive-field parameter domain. -/
theorem continuousOn_rsA_pos_field :
    ContinuousOn (fun p : ℝ × ℝ => rsA p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact (continuousAt_rsA hp).continuousWithinAt

/-- Joint continuity of the strict AT parameter `α` at positive external
field. -/
theorem continuousAt_atParameter {β h : ℝ} (hh : 0 < h) :
    ContinuousAt (fun p : ℝ × ℝ => atParameter p.1 p.2) (β, h) := by
  have ha := continuousAt_rsA (β := β) hh
  change ContinuousAt
    (fun p : ℝ × ℝ => p.1 ^ 2 * rsA p.1 p.2) (β, h)
  fun_prop

/-- Continuity of `α(β,h)` on the positive-field parameter domain. -/
theorem continuousOn_atParameter_pos_field :
    ContinuousOn (fun p : ℝ × ℝ => atParameter p.1 p.2)
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact (continuousAt_atParameter hp).continuousWithinAt

/-- The open parameter region with positive inverse temperature, positive
external field, and strict AT inequality. -/
def strictATRegion : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ atParameter p.1 p.2 < 1}

/-- The maps `q`, `r`, and `α` are continuous on every subset of the strict
AT region. -/
theorem continuousOn_rsParameters_of_subset_strictATRegion
    {K : Set (ℝ × ℝ)} (hKsub : K ⊆ strictATRegion) :
    ContinuousOn (fun p : ℝ × ℝ => rsQ p.1 p.2) K ∧
      ContinuousOn (fun p : ℝ × ℝ => rsR p.1 p.2) K ∧
      ContinuousOn (fun p : ℝ × ℝ => atParameter p.1 p.2) K := by
  have hh : ∀ p ∈ K, 0 < p.2 := fun p hp => (hKsub hp).2.1
  refine ⟨continuousOn_rsQ_of_pos_field hh, ?_, ?_⟩
  · intro p hp
    exact (continuousAt_rsR (hh p hp)).continuousWithinAt
  · intro p hp
    exact (continuousAt_atParameter (hh p hp)).continuousWithinAt

/-- On a nonempty compact subset of the strict AT region, `1 - α` has a
uniform positive lower bound. -/
theorem exists_uniform_at_gap_on_compact {K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKsub : K ⊆ strictATRegion) :
    ∃ δK : ℝ, 0 < δK ∧
      ∀ p ∈ K, δK ≤ 1 - atParameter p.1 p.2 := by
  have hcont :=
    (continuousOn_rsParameters_of_subset_strictATRegion hKsub).2.2
  obtain ⟨p₀, hp₀, hmin⟩ := hKcompact.exists_isMinOn hKne
    ((continuousOn_const : ContinuousOn
      (fun _ : ℝ × ℝ => (1 : ℝ)) K).sub hcont)
  refine ⟨1 - atParameter p₀.1 p₀.2, ?_, ?_⟩
  · exact sub_pos.mpr (hKsub hp₀).2.2
  · intro p hp
    exact hmin hp

/-- The infimum of the canonical fixed point over a parameter set. -/
noncomputable def rsQInfOn (K : Set (ℝ × ℝ)) : ℝ :=
  sInf ((fun p : ℝ × ℝ => rsQ p.1 p.2) '' K)

/-- The supremum of the canonical fixed point over a parameter set. -/
noncomputable def rsQSupOn (K : Set (ℝ × ℝ)) : ℝ :=
  sSup ((fun p : ℝ × ℝ => rsQ p.1 p.2) '' K)

/-- On a nonempty compact subset of the strict AT region, the infimum of `q`
is positive and its supremum is strictly less than one. -/
theorem compact_rsQ_range {K : Set (ℝ × ℝ)}
    (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKsub : K ⊆ strictATRegion) :
    0 < rsQInfOn K ∧ rsQInfOn K ≤ rsQSupOn K ∧ rsQSupOn K < 1 := by
  let f : ℝ × ℝ → ℝ := fun p => rsQ p.1 p.2
  have hcont : ContinuousOn f K :=
    (continuousOn_rsParameters_of_subset_strictATRegion hKsub).1
  obtain ⟨pmin, hpmin, hmin⟩ :=
    hKcompact.exists_isMinOn hKne hcont
  obtain ⟨pmax, hpmax, hmax⟩ :=
    hKcompact.exists_isMaxOn hKne hcont
  have hSne : (f '' K).Nonempty := hKne.image f
  have hSbelow : BddBelow (f '' K) :=
    ⟨0, by
      rintro _ ⟨p, _hp, rfl⟩
      exact (rsQ_mem_Icc p.1 p.2).1⟩
  have hSabove : BddAbove (f '' K) :=
    ⟨1, by
      rintro _ ⟨p, _hp, rfl⟩
      exact (rsQ_mem_Icc p.1 p.2).2⟩
  have hinf : rsQInfOn K = f pmin := by
    apply le_antisymm
    · exact csInf_le hSbelow ⟨pmin, hpmin, rfl⟩
    · apply le_csInf hSne
      rintro _ ⟨p, hp, rfl⟩
      exact hmin hp
  have hsup : rsQSupOn K = f pmax := by
    apply le_antisymm
    · apply csSup_le hSne
      rintro _ ⟨p, hp, rfl⟩
      exact hmax hp
    · exact le_csSup hSabove ⟨pmax, hpmax, rfl⟩
  rw [hinf, hsup]
  refine ⟨rsQ_pos (hKsub hpmin).1 (hKsub hpmin).2.1, ?_,
    rsQ_lt_one (hKsub hpmax).1 (hKsub hpmax).2.1⟩
  exact hmin hpmax

end SpinGlass.AT
