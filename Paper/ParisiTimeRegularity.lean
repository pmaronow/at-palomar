module

public import Paper.ParisiSpatialSmooth
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! # Bounded weak time derivatives at every spatial order

The CDF of a general probability measure may jump. Time derivatives are
therefore represented distributionally by the actual measurable PDE right
hand side, rather than asserted to be pointwise continuous.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff

namespace Paper

theorem parisiTestX_testT_commute (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) : parisiTestX (parisiTestT φ) = parisiTestT (parisiTestX φ) := by
  rw [parisiTestX_eq_fderiv _ (contDiff_parisiTestT φ hφ),
    parisiTestT_eq_fderiv _ (contDiff_parisiTestX φ hφ),
    parisiTestT_eq_fderiv φ hφ, parisiTestX_eq_fderiv φ hφ]
  funext p
  rw [fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hφ).2.differentiable (by simp) p)
      (differentiableAt_const _),
    fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hφ).2.differentiable (by simp) p)
      (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, map_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp)).eq (0, 1) (1, 0)

/-- A bounded measurable field multiplied by a genuine compact test is
integrable, so no distributional identity uses an undefined integral. -/
theorem integrable_boundedField_mul_compactTest (f φ : ℝ × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ p, ‖f p‖ ≤ M)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun p => f p * φ p) parisiSpaceTime := by
  have hi := (hφ.norm.integrable_of_hasCompactSupport hc.norm
    (μ := parisiSpaceTime)).const_mul M
  apply hi.mono' (hf.mul hφ.measurable).aestronglyMeasurable
  filter_upwards with p
  convert! mul_le_mul_of_nonneg_right (hb p) (norm_nonneg (φ p)) using 1
  simp only [Pi.mul_apply, norm_mul]

/-- Spatial integration by parts needs only measurable bounded fields and
their genuine section derivative; joint time continuity is unnecessary. -/
theorem integral_spatial_byParts_bounded (u v φ : ℝ × ℝ → ℝ)
    (hu : Measurable u) (hv : Measurable v) (M N : ℝ)
    (hub : ∀ p, ‖u p‖ ≤ M) (hvb : ∀ p, ‖v p‖ ≤ N)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      HasDerivAt (fun y => u (t, y)) (v (t, x)) x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, u p * parisiTestX φ p ∂parisiSpaceTime) =
      -(∫ p, v p * φ p ∂parisiSpaceTime) := by
  have hi := integrable_boundedField_mul_compactTest u (parisiTestX φ) hu M hub
    (continuous_parisiTestX φ hφ) (hasCompactSupport_parisiTestX φ hφ hc)
  have hj := integrable_boundedField_mul_compactTest v φ hv N hvb hφ.continuous hc
  unfold parisiSpaceTime at hi hj ⊢
  rw [integral_prod _ hi, integral_prod _ hj, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have huC : Continuous (fun x => u (t, x)) :=
    continuous_iff_continuousAt.mpr (fun x => (hd t ht x).continuousAt)
  have hxC : Continuous (fun x : ℝ => parisiTestX φ (t, x)) :=
    (continuous_parisiTestX φ hφ).comp (by fun_prop)
  have hφC : Continuous (fun x : ℝ => φ (t, x)) := hφ.continuous.comp (by fun_prop)
  have hi' : Integrable (fun x => u (t, x) * parisiTestX φ (t, x)) :=
    (huC.mul hxC).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section _ (hasCompactSupport_parisiTestX φ hφ hc) t).mul_left
  have hj' : Integrable (fun x => v (t, x) * φ (t, x)) := by
    apply (hφC.norm.integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section φ hc t).norm |>.const_mul N).mono'
    · have hvM : Measurable (fun x : ℝ => v (t, x)) := hv.comp (by fun_prop)
      exact (hvM.mul hφC.measurable).aestronglyMeasurable
    · filter_upwards with x
      convert! mul_le_mul_of_nonneg_right (hvb (t, x)) (norm_nonneg (φ (t, x))) using 1
      simp only [norm_mul]
  have hk' : Integrable (fun x => u (t, x) * φ (t, x)) :=
    (huC.mul (hφ.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (hasCompactSupport_spatial_section φ hc t).mul_left
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd t ht x) (fun x _ => hasDerivAt_parisiTestX φ hφ t x) hi' hj' hk'

private theorem contDiff_bcf_spatial_section {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ) (hv : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v)) (p : P) :
    ContDiff ℝ ∞ (fun x => v (p, x)) := by
  have h := (BoundedContinuousFunction.evalCLM ℝ (p, 0)).contDiff.comp hv
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    bcfTranslate_apply, zero_add] using h

private theorem hasDerivAt_bcfSpatialDerivative_section {P : Type*} [TopologicalSpace P]
    (v : (P × ℝ) →ᵇ ℝ) (hv : ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ v))
    (n : ℕ) (p : P) (x : ℝ) :
    HasDerivAt (fun y => bcfSpatialDerivative v n (p, y))
      (bcfSpatialDerivative v (n + 1) (p, x)) x := by
  simp_rw [bcfSpatialDerivative_apply v hv]
  rw [iteratedDeriv_succ]
  exact ((contDiff_bcf_spatial_section v hv p).differentiable_iteratedDeriv n
    (by exact_mod_cast (ENat.natCast_lt_top n)) x).hasDerivAt

theorem contDiff_bcfTranslate_parisiGradientSquare (β : ℝ) (μ : ParisiMeasure) :
    ContDiff ℝ ∞ (fun ξ => bcfTranslate ξ (parisiGradientBCF β μ * parisiGradientBCF β μ)) := by
  have h := (contDiff_bcfTranslate_parisiGradient β μ).mul
    (contDiff_bcfTranslate_parisiGradient β μ)
  convert! h using 1

/-- A full-plane representative of each spatial derivative. On the
physical strip it is exactly `∂x^j u`; off it the bounded derivatives are
extended by the already constructed clamping map. -/
noncomputable def parisiSpatialField (β : ℝ) (μ : ParisiMeasure) : ℕ → ℝ × ℝ → ℝ
  | 0 => parisiPotential β μ
  | n + 1 => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
      (bcfSpatialDerivative (parisiGradientBCF β μ) n)

noncomputable def parisiSquareSpatialField (β : ℝ) (μ : ParisiMeasure)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
    (bcfSpatialDerivative (parisiGradientBCF β μ * parisiGradientBCF β μ) n)

theorem continuous_parisiSpatialField (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    Continuous (parisiSpatialField β μ n) := by
  cases n with
  | zero => exact continuous_parisiPotential β μ
  | succ n => exact continuous_parisiSlabExtend (by norm_num) _

theorem continuous_parisiSquareSpatialField (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    Continuous (parisiSquareSpatialField β μ n) :=
  continuous_parisiSlabExtend (by norm_num) _

theorem parisiSpatialField_bounded (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ∃ M : ℝ, ∀ p, ‖parisiSpatialField β μ (n + 1) p‖ ≤ M :=
  ⟨‖bcfSpatialDerivative (parisiGradientBCF β μ) n‖,
    norm_parisiSlabExtend_le (by norm_num) _⟩

theorem parisiSquareSpatialField_bounded (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ∃ M : ℝ, ∀ p, ‖parisiSquareSpatialField β μ n p‖ ≤ M :=
  ⟨‖bcfSpatialDerivative (parisiGradientBCF β μ * parisiGradientBCF β μ) n‖,
    norm_parisiSlabExtend_le (by norm_num) _⟩

theorem parisiSpatialField_eq_iteratedDeriv (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiSpatialField β μ n (t, x) =
      iteratedDeriv n (fun y => parisiPotential β μ (t, y)) x := by
  cases n with
  | zero => rfl
  | succ n =>
    change bcfSpatialDerivative (parisiGradientBCF β μ) n
      (projIcc (0 : ℝ) 1 (by norm_num) t, x) = _
    rw [projIcc_of_mem _ ht]
    exact parisiSpatialDerivative_representation β μ
      (contDiff_bcfTranslate_parisiGradient β μ) n (⟨t, ht⟩, x)

theorem hasDerivAt_parisiSpatialField (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => parisiSpatialField β μ n (t, y))
      (parisiSpatialField β μ (n + 1) (t, x)) x := by
  cases n with
  | zero =>
    have heq : parisiSpatialField β μ 1 = parisiGradient β μ := by
      funext p
      simp only [parisiSpatialField, bcfSpatialDerivative, iteratedDeriv_zero,
        bcfTranslate_zero, parisiGradient]
    rw [heq]
    exact hasDerivAt_parisiPotential_spatial_all β μ t x ht
  | succ n =>
    exact hasDerivAt_bcfSpatialDerivative_section _
      (contDiff_bcfTranslate_parisiGradient β μ) n
      (projIcc (0 : ℝ) 1 (by norm_num) t) x

theorem hasDerivAt_parisiSquareSpatialField (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (t x : ℝ) :
    HasDerivAt (fun y => parisiSquareSpatialField β μ n (t, y))
      (parisiSquareSpatialField β μ (n + 1) (t, x)) x :=
  hasDerivAt_bcfSpatialDerivative_section _
    (contDiff_bcfTranslate_parisiGradientSquare β μ) n
    (projIcc (0 : ℝ) 1 (by norm_num) t) x

@[simp] theorem parisiSpatialField_one (β : ℝ) (μ : ParisiMeasure) :
    parisiSpatialField β μ 1 = parisiGradient β μ := by
  funext p
  simp only [parisiSpatialField, bcfSpatialDerivative, iteratedDeriv_zero,
    bcfTranslate_zero, parisiGradient]

@[simp] theorem parisiSquareSpatialField_zero (β : ℝ) (μ : ParisiMeasure) :
    parisiSquareSpatialField β μ 0 = fun p => parisiGradient β μ p ^ 2 := by
  funext p
  simp only [parisiSquareSpatialField, bcfSpatialDerivative, iteratedDeriv_zero,
    bcfTranslate_zero, parisiSlabExtend, parisiGradient,
    BoundedContinuousFunction.mul_apply, pow_two]

/-- The actual measurable right hand side of the differentiated PDE. -/
noncomputable def parisiTimeField (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (p : ℝ × ℝ) : ℝ :=
  -(β ^ 2 / 2) * (parisiSpatialField β μ (n + 2) p +
    parisiCDF μ p.1 * parisiSquareSpatialField β μ n p)

theorem measurable_parisiTimeField (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    Measurable (parisiTimeField β μ n) :=
  measurable_const.mul ((continuous_parisiSpatialField β μ (n + 2)).measurable.add
    (((parisiCDF_measurable μ).comp measurable_fst).mul
      (continuous_parisiSquareSpatialField β μ n).measurable))

theorem parisiTimeField_bounded (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ∃ M : ℝ, ∀ p, ‖parisiTimeField β μ n p‖ ≤ M := by
  obtain ⟨M, hM⟩ := parisiSpatialField_bounded β μ (n + 1)
  obtain ⟨N, hN⟩ := parisiSquareSpatialField_bounded β μ n
  refine ⟨β ^ 2 / 2 * (M + N), fun p => ?_⟩
  have hm : ‖parisiCDF μ p.1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ p.1)]
    exact parisiCDF_le_one μ p.1
  have hb : ‖parisiCDF μ p.1 * parisiSquareSpatialField β μ n p‖ ≤ N := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans (by simpa using hN p)
  rw [parisiTimeField, norm_mul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hM p) hb))
    (by positivity)

theorem hasDerivAt_parisiTimeField_spatial (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => parisiTimeField β μ n (t, y))
      (parisiTimeField β μ (n + 1) (t, x)) x := by
  have h := (hasDerivAt_parisiSpatialField β μ (n + 2) t x ht).add
    ((hasDerivAt_parisiSquareSpatialField β μ n t x).const_mul (parisiCDF μ t))
  convert! h.const_mul (-(β ^ 2 / 2)) using 1

/-- Distributional time derivative on the physical open strip. Tests,
integrability and the identity are explicit. -/
def IsParisiWeakTimeDerivative (u w : ℝ × ℝ → ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} →
    Integrable (fun p => u p * parisiTestT φ p + w p * φ p) parisiSpaceTime ∧
    (∫ p, u p * parisiTestT φ p + w p * φ p ∂parisiSpaceTime) = 0

private theorem integrable_continuousField_mul_test (u φ : ℝ × ℝ → ℝ)
    (hu : Continuous u) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun p => u p * φ p) parisiSpaceTime :=
  (hu.mul hφ).integrable_of_hasCompactSupport hc.mul_left

private theorem integral_spatial_byParts_continuous (u v φ : ℝ × ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      HasDerivAt (fun y => u (t, y)) (v (t, x)) x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1}) :
    (∫ p, u p * parisiTestX φ p ∂parisiSpaceTime) =
      -(∫ p, v p * φ p ∂parisiSpaceTime) := by
  have h := (isParisiWeakGradient_of_hasDerivAt u v hu hv hd φ hφ hc hs).2
  rw [integral_add
    (integrable_continuousField_mul_test u _ hu (continuous_parisiTestX φ hφ)
      (hasCompactSupport_parisiTestX φ hφ hc))
    (integrable_continuousField_mul_test v φ hv hφ.continuous hc)] at h
  linarith

theorem integral_parisiSpatialField_byParts (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1}) :
    (∫ p, parisiSpatialField β μ n p * parisiTestX φ p ∂parisiSpaceTime) =
      -(∫ p, parisiSpatialField β μ (n + 1) p * φ p ∂parisiSpaceTime) :=
  integral_spatial_byParts_continuous _ _ φ
    (continuous_parisiSpatialField β μ n) (continuous_parisiSpatialField β μ (n + 1))
    (fun t ht x => hasDerivAt_parisiSpatialField β μ n t x ht) hφ hc hs

theorem integral_parisiTimeField_spatial_byParts (β : ℝ) (μ : ParisiMeasure) (n : ℕ)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p, parisiTimeField β μ n p * parisiTestX φ p ∂parisiSpaceTime) =
      -(∫ p, parisiTimeField β μ (n + 1) p * φ p ∂parisiSpaceTime) := by
  obtain ⟨M, hM⟩ := parisiTimeField_bounded β μ n
  obtain ⟨N, hN⟩ := parisiTimeField_bounded β μ (n + 1)
  exact integral_spatial_byParts_bounded _ _ φ
    (measurable_parisiTimeField β μ n) (measurable_parisiTimeField β μ (n + 1))
    M N hM hN (fun t ht x => hasDerivAt_parisiTimeField_spatial β μ n t x ht) hφ hc

theorem isParisiWeakTimeDerivative_potential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    IsParisiWeakTimeDerivative (parisiPotential β μ) (parisiTimeField β μ 0) := by
  intro φ hφ hc hs
  obtain ⟨M, hM⟩ := parisiTimeField_bounded β μ 0
  have hiT := integrable_continuousField_mul_test _ _ (continuous_parisiPotential β μ)
    (continuous_parisiTestT φ hφ) (hasCompactSupport_parisiTestT φ hφ hc)
  have hiW := integrable_boundedField_mul_compactTest _ φ
    (measurable_parisiTimeField β μ 0) M hM hφ.continuous hc
  refine ⟨hiT.add hiW, ?_⟩
  have hspos : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1} := fun p hp => (hs hp).1
  have hboundary : (fun x => φ (1, x) * Real.log (Real.cosh x)) = fun _ => (0 : ℝ) := by
    funext x
    have hz : φ (1, x) = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hp
      exact (lt_irrefl (1 : ℝ)) (hs hp).2)
    rw [hz, zero_mul]
  have hP := ((parisiPotential_isWeakSolution β hβ μ).equation φ hφ hc hspos).2.2
  rw [hboundary, integral_zero, add_zero] at hP
  have hiXX := integrable_continuousField_mul_test _ _ (continuous_parisiPotential β μ)
    (continuous_parisiTestXX φ hφ) (hasCompactSupport_parisiTestXX φ hφ hc)
  have hiH := integrable_continuousField_mul_test _ φ
    (continuous_parisiSpatialField β μ 2) hφ.continuous hc
  have hsm : Measurable (fun p : ℝ × ℝ => parisiCDF μ p.1 * parisiGradient β μ p ^ 2) :=
    ((parisiCDF_measurable μ).comp measurable_fst).mul
      ((continuous_parisiGradient β μ).measurable.pow_const 2)
  have hsb : ∀ p : ℝ × ℝ, ‖parisiCDF μ p.1 * parisiGradient β μ p ^ 2‖ ≤ 1 := by
    intro p
    rw [norm_mul, norm_pow]
    have hm : ‖parisiCDF μ p.1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (parisiCDF_nonneg μ p.1)]
      exact parisiCDF_le_one μ p.1
    simpa using mul_le_mul hm
      (pow_le_pow_left₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ p) 2)
      (by positivity) zero_le_one
  have hiS := integrable_boundedField_mul_compactTest _ φ hsm 1 hsb hφ.continuous hc
  have hXX : (∫ p, parisiPotential β μ p * parisiTestXX φ p ∂parisiSpaceTime) =
      ∫ p, parisiSpatialField β μ 2 p * φ p ∂parisiSpaceTime := by
    have h1 := integral_parisiSpatialField_byParts β μ 0 (parisiTestX φ)
      (contDiff_parisiTestX φ hφ) (hasCompactSupport_parisiTestX φ hφ hc)
      ((tsupport_parisiTestX_subset φ hφ).trans hs)
    have h2 := integral_parisiSpatialField_byParts β μ 1 φ hφ hc hs
    change (∫ p, parisiPotential β μ p * parisiTestXX φ p ∂parisiSpaceTime) = _ at h1
    rw [h2, neg_neg] at h1
    exact h1
  have hPsplit : -(∫ p, parisiPotential β μ p * parisiTestT φ p ∂parisiSpaceTime) +
      β ^ 2 / 2 * ((∫ p, parisiPotential β μ p * parisiTestXX φ p ∂parisiSpaceTime) +
        (∫ p, (parisiCDF μ p.1 * parisiGradient β μ p ^ 2) * φ p ∂parisiSpaceTime)) = 0 := by
    have heq : (fun p => -parisiPotential β μ p * parisiTestT φ p + β ^ 2 / 2 *
        (parisiPotential β μ p * parisiTestXX φ p +
          parisiCDF μ p.1 * parisiGradient β μ p ^ 2 * φ p)) =
        (fun p => -(parisiPotential β μ p * parisiTestT φ p)) +
          (fun p => β ^ 2 / 2 * (parisiPotential β μ p * parisiTestXX φ p +
            (parisiCDF μ p.1 * parisiGradient β μ p ^ 2) * φ p)) := by
      funext p
      dsimp only [Pi.add_apply]
      ring
    rw [heq] at hP
    change (∫ p, -(parisiPotential β μ p * parisiTestT φ p) + β ^ 2 / 2 *
      (parisiPotential β μ p * parisiTestXX φ p +
        (parisiCDF μ p.1 * parisiGradient β μ p ^ 2) * φ p) ∂parisiSpaceTime) = 0 at hP
    have hAdd := integral_add hiT.neg ((hiXX.add hiS).const_mul (β ^ 2 / 2))
    simp only [Pi.add_apply, Pi.neg_apply] at hAdd
    rw [hAdd, integral_neg, integral_const_mul] at hP
    have hAdd' := integral_add hiXX hiS
    rw [hAdd'] at hP
    exact hP
  have hWsplit : (∫ p, parisiTimeField β μ 0 p * φ p ∂parisiSpaceTime) =
      -(β ^ 2 / 2) * ((∫ p, parisiSpatialField β μ 2 p * φ p ∂parisiSpaceTime) +
        (∫ p, (parisiCDF μ p.1 * parisiGradient β μ p ^ 2) * φ p ∂parisiSpaceTime)) := by
    calc
      _ = ∫ p, -(β ^ 2 / 2) * (parisiSpatialField β μ 2 p * φ p +
        (parisiCDF μ p.1 * parisiGradient β μ p ^ 2) * φ p) ∂parisiSpaceTime := by
          apply integral_congr_ae
          filter_upwards with p
          simp only [parisiTimeField, zero_add, parisiSquareSpatialField_zero]
          ring
      _ = _ := by rw [integral_const_mul, integral_add hiH hiS]
  rw [integral_add hiT hiW, hWsplit]
  rw [hXX] at hPsplit
  linarith

theorem isParisiWeakTimeDerivative_spatialField (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) :
    IsParisiWeakTimeDerivative (parisiSpatialField β μ n) (parisiTimeField β μ n) := by
  induction n with
  | zero => exact isParisiWeakTimeDerivative_potential β hβ μ
  | succ n ih =>
    intro φ hφ hc hs
    obtain ⟨M, hM⟩ := parisiTimeField_bounded β μ (n + 1)
    have hiT := integrable_continuousField_mul_test _ _
      (continuous_parisiSpatialField β μ (n + 1))
      (continuous_parisiTestT φ hφ) (hasCompactSupport_parisiTestT φ hφ hc)
    have hiW := integrable_boundedField_mul_compactTest _ φ
      (measurable_parisiTimeField β μ (n + 1)) M hM hφ.continuous hc
    refine ⟨hiT.add hiW, ?_⟩
    have hprev := (ih (parisiTestX φ) (contDiff_parisiTestX φ hφ)
      (hasCompactSupport_parisiTestX φ hφ hc)
      ((tsupport_parisiTestX_subset φ hφ).trans hs)).2
    have hiTX := integrable_continuousField_mul_test _ _ (continuous_parisiSpatialField β μ n)
      (continuous_parisiTestT _ (contDiff_parisiTestX φ hφ))
      (hasCompactSupport_parisiTestT _ (contDiff_parisiTestX φ hφ)
        (hasCompactSupport_parisiTestX φ hφ hc))
    obtain ⟨N, hN⟩ := parisiTimeField_bounded β μ n
    have hiWX := integrable_boundedField_mul_compactTest _ _
      (measurable_parisiTimeField β μ n) N hN (continuous_parisiTestX φ hφ)
      (hasCompactSupport_parisiTestX φ hφ hc)
    rw [integral_add hiTX hiWX] at hprev
    rw [← parisiTestX_testT_commute φ hφ] at hprev
    have hspace := integral_parisiSpatialField_byParts β μ n (parisiTestT φ)
      (contDiff_parisiTestT φ hφ) (hasCompactSupport_parisiTestT φ hφ hc)
      ((tsupport_parisiTestT_subset φ hφ).trans hs)
    have hsource := integral_parisiTimeField_spatial_byParts β μ n φ hφ hc
    rw [hspace, hsource] at hprev
    rw [integral_add hiT hiW]
    linarith

/-- The time derivative of every spatial derivative of the actual Parisi
potential has a measurable, uniformly bounded distributional representative.
Uniform boundedness is stronger than essential boundedness on the strip. -/
theorem parisiPotential_all_weakTimeDerivatives_bounded (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) :
    ∃ w : ℝ × ℝ → ℝ, Measurable w ∧
      (∃ M : ℝ, ∀ p, ‖w p‖ ≤ M) ∧
      IsParisiWeakTimeDerivative
        (fun p => iteratedDeriv n (fun y => parisiPotential β μ (p.1, y)) p.2) w := by
  refine ⟨parisiTimeField β μ n, measurable_parisiTimeField β μ n,
    parisiTimeField_bounded β μ n, ?_⟩
  intro φ hφ hc hs
  have heq : (fun p : ℝ × ℝ => iteratedDeriv n
      (fun y => parisiPotential β μ (p.1, y)) p.2 * parisiTestT φ p +
        parisiTimeField β μ n p * φ p) =ᵐ[parisiSpaceTime]
      (fun p => parisiSpatialField β μ n p * parisiTestT φ p +
        parisiTimeField β μ n p * φ p) := by
    have ht : ∀ᵐ p : ℝ × ℝ ∂parisiSpaceTime, p.1 ∈ Icc (0 : ℝ) 1 := by
      unfold parisiSpaceTime
      apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact Eventually.of_forall (fun _ => ht)
    filter_upwards [ht] with p hp
    rw [parisiSpatialField_eq_iteratedDeriv β μ n p.1 p.2 hp]
  have h := isParisiWeakTimeDerivative_spatialField β hβ μ n φ hφ hc hs
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).trans h.2⟩

theorem memLp_top_parisiTimeField (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    MemLp (parisiTimeField β μ n) ⊤ parisiSpaceTime := by
  obtain ⟨M, hM⟩ := parisiTimeField_bounded β μ n
  exact memLp_top_of_bound (measurable_parisiTimeField β μ n).aestronglyMeasurable
    M (Eventually.of_forall hM)

theorem parisiPotential_all_weakTimeDerivatives_memLp_top (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) :
    ∃ w : ℝ × ℝ → ℝ, MemLp w ⊤ parisiSpaceTime ∧
      IsParisiWeakTimeDerivative
        (fun p => iteratedDeriv n (fun y => parisiPotential β μ (p.1, y)) p.2) w := by
  obtain ⟨w, hwM, hwB, hw⟩ := parisiPotential_all_weakTimeDerivatives_bounded β hβ μ n
  obtain ⟨M, hM⟩ := hwB
  exact ⟨w, memLp_top_of_bound hwM.aestronglyMeasurable M (Eventually.of_forall hM), hw⟩

end Paper
