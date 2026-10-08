/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# The Cameron--Martin space of a Gaussian measure

For a Gaussian measure `μ` on a real separable Banach space `W`, the Cameron--Martin
space is constructed from the first Gaussian chaos.  We take the closure in `L²(μ)` of
the centered continuous linear functionals on `W`.  The covariance (or reproducing-kernel)
map sends this Hilbert space continuously and injectively into `W`.

This construction deliberately precedes quasi-invariance.  The Cameron--Martin theorem
will identify the range of `CameronMartin.inclusion` with the translations whose laws are
equivalent to `μ`; using that characterization as the definition here would be circular.

## Main definitions

* `translatedMeasure μ h`: the law of `x + h` when `x` has law `μ`;
* `CameronMartin.centeredDualToLp`: a continuous functional, centered and regarded in `L²(μ)`;
* `CameronMartin.firstChaos`: the closed span of centered continuous functionals;
* `CameronMartin.Space`: the Cameron--Martin Hilbert space;
* `CameronMartin.inclusion`: its covariance embedding into the ambient Banach space;
* `CameronMartin.logDensity`: the log Radon--Nikodym derivative used by the next rung.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology

universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_7



























namespace StochasticCalculus

section Translations

variable {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W]

/-- Translation of the ambient space by `h`. -/
@[expose] def translate (h : W) : W → W := fun x ↦ x + h

/-- The law obtained by translating `μ` by `h`. -/
@[expose] noncomputable def translatedMeasure (μ : Measure W) (h : W) : Measure W :=
  μ.map (translate h)

@[fun_prop]
theorem measurable_translate [BorelSpace W] (h : W) : Measurable (translate h) := by
  unfold translate
  fun_prop

@[simp]
theorem translatedMeasure_zero (μ : Measure W) : translatedMeasure μ 0 = μ := by
  have h_zero : translate (0 : W) = id := by
    funext x
    simp only [translate, add_zero, id_eq]
  simp only [translatedMeasure, h_zero, Measure.map_id]

theorem translatedMeasure_add [BorelSpace W] (μ : Measure W) (h k : W) :
    translatedMeasure (translatedMeasure μ h) k = translatedMeasure μ (h + k) := by
  change (μ.map (translate h)).map (translate k) = μ.map (translate (h + k))
  rw [Measure.map_map (measurable_translate k) (measurable_translate h)]
  congr 1
  funext x
  simp only [Function.comp_apply, translate, add_assoc]

/-- A shift is admissible when its translated law is absolutely continuous with respect to
the original law.  The Cameron--Martin theorem will characterize these shifts. -/
def IsAdmissibleShift (μ : Measure W) (h : W) : Prop :=
  translatedMeasure μ h ≪ μ

/-- A shift is quasi-invariant when translation preserves the measure class. -/
@[expose] def IsQuasiInvariantShift (μ : Measure W) (h : W) : Prop :=
  translatedMeasure μ h ≪ μ ∧ μ ≪ translatedMeasure μ h

end Translations

namespace CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

/-- The Bochner mean of a Gaussian measure. -/
@[expose] noncomputable def mean : W := ∫ x, x ∂μ

/-- The centered identity random variable. -/
noncomputable def centeredId : W → W := id - fun _ ↦ mean μ

/-- Gaussian measures have a square-integrable centered identity. -/
theorem memLp_centeredId : MemLp (centeredId μ) 2 μ := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_const : MemLp (fun _ : W ↦ mean μ) 2 μ := memLp_const (mean μ)
  exact h_id.sub h_const

/-- The centered identity as an element of `L²(μ; W)`. -/
noncomputable def centeredIdLp : Lp W 2 μ :=
  (memLp_centeredId μ).toLp (centeredId μ)

/-- The continuous map taking a continuous linear functional to its centered `L²(μ)` class. -/
noncomputable def centeredDualToLp : StrongDual ℝ W →L[ℝ] Lp ℝ 2 μ :=
  StrongDual.toLp μ 2 -
    (Lp.constL 2 μ ℝ).comp (ContinuousLinearMap.apply ℝ ℝ (mean μ))

/-- Pointwise description of `centeredDualToLp`. -/
theorem centeredDualToLp_ae_eq (L : StrongDual ℝ W) :
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ]
      fun x ↦ L x - L (mean μ) := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_toLp :
      ((StrongDual.toLp μ 2 L : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ] L := by
    simpa only [StrongDual.toLp_apply h_id, id_eq] using
      MemLp.coeFn_toLp (h_id.continuousLinearMap_comp L)
  have h_const :
      ((Lp.constL 2 μ ℝ (L (mean μ)) : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ]
        Function.const W (L (mean μ)) := by
    simpa only [Lp.constL_apply] using Lp.coeFn_const 2 μ (L (mean μ))
  unfold centeredDualToLp
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  filter_upwards [Lp.coeFn_sub (StrongDual.toLp μ 2 L)
      (Lp.constL 2 μ ℝ (L (mean μ))), h_toLp, h_const] with x hsub hL hc
  simpa [hL, hc, Function.const_apply] using hsub

/-- The first Gaussian chaos: the closed span of centered continuous linear functionals. -/
@[expose] noncomputable def firstChaos : Submodule ℝ (Lp ℝ 2 μ) :=
  (centeredDualToLp μ).range.topologicalClosure

/-- The Cameron--Martin Hilbert space.  Its norm and inner product are inherited from `L²(μ)`. -/
noncomputable abbrev Space := firstChaos μ

/-- Continuous linear functionals give a dense family of Cameron--Martin vectors. -/
@[expose] noncomputable def ofDual : StrongDual ℝ W →L[ℝ] Space μ :=
  (centeredDualToLp μ).codRestrict (firstChaos μ) fun L ↦
    Submodule.le_topologicalClosure _ ⟨L, rfl⟩

omit [CompleteSpace W] [SecondCountableTopology W] in
@[simp]
theorem coe_ofDual (L : StrongDual ℝ W) :
    ((ofDual μ L : Space μ) : Lp ℝ 2 μ) = centeredDualToLp μ L :=
  rfl

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The range of `ofDual` is dense by construction. -/
theorem denseRange_ofDual : DenseRange (ofDual μ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro f hf
  have h_image :
      ((↑) '' Set.range (ofDual μ) : Set (Lp ℝ 2 μ)) =
        Set.range (centeredDualToLp μ) := by
    ext g
    constructor
    · rintro ⟨_, ⟨L, rfl⟩, rfl⟩
      exact ⟨L, rfl⟩
    · rintro ⟨L, rfl⟩
      exact ⟨ofDual μ L, ⟨L, rfl⟩, rfl⟩
  have hf' : f ∈ closure (Set.range (centeredDualToLp μ)) := hf
  exact h_image.symm ▸ hf'

/-- Multiplying a scalar `L²` random variable by the centered identity is integrable. -/
theorem integrable_smul_centeredId (f : Lp ℝ 2 μ) :
    Integrable (fun x ↦ f x • centeredId μ x) μ := by
  change Integrable (((fun x ↦ f x) • centeredId μ)) μ
  have h_one :
      MemLp ((fun x ↦ f x) • centeredId μ) 1 μ :=
    (Lp.memLp f).smul (memLp_centeredId μ)
  have h_integrable : Integrable (((fun x ↦ f x) • centeredId μ)) μ :=
    memLp_one_iff_integrable.mp h_one
  exact h_integrable

/-- The algebraic covariance map from scalar `L²(μ)` to the ambient Banach space. -/
noncomputable def covarianceLinearMap : Lp ℝ 2 μ →ₗ[ℝ] W where
  toFun f := ∫ x, f x • centeredId μ x ∂μ
  map_add' f g := by
    rw [← integral_add (integrable_smul_centeredId μ f)
      (integrable_smul_centeredId μ g)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx, add_smul]
  map_smul' c f := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply] at hx ⊢
    calc
      (c • f) x • centeredId μ x = (c * f x) • centeredId μ x := by
        simpa only [smul_eq_mul] using congrArg (fun a : ℝ ↦ a • centeredId μ x) hx
      _ = c • (f x • centeredId μ x) := by rw [smul_smul]

/-- The covariance map is the Hölder pairing of a scalar `L²` random variable with the
centered identity.  Its continuity is supplied by the `L²` pairing. -/
noncomputable def covarianceMap : Lp ℝ 2 μ →L[ℝ] W :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := W)).lpPairing μ 2 2).flip (centeredIdLp μ)

@[simp]
theorem covarianceMap_apply (f : Lp ℝ 2 μ) :
    covarianceMap μ f = ∫ x, f x • centeredId μ x ∂μ := by
  rw [covarianceMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_centeredId μ)] with x hx
  simp only [ContinuousLinearMap.lsmul_apply]
  change f x • ((memLp_centeredId μ).toLp (centeredId μ)) x = _
  rw [hx]

/-- The covariance, or RKHS, embedding of the Cameron--Martin space into `W`. -/
noncomputable def inclusion : Space μ →L[ℝ] W :=
  (covarianceMap μ).domRestrict (firstChaos μ)

@[simp]
theorem inclusion_apply (h : Space μ) :
    inclusion μ h = ∫ x, (h : Lp ℝ 2 μ) x • centeredId μ x ∂μ :=
  covarianceMap_apply μ (h : Lp ℝ 2 μ)

/-- Reproducing identity between the covariance embedding and the first-chaos inner product. -/
theorem apply_inclusion (L : StrongDual ℝ W) (h : Space μ) :
    L (inclusion μ h) = @inner ℝ _ _ (ofDual μ L) h := by
  rw [inclusion_apply, ← L.integral_comp_comm
    (integrable_smul_centeredId μ (h : Lp ℝ 2 μ)), Submodule.coe_inner,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
  simp only [coe_ofDual]
  rw [hx]
  simp only [centeredId, Pi.sub_apply, id_eq, map_smul, map_sub, smul_eq_mul,
    RCLike.inner_apply, conj_trivial]

/-- The covariance embedding is injective on the closed first chaos. -/
theorem inclusion_injective : Function.Injective (inclusion μ) := by
  intro h k hhk
  apply (denseRange_ofDual μ).eq_of_inner_right ℝ
  intro L
  rw [← apply_inclusion μ L h, ← apply_inclusion μ L k, hhk]

/-- The Cameron--Martin space as a linear subspace of the ambient Banach space. -/
noncomputable def subspace : Submodule ℝ W :=
  (inclusion μ).range

theorem mem_subspace_iff (h : W) :
    h ∈ subspace μ ↔ ∃ k : Space μ, inclusion μ k = h := by
  rfl

/-- The `L²` inner product of generators is the covariance bilinear form. -/
theorem inner_ofDual (L K : StrongDual ℝ W) :
    @inner ℝ _ _ (ofDual μ L) (ofDual μ K) = covarianceBilinDual μ L K := by
  rw [Submodule.coe_inner, L2.inner_def]
  rw [covarianceBilinDual_apply IsGaussian.memLp_two_id]
  apply integral_congr_ae
  filter_upwards [centeredDualToLp_ae_eq μ L,
    centeredDualToLp_ae_eq μ K] with x hL hK
  simp only [coe_ofDual]
  rw [hL, hK]
  rw [IsGaussian.integral_dual L, IsGaussian.integral_dual K]
  simp only [mean, RCLike.inner_apply, conj_trivial]
  ring

/-- Fernique's exponential integrability, recorded at the Cameron--Martin interface. -/
theorem exists_integrable_exp_sq :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x ↦ Real.exp (C * ‖x‖ ^ 2)) μ := by
  have h_fernique :
      ∃ C : ℝ, 0 < C ∧ Integrable (fun x ↦ Real.exp (C * ‖x‖ ^ 2)) μ :=
    IsGaussian.exists_integrable_exp_sq μ
  exact h_fernique

/-- The translated law along a Cameron--Martin vector. -/
@[expose] noncomputable def translated (h : Space μ) : Measure W :=
  translatedMeasure μ (inclusion μ h)

/-- Its log Radon--Nikodym derivative with respect to `μ`.  The Cameron--Martin theorem will
identify this almost everywhere with `h - ‖h‖² / 2`. -/
@[expose] noncomputable def logDensity (h : Space μ) : W → ℝ :=
  llr (translated μ h) μ

end CameronMartin

end StochasticCalculus
