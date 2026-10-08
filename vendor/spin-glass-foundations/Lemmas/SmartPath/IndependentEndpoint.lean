module

public import Lemmas.SpinGlass.SKModel
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Permanent support for the independent endpoint

This module contains the Gaussian-law, reference-field, and product-spin identities used by
the independent endpoint of the generalized Latała argument.
-/

open MeasureTheory ProbabilityTheory Real BigOperators
open PhysLean.Probability.GaussianIBP
open scoped ENNReal NNReal

namespace SpinGlass.GeneralizedLatala

variable {Ω H : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma gaussianHilbert_hasGaussianLaw {g : Ω → H} (hg : IsGaussianHilbert g) :
    HasGaussianLaw g ℙ := by
  have hc : ∀ i, HasGaussianLaw (hg.c i) ℙ := by
    intro i
    exact HasLaw.hasGaussianLaw
      (HasLaw.mk (P := ℙ) (hg.c_meas i).aemeasurable (hg.c_gauss i))
  have hterm : ∀ i, HasGaussianLaw (fun ω => (hg.c i ω) • hg.w i) ℙ := by
    intro i
    exact (hc i).map_fun ((ContinuousLinearMap.id ℝ ℝ).smulRight (hg.w i))
  have hind : iIndepFun (fun i ω => (hg.c i ω) • hg.w i) ℙ :=
    hg.c_indep.comp (fun i x => x • hg.w i) (fun i => by fun_prop)
  have hsum : HasGaussianLaw (fun ω => ∑ i, (hg.c i ω) • hg.w i) ℙ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum hterm hind
  exact hsum.congr (Filter.Eventually.of_forall fun ω => by
    simpa using congrFun hg.repr ω |>.symm)

noncomputable def gaussianProduct (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N => gaussianReal 0 1)

noncomputable def siteVector (N : ℕ) (β q : ℝ) (i : Fin N) : EnergySpace N :=
  WithLp.toLp 2 (fun σ => β * Real.sqrt q * spin N σ i)

noncomputable def referenceFieldCLM (N : ℕ) (β q : ℝ) :
    (Fin N → ℝ) →L[ℝ] EnergySpace N :=
  ∑ i : Fin N, (ContinuousLinearMap.proj i).smulRight (siteVector N β q i)

noncomputable def referenceField (N : ℕ) (β q : ℝ) (z : Fin N → ℝ) : EnergySpace N :=
  referenceFieldCLM N β q z

lemma referenceField_apply (N : ℕ) (β q : ℝ) (z : Fin N → ℝ) (σ : Config N) :
    referenceField N β q z σ = β * Real.sqrt q * ∑ i, z i * spin N σ i := by
  classical
  simp [referenceField, referenceFieldCLM, siteVector, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma referenceField_eq_sum (N : ℕ) (β q : ℝ) (z : Fin N → ℝ) :
    referenceField N β q z = ∑ i, z i • siteVector N β q i := by
  classical
  simp [referenceField, referenceFieldCLM]

lemma gaussianProduct_eval_law (N : ℕ) (i : Fin N) :
    Measure.map (fun z : Fin N → ℝ => z i) (gaussianProduct N) = gaussianReal 0 1 := by
  simpa [gaussianProduct] using
    (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).map_eq

lemma gaussianProduct_iIndep (N : ℕ) :
    iIndepFun (fun i (z : Fin N → ℝ) => z i) (gaussianProduct N) := by
  simpa [gaussianProduct] using
    (iIndepFun_pi (μ := fun _ : Fin N => gaussianReal 0 1)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable))

lemma gaussianProduct_eval_gaussian (N : ℕ) (i : Fin N) :
    HasGaussianLaw (fun z : Fin N → ℝ => z i) (gaussianProduct N) :=
  HasLaw.hasGaussianLaw
    (HasLaw.mk (P := gaussianProduct N) (measurable_pi_apply i).aemeasurable
      (gaussianProduct_eval_law N i))

lemma referenceField_hasGaussianLaw (N : ℕ) (β q : ℝ) :
    HasGaussianLaw (referenceField N β q) (gaussianProduct N) := by
  have hz : HasGaussianLaw (fun z : Fin N → ℝ => z) (gaussianProduct N) := by
    apply ProbabilityTheory.iIndepFun.hasGaussianLaw
    · intro i
      exact gaussianProduct_eval_gaussian N i
    · exact gaussianProduct_iIndep N
  exact hz.map_fun (referenceFieldCLM N β q)

lemma gaussianProduct_mean (N : ℕ) (i : Fin N) :
    ∫ z, z i ∂gaussianProduct N = 0 := by
  have hmap := integral_map (μ := gaussianProduct N)
    (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id
  rw [gaussianProduct_eval_law] at hmap
  simpa using hmap.symm.trans integral_id_gaussianReal

lemma gaussianProduct_secondMoment (N : ℕ) (i j : Fin N) :
    ∫ z, z i * z j ∂gaussianProduct N = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp only [← pow_two]
    have hmap := integral_map (μ := gaussianProduct N)
      (measurable_pi_apply i).aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2)
          (Measure.map (fun z : Fin N → ℝ => z i) (gaussianProduct N)) by fun_prop)
    rw [gaussianProduct_eval_law] at hmap
    simpa using hmap.symm.trans (integral_sq_gaussianReal_centered (v := 1))
  · rw [if_neg hij]
    have hmul := (gaussianProduct_iIndep N).indepFun hij |>.integral_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
    simpa [gaussianProduct_mean] using hmul

lemma energy_eq_sum_std (N : ℕ) (x : EnergySpace N) :
    x = ∑ σ : Config N, (x σ) • std_basis N σ := by
  classical
  ext τ
  simp [std_basis]

lemma bilin_eq_sum_std (N : ℕ) (C : EnergySpace N →L[ℝ] EnergySpace N →L[ℝ] ℝ)
    (x y : EnergySpace N) :
    C x y = ∑ σ, ∑ τ, x σ * y τ * C (std_basis N σ) (std_basis N τ) := by
  classical
  calc
    C x y = C (∑ σ, (x σ) • std_basis N σ) (∑ τ, (y τ) • std_basis N τ) :=
      congrArg₂ (fun a b => C a b) (energy_eq_sum_std N x) (energy_eq_sum_std N y)
    _ = _ := by
      simp [map_sum, map_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      ring

lemma map_gaussian_mean_zero {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (N : ℕ) (g : Ω → EnergySpace N)
    (hg : IsGaussianHilbert g) :
    ∫ x, id x ∂Measure.map g ℙ = 0 := by
  have hgLaw := gaussianHilbert_hasGaussianLaw hg
  have hmap : ∫ x, id x ∂Measure.map g ℙ = ∫ ω, g ω ∂ℙ := by
    exact integral_map hgLaw.aemeasurable aestronglyMeasurable_id
  rw [hmap]
  have hcMean : ∀ i, ∫ ω, hg.c i ω ∂ℙ = 0 := by
    intro i
    have hmapc := integral_map (μ := ℙ) (hg.c_meas i).aemeasurable aestronglyMeasurable_id
    rw [hg.c_gauss i] at hmapc
    simpa using hmapc.symm.trans integral_id_gaussianReal
  rw [hg.repr, integral_finset_sum]
  · simp [integral_smul_const, hcMean]
  · intro i _
    have hci : HasGaussianLaw (hg.c i) ℙ := HasLaw.hasGaussianLaw
      (HasLaw.mk (P := ℙ) (hg.c_meas i).aemeasurable (hg.c_gauss i))
    exact hci.integrable.smul_const _

lemma gaussianHilbert_coord_secondMoment {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] (g : Ω → H) (hg : IsGaussianHilbert g)
    [DecidableEq hg.ι]
    (i j : hg.ι) :
    ∫ ω, hg.c i ω * hg.c j ω ∂ℙ = if i = j then (hg.τ i : ℝ) else 0 := by
  classical
  have hc (k : hg.ι) : HasGaussianLaw (hg.c k) ℙ := HasLaw.hasGaussianLaw
    (HasLaw.mk (P := ℙ) (hg.c_meas k).aemeasurable (hg.c_gauss k))
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp only [← pow_two]
    have hmap := integral_map (μ := ℙ) (hg.c_meas i).aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2) (Measure.map (hg.c i) ℙ) by fun_prop)
    rw [hg.c_gauss i] at hmap
    simpa using hmap.symm.trans (integral_sq_gaussianReal_centered (hg.τ i))
  · rw [if_neg hij]
    have hmul := hg.c_indep.indepFun hij |>.integral_mul_eq_mul_integral
      (hg.c_meas i).aestronglyMeasurable (hg.c_meas j).aestronglyMeasurable
    have hmean (k : hg.ι) : ∫ ω, hg.c k ω ∂ℙ = 0 := by
      have hmap := integral_map (μ := ℙ) (hg.c_meas k).aemeasurable aestronglyMeasurable_id
      rw [hg.c_gauss k] at hmap
      simpa using hmap.symm.trans integral_id_gaussianReal
    simpa [hmean] using hmul

lemma gaussianHilbert_eval_pairing {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (N : ℕ) (g : Ω → EnergySpace N)
    (hg : IsGaussianHilbert g) (σ τ : Config N) :
    ∫ ω, g ω σ * g ω τ ∂ℙ = inner ℝ ((covOp (g := g) hg) (std_basis N σ))
      (std_basis N τ) := by
  classical
  have hpoint (ω : Ω) (ρ : Config N) :
      g ω ρ = ∑ i, hg.c i ω * hg.w i ρ := by
    have := congrFun hg.repr ω
    rw [this]
    simp
  have hterm (i j : hg.ι) :
      Integrable (fun ω => hg.c i ω * hg.w i σ * (hg.c j ω * hg.w j τ)) ℙ := by
    have hc (k : hg.ι) : HasGaussianLaw (hg.c k) ℙ := HasLaw.hasGaussianLaw
      (HasLaw.mk (P := ℙ) (hg.c_meas k).aemeasurable (hg.c_gauss k))
    have hij : Integrable (fun ω => hg.c i ω * hg.c j ω) ℙ := by
      exact ((hc i).memLp_two.integrable_mul (hc j).memLp_two).congr
        (Filter.Eventually.of_forall fun ω => by rfl)
    convert hij.const_mul (hg.w i σ * hg.w j τ) using 1 <;> ext ω <;> ring
  simp_rw [hpoint, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hterm i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hterm _ j)]
  simp_rw [show ∀ i j, (fun ω => hg.c i ω * hg.w i σ * (hg.c j ω * hg.w j τ)) =
      fun ω => (hg.w i σ * hg.w j τ) * (hg.c i ω * hg.c j ω) by
    intro i j; funext ω; ring, integral_const_mul, gaussianHilbert_coord_secondMoment g hg]
  simp [covOp_apply, sum_inner, inner_smul_left, real_inner_comm, inner_std_basis_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma referenceField_mean_zero (N : ℕ) (β q : ℝ) :
    ∫ x, id x ∂Measure.map (referenceField N β q) (gaussianProduct N) = 0 := by
  have href := referenceField_hasGaussianLaw N β q
  rw [integral_map href.aemeasurable aestronglyMeasurable_id]
  simp only [id_eq]
  simp_rw [referenceField_eq_sum]
  rw [integral_finset_sum]
  · simp [integral_smul_const, gaussianProduct_mean]
  · intro i _
    exact (gaussianProduct_eval_gaussian N i).integrable.smul_const _

lemma referenceField_pairing (N : ℕ) (β q : ℝ) (hN : 0 < N) (hq0 : 0 ≤ q)
    (σ τ : Config N) :
    ∫ z, referenceField N β q z σ * referenceField N β q z τ ∂gaussianProduct N =
      simple_cov_kernel N β (fun x => q * x) σ τ := by
  classical
  have hprod (z : Fin N → ℝ) :
      referenceField N β q z σ * referenceField N β q z τ =
        ∑ i, ∑ j, (β * √q) ^ 2 * (z i * spin N σ i) * (z j * spin N τ j) := by
    simp only [referenceField_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  have hterm (i j : Fin N) :
      Integrable (fun z : Fin N → ℝ =>
        (β * √q) ^ 2 * (z i * spin N σ i) * (z j * spin N τ j)) (gaussianProduct N) := by
    have hij : Integrable (fun z : Fin N → ℝ => z i * z j) (gaussianProduct N) := by
      exact ((gaussianProduct_eval_gaussian N i).memLp_two.integrable_mul
        (gaussianProduct_eval_gaussian N j).memLp_two).congr
          (Filter.Eventually.of_forall fun z => by rfl)
    convert hij.const_mul ((β * √q) ^ 2 * spin N σ i * spin N τ j) using 1 <;>
      ext z <;> ring
  have hint (i j : Fin N) :
      ∫ z, (β * √q) ^ 2 * (z i * spin N σ i) * (z j * spin N τ j)
          ∂gaussianProduct N =
        (β * √q) ^ 2 * spin N σ i * spin N τ j * (if i = j then 1 else 0) := by
    rw [show (fun z : Fin N → ℝ =>
        (β * √q) ^ 2 * (z i * spin N σ i) * (z j * spin N τ j)) =
      fun z => ((β * √q) ^ 2 * spin N σ i * spin N τ j) * (z i * z j) by
        funext z; ring]
    rw [integral_const_mul, gaussianProduct_secondMoment]
  simp_rw [hprod]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hterm i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hterm _ j)]
  simp_rw [hint]
  simp [simple_cov_kernel, overlap, Finset.mul_sum]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp_rw [mul_pow, Real.sq_sqrt hq0]
  field_simp [hN0]

lemma simpleDisorder_law_eq_reference {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (N : ℕ) (β q : ℝ)
    (sim : SimpleDisorder (Ω := Ω) N β q) (hN : 0 < N) (hq0 : 0 ≤ q) :
    Measure.map sim.V ℙ = Measure.map (referenceField N β q) (gaussianProduct N) := by
  let μ := Measure.map sim.V ℙ
  let ν := Measure.map (referenceField N β q) (gaussianProduct N)
  have hsimLaw := gaussianHilbert_hasGaussianLaw sim.hV
  have hrefLaw := referenceField_hasGaussianLaw N β q
  letI : IsGaussian μ := hsimLaw.isGaussian_map
  letI : IsGaussian ν := hrefLaw.isGaussian_map
  have hmatrix (σ τ : Config N) :
      covarianceBilin μ (std_basis N σ) (std_basis N τ) =
        covarianceBilin ν (std_basis N σ) (std_basis N τ) := by
    simp only [μ, ν]
    rw [covarianceBilin_apply hsimLaw.isGaussian_map.memLp_two_id,
      covarianceBilin_apply hrefLaw.isGaussian_map.memLp_two_id,
      map_gaussian_mean_zero N sim.V sim.hV, referenceField_mean_zero N β q]
    simp only [sub_zero]
    rw [integral_map hsimLaw.aemeasurable, integral_map hrefLaw.aemeasurable]
    · simpa [inner_std_basis_apply, real_inner_comm] using
        (gaussianHilbert_eval_pairing N sim.V sim.hV σ τ).trans
          ((sim.cov_eq σ τ).trans (referenceField_pairing N β q hN hq0 σ τ).symm)
    · fun_prop
    · fun_prop
  apply ProbabilityTheory.IsGaussian.ext
  · simpa [μ, ν] using (map_gaussian_mean_zero N sim.V sim.hV).trans
      (referenceField_mean_zero N β q).symm
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    calc
      covarianceBilin μ x y = ∑ σ, ∑ τ, x σ * y τ *
          covarianceBilin μ (std_basis N σ) (std_basis N τ) :=
        bilin_eq_sum_std N (covarianceBilin μ) x y
      _ = ∑ σ, ∑ τ, x σ * y τ *
          covarianceBilin ν (std_basis N σ) (std_basis N τ) := by
        simp_rw [hmatrix]
      _ = covarianceBilin ν x y := (bilin_eq_sum_std N (covarianceBilin ν) x y).symm

def boolSpin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def siteEnergy (N : ℕ) (a : Fin N → ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ => ∑ i, a i * spin N σ i)

lemma siteEnergy_apply (N : ℕ) (a : Fin N → ℝ) (σ : Config N) :
    siteEnergy N a σ = ∑ i, a i * spin N σ i := rfl

lemma spin_eq_boolSpin (N : ℕ) (σ : Config N) (i : Fin N) :
    spin N σ i = boolSpin (σ i) := rfl

lemma Z_siteEnergy (N : ℕ) (a : Fin N → ℝ) :
    Z N (siteEnergy N a) = ∏ i, ∑ b : Bool, Real.exp (-(a i * boolSpin b)) := by
  classical
  rw [show Z N (siteEnergy N a) =
      ∑ σ : Config N, ∏ i, Real.exp (-(a i * boolSpin (σ i))) by
    simp only [Z, siteEnergy_apply, spin_eq_boolSpin]
    congr 1
    ext σ
    rw [← Finset.sum_neg_distrib, Real.exp_sum]]
  exact (Fintype.prod_sum (fun i b => Real.exp (-(a i * boolSpin b)))).symm

lemma gibbs_pmf_siteEnergy (N : ℕ) (a : Fin N → ℝ) (σ : Config N) :
    gibbs_pmf N (siteEnergy N a) σ =
      ∏ i, Real.exp (-(a i * boolSpin (σ i))) / (∑ b : Bool, Real.exp (-(a i * boolSpin b))) := by
  classical
  rw [gibbs_pmf, Z_siteEnergy]
  simp only [siteEnergy_apply, spin_eq_boolSpin]
  rw [← Finset.sum_neg_distrib, Real.exp_sum, Finset.prod_div_distrib]

lemma reference_add_field_eq_siteEnergy (N : ℕ) (β h q : ℝ) (z : Fin N → ℝ) :
    referenceField N β q z + magnetic_field_vector (N := N) h =
      siteEnergy N (fun i => h + β * Real.sqrt q * z i) := by
  classical
  ext σ
  simp [referenceField_apply, magnetic_field_vector, siteEnergy_apply, magnetization,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def transposeReplicaEquiv (N n : ℕ) :
    (Fin n → Fin N → Bool) ≃ (Fin N → Fin n → Bool) where
  toFun σ i l := σ l i
  invFun x l i := x i l
  left_inv _ := rfl
  right_inv _ := rfl

end SpinGlass.GeneralizedLatala
