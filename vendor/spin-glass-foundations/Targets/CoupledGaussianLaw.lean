module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/-
# Change of Gaussian coordinates for the coupled cascade

The spectral realisation and the abstract SK disorder have the same law,
jointly with an independent standard outer field. No nondegeneracy of the
spectral variances is required.
-/
public import Targets.CoupledConcentration

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}

/-- Scaling a standard Gaussian also covers zero variance. -/
theorem gaussianReal_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one]
    exact Real.sq_sqrt v.coe_nonneg

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem sk_spectral_map (sk : SKDisorder (Ω := Ω) n β h) :
    (Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map
      (fun z => ∑ i, (Real.sqrt (sk.hU.τ i) * z i) • sk.hU.w i) =
      (ℙ : Measure Ω).map sk.U := by
  let C : Ω → (sk.hU.ι → ℝ) := fun ω i => sk.hU.c i ω
  let S : (sk.hU.ι → ℝ) → (sk.hU.ι → ℝ) := fun z i => Real.sqrt (sk.hU.τ i) * z i
  let W : (sk.hU.ι → ℝ) → EnergySpace n := fun z => ∑ i, z i • sk.hU.w i
  have hC : Measurable C := Measurable.of_eval sk.hU.c_meas
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hClaw : (ℙ : Measure Ω).map C = Measure.pi (fun i => gaussianReal 0 (sk.hU.τ i)) := by
    have H := iIndepFun.map_fun_eq_pi_map (fun i => (sk.hU.c_meas i).aemeasurable) sk.hU.c_indep
    simpa only [show ∀ i, (ℙ : Measure Ω).map (sk.hU.c i) = gaussianReal 0 (sk.hU.τ i)
      from sk.hU.c_gauss] using H
  have hSlaw : (Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map S =
      Measure.pi (fun i => gaussianReal 0 (sk.hU.τ i)) := by
    haveI (i : sk.hU.ι) : IsProbabilityMeasure
        ((gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (sk.hU.τ i) * z)) := by
      rw [gaussianReal_map_sqrt]
      infer_instance
    rw [show S = (fun z i => Real.sqrt (sk.hU.τ i) * z i) from rfl,
      Measure.pi_map_pi (μ := fun _ : sk.hU.ι => gaussianReal 0 1)
        (f := fun i z => Real.sqrt (sk.hU.τ i) * z)
        (fun i => (measurable_const.mul measurable_id).aemeasurable)]
    simp only [gaussianReal_map_sqrt]
  calc
    _ = ((Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map S).map W := by
      rw [Measure.map_map hW hS]
      rfl
    _ = ((ℙ : Measure Ω).map C).map W := by rw [hSlaw, hClaw]
    _ = (ℙ : Measure Ω).map sk.U := by
      rw [Measure.map_map hW hC]
      congr 1
      exact sk.hU.repr.symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The law is preserved jointly with the independent, as yet unscaled outer field. -/
theorem coupledGaussian_pair_map (sk : SKDisorder (Ω := Ω) n β h) :
    (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)).map
      (fun z => (coupledGaussianU sk z, fun i => z (Sum.inr i))) =
      ((ℙ : Measure Ω).map sk.U).prod (piGauss n) := by
  let μ := Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : sk.hU.ι ⊕ Fin n => gaussianReal 0 1)
  let W : (sk.hU.ι → ℝ) → EnergySpace n :=
    fun z => ∑ i, (Real.sqrt (sk.hU.τ i) * z i) • sk.hU.w i
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : sk.hU.ι ⊕ Fin n => ℝ)
  have hW : Measurable W := by dsimp [W]; fun_prop
  have he : ν.map e = μ.prod (piGauss n) :=
    (measurePreserving_sumPiEquivProdPi (fun _ : sk.hU.ι ⊕ Fin n => gaussianReal 0 1)).map_eq
  have hto : Measurable (WithLp.toLp 2 : (sk.hU.ι ⊕ Fin n → ℝ) → CoupledGaussianSpace sk) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : sk.hU.ι ⊕ Fin n => ℝ)).symm.continuous.measurable
  have hpair : Measurable (fun z : CoupledGaussianSpace sk =>
      (coupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold coupledGaussianU
    fun_prop
  rw [SYK.standardGaussianMeasureOnEuclidean, Measure.map_map hpair hto]
  change ν.map _ = _
  calc
    _ = (ν.map e).map (Prod.map W id) := by
      rw [Measure.map_map (hW.prodMap measurable_id) e.measurable]
      rfl
    _ = (μ.map W).prod (piGauss n) := by
      rw [he, ← Measure.map_prod_map μ (piGauss n) hW measurable_id, Measure.map_id]
    _ = _ := by rw [sk_spectral_map sk]

/-- Change of coordinates for any jointly measurable disorder/outer-field test. -/
theorem integral_coupledGaussian_pair (sk : SKDisorder (Ω := Ω) n β h)
    {F : EnergySpace n × (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    (∫ z, F (coupledGaussianU sk z, fun i => z (Sum.inr i))
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ p : Ω × (Fin n → ℝ), F (sk.U p.1, p.2) ∂(ℙ : Measure Ω).prod (piGauss n) := by
  have hpair : Measurable (fun z : CoupledGaussianSpace sk =>
      (coupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold coupledGaussianU
    fun_prop
  rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable, coupledGaussian_pair_map,
    ← Measure.map_id (μ := piGauss n),
    Measure.map_prod_map _ _ sk.hU.repr_measurable measurable_id,
    integral_map (sk.hU.repr_measurable.prodMap measurable_id).aemeasurable hF.aestronglyMeasurable]
  simp only [Measure.map_id]
  rfl

theorem integrable_coupledGaussian_pair_iff (sk : SKDisorder (Ω := Ω) n β h)
    {F : EnergySpace n × (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Integrable (fun z => F (coupledGaussianU sk z, fun i => z (Sum.inr i)))
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ↔
    Integrable (fun p : Ω × (Fin n → ℝ) => F (sk.U p.1, p.2))
      ((ℙ : Measure Ω).prod (piGauss n)) := by
  have hpair : Measurable (fun z : CoupledGaussianSpace sk =>
      (coupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold coupledGaussianU
    fun_prop
  have H := integrable_map_measure
    (μ := SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n))
    hF.aestronglyMeasurable hpair.aemeasurable
  rw [coupledGaussian_pair_map, ← Measure.map_id (μ := piGauss n),
    Measure.map_prod_map _ _ sk.hU.repr_measurable measurable_id] at H
  have H' := integrable_map_measure (μ := (ℙ : Measure Ω).prod (piGauss n))
    hF.aestronglyMeasurable (sk.hU.repr_measurable.prodMap measurable_id).aemeasurable
  exact H.symm.trans H'

end SpinGlass.Targets
