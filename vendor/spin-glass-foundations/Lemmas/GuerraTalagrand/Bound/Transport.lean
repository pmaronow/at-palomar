module

public import Lemmas.GuerraTalagrand.Bound.Basic
public import Lemmas.Concentration.Transport

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

lemma gtFullPath_eval_integrable
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ}
    (path : RSSmartPathDisorder Ω N β h q)
    (σ : SpinGlass.Config N) :
    Integrable (fun ω => fullPathHamiltonian path s ω σ) := by
  have hU : HasGaussianLaw path.sk.U volume :=
    gaussianHilbert_hasGaussianLaw path.sk.hU
  have hV : HasGaussianLaw path.simple.V volume :=
    gaussianHilbert_hasGaussianLaw path.simple.hV
  have hUeval : Integrable (fun ω => path.sk.U ω σ) := by
    simpa using (hU.map_fun (SpinGlass.evalCLM (N := N) σ)).integrable
  have hVeval : Integrable (fun ω => path.simple.V ω σ) := by
    simpa using (hV.map_fun (SpinGlass.evalCLM (N := N) σ)).integrable
  change Integrable (fun ω =>
    Real.sqrt s * path.sk.U ω σ +
      Real.sqrt (1 - s) * path.simple.V ω σ +
        SpinGlass.magnetic_field_vector N h σ)
  exact ((hUeval.const_mul _).add (hVeval.const_mul _)).add (integrable_const _)

lemma gtConstrainedLog_integrable
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s v : ℝ}
    (path : RSSmartPathDisorder Ω N β h q)
    (hv : v ∈ attainableOverlaps N) :
    Integrable (fun ω => Real.log
      (constrainedPartition (fullPathHamiltonian path s ω) v)) := by
  classical
  letI := constrainedPair_nonempty hv
  let F : ConstrainedPair N v → Ω → ℝ := fun p ω =>
    -(fullPathHamiltonian path s ω p.1.1 +
      fullPathHamiltonian path s ω p.1.2)
  have hF (p : ConstrainedPair N v) : Integrable (F p) :=
    ((gtFullPath_eval_integrable path p.1.1).add
      (gtFullPath_eval_integrable path p.1.2)).neg
  have hint := gt_integrable_log_sum_exp F hF
  convert hint using 1
  funext ω
  rw [constrainedPartition_eq_sum_constrainedPair]

/-- Equality of the arbitrary and canonical constrained log-partition expectations. -/
theorem constrained_log_partition_integral_eq_canonical
    {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s v : ℝ}
    (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    (∫ ω, Real.log
        (constrainedPartition (fullPathHamiltonian path s ω) v) ∂volume) =
      ∫ x, coupledConstrainedLogPartition N β h q s v x
        ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) := by
  let I := {w : ℝ // w ∈ attainableOverlaps N}
  let Y : Ω → I → ℝ := fun ω w => Real.log
    (constrainedPartition (fullPathHamiltonian path s ω) w.1)
  let X : EuclideanSpace ℝ (CoupledGaussianIndex N) → I → ℝ := fun x w =>
    coupledConstrainedLogPartition N β h q s w.1 x
  let e : I := ⟨v, hv⟩
  let ev : (I → ℝ) → ℝ := fun f => f e
  have hY : AEMeasurable Y volume := by
    apply aemeasurable_pi_lambda
    intro w
    exact (gtConstrainedLog_integrable path w.2).aemeasurable
  have hX : AEMeasurable X
      (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
    apply aemeasurable_pi_lambda
    intro w
    exact (coupled_constrained_log_partition_lipschitz N β h q s w.1
      hN hs hq w.2).continuous.aemeasurable
  have hev : Measurable ev := measurable_pi_apply e
  have hlaw := coupled_constrained_log_partition_vector_law path ⟨s, hs⟩ hq.1
  have hmap := congrArg (Measure.map ev) hlaw
  rw [AEMeasurable.map_map_of_aemeasurable hev.aemeasurable hY,
    AEMeasurable.map_map_of_aemeasurable hev.aemeasurable hX] at hmap
  change (∫ ω, ev (Y ω) ∂volume) =
    ∫ x, ev (X x)
      ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)
  calc
    (∫ ω, ev (Y ω) ∂volume) =
        ∫ z, z ∂Measure.map (ev ∘ Y) volume := by
      have hm := integral_map (hev.comp_aemeasurable hY)
        (f := id) aestronglyMeasurable_id
      simpa [Function.comp_apply] using hm.symm
    _ = ∫ z, z ∂Measure.map (ev ∘ X)
        (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
      rw [hmap]
    _ = ∫ x, ev (X x)
        ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) := by
      have hm := integral_map (hev.comp_aemeasurable hX)
        (f := id) aestronglyMeasurable_id
      simpa [Function.comp_apply] using hm

end SpinGlass.AT
