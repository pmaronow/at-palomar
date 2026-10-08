module

/-
# Coordinate Stein identity for a finite product of standard Gaussians

The hypotheses use only derivatives along coordinate lines.  This is the form
needed for the cascade-field integration by parts in Talagrand's Theorem 2.1.
-/
public import ParisiFormula.CoordStein

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open PhysLean.Probability.GaussianIBP

namespace SpinGlass

/-- Stein's identity for one coordinate of the standard product Gaussian,
without a Fréchet smoothness assumption. -/
theorem stein_pi_of_hasDerivAt {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) {F F' : (I → ℝ) → ℝ}
    (hline : ∀ z : I → ℝ, ∀ r : ℝ,
      HasDerivAt (fun u => F (z + u • Pi.single i 1)) (F' (z + r • Pi.single i 1)) r)
    (hFm : Measurable F) (hF'm : Measurable F')
    (hF : Integrable F (Measure.pi fun _ : I => gaussianReal 0 1))
    (hzF : Integrable (fun z => z i * F z) (Measure.pi fun _ : I => gaussianReal 0 1))
    (hF' : Integrable F' (Measure.pi fun _ : I => gaussianReal 0 1)) :
    (∫ z, z i * F z ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z, F' z ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
  let pull : (I → ℝ) → EuclideanSpace ℝ I := WithLp.toLp 2
  letI : MeasureSpace (I → ℝ) := ⟨Measure.pi fun _ : I => gaussianReal 0 1⟩
  letI : IsProbabilityMeasure (ℙ : Measure (I → ℝ)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : I => gaussianReal 0 1))
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi fun _ : I => gaussianReal 0 1) = gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
  }
  have hd : ∀ z : EuclideanSpace ℝ I, ∀ r : ℝ,
      HasDerivAt (fun u => F (WithLp.ofLp (z + u • hg.w i)))
        (F' (WithLp.ofLp (z + r • hg.w i))) r := by
    intro z r
    simpa only [hg, EuclideanSpace.basisFun_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
      EuclideanSpace.single, PiLp.single, WithLp.ofLp_toLp] using hline (WithLp.ofLp z) r
  have hs := stein_coord_of_hasDerivAt hg i
    (Φ := fun z => F (WithLp.ofLp z)) (Φ' := fun z => F' (WithLp.ofLp z)) hd
    (hFm.comp (WithLp.measurable_ofLp 2 (I → ℝ)))
    (hF'm.comp (WithLp.measurable_ofLp 2 (I → ℝ))) hzF hF hF'
  change (∫ z, z i * F z ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
    (1 : ℝ) * ∫ z, F' z ∂Measure.pi (fun _ : I => gaussianReal 0 1) at hs
  simpa only [one_mul] using hs

end SpinGlass
