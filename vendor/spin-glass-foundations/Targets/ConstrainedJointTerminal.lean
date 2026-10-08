module

public import Targets.ConstrainedFiniteState
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

@[expose] public section

/-!
# Joint differentiability of the actual constrained terminal

All disorder and physical-field coordinates are absorbed into RSAT's finite
state field. Its checked smooth log-partition function supplies joint, rather
than merely separate, differentiability. The overlap constraint is fixed and
attainable.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ContDiff

namespace SpinGlass.Targets

variable {n : ℕ}

/-- The constrained terminal is jointly smooth in its actual disorder and both
replica fields. -/
theorem contDiff_constrainedPairFieldBase_joint (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] :
    ContDiff ℝ ∞ (fun q : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      constrainedPairFieldBase n q.1 u q.2.1 q.2.2) := by
  classical
  let H : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) →
      AT.GTStateSpace (AT.ConstrainedPair n u) := fun q =>
    WithLp.toLp 2 (fun p => q.1 p.1.1 + q.1 p.1.2 + pairFieldPotential n u q.2.1 q.2.2 p)
  have hH : ContDiff ℝ ∞ H := by
    apply (contDiff_piLp 2).mpr
    intro p
    dsimp only [H, PiLp.toLp_apply, pairFieldPotential]
    fun_prop
  have hc := (AT.contDiff_gtStateLogPartition (fun _ : AT.ConstrainedPair n u => 0)).comp hH
  simpa only [Function.comp_def, constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
    AT.gtStatePartition, H, PiLp.toLp_apply, add_zero, pairDisorderCLM_apply] using! hc

/-- Joint differentiation of a genuine disorder path and the two independent
physical-field arguments, without a joint-regularity hypothesis on the terminal. -/
theorem differentiableAt_constrainedPairFieldBase_joint (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {U : ℝ → EnergySpace n} {w : ℝ}
    (hU : DifferentiableAt ℝ U w) (x y : Fin n → ℝ) :
    DifferentiableAt ℝ
      (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        constrainedPairFieldBase n (U q.1) u q.2.1 q.2.2) (w, x, y) := by
  have hmap : DifferentiableAt ℝ
      (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => (U q.1, q.2)) (w, x, y) :=
    (hU.comp (w, x, y) differentiableAt_fst).prodMk differentiableAt_snd
  have hF : DifferentiableAt ℝ
      (fun q : EnergySpace n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        constrainedPairFieldBase n q.1 u q.2.1 q.2.2) (U w, x, y) :=
    ((contDiff_constrainedPairFieldBase_joint u).differentiable (by simp)).differentiableAt
  simpa only [Function.comp_def] using hF.comp (w, x, y) hmap

end SpinGlass.Targets
