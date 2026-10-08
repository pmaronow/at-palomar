module

public import Targets.CoupledPathContinuity

@[expose] public section

/-!
# Continuity along actual constrained disorder and field paths

RSAT's finite-state log partition handles simultaneous changes of the terminal
disorder and both physical fields. Compact parameter sets bound the disorder,
so the existing terminal growth estimate is uniform in the parameter. The
checked finite-step continuity rule then covers all original field variances
varying simultaneously, including their zero-variance faces.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P] {n : ℕ}

/-- Simultaneous disorder/field continuity of the actual constrained terminal.
No differentiability, compactness, or Gaussian assumption is required here. -/
theorem continuousOn_constrainedPairFieldBase_paths (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P}
    {U : P → EnergySpace n} {x y : P → Fin n → ℝ}
    (hU : ContinuousOn U S) (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun z => constrainedPairFieldBase n (U z) u (x z) (y z)) S := by
  classical
  let H : P → AT.GTStateSpace (AT.ConstrainedPair n u) := fun z =>
    WithLp.toLp 2 (fun p => U z p.1.1 + U z p.1.2 + pairFieldPotential n u (x z) (y z) p)
  have hH : ContinuousOn H S := by
    apply (PiLp.continuous_toLp (p := 2) (fun _ : AT.ConstrainedPair n u => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro p
    unfold pairFieldPotential
    fun_prop
  have hc := ((AT.contDiff_gtStateLogPartition (fun _ : AT.ConstrainedPair n u => 0)).continuous).comp_continuousOn hH
  simpa only [Function.comp_def, constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
    AT.gtStatePartition, H, PiLp.toLp_apply, add_zero, pairDisorderCLM_apply] using! hc

/-- The actual constrained terminal has uniform linear field growth along any
continuous disorder path on a compact parameter set. -/
theorem constrainedPairFieldBase_uniform_growth_on_compact (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P} (hS : IsCompact S)
    {U : P → EnergySpace n} (hU : ContinuousOn U S) :
    ∃ C D : ℝ, 0 ≤ D ∧ ∀ z ∈ S, ∀ x y : Fin n → ℝ,
      |constrainedPairFieldBase n (U z) u x y| ≤ C + D * (l1 x + l1 y) := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hU
  have hzero := (constrainedPairFieldBase_paramDeriv (0 : EnergySpace n) 0 u 0).growth_at
    (a := 0) (by constructor <;> norm_num [guerraLineNbhd])
  obtain ⟨C, D, hD, hb⟩ := hzero.bound
  refine ⟨C + 2 * (Fintype.card (Config n) : ℝ) * M, D, hD, ?_⟩
  intro z hz x y
  have hbase : |constrainedPairFieldBase n 0 u x y| ≤ C + D * (l1 x + l1 y) := by
    simpa only [zero_smul, add_zero] using hb x y
  have hdiff := constrainedPairFieldBase_dist_zero (U z) u x y
  have hUbound := (uAbs_le_card_mul_norm n (U z)).trans
    (mul_le_mul_of_nonneg_left (hM z hz) (by positivity))
  have htri := abs_add_le
    (constrainedPairFieldBase n (U z) u x y - constrainedPairFieldBase n 0 u x y)
    (constrainedPairFieldBase n 0 u x y)
  rw [sub_add_cancel] at htri
  nlinarith

/-- The compact-parameter continuity API is satisfied by the actual terminal;
all of its measurability and uniform growth hypotheses are discharged. -/
theorem coupledContinuousOn_constrainedPairFieldBase (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P} (hS : IsCompact S)
    {U : P → EnergySpace n} (hU : ContinuousOn U S) :
    CoupledContinuousOn (fun z => constrainedPairFieldBase n (U z) u) S := by
  classical
  refine ⟨?_, constrainedPairFieldBase_uniform_growth_on_compact u hS hU,
    fun x y hx hy => continuousOn_constrainedPairFieldBase_paths u hU hx hy⟩
  intro z _
  simp only [constrainedPairFieldBase_eq_gtStateLogPartition, AT.gtStateLogPartition,
    AT.gtStatePartition, pairFieldPotential]
  fun_prop

variable [FirstCountableTopology P]

/-- Actual full-cascade continuity and uniform field growth, with simultaneous
continuous disorder and variance paths. Zero masses and variances are allowed. -/
theorem coupledContinuousOn_constrainedPairFieldCascade (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P} (hS : IsCompact S)
    {U : P → EnergySpace n} (hU : ContinuousOn U S)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hvc : ∀ j, ContinuousOn (v j) S) (hv : ∀ j z, z ∈ S → 0 ≤ v j z)
    (d j : ℕ) :
    CoupledContinuousOn (fun z => coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (U z) u) j) S :=
  (coupledContinuousOn_constrainedPairFieldBase u hS hU).fieldCascade hS m v hm hvc hv d j

/-- Joint continuity along actual disorder, variance, and physical-field paths.
No abstract regularity or growth assumptions on the cascade remain. -/
theorem continuousOn_constrainedPairFieldCascade_paths (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P} (hS : IsCompact S)
    {U : P → EnergySpace n} (hU : ContinuousOn U S)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hvc : ∀ j, ContinuousOn (v j) S) (hv : ∀ j z, z ∈ S → 0 ≤ v j z)
    (d j : ℕ) {x y : P → Fin n → ℝ} (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun z => coupledFieldCascade n m (fun l => v l z) d
      (constrainedPairFieldBase n (U z) u) j (x z) (y z)) S :=
  (coupledContinuousOn_constrainedPairFieldCascade u hS hU m v hm hvc hv d j).continuous x y hx hy

end SpinGlass.Targets
