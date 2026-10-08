module

public import Targets.CoupledNestedVariance
public import Targets.CascadeContinuityPi

@[expose] public section

/-!
# Continuity of the actual cascade with all variances varying

Compact parameter sets supply uniform growth bounds. Every smoothing step is
reduced to the existing fixed-variance continuity theorem by placing the moving
Gaussian coefficient in its input. No variance-endpoint derivative is used.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] {n p : ℕ}

/-- Uniform growth and continuity along continuous physical-field paths. The
parameter may itself include both fields and every original variance. -/
structure CoupledContinuousOn (A : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (S : Set P) : Prop where
  measurable : ∀ z ∈ S, Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => A z q.1 q.2)
  growth : ∃ C D : ℝ, 0 ≤ D ∧ ∀ z ∈ S, ∀ x y, |A z x y| ≤ C + D * (l1 x + l1 y)
  continuous : ∀ x y : P → Fin n → ℝ, ContinuousOn x S → ContinuousOn y S →
    ContinuousOn (fun z => A z (x z) (y z)) S

omit [FirstCountableTopology P] in
theorem CoupledContinuousOn.growth_at {A : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {S : Set P} (hA : CoupledContinuousOn A S) {z : P} (hz : z ∈ S) : CoupledGrowth (A z) := by
  obtain ⟨C, D, hD, hb⟩ := hA.growth
  exact ⟨hA.measurable z hz, C, D, hD, hb z hz⟩

/-- One actual finite-direction Gaussian step preserves compact-parameter
continuity, including its zero-mass and zero-variance branches. -/
theorem CoupledContinuousOn.linearStep
    {F : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) (hS : IsCompact S)
    (A B : Fin p → Fin n → ℝ) {mass : ℝ} (hm : 0 ≤ mass)
    {v : P → ℝ} (hvc : ContinuousOn v S) (hv : ∀ z ∈ S, 0 ≤ v z) :
    CoupledContinuousOn (fun z => coupledLinearStep mass (v z) A B (F z)) S := by
  obtain ⟨C, D, hD, hb⟩ := hF.growth
  obtain ⟨V, hV⟩ := hS.bddAbove_image hvc
  let L := ∑ i, (l1 (A i) + l1 (B i))
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  have hDL : 0 ≤ D * L := mul_nonneg hD hL
  refine ⟨fun z hz => measurable_coupledLinearStep (hF.measurable z hz) A B mass (v z),
    ⟨C + stepK p mass V (D * L), D, hD, ?_⟩, ?_⟩
  · intro z hz x y
    have H := parisiStepPi_abs_le (C := C + D * (l1 x + l1 y)) hm (hv z hz) hDL
      (coupled_linear_growth_bound hD (hb z hz) A B x y)
      ((hF.growth_at hz).linear_input A B x y).measurable (0 : Fin p → ℝ)
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at H
    have HK := stepK_mono_variance (n := p) hm hDL (hV (Set.mem_image_of_mem v hz))
    change |parisiStepPi p mass (v z) _ 0| ≤ _
    nlinarith
  · intro x y hx hy
    have hxy : ContinuousOn (fun z => l1 (x z) + l1 (y z)) S := by
      unfold l1
      fun_prop
    obtain ⟨X, hX⟩ := hS.bddAbove_image hxy
    let G := fun (z : P) (a : Fin p → ℝ) => F z
      (x z + pairedFieldLinear A (fun i => Real.sqrt (v z) * a i))
      (y z + pairedFieldLinear B (fun i => Real.sqrt (v z) * a i))
    have hGm (z : P) (hz : z ∈ S) : Measurable (G z) := by
      exact (hF.measurable z hz).comp
        ((measurable_const.add ((measurable_pairedFieldLinear A).comp (by fun_prop))).prodMk
          (measurable_const.add ((measurable_pairedFieldLinear B).comp (by fun_prop))))
    have hGb (z : P) (hz : z ∈ S) (a : Fin p → ℝ) :
        |G z a| ≤ (C + D * X) + (D * L * Real.sqrt V) * l1 a := by
      have H := coupled_linear_growth_bound hD (hb z hz) A B (x z) (y z)
        (fun i => Real.sqrt (v z) * a i)
      rw [l1_const_smul, abs_of_nonneg (Real.sqrt_nonneg _)] at H
      have HX := mul_le_mul_of_nonneg_left (hX (Set.mem_image_of_mem _ hz)) hD
      have HV := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hV (Set.mem_image_of_mem _ hz))) (mul_nonneg hDL (l1_nonneg a))
      change |G z a| ≤ _ at H
      dsimp [L] at *
      nlinarith
    have hGc (a : Fin p → ℝ) : ContinuousOn (fun z => G z a) S := by
      apply hF.continuous
      · unfold pairedFieldLinear
        fun_prop
      · unfold pairedFieldLinear
        fun_prop
    have H := continuousOn_parisiStepPi_param (m := mass) (v := 1)
      (mul_nonneg hDL (Real.sqrt_nonneg V)) hGm hGb hGc (0 : Fin p → ℝ)
    simpa only [G, coupledLinearStep, parisiStepPi, Real.sqrt_one, Pi.zero_apply,
      zero_add, one_mul] using! H

/-- All original Gaussian variances may vary simultaneously. -/
theorem CoupledContinuousOn.fieldCascade
    {F : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) (hS : IsCompact S)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hvc : ∀ j, ContinuousOn (v j) S) (hv : ∀ j z, z ∈ S → 0 ≤ v j z)
    (d j : ℕ) :
    CoupledContinuousOn (fun z => coupledFieldCascade n m (fun l => v l z) d (F z) j) S := by
  induction j with
  | zero => exact hF
  | succ j ih =>
    by_cases hj : j < d
    · simpa only [coupledFieldCascade, if_pos hj, coupledLinearStep_independent] using
        ih.linearStep hS (independentLeftDirection n) (independentRightDirection n)
          (hm j) (hvc j) (hv j)
    · simpa only [coupledFieldCascade, if_neg hj, coupledLinearStep_shared] using
        ih.linearStep hS (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1)
          (hm j) (hvc j) (hv j)

end SpinGlass.Targets
