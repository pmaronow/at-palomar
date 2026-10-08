module

public import Paper.ATApproximation
public import Paper.RSContinuity
public import Paper.FiniteContinuity

@[expose] public section

/-!
# Closing the strict AT region

The extension uses explicit strict-AT perturbations, continuity of the actual
Gaussian RS expression, and a finite-volume parameter estimate independent of
the number of spins. The strict-region convergence is an ordinary theorem
input, isolated for the verified strict-region backend to discharge.
-/

open Filter
open scoped Topology

namespace Paper

/-- The precise strict-region statement needed to obtain the paper's closed
AT-region statement. This is a proposition, not an axiom. -/
def StrictReplicaSymmetryTarget : Prop :=
  ∀ β h q : ℝ, 0 < β → 0 < h → q ∈ Set.Icc (0 : ℝ) 1 →
    q = overlapMap β h q → atParameter β h q < 1 →
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (rsFreeEnergy β h q))

/-- Actual RS values converge along the explicit strict-AT perturbation. -/
theorem tendsto_rsFreeEnergy_atStrictApprox (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q) :
    Tendsto (fun ε : ℝ => rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε)
        (atStrictApproxOverlap β h q ε)) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (rsFreeEnergy β h q)) := by
  have hc : Tendsto (fun p : ℝ × ℝ × ℝ => rsFreeEnergy p.1 p.2.1 p.2.2)
      (𝓝 (β, h, q)) (𝓝 (rsFreeEnergy β h q)) :=
    Continuous.tendsto (f := fun p : ℝ × ℝ × ℝ => rsFreeEnergy p.1 p.2.1 p.2.2)
      continuous_rsFreeEnergy_joint (β, h, q)
  exact Filter.Tendsto.comp
    (f := fun ε : ℝ => (atStrictApproxBeta β h q ε, h + ε, atStrictApproxOverlap β h q ε))
    (g := fun p : ℝ × ℝ × ℝ => rsFreeEnergy p.1 p.2.1 p.2.2)
    hc (tendsto_atStrictApprox_point_zero_right β h q hβ hh hq hfixed)

/-- A uniform finite-volume comparison closes the AT region. All continuity
and approximation claims in this statement refer to the concrete model. -/
theorem mainReplicaSymmetry_of_strict (hstrict : StrictReplicaSymmetryTarget) :
    MainReplicaSymmetryTarget := by
  intro β h q hβ hh hq hfixed hα
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hδ3 : 0 < δ / 3 := by positivity
  have hqpos := fixedPoint_pos hh hq.1 hfixed
  have hb := tendsto_atStrictApproxBeta_zero_right β h q hβ hqpos hfixed
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) :=
    (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ)))
  have hparameter : Tendsto
      (fun ε : ℝ => skParameterLipschitz * |atStrictApproxBeta β h q ε - β| + |ε|)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => skParameterLipschitz)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 skParameterLipschitz) := tendsto_const_nhds
    have hβc : Tendsto (fun _ : ℝ => β)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 β) := tendsto_const_nhds
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      (hc.mul (hb.sub hβc).abs).add he.abs
  have hrs := tendsto_rsFreeEnergy_atStrictApprox β h q hβ hh hq hfixed
  have hrserror : Tendsto
      (fun ε : ℝ => |rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε)
          (atStrictApproxOverlap β h q ε) - rsFreeEnergy β h q|)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => rsFreeEnergy β h q)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (rsFreeEnergy β h q)) := tendsto_const_nhds
    simpa only [sub_self, abs_zero] using (hrs.sub hc).abs
  have hsmall := (hparameter.eventually (eventually_lt_nhds hδ3)).and
    ((hrserror.eventually (eventually_lt_nhds hδ3)).and
      (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < ε))
  obtain ⟨ε, hεparameter, hεRS, hεpos⟩ := hsmall.exists
  obtain ⟨hβε, hhε, hqε, hfixedε, hαε⟩ :=
    atStrictApprox_properties β h q ε hβ hh hq hfixed hα hεpos
  have hlimit := hstrict (atStrictApproxBeta β h q ε) (h + ε)
    (atStrictApproxOverlap β h q ε) hβε hhε ⟨hqε.1.le, hqε.2.le⟩ hfixedε hαε
  have hevent := Metric.tendsto_nhds.mp hlimit (δ / 3) hδ3
  filter_upwards [hevent] with n hn
  rw [Real.dist_eq] at hn ⊢
  have hfinite := finiteSKFreeEnergy_parameters_lipschitz β h
    (atStrictApproxBeta β h q ε) (h + ε) n
  rw [abs_sub_comm β, show h - (h + ε) = -ε by ring, abs_neg] at hfinite
  have htri : |finiteSKFreeEnergy β h n - rsFreeEnergy β h q| ≤
      |finiteSKFreeEnergy β h n - finiteSKFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) n| +
      |finiteSKFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) n -
        rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) (atStrictApproxOverlap β h q ε)| +
      |rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) (atStrictApproxOverlap β h q ε) -
        rsFreeEnergy β h q| := by
    have h1 := abs_add_le
      (finiteSKFreeEnergy β h n - finiteSKFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) n)
      (finiteSKFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) n - rsFreeEnergy β h q)
    have h2 := abs_add_le
      (finiteSKFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) n -
        rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) (atStrictApproxOverlap β h q ε))
      (rsFreeEnergy (atStrictApproxBeta β h q ε) (h + ε) (atStrictApproxOverlap β h q ε) -
        rsFreeEnergy β h q)
    simp only [sub_add_sub_cancel] at h1 h2
    linarith
  linarith

end Paper
