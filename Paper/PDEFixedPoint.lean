module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# A quantitative fixed point for the bounded-gradient Duhamel operator

The complete-space argument works on the closed norm ball of radius two.
Its hypotheses are operator estimates; the heat-kernel construction supplies
these estimates separately.
-/

open scoped NNReal

namespace Paper

theorem boundedGradient_fixedPoint {X : Type*} [NormedAddCommGroup X]
    [CompleteSpace X] (G : X → X) (K : ℝ) (hK : 0 ≤ K) (hsmall : K ≤ 1 / 8)
    (hsize : ∀ v, ‖G v‖ ≤ 1 + K * ‖v‖ ^ 2)
    (hlip : ∀ v w, ‖v‖ ≤ 2 → ‖w‖ ≤ 2 →
      ‖G v - G w‖ ≤ 4 * K * ‖v - w‖) :
    ∃! v : X, ‖v‖ ≤ 2 ∧ G v = v := by
  let S : Set X := {v | ‖v‖ ≤ 2}
  have hclosed : IsClosed S := isClosed_le continuous_norm continuous_const
  letI : CompleteSpace S := hclosed.isComplete.completeSpace_coe
  letI : Nonempty S := ⟨⟨0, by simp [S]⟩⟩
  have hmap : ∀ v : S, G v ∈ S := by
    intro v
    have hv : ‖(v : X)‖ ≤ 2 := v.property
    have hnorm := norm_nonneg (v : X)
    have hsq : ‖(v : X)‖ ^ 2 ≤ 4 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hK
    have hb := hsize (v : X)
    change ‖G (v : X)‖ ≤ 2
    linarith
  let F : S → S := fun v => ⟨G v, hmap v⟩
  let k : ℝ≥0 := NNReal.mk (4 * K) (by positivity)
  have hc : ContractingWith k F := by
    constructor
    · change 4 * K < 1
      linarith
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      change dist (G (v : X)) (G (w : X)) ≤ 4 * K * dist (v : X) (w : X)
      simpa only [dist_eq_norm] using hlip v w v.property w.property
  let v : S := hc.fixedPoint F
  have hv : G (v : X) = (v : X) := congrArg Subtype.val hc.fixedPoint_isFixedPt
  refine ⟨v, ⟨v.property, hv⟩, ?_⟩
  intro w hw
  let w' : S := ⟨w, hw.1⟩
  have hw' : Function.IsFixedPt F w' := by
    apply Subtype.ext
    exact hw.2
  exact congrArg Subtype.val (hc.fixedPoint_unique hw')

end Paper
