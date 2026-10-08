module

public import BrownianMotion.Gaussian.BrownianMotion
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-!
# A concrete continuous Brownian driver

The vendored Brownian foundation constructs the Gaussian projective limit
and its continuous Brownian modification. Here we expose the resulting
probability space and a measurable random continuous path on `[0,1]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

abbrev BrownianSample := ℝ≥0 → ℝ

/-- The probability measure constructed from the Gaussian projective family. -/
def canonicalBrownianMeasure : Measure BrownianSample := gaussianLimit

instance canonicalBrownianMeasure_isProbability : IsProbabilityMeasure canonicalBrownianMeasure :=
  inferInstanceAs (IsProbabilityMeasure gaussianLimit)

/-- A continuous Brownian version which starts at zero on every sample path. -/
def canonicalBrownian (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  brownian t ω - brownian 0 ω

@[simp] theorem canonicalBrownian_zero (ω : BrownianSample) : canonicalBrownian 0 ω = 0 := by
  simp [canonicalBrownian]

theorem measurable_canonicalBrownian (t : ℝ≥0) : Measurable (canonicalBrownian t) :=
  (measurable_brownian t).sub (measurable_brownian 0)

theorem continuous_canonicalBrownian (ω : BrownianSample) :
    Continuous (fun t => canonicalBrownian t ω) :=
  (continuous_brownian ω).sub continuous_const

theorem canonicalBrownian_ae_eq (t : ℝ≥0) :
    canonicalBrownian t =ᵐ[canonicalBrownianMeasure] brownian t := by
  filter_upwards [isBrownianReal_brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp [canonicalBrownian, hω]

/-- This is an actual Brownian process under the concrete constructed measure. -/
theorem isBrownianReal_canonicalBrownian :
    IsBrownianReal canonicalBrownian canonicalBrownianMeasure := by
  refine ⟨isBrownianReal_brownian.toIsPreBrownianReal.congr
    (fun t => (canonicalBrownian_ae_eq t).symm),
    Filter.Eventually.of_forall continuous_canonicalBrownian⟩

/-- Restrict the actual Brownian driver to a continuous path on `[0,1]`. -/
def canonicalBrownianPath (ω : BrownianSample) : C(Set.Icc (0 : ℝ) 1, ℝ) where
  toFun t := canonicalBrownian t.1.toNNReal ω
  continuous_toFun := (continuous_canonicalBrownian ω).comp
    (continuous_real_toNNReal.comp continuous_subtype_val)

theorem measurable_canonicalBrownianPath : Measurable canonicalBrownianPath := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_canonicalBrownian t.1.toNNReal

@[simp] theorem canonicalBrownianPath_zero (ω : BrownianSample) :
    canonicalBrownianPath ω ⟨0, by norm_num⟩ = 0 := by
  simp [canonicalBrownianPath]

/-- The induced probability law of continuous Brownian paths on `[0,1]`. -/
def canonicalWienerMeasure : Measure C(Set.Icc (0 : ℝ) 1, ℝ) :=
  canonicalBrownianMeasure.map canonicalBrownianPath

instance canonicalWienerMeasure_isProbability : IsProbabilityMeasure canonicalWienerMeasure := by
  unfold canonicalWienerMeasure
  infer_instance

end Paper
