module

public import Paper.DiracState
public import Paper.CanonicalBrownian

@[expose] public section

/-!
# A concrete strong Dirac state driven by constructed Brownian motion

The actual state is the measurable, causal Picard–Lindelöf image of the
canonical continuous Brownian path. It satisfies the additive-noise integral
equation on every sample path and is adapted to the driver's natural filtration.
The Gaussian state law before the Dirac interface is identified explicitly.
The post-interface transition-law identification is a separate theorem.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

/-- A real-time continuous extension of the canonical Brownian driver on `[0,1]`. -/
def canonicalDiracNoise (ω : BrownianSample) : ℝ → ℝ :=
  compactNoiseExtension 0 1 zero_le_one (canonicalBrownianPath ω)

theorem continuous_canonicalDiracNoise (ω : BrownianSample) :
    Continuous (canonicalDiracNoise ω) :=
  continuous_compactNoiseExtension 0 1 zero_le_one _

theorem canonicalDiracNoise_eq (ω : BrownianSample) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    canonicalDiracNoise ω t = canonicalBrownian t.toNNReal ω := by
  simp only [canonicalDiracNoise, compactNoiseExtension, projIcc_of_mem zero_le_one ht]
  rfl

@[simp] theorem canonicalDiracNoise_zero (ω : BrownianSample) : canonicalDiracNoise ω 0 = 0 := by
  rw [canonicalDiracNoise_eq ω (by norm_num)]
  simp

/-- The actual continuous state, extended constantly in its ODE correction
outside the physical interval. -/
def canonicalDiracStateReal (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : ℝ → ℝ :=
  diracState β h q hq.2 (canonicalDiracNoise ω) (continuous_canonicalDiracNoise ω)

/-- The random continuous state path on `[0,1]`. -/
def canonicalDiracStatePath (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    BrownianSample → C(Icc (0 : ℝ) 1, ℝ) :=
  fun ω => diracStatePath β h q hq (canonicalBrownianPath ω)

/-- The actual state process indexed by physical time. -/
def canonicalDiracState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (t : Icc (0 : ℝ) 1) (ω : BrownianSample) : ℝ :=
  canonicalDiracStatePath β h q hq ω t

theorem measurable_canonicalDiracStatePath (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    Measurable (canonicalDiracStatePath β h q hq) :=
  measurable_random_diracStatePath β h q hq measurable_canonicalBrownianPath

theorem continuous_canonicalDiracStateReal (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : Continuous (canonicalDiracStateReal β h q hq ω) :=
  continuous_diracState β h q hq.2 _ _

@[simp] theorem canonicalDiracState_initial (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) : canonicalDiracStateReal β h q hq ω 0 = h :=
  diracState_initial β h q hq _ _ (canonicalDiracNoise_zero ω)

/-- This constructed state solves the actual continuous integral equation. -/
theorem canonicalDiracState_spec (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) :
    IsDiracStateSolution β h q (canonicalDiracNoise ω) (canonicalDiracStateReal β h q hq ω) :=
  diracState_spec β h q hq _ _

/-- Exact Brownian state equation before the interface. -/
theorem canonicalDiracState_before (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    canonicalDiracStateReal β h q hq ω t = h + β * canonicalBrownian t.toNNReal ω := by
  rw [(canonicalDiracState_spec β h q hq ω).before t ht,
    canonicalDiracNoise_eq ω ⟨ht.1, ht.2.trans hq.2⟩]

/-- Exact post-interface additive-noise SDE in integral form. -/
theorem canonicalDiracState_after (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    canonicalDiracStateReal β h q hq ω t = h + β * canonicalBrownian t.toNNReal ω +
      ∫ s in q..t, β ^ 2 * Real.tanh (canonicalDiracStateReal β h q hq ω s) := by
  rw [(canonicalDiracState_spec β h q hq ω).after t ht,
    canonicalDiracNoise_eq ω ⟨hq.1.trans ht.1, ht.2⟩]

/-- Strong pathwise uniqueness for the actual Brownian state integral equation. -/
theorem canonicalDiracState_unique (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (ω : BrownianSample) {X : ℝ → ℝ}
    (hX : IsDiracStateSolution β h q (canonicalDiracNoise ω) X) :
    EqOn X (canonicalDiracStateReal β h q hq ω) (Icc (0 : ℝ) 1) :=
  hX.eqOn hq (canonicalDiracState_spec β h q hq ω)

/-- Adaptedness to the natural filtration of the actual Brownian driver. -/
theorem adapted_canonicalDiracState (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    Adapted (diracNoiseFiltration canonicalBrownianPath measurable_canonicalBrownianPath)
      (canonicalDiracState β h q hq) :=
  adapted_diracStatePath β h q hq canonicalBrownianPath measurable_canonicalBrownianPath

/-- Before the interface, the actual state has the specified shifted Gaussian law. -/
theorem hasLaw_canonicalDiracState_before (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    HasLaw (fun ω => canonicalDiracStateReal β h q hq ω t)
      (gaussianReal h (β ^ 2 * t).toNNReal) canonicalBrownianMeasure := by
  have hl := gaussianReal_const_add (gaussianReal_const_mul
    (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval t.toNNReal) β) h
  have hv : NNReal.mk (β ^ 2) (sq_nonneg β) * t.toNNReal = (β ^ 2 * t).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ ht.1,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) ht.1)]
  have he : (fun ω => canonicalDiracStateReal β h q hq ω t) =
      fun ω => h + β * canonicalBrownian t.toNNReal ω :=
    funext (fun ω => canonicalDiracState_before β h q hq ω ht)
  rw [he]
  simpa only [mul_zero, zero_add, hv] using hl

end Paper
