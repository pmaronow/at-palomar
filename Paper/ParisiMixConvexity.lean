module

public import Paper.ParisiHJB
public import Paper.JTVariational

@[expose] public section

/-! # Actual convexity along probability-measure mixing segments -/

open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Paper

theorem parisiMix_parisiMix (μ ν : ParisiMeasure) (a b θ : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    parisiMix (parisiMix μ ν a) (parisiMix μ ν b) θ =
      parisiMix μ ν ((1 - θ) * a + θ * b) := by
  have hθ1 := sub_nonneg.mpr hθ.2
  have ha1 := sub_nonneg.mpr ha.2
  have hb1 := sub_nonneg.mpr hb.2
  have hc : (1 - θ) * a + θ * b ∈ Icc (0 : ℝ) 1 := by
    refine ⟨add_nonneg (mul_nonneg hθ1 ha.1) (mul_nonneg hθ.1 hb.1), ?_⟩
    calc
      _ ≤ (1 - θ) * 1 + θ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left ha.2 hθ1) (mul_le_mul_of_nonneg_left hb.2 hθ.1)
      _ = 1 := by ring
  have hμ : ENNReal.ofReal (1 - θ) * ENNReal.ofReal (1 - a) +
      ENNReal.ofReal θ * ENNReal.ofReal (1 - b) =
      ENNReal.ofReal (1 - ((1 - θ) * a + θ * b)) := by
    rw [← ENNReal.ofReal_mul hθ1, ← ENNReal.ofReal_mul hθ.1,
      ← ENNReal.ofReal_add (mul_nonneg hθ1 ha1) (mul_nonneg hθ.1 hb1)]
    congr 1
    ring
  have hν : ENNReal.ofReal (1 - θ) * ENNReal.ofReal a +
      ENNReal.ofReal θ * ENNReal.ofReal b = ENNReal.ofReal ((1 - θ) * a + θ * b) := by
    rw [← ENNReal.ofReal_mul hθ1, ← ENNReal.ofReal_mul hθ.1,
      ← ENNReal.ofReal_add (mul_nonneg hθ1 ha.1) (mul_nonneg hθ.1 hb.1)]
  apply Subtype.ext
  change (parisiMix (parisiMix μ ν a) (parisiMix μ ν b) θ : Measure Overlap) =
    (parisiMix μ ν ((1 - θ) * a + θ * b) : Measure Overlap)
  rw [parisiMix_measure _ _ θ hθ, parisiMix_measure μ ν a ha,
    parisiMix_measure μ ν b hb, parisiMix_measure μ ν _ hc,
    smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    add_add_add_comm, ← add_smul, ← add_smul, hμ, hν]

/-- Convexity of the actual all-measure Parisi functional along every
genuine probability mixing segment, derived from actual HJB verification. -/
theorem convexOn_parisiPDEFunctional_mix (β h : ℝ) (μ ν : ParisiMeasure) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun θ => parisiPDEFunctional β h (parisiMix μ ν θ)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb u v hu hv huv
  have hv1 : v ∈ Icc (0 : ℝ) 1 := ⟨hv, by linarith⟩
  have hu1 : 1 - v = u := by linarith
  have he := parisiPDEFunctional_mix_le β h (parisiMix μ ν a) (parisiMix μ ν b) v hv1
  rw [parisiMix_parisiMix μ ν a b v ha hb hv1, hu1] at he
  simpa only [smul_eq_mul] using he

end Paper
