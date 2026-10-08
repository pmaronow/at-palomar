module

public import Paper.ParisiTerminalOperator
public import Paper.QuadraticImplicit
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! # Local Parisi mixture derivatives with changing terminal data

A genuine Gaussian terminal heat operator and the concrete quadratic
Duhamel correction enter a smooth implicit equation. Its inverse exists
by the proved slab norm bound. This supplies the derivative needed to
continue a probability-mixture variation backward across time slabs.
-/

open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff

namespace Paper

set_option maxHeartbeats 2000000

private noncomputable def parisiVariationBilinearNorm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) : ℝ := ‖B‖

private theorem parisiVariationBilinearNorm_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ v w, ‖B v w‖ ≤ C * ‖v‖ * ‖w‖) : parisiVariationBilinearNorm B ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound B hC
  intro v
  apply ContinuousLinearMap.opNorm_le_bound (B v) (mul_nonneg hC (norm_nonneg v))
  exact hb v

private noncomputable def affineBilinearOperator {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B D : X →L[𝕜] X →L[𝕜] X) (p : 𝕜 × X) : X →L[𝕜] X →L[𝕜] X :=
  (ContinuousLinearMap.toSpanSingleton 𝕜 B) (1 - p.1) +
    (ContinuousLinearMap.toSpanSingleton 𝕜 D) p.1

private theorem contDiff_affineBilinearOperator {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B D : X →L[𝕜] X →L[𝕜] X) : ContDiff 𝕜 ∞ (affineBilinearOperator B D) :=
  (((ContinuousLinearMap.toSpanSingleton 𝕜 B).contDiff).comp
    (contDiff_const.sub contDiff_fst)).add
      ((ContinuousLinearMap.toSpanSingleton 𝕜 D).contDiff.comp contDiff_fst)

/-- The actual local mixture family is continuous when its terminal gradient is continuous. -/
theorem continuousWithinAt_localParisiGradient_terminal_mix
    (β : ℝ) (μ ν : ParisiMeasure) {a b : ℝ} (hab : a ≤ b)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (g : ℝ → (ℝ →ᵇ ℝ)) (v : ℝ → ParisiSlabGradient a b)
    (hgb : ∀ ε x, ‖g ε x‖ ≤ 1) (hvb : ∀ ε, ‖v ε‖ ≤ 2)
    (hfix : ∀ ε ∈ Icc (0 : ℝ) 1,
      parisiSlabGradientOperator β (parisiMix μ ν ε) hab (g ε) (g ε).continuous (hgb ε)
        (v ε) = v ε)
    (hg : ContinuousWithinAt g (Icc (0 : ℝ) 1) 0) :
    ContinuousWithinAt v (Icc (0 : ℝ) 1) 0 := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (.of_forall fun ε => norm_nonneg (v ε - v 0))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have h0 := hfix 0 (by norm_num)
    simp only [parisiMix_zero] at h0
    have h := localParisiGradient_terminal_mix_stability β μ ν hab (g 0) (g ε)
      (hgb 0) (hgb ε) hshort (v 0) (v ε) (hvb 0) (hvb ε) ε hε h0 (hfix ε hε)
    simpa only [norm_sub_rev] using h
  · have hnorm : Tendsto (fun ε => ‖g ε - g 0‖) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
      simpa using (hg.tendsto.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => g 0) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (g 0)))).norm
    simpa using (tendsto_const_nhds.mul hnorm).add
      (tendsto_const_nhds.mul nhdsWithin_le_nhds)

/-- Local differentiability with an actually varying bounded terminal gradient.
All fixed-point and norm assumptions refer to the genuine Duhamel operator. -/
theorem differentiableWithinAt_localParisiGradient_terminal_mix
    (β : ℝ) (μ ν : ParisiMeasure) {a b : ℝ} (hab : a ≤ b)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (g : ℝ → (ℝ →ᵇ ℝ)) (v : ℝ → ParisiSlabGradient a b)
    (k : ℝ →ᵇ ℝ) (hgb : ∀ ε x, ‖g ε x‖ ≤ 1) (hvb : ∀ ε, ‖v ε‖ ≤ 2)
    (hfix : ∀ ε ∈ Icc (0 : ℝ) 1,
      parisiSlabGradientOperator β (parisiMix μ ν ε) hab (g ε) (g ε).continuous (hgb ε)
        (v ε) = v ε)
    (hg : HasDerivWithinAt g k (Icc (0 : ℝ) 1) 0) :
    DifferentiableWithinAt ℝ v (Icc (0 : ℝ) 1) 0 := by
  let B := parisiSlabBilinearOperator β μ hab
  let D := parisiSlabBilinearOperator β ν hab
  let H := parisiSlabTerminalHeatOperator β hab
  let p0 : ℝ × ParisiSlabGradient a b := (0, H (g 0))
  have hBnorm : parisiVariationBilinearNorm B ≤ parisiSlabContractionConstant β a b :=
    parisiVariationBilinearNorm_le B _ (parisiSlabContractionConstant_nonneg β a b)
      (norm_parisiSlabBilinearOperator_apply_le β μ hab)
  have h0 := hfix 0 (by norm_num)
  simp only [parisiMix_zero, parisiSlabGradientOperator_eq_terminalHeat_add_quadratic,
    parisiSlabQuadraticOperator_eq_bilinear] at h0
  have hbase : v 0 = p0.2 + affineBilinearOperator B D p0 (v 0) (v 0) := by
    simpa only [affineBilinearOperator, p0, sub_zero, map_zero, add_zero,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h0.symm
  have hsmall : 2 * parisiVariationBilinearNorm (affineBilinearOperator B D p0) * ‖v 0‖ < 1 := by
    simp only [affineBilinearOperator, p0, sub_zero, map_zero, add_zero,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    have hC := parisiSlabContractionConstant_nonneg β a b
    have hN := parisiVariationBilinearNorm_le B _ hC
      (norm_parisiSlabBilinearOperator_apply_le β μ hab)
    have hprod := mul_le_mul_of_nonneg_right hN (norm_nonneg (v 0))
    have hbound := mul_le_mul_of_nonneg_left (hvb 0) hC
    nlinarith
  obtain ⟨ψ, hψ0, hψ, hψunique⟩ := quadratic_local_solution
    (affineBilinearOperator B D) (fun p : ℝ × ParisiSlabGradient a b => p.2)
    p0 (v 0) (contDiff_affineBilinearOperator B D).contDiffAt contDiffAt_snd hbase hsmall
  let p : ℝ → ℝ × ParisiSlabGradient a b := fun ε => (ε, H (g ε))
  have hp : HasDerivWithinAt p (1, H k) (Icc (0 : ℝ) 1) 0 :=
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.prodMk
      (H.hasFDerivAt.comp_hasDerivWithinAt 0 hg)
  have hv := continuousWithinAt_localParisiGradient_terminal_mix β μ ν hab hshort g v hgb hvb
    hfix hg.continuousWithinAt
  have hpair : Tendsto (fun ε => (p ε, v ε)) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (p0, v 0)) :=
    hp.continuousWithinAt.tendsto.prodMk_nhds hv.tendsto
  have he : (fun ε => ψ (p ε)) =ᶠ[𝓝[Icc (0 : ℝ) 1] 0] v := by
    filter_upwards [hpair.eventually hψunique, self_mem_nhdsWithin] with ε hψu hε
    apply hψu.mp
    have hf := hfix ε hε
    rw [parisiSlabGradientOperator_eq_terminalHeat_add_quadratic,
      parisiSlabQuadraticOperator_eq_bilinear,
      parisiSlabBilinearOperator_mix_apply β μ ν hab ε hε] at hf
    exact hf.symm
  have hd := (hψ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivWithinAt 0 hp
  exact (hd.congr_of_eventuallyEq he.symm hψ0.symm).differentiableWithinAt

private theorem hasDerivWithinAt_affineQuadratic {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedCommRing X] [NormedAlgebra 𝕜 X]
    (A B : X →L[𝕜] X) (v : 𝕜 → X) (w : X) (s : Set 𝕜)
    (hv : HasDerivWithinAt v w s 0) :
    HasDerivWithinAt (fun ε => (1 - ε) • A (v ε * v ε) + ε • B (v ε * v ε))
      (B (v 0 * v 0) - A (v 0 * v 0) + (2 : 𝕜) • A (v 0 * w)) s 0 := by
  have hA := A.hasFDerivAt.comp_hasDerivWithinAt 0 (hv.mul hv)
  have hB := B.hasFDerivAt.comp_hasDerivWithinAt 0 (hv.mul hv)
  have hId := (hasDerivAt_id (0 : 𝕜)).hasDerivWithinAt (s := s)
  have hOne := (hasDerivAt_const (0 : 𝕜) (1 : 𝕜)).hasDerivWithinAt (s := s)
  have h := ((hOne.sub hId).smul hA).add (hId.smul hB)
  have hmul : w * v 0 + v 0 * w = (2 : 𝕜) • (v 0 * w) := by
    simp only [two_smul 𝕜]
    rw [mul_comm w (v 0)]
  convert! h using 1
  simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply,
    id_eq, sub_zero, zero_sub, zero_smul, one_smul, hmul, map_smul]
  module

/-- Differentiating the genuine quadratic Duhamel correction along an actual mixture. -/
theorem hasDerivWithinAt_parisiSlabQuadraticOperator_mix
    (β : ℝ) (μ ν : ParisiMeasure) {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → ParisiSlabGradient a b) (w : ParisiSlabGradient a b)
    (hv : HasDerivWithinAt v w (Icc (0 : ℝ) 1) 0) :
    HasDerivWithinAt (fun ε => parisiSlabQuadraticOperator β (parisiMix μ ν ε) hab (v ε))
      (parisiSlabQuadraticOperator β ν hab (v 0) - parisiSlabQuadraticOperator β μ hab (v 0) +
        parisiSlabLinearizedOperator β μ hab (v 0) w) (Icc (0 : ℝ) 1) 0 := by
  have h := hasDerivWithinAt_affineQuadratic
    (parisiSlabLinearOperator β μ hab) (parisiSlabLinearOperator β ν hab) v w
    (Icc (0 : ℝ) 1) hv
  have hd : parisiSlabLinearOperator β ν hab (v 0 * v 0) -
      parisiSlabLinearOperator β μ hab (v 0 * v 0) +
        (2 : ℝ) • parisiSlabLinearOperator β μ hab (v 0 * w) =
      parisiSlabQuadraticOperator β ν hab (v 0) - parisiSlabQuadraticOperator β μ hab (v 0) +
        parisiSlabLinearizedOperator β μ hab (v 0) w := by
    simp only [parisiSlabQuadraticOperator_eq_bilinear, parisiSlabLinearizedOperator_apply,
      parisiSlabBilinearOperator_apply]
  apply (h.congr_deriv hd).congr
  · intro ε hε
    rw [parisiSlabQuadraticOperator_eq_bilinear,
      parisiSlabBilinearOperator_mix_apply β μ ν hab ε hε]
    rfl
  · simp only [parisiMix_zero, parisiSlabQuadraticOperator_eq_bilinear,
      parisiSlabBilinearOperator_apply, sub_zero, one_smul, zero_smul, add_zero]

/-- The actual local family has a derivative solving the inhomogeneous Gaussian
linearized equation, including the genuinely varying terminal derivative. -/
theorem exists_localParisiGradient_terminal_mix_derivative
    (β : ℝ) (μ ν : ParisiMeasure) {a b : ℝ} (hab : a ≤ b)
    (hshort : parisiSlabContractionConstant β a b ≤ 1 / 8)
    (g : ℝ → (ℝ →ᵇ ℝ)) (v : ℝ → ParisiSlabGradient a b)
    (k : ℝ →ᵇ ℝ) (hgb : ∀ ε x, ‖g ε x‖ ≤ 1) (hvb : ∀ ε, ‖v ε‖ ≤ 2)
    (hfix : ∀ ε ∈ Icc (0 : ℝ) 1,
      parisiSlabGradientOperator β (parisiMix μ ν ε) hab (g ε) (g ε).continuous (hgb ε)
        (v ε) = v ε)
    (hg : HasDerivWithinAt g k (Icc (0 : ℝ) 1) 0) :
    ∃ w : ParisiSlabGradient a b,
      HasDerivWithinAt v w (Icc (0 : ℝ) 1) 0 ∧
      w = parisiSlabTerminalHeatOperator β hab k +
        (parisiSlabQuadraticOperator β ν hab (v 0) - parisiSlabQuadraticOperator β μ hab (v 0) +
          parisiSlabLinearizedOperator β μ hab (v 0) w) := by
  have hv := differentiableWithinAt_localParisiGradient_terminal_mix β μ ν hab hshort
    g v k hgb hvb hfix hg
  let w := derivWithin v (Icc (0 : ℝ) 1) 0
  have hd : HasDerivWithinAt v w (Icc (0 : ℝ) 1) 0 := hv.hasDerivWithinAt
  refine ⟨w, hd, ?_⟩
  have hH := (parisiSlabTerminalHeatOperator β hab).hasFDerivAt.comp_hasDerivWithinAt 0 hg
  have hQ := hasDerivWithinAt_parisiSlabQuadraticOperator_mix β μ ν hab v w hd
  have hsum := hH.add hQ
  have hderiv : HasDerivWithinAt v
      (parisiSlabTerminalHeatOperator β hab k +
        (parisiSlabQuadraticOperator β ν hab (v 0) - parisiSlabQuadraticOperator β μ hab (v 0) +
          parisiSlabLinearizedOperator β μ hab (v 0) w)) (Icc (0 : ℝ) 1) 0 := by
    apply hsum.congr
    · intro ε hε
      have h := hfix ε hε
      rw [parisiSlabGradientOperator_eq_terminalHeat_add_quadratic] at h
      exact h.symm
    · have h := hfix 0 (by norm_num)
      rw [parisiSlabGradientOperator_eq_terminalHeat_add_quadratic] at h
      exact h.symm
  exact (uniqueDiffOn_Icc_zero_one 0 (by norm_num)).eq_deriv _ hd hderiv

end Paper
