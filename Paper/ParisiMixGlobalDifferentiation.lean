module

public import Paper.ParisiMixContinuity
public import Paper.ParisiWeightedVolterra
public import Paper.ParisiPotentialVariation
public import Paper.ParisiTranslation

@[expose] public section

/-! # Actual global Parisi differentiability along probability mixtures

The global Gaussian Volterra residual is genuinely invertible after a
bounded exponential conjugation. Together with actual mixture continuity,
this identifies the smooth local implicit selector with the constructed
PDE gradient, for arbitrary inverse temperature.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction ContDiff

namespace Paper

private noncomputable def globalAffineBilinear {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B D : X →L[𝕜] X →L[𝕜] X) (ε : 𝕜) : X →L[𝕜] X →L[𝕜] X :=
  (ContinuousLinearMap.toSpanSingleton 𝕜 B) (1 - ε) +
    (ContinuousLinearMap.toSpanSingleton 𝕜 D) ε

private theorem contDiff_globalAffineBilinear {𝕜 X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (B D : X →L[𝕜] X →L[𝕜] X) : ContDiff 𝕜 ∞ (globalAffineBilinear B D) :=
  (((ContinuousLinearMap.toSpanSingleton 𝕜 B).contDiff).comp
    (contDiff_const.sub contDiff_id)).add
      (ContinuousLinearMap.toSpanSingleton 𝕜 D).contDiff

/-- The actual globally constructed gradient is differentiable along every probability mixture. -/
theorem differentiableWithinAt_parisiGradientBCF_mix (β : ℝ) (μ ν : ParisiMeasure) :
    DifferentiableWithinAt ℝ (fun ε => parisiGradientBCF β (parisiMix μ ν ε))
      (Icc (0 : ℝ) 1) 0 := by
  let B := parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
  let D := parisiSlabBilinearOperator β ν (by norm_num : (0 : ℝ) ≤ 1)
  let V := fun ε => parisiGradientBCF β (parisiMix μ ν ε)
  let H := parisiSlabTerminalHeatOperator β (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF
  have hgb : ∀ x, ‖parisiLineTanhBCF x‖ ≤ 1 := fun x => by
    simpa only [parisiLineTanhBCF, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
  have hfix (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) :
      V ε = H + globalAffineBilinear B D ε (V ε) (V ε) := by
    have hf := parisiGradientBCF_fixedPoint β (parisiMix μ ν ε)
    have he := parisiSlabGradientOperator_eq_terminalHeat_add_quadratic β (parisiMix μ ν ε)
      (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF hgb (V ε)
    rw [parisiSlabQuadraticOperator_eq_bilinear,
      parisiSlabBilinearOperator_mix_apply β μ ν (by norm_num : (0 : ℝ) ≤ 1) ε hε] at he
    exact hf.symm.trans he
  have hbase := hfix 0 (by norm_num)
  have hinv : quadraticLinearizationIsInvertible (globalAffineBilinear B D 0) (V 0) := by
    simpa only [globalAffineBilinear, sub_zero, map_zero, add_zero,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, V, parisiMix_zero, B] using
      parisiSlabBilinearOperator_global_residual_isInvertible β μ (parisiGradientBCF β μ)
        (norm_parisiGradientBCF_le_one β μ)
  obtain ⟨ψ, hψ0, hψ, hψunique⟩ := quadratic_local_solution_of_invertible
    (globalAffineBilinear B D) (fun _ : ℝ => H) 0 (V 0)
    (contDiff_globalAffineBilinear B D).contDiffAt contDiffAt_const hbase hinv
  have hv : ContinuousWithinAt V (Icc (0 : ℝ) 1) 0 := continuousWithinAt_parisiGradientBCF_mix β μ ν
  have hpair : Tendsto (fun ε => (ε, V ε)) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (0, V 0)) :=
    (show Tendsto (fun ε : ℝ => ε) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) from
      nhdsWithin_le_nhds).prodMk_nhds hv.tendsto
  have he : ψ =ᶠ[𝓝[Icc (0 : ℝ) 1] 0] V := by
    filter_upwards [hpair.eventually hψunique, self_mem_nhdsWithin] with ε hp hε
    exact hp.mp (hfix ε hε)
  have hd := (hψ.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt (s := Icc (0 : ℝ) 1)
  exact (hd.congr_of_eventuallyEq he.symm hψ0.symm).differentiableWithinAt

noncomputable def parisiGradientMixDerivative (β : ℝ) (μ ν : ParisiMeasure) : ParisiSlabGradient 0 1 :=
  derivWithin (fun ε => parisiGradientBCF β (parisiMix μ ν ε)) (Icc (0 : ℝ) 1) 0

theorem hasDerivWithinAt_parisiGradientBCF_mix (β : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε => parisiGradientBCF β (parisiMix μ ν ε))
      (parisiGradientMixDerivative β μ ν) (Icc (0 : ℝ) 1) 0 :=
  (differentiableWithinAt_parisiGradientBCF_mix β μ ν).hasDerivWithinAt

/-- The actual globally constructed potential has the derivative of its genuine Gaussian mild formula. -/
theorem hasDerivWithinAt_parisiPotential_mix (β : ℝ) (μ ν : ParisiMeasure)
    (t x : ℝ) (ht : t ≤ 1) :
    HasDerivWithinAt (fun ε => parisiPotential β (parisiMix μ ν ε) (t, x))
      (parisiDuhamelCorrection β ν (parisiGradient β μ) 1 t x -
        parisiDuhamelCorrection β μ (parisiGradient β μ) 1 t x +
        2 * parisiSlabPotentialLinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1) t x ht
          (parisiGradientBCF β μ * parisiGradientMixDerivative β μ ν))
      (Icc (0 : ℝ) 1) 0 := by
  have hd := hasDerivWithinAt_parisiDuhamelCorrection_mix β μ ν
    (by norm_num : (0 : ℝ) ≤ 1) t x ht
    (fun ε => parisiGradientBCF β (parisiMix μ ν ε)) (parisiGradientMixDerivative β μ ν)
    (hasDerivWithinAt_parisiGradientBCF_mix β μ ν)
  simp only [parisiMix_zero] at hd
  have hs := hd.const_add (heatSemigroup (β ^ 2 * (1 - t)) (fun y => Real.log (Real.cosh y)) x)
  apply hs.congr
  · intro ε _
    exact parisiPotential_eq_duhamel β (parisiMix μ ν ε) t x ht
  · exact parisiPotential_eq_duhamel β (parisiMix μ ν 0) t x ht

theorem hasDerivWithinAt_right_of_Icc {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : ℝ → X} {w : X}
    (h : HasDerivWithinAt f w (Icc (0 : ℝ) 1) 0) :
    HasDerivWithinAt f w (Ioi (0 : ℝ)) 0 := by
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := 0))] with ε hε hε1
  exact ⟨hε.le, hε1.le⟩

private theorem hasDerivWithinAt_parisiCorrection_mix_Icc (β : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt
      (fun ε => β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, s * parisiCDF (parisiMix μ ν ε) s)
      (β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
        ∫ s in (0 : ℝ)..1, s * parisiCDF μ s)) (Icc (0 : ℝ) 1) 0 := by
  let a := ∫ s in (0 : ℝ)..1, s * parisiCDF μ s
  let b := ∫ s in (0 : ℝ)..1, s * parisiCDF ν s
  have hd : HasDerivAt (fun ε : ℝ => β ^ 2 / 2 * ((1 - ε) * a + ε * b))
      (β ^ 2 / 2 * (b - a)) 0 := by
    convert! ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).mul_const a).add
      ((hasDerivAt_id 0).mul_const b)).const_mul (β ^ 2 / 2) using 1
    first | rfl | ring
  apply hd.hasDerivWithinAt.congr
  · intro ε hε
    rw [parisiCorrection_integral_mix μ ν ε hε]
  · rw [parisiCorrection_integral_mix μ ν 0 (by norm_num)]

/-- Genuine Gateaux derivative of the constructed general-measure Parisi PDE functional.
The remaining stochastic first-variation bridge identifies this proved mild derivative
with the state-observable pairing. -/
theorem hasDerivWithinAt_parisiPDEFunctional_mix (β h : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun ε => parisiPDEFunctional β h (parisiMix μ ν ε))
      (parisiDuhamelCorrection β ν (parisiGradient β μ) 1 0 h -
        parisiDuhamelCorrection β μ (parisiGradient β μ) 1 0 h +
        2 * parisiSlabPotentialLinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1) 0 h (by norm_num)
          (parisiGradientBCF β μ * parisiGradientMixDerivative β μ ν) -
        β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
          ∫ s in (0 : ℝ)..1, s * parisiCDF μ s))
      (Icc (0 : ℝ) 1) 0 := by
  have hU := hasDerivWithinAt_parisiPotential_mix β μ ν 0 h (by norm_num)
  have hC := hasDerivWithinAt_parisiCorrection_mix_Icc β μ ν
  exact (hU.const_add (Real.log 2)).sub hC

/-- The constructed global measure derivative solves its actual Gaussian linearized equation. -/
theorem parisiGradientMixDerivative_equation (β : ℝ) (μ ν : ParisiMeasure) :
    parisiGradientMixDerivative β μ ν =
      parisiSlabQuadraticOperator β ν (by norm_num : (0 : ℝ) ≤ 1) (parisiGradientBCF β μ) -
        parisiSlabQuadraticOperator β μ (by norm_num : (0 : ℝ) ≤ 1) (parisiGradientBCF β μ) +
        parisiSlabLinearizedOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
          (parisiGradientBCF β μ) (parisiGradientMixDerivative β μ ν) := by
  let V := fun ε => parisiGradientBCF β (parisiMix μ ν ε)
  let H := parisiSlabTerminalHeatOperator β (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF
  have hgb : ∀ x, ‖parisiLineTanhBCF x‖ ≤ 1 := fun x => by
    simpa only [parisiLineTanhBCF, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
      Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
  have hV := hasDerivWithinAt_parisiGradientBCF_mix β μ ν
  have hQ := hasDerivWithinAt_parisiSlabQuadraticOperator_mix β μ ν
    (by norm_num : (0 : ℝ) ≤ 1) V (parisiGradientMixDerivative β μ ν) hV
  simp only [V, parisiMix_zero] at hQ
  have hfamily (ε : ℝ) : V ε = H +
      parisiSlabQuadraticOperator β (parisiMix μ ν ε) (by norm_num : (0 : ℝ) ≤ 1) (V ε) := by
    exact (parisiGradientBCF_fixedPoint β (parisiMix μ ν ε)).symm.trans
      (parisiSlabGradientOperator_eq_terminalHeat_add_quadratic β (parisiMix μ ν ε)
        (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF hgb (V ε))
  have hother := (hQ.const_add H).congr (fun ε _ => hfamily ε) (hfamily 0)
  exact (uniqueDiffOn_Icc_zero_one 0 (by norm_num)).eq_deriv _ hV hother

end Paper


