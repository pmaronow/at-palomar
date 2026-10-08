module

public import Paper.ParisiControlDerivative
public import Paper.ParisiStateStability

@[expose] public section

/-! Quantitative continuity of actual fixed-control measure derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper

theorem parisiControlDrift_control_sub_le {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A C : ℝ → Ω → ℝ) (hA : ∀ omega, Measurable (fun s => A s omega))
    (hC : ∀ omega, Measurable (fun s => C s omega))
    (hbA : ∀ s omega, ‖A s omega‖ ≤ 1) (hbC : ∀ s omega, ‖C s omega‖ ≤ 1)
    (D : ℝ) (hD : ∀ s omega, ‖A s omega - C s omega‖ ≤ D) (omega : Ω) :
    ‖parisiControlDrift β μ A omega - parisiControlDrift β μ C omega‖ ≤ β ^ 2 * D := by
  have hi := (parisiControl_intervalIntegrable μ A hA hbA omega).1
  have hj := (parisiControl_intervalIntegrable μ C hC hbC omega).1
  unfold parisiControlDrift
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := D) (f := fun s => parisiCDF μ s * A s omega - parisiCDF μ s * C s omega)
    (fun s _ => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
      exact (mul_le_mul_of_nonneg_right (parisiCDF_le_one μ s) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hD s omega))
  simpa using hn

theorem parisiControlCost_control_sub_le {Ω : Type*} (β : ℝ) (μ : ParisiMeasure)
    (A C : ℝ → Ω → ℝ) (hA : ∀ omega, Measurable (fun s => A s omega))
    (hC : ∀ omega, Measurable (fun s => C s omega))
    (hbA : ∀ s omega, ‖A s omega‖ ≤ 1) (hbC : ∀ s omega, ‖C s omega‖ ≤ 1)
    (D : ℝ) (hD : ∀ s omega, ‖A s omega - C s omega‖ ≤ D) (omega : Ω) :
    ‖parisiControlCost β μ A omega - parisiControlCost β μ C omega‖ ≤ β ^ 2 * D := by
  have hi := (parisiControl_intervalIntegrable μ A hA hbA omega).2
  have hj := (parisiControl_intervalIntegrable μ C hC hbC omega).2
  unfold parisiControlCost
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hj, norm_mul,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 2 * D) (f := fun s => parisiCDF μ s * A s omega ^ 2 - parisiCDF μ s * C s omega ^ 2)
    (fun s _ => by
      rw [← mul_sub, show A s omega ^ 2 - C s omega ^ 2 =
        (A s omega - C s omega) * (A s omega + C s omega) by ring,
        norm_mul, norm_mul, Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
      have hadd : ‖A s omega + C s omega‖ ≤ 2 :=
        (norm_add_le _ _).trans (by linarith [hbA s omega, hbC s omega])
      have hp := mul_le_mul (hD s omega) hadd (norm_nonneg _)
        ((norm_nonneg _).trans (hD s omega))
      exact (mul_le_mul_of_nonneg_right (parisiCDF_le_one μ s)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
        (by simpa only [one_mul, mul_one, mul_comm] using hp))
  have hn' : ‖∫ s in (0 : ℝ)..1,
      parisiCDF μ s * A s omega ^ 2 - parisiCDF μ s * C s omega ^ 2‖ ≤ 2 * D := by
    simpa using hn
  exact (mul_le_mul_of_nonneg_left hn' (div_nonneg (sq_nonneg β) (by norm_num))).trans_eq
    (by ring)

/-- Uniform stability of the actual measure derivative under bounded
control perturbations. No endpoint distribution hypothesis is needed. -/
theorem parisiAffineControlDerivative_control_sub_le {Ω : Type*}
    (β h : ℝ) (B : Ω → ℝ) (A C : ℝ → Ω → ℝ)
    (hA : ∀ omega, Measurable (fun s => A s omega))
    (hC : ∀ omega, Measurable (fun s => C s omega))
    (hbA : ∀ s omega, ‖A s omega‖ ≤ 1) (hbC : ∀ s omega, ‖C s omega‖ ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (hAC : ∀ s omega, ‖A s omega - C s omega‖ ≤ D)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (omega : Ω) :
    ‖parisiAffineControlDerivative β h B A μ ν t omega -
      parisiAffineControlDerivative β h B C μ ν t omega‖ ≤
      (2 * β ^ 4 + 4 * β ^ 2) * D := by
  let da := parisiControlDrift β ν A omega - parisiControlDrift β μ A omega
  let dc := parisiControlDrift β ν C omega - parisiControlDrift β μ C omega
  let x := h + β * B omega + parisiControlDrift β μ A omega + t * da
  let y := h + β * B omega + parisiControlDrift β μ C omega + t * dc
  let ca := parisiControlCost β ν A omega - parisiControlCost β μ A omega
  let cc := parisiControlCost β ν C omega - parisiControlCost β μ C omega
  have hxy : ‖x - y‖ ≤ β ^ 2 * D := by
    have hx : x = h + β * B omega + parisiControlDrift β (parisiMix μ ν t) A omega := by
      rw [parisiControlDrift_mix β μ ν A hA hbA t ht omega]
      dsimp [x, da]
      ring
    have hy : y = h + β * B omega + parisiControlDrift β (parisiMix μ ν t) C omega := by
      rw [parisiControlDrift_mix β μ ν C hC hbC t ht omega]
      dsimp [y, dc]
      ring
    rw [hx, hy]
    simpa only [add_sub_add_left_eq_sub] using
      parisiControlDrift_control_sub_le β (parisiMix μ ν t) A C hA hC hbA hbC D hAC omega
  have ht : ‖Real.tanh x - Real.tanh y‖ ≤ β ^ 2 * D := by
    have ht := lipschitzWith_tanh.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at ht
    exact ht.trans hxy
  have hd : ‖da‖ ≤ 2 * β ^ 2 := by
    exact (norm_sub_le _ _).trans (by
      linarith [parisiControlDrift_norm_le β ν A hbA omega,
        parisiControlDrift_norm_le β μ A hbA omega])
  have hdd : ‖da - dc‖ ≤ 2 * β ^ 2 * D := by
    have he : da - dc = (parisiControlDrift β ν A omega - parisiControlDrift β ν C omega) -
        (parisiControlDrift β μ A omega - parisiControlDrift β μ C omega) := by dsimp [da, dc]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (by
      linarith [parisiControlDrift_control_sub_le β ν A C hA hC hbA hbC D hAC omega,
        parisiControlDrift_control_sub_le β μ A C hA hC hbA hbC D hAC omega])
  have hcc : ‖ca - cc‖ ≤ 2 * β ^ 2 * D := by
    have he : ca - cc = (parisiControlCost β ν A omega - parisiControlCost β ν C omega) -
        (parisiControlCost β μ A omega - parisiControlCost β μ C omega) := by dsimp [ca, cc]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (by
      linarith [parisiControlCost_control_sub_le β ν A C hA hC hbA hbC D hAC omega,
        parisiControlCost_control_sub_le β μ A C hA hC hbA hbC D hAC omega])
  have hty : ‖Real.tanh y‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le
  change ‖(Real.tanh x * da - ca) - (Real.tanh y * dc - cc)‖ ≤ _
  rw [show (Real.tanh x * da - ca) - (Real.tanh y * dc - cc) =
    (Real.tanh x - Real.tanh y) * da + Real.tanh y * (da - dc) - (ca - cc) by ring]
  calc
    _ ≤ ‖(Real.tanh x - Real.tanh y) * da‖ + ‖Real.tanh y * (da - dc)‖ +
      ‖ca - cc‖ := by
      have hs := norm_sub_le
        ((Real.tanh x - Real.tanh y) * da + Real.tanh y * (da - dc)) (ca - cc)
      have ha := norm_add_le ((Real.tanh x - Real.tanh y) * da) (Real.tanh y * (da - dc))
      linarith
    _ ≤ (β ^ 2 * D) * (2 * β ^ 2) + 1 * (2 * β ^ 2 * D) + 2 * β ^ 2 * D := by
      rw [norm_mul, norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul ht hd (norm_nonneg _) (mul_nonneg (sq_nonneg β) hD))
        (mul_le_mul hty hdd (norm_nonneg _) zero_le_one)) hcc
    _ = _ := by ring

theorem integrable_parisiAffineControlDerivative
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B)
    (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1) (μ ν : ParisiMeasure) (t : ℝ) :
    Integrable (parisiAffineControlDerivative β h B A μ ν t) P := by
  exact (integrable_const (μ := P) (3 * β ^ 2)).mono'
    (measurable_parisiAffineControlDerivative β h B hB A hA μ ν t).aestronglyMeasurable
    (.of_forall fun omega => parisiAffineControlDerivative_norm_le β h B A hb μ ν t omega)

/-- The actual affine derivative has a uniform Lipschitz estimate in its
measure-mixing parameter, for every bounded control and all real parameters. -/
theorem parisiAffineControlDerivative_parameter_sub_le {Ω : Type*}
    (β h : ℝ) (B : Ω → ℝ) (A : ℝ → Ω → ℝ)
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1) (μ ν : ParisiMeasure)
    (t r : ℝ) (omega : Ω) :
    ‖parisiAffineControlDerivative β h B A μ ν t omega -
      parisiAffineControlDerivative β h B A μ ν r omega‖ ≤
      4 * β ^ 4 * ‖t - r‖ := by
  let d := parisiControlDrift β ν A omega - parisiControlDrift β μ A omega
  let x := h + β * B omega + parisiControlDrift β μ A omega + t * d
  let y := h + β * B omega + parisiControlDrift β μ A omega + r * d
  have hd : ‖d‖ ≤ 2 * β ^ 2 := by
    exact (norm_sub_le _ _).trans (by
      linarith [parisiControlDrift_norm_le β ν A hb omega,
        parisiControlDrift_norm_le β μ A hb omega])
  have htanh : ‖Real.tanh x - Real.tanh y‖ ≤ ‖t - r‖ * ‖d‖ := by
    have htanh := lipschitzWith_tanh.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at htanh
    have he : x - y = (t - r) * d := by dsimp [x, y]; ring
    simpa only [he, norm_mul] using htanh
  unfold parisiAffineControlDerivative
  change ‖(Real.tanh x * d - _) - (Real.tanh y * d - _)‖ ≤ _
  rw [sub_sub_sub_cancel_right, ← sub_mul, norm_mul]
  calc
    _ ≤ (‖t - r‖ * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right htanh (norm_nonneg _)
    _ ≤ (‖t - r‖ * (2 * β ^ 2)) * (2 * β ^ 2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) hd
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg β)))
    _ = _ := by ring

/-- A genuine uniform quadratic remainder for the affine payoff. The bound
is independent of the sample, the endpoint noise, and the bounded control. -/
theorem parisiAffineControlPayoff_remainder_le {Ω : Type*}
    (β h : ℝ) (B : Ω → ℝ) (A : ℝ → Ω → ℝ)
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1) (μ ν : ParisiMeasure)
    (t : ℝ) (ht : 0 ≤ t) (omega : Ω) :
    ‖parisiAffineControlPayoff β h B A μ ν t omega -
      parisiAffineControlPayoff β h B A μ ν 0 omega -
      t * parisiAffineControlDerivative β h B A μ ν 0 omega‖ ≤ 4 * β ^ 4 * t ^ 2 := by
  let f := fun r => parisiAffineControlPayoff β h B A μ ν r omega -
    r * parisiAffineControlDerivative β h B A μ ν 0 omega
  let d := fun r => parisiAffineControlDerivative β h B A μ ν r omega -
    parisiAffineControlDerivative β h B A μ ν 0 omega
  have hf : ∀ r ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (d r) (Icc (0 : ℝ) t) r := by
    intro r _
    have hl : HasDerivAt (fun a => a * parisiAffineControlDerivative β h B A μ ν 0 omega)
        (parisiAffineControlDerivative β h B A μ ν 0 omega) r := by
      simpa using (hasDerivAt_id r).mul_const (parisiAffineControlDerivative β h B A μ ν 0 omega)
    exact ((parisiAffineControlPayoff_hasDerivAt β h B A μ ν r omega).sub
      hl).hasDerivWithinAt
  have hd : ∀ r ∈ Ico (0 : ℝ) t, ‖d r‖ ≤ 4 * β ^ 4 * t := by
    intro r hr
    have hn := parisiAffineControlDerivative_parameter_sub_le β h B A hb μ ν r 0 omega
    rw [sub_zero, Real.norm_of_nonneg hr.1] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left hr.2.le (by positivity))
  have hn := norm_image_sub_le_of_norm_deriv_le_segment' hf hd t ⟨ht, le_rfl⟩
  change ‖(parisiAffineControlPayoff β h B A μ ν t omega -
    t * parisiAffineControlDerivative β h B A μ ν 0 omega) -
    (parisiAffineControlPayoff β h B A μ ν 0 omega -
      0 * parisiAffineControlDerivative β h B A μ ν 0 omega)‖ ≤
      (4 * β ^ 4 * t) * (t - 0) at hn
  convert hn using 1
  · congr 1
    ring
  · ring

theorem parisiControlObjective_mix_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β h : ℝ) (B : Ω → ℝ) (hBm : Measurable B) (hBi : Integrable B P)
    (A : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hb : ∀ s omega, ‖A s omega‖ ≤ 1) (μ ν : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiControlObjective P β h B A (parisiMix μ ν t) -
      parisiControlObjective P β h B A μ -
      t * (∫ omega, parisiAffineControlDerivative β h B A μ ν 0 omega ∂P)‖ ≤
      4 * β ^ 4 * t ^ 2 := by
  have hi := integrable_parisiControlPayoff P β h B hBm hBi A hA hb (parisiMix μ ν t)
  have hj := integrable_parisiControlPayoff P β h B hBm hBi A hA hb μ
  have hd := integrable_parisiAffineControlDerivative P β h B hBm A hA hb μ ν 0
  have hin : Integrable (fun omega => parisiControlPayoff β h B A (parisiMix μ ν t) omega -
      parisiControlPayoff β h B A μ omega) P := hi.sub hj
  have hdn : Integrable (fun omega => t * parisiAffineControlDerivative β h B A μ ν 0 omega) P :=
    hd.const_mul t
  unfold parisiControlObjective
  rw [← integral_sub hi hj, ← integral_const_mul, ← integral_sub hin hdn]
  have hbound : ∀ omega, ‖parisiControlPayoff β h B A (parisiMix μ ν t) omega -
      parisiControlPayoff β h B A μ omega -
      t * parisiAffineControlDerivative β h B A μ ν 0 omega‖ ≤ 4 * β ^ 4 * t ^ 2 := by
    intro omega
    have he := parisiAffineControlPayoff_eq_mix β h B A
      (fun omega => hA.comp (measurable_id.prodMk measurable_const)) hb μ ν t ht omega
    rw [← he]
    have hzero : parisiControlPayoff β h B A μ omega =
        parisiAffineControlPayoff β h B A μ ν 0 omega := by
      simp [parisiAffineControlPayoff, parisiControlPayoff]
    rw [hzero]
    exact parisiAffineControlPayoff_remainder_le β h B A hb μ ν t ht.1 omega
  simpa using norm_integral_le_of_norm_le_const (μ := P) (.of_forall hbound)

/-- The actual expected derivative is uniformly continuous under a control
perturbation, for every probability measure and measurable noise endpoint. -/
theorem integral_parisiAffineControlDerivative_control_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (β h : ℝ) (B : Ω → ℝ) (hB : Measurable B)
    (A C : ℝ → Ω → ℝ) (hA : Measurable (Function.uncurry A))
    (hC : Measurable (Function.uncurry C))
    (hbA : ∀ s omega, ‖A s omega‖ ≤ 1) (hbC : ∀ s omega, ‖C s omega‖ ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (hAC : ∀ s omega, ‖A s omega - C s omega‖ ≤ D)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(∫ omega, parisiAffineControlDerivative β h B A μ ν t omega ∂P) -
      (∫ omega, parisiAffineControlDerivative β h B C μ ν t omega ∂P)‖ ≤
      (2 * β ^ 4 + 4 * β ^ 2) * D := by
  rw [← integral_sub (integrable_parisiAffineControlDerivative P β h B hB A hA hbA μ ν t)
    (integrable_parisiAffineControlDerivative P β h B hB C hC hbC μ ν t)]
  simpa using norm_integral_le_of_norm_le_const (μ := P) (.of_forall fun omega =>
    parisiAffineControlDerivative_control_sub_le β h B A C
      (fun omega => hA.comp (measurable_id.prodMk measurable_const))
      (fun omega => hC.comp (measurable_id.prodMk measurable_const))
      hbA hbC D hD hAC μ ν t ht omega)

/-- The measure derivative for the actual feedback selectors converges
uniformly in the derivative parameter and on every Brownian sample. -/
theorem parisiAffineControlDerivative_selected_mix_sub_le (β h : ℝ)
    (B : BrownianSample → ℝ) (μ ν : ParisiMeasure)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (omega : BrownianSample) :
    ‖parisiAffineControlDerivative β h B (selectedParisiFeedbackControl β h μ) μ ν t omega -
      parisiAffineControlDerivative β h B
        (selectedParisiFeedbackControl β h (parisiMix μ ν ε)) μ ν t omega‖ ≤
      (2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β * ε := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl β h μ
  have hC := isParisiAdmissibleControl_selectedParisiFeedbackControl β h (parisiMix μ ν ε)
  have hb := parisiAffineControlDerivative_control_sub_le β h B
    (selectedParisiFeedbackControl β h μ) (selectedParisiFeedbackControl β h (parisiMix μ ν ε))
    (fun omega => (hA.continuous_paths omega).measurable)
    (fun omega => (hC.continuous_paths omega).measurable)
    hA.bounded hC.bounded (parisiFeedbackMixConstant β * ε)
    (mul_nonneg (parisiFeedbackMixConstant_nonneg β) hε.1)
    (fun s omega => by simpa only [dist_eq_norm] using
      selectedParisiFeedbackControl_mix_dist_le β h μ ν ε hε s omega)
    μ ν t ht omega
  exact hb.trans_eq (by ring)

theorem integral_parisiAffineControlDerivative_selected_mix_sub_le (β h : ℝ)
    (B : BrownianSample → ℝ) (hB : Measurable B) (μ ν : ParisiMeasure)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(∫ omega, parisiAffineControlDerivative β h B
        (selectedParisiFeedbackControl β h μ) μ ν t omega ∂canonicalBrownianMeasure) -
      (∫ omega, parisiAffineControlDerivative β h B
        (selectedParisiFeedbackControl β h (parisiMix μ ν ε)) μ ν t omega
        ∂canonicalBrownianMeasure)‖ ≤
      (2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β * ε := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl β h μ
  have hC := isParisiAdmissibleControl_selectedParisiFeedbackControl β h (parisiMix μ ν ε)
  have hb := integral_parisiAffineControlDerivative_control_sub_le canonicalBrownianMeasure
    β h B hB (selectedParisiFeedbackControl β h μ)
    (selectedParisiFeedbackControl β h (parisiMix μ ν ε)) hA.measurable hC.measurable
    hA.bounded hC.bounded (parisiFeedbackMixConstant β * ε)
    (mul_nonneg (parisiFeedbackMixConstant_nonneg β) hε.1)
    (fun s omega => by simpa only [dist_eq_norm] using
      selectedParisiFeedbackControl_mix_dist_le β h μ ν ε hε s omega)
    μ ν t ht
  exact hb.trans_eq (by ring)

theorem continuousWithinAt_integral_parisiAffineControlDerivative_selected_mix
    (β h : ℝ) (B : BrownianSample → ℝ) (hB : Measurable B)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (fun ε => ∫ omega,
      parisiAffineControlDerivative β h B
        (selectedParisiFeedbackControl β h (parisiMix μ ν ε)) μ ν t omega
        ∂canonicalBrownianMeasure) (Icc (0 : ℝ) 1) 0 := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [parisiMix_zero]
  apply squeeze_zero' (.of_forall fun ε => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [norm_sub_rev] using
      integral_parisiAffineControlDerivative_selected_mix_sub_le β h B hB μ ν ε hε t ht
  · simpa using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => (2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β)
      (𝓝[Icc (0 : ℝ) 1] 0)
      (𝓝 ((2 * β ^ 4 + 4 * β ^ 2) * parisiFeedbackMixConstant β))).mul nhdsWithin_le_nhds

end Paper
