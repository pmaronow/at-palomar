module

public import Paper.DiracConditionalLaw
public import Paper.ItoLeftSums
public import Paper.GaussianDifferentiation

@[expose] public section

/-! Actual post-interface magnetization and its Brownian stochastic integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal ENNReal Topology ContDiff
namespace Paper

/-- The sinh eigenfunction identity for the genuine Gaussian heat kernel. -/
theorem integral_sinh_gaussianReal (x : ℝ) (v : ℝ≥0) :
    (∫ y, Real.sinh y ∂gaussianReal x v) = Real.exp ((v : ℝ) / 2) * Real.sinh x := by
  have hp : Integrable (fun y => Real.exp y) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) 1)
  have hn : Integrable (fun y => Real.exp (-y)) (gaussianReal x v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := x) (v := v) (-1))
  have hIp : (∫ y, Real.exp y ∂gaussianReal x v) = Real.exp (x + (v : ℝ) / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := x) (v := v)) 1
    simpa [mgf] using h
  have hIn : (∫ y, Real.exp (-y) ∂gaussianReal x v) = Real.exp (-x + (v : ℝ) / 2) := by
    have h := congrFun (mgf_fun_id_gaussianReal (μ := x) (v := v)) (-1)
    simpa [mgf] using h
  simp_rw [Real.sinh_eq]
  rw [integral_div, integral_sub hp hn, hIp, hIn, Real.exp_add, Real.exp_add]
  ring

/-- Magnetization is a harmonic observable for the normalized Doob kernel. -/
theorem doobOperator_tanh (v : ℝ≥0) (x : ℝ) : doobOperator v Real.tanh x = Real.tanh x := by
  have hfun : (fun y => Real.cosh y * Real.tanh y) = Real.sinh := by
    funext y
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos y)]
  unfold doobOperator
  rw [hfun, integral_sinh_gaussianReal]
  rw [div_mul_eq_mul_div, ← mul_assoc, ← Real.exp_add]
  simp only [neg_div, neg_add_cancel, Real.exp_zero, one_mul]
  exact (Real.tanh_eq_sinh_div_cosh x).symm

/-- Conditional magnetization conservation for the actual Brownian state. -/
theorem condExp_canonicalDiracMagnetization_after
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1) :
    canonicalBrownianMeasure[(fun omega => Real.tanh (canonicalDiracItoState β h q hq (a + T) omega)) |
      canonicalBrownianFiltration a] =ᵐ[canonicalBrownianMeasure]
      fun omega => Real.tanh (canonicalDiracItoState β h q hq a omega) := by
  simpa only [doobOperator_tanh] using condExp_canonicalDiracItoState_after β h q hq a T hqa haT
    Real.tanh gaussian_continuous_tanh.measurable 1
    (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)

@[fun_prop] theorem contDiff_tanh_all (n : ℕ∞ω) : ContDiff ℝ n Real.tanh := by
  have he : Real.tanh = (fun x => Real.sinh x / Real.cosh x) := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => ne_of_gt (Real.cosh_pos x))

private theorem tanh_ito_timeDerivative : itoTimeDerivative (fun _ x : ℝ => Real.tanh x) =
    fun _ _ => 0 := by
  funext s x
  exact deriv_const s (Real.tanh x)

private theorem tanh_ito_spaceSecondDerivative (s x : ℝ) :
    itoSpaceSecondDerivative (fun _ x : ℝ => Real.tanh x) s x =
      -2 * Real.tanh x * sech x ^ 2 := by
  exact (hasDerivAt_deriv_tanh x).deriv

/-- Explicit Brownian left sums for the actual magnetization stochastic integral. -/
def canonicalMagnetizationItoApprox (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (n : ℕ) (omega : BrownianSample) : ℝ :=
  ∑ i ∈ Finset.range n,
    β * sech (canonicalDiracItoState β h q hq (a + uniformPartitionTime T n i) omega) ^ 2 *
      (canonicalBrownian (a + uniformPartitionTime T n (i + 1)) omega -
        canonicalBrownian (a + uniformPartitionTime T n i) omega)

/-- The chosen representative is identified below as the genuine limit in
probability of the Brownian left sums, hence defines the stochastic integral. -/
def canonicalMagnetizationItoIntegral (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (omega : BrownianSample) : ℝ :=
  Real.tanh (canonicalDiracItoState β h q hq (a + T) omega) -
    Real.tanh (canonicalDiracItoState β h q hq a omega)

/-- **Proposition 5.1, stochastic equation.** The actual magnetization change
is the stochastic integral `∫ β sech²(X_s) dB_s`, characterized by convergence
in probability of genuine adapted Brownian left sums. -/
theorem canonicalMagnetizationItoApprox_tendstoInMeasure
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (a T : ℝ≥0) (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => canonicalMagnetizationItoApprox β h q hq a T (n + 1)) atTop
      (canonicalMagnetizationItoIntegral β h q hq a T) := by
  let X := canonicalDiracShiftState β h q hq a
  let μ := canonicalDiracShiftDrift β h q hq a
  let f : ℝ → ℝ → ℝ := fun _ x => Real.tanh x
  have hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) := by
    simp only [f, tanh_ito_timeDerivative]
    exact continuous_const
  have hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2) := by
    change Continuous (fun p : ℝ × ℝ => deriv Real.tanh p.2)
    simp only [deriv_tanh]
    exact (gaussian_continuous_sech.pow 2).comp continuous_snd
  have hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2) := by
    simp only [f, tanh_ito_spaceSecondDerivative]
    exact (gaussian_continuous_tanh.const_mul (-2)).mul (gaussian_continuous_sech.pow 2) |>.comp continuous_snd
  have hl := ito_stochastic_leftSums_tendstoInMeasure
    (boundedDriftItoCharacteristics_canonicalDiracShift β h q hq a) f
    (gaussian_continuous_tanh.comp continuous_snd) (fun _ => differentiable_const _)
    (fun _ => contDiff_tanh_all 2) hdt hdx hsecond T
  have hμ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) (omega : BrownianSample) :
      μ s.toNNReal omega = β ^ 2 * Real.tanh (X s.toNNReal omega) := by
    have hp : q ≤ ((a + s.toNNReal : ℝ≥0) : ℝ) ∧
        ((a + s.toNNReal : ℝ≥0) : ℝ) ≤ 1 := by
      rw [NNReal.coe_add, Real.coe_toNNReal s hs.1]
      exact ⟨hqa.trans (le_add_of_nonneg_right hs.1), (add_le_add le_rfl hs.2).trans haT⟩
    dsimp [μ, X, canonicalDiracShiftDrift, canonicalDiracShiftState, canonicalDiracItoDrift]
    exact ite_eq_left hp
  have htime (omega : BrownianSample) : generalItoTimeIntegral f X T omega = 0 := by
    simp only [generalItoTimeIntegral, f, tanh_ito_timeDerivative, integral_zero]
  have hD (omega : BrownianSample) : itoDriftIntegral X μ f T omega =
      ∫ s in Icc (0 : ℝ) (T : ℝ), β ^ 2 * Real.tanh (X s.toNNReal omega) * sech (X s.toNNReal omega) ^ 2 := by
    unfold itoDriftIntegral
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [hμ s hs omega]
    change deriv Real.tanh _ * _ = _
    rw [deriv_tanh]
    ring
  have hQ (omega : BrownianSample) : generalItoQuadraticIntegral f X (fun _ _ => β) T omega =
      -itoDriftIntegral X μ f T omega := by
    rw [hD]
    unfold generalItoQuadraticIntegral
    rw [← integral_const_mul, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [f]
    rw [tanh_ito_spaceSecondDerivative]
    ring
  apply hl.congr
  · intro n
    apply Eventually.of_forall
    intro omega
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
    unfold canonicalMagnetizationItoApprox
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f, itoSpaceDerivative, X, canonicalDiracShiftState, canonicalDiracShiftMartingale]
    rw [deriv_tanh]
    ring
  · apply Eventually.of_forall
    intro omega
    change f T (X T omega) - f 0 (X 0 omega) - generalItoTimeIntegral f X T omega -
      itoDriftIntegral X μ f T omega - generalItoQuadraticIntegral f X (fun _ _ => β) T omega = _
    rw [htime, hQ]
    dsimp [f, X, canonicalDiracShiftState, canonicalMagnetizationItoIntegral]
    rw [add_zero]
    ring

/-- Integral equation for the actual magnetization with the independently
verified Brownian left-sum stochastic integral. -/
theorem canonicalDiracMagnetization_stochastic_equation
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0)
    (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => canonicalMagnetizationItoApprox β h q hq a T (n + 1)) atTop
      (canonicalMagnetizationItoIntegral β h q hq a T) ∧
    ∀ omega, Real.tanh (canonicalDiracItoState β h q hq (a + T) omega) =
      Real.tanh (canonicalDiracItoState β h q hq a omega) +
        canonicalMagnetizationItoIntegral β h q hq a T omega := by
  refine ⟨canonicalMagnetizationItoApprox_tendstoInMeasure β h q hq a T hqa haT, ?_⟩
  intro omega
  unfold canonicalMagnetizationItoIntegral
  ring


/-- The actual magnetization is a Mathlib martingale throughout every closed
post-interface time interval, in the original Brownian filtration. -/
theorem martingale_canonicalDiracMagnetization
    (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0)
    (hqa : q ≤ (a : ℝ)) (haT : (a : ℝ) + T ≤ 1) :
    Martingale (fun (s : Icc (0 : ℝ≥0) T) omega =>
      Real.tanh (canonicalDiracItoState β h q hq (a + s.1) omega))
      (monotoneReindexFiltration canonicalBrownianFiltration
        (fun s : Icc (0 : ℝ≥0) T => a + s.1) (fun _ _ hs => add_le_add le_rfl hs))
      canonicalBrownianMeasure := by
  refine ⟨fun s => gaussian_continuous_tanh.comp_stronglyMeasurable
    (stronglyAdapted_canonicalDiracItoState β h q hq (a + s.1)), ?_⟩
  intro s t hst
  have hst' : s.1 ≤ t.1 := hst
  have hqa' : q ≤ ((a + s.1 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add]
    exact hqa.trans (le_add_of_nonneg_right s.1.coe_nonneg)
  have hsum : a + s.1 + (t.1 - s.1) = a + t.1 := by
    rw [add_assoc, add_tsub_cancel_of_le hst']
  have haT' : ((a + s.1 : ℝ≥0) : ℝ) + (t.1 - s.1 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_add, hsum, NNReal.coe_add]
    exact (add_le_add le_rfl (NNReal.coe_le_coe.mpr t.2.2)).trans haT
  have he := condExp_canonicalDiracMagnetization_after β h q hq (a + s.1)
    (t.1 - s.1) hqa' haT'
  change canonicalBrownianMeasure[(fun omega => Real.tanh
    (canonicalDiracItoState β h q hq (a + t.1) omega)) |
    canonicalBrownianFiltration (a + s.1)] =ᵐ[canonicalBrownianMeasure]
    (fun omega => Real.tanh (canonicalDiracItoState β h q hq (a + s.1) omega))
  simpa only [hsum] using he

end Paper
