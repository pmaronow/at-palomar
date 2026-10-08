module

public import Paper.ParisiFiniteStep
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Gaussian evolution of an actual finite Parisi slab.  The convolution
derivative cancels its Hessian against the Parisi PDE, leaving the genuine
quadratic Duhamel source. -/

open Set MeasureTheory ProbabilityTheory Real Filter Topology

namespace Paper

open SpinGlass SpinGlass.Targets

noncomputable def parisiSlabGaussianEvolution {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x r : ℝ) : ℝ :=
  ∫ z, parisiSlabPotential s β j m b r (x + Real.sqrt (β ^ 2 * (r - t)) * z)
    ∂gaussianReal 0 1

noncomputable def parisiSlabGaussianSource {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x r : ℝ) : ℝ :=
  ∫ z, (parisiSlabGradient s β j m b r
    (x + Real.sqrt (β ^ 2 * (r - t)) * z)) ^ 2 ∂gaussianReal 0 1

theorem parisiSlabTimeVelocity_bound {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc 0 1) (b r x : ℝ) :
    |-(β ^ 2 / 2) * (parisiSlabHessian s β j m b r x +
      m * (parisiSlabGradient s β j m b r x) ^ 2)| ≤ β ^ 2 := by
  have hh := parisiSlabHessian_nonneg s β j hm b r x
  have hb := parisiSlabHessian_add_sq_le_one s β j hm b r x
  have hq := sq_nonneg (parisiSlabGradient s β j m b r x)
  have hs : 0 ≤ parisiSlabHessian s β j m b r x +
      m * (parisiSlabGradient s β j m b r x) ^ 2 :=
    add_nonneg hh (mul_nonneg hm.1 hq)
  have hs1 : parisiSlabHessian s β j m b r x +
      m * (parisiSlabGradient s β j m b r x) ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hm.2 hq]
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2), abs_of_nonneg hs]
  nlinarith [sq_nonneg β, mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ β ^ 2 / 2)]

theorem hasDerivAt_parisiSlabGaussianEvolution {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc 0 1)
    (b t x : ℝ) {r : ℝ} (hr : r ∈ Ioo t b) :
    HasDerivAt (parisiSlabGaussianEvolution s β j m b t x)
      (-(β ^ 2 / 2) * m * parisiSlabGaussianSource s β j m b t x r) r := by
  let U := fun w v => parisiSlabPotential s β j m b v w
  let G := fun w v => parisiSlabGradient s β j m b v w
  let J := fun w v => parisiSlabHessian s β j m b v w
  let V := fun w v => -(β ^ 2 / 2) * (J w v + m * (G w v) ^ 2)
  have hc := continuous_parisiSlab s β j hm.1 b
  have hσ : HasDerivAt (fun v : ℝ => β ^ 2 * (v - t)) (β ^ 2) r := by
    simpa using ((hasDerivAt_id r).sub_const t).const_mul (β ^ 2)
  have hσpos : 0 < β ^ 2 * (r - t) :=
    mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hr.1)
  have hΦ : ∀ᶠ v in 𝓝 r, ∀ z,
      HasDerivAt (fun v => U (x + Real.sqrt (β ^ 2 * (v - t)) * z) v)
        (G (x + Real.sqrt (β ^ 2 * (v - t)) * z) v *
          ((0 : ℝ) + β ^ 2 / (2 * Real.sqrt (β ^ 2 * (v - t))) * z) +
          V (x + Real.sqrt (β ^ 2 * (v - t)) * z) v) v := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with v hv z
    have hvσ : 0 < β ^ 2 * (v - t) :=
      mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hv.1)
    have hVi : HasDerivAt (fun v : ℝ => β ^ 2 * (b - v)) (-(β ^ 2)) v := by
      simpa only [Pi.sub_apply, id_eq, mul_one, sub_zero, zero_sub, mul_neg, neg_mul] using
        ((hasDerivAt_const v b).sub (hasDerivAt_id v)).const_mul (β ^ 2)
    have hXi : HasDerivAt (fun v : ℝ => x + Real.sqrt (β ^ 2 * (v - t)) * z)
        ((β ^ 2 / (2 * Real.sqrt (β ^ 2 * (v - t)))) * z) v := by
      simpa only [id_eq, mul_one] using
        (((((hasDerivAt_id v).sub_const t).const_mul (β ^ 2)).sqrt hvσ.ne').mul_const z).const_add x
    have hd := hasDerivAt_parisiStep_variance_curve
      (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
      (continuous_parisiFSecond s β j) hm.1 hVi hXi
      (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hv.2))
    convert hd using 1
    · rfl
    · dsimp [U, G, J, V, parisiSlabGradient, parisiSlabHessian]
      ring
  have hHw : ∀ w, HasDerivAt (fun w => G w r) (J w r) w :=
    hasDerivAt_parisiSlabGradient_spatial s β j m b r
  have hJc : Continuous (fun w => J w r) := hc.2.2.comp (continuous_const.prodMk continuous_id)
  have hJg : ColeHopfFoundation.ProbabilityTheory.HasExpGrowth (fun w => J w r) :=
    ColeHopfFoundation.ProbabilityTheory.HasExpGrowth.of_bounded
      ((parisiSlab_C2 s β j hm b r).abs_second_le_one)
  have hUintegrable : Integrable (fun z => U (x + Real.sqrt (β ^ 2 * (r - t)) * z) r)
      (gaussianReal 0 1) :=
    integrable_of_hasLinearGrowth
      (hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β j)
        (parisiF_measurable s β j) m (β ^ 2 * (b - r)))
      ((hc.1.comp (continuous_const.prodMk continuous_id)).measurable) x _
  have hd := ColeHopfFoundation.ProbabilityTheory.hasDerivAt_integral_curve_gaussianReal
    (H := U) (Hw := G) (Hww := J) (Hv := V)
    (y := fun _ => x) (y' := fun _ => 0)
    (σ := fun v => β ^ 2 * (v - t)) (σ' := fun _ => β ^ 2) hσpos
    (Eventually.of_forall (fun v => hasDerivAt_const v x)) continuousAt_const
    (Eventually.of_forall (fun v => by
      simpa using ((hasDerivAt_id v).sub_const t).const_mul (β ^ 2))) continuousAt_const
    hΦ
    (fun v => (hc.1.comp (continuous_const.prodMk continuous_id)).measurable)
    ((hc.2.1.comp (continuous_const.prodMk continuous_id)).measurable)
    (((hc.2.2.add ((hc.2.1.pow 2).const_mul m)).const_mul (-(β ^ 2 / 2))).comp
      (continuous_const.prodMk continuous_id)).measurable
    ⟨1, 0, le_rfl, Eventually.of_forall (fun v w => by
      simpa using abs_parisiSlabGradient_le_one s β j hm b v w)⟩
    ⟨β ^ 2, 0, le_rfl, Eventually.of_forall (fun v w => by
      simpa only [V, J, G, mul_zero, zero_mul, Real.exp_zero, mul_one] using
        parisiSlabTimeVelocity_bound s β j hm b v w)⟩
    hUintegrable hHw hJc hJg
  convert hd.congr_deriv ?_ using 1
  · rfl
  · dsimp [V]
    simp_rw [show ∀ z : ℝ, (0 : ℝ) * G (x + Real.sqrt (β ^ 2 * (r - t)) * z) r +
      β ^ 2 / 2 * J (x + Real.sqrt (β ^ 2 * (r - t)) * z) r +
      -(β ^ 2 / 2) * (J (x + Real.sqrt (β ^ 2 * (r - t)) * z) r +
        m * (G (x + Real.sqrt (β ^ 2 * (r - t)) * z) r) ^ 2) =
      (-(β ^ 2 / 2) * m) * (G (x + Real.sqrt (β ^ 2 * (r - t)) * z) r) ^ 2 from
        fun z => by ring]
    rw [integral_const_mul]
    rfl

theorem continuous_parisiSlabGaussianSource {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc 0 1) (b t x : ℝ) :
    Continuous (parisiSlabGaussianSource s β j m b t x) := by
  have hc := (continuous_parisiSlab s β j hm.1 b).2.1
  apply continuous_of_dominated (μ := gaussianReal 0 1)
    (F := fun r z => (parisiSlabGradient s β j m b r
      (x + Real.sqrt (β ^ 2 * (r - t)) * z)) ^ 2)
    (bound := fun _ : ℝ => (1 : ℝ))
  · intro r
    have hmap : Continuous (fun z : ℝ => (r, x + Real.sqrt (β ^ 2 * (r - t)) * z)) := by fun_prop
    exact ((hc.comp hmap).pow 2).aestronglyMeasurable
  · intro r
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := abs_parisiSlabGradient_le_one s β j hm b r
      (x + Real.sqrt (β ^ 2 * (r - t)) * z)
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans_eq (by norm_num)
  · exact integrable_const 1
  · filter_upwards with z
    have hmap : Continuous (fun r : ℝ => (r, x + Real.sqrt (β ^ 2 * (r - t)) * z)) := by fun_prop
    exact (hc.comp hmap).pow 2

theorem continuous_parisiSlabGaussianEvolution {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc 0 1) (b t x : ℝ) :
    Continuous (parisiSlabGaussianEvolution s β j m b t x) := by
  have hc := (continuous_parisiSlab s β j hm.1 b).1
  have hLip (v w : ℝ) :
      |parisiSlabPotential s β j m b v w| ≤
        |parisiSlabPotential s β j m b v 0| + |w| := by
    have hstep := parisiStep_lipschitz (m := m) (v := β ^ 2 * (b - v)) (L := 1)
      (by simpa using parisiF_lipschitz s β j) (parisiF_hasLinearGrowth s β j)
      (parisiF_measurable s β j) w 0
    have htri := abs_add_le (parisiSlabPotential s β j m b v w -
      parisiSlabPotential s β j m b v 0) (parisiSlabPotential s β j m b v 0)
    simp only [sub_add_cancel] at htri
    have hstep' : |parisiSlabPotential s β j m b v w -
        parisiSlabPotential s β j m b v 0| ≤ |w| := by
      simpa only [one_mul, sub_zero, parisiSlabPotential] using hstep
    linarith
  have hlocal : ∀ v₀ : ℝ, ∃ δ C c : ℝ, 0 < δ ∧ 0 ≤ c ∧
      ∀ v ∈ Metric.ball v₀ δ, ∀ w,
        |parisiSlabPotential s β j m b v w| ≤ C * Real.exp (c * |w|) := by
    intro v₀
    have hc0 : Continuous (fun v : ℝ => |parisiSlabPotential s β j m b v 0|) :=
      (hc.comp (continuous_id.prodMk continuous_const)).abs
    have hev : ∀ᶠ v in 𝓝 v₀, |parisiSlabPotential s β j m b v 0| <
        |parisiSlabPotential s β j m b v₀ 0| + 1 :=
      (hc0.tendsto v₀).eventually (isOpen_Iio.mem_nhds (lt_add_one _))
    obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨δ, |parisiSlabPotential s β j m b v₀ 0| + 2, 1, hδ, zero_le_one, ?_⟩
    intro v hv w
    have hh := (hb hv).le
    have he1 := Real.one_le_exp (abs_nonneg w)
    have he2 := Real.add_one_le_exp |w|
    have hmule := mul_le_mul_of_nonneg_left he1
      (by positivity : 0 ≤ |parisiSlabPotential s β j m b v₀ 0| + 1)
    have hL := hLip v w
    simp only [one_mul]
    nlinarith [Real.exp_pos |w|]
  have hconv := ColeHopfFoundation.ProbabilityTheory.continuous_integral_comp_curve
    (Ψ := fun v w => parisiSlabPotential s β j m b v w)
    (s := fun v => Real.sqrt (β ^ 2 * (v - t)))
    hc (by fun_prop) (fun _ => Real.sqrt_nonneg _) hlocal
  exact hconv.comp (continuous_const.prodMk continuous_id)

theorem parisiSlabPotential_duhamel {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc 0 1)
    (b t x : ℝ) (ht : t ≤ b) :
    parisiSlabPotential s β j m b t x =
      (∫ z, parisiF s β j (x + Real.sqrt (β ^ 2 * (b - t)) * z) ∂gaussianReal 0 1) +
        (β ^ 2 / 2) * m * ∫ r in t..b, parisiSlabGaussianSource s β j m b t x r := by
  have hE := continuous_parisiSlabGaussianEvolution s β j hm b t x
  have hS := continuous_parisiSlabGaussianSource s β j hm b t x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hE.continuousOn
    (fun r hr => hasDerivAt_parisiSlabGaussianEvolution s β hβ j hm b t x hr)
    ((hS.const_mul (-(β ^ 2 / 2) * m)).intervalIntegrable t b)
  rw [intervalIntegral.integral_const_mul] at hFTC
  have hterminal : parisiSlabGaussianEvolution s β j m b t x b =
      ∫ z, parisiF s β j (x + Real.sqrt (β ^ 2 * (b - t)) * z) ∂gaussianReal 0 1 := by
    simp [parisiSlabGaussianEvolution, parisiSlabPotential, parisiStep_zero_var]
  have hinitial : parisiSlabGaussianEvolution s β j m b t x t =
      parisiSlabPotential s β j m b t x := by
    simp [parisiSlabGaussianEvolution]
  rw [hterminal, hinitial] at hFTC
  linarith

end Paper
