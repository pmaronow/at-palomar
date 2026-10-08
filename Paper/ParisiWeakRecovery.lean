module

public import Paper.WeakHeatUniqueness
public import Paper.ParisiWeakRepresentative
public import Paper.ParisiWeakMild
public import Paper.BoundedHeatSourceRegularity

@[expose] public section

/-! # Recovering the actual heat integral from the tested weak equation -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

namespace Paper

theorem norm_parisiTerminalHeat_le (β t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiTerminalHeat β (t, x)‖ ≤ ‖x‖ + |β| * gaussianAbsMoment := by
  let ell := β ^ 2 * (1 - t)
  have hvar : ell ≤ β ^ 2 := by
    dsimp [ell]
    nlinarith [mul_nonneg (sq_nonneg β) ht.1]
  have hs : Real.sqrt ell ≤ |β| := by
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hvar
  have hi : Integrable (fun z : ℝ => ‖x‖ + |β| * ‖z‖) (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_standardGaussian_id.norm.const_mul _)
  have he : ∀ z : ℝ, ‖Real.log (Real.cosh (x + Real.sqrt ell * z))‖ ≤
      ‖x‖ + |β| * ‖z‖ := by
    intro z
    calc
      _ ≤ ‖x + Real.sqrt ell * z‖ := by
        simpa only [Real.norm_eq_abs] using norm_logcosh_le_abs _
      _ ≤ ‖x‖ + ‖Real.sqrt ell * z‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hn := norm_integral_le_of_norm_le hi (.of_forall he)
  rw [integral_add (integrable_const _) (integrable_standardGaussian_id.norm.const_mul _),
    integral_const_mul] at hn
  simpa only [parisiTerminalHeat, heatSemigroup, gaussianExpectation,
    integral_const, probReal_univ, smul_eq_mul, one_mul, gaussianAbsMoment, ell] using hn

theorem boundedVolterraPotential_terminal (β : ℝ) (F : ℝ × ℝ → ℝ) (x : ℝ) :
    boundedVolterraPotential β F (1, x) = 0 := by
  unfold boundedVolterraPotential
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  change (if (1 : ℝ) < s then boundedHeatSource β F 1 s x else 0) = 0
  rw [if_neg (not_lt_of_ge hs.2)]

/-- The Gaussian heat and bounded-source Volterra potential is the
unique continuous linear-growth solution of its actual tested equation.
The source continuity premise concerns this concrete integral; it is
discharged separately by bounded measurable heat-source regularity. -/
theorem weak_terminal_equation_eq_heatVolterra (β : ℝ) (hβ : β ≠ 0)
    (u : ℝ × ℝ → ℝ) (hu : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ))
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖u (t, x)‖ ≤ A + L * ‖x‖)
    (hterminal : ∀ x, u (1, x) = Real.log (Real.cosh x))
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (hV : Continuous (boundedVolterraPotential β F))
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ p, u p * parisiAdjointSource β φ p ∂parisiSpaceTime) +
        β ^ 2 / 2 * (∫ p, F p * φ p ∂parisiSpaceTime) +
        (∫ x, Real.log (Real.cosh x) * φ (1, x)) = 0) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ,
      u p = parisiTerminalHeat β p + β ^ 2 / 2 * boundedVolterraPotential β F p := by
  let U : ℝ × ℝ → ℝ := fun p => parisiTerminalHeat β p +
    β ^ 2 / 2 * boundedVolterraPotential β F p
  have hUc : Continuous U := (continuous_parisiTerminalHeat β).add (continuous_const.mul hV)
  have hM : 0 ≤ M := (norm_nonneg (F (0, 0))).trans (hb _)
  have hC : 0 ≤ |β| * gaussianAbsMoment + β ^ 2 / 2 * M := by
    exact add_nonneg (mul_nonneg (abs_nonneg _) gaussianAbsMoment_nonneg) (by positivity)
  have hUb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖U (t, x)‖ ≤
      (|β| * gaussianAbsMoment + β ^ 2 / 2 * M) + ‖x‖ := by
    intro t ht x
    calc
      _ ≤ ‖parisiTerminalHeat β (t, x)‖ +
          ‖β ^ 2 / 2 * boundedVolterraPotential β F (t, x)‖ := norm_add_le _ _
      _ ≤ (‖x‖ + |β| * gaussianAbsMoment) + β ^ 2 / 2 * M := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
        exact add_le_add (norm_parisiTerminalHeat_le β t x ht)
          (mul_le_mul_of_nonneg_left (norm_boundedVolterraPotential_le β F M hb _) (by positivity))
      _ = _ := by ring
  have hUt : ∀ x, U (1, x) = Real.log (Real.cosh x) := by
    intro x
    simp only [U, parisiTerminalHeat, sub_self, mul_zero,
      heatSemigroup_zero, boundedVolterraPotential_terminal, add_zero]
  have hwc : ContinuousOn (fun p => u p - U p) (Icc (0 : ℝ) 1 ×ˢ univ) :=
    hu.sub hUc.continuousOn
  have hwb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖u (t, x) - U (t, x)‖ ≤
        (A + (|β| * gaussianAbsMoment + β ^ 2 / 2 * M)) + (L + 1) * ‖x‖ := by
    intro t ht x
    exact (norm_sub_le _ _).trans ((add_le_add (hub t ht x) (hUb t ht x)).trans_eq (by ring))
  have hwweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {q : ℝ × ℝ | 0 < q.1} →
      (∫ p, (u p - U p) * parisiAdjointSource β φ p ∂parisiSpaceTime) = 0 := by
    intro φ hφ hc hs
    let ψ := parisiAdjointSource β φ
    have hψ := continuous_parisiAdjointSource β φ hφ
    have hψc := hasCompactSupport_parisiAdjointSource β φ hφ hc
    have hui : Integrable (fun p => u p * ψ p) parisiSpaceTime := by
      have hi := ((continuous_parisiClampPotential u hu).mul hψ).integrable_of_hasCompactSupport
        (μ := parisiSpaceTime) hψc.mul_left
      exact hi.congr (by
        filter_upwards [ae_parisiSpaceTime_openStrip] with p hp
        change parisiClampPotential u p * ψ p = u p * ψ p
        rw [parisiClampPotential_eq u ⟨hp.1.le, hp.2.le⟩])
    have hTi : Integrable (fun p => parisiTerminalHeat β p * ψ p) parisiSpaceTime :=
      ((continuous_parisiTerminalHeat β).mul hψ).integrable_of_hasCompactSupport hψc.mul_left
    have hVi : Integrable (fun p => boundedVolterraPotential β F p * ψ p) parisiSpaceTime := by
      rw [parisiSpaceTime_eq_timeProd]
      exact integrable_boundedVolterra_test β F hF M hb _ hψ hψc
    have hUi : Integrable (fun p => U p * ψ p) parisiSpaceTime := by
      convert hTi.add (hVi.const_mul (β ^ 2 / 2)) using 1
      funext p
      dsimp [U]
      ring
    have hUeq : (∫ p, U p * ψ p ∂parisiSpaceTime) =
        -(∫ x, Real.log (Real.cosh x) * φ (1, x)) -
          β ^ 2 / 2 * (∫ p, F p * φ p ∂parisiSpaceTime) := by
      change (∫ p, (parisiTerminalHeat β p + β ^ 2 / 2 * boundedVolterraPotential β F p) * ψ p
        ∂parisiSpaceTime) = _
      simp_rw [add_mul, mul_assoc]
      rw [integral_add hTi (hVi.const_mul _), integral_const_mul,
        parisiSpaceTime_eq_timeProd,
        integral_parisiTerminalHeat_adjointSource β hβ φ hφ hc hs,
        integral_boundedVolterra_adjointSource β hβ F hF M hb φ hφ hc hs]
      ring
    simp_rw [sub_mul]
    rw [integral_sub hui hUi, hUeq]
    linarith [hweak φ hφ hc hs]
  have hz := weak_backwardHeat_eq_zero_of_linearGrowth β (fun p => u p - U p) hwc
    (A + (|β| * gaussianAbsMoment + β ^ 2 / 2 * M)) (L + 1)
    (add_nonneg hA hC) (by linarith) hwb
    (fun x => by rw [hterminal, hUt]; exact sub_self _)
    hwweak
  intro p hp
  exact sub_eq_zero.mp (hz p hp)

theorem IsParisiWeakSolution.integral_adjointSource {β : ℝ} {μ : ParisiMeasure}
    {u v : ℝ × ℝ → ℝ} (huv : IsParisiWeakSolution β μ u v)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) :
    (∫ p, u p * parisiAdjointSource β φ p ∂parisiSpaceTime) + β ^ 2 / 2 *
      (∫ p, parisiNonlinearity μ v p * φ p ∂parisiSpaceTime) +
      (∫ x, Real.log (Real.cosh x) * φ (1, x)) = 0 := by
  have hui : Integrable (fun p => u p * parisiAdjointSource β φ p) parisiSpaceTime := by
    have hi := ((continuous_parisiClampPotential u huv.continuous_potential).mul
      (continuous_parisiAdjointSource β φ hφ)).integrable_of_hasCompactSupport
      (μ := parisiSpaceTime) (hasCompactSupport_parisiAdjointSource β φ hφ hc).mul_left
    exact hi.congr (by
      filter_upwards [ae_parisiSpaceTime_openStrip] with p hp
      change parisiClampPotential u p * parisiAdjointSource β φ p = _
      rw [parisiClampPotential_eq u ⟨hp.1.le, hp.2.le⟩])
  have hφi : Integrable φ parisiSpaceTime := hφ.continuous.integrable_of_hasCompactSupport hc
  have hFi : Integrable (fun p => parisiNonlinearity μ v p * φ p) parisiSpaceTime := by
    have hi := hφi.mul_bdd (parisiNonlinearity_measurable μ v hv).aestronglyMeasurable
      (.of_forall (norm_parisiNonlinearity_le μ v R hb))
    exact hi.congr (.of_forall fun p => mul_comm _ _)
  obtain ⟨_, _, hz⟩ := huv.equation φ hφ hc hs
  have he : (∫ p, -u p * parisiTestT φ p + β ^ 2 / 2 *
      (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p) ∂parisiSpaceTime) =
      (∫ p, u p * parisiAdjointSource β φ p ∂parisiSpaceTime) + β ^ 2 / 2 *
      (∫ p, parisiNonlinearity μ v p * φ p ∂parisiSpaceTime) := by
    rw [← integral_const_mul, ← integral_add hui (hFi.const_mul _)]
    apply integral_congr_ae
    exact .of_forall fun p => by unfold parisiAdjointSource parisiNonlinearity; ring
  rw [he] at hz
  convert hz using 1
  congr 1
  exact integral_congr_ae (.of_forall fun x => mul_comm _ _)

theorem IsParisiWeakSolution.eq_heatVolterra_of_continuous_source
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R)
    (hV : Continuous (boundedVolterraPotential β (parisiNonlinearity μ v))) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ,
      u p = parisiTerminalHeat β p +
        β ^ 2 / 2 * boundedVolterraPotential β (parisiNonlinearity μ v) p := by
  obtain ⟨A, L, hA, hL, hub⟩ := huv.uniform_linear_growth
  exact weak_terminal_equation_eq_heatVolterra β hβ u huv.continuous_potential
    A L hA hL hub huv.terminal (parisiNonlinearity μ v)
    (parisiNonlinearity_measurable μ v hv) (R ^ 2)
    (norm_parisiNonlinearity_le μ v R hb) hV
    (fun φ hφ hc hs => huv.integral_adjointSource hv R hb φ hφ hc hs)

/-- For every bounded measurable representative, the paper's tested weak
equation yields its actual Gaussian Duhamel formula. All regularity
requirements of the concrete bounded-source integral are discharged. -/
theorem IsParisiWeakSolution.eq_heatVolterra
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0)
    (hv : Measurable v) (R : ℝ) (hb : ∀ p, ‖v p‖ ≤ R) :
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ,
      u p = parisiTerminalHeat β p +
        β ^ 2 / 2 * boundedVolterraPotential β (parisiNonlinearity μ v) p :=
  huv.eq_heatVolterra_of_continuous_source hβ hv R hb
    (continuous_boundedVolterraPotential β hβ _
      (parisiNonlinearity_measurable μ v hv) (R ^ 2) (norm_parisiNonlinearity_le μ v R hb))

/-- Recovery applies to every member of the original weak class, even
when its specified gradient is only almost-everywhere measurable and bounded. -/
theorem IsParisiWeakSolution.exists_heatVolterra_representative
    {β : ℝ} {μ : ParisiMeasure} {u v : ℝ × ℝ → ℝ}
    (huv : IsParisiWeakSolution β μ u v) (hβ : β ≠ 0) :
    ∃ (R : ℝ) (w : ℝ × ℝ → ℝ), 0 ≤ R ∧ Measurable w ∧
      (∀ p, ‖w p‖ ≤ R) ∧ v =ᵐ[parisiSpaceTime] w ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ univ,
        u p = parisiTerminalHeat β p +
          β ^ 2 / 2 * boundedVolterraPotential β (parisiNonlinearity μ w) p := by
  obtain ⟨R, w, hR, hw, hb, he, huvw⟩ := huv.exists_bounded_measurable_representative
  exact ⟨R, w, hR, hw, hb, he, huvw.eq_heatVolterra hβ hw R hb⟩

end Paper
