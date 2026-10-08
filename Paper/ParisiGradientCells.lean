module

public import Paper.ParisiGradientMartingale
public import Paper.ParisiFiniteGradientTime
public import Paper.HJBGridCells

@[expose] public section

/-! Actual finite Cole--Hopf gradient generator errors on the selected state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper
open SpinGlass SpinGlass.Targets

lemma norm_parisiSlabHessian_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    ‖parisiSlabHessian s β j m b t x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (parisiSlabHessian_pos s β j hm b t x).le]
  have hh := parisiSlabHessian_add_sq_le_one s β j hm b t x
  linarith [sq_nonneg (parisiSlabGradient s β j m b t x)]

lemma hjbSlabGradientTest_generator_norm_le {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b)
    (t x R A eps : ℝ) (ht : t ≤ c) (hA : ‖A‖ ≤ 1)
    (hclose : ‖A - parisiSlabGradient s β j m b t x‖ ≤ eps) :
    ‖itoTimeDerivative (hjbSlabGradientTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) t x * (β ^ 2 * R * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) t x * β ^ 2‖ ≤
      β ^ 2 * (|R - m| + eps) := by
  rw [hjbSlabGradientTest_drift_eq s β hβ j hm b c hδ hb t x R A ht,
    norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg β)]
  have hdiff : ‖R * A - m * parisiSlabGradient s β j m b t x‖ ≤ |R - m| + eps := by
    have he : R * A - m * parisiSlabGradient s β j m b t x =
        (R - m) * A + m * (A - parisiSlabGradient s β j m b t x) := by ring
    rw [he]
    calc
      _ ≤ ‖(R - m) * A‖ + ‖m * (A - parisiSlabGradient s β j m b t x)‖ := norm_add_le _ _
      _ ≤ |R - m| * 1 + 1 * eps := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
          (mul_le_mul (by simpa only [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2)
            hclose (norm_nonneg _) zero_le_one)
      _ = _ := by ring
  exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_parisiSlabHessian_le_one s β j hm b t x)
    (sq_nonneg β)) hdiff (norm_nonneg _) (by positivity) |>.trans_eq (by ring)

lemma hjbSlabGradientTest_generator_norm_le_sixteen {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b)
    (t x R A : ℝ) (hR : R ∈ Icc (0 : ℝ) 1) (hA : ‖A‖ ≤ 1) :
    ‖itoTimeDerivative (hjbSlabGradientTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) t x * (β ^ 2 * R * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) t x * β ^ 2‖ ≤
      16 * β ^ 2 := by
  have hcap : ‖hjbTimeCapD c δ t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hjbTimeCapD_nonneg c δ t)]
    exact hjbTimeCapD_le_one c hδ t
  have hg : ‖parisiSlabGradient s β j m b (hjbTimeCap c δ t) x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b _ x
  have hh := norm_parisiSlabHessian_le_one s β j hm b (hjbTimeCap c δ t) x
  have h3 : ‖parisiSlabThird s β j m b (hjbTimeCap c δ t) x‖ ≤ 14 := by
    simpa only [Real.norm_eq_abs] using abs_parisiSlabThird_le_fourteen s β j hm b _ x
  have hm1 : ‖m‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2
  have hR1 : ‖R‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hR.1] using hR.2
  have hprod : ‖2 * m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x *
      parisiSlabHessian s β j m b (hjbTimeCap c δ t) x‖ ≤ 2 := by
    rw [norm_mul, norm_mul, norm_mul, show ‖(2 : ℝ)‖ = 2 by norm_num]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hm1 (by norm_num)) hg
      (norm_nonneg _) (by norm_num)) hh (norm_nonneg _) (by norm_num) |>.trans_eq (by norm_num)
  have htd : ‖itoTimeDerivative (hjbSlabGradientTest s β j m b c δ) t x‖ ≤ 8 * β ^ 2 := by
    rw [itoTimeDerivative, (hasDerivAt_hjbSlabGradientTest_time s β hβ j hm b c hδ hb t x).deriv,
      norm_mul, norm_mul, norm_neg, norm_div,
      show ‖β ^ 2‖ = β ^ 2 by simp [Real.norm_eq_abs],
      show ‖(2 : ℝ)‖ = 2 by norm_num]
    have hi := norm_add_le (parisiSlabThird s β j m b (hjbTimeCap c δ t) x)
      (2 * m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * parisiSlabHessian s β j m b (hjbTimeCap c δ t) x)
    have hb16 : ‖parisiSlabThird s β j m b (hjbTimeCap c δ t) x +
      2 * m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * parisiSlabHessian s β j m b (hjbTimeCap c δ t) x‖ ≤ 16 := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hcap (by positivity)) hb16
      (norm_nonneg _) (by positivity) |>.trans_eq (by ring)
  have hdrift : ‖itoSpaceDerivative (hjbSlabGradientTest s β j m b c δ) t x * (β ^ 2 * R * A)‖ ≤ β ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul,
      show ‖β ^ 2‖ = β ^ 2 by simp [Real.norm_eq_abs]]
    exact mul_le_mul (norm_hjbSlabGradientTest_spaceDerivative_le_one s β j hm b c δ t x)
      (mul_le_mul (mul_le_mul_of_nonneg_left hR1 (sq_nonneg β)) hA (norm_nonneg _) (by positivity))
      (by positivity) zero_le_one |>.trans_eq (by ring)
  have hquad : ‖(1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabGradientTest s β j m b c δ) t x * β ^ 2‖ ≤ 7 * β ^ 2 := by
    rw [norm_mul, norm_mul,
      show ‖β ^ 2‖ = β ^ 2 by simp [Real.norm_eq_abs]]
    have hx := norm_hjbSlabGradientTest_spaceSecondDerivative_le_fourteen s β j hm b c δ t x
    calc
      _ ≤ ‖(1 / 2 : ℝ)‖ * 14 * β ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (norm_nonneg _)) (sq_nonneg β)
      _ = _ := by norm_num
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    (by linarith))


def parisiGradientTailError (K c t : ℝ) : ℝ := if t ≤ c then 0 else K

lemma parisiGradientTailError_monotone {K : ℝ} (hK : 0 ≤ K) (c : ℝ) :
    Monotone (parisiGradientTailError K c) := by
  intro a b hab
  by_cases ha : a ≤ c
  · by_cases hb : b ≤ c
    · simp [parisiGradientTailError, ha, hb]
    · simpa only [parisiGradientTailError, ite_eq_left ha, ite_eq_right hb] using hK
  · have hb : ¬b ≤ c := fun hb => ha (hab.trans hb)
    simp [parisiGradientTailError, ha, hb]

lemma integral_parisiGradientTailError {K a b c : ℝ} (hK : 0 ≤ K)
    (hac : a ≤ c) (hcb : c ≤ b) :
    (∫ t in a..b, parisiGradientTailError K c t) = K * (b - c) := by
  have hi (u v : ℝ) := (parisiGradientTailError_monotone hK c).intervalIntegrable (μ := volume) (a := u) (b := v)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a c) (hi c b)]
  have hl : (∫ t in a..c, parisiGradientTailError K c t) = 0 := by
    calc
      _ = ∫ _t in a..c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        rw [uIoo_of_le hac]
        intro t ht
        simp [parisiGradientTailError, ht.2.le]
      _ = 0 := by simp
  have hr : (∫ t in c..b, parisiGradientTailError K c t) = (b - c) * K := by
    calc
      _ = ∫ _t in c..b, K := by
        apply intervalIntegral.integral_congr_uIoo
        rw [uIoo_of_le hcb]
        intro t ht
        simp [parisiGradientTailError, not_le.mpr ht.1]
      _ = _ := by simp
  rw [hl, hr]
  ring

lemma integrable_weighted_parisiSlabGradient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t : ℝ)
    (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (C : ℝ) (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    Integrable (fun ω => Z ω * parisiSlabGradient s β j m b t (Y ω)) P := by
  apply (integrable_const C).mono'
  · exact (hZ.mul ((continuous_parisiSlab s β j hm.1 b).2.1.measurable.comp
      (measurable_const.prodMk hY))).aestronglyMeasurable
  · exact .of_forall fun ω => by
      rw [norm_mul]
      have hg : ‖parisiSlabGradient s β j m b t (Y ω)‖ ≤ 1 := by
        simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b t (Y ω)
      exact (mul_le_mul_of_nonneg_left hg (norm_nonneg _)).trans (by simpa using hC ω)

set_option maxHeartbeats 1000000 in
/-- A genuine weighted Cole--Hopf gradient cell estimate on the constructed
state. Its only errors are the actual CDF mismatch and spatial gradient
mismatch; the time cap has been removed by dominated convergence. -/
theorem canonicalParisiState_gradient_cell_bound
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (v : ℝ → ℝ → ℝ)
    (hv : Continuous (Function.uncurry v)) (hvb : ∀ t x, ‖v t x‖ ≤ 1)
    (hvl : ∀ t, LipschitzWith 1 (v t))
    (r a b : ℝ≥0) (hra : r ≤ a) (hab : a < b) (hb1 : (b : ℝ) ≤ 1)
    {k : ℕ} (s : RSBScheme k) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration r] Z)
    (hZb : ∀ ω, ‖Z ω‖ ≤ 1) {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ ω, ∀ t ∈ Icc (a : ℝ) (b : ℝ),
      ‖v t (canonicalParisiItoState β h μ v hv hvb hvl t.toNNReal ω) -
        parisiSlabGradient s β j m b t (canonicalParisiItoState β h μ v hv hvb hvl t.toNNReal ω)‖ ≤ eps) :
    ‖(∫ ω, Z ω * parisiSlabGradient s β j m b b (canonicalParisiItoState β h μ v hv hvb hvl b ω)
        ∂canonicalBrownianMeasure) -
      ∫ ω, Z ω * parisiSlabGradient s β j m b a (canonicalParisiItoState β h μ v hv hvb hvl a ω)
        ∂canonicalBrownianMeasure‖ ≤
      β ^ 2 * (∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - m|) + β ^ 2 * eps * ((b : ℝ) - a) := by
  let X := canonicalParisiItoState β h μ v hv hvb hvl
  let d := canonicalParisiItoDrift β h μ v hv hvb hvl
  let err : ℝ → ℝ := fun t => β ^ 2 * (|parisiCDF μ t - m| + eps)
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    ((stronglyAdapted_canonicalParisiItoState β h μ v hv hvb hvl t).mono
      (canonicalBrownianFiltration.le t)).measurable
  have hZm : Measurable Z := (hZ.mono (canonicalBrownianFiltration.le r)).measurable
  have herr : IntervalIntegrable err volume a b :=
    ((((parisiCDF_monotone μ).intervalIntegrable (a := a) (b := b)).sub
      intervalIntegrable_const).norm.add intervalIntegrable_const).const_mul _
  have herror : (∫ t in (a : ℝ)..(b : ℝ), err t) =
      β ^ 2 * (∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - m|) + β ^ 2 * eps * ((b : ℝ) - a) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · exact (((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm
    · exact intervalIntegrable_const
  have hpoint (c : ℝ) (hc : c ∈ Ioo (a : ℝ) (b : ℝ)) :
      ‖(∫ ω, Z ω * parisiSlabGradient s β j m b (hjbTimeCap c (((b : ℝ) - c) / 2) b) (X b ω)
          ∂canonicalBrownianMeasure) -
        ∫ ω, Z ω * parisiSlabGradient s β j m b a (X a ω) ∂canonicalBrownianMeasure‖ ≤
      (∫ t in (a : ℝ)..(b : ℝ), err t) + 16 * β ^ 2 * ((b : ℝ) - c) := by
    let δ := ((b : ℝ) - c) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith [hc.2]
    have hcb : c + δ ≤ (b : ℝ) := by dsimp [δ]; linarith [hc.2]
    let f := hjbSlabGradientTest s β j m b c δ
    have hf := continuous_hjbSlabGradientTest s β j hm.1 b c δ
    have ht : ∀ x, Differentiable ℝ (fun t => f t x) := fun x t =>
      (hasDerivAt_hjbSlabGradientTest_time s β hβ j hm b c hδ hcb t x).differentiableAt
    have hx := continuous_hjbSlabGradientTest_spaceDerivative s β j hm.1 b c δ
    have hxx := continuous_hjbSlabGradientTest_spaceSecondDerivative s β j hm b c δ
    have hdt := continuous_hjbSlabGradientTest_timeDerivative s β hβ j hm b c hδ hcb
    let E : ℝ → ℝ := fun t => err t + parisiGradientTailError (16 * β ^ 2) c t
    have hE : IntervalIntegrable E volume a b := herr.add
      ((parisiGradientTailError_monotone (by positivity : 0 ≤ 16 * β ^ 2) c).intervalIntegrable)
    have hgen : ∀ ω, ∀ t ∈ Icc (a : ℝ) (b : ℝ), ‖hjbGenerator X d β f t ω‖ ≤ E t := by
      intro ω t ht0
      have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨a.coe_nonneg.trans ht0.1, ht0.2.trans hb1⟩
      have hd : d t.toNNReal ω = β ^ 2 * parisiCDF μ t * v t (X t.toNNReal ω) := by
        simp only [d, canonicalParisiItoDrift, Real.coe_toNNReal t ht1.1, ite_eq_left ht1.2, X]
      unfold hjbGenerator
      rw [hd]
      by_cases htc : t ≤ c
      · simpa only [E, err, parisiGradientTailError, ite_eq_left htc, add_zero] using
          hjbSlabGradientTest_generator_norm_le s β hβ j hm b c hδ hcb t (X t.toNNReal ω)
            (parisiCDF μ t) (v t (X t.toNNReal ω)) eps htc (hvb _ _) (hclose ω t ht0)
      · have hh := hjbSlabGradientTest_generator_norm_le_sixteen s β hβ j hm b c hδ hcb
          t (X t.toNNReal ω) (parisiCDF μ t) (v t (X t.toNNReal ω))
          ⟨parisiCDF_nonneg μ t, parisiCDF_le_one μ t⟩ (hvb _ _)
        exact hh.trans (by
          dsimp only [E, parisiGradientTailError]
          rw [ite_eq_right htc]
          apply le_add_of_nonneg_left
          dsimp only [err]
          positivity)
    have hia : Integrable (fun ω => Z ω * f a (X a ω)) canonicalBrownianMeasure :=
      integrable_weighted_parisiSlabGradient canonicalBrownianMeasure s β j hm b _ (X a) Z (hXm a) hZm 1 hZb
    have hib : Integrable (fun ω => Z ω * f b (X b ω)) canonicalBrownianMeasure :=
      integrable_weighted_parisiSlabGradient canonicalBrownianMeasure s β j hm b _ (X b) Z (hXm b) hZm 1 hZb
    have hh := canonicalParisiState_weighted_expectation_error β h μ v hv hvb hvl r a b hra hab.le
      f hf ht (contDiff_hjbSlabGradientTest_spatial s β j hm b c δ) hdt hx hxx 1
      (fun t _ x => norm_hjbSlabGradientTest_spaceDerivative_le_one s β j hm b c δ t x)
      Z hZ 1 hZb E hE hgen hia hib
    have htail : IntervalIntegrable (parisiGradientTailError (16 * β ^ 2) c) volume a b :=
      (parisiGradientTailError_monotone (by positivity) c).intervalIntegrable
    dsimp only [E] at hh
    rw [intervalIntegral.integral_add herr htail,
      integral_parisiGradientTailError (by positivity : 0 ≤ 16 * β ^ 2) hc.1.le hc.2.le] at hh
    simpa only [f, hjbSlabGradientTest, δ, X, hjbTimeCap_of_le c (((b : ℝ) - c) / 2) a hc.1.le,
      NNReal.coe_one, one_mul] using hh

  have hlim := (tendsto_integral_parisiSlabGradient_terminalCap (P := canonicalBrownianMeasure) s β j m hm b (X b) Z (hXm b) hZm 1 hZb).sub
    (tendsto_const_nhds (x := ∫ ω, Z ω * parisiSlabGradient s β j m b a (X a ω) ∂canonicalBrownianMeasure))
  have hright : Tendsto (fun c : ℝ => (∫ t in (a : ℝ)..(b : ℝ), err t) + 16 * β ^ 2 * ((b : ℝ) - c))
      (𝓝[<] (b : ℝ)) (𝓝 (∫ t in (a : ℝ)..(b : ℝ), err t)) := by
    have hi : Tendsto (fun c : ℝ => c) (𝓝[<] (b : ℝ)) (𝓝 (b : ℝ)) := nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := ∫ t in (a : ℝ)..(b : ℝ), err t)).add
      (((tendsto_const_nhds (x := (b : ℝ))).sub hi).const_mul (16 * β ^ 2))
  have hh := le_of_tendsto_of_tendsto hlim.norm hright (by
    filter_upwards [Ioo_mem_nhdsLT (NNReal.coe_lt_coe.mpr hab)] with c hc
    exact hpoint c hc)
  simpa only [X, herror] using hh

end Paper
