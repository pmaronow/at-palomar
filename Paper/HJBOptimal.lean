module

public import Paper.HJBVerification
public import Paper.HJBEndpoint

@[expose] public section

/-! Perturbed finite-slab HJB verification.  The deterministic error permits
applying a rounded-grid PDE to a state driven by the original CDF. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace Paper
open SpinGlass SpinGlass.Targets

section ErrorVerification
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ≥0) (hab : a ≤ b) (K : ℝ≥0)
    (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K)
include hc hf htdiff hslice hdt hdx hsecond hab K hK

set_option maxHeartbeats 1000000 in
/-- A pathwise integral bound on the generator gives an expected payoff bound. -/
theorem hjb_control_expected_integral_upper (cost : ℝ → Ω → ℝ) (E : ℝ)
    (hcost : ∀ sample, IntervalIntegrable (fun s => cost s sample) volume a b)
    (hgen : ∀ sample, (∫ r in (a : ℝ)..(b : ℝ),
      hjbGenerator X d β f r sample - cost r sample) ≤ E)
    (hia : Integrable (fun sample => f a (X a sample)) P)
    (hib : Integrable (fun sample => f b (X b sample)) P)
    (hic : Integrable (fun sample => ∫ s in (a : ℝ)..(b : ℝ), cost s sample) P) :
    (∫ sample, f b (X b sample) - (∫ s in (a : ℝ)..(b : ℝ), cost s sample) ∂P) ≤
      (∫ sample, f a (X a sample) ∂P) + E := by
  obtain ⟨N, hN, hNzero, hformula⟩ := hjb_ito_increment hc f hf htdiff hslice hdt hdx hsecond a b hab K hK
  have hbound : ∀ᵐ sample ∂P, f b (X b sample) - (∫ r in (a : ℝ)..(b : ℝ), cost r sample) ≤
      f a (X a sample) + N sample + E := by
    filter_upwards [hformula] with sample he
    have hgi : IntervalIntegrable (fun r => hjbGenerator X d β f r sample) volume a b :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le (NNReal.coe_le_coe.mpr hab)] using
          (hjbGenerator_integrableOn hc f hdt hdx hsecond a b sample))
    have hh := hgen sample
    rw [intervalIntegral.integral_sub hgi (hcost sample)] at hh
    rw [he]
    linarith
  have hh := integral_mono_ae (hib.sub hic) ((hia.add hN).add (integrable_const E)) hbound
  have hAdd := integral_add (hia.add hN) (integrable_const E)
  have hAddN := integral_add hia hN
  simp only [Pi.add_apply] at hAdd hAddN
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [hAdd, hAddN, hNzero, add_zero, integral_const] at hh
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hh

set_option maxHeartbeats 1000000 in
/-- The corresponding lower integral bound proves optimal-control equality
when both error bounds tend to zero. -/
theorem hjb_control_expected_integral_lower (cost : ℝ → Ω → ℝ) (E : ℝ)
    (hcost : ∀ sample, IntervalIntegrable (fun s => cost s sample) volume a b)
    (hgen : ∀ sample, E ≤ (∫ r in (a : ℝ)..(b : ℝ),
      hjbGenerator X d β f r sample - cost r sample))
    (hia : Integrable (fun sample => f a (X a sample)) P)
    (hib : Integrable (fun sample => f b (X b sample)) P)
    (hic : Integrable (fun sample => ∫ s in (a : ℝ)..(b : ℝ), cost s sample) P) :
    (∫ sample, f a (X a sample) ∂P) + E ≤
      ∫ sample, f b (X b sample) - (∫ s in (a : ℝ)..(b : ℝ), cost s sample) ∂P := by
  obtain ⟨N, hN, hNzero, hformula⟩ := hjb_ito_increment hc f hf htdiff hslice hdt hdx hsecond a b hab K hK
  have hbound : ∀ᵐ sample ∂P, f a (X a sample) + N sample + E ≤
      f b (X b sample) - (∫ r in (a : ℝ)..(b : ℝ), cost r sample) := by
    filter_upwards [hformula] with sample he
    have hgi : IntervalIntegrable (fun r => hjbGenerator X d β f r sample) volume a b :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le (NNReal.coe_le_coe.mpr hab)] using
          (hjbGenerator_integrableOn hc f hdt hdx hsecond a b sample))
    have hh := hgen sample
    rw [intervalIntegral.integral_sub hgi (hcost sample)] at hh
    rw [he]
    linarith
  have hh := integral_mono_ae ((hia.add hN).add (integrable_const E)) (hib.sub hic) hbound
  have hAdd := integral_add (hia.add hN) (integrable_const E)
  have hAddN := integral_add hia hN
  simp only [Pi.add_apply] at hAdd hAddN
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [hAdd, hAddN, hNzero, add_zero, integral_const] at hh
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hh
end ErrorVerification

/-- The true CDF may differ from the grid slab coefficient.  Its contribution
is explicit, rather than hidden in a state-law assumption. -/
lemma hjbSlabTest_generator_mass_gap {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (m b c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hb : c + δ ≤ b) (t x A r : ℝ) :
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * r * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 -
      β ^ 2 / 2 * r * A ^ 2 =
    β ^ 2 / 2 * (1 - hjbTimeCapD c δ t) *
      (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
        m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2) -
      β ^ 2 / 2 * m * (A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x) ^ 2 +
      β ^ 2 * (r - m) *
        (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * A - A ^ 2 / 2) := by
  simp only [itoTimeDerivative, itoSpaceDerivative, itoSpaceSecondDerivative,
    (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb t x).deriv,
    deriv_hjbSlabTest_spatial, deriv_hjbSlabTest_spatial_second]
  ring

lemma hjb_control_mass_error_norm {A G r m β : ℝ} (hA : ‖A‖ ≤ 1) (hG : ‖G‖ ≤ 1) :
    ‖β ^ 2 * (r - m) * (G * A - A ^ 2 / 2)‖ ≤ (3 / 2 : ℝ) * β ^ 2 * |r - m| := by
  have hga : ‖G * A‖ ≤ 1 := by simpa only [norm_mul] using mul_le_one₀ hG (norm_nonneg A) hA
  have hasq : ‖A ^ 2 / 2‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div, norm_pow, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg A) hA) (by norm_num)
  have hh : ‖G * A - A ^ 2 / 2‖ ≤ (3 / 2 : ℝ) := by
    calc
      _ ≤ ‖G * A‖ + ‖A ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + 1 / 2 := add_le_add hga hasq
      _ = _ := by norm_num
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_eq_abs]
  have hn : 0 ≤ β ^ 2 * |r - m| := mul_nonneg (sq_nonneg β) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hh hn]

lemma hjbSlabTest_generator_perturbed_upper {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b)
    (t x A r : ℝ) (hA : ‖A‖ ≤ 1) :
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * r * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 -
      β ^ 2 / 2 * r * A ^ 2 ≤
    (3 / 2 : ℝ) * β ^ 2 * |r - m| + if t ≤ c then 0 else β ^ 2 / 2 := by
  have hbase := hjbSlabTest_generator_upper s β hβ j hm b c hδ hb t x A
  have hgap := hjbSlabTest_generator_gap s β hβ j m b c hδ hb t x A
  have hnew := hjbSlabTest_generator_mass_gap s β hβ j m b c hδ hb t x A r
  have hG : ‖parisiSlabGradient s β j m b (hjbTimeCap c δ t) x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b _ x
  have hn := hjb_control_mass_error_norm (β := β) (r := r) (m := m) hA hG
  have hu := (le_abs_self (β ^ 2 * (r - m) *
    (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * A - A ^ 2 / 2))).trans hn
  linarith

lemma hjbSlabTest_generator_perturbed_lower {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b)
    (t x A r : ℝ) (hA : ‖A‖ ≤ 1) {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : t ≤ c → ‖A - parisiSlabGradient s β j m b t x‖ ≤ eps) :
    -(3 / 2 : ℝ) * β ^ 2 * |r - m| - β ^ 2 / 2 * eps ^ 2 -
      (if t ≤ c then 0 else 2 * β ^ 2) ≤
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * r * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 -
      β ^ 2 / 2 * r * A ^ 2 := by
  have hnew := hjbSlabTest_generator_mass_gap s β hβ j m b c hδ hb t x A r
  have hH := parisiSlabHessian_nonneg s β j hm b (hjbTimeCap c δ t) x
  have hG : ‖parisiSlabGradient s β j m b (hjbTimeCap c δ t) x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b _ x
  have hn := hjb_control_mass_error_norm (β := β) (r := r) (m := m) hA hG
  have hl := (neg_abs_le (β ^ 2 * (r - m) *
    (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * A - A ^ 2 / 2)))
  have herr : -(3 / 2 : ℝ) * β ^ 2 * |r - m| ≤ β ^ 2 * (r - m) *
      (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x * A - A ^ 2 / 2) := by
    rw [Real.norm_eq_abs] at hn
    linarith
  have hm0 := hm.1
  have hcap := hjbTimeCapD_le_one c hδ t
  have hp : 0 ≤ β ^ 2 / 2 * (1 - hjbTimeCapD c δ t) *
      (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
        m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2) := by positivity
  by_cases ht : t ≤ c
  · have hd := hclose ht
    rw [hjbTimeCap_of_le c δ t ht] at hnew
    have hsq : (A - parisiSlabGradient s β j m b t x) ^ 2 ≤ eps ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hm1 := mul_le_mul_of_nonneg_right hm.2 (sq_nonneg (A - parisiSlabGradient s β j m b t x))
    simp only [one_mul] at hm1
    have hmulp := mul_le_mul_of_nonneg_left (hm1.trans hsq) (by positivity : 0 ≤ β ^ 2 / 2)
    rw [hjbTimeCap_of_le c δ t ht] at hp herr
    simp only [ite_eq_left ht] at *
    linarith
  · have hd : ‖A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith)
    have hsq : (A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x) ^ 2 ≤ 4 := by
      simpa only [Real.norm_eq_abs, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hm1 := mul_le_mul_of_nonneg_right hm.2 (sq_nonneg (A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x))
    simp only [one_mul] at hm1
    have hmulp := mul_le_mul_of_nonneg_left (hm1.trans hsq) (by positivity : 0 ≤ β ^ 2 / 2)
    have hep : 0 ≤ β ^ 2 / 2 * eps ^ 2 := by positivity
    simp only [ite_eq_right ht]
    linarith

set_option maxHeartbeats 1000000 in
/-- The rounded slab verifies a state driven by any coefficient `R`, with
an explicit deterministic coefficient error and a spatial-gradient error. -/
theorem parisiSlab_control_cap_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    {k : ℕ} (s : RSBScheme k) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (a b : ℝ≥0) (c : ℝ) (hac : (a : ℝ) ≤ c) (hcb : c < (b : ℝ))
    (R : ℝ → ℝ) (A : ℝ → Ω → ℝ) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (a : ℝ) (b : ℝ), d r.toNNReal sample = β ^ 2 * R r * A r sample)
    (hcost : ∀ sample, IntervalIntegrable (fun r => β ^ 2 / 2 * R r * A r sample ^ 2) volume a b)
    (hicost : Integrable (fun sample => ∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * R r * A r sample ^ 2) P)
    (herr : IntervalIntegrable (fun r => (3 / 2 : ℝ) * β ^ 2 * |R r - m|) volume a b)
    (hXa : Integrable (X a) P) (hXb : Integrable (X b) P)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ sample, ∀ r ∈ Icc (a : ℝ) (b : ℝ),
      ‖A r sample - parisiSlabGradient s β j m b r (X r.toNNReal sample)‖ ≤ eps) :
    let payoff := ∫ sample, parisiSlabPotential s β j m b
      (hjbTimeCap c (((b : ℝ) - c) / 2) b) (X b sample) -
      (∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * R r * A r sample ^ 2) ∂P
    let initial := ∫ sample, parisiSlabPotential s β j m b a (X a sample) ∂P
    let error := ∫ r in (a : ℝ)..(b : ℝ), (3 / 2 : ℝ) * β ^ 2 * |R r - m|
    payoff ≤ initial + error + β ^ 2 / 2 * ((b : ℝ) - c) ∧
      initial - error - β ^ 2 / 2 * eps ^ 2 * ((b : ℝ) - a) -
        2 * β ^ 2 * ((b : ℝ) - c) ≤ payoff := by
  let δ := ((b : ℝ) - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : c + δ ≤ (b : ℝ) := by dsimp [δ]; linarith
  have habR : (a : ℝ) ≤ b := hac.trans hcb.le
  have hab : a ≤ b := NNReal.coe_le_coe.mp habR
  let f := hjbSlabTest s β j m b c δ
  let cost := fun r sample => β ^ 2 / 2 * R r * A r sample ^ 2
  let err := fun r => (3 / 2 : ℝ) * β ^ 2 * |R r - m|
  let Q := β ^ 2 / 2 * eps ^ 2
  have hf := continuous_hjbSlabTest s β j hm.1 b c δ
  have ht : ∀ x, Differentiable ℝ (fun r => f r x) := fun x r =>
    (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb r x).differentiableAt
  have hslice := contDiff_hjbSlabTest_spatial s β j hm.1 b c δ
  have hdt := continuous_hjbSlabTest_timeDerivative s β hβ j hm.1 b c hδ hb
  have hdx := continuous_hjbSlabTest_spaceDerivative s β j hm.1 b c δ
  have hxx := continuous_hjbSlabTest_spaceSecondDerivative s β j hm.1 b c δ
  have hK : ∀ r ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f r x‖ ≤ (1 : ℝ≥0) := by
    intro r hr x
    exact norm_hjbSlabTest_spaceDerivative_le_one s β j hm b c δ r x
  have hia : Integrable (fun sample => f a (X a sample)) P := by
    simpa only [f, hjbSlabTest, hjbTimeCap_of_le c δ a hac] using
      integrable_parisiSlabPotential s β j hm b a hXa
  have hib : Integrable (fun sample => f b (X b sample)) P :=
    integrable_parisiSlabPotential s β j hm b _ hXb
  have hgi (sample : Ω) : IntervalIntegrable (fun r => hjbGenerator X d β f r sample) volume a b :=
    IntegrableOn.intervalIntegrable (by
      simpa only [uIcc_of_le habR] using hjbGenerator_integrableOn hc f hdt hdx hxx a b sample)
  have hu (sample : Ω) : (∫ r in (a : ℝ)..(b : ℝ), hjbGenerator X d β f r sample - cost r sample) ≤
      (∫ r in (a : ℝ)..(b : ℝ), err r) + β ^ 2 / 2 * ((b : ℝ) - c) := by
    have hp (r : ℝ) (hr : r ∈ Icc (a : ℝ) (b : ℝ)) :=
      hjbSlabTest_generator_perturbed_upper s β hβ j hm b c hδ hb r (X r.toNNReal sample) (A r sample) (R r) (hA r sample)
    have hh := intervalIntegral_le_tail (C := β ^ 2 / 2) hac hcb.le (((hgi sample).sub (hcost sample)).sub herr)
      (fun r hr => by
        have h := hp r ⟨hr.1, hr.2.trans hcb.le⟩
        unfold hjbGenerator; rw [hd sample r ⟨hr.1, hr.2.trans hcb.le⟩]
        simp only [ite_eq_left hr.2] at h
        dsimp only [f, cost, err]; linarith)
      (fun r hr => by
        have h := hp r ⟨hac.trans hr.1, hr.2⟩
        unfold hjbGenerator; rw [hd sample r ⟨hac.trans hr.1, hr.2⟩]
        have hi : (if r ≤ c then (0 : ℝ) else β ^ 2 / 2) ≤ β ^ 2 / 2 := by
          split_ifs
          · positivity
          · exact le_rfl
        dsimp only [f, cost, err]; linarith)
    rw [intervalIntegral.integral_sub ((hgi sample).sub (hcost sample)) herr] at hh
    dsimp only [cost, err] at *
    linarith
  have hl (sample : Ω) : -(∫ r in (a : ℝ)..(b : ℝ), err r) - Q * ((b : ℝ) - a) -
      2 * β ^ 2 * ((b : ℝ) - c) ≤
      (∫ r in (a : ℝ)..(b : ℝ), hjbGenerator X d β f r sample - cost r sample) := by
    have hp (r : ℝ) (hr : r ∈ Icc (a : ℝ) (b : ℝ)) :=
      hjbSlabTest_generator_perturbed_lower s β hβ j hm b c hδ hb r (X r.toNNReal sample) (A r sample) (R r)
        (hA r sample) heps (fun _ => hclose sample r hr)
    have hneg : IntervalIntegrable (fun r => -(hjbGenerator X d β f r sample - cost r sample) - err r - Q) volume a b :=
      ((((hgi sample).sub (hcost sample)).neg.sub herr).sub (intervalIntegrable_const (c := Q)))
    have hh := intervalIntegral_le_tail (C := 2 * β ^ 2) hac hcb.le hneg
      (fun r hr => by
        have h := hp r ⟨hr.1, hr.2.trans hcb.le⟩
        unfold hjbGenerator; rw [hd sample r ⟨hr.1, hr.2.trans hcb.le⟩]
        simp only [ite_eq_left hr.2] at h
        dsimp only [f, cost, err, Q]; linarith)
      (fun r hr => by
        have h := hp r ⟨hac.trans hr.1, hr.2⟩
        unfold hjbGenerator; rw [hd sample r ⟨hac.trans hr.1, hr.2⟩]
        have hi : (if r ≤ c then (0 : ℝ) else 2 * β ^ 2) ≤ 2 * β ^ 2 := by
          split_ifs
          · positivity
          · exact le_rfl
        dsimp only [f, cost, err, Q]; linarith)
    have hi2 : IntervalIntegrable (fun r => -(hjbGenerator X d β f r sample - cost r sample)) volume a b :=
      ((hgi sample).sub (hcost sample)).neg
    have hi1 : IntervalIntegrable (fun r => -(hjbGenerator X d β f r sample - cost r sample) - err r) volume a b :=
      hi2.sub herr
    have he1 := intervalIntegral.integral_sub hi1 (intervalIntegrable_const (c := Q))
    have he2 := intervalIntegral.integral_sub hi2 herr
    try simp only [Pi.sub_apply, Pi.neg_apply] at he1 he2
    rw [he1, he2, intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul] at hh
    linarith
  have hupper := hjb_control_expected_integral_upper hc f hf ht hslice hdt hdx hxx a b hab 1 hK cost _
    hcost hu hia hib hicost
  have hlower := hjb_control_expected_integral_lower hc f hf ht hslice hdt hdx hxx a b hab 1 hK cost _
    hcost hl hia hib hicost
  dsimp only
  constructor
  · simpa only [f, hjbSlabTest, cost, err, δ, hjbTimeCap_of_le c (((b : ℝ) - c) / 2) a hac, add_assoc] using hupper
  · dsimp only [f, hjbSlabTest, cost, err, δ, Q] at hlower
    rw [hjbTimeCap_of_le c (((b : ℝ) - c) / 2) a hac] at hlower
    linarith

set_option maxHeartbeats 1000000 in
/-- Removing the cap proves verification at both actual slab endpoints,
including a nonzero deterministic coefficient error. -/
theorem parisiSlab_control_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    {k : ℕ} (s : RSBScheme k) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (a b : ℝ≥0) (hab : a < b)
    (R : ℝ → ℝ) (A : ℝ → Ω → ℝ) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (a : ℝ) (b : ℝ), d r.toNNReal sample = β ^ 2 * R r * A r sample)
    (hcost : ∀ sample, IntervalIntegrable (fun r => β ^ 2 / 2 * R r * A r sample ^ 2) volume a b)
    (hicost : Integrable (fun sample => ∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * R r * A r sample ^ 2) P)
    (herr : IntervalIntegrable (fun r => (3 / 2 : ℝ) * β ^ 2 * |R r - m|) volume a b)
    (hXa : Integrable (X a) P) (hXb : Integrable (X b) P)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ sample, ∀ r ∈ Icc (a : ℝ) (b : ℝ),
      ‖A r sample - parisiSlabGradient s β j m b r (X r.toNNReal sample)‖ ≤ eps) :
    let payoff := ∫ sample, parisiSlabPotential s β j m b b (X b sample) -
      (∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * R r * A r sample ^ 2) ∂P
    let initial := ∫ sample, parisiSlabPotential s β j m b a (X a sample) ∂P
    let error := ∫ r in (a : ℝ)..(b : ℝ), (3 / 2 : ℝ) * β ^ 2 * |R r - m|
    payoff ≤ initial + error ∧
      initial - error - β ^ 2 / 2 * eps ^ 2 * ((b : ℝ) - a) ≤ payoff := by
  have habR : (a : ℝ) < b := NNReal.coe_lt_coe.mpr hab
  let C := ∫ sample, (∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * R r * A r sample ^ 2) ∂P
  let I := ∫ sample, parisiSlabPotential s β j m b a (X a sample) ∂P
  let E := ∫ r in (a : ℝ)..(b : ℝ), (3 / 2 : ℝ) * β ^ 2 * |R r - m|
  let B := β ^ 2 / 2 * eps ^ 2 * ((b : ℝ) - a)
  have hp := (tendsto_integral_parisiSlab_terminalCap s β j m hm a b habR (X b) hXb).sub
    (tendsto_const_nhds (x := C))
  have hup : Tendsto (fun c : ℝ => I + E + β ^ 2 / 2 * ((b : ℝ) - c)) (𝓝[<] (b : ℝ)) (𝓝 (I + E)) := by
    have hi : Tendsto (fun c : ℝ => c) (𝓝[<] (b : ℝ)) (𝓝 (b : ℝ)) := nhdsWithin_le_nhds
    convert (tendsto_const_nhds (x := I + E)).add ((tendsto_const_nhds.sub hi).const_mul (β ^ 2 / 2)) using 1 <;> simp
  have hlow : Tendsto (fun c : ℝ => I - E - B - 2 * β ^ 2 * ((b : ℝ) - c))
      (𝓝[<] (b : ℝ)) (𝓝 (I - E - B)) := by
    have hi : Tendsto (fun c : ℝ => c) (𝓝[<] (b : ℝ)) (𝓝 (b : ℝ)) := nhdsWithin_le_nhds
    convert (tendsto_const_nhds (x := I - E - B)).sub ((tendsto_const_nhds.sub hi).const_mul (2 * β ^ 2)) using 1 <;> simp
  have hupper := le_of_tendsto_of_tendsto hp hup (by
    filter_upwards [Ioo_mem_nhdsLT habR] with c hcc
    have hh := (parisiSlab_control_cap_error_bounds hc s hβ j hm a b c hcc.1.le hcc.2 R A hA hd
      hcost hicost herr hXa hXb heps hclose).1
    rw [integral_sub (integrable_parisiSlabPotential s β j hm b _ hXb) hicost] at hh
    exact hh)
  have hlower := le_of_tendsto_of_tendsto hlow hp (by
    filter_upwards [Ioo_mem_nhdsLT habR] with c hcc
    have hh := (parisiSlab_control_cap_error_bounds hc s hβ j hm a b c hcc.1.le hcc.2 R A hA hd
      hcost hicost herr hXa hXb heps hclose).2
    rw [integral_sub (integrable_parisiSlabPotential s β j hm b _ hXb) hicost] at hh
    exact hh)
  dsimp only
  rw [integral_sub (integrable_parisiSlabPotential s β j hm b b hXb) hicost]
  exact ⟨hupper, hlower⟩

end Paper
