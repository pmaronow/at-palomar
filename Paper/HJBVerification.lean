module

public import Paper.ParisiFiniteCells
public import Paper.ItoExpectation
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-!
# Finite-slab Hamilton--Jacobi--Bellman verification

A C¹ upper time cap localizes each actual Cole--Hopf slab below its terminal
variance-zero boundary. This supplies globally regular test functions for the
genuine Itô theorem while preserving the PDE on each compact subslab.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace Paper
open SpinGlass SpinGlass.Targets

/-- A differentiable upper cap equal to identity before `c`, always below `c+δ`. -/
def hjbTimeCap (c δ t : ℝ) : ℝ :=
  if t ≤ c then t else c + δ * (1 - Real.exp (-(t - c) / δ))

def hjbTimeCapD (c δ t : ℝ) : ℝ :=
  if t ≤ c then 1 else Real.exp (-(t - c) / δ)

@[simp] theorem hjbTimeCap_of_le (c δ t : ℝ) (ht : t ≤ c) : hjbTimeCap c δ t = t := by
  simp [hjbTimeCap, ht]

lemma hjbTimeCap_lt (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : hjbTimeCap c δ t < c + δ := by
  unfold hjbTimeCap
  split_ifs with ht
  · linarith
  · have he := Real.exp_pos (-(t - c) / δ)
    nlinarith

@[fun_prop] theorem continuous_hjbTimeCap (c δ : ℝ) : Continuous (hjbTimeCap c δ) := by
  unfold hjbTimeCap
  apply Continuous.if_le continuous_id (by fun_prop) continuous_id continuous_const
  intro t ht
  change t = c at ht
  subst t
  simp

@[fun_prop] theorem continuous_hjbTimeCapD (c δ : ℝ) : Continuous (hjbTimeCapD c δ) := by
  unfold hjbTimeCapD
  apply Continuous.if_le continuous_const (by fun_prop) continuous_id continuous_const
  intro t ht
  change t = c at ht
  subst t
  simp

private lemma hasDerivAt_hjbTimeCap_tail (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => c + δ * (1 - Real.exp (-(s - c) / δ)))
      (Real.exp (-(t - c) / δ)) t := by
  have hd := ((((hasDerivAt_id t).sub_const c).neg.div_const δ).exp.const_sub 1).const_mul δ
  convert hd.const_add c using 1
  · funext s
    simp only [Function.comp_def, id_eq, Pi.neg_apply]
  · simp only [Function.comp_def, id_eq, Pi.neg_apply]
    field_simp

/-- The upper time cap has a genuine continuous derivative even at the junction. -/
theorem hasDerivAt_hjbTimeCap (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (hjbTimeCap c δ) (hjbTimeCapD c δ t) t := by
  rcases lt_trichotomy t c with ht | he | ht
  · simp only [hjbTimeCapD, ite_eq_left ht.le]
    apply (hasDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    change s < c at hs
    simp [hjbTimeCap, hs.le]
  · subst t
    have hl : HasDerivWithinAt (hjbTimeCap c δ) 1 (Iic c) c := by
      apply (hasDerivAt_id c).hasDerivWithinAt.congr_of_mem
      · intro s hs
        change s ≤ c at hs
        simp [hjbTimeCap, hs]
      · exact self_mem_Iic
    have hr : HasDerivWithinAt (hjbTimeCap c δ) 1 (Ici c) c := by
      have hd := (hasDerivAt_hjbTimeCap_tail c hδ.ne' c).hasDerivWithinAt (s := Ici c)
      simp only [sub_self, neg_zero, zero_div, Real.exp_zero] at hd
      apply hd.congr_of_mem
      · intro s hs
        change c ≤ s at hs
        by_cases he : s ≤ c
        · have heq : s = c := le_antisymm he hs
          subst s
          simp [hjbTimeCap]
        · simp [hjbTimeCap, he]
      · exact self_mem_Ici
    have hh := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hh
    simpa [hjbTimeCapD] using hh
  · have hd := hasDerivAt_hjbTimeCap_tail c hδ.ne' t
    simp only [hjbTimeCapD, ite_eq_right (not_le.mpr ht)]
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change c < s at hs
    simp [hjbTimeCap, not_le.mpr hs]

/-- Globally regular time-localized actual Cole--Hopf potential. -/
def hjbSlabTest {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (m b c δ : ℝ) (t x : ℝ) : ℝ :=
  parisiSlabPotential s β j m b (hjbTimeCap c δ t) x


lemma hjbSlabTest_hasDerivAt_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    HasDerivAt (hjbSlabTest s β j m b c δ t)
      (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x) x :=
  hasDerivAt_parisiSlabPotential_spatial s β j m b _ x

lemma hjbSlabTest_hasDerivAt_gradient {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    HasDerivAt (parisiSlabGradient s β j m b (hjbTimeCap c δ t))
      (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x) x :=
  hasDerivAt_parisiSlabGradient_spatial s β j m b _ x

lemma deriv_hjbSlabTest_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    deriv (hjbSlabTest s β j m b c δ t) x =
      parisiSlabGradient s β j m b (hjbTimeCap c δ t) x :=
  (hjbSlabTest_hasDerivAt_spatial s β j m b c δ t x).deriv

lemma deriv_hjbSlabTest_spatial_second {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b c δ t x : ℝ) :
    deriv (deriv (hjbSlabTest s β j m b c δ t)) x =
      parisiSlabHessian s β j m b (hjbTimeCap c δ t) x := by
  have he : deriv (hjbSlabTest s β j m b c δ t) =
      parisiSlabGradient s β j m b (hjbTimeCap c δ t) :=
    funext (deriv_hjbSlabTest_spatial s β j m b c δ t)
  rw [he, (hjbSlabTest_hasDerivAt_gradient s β j m b c δ t x).deriv]

lemma hasDerivAt_hjbSlabTest_time {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (m b c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hb : c + δ ≤ b) (t x : ℝ) :
    HasDerivAt (fun r => hjbSlabTest s β j m b c δ r x)
      (hjbTimeCapD c δ t * (-(β ^ 2 / 2)) *
        (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
          m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2)) t := by
  have hd := (hasDerivAt_parisiSlabPotential_time s β hβ j m b x
    ((hjbTimeCap_lt c hδ t).trans_le hb)).comp t (hasDerivAt_hjbTimeCap c hδ t)
  convert hd using 1
  · rfl
  · ring

lemma continuous_hjbSlabTest {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => hjbSlabTest s β j m b c δ p.1 p.2) :=
  (continuous_parisiSlab s β j hm b).1.comp
    ((continuous_hjbTimeCap c δ).comp continuous_fst |>.prodMk continuous_snd)

lemma contDiff_hjbSlabTest_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ t : ℝ) :
    ContDiff ℝ 2 (hjbSlabTest s β j m b c δ t) := by
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) _
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hjbSlabTest_hasDerivAt_spatial s β j m b c δ t x).differentiableAt, by simp, ?_⟩
  have he : deriv (hjbSlabTest s β j m b c δ t) =
      parisiSlabGradient s β j m b (hjbTimeCap c δ t) :=
    funext (deriv_hjbSlabTest_spatial s β j m b c δ t)
  rw [he, contDiff_one_iff_deriv]
  refine ⟨fun x => (hjbSlabTest_hasDerivAt_gradient s β j m b c δ t x).differentiableAt, ?_⟩
  have hge : deriv (parisiSlabGradient s β j m b (hjbTimeCap c δ t)) =
      parisiSlabHessian s β j m b (hjbTimeCap c δ t) :=
    funext (fun x => (hjbSlabTest_hasDerivAt_gradient s β j m b c δ t x).deriv)
  rw [hge]
  exact (continuous_parisiSlab s β j hm b).2.2.comp (continuous_const.prodMk continuous_id)

lemma continuous_hjbSlabTest_spaceDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (hjbSlabTest s β j m b c δ) p.1 p.2) := by
  simp only [itoSpaceDerivative, deriv_hjbSlabTest_spatial]
  exact (continuous_parisiSlab s β j hm b).2.1.comp
    (((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd)

lemma continuous_hjbSlabTest_spaceSecondDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c δ : ℝ) :
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) p.1 p.2) := by
  simp only [itoSpaceSecondDerivative, deriv_hjbSlabTest_spatial_second]
  exact (continuous_parisiSlab s β j hm b).2.2.comp
    (((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd)

lemma continuous_hjbSlabTest_timeDerivative {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b c : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b) :
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (hjbSlabTest s β j m b c δ) p.1 p.2) := by
  simp only [itoTimeDerivative, (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb _ _).deriv]
  have hcmap : Continuous (fun p : ℝ × ℝ => (hjbTimeCap c δ p.1, p.2)) :=
    ((continuous_hjbTimeCap c δ).comp continuous_fst).prodMk continuous_snd
  exact (((continuous_hjbTimeCapD c δ).comp continuous_fst).mul continuous_const).mul
    (((continuous_parisiSlab s β j hm b).2.2.comp hcmap).add
      (((continuous_parisiSlab s β j hm b).2.1.comp hcmap).pow 2 |>.const_mul m))

lemma norm_hjbSlabTest_spaceDerivative_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b c δ t x : ℝ) :
    ‖itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x‖ ≤ 1 := by
  simp only [itoSpaceDerivative, deriv_hjbSlabTest_spatial, Real.norm_eq_abs]
  exact abs_parisiSlabGradient_le_one s β j hm b _ x

/-- The actual PDE gives the HJB square-completion identity on the unchanged subslab. -/
theorem hjbSlabTest_square_completion {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (m b c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hb : c + δ ≤ b) (t x A : ℝ) (ht : t ≤ c) :
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * m * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 -
      β ^ 2 / 2 * m * A ^ 2 =
    -(β ^ 2 / 2 * m) * (A - parisiSlabGradient s β j m b t x) ^ 2 := by
  simp only [itoTimeDerivative, itoSpaceDerivative, itoSpaceSecondDerivative,
    (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb t x).deriv,
    deriv_hjbSlabTest_spatial, deriv_hjbSlabTest_spatial_second, hjbTimeCap_of_le c δ t ht,
    hjbTimeCapD, ite_eq_left ht]
  ring


/-- The real-time generator evaluated along an actual Itô state. -/
def hjbGenerator {Ω : Type*} (X d : ℝ≥0 → Ω → ℝ) (β : ℝ)
    (f : ℝ → ℝ → ℝ) (s : ℝ) (sample : Ω) : ℝ :=
  itoTimeDerivative f s (X s.toNNReal sample) +
    itoSpaceDerivative f s (X s.toNNReal sample) * d s.toNNReal sample +
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s (X s.toNNReal sample) * β ^ 2

lemma hjbGenerator_integrableOn {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (a b : ℝ) (sample : Ω) : IntegrableOn (fun s => hjbGenerator X d β f s sample) (Icc a b) := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  have hp : Continuous (fun s : ℝ => (s, X s.toNNReal sample)) :=
    continuous_id.prodMk ((hc.continuous_state sample).comp continuous_real_toNNReal)
  have ht := (hdt.comp hp).integrableOn_Icc (μ := volume) (a := a) (b := b)
  have hx := (hdx.comp hp).integrableOn_Icc (μ := volume) (a := a) (b := b)
  have hd : AEStronglyMeasurable (fun s : ℝ => d s.toNNReal sample) (volume.restrict (Icc a b)) :=
    (hc.measurable_drift.comp (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  have hxd := hx.mul_bdd hd (Eventually.of_forall fun s => hD s.toNNReal sample)
  have hxx := (((hsecond.comp hp).const_mul (1 / 2)).mul_const (β ^ 2)).integrableOn_Icc
    (μ := volume) (a := a) (b := b)
  exact (ht.add hxd).add hxx

lemma hjbGenerator_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (b : ℝ≥0) (sample : Ω) :
    (∫ s in (0 : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) =
      generalItoTimeIntegral f X b sample + itoDriftIntegral X d f b sample +
        generalItoQuadraticIntegral f X (fun _ _ => β) b sample := by
  obtain ⟨D, hD⟩ := hc.bounded_drift
  have hp : Continuous (fun s : ℝ => (s, X s.toNNReal sample)) :=
    continuous_id.prodMk ((hc.continuous_state sample).comp continuous_real_toNNReal)
  have ht := (hdt.comp hp).integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (b : ℝ))
  have hx := (hdx.comp hp).integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (b : ℝ))
  have hd : AEStronglyMeasurable (fun s : ℝ => d s.toNNReal sample) (volume.restrict (Icc 0 (b : ℝ))) :=
    (hc.measurable_drift.comp (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
  have hxd := hx.mul_bdd hd (Eventually.of_forall fun s => hD s.toNNReal sample)
  have hxx := (((hsecond.comp hp).const_mul (1 / 2)).mul_const (β ^ 2)).integrableOn_Icc
    (μ := volume) (a := (0 : ℝ)) (b := (b : ℝ))
  dsimp only [Function.comp_def] at ht hx hxd hxx
  rw [intervalIntegral.integral_of_le b.coe_nonneg, ← integral_Icc_eq_integral_Ioc]
  unfold hjbGenerator generalItoTimeIntegral itoDriftIntegral generalItoQuadraticIntegral
  have hadd := integral_add (ht.add hxd) hxx
  have hadd2 := integral_add ht hxd
  simp only [Pi.add_apply] at hadd hadd2
  rw [hadd, hadd2, ← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  ring

set_option maxHeartbeats 1000000 in
/-- The genuine Itô increment on an arbitrary finite subinterval, with centered noise. -/
theorem hjb_ito_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
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
    (hK : ∀ s ∈ Icc (0 : ℝ) (b : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K) :
    ∃ N : Ω → ℝ, Integrable N P ∧ (∫ sample, N sample ∂P) = 0 ∧
      ∀ᵐ sample ∂P, f b (X b sample) = f a (X a sample) +
        (∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) + N sample := by
  have hKa : ∀ s ∈ Icc (0 : ℝ) (a : ℝ), ∀ x, ‖itoSpaceDerivative f s x‖ ≤ K :=
    fun s hs x => hK s ⟨hs.1, hs.2.trans (NNReal.coe_le_coe.mpr hab)⟩ x
  obtain ⟨Na, hNa, _hNa1, hNazero, hfa⟩ := ito_centered_weighted_of_boundedDrift hc f hf htdiff hslice
    hdt hdx hsecond a K hKa (fun _ => 1) stronglyMeasurable_const 1 (by intros; norm_num)
  obtain ⟨Nb, hNb, _hNb1, hNbzero, hfb⟩ := ito_centered_weighted_of_boundedDrift hc f hf htdiff hslice
    hdt hdx hsecond b K hK (fun _ => 1) stronglyMeasurable_const 1 (by intros; norm_num)
  simp only [one_mul] at hNazero hNbzero
  refine ⟨fun sample => Nb sample - Na sample, hNb.sub hNa, by rw [integral_sub hNb hNa, hNbzero, hNazero, sub_self], ?_⟩
  filter_upwards [hfa, hfb] with sample hsamplea hsampleb
  have hai : IntervalIntegrable (fun s => hjbGenerator X d β f s sample) volume 0 a :=
    IntegrableOn.intervalIntegrable (by
      simpa only [uIcc_of_le a.coe_nonneg] using hjbGenerator_integrableOn hc f hdt hdx hsecond 0 a sample)
  have hbi : IntervalIntegrable (fun s => hjbGenerator X d β f s sample) volume 0 b :=
    IntegrableOn.intervalIntegrable (by
      simpa only [uIcc_of_le b.coe_nonneg] using hjbGenerator_integrableOn hc f hdt hdx hsecond 0 b sample)
  have he : (∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) =
      (∫ s in (0 : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) -
      ∫ s in (0 : ℝ)..(a : ℝ), hjbGenerator X d β f s sample :=
    (intervalIntegral.integral_interval_sub_left hbi hai).symm
  rw [he, hjbGenerator_integral_eq hc f hdt hdx hsecond b sample,
    hjbGenerator_integral_eq hc f hdt hdx hsecond a sample, hsamplea, hsampleb]
  ring


section Verification
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

/-- Actual Itô verification gives the control payoff upper bound. -/
theorem hjb_control_expected_upper (cost : ℝ → Ω → ℝ)
    (hcost : ∀ sample, IntervalIntegrable (fun s => cost s sample) volume a b)
    (hgen : ∀ sample, ∀ s ∈ Icc (a : ℝ) (b : ℝ), hjbGenerator X d β f s sample ≤ cost s sample)
    (hia : Integrable (fun sample => f a (X a sample)) P)
    (hib : Integrable (fun sample => f b (X b sample)) P)
    (hic : Integrable (fun sample => ∫ s in (a : ℝ)..(b : ℝ), cost s sample) P) :
    (∫ sample, f b (X b sample) - (∫ s in (a : ℝ)..(b : ℝ), cost s sample) ∂P) ≤
      ∫ sample, f a (X a sample) ∂P := by
  obtain ⟨N, hN, hNzero, hformula⟩ := hjb_ito_increment hc f hf htdiff hslice hdt hdx hsecond a b hab K hK
  have hbound : ∀ᵐ sample ∂P, f b (X b sample) - (∫ s in (a : ℝ)..(b : ℝ), cost s sample) ≤
      f a (X a sample) + N sample := by
    filter_upwards [hformula] with sample he
    have hi : IntervalIntegrable (fun s => hjbGenerator X d β f s sample) volume a b :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le (NNReal.coe_le_coe.mpr hab)] using
          hjbGenerator_integrableOn hc f hdt hdx hsecond a b sample)
    have hbnd := intervalIntegral.integral_mono_on (NNReal.coe_le_coe.mpr hab) hi (hcost sample) (hgen sample)
    rw [he]
    linarith
  have hh := integral_mono_ae (hib.sub hic) (hia.add hN) hbound
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  have hs := integral_add hia hN
  try simp only [Pi.add_apply] at hs
  rw [hs, hNzero, add_zero] at hh
  exact hh

/-- The optimal gradient control attains equality by the actual Itô equation. -/
theorem hjb_control_expected_eq (cost : ℝ → Ω → ℝ)
    (hcost : ∀ sample, IntervalIntegrable (fun s => cost s sample) volume a b)
    (hgen : ∀ sample, ∀ s ∈ Icc (a : ℝ) (b : ℝ), hjbGenerator X d β f s sample = cost s sample)
    (hia : Integrable (fun sample => f a (X a sample)) P)
    (hib : Integrable (fun sample => f b (X b sample)) P)
    (hic : Integrable (fun sample => ∫ s in (a : ℝ)..(b : ℝ), cost s sample) P) :
    (∫ sample, f b (X b sample) - (∫ s in (a : ℝ)..(b : ℝ), cost s sample) ∂P) =
      ∫ sample, f a (X a sample) ∂P := by
  obtain ⟨N, hN, hNzero, hformula⟩ := hjb_ito_increment hc f hf htdiff hslice hdt hdx hsecond a b hab K hK
  have he : (fun sample => f b (X b sample) - ∫ s in (a : ℝ)..(b : ℝ), cost s sample) =ᵐ[P]
      (fun sample => f a (X a sample) + N sample) := by
    filter_upwards [hformula] with sample he
    have hi : (∫ s in (a : ℝ)..(b : ℝ), hjbGenerator X d β f s sample) =
        ∫ s in (a : ℝ)..(b : ℝ), cost s sample := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hgen sample s (by simpa only [uIcc_of_le (NNReal.coe_le_coe.mpr hab)] using hs)
    rw [he, hi]
    ring
  rw [integral_congr_ae he, integral_add hia hN, hNzero, add_zero]

end Verification

lemma hjb_control_cost_norm_le {Ω : Type*} (β : ℝ) {m : ℝ} (hm : 0 ≤ m)
    (A : ℝ → Ω → ℝ) (hA : ∀ s sample, ‖A s sample‖ ≤ 1) (s : ℝ) (sample : Ω) :
    ‖β ^ 2 / 2 * m * A s sample ^ 2‖ ≤ β ^ 2 / 2 * m := by
  rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2 * m), norm_pow]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) (hA s sample))

lemma hjb_control_cost_intervalIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) {m : ℝ} (hm : 0 ≤ m) (A : ℝ → Ω → ℝ)
    (hAm : Measurable (Function.uncurry A)) (hA : ∀ s sample, ‖A s sample‖ ≤ 1)
    (a b : ℝ) (sample : Ω) :
    IntervalIntegrable (fun s => β ^ 2 / 2 * m * A s sample ^ 2) volume a b := by
  apply (intervalIntegrable_const (c := (β ^ 2 / 2 * m))).mono_fun'
    (((hAm.comp (measurable_id.prodMk measurable_const)).pow_const 2).const_mul _).aestronglyMeasurable
  exact Eventually.of_forall (fun s => hjb_control_cost_norm_le β hm A hA s sample)

lemma hjb_control_cost_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (β : ℝ) {m : ℝ} (hm : 0 ≤ m)
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A))
    (hA : ∀ s sample, ‖A s sample‖ ≤ 1) (a b : ℝ) (hab : a ≤ b) :
    Integrable (fun sample => ∫ s in a..b, β ^ 2 / 2 * m * A s sample ^ 2) P := by
  have hmj : Measurable (fun p : ℝ × Ω => β ^ 2 / 2 * m * A p.1 p.2 ^ 2) :=
    (hAm.pow_const 2).const_mul _
  have hi := hmj.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc a b))
  have hmInt : Measurable (fun sample => ∫ s in a..b, β ^ 2 / 2 * m * A s sample ^ 2) := by
    simpa only [intervalIntegral.integral_of_le hab] using hi.measurable
  apply (integrable_const ((β ^ 2 / 2 * m) * |b - a|)).mono' hmInt.aestronglyMeasurable
  exact Eventually.of_forall (fun sample => intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => hjb_control_cost_norm_le β hm A hA s sample))

set_option maxHeartbeats 1000000 in
/-- The actual Cole--Hopf slab bounds every bounded measurable control payoff
along an actual Itô state, on each compact subslab. -/
theorem parisiSlab_control_upper {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    {k : ℕ} (s : RSBScheme k) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b : ℝ) (a c : ℝ≥0) (hac : a ≤ c) (hcb : (c : ℝ) < b)
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A))
    (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (a : ℝ) (c : ℝ), d r.toNNReal sample = β ^ 2 * m * A r sample)
    (hia : Integrable (fun sample => parisiSlabPotential s β j m b a (X a sample)) P)
    (hic : Integrable (fun sample => parisiSlabPotential s β j m b c (X c sample)) P) :
    (∫ sample, parisiSlabPotential s β j m b c (X c sample) -
      (∫ r in (a : ℝ)..(c : ℝ), β ^ 2 / 2 * m * A r sample ^ 2) ∂P) ≤
      ∫ sample, parisiSlabPotential s β j m b a (X a sample) ∂P := by
  let δ := (b - (c : ℝ)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : (c : ℝ) + δ ≤ b := by dsimp [δ]; linarith
  let f := hjbSlabTest s β j m b c δ
  have hfa : ∀ sample, f a (X a sample) = parisiSlabPotential s β j m b a (X a sample) := by
    intro sample
    simp only [f, hjbSlabTest, hjbTimeCap_of_le _ _ _ (NNReal.coe_le_coe.mpr hac)]
  have hfc : ∀ sample, f c (X c sample) = parisiSlabPotential s β j m b c (X c sample) := by
    intro sample
    simp only [f, hjbSlabTest, hjbTimeCap_of_le _ _ _ le_rfl]
  have hgen : ∀ sample, ∀ r ∈ Icc (a : ℝ) (c : ℝ), hjbGenerator X d β f r sample ≤
      β ^ 2 / 2 * m * A r sample ^ 2 := by
    intro sample r hr
    have he := hjbSlabTest_square_completion s β hβ j m b c hδ hb r (X r.toNNReal sample) (A r sample) hr.2
    unfold hjbGenerator
    rw [hd sample r hr]
    dsimp only [f]
    have hn : 0 ≤ β ^ 2 / 2 * m := mul_nonneg (by positivity) hm.1
    have hs : 0 ≤ (A r sample - parisiSlabGradient s β j m b r (X r.toNNReal sample)) ^ 2 := sq_nonneg _
    nlinarith [he, mul_nonneg hn hs]
  have hf := continuous_hjbSlabTest s β j hm.1 b c δ
  have ht : ∀ x, Differentiable ℝ (fun r => f r x) := fun x r =>
    (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb r x).differentiableAt
  have hslice := contDiff_hjbSlabTest_spatial s β j hm.1 b c δ
  have hdt := continuous_hjbSlabTest_timeDerivative s β hβ j hm.1 b c hδ hb
  have hdx := continuous_hjbSlabTest_spaceDerivative s β j hm.1 b c δ
  have hxx := continuous_hjbSlabTest_spaceSecondDerivative s β j hm.1 b c δ
  have hK : ∀ r ∈ Icc (0 : ℝ) (c : ℝ), ∀ x, ‖itoSpaceDerivative f r x‖ ≤ (1 : ℝ≥0) := by
    intro r hr x
    exact norm_hjbSlabTest_spaceDerivative_le_one s β j hm b c δ r x
  have hia' : Integrable (fun sample => f a (X a sample)) P := by simp_rw [hfa]; exact hia
  have hic' : Integrable (fun sample => f c (X c sample)) P := by simp_rw [hfc]; exact hic
  have hh := hjb_control_expected_upper hc f hf ht hslice hdt hdx hxx a c hac 1 hK
    (fun r sample => β ^ 2 / 2 * m * A r sample ^ 2)
    (hjb_control_cost_intervalIntegrable β hm.1 A hAm hA a c) hgen hia' hic'
    (hjb_control_cost_integrable β hm.1 A hAm hA a c (NNReal.coe_le_coe.mpr hac))
  simp_rw [hfa, hfc] at hh
  exact hh


lemma hjbTimeCapD_nonneg (c δ t : ℝ) : 0 ≤ hjbTimeCapD c δ t := by
  unfold hjbTimeCapD
  split_ifs
  · norm_num
  · exact (Real.exp_pos _).le

lemma hjbTimeCapD_le_one (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : hjbTimeCapD c δ t ≤ 1 := by
  unfold hjbTimeCapD
  split_ifs with ht
  · exact le_rfl
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (lt_of_not_ge ht).le)) hδ.le

lemma hjbTimeCap_ge (c : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : c ≤ t) : c ≤ hjbTimeCap c δ t := by
  unfold hjbTimeCap
  split_ifs with he
  · exact ht
  · have hexp : Real.exp (-(t - c) / δ) ≤ 1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr ht)) hδ.le)
    exact le_add_of_nonneg_right (mul_nonneg hδ.le (sub_nonneg.mpr hexp))

/-- Exact generator defect of a capped actual Cole--Hopf test. -/
theorem hjbSlabTest_generator_gap {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (m b c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hb : c + δ ≤ b) (t x A : ℝ) :
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * m * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 -
      β ^ 2 / 2 * m * A ^ 2 =
    β ^ 2 / 2 * (1 - hjbTimeCapD c δ t) *
      (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
        m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2) -
      β ^ 2 / 2 * m * (A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x) ^ 2 := by
  simp only [itoTimeDerivative, itoSpaceDerivative, itoSpaceSecondDerivative,
    (hasDerivAt_hjbSlabTest_time s β hβ j m b c hδ hb t x).deriv,
    deriv_hjbSlabTest_spatial, deriv_hjbSlabTest_spatial_second]
  ring

/-- The entire cap error is uniformly bounded and vanishes before the cap junction. -/
theorem hjbSlabTest_generator_upper {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (b c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hb : c + δ ≤ b) (t x A : ℝ) :
    itoTimeDerivative (hjbSlabTest s β j m b c δ) t x +
      itoSpaceDerivative (hjbSlabTest s β j m b c δ) t x * (β ^ 2 * m * A) +
      (1 / 2 : ℝ) * itoSpaceSecondDerivative (hjbSlabTest s β j m b c δ) t x * β ^ 2 ≤
      β ^ 2 / 2 * m * A ^ 2 + if t ≤ c then 0 else β ^ 2 / 2 := by
  have he := hjbSlabTest_generator_gap s β hβ j m b c hδ hb t x A
  have hH := parisiSlabHessian_nonneg s β j hm b (hjbTimeCap c δ t) x
  have hHG := parisiSlabHessian_add_sq_le_one s β j hm b (hjbTimeCap c δ t) x
  have hG := sq_nonneg (parisiSlabGradient s β j m b (hjbTimeCap c δ t) x)
  have hsum : 0 ≤ parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
      m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2 := add_nonneg hH (mul_nonneg hm.1 hG)
  have hsum1 : parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
      m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hG]
  have hsq : 0 ≤ β ^ 2 / 2 * m * (A - parisiSlabGradient s β j m b (hjbTimeCap c δ t) x) ^ 2 :=
    mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num)) hm.1) (sq_nonneg _)
  by_cases ht : t ≤ c
  · simp only [ite_eq_left ht, hjbTimeCapD, ite_eq_left ht, sub_self, mul_zero, zero_mul] at he ⊢
    linarith
  · have hc0 := hjbTimeCapD_nonneg c δ t
    have hc1 := hjbTimeCapD_le_one c hδ t
    have hb0 : 0 ≤ β ^ 2 / 2 := by positivity
    have hp : β ^ 2 / 2 * (1 - hjbTimeCapD c δ t) *
        (parisiSlabHessian s β j m b (hjbTimeCap c δ t) x +
          m * parisiSlabGradient s β j m b (hjbTimeCap c δ t) x ^ 2) ≤ β ^ 2 / 2 := by
      calc
        _ ≤ β ^ 2 / 2 * 1 * 1 := by gcongr <;> linarith
        _ = _ := by ring
    simp only [ite_eq_right ht]
    linarith

/-- A bounded spatial derivative gives the actual slab's global linear growth. -/
lemma parisiSlabPotential_norm_le {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t x : ℝ) :
    ‖parisiSlabPotential s β j m b t x‖ ≤
      ‖parisiSlabPotential s β j m b t 0‖ + ‖x‖ := by
  have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ))
    (fun y _ => (hasDerivAt_parisiSlabPotential_spatial s β j m b t y).hasDerivWithinAt)
    (fun y _ => by simpa only [Real.norm_eq_abs] using abs_parisiSlabGradient_le_one s β j hm b t y)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ 0) (mem_univ x)
  simp only [one_mul, sub_zero] at hl
  calc
    _ = ‖(parisiSlabPotential s β j m b t x - parisiSlabPotential s β j m b t 0) +
        parisiSlabPotential s β j m b t 0‖ := by congr 1; ring
    _ ≤ ‖parisiSlabPotential s β j m b t x - parisiSlabPotential s β j m b t 0‖ +
        ‖parisiSlabPotential s β j m b t 0‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖parisiSlabPotential s β j m b t 0‖ := by gcongr
    _ = _ := add_comm _ _

lemma integrable_parisiSlabPotential {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (b t : ℝ) {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun sample => parisiSlabPotential s β j m b t (Y sample)) P := by
  apply ((integrable_const ‖parisiSlabPotential s β j m b t 0‖).add hY.norm).mono'
  · exact ((continuous_parisiSlab s β j hm.1 b).1.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hY.aestronglyMeasurable))
  · exact Eventually.of_forall (fun sample => parisiSlabPotential_norm_le s β j hm b t (Y sample))

/-- An error supported after `c` contributes only the tail length. -/
lemma intervalIntegral_le_tail {g : ℝ → ℝ} {a b c C : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hg : IntervalIntegrable g volume a b)
    (hleft : ∀ r ∈ Icc a c, g r ≤ 0) (hright : ∀ r ∈ Icc c b, g r ≤ C) :
    (∫ r in a..b, g r) ≤ C * (b - c) := by
  have hacb : c ∈ uIcc a b := by simp only [uIcc_of_le (hac.trans hcb), mem_Icc]; exact ⟨hac, hcb⟩
  have hga : IntervalIntegrable g volume a c := hg.mono_set (by
    rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc le_rfl hcb)
  have hgb : IntervalIntegrable g volume c b := hg.mono_set (by
    rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc hac le_rfl)
  have ha := intervalIntegral.integral_mono_on hac hga (intervalIntegrable_const (c := (0 : ℝ))) hleft
  have hb := intervalIntegral.integral_mono_on hcb hgb (intervalIntegrable_const (c := C)) hright
  rw [← intervalIntegral.integral_add_adjacent_intervals hga hgb]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at ha hb
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Actual verification up to the terminal time for a capped slab test, with
an error no larger than the length of the cap tail. -/
theorem parisiSlab_control_cap_upper {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    {k : ℕ} (s : RSBScheme k) (hβ : β ≠ 0) (j : ℕ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (a b : ℝ≥0) (c : ℝ) (hac : (a : ℝ) ≤ c) (hcb : c < (b : ℝ))
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A))
    (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (a : ℝ) (b : ℝ), d r.toNNReal sample = β ^ 2 * m * A r sample)
    (hXa : Integrable (X a) P) (hXb : Integrable (X b) P) :
    (∫ sample, parisiSlabPotential s β j m b
      (hjbTimeCap c (((b : ℝ) - c) / 2) b) (X b sample) -
      (∫ r in (a : ℝ)..(b : ℝ), β ^ 2 / 2 * m * A r sample ^ 2) ∂P) ≤
      (∫ sample, parisiSlabPotential s β j m b a (X a sample) ∂P) + β ^ 2 / 2 * ((b : ℝ) - c) := by
  let δ := ((b : ℝ) - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : c + δ ≤ (b : ℝ) := by dsimp [δ]; linarith
  have habR : (a : ℝ) ≤ b := hac.trans hcb.le
  have hab : a ≤ b := NNReal.coe_le_coe.mp habR
  let f := hjbSlabTest s β j m b c δ
  let cost := fun r sample => β ^ 2 / 2 * m * A r sample ^ 2
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
  obtain ⟨N, hN, hNzero, hformula⟩ := hjb_ito_increment hc f hf ht hslice hdt hdx hxx a b hab 1 hK
  have hcost : ∀ sample, IntervalIntegrable (fun r => cost r sample) volume a b :=
    fun sample => hjb_control_cost_intervalIntegrable β hm.1 A hAm hA a b sample
  have hic : Integrable (fun sample => ∫ r in (a : ℝ)..(b : ℝ), cost r sample) P :=
    hjb_control_cost_integrable β hm.1 A hAm hA a b habR
  have hia : Integrable (fun sample => f a (X a sample)) P := by
    simpa only [f, hjbSlabTest, hjbTimeCap_of_le c δ a hac] using
      integrable_parisiSlabPotential s β j hm b a hXa
  have hib : Integrable (fun sample => f b (X b sample)) P :=
    integrable_parisiSlabPotential s β j hm b _ hXb
  have hbound : ∀ᵐ sample ∂P, f b (X b sample) - (∫ r in (a : ℝ)..(b : ℝ), cost r sample) ≤
      f a (X a sample) + N sample + β ^ 2 / 2 * ((b : ℝ) - c) := by
    filter_upwards [hformula] with sample he
    have hgi : IntervalIntegrable (fun r => hjbGenerator X d β f r sample) volume a b :=
      IntegrableOn.intervalIntegrable (by
        simpa only [uIcc_of_le habR] using hjbGenerator_integrableOn hc f hdt hdx hxx a b sample)
    have hleft : ∀ r ∈ Icc (a : ℝ) c, hjbGenerator X d β f r sample - cost r sample ≤ 0 := by
      intro r hr
      have hh := hjbSlabTest_generator_upper s β hβ j hm b c hδ hb r (X r.toNNReal sample) (A r sample)
      unfold hjbGenerator
      rw [hd sample r ⟨hr.1, hr.2.trans hcb.le⟩]
      simp only [ite_eq_left hr.2, add_zero] at hh
      exact sub_nonpos.mpr hh
    have hright : ∀ r ∈ Icc c (b : ℝ), hjbGenerator X d β f r sample - cost r sample ≤ β ^ 2 / 2 := by
      intro r hr
      have hh := hjbSlabTest_generator_upper s β hβ j hm b c hδ hb r (X r.toNNReal sample) (A r sample)
      unfold hjbGenerator
      rw [hd sample r ⟨hac.trans hr.1, hr.2⟩]
      have hi : (if r ≤ c then (0 : ℝ) else β ^ 2 / 2) ≤ β ^ 2 / 2 := by
        split_ifs
        · positivity
        · exact le_rfl
      dsimp only [cost]
      linarith
    have htail := intervalIntegral_le_tail hac hcb.le (hgi.sub (hcost sample)) hleft hright
    rw [intervalIntegral.integral_sub hgi (hcost sample)] at htail
    rw [he]
    linarith
  have hh := integral_mono_ae (hib.sub hic) ((hia.add hN).add (integrable_const (β ^ 2 / 2 * ((b : ℝ) - c)))) hbound
  have hAdd := integral_add (hia.add hN) (integrable_const (β ^ 2 / 2 * ((b : ℝ) - c)))
  have hAddN := integral_add hia hN
  simp only [Pi.add_apply] at hAdd hAddN
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [hAdd, hAddN, hNzero, add_zero, integral_const] at hh
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  simpa only [f, hjbSlabTest, cost, δ, hjbTimeCap_of_le c (((b : ℝ) - c) / 2) a hac] using hh

end Paper
