module

public import Targets.Section4NestedDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# The normalized squared-slope factor in Section 4

The actual split derivative is its mass gap divided by two times a nested
normalized mean of the squared spatial slope. The normalized factor is defined
without division by the mass gap, so remains meaningful at the baseline mass.
No mass/variance interchange or derivative of U is asserted here.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual nested tilted average of the squared inner spatial slope.
Its first field is only the dummy coordinate of the existing paired API. -/
noncomputable def section4VarianceQ {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ) (m : ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => fun v =>
      pairedSecondMean (s.m (r - 1)) (β ^ 2 * (s.q r - s.q (r - 1)) - v)
        (fun _ y => parisiStep m v (parisiF s β (k + 2 - r)) (y 0))
        (fun _ y => (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r))
          m v (y 0)) ^ 2)
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 2 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) - s.q (k + 2 - (k + 2 - r + 2 + j))))
        (fun _ y => scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 2 + j) (y 0))
        (section4VarianceQ s β r m j v)

/-- Factorization is exact even at equal masses: it does not divide by the gap. -/
theorem section4VarianceD_eq_massGap_mul {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceD s β r m j v x y =
      (m - s.m (r - 1)) / 2 * section4VarianceQ s β r m j v x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    simp only [section4VarianceD, section4VarianceQ, pairedSecondMean, pairedTiltMean,
      ih, mul_assoc, integral_const_mul]

/-- Spatial measurability of the normalized observable at every outer depth. -/
theorem measurable_section4VarianceQ {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) (m : ℝ) (j : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => section4VarianceQ s β r m j v p.1 p.2) := by
  induction j with
  | zero =>
    unfold section4VarianceQ
    apply measurable_pairedSecondMean
    · exact (measurable_parisiStep (parisiF_measurable s β _) m v).comp
        ((measurable_pi_apply 0).comp measurable_snd)
    · exact ((measurable_stepD1 (parisiF_measurable s β _) (parisiF_C2_props s β _).2.1 m v).pow_const 2).comp
        ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    unfold section4VarianceQ
    apply measurable_pairedSecondMean
    · exact (scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd)
    · exact ih

theorem guerraGrowth_one {A : ℝ → ℝ} (hA : HasLinearGrowth A) (hAm : Measurable A) :
    GuerraGrowth (fun y : Fin 1 → ℝ => A (y 0)) := by
  obtain ⟨C, D, _, hD, hb⟩ := hA
  refine ⟨hAm.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
  intro y
  simpa [l1] using hb (y 0)

theorem pairedTiltMean_mem_Icc {n : ℕ} {A G : (Fin n → ℝ) → ℝ}
    (hA : GuerraGrowth A) (hG : Measurable G) (hG01 : ∀ y, G y ∈ Set.Icc 0 1)
    (m v : ℝ) (x : Fin n → ℝ) : pairedTiltMean m v A G x ∈ Set.Icc 0 1 := by
  refine ⟨?_, (le_abs_self _).trans (pairedTiltMean_abs_le hA hG (fun y => ?_) x)⟩
  · obtain ⟨C, D, hD, hb⟩ := hA.bound
    exact integral_nonneg (fun z => mul_nonneg (hG01 _).1
      (tiltWeightPi_nonneg hD hb hA.measurable x z))
  · simpa only [abs_of_nonneg (hG01 y).1] using (hG01 y).2

/-- The normalized average stays in `[0,1]` at every depth. This includes the
baseline masses zero and one, and all formal variance values (hence endpoints). -/
theorem section4VarianceQ_mem_Icc {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β r m j v x y ∈ Set.Icc 0 1 := by
  induction j generalizing x y with
  | zero =>
    have hAm := parisiF_measurable s β (k + 2 - r)
    have hc := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 (parisiF_C2_props s β _).1
      (parisiF_hasLinearGrowth s β _) hAm (parisiF_C2_props s β _).2.1 (parisiF_C2_props s β _).2.2
    apply pairedTiltMean_mem_Icc
      (guerraGrowth_one (hasLinearGrowth_parisiStep (parisiF_hasLinearGrowth s β _) hAm m v)
        (measurable_parisiStep hAm m v))
      (((measurable_stepD1 hAm (parisiF_C2_props s β _).2.1 m v).pow_const 2).comp
        (measurable_pi_apply 0))
    intro z
    refine ⟨sq_nonneg _, ?_⟩
    dsimp only [Function.comp_apply]
    nlinarith [hc.abs_first_le_one (z 0), sq_abs
      (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) m v (z 0)),
      abs_nonneg (stepD1 (parisiF s β (k + 2 - r)) (parisiFDeriv s β (k + 2 - r)) m v (z 0))]
  | succ j ih =>
    exact pairedTiltMean_mem_Icc
      (guerraGrowth_one (scalarFieldCascade_props _ _ _).2.1 (scalarFieldCascade_props _ _ _).1)
      ((measurable_section4VarianceQ s β r m j v).comp (measurable_const.prodMk measurable_id))
      (ih x) _ _ y

/-- The normalized factor after all unchanged outer levels. -/
noncomputable def section4TVarianceQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) : ℝ := section4VarianceQ s β r m (r - 1) v 0 (fun _ => h)

theorem section4TVarianceD_eq_massGap_mul {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m v : ℝ) :
    section4TVarianceD s β h r m v = (m - s.m (r - 1)) / 2 * section4TVarianceQ s β h r m v :=
  section4VarianceD_eq_massGap_mul s β r m (r - 1) v 0 (fun _ => h)

theorem section4TVarianceQ_mem_Icc {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v : ℝ) :
    section4TVarianceQ s β h r m v ∈ Set.Icc 0 1 :=
  section4VarianceQ_mem_Icc s β r hm (r - 1) v 0 (fun _ => h)

/-- The actual full variance derivative with its normalized factor exposed.
Differentiation is on the interior; the factor itself is defined at endpoints. -/
theorem hasDerivAt_section4T_variance_factor {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4T s β h r m)
      ((m - s.m (r - 1)) / 2 * section4TVarianceQ s β h r m v) v := by
  rw [← section4TVarianceD_eq_massGap_mul]
  exact hasDerivAt_section4T_variance s β h hr0 hr hm hmm hv

/-- The factored derivative is integrable on every closed split subinterval,
using Mathlib's automatic integrability for a nonnegative derivative. -/
theorem intervalIntegrable_section4T_variance_factor {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    IntervalIntegrable (fun t => (m - s.m (r - 1)) / 2 * section4TVarianceQ s β h r m t)
      volume v w := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hvw).mpr
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    ((continuousOn_section4T s β h hr0 hr hm.1).mono (Set.Icc_subset_Icc hv.1 hw.2))
  · intro t ht
    exact hasDerivAt_section4T_variance_factor s β h hr0 hr hm hmm
      ⟨hv.1.trans_lt ht.1, ht.2.trans_le hw.2⟩
  · intro t _
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hmm) (by norm_num))
      (section4TVarianceQ_mem_Icc s β h r hm t).1

/-- Endpoint-safe integral form of the actual variance derivative. At baseline
the coefficient vanishes; no division or endpoint derivative is used. -/
theorem section4T_sub_eq_massGap_mul_integral {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    section4T s β h r m w - section4T s β h r m v =
      (m - s.m (r - 1)) / 2 * ∫ t in v..w, section4TVarianceQ s β h r m t := by
  rw [← intervalIntegral.integral_const_mul]
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvw
    ((continuousOn_section4T s β h hr0 hr hm.1).mono (Set.Icc_subset_Icc hv.1 hw.2))
  · intro t ht
    exact hasDerivAt_section4T_variance_factor s β h hr0 hr hm hmm
      ⟨hv.1.trans_lt ht.1, ht.2.trans_le hw.2⟩
  · exact intervalIntegrable_section4T_variance_factor s β h hr0 hr hm hmm hv hw hvw

/-- Away from equal masses, the normalized factor itself is integrable; this
uses the actual derivative, not an assumed continuity theorem for the factor. -/
theorem intervalIntegrable_section4TVarianceQ {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) < m) {v w : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1))))
    (hw : w ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) (hvw : v ≤ w) :
    IntervalIntegrable (section4TVarianceQ s β h r m) volume v w := by
  have hc : (m - s.m (r - 1)) / 2 ≠ 0 := ne_of_gt (by positivity)
  have H := (intervalIntegrable_section4T_variance_factor s β h hr0 hr hm hmm.le hv hw hvw).div_const
    ((m - s.m (r - 1)) / 2)
  simpa only [mul_div_cancel_left₀ _ hc] using H

end SpinGlass.Targets
