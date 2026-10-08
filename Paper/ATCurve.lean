module

public import Paper.GaussianHeat
public import Paper.ATCoordinates

@[expose] public section

/-!
# The actual positive Gaussian zero curve

Existence, uniqueness, strict increase, and continuity of the field coordinate
are proved from the concrete Gaussian function. These are completed analytic
steps of the appendix. This module does not assert smoothness or the final
inverse-temperature graph theorem.
-/

open Filter
open scoped Topology

namespace Paper

/-- Every strictly positive variance has a unique positive zero of the actual
Gaussian appendix function. -/
theorem at_exists_unique_field_zero (t : ℝ) (ht : 0 < t) :
    ∃! h : ℝ, 0 < h ∧ atZeroFunction h t = 0 := by
  have hneg : ∀ᶠ b in atTop, atZeroFunction b t < 0 :=
    (tendsto_atZeroFunction_field t).eventually
      (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨b, hb, hFb⟩ := ((eventually_gt_atTop (0 : ℝ)).and hneg).exists
  have hcont : ContinuousOn (fun h => atZeroFunction h t) (Set.Icc 0 b) :=
    (continuous_atZeroFunction_joint.comp
      (continuous_id.prodMk continuous_const)).continuousOn
  exact at_exists_unique_positive_zero (fun h => atZeroFunction h t) b hb hcont
    ((atZeroFunction_strictAntiOn_field ht).mono Set.Ioi_subset_Ici_self)
    (atZeroFunction_zero_mean_pos ht) hFb

/-- The appendix's unique positive field root, extended by zero on nonpositive
variances. The extension is a concrete choice from a proved existence theorem. -/
noncomputable def atFieldRoot (t : ℝ) : ℝ :=
  if ht : 0 < t then Classical.choose (at_exists_unique_field_zero t ht).exists else 0

@[simp] theorem atFieldRoot_zero_variance : atFieldRoot 0 = 0 := by
  simp [atFieldRoot]

theorem atFieldRoot_pos_and_zero (t : ℝ) (ht : 0 < t) :
    0 < atFieldRoot t ∧ atZeroFunction (atFieldRoot t) t = 0 := by
  rw [atFieldRoot, dite_eq_left ht]
  exact Classical.choose_spec (at_exists_unique_field_zero t ht).exists

theorem atFieldRoot_pos (t : ℝ) (ht : 0 < t) : 0 < atFieldRoot t :=
  (atFieldRoot_pos_and_zero t ht).1

theorem atFieldRoot_nonneg (t : ℝ) : 0 ≤ atFieldRoot t := by
  by_cases ht : 0 < t
  · exact (atFieldRoot_pos t ht).le
  · simp [atFieldRoot, ht]

theorem atFieldRoot_zero (t : ℝ) (ht : 0 < t) :
    atZeroFunction (atFieldRoot t) t = 0 :=
  (atFieldRoot_pos_and_zero t ht).2

theorem atFieldRoot_unique (h t : ℝ) (ht : 0 < t) (hh : 0 < h)
    (hzero : atZeroFunction h t = 0) : h = atFieldRoot t := by
  exact (at_exists_unique_field_zero t ht).unique ⟨hh, hzero⟩
    (atFieldRoot_pos_and_zero t ht)

/-- Positivity of `F(a,t)` brackets `a` strictly below its positive root. -/
theorem lt_atFieldRoot_of_zeroFunction_pos (a t : ℝ) (ht : 0 < t)
    (ha : 0 ≤ a) (hF : 0 < atZeroFunction a t) : a < atFieldRoot t := by
  by_contra hn
  have hle : atFieldRoot t ≤ a := le_of_not_gt hn
  have hmono := (atZeroFunction_strictAntiOn_field ht).antitoneOn
    (atFieldRoot_pos t ht).le ha hle
  rw [atFieldRoot_zero t ht] at hmono
  linarith

/-- Negativity of `F(b,t)` brackets the positive root strictly below `b`. -/
theorem atFieldRoot_lt_of_zeroFunction_neg (b t : ℝ) (ht : 0 < t)
    (hb : 0 ≤ b) (hF : atZeroFunction b t < 0) : atFieldRoot t < b := by
  by_contra hn
  have hle : b ≤ atFieldRoot t := le_of_not_gt hn
  have hmono := (atZeroFunction_strictAntiOn_field ht).antitoneOn
    hb (atFieldRoot_pos t ht).le hle
  rw [atFieldRoot_zero t ht] at hmono
  linarith

/-- The selected field root is strictly increasing on positive variances. -/
theorem atFieldRoot_strictMonoOn : StrictMonoOn atFieldRoot (Set.Ioi 0) := by
  intro a ha b hb hab
  have hF : atZeroFunction (atFieldRoot a) a < atZeroFunction (atFieldRoot a) b :=
    atZeroFunction_strictMonoOn_variance (atFieldRoot a)
      (atFieldRoot_pos a ha).le
      (show a ∈ Set.Ici 0 from le_of_lt (show 0 < a from ha))
      (show b ∈ Set.Ici 0 from le_of_lt (show 0 < b from hb)) hab
  rw [atFieldRoot_zero a ha] at hF
  exact lt_atFieldRoot_of_zeroFunction_pos (atFieldRoot a) b hb
    (atFieldRoot_pos a ha).le hF

/-- Sign bracketing and joint continuity prove continuity of the actual root
without importing an implicit-function existence premise. -/
theorem continuousAt_atFieldRoot (t : ℝ) (ht : 0 < t) :
    ContinuousAt atFieldRoot t := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : 0 ≤ a
    · have hF : 0 < atZeroFunction a t := by
        have hmono := atZeroFunction_strictAntiOn_field ht ha0
          (atFieldRoot_pos t ht).le ha
        dsimp only at hmono
        rw [atFieldRoot_zero t ht] at hmono
        exact hmono
      have hcont : Continuous (atZeroFunction a) :=
        continuous_atZeroFunction_joint.comp (continuous_const.prodMk continuous_id)
      have hevent : ∀ᶠ s in 𝓝 t, 0 < atZeroFunction a s :=
        (hcont.tendsto t).eventually (eventually_gt_nhds hF)
      filter_upwards [eventually_gt_nhds ht, hevent] with s hs hFs
      exact lt_atFieldRoot_of_zeroFunction_pos a s hs ha0 hFs
    · have haneg : a < 0 := lt_of_not_ge ha0
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact lt_trans haneg (atFieldRoot_pos s hs)
  · intro b hb
    have hbpos : 0 < b := lt_trans (atFieldRoot_pos t ht) hb
    have hF : atZeroFunction b t < 0 := by
      have hmono := atZeroFunction_strictAntiOn_field ht
        (atFieldRoot_pos t ht).le hbpos.le hb
      dsimp only at hmono
      rw [atFieldRoot_zero t ht] at hmono
      exact hmono
    have hcont : Continuous (atZeroFunction b) :=
      continuous_atZeroFunction_joint.comp (continuous_const.prodMk continuous_id)
    have hevent : ∀ᶠ s in 𝓝 t, atZeroFunction b s < 0 :=
      (hcont.tendsto t).eventually (eventually_lt_nhds hF)
    filter_upwards [eventually_gt_nhds ht, hevent] with s hs hFs
    exact atFieldRoot_lt_of_zeroFunction_neg b s hs hbpos.le hFs

theorem continuousOn_atFieldRoot : ContinuousOn atFieldRoot (Set.Ioi 0) :=
  fun t ht => (continuousAt_atFieldRoot t ht).continuousWithinAt

/-- The root tends to zero at zero variance. The proof uses a negative field
bracket at variance zero and joint continuity, not a monotone-limit axiom. -/
theorem continuousAt_atFieldRoot_zero : ContinuousAt atFieldRoot 0 := by
  change Tendsto atFieldRoot (𝓝 0) (𝓝 (atFieldRoot 0))
  rw [atFieldRoot_zero_variance]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall fun s => lt_of_lt_of_le ha (atFieldRoot_nonneg s)
  · intro b hb
    have hF : atZeroFunction b 0 < 0 := by
      simp only [atZeroFunction, zero_mul, zero_add, gaussianA_zero_time]
      have he := tanh_sq_add_sech_sq b
      have hp := sq_pos_of_pos (tanh_pos hb)
      nlinarith
    have hcont : Continuous (atZeroFunction b) :=
      continuous_atZeroFunction_joint.comp (continuous_const.prodMk continuous_id)
    have hevent : ∀ᶠ s in 𝓝 (0 : ℝ), atZeroFunction b s < 0 :=
      (hcont.tendsto 0).eventually (eventually_lt_nhds hF)
    filter_upwards [hevent] with s hs
    by_cases hspos : 0 < s
    · exact atFieldRoot_lt_of_zeroFunction_neg b s hspos hb.le hs
    · simpa [atFieldRoot, hspos] using hb

theorem tendsto_atFieldRoot_zero_right :
    Tendsto atFieldRoot (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
  have h := continuousAt_atFieldRoot_zero.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  change Tendsto atFieldRoot (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (atFieldRoot 0)) at h
  simpa only [atFieldRoot_zero_variance] using h

theorem continuousOn_atFieldRoot_nonneg : ContinuousOn atFieldRoot (Set.Ici 0) := by
  intro t ht
  rcases lt_or_eq_of_le (show 0 ≤ t from ht) with htpos | htzero
  · exact (continuousAt_atFieldRoot t htpos).continuousWithinAt
  · rw [← htzero]
    exact continuousAt_atFieldRoot_zero.continuousWithinAt

/-- All positive zeros are exactly the graph of the selected field root in
the appendix's `(h,t)` coordinate order. -/
theorem positiveATZeroSet_eq_root_graph :
    positiveATZeroSet = {p : ℝ × ℝ | 0 < p.2 ∧ p.1 = atFieldRoot p.2} := by
  ext p
  constructor
  · rintro ⟨hh, ht, hzero⟩
    exact ⟨ht, atFieldRoot_unique p.1 p.2 ht hh hzero⟩
  · rintro ⟨ht, hroot⟩
    change 0 < p.1 ∧ 0 < p.2 ∧ atZeroFunction p.1 p.2 = 0
    rw [hroot]
    exact ⟨atFieldRoot_pos p.2 ht, ht, atFieldRoot_zero p.2 ht⟩

/-- The actual inverse-temperature coordinate along the proved field curve. -/
noncomputable def atBetaCurve (t : ℝ) : ℝ :=
  Real.sqrt (1 / gaussianC (atFieldRoot t) t)

theorem atBetaCurve_pos (t : ℝ) : 0 < atBetaCurve t :=
  Real.sqrt_pos.mpr (one_div_pos.mpr (gaussianC_pos (atFieldRoot t) t))

@[simp] theorem atBetaCurve_zero : atBetaCurve 0 = 1 := by
  simp [atBetaCurve, gaussianC_zero_time]

theorem continuousAt_atBetaCurve_zero : ContinuousAt atBetaCurve 0 := by
  change ContinuousAt (fun t : ℝ => Real.sqrt (1 / gaussianC (atFieldRoot t) t)) 0
  have hpair : ContinuousAt (fun t : ℝ => (atFieldRoot t, t)) 0 :=
    continuousAt_atFieldRoot_zero.prodMk continuousAt_id
  have hCbase : ContinuousAt (fun p : ℝ × ℝ => gaussianC p.1 p.2)
      (atFieldRoot 0, 0) := continuous_gaussianC_joint.continuousAt
  have hC : ContinuousAt (fun t => gaussianC (atFieldRoot t) t) 0 :=
    hCbase.comp (f := fun t : ℝ => (atFieldRoot t, t)) (x := 0) hpair
  have hInv : ContinuousAt (fun t : ℝ => (1 : ℝ) / gaussianC (atFieldRoot t) t) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0).div hC
      (ne_of_gt (gaussianC_pos (atFieldRoot 0) 0))
  exact hInv.sqrt

theorem tendsto_atBetaCurve_zero_right :
    Tendsto atBetaCurve (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (1 : ℝ)) := by
  have h := continuousAt_atBetaCurve_zero.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  change Tendsto atBetaCurve (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (atBetaCurve 0)) at h
  simpa only [atBetaCurve_zero] using h

theorem atBetaCurve_sq_gt_time (t : ℝ) (ht : 0 < t) : t < atBetaCurve t ^ 2 := by
  rw [atBetaCurve, Real.sq_sqrt (le_of_lt
    (one_div_pos.mpr (gaussianC_pos (atFieldRoot t) t)))]
  exact at_inverse_temperature_bound t (gaussianA (atFieldRoot t) t)
    (gaussianC (atFieldRoot t) t) (gaussianC_pos (atFieldRoot t) t)
    (gaussianA_pos (atFieldRoot t) t) (atFieldRoot_zero t ht)

theorem tendsto_atBetaCurve_atTop : Tendsto atBetaCurve atTop atTop :=
  at_beta_tendsto_atTop atBetaCurve (fun t _ => (atBetaCurve_pos t).le)
    atBetaCurve_sq_gt_time

theorem atBetaCurve_gt_one (t : ℝ) (ht : 0 < t) : 1 < atBetaCurve t := by
  have hr := gaussian_at_zero_reconstruction (atFieldRoot t) t (atFieldRoot_pos t ht) ht
    (atFieldRoot_zero t ht)
  exact gaussian_at_critical_beta_gt_one (atBetaCurve t) (atFieldRoot t)
    (t * gaussianC (atFieldRoot t) t) hr.1 (atFieldRoot_pos t ht) hr.2.2.2

/-- The full concrete AT boundary is parametrized by the proved field-root
curve. This statement does not assert smoothness or injectivity of the beta
coordinate. -/
theorem atBoundary_eq_curve_image :
    atBoundary = (fun t : ℝ => (atBetaCurve t, atFieldRoot t)) '' Set.Ioi 0 ∪ {(1, 0)} := by
  rw [atBoundary_eq_zero_image]
  apply congrArg (fun s : Set (ℝ × ℝ) => s ∪ {(1, 0)})
  ext p
  constructor
  · rintro ⟨z, hz, hzp⟩
    rcases hz with ⟨hh, ht, hzero⟩
    have hroot := atFieldRoot_unique z.1 z.2 ht hh hzero
    refine ⟨z.2, ht, ?_⟩
    simpa only [atZeroToBoundary, atBetaCurve, hroot] using hzp
  · rintro ⟨t, ht, htp⟩
    refine ⟨(atFieldRoot t, t),
      ⟨atFieldRoot_pos t ht, ht, atFieldRoot_zero t ht⟩, ?_⟩
    exact htp

end Paper
