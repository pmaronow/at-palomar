module

public import Paper.ATImplicit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-! # The global AT graph and its inverse coordinate -/

open Filter
open scoped Topology ContDiff

namespace Paper

/-- The unique inverse time coordinate, extended by zero below the critical
inverse temperature. The existence proof is the concrete beta bijection. -/
noncomputable def atTimeFromBeta (β : ℝ) : ℝ :=
  if hβ : 1 < β then Classical.choose (atBetaCurve_bijOn.2.2 hβ) else 0

theorem atTimeFromBeta_pos_and_inverse (β : ℝ) (hβ : 1 < β) :
    0 < atTimeFromBeta β ∧ atBetaCurve (atTimeFromBeta β) = β := by
  rw [atTimeFromBeta, dite_eq_left hβ]
  exact Classical.choose_spec (atBetaCurve_bijOn.2.2 hβ)

theorem atTimeFromBeta_pos (β : ℝ) (hβ : 1 < β) : 0 < atTimeFromBeta β :=
  (atTimeFromBeta_pos_and_inverse β hβ).1

theorem atBetaCurve_atTimeFromBeta (β : ℝ) (hβ : 1 < β) :
    atBetaCurve (atTimeFromBeta β) = β := (atTimeFromBeta_pos_and_inverse β hβ).2

theorem atTimeFromBeta_nonneg (β : ℝ) : 0 ≤ atTimeFromBeta β := by
  by_cases hβ : 1 < β
  · exact (atTimeFromBeta_pos β hβ).le
  · simp [atTimeFromBeta, hβ]

@[simp] theorem atTimeFromBeta_one : atTimeFromBeta 1 = 0 := by simp [atTimeFromBeta]

theorem atTimeFromBeta_atBetaCurve (t : ℝ) (ht : 0 < t) :
    atTimeFromBeta (atBetaCurve t) = t := by
  exact atBetaCurve_bijOn.2.1 (atTimeFromBeta_pos (atBetaCurve t) (atBetaCurve_gt_one t ht))
    ht (atBetaCurve_atTimeFromBeta (atBetaCurve t) (atBetaCurve_gt_one t ht))

theorem atTimeFromBeta_strictMonoOn : StrictMonoOn atTimeFromBeta (Set.Ioi 1) := by
  intro a ha b hb hab
  by_contra hn
  have hle : atTimeFromBeta b ≤ atTimeFromBeta a := le_of_not_gt hn
  have hm := atBetaCurve_strictMonoOn.monotoneOn
    (atTimeFromBeta_pos b hb).le (atTimeFromBeta_pos a ha).le hle
  rw [atBetaCurve_atTimeFromBeta b hb, atBetaCurve_atTimeFromBeta a ha] at hm
  linarith

theorem lt_atTimeFromBeta_of_beta_lt (a β : ℝ) (ha : 0 ≤ a) (hβ : 1 < β)
    (hlt : atBetaCurve a < β) : a < atTimeFromBeta β := by
  by_contra hn
  have hle : atTimeFromBeta β ≤ a := le_of_not_gt hn
  have hm := atBetaCurve_strictMonoOn.monotoneOn (atTimeFromBeta_pos β hβ).le ha hle
  rw [atBetaCurve_atTimeFromBeta β hβ] at hm
  linarith

theorem atTimeFromBeta_lt_of_lt_beta (b β : ℝ) (hb : 0 ≤ b) (hβ : 1 < β)
    (hlt : β < atBetaCurve b) : atTimeFromBeta β < b := by
  by_contra hn
  have hle : b ≤ atTimeFromBeta β := le_of_not_gt hn
  have hm := atBetaCurve_strictMonoOn.monotoneOn hb (atTimeFromBeta_pos β hβ).le hle
  rw [atBetaCurve_atTimeFromBeta β hβ] at hm
  linarith

theorem continuousAt_atTimeFromBeta (β : ℝ) (hβ : 1 < β) :
    ContinuousAt atTimeFromBeta β := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : 0 ≤ a
    · have hlt : atBetaCurve a < β := by
        have hm := atBetaCurve_strictMonoOn ha0 (atTimeFromBeta_pos β hβ).le ha
        rwa [atBetaCurve_atTimeFromBeta β hβ] at hm
      filter_upwards [eventually_gt_nhds hβ, eventually_gt_nhds hlt] with b hb hba
      exact lt_atTimeFromBeta_of_beta_lt a b ha0 hb hba
    · exact .of_forall fun b => lt_of_lt_of_le (lt_of_not_ge ha0) (atTimeFromBeta_nonneg b)
  · intro b hb
    have hbpos : 0 < b := lt_trans (atTimeFromBeta_pos β hβ) hb
    have hlt : β < atBetaCurve b := by
      have hm := atBetaCurve_strictMonoOn (atTimeFromBeta_pos β hβ).le hbpos.le hb
      rwa [atBetaCurve_atTimeFromBeta β hβ] at hm
    filter_upwards [eventually_gt_nhds hβ, eventually_lt_nhds hlt] with a ha hab
    exact atTimeFromBeta_lt_of_lt_beta b a hbpos.le ha hab

theorem continuousAt_atTimeFromBeta_one : ContinuousAt atTimeFromBeta 1 := by
  change Tendsto atTimeFromBeta (𝓝 1) (𝓝 (atTimeFromBeta 1))
  rw [atTimeFromBeta_one]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall fun β => lt_of_lt_of_le ha (atTimeFromBeta_nonneg β)
  · intro b hb
    have hlt := atBetaCurve_gt_one b hb
    filter_upwards [eventually_lt_nhds hlt] with β hβb
    by_cases hβ : 1 < β
    · exact atTimeFromBeta_lt_of_lt_beta b β hb.le hβ hβb
    · simpa [atTimeFromBeta, hβ] using hb

theorem tendsto_atTimeFromBeta_one_right :
    Tendsto atTimeFromBeta (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (0 : ℝ)) := by
  have h := continuousAt_atTimeFromBeta_one.continuousWithinAt (s := Set.Ioi (1 : ℝ))
  change Tendsto atTimeFromBeta (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (atTimeFromBeta 1)) at h
  simpa only [atTimeFromBeta_one] using h

/-- The field of the actual AT graph. -/
noncomputable def atBoundaryField (β : ℝ) : ℝ := atFieldRoot (atTimeFromBeta β)

theorem atBoundaryField_pos (β : ℝ) (hβ : 1 < β) : 0 < atBoundaryField β :=
  atFieldRoot_pos (atTimeFromBeta β) (atTimeFromBeta_pos β hβ)

theorem atBoundaryField_strictMonoOn : StrictMonoOn atBoundaryField (Set.Ioi 1) :=
  at_boundary_strictMono atFieldRoot atTimeFromBeta atFieldRoot_strictMonoOn
    atTimeFromBeta_strictMonoOn atTimeFromBeta_pos

theorem tendsto_atBoundaryField_one_right :
    Tendsto atBoundaryField (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (0 : ℝ)) := by
  have hroot : Tendsto atFieldRoot (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [atFieldRoot_zero_variance] using continuousAt_atFieldRoot_zero.tendsto
  exact hroot.comp tendsto_atTimeFromBeta_one_right

theorem atBoundary_eq_field_graph :
    atBoundary = {p : ℝ × ℝ | 1 < p.1 ∧ p.2 = atBoundaryField p.1} ∪ {(1, 0)} := by
  rw [atBoundary_eq_curve_image]
  apply congrArg (fun s : Set (ℝ × ℝ) => s ∪ {(1, 0)})
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨atBetaCurve_gt_one t ht, ?_⟩
    simp only [atBoundaryField, atTimeFromBeta_atBetaCurve t ht]
  · rintro ⟨hβ, hfield⟩
    refine ⟨atTimeFromBeta p.1, atTimeFromBeta_pos p.1 hβ, ?_⟩
    apply Prod.ext
    · exact atBetaCurve_atTimeFromBeta p.1 hβ
    · exact hfield.symm

end Paper
