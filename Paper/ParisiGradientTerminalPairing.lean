module

public import Paper.ParisiGradientGrid
public import Paper.ParisiGradientMesh
public import Paper.ParisiControlFirstVariation

@[expose] public section

/-! # Actual optimal-gradient terminal pairing

Weighted finite Cole--Hopf gradient estimates are telescoped on the genuine
selected state, and both approximation errors vanish. This identifies the
terminal tanh pairing without a supplied martingale or stochastic-law premise.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper

lemma parisiGradientGridError_integral_le (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, parisiGradientGridError β μ n t) ≤
      β ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) + parisiHJBGradientError β μ n) := by
  dsimp only [parisiGradientGridError]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
    gcongr
    simpa only [Real.norm_eq_abs] using parisiCDF_grid_norm_integral_le μ n
  · exact (((parisiCDF_monotone μ).intervalIntegrable).sub
      ((parisiCDF_monotone (parisiGridMeasure μ n)).intervalIntegrable)).norm
  · exact intervalIntegrable_const

lemma tendsto_integral_parisiGradientGridError (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, parisiGradientGridError β μ n t) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ => parisiGradientGridError_nonneg β μ n t)
  · exact parisiGradientGridError_integral_le β μ
  · have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (hinv.add (tendsto_parisiHJBGradientError β hβ μ)).const_mul (β ^ 2)

set_option maxHeartbeats 1000000 in
lemma selectedParisiState_gradient_grid_weighted_bound
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n : ℕ)
    (s : ℝ≥0) (hs : (s : ℝ) ≤ 1) (Z : BrownianSample → ℝ)
    (hZ : StronglyMeasurable[canonicalBrownianFiltration s] Z) (hZb : ∀ ω, ‖Z ω‖ ≤ 1) :
    ‖(∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (1, selectedParisiItoState β h hβ μ 1 ω) ∂canonicalBrownianMeasure) -
      ∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (s, selectedParisiItoState β h hβ μ s ω) ∂canonicalBrownianMeasure‖ ≤
      ∫ t in (0 : ℝ)..1, parisiGradientGridError β μ n t := by
  let T := parisiGradientMeshTime n s
  let X := selectedParisiItoState β h hβ μ
  let F : ℕ → ℝ := fun i => ∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
    (T i, X (T i).toNNReal ω) ∂canonicalBrownianMeasure
  have hs0 : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨s.coe_nonneg, hs⟩
  have hcell : ∀ i, i < n + 1 → ‖F (i + 1) - F i‖ ≤
      ∫ t in T i..T (i + 1), parisiGradientGridError β μ n t := by
    intro i hi
    rcases parisiGradientMeshTime_step_cases n s i with he | hlt
    · simp only [F, T, he, sub_self, norm_zero, intervalIntegral.integral_same, le_refl]
    · let a := (T i).toNNReal
      let b := (T (i + 1)).toNNReal
      have ha0 : 0 ≤ T i := (parisiGradientMeshTime_mem n hs0 (by omega : i ≤ n + 1)).1
      have hb0 : 0 ≤ T (i + 1) := (parisiGradientMeshTime_mem n hs0 (by omega : i + 1 ≤ n + 1)).1
      have hca : (a : ℝ) = T i := Real.coe_toNNReal _ ha0
      have hcb : (b : ℝ) = T (i + 1) := Real.coe_toNNReal _ hb0
      have hra : s ≤ a := NNReal.coe_le_coe.mp (by
        rw [hca]; exact le_max_left _ _)
      have hab : a < b := NNReal.coe_lt_coe.mp (by simpa only [hca, hcb] using hlt)
      have hac : (a : ℝ) ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1)) := by
        rw [hca]
        exact parisiGradientMeshTime_cell_subset n s i hlt
          ⟨le_rfl, (parisiGradientMeshTime_mono n s (Nat.le_succ i))⟩
      have hbc : (b : ℝ) = hjbGridTime n (i + 1) := hcb.trans
        (parisiGradientMeshTime_step_lt_terminal n s i hlt)
      have hh := selectedParisiState_gradient_grid_cell_bound β h hβ μ n i hi s a b hra hab hac hbc Z hZ hZb
      simpa only [F, X, a, b, hca, hcb] using hh
  have hh := parisiGradientMesh_norm_telescope F (parisiGradientGridError β μ n) T (n + 1)
    (fun i _ => parisiGradientGridError_intervalIntegrable β μ n (T i) (T (i + 1))) hcell
  have hT0 : T 0 = s := parisiGradientMeshTime_zero n s.coe_nonneg
  have hTN : T (n + 1) = 1 := parisiGradientMeshTime_terminal n hs
  have hh' : ‖(∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (1, X 1 ω) ∂canonicalBrownianMeasure) -
      ∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (s, X s ω) ∂canonicalBrownianMeasure‖ ≤
      ∫ t in (s : ℝ)..1, parisiGradientGridError β μ n t := by
    simpa only [F, hT0, hTN, Real.toNNReal_coe, Real.toNNReal_one] using hh
  exact hh'.trans (parisiGradientMesh_integral_le_full hs0
    (parisiGradientGridError_intervalIntegrable β μ n 0 1) (parisiGradientGridError_nonneg β μ n))

lemma tendsto_integral_weighted_grid_gradient (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (Z : BrownianSample → ℝ) (hZ : Measurable Z) (hZb : ∀ ω, ‖Z ω‖ ≤ 1) :
    Tendsto (fun n => ∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
      (t, selectedParisiItoState β h hβ μ t ω) ∂canonicalBrownianMeasure) atTop
      (𝓝 (∫ ω, Z ω * parisiGradient β μ
        (t, selectedParisiItoState β h hβ μ t ω) ∂canonicalBrownianMeasure)) := by
  let X := selectedParisiItoState β h hβ μ
  have hXm : Measurable (X t) :=
    ((stronglyAdapted_canonicalParisiItoState β h μ _ _ _ _ t).mono
      (canonicalBrownianFiltration.le t)).measurable
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω => Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
      (t, X t ω)) canonicalBrownianMeasure :=
    (hZ.mul ((continuous_parisiFiniteGradient _ β).measurable.comp
      (measurable_const.prodMk hXm))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂canonicalBrownianMeasure, ‖Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
      (t, X t ω)‖ ≤ (1 : ℝ) := .of_forall fun ω => by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hZb ω)
      (norm_parisiFiniteGradient_le_one (parisiGridRSBScheme μ n) β (t, X t ω))
      (norm_nonneg _) zero_le_one
  have hpoint : ∀ᵐ ω ∂canonicalBrownianMeasure, Tendsto
      (fun n => Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β (t, X t ω)) atTop
      (𝓝 (Z ω * parisiGradient β μ (t, X t ω))) := by
    refine .of_forall fun ω => tendsto_const_nhds.mul ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => by simpa only [norm_sub_rev] using parisiHJBGradientError_bound β μ n t (X t ω))
      (tendsto_parisiHJBGradientError β hβ μ)
  exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmeas
    (integrable_const 1) hbound hpoint

/-- The actual PDE-selected gradient conserves every bounded past-measurable
weighted expectation up to terminal time. All stochastic inputs are proved. -/
theorem selectedParisiGradient_terminal_weighted_expectation
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ≥0) (hs : (s : ℝ) ≤ 1) (Z : BrownianSample → ℝ)
    (hZ : StronglyMeasurable[canonicalBrownianFiltration s] Z) (hZb : ∀ ω, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * parisiGradient β μ (1, selectedParisiItoState β h hβ μ 1 ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * parisiGradient β μ (s, selectedParisiItoState β h hβ μ s ω) ∂canonicalBrownianMeasure := by
  have hZm : Measurable Z := (hZ.mono (canonicalBrownianFiltration.le s)).measurable
  have hlim := ((tendsto_integral_weighted_grid_gradient β h hβ μ 1 Z hZm hZb).sub
    (tendsto_integral_weighted_grid_gradient β h hβ μ s Z hZm hZb)).norm
  have hh := le_of_tendsto_of_tendsto hlim (tendsto_integral_parisiGradientGridError β hβ μ)
    (.of_forall fun n => selectedParisiState_gradient_grid_weighted_bound β h hβ μ n s hs Z hZ hZb)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- The exact terminal pairing needed by the actual optimal-control first
variation. No supplied martingale, Itô or law premise remains. -/
theorem selectedParisiFeedbackControl_terminal_pairing
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ ω, Real.tanh (h + β * canonicalBrownian 1 ω +
        parisiControlDrift β μ (selectedParisiFeedbackControl β h μ) ω) *
      selectedParisiFeedbackControl β h μ s ω ∂canonicalBrownianMeasure) =
    ∫ ω, selectedParisiFeedbackControl β h μ s ω ^ 2 ∂canonicalBrownianMeasure := by
  let A := selectedParisiFeedbackControl β h μ
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl β h μ
  have hZ : StronglyMeasurable[canonicalBrownianFiltration s.toNNReal] (A s) := by
    have hh := hA.adapted s.toNNReal
    dsimp only at hh
    rw [Real.coe_toNNReal s hs.1] at hh
    exact hh
  have hh := selectedParisiGradient_terminal_weighted_expectation β h hβ μ s.toNNReal
    (by simpa only [Real.coe_toNNReal s hs.1] using hs.2) (A s) hZ (hA.bounded s)
  have hleft (ω : BrownianSample) : A s ω * parisiGradient β μ
      (1, selectedParisiItoState β h hβ μ 1 ω) =
      Real.tanh (h + β * canonicalBrownian 1 ω + parisiControlDrift β μ A ω) * A s ω := by
    rw [parisiGradient_terminal β μ,
      selectedParisiItoState_eq β h hβ μ (by norm_num) ω]
    simp only [NNReal.coe_one]
    rw [← selectedParisiFeedbackControl_terminal_state_eq β h hβ μ ω]
    exact mul_comm _ _
  have hright (ω : BrownianSample) : A s ω * parisiGradient β μ
      (s.toNNReal, selectedParisiItoState β h hβ μ s.toNNReal ω) = A s ω ^ 2 := by
    rw [selectedParisiItoState_eq β h hβ μ
      (by simpa only [Real.coe_toNNReal s hs.1] using hs.2) ω, Real.coe_toNNReal s hs.1]
    rw [← selectedParisiFeedbackControl_apply β h hβ μ s hs ω]
    ring
  simpa only [hleft, hright, A] using hh

end Paper
