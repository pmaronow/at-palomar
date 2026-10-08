module

public import Targets.ParisiMassUniform
public import Targets.Section4FirstVariation

@[expose] public section

/-!
# The uniform first mass estimate through the actual Section 4 recursion

Normalized outer means preserve the scalar first derivative bound exactly.
The actual full mass derivative is covered on the admissible inserted-mass
interval, including its zero-mass branch and zero-variance endpoints. The
second derivative of the full nested transform is not asserted here.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual nested first mass observable is spatially measurable. -/
theorem measurable_section4MassD {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) (v m : ℝ) :
    Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => section4MassD s β r v j m p.1 p.2) := by
  induction j with
  | zero =>
    exact (measurable_deriv_parisiStep_mass (parisiF_hasLinearGrowth s β _)
      (parisiF_measurable s β _) m v).comp ((measurable_pi_apply 0).comp measurable_snd)
  | succ j ih =>
    unfold section4MassD
    apply measurable_pairedSecondMean
    · exact (scalarFieldCascade_props _ _ _).1.comp ((measurable_pi_apply 0).comp measurable_snd)
    · exact ih

/-- Uniformity in depth is exact: every remaining level is a normalized mean,
so it does not multiply or increase the field-uniform inner derivative bound. -/
theorem section4MassD_abs_le_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (r j : ℕ) {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V)
    (x y : Fin 1 → ℝ) :
    |section4MassD s β r v j m x y| ≤ parisiMassFirstBound V := by
  induction j generalizing x y with
  | zero => exact (parisiStep_parisiF_mass_derivatives_uniform s β _ hm hv (y 0)).1
  | succ j ih =>
    obtain ⟨C, D, _, hD, hb⟩ := (scalarFieldCascade_props
      (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) v) (k + 2 - r + 1 + j)).2.1
    apply pairedTiltMean_abs_le
    · refine ⟨(scalarFieldCascade_props _ _ _).1.comp (measurable_pi_apply 0), C, D, hD, ?_⟩
      intro z
      simpa only [l1, Fin.sum_univ_one] using hb (z 0)
    · exact (measurable_section4MassD s β r j v m).comp (measurable_const.prodMk measurable_id)
    · exact ih x

/-- The first half of Talagrand Lemma 4.5 for the actual full transform.
The constant depends only on beta, not on the level count, field, or mass gap.
An actual derivative predicate, rather than only a bound on Lean's `deriv`,
records differentiability at zero inserted mass and at both variance endpoints. -/
theorem section4T_mass_derivative_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ∃ d : ℝ, HasDerivAt (fun a => section4T s β h r a v) d m ∧
      |d| ≤ parisiMassFirstBound (β ^ 2) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hv' : v ∈ Set.Icc 0 (β ^ 2) := by
    refine ⟨hv.1, hv.2.trans ?_⟩
    have hq0 := s.q_nonneg (p := r - 1) (by omega)
    have hq1 := s.q_le_one (p := r) (by omega)
    nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hq0,
      mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq1)]
  rcases eq_or_lt_of_le hv.1 with he | hvpos
  · subst v
    refine ⟨0, ?_, by simpa using parisiMassFirstBound_nonneg (β ^ 2)⟩
    simpa only [section4T_zero_variance s β h hr0 hr] using
      hasDerivAt_const m (parisiF s β (k + 2) h)
  · rcases eq_or_lt_of_le hm0 with he | hmpos
    · subst m
      have hz : s.m (r - 1) = 0 := le_antisymm hm.1 (s.m_nonneg (by omega))
      refine ⟨_, hasDerivAt_section4T_mass_zero s β h hr0 hr hz hv, ?_⟩
      have H := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
        (f := fun z => deriv (fun a => parisiStep a v (parisiF s β (k + 2 - r))
          (h + Real.sqrt (β ^ 2 * s.q r - v) * z)) 0)
        (C := parisiMassFirstBound (β ^ 2)) (Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs] using
          (parisiStep_parisiF_mass_derivatives_uniform s β (k + 2 - r)
            (m := 0) ⟨le_rfl, by norm_num⟩ hv'
            (h + Real.sqrt (β ^ 2 * s.q r - v) * z)).1)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using H
    · refine ⟨section4TMassD s β h r v m,
        hasDerivAt_section4T_mass_pos s β h hr0 hr hmpos ⟨hvpos, hv.2⟩, ?_⟩
      exact section4MassD_abs_le_uniform s β r r ⟨hm0, hm.2⟩ hv' 0 (fun _ => h)

theorem abs_deriv_section4T_mass_le_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |deriv (fun a => section4T s β h r a v) m| ≤ parisiMassFirstBound (β ^ 2) := by
  obtain ⟨d, hd, hb⟩ := section4T_mass_derivative_uniform s β h hr0 hr hm hv
  rwa [hd.deriv]

/-- The first mass derivative bound for the actual inserted Parisi functional,
with its deterministic correction included. No optimality assumption is used. -/
theorem section4Phi_mass_derivative_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    ∃ d : ℝ, HasDerivAt (fun a => section4Phi s β h r a u) d m ∧
      |d| ≤ parisiMassFirstBound (β ^ 2) + β ^ 2 / 4 := by
  have hv := section5SplitVariance_mem s β (t := 1) ⟨by norm_num, le_rfl⟩ hu
  simp only [one_mul] at hv
  obtain ⟨d, hd, hb⟩ := section4T_mass_derivative_uniform s β h hr0 hr hm hv
  let c := β ^ 2 / 4 * (s.q r ^ 2 - u ^ 2)
  have hc : c ∈ Set.Icc 0 (β ^ 2 / 4) := by
    have hq0 := s.q_nonneg (p := r - 1) (by omega)
    have hq1 := s.q_le_one (p := r) (by omega)
    have hu0 : 0 ≤ u := hq0.trans hu.1
    have hq0' : 0 ≤ s.q r := hu0.trans hu.2
    have hdiff : s.q r ^ 2 - u ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (add_nonneg hq0' hu0)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (by linarith : 0 ≤ 1 + s.q r), sq_nonneg u]
    exact ⟨mul_nonneg (by positivity) hdiff.1, mul_le_of_le_one_right (by positivity) hdiff.2⟩
  refine ⟨d - c, ?_, ?_⟩
  · have HC := ((hasDerivAt_id m).const_sub (s.m (r - 1))).mul_const c
    simpa only [section4Phi, c, id_eq, neg_mul, one_mul, sub_eq_add_neg] using!
      ((hd.const_add (Real.log 2)).sub_const (parisiCorrection s β)).add HC
  · exact (abs_sub d c).trans (add_le_add hb (by simpa only [abs_of_nonneg hc.1] using hc.2))

theorem abs_deriv_section4Phi_mass_le_uniform {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |deriv (fun a => section4Phi s β h r a u) m| ≤ parisiMassFirstBound (β ^ 2) + β ^ 2 / 4 := by
  obtain ⟨d, hd, hb⟩ := section4Phi_mass_derivative_uniform s β h hr0 hr hm hu
  rwa [hd.deriv]

end SpinGlass.Targets
