module

public import Paper.ParisiFiniteCells
public import Paper.ParisiFiniteMild
public import Paper.ParisiGlobalApproximation
public import Paper.ParisiPotentialStability

@[expose] public section

/-! # The concrete finite-grid gradients in the global approximation space -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

open SpinGlass SpinGlass.Targets

theorem parisiFiniteGradientAux_above_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (hj : j ≤ k + 2) (t x : ℝ) (ht : 1 < t) :
    parisiFiniteGradientAux s β j t x = parisiFDeriv s β 0 x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hq := s.q_le_one (p := k + 2 - j) (by omega)
    have hn : ¬t ≤ s.q (k + 2 - j) := by linarith
    simpa only [parisiFiniteGradientAux, ite_eq_right hn] using ih (by omega)

theorem parisiFiniteGradient_terminal {k : ℕ} (s : RSBScheme k) (β x : ℝ) :
    parisiFiniteGradient s β (1, x) = Real.tanh x := by
  have hc := (continuous_parisiFiniteAux s β (j := k + 2) le_rfl).2.1.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  have hs : IsClosed {t : ℝ | parisiFiniteGradientAux s β (k + 2) t x =
      parisiFDeriv s β 0 x} := isClosed_eq hc continuous_const
  have hsub : Ioi (1 : ℝ) ⊆ {t : ℝ | parisiFiniteGradientAux s β (k + 2) t x =
      parisiFDeriv s β 0 x} := fun t ht =>
    parisiFiniteGradientAux_above_terminal s β (k + 2) le_rfl t x ht
  have ht : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by
    rw [closure_Ioi]
    exact (le_refl (1 : ℝ))
  have he := closure_minimal hsub hs ht
  change parisiFiniteGradientAux s β (k + 2) 1 x = parisiFDeriv s β 0 x at he
  simpa only [parisiFiniteGradient, Prod.fst, Prod.snd, min_self, max_eq_right zero_le_one,
    parisiFDeriv, ← Real.tanh_eq_sinh_div_cosh] using he

theorem parisiFinitePotentialAux_above_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (hj : j ≤ k + 2) (t x : ℝ) (ht : 1 < t) :
    parisiFinitePotentialAux s β j t x = parisiF s β 0 x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hq := s.q_le_one (p := k + 2 - j) (by omega)
    have hn : ¬t ≤ s.q (k + 2 - j) := by linarith
    simpa only [parisiFinitePotentialAux, ite_eq_right hn] using ih (by omega)

theorem parisiFinitePotential_terminal {k : ℕ} (s : RSBScheme k) (β x : ℝ) :
    parisiFinitePotential s β (1, x) = Real.log (Real.cosh x) := by
  have hc := (continuous_parisiFiniteAux s β (j := k + 2) le_rfl).1.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  have hs : IsClosed {t : ℝ | parisiFinitePotentialAux s β (k + 2) t x = parisiF s β 0 x} :=
    isClosed_eq hc continuous_const
  have hsub : Ioi (1 : ℝ) ⊆ {t : ℝ | parisiFinitePotentialAux s β (k + 2) t x = parisiF s β 0 x} :=
    fun t ht => parisiFinitePotentialAux_above_terminal s β (k + 2) le_rfl t x ht
  have ht : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by
    rw [closure_Ioi]
    exact (le_refl (1 : ℝ))
  have he := closure_minimal hsub hs ht
  change parisiFinitePotentialAux s β (k + 2) 1 x = parisiF s β 0 x at he
  simpa only [parisiFinitePotential, Prod.fst, Prod.snd, min_self, max_eq_right zero_le_one,
    parisiF] using he

noncomputable def parisiFiniteStripGradient {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ParisiSlabGradient 0 1 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => parisiFiniteGradient s β (p.1, p.2))
    ((continuous_parisiFiniteGradient s β).comp (by fun_prop)) 1
    (fun p => norm_parisiFiniteGradient_le_one s β _)

theorem norm_parisiFiniteStripGradient_le_one {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    ‖parisiFiniteStripGradient s β‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ zero_le_one _

theorem parisiFiniteStripGradient_extend {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (parisiFiniteStripGradient s β) =
      parisiFiniteGradient s β := by
  funext p
  unfold parisiSlabExtend parisiFiniteStripGradient
  simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup, parisiFiniteGradient]
  rw [min_eq_right (projIcc (0 : ℝ) 1 (by norm_num) p.1).property.2,
    max_eq_right (projIcc (0 : ℝ) 1 (by norm_num) p.1).property.1]
  rfl

noncomputable def parisiGridGradientApproximation (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ParisiSlabGradient 0 1 := parisiFiniteStripGradient (parisiGridRSBScheme μ n) β

theorem norm_parisiGridGradientApproximation_le_one (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ‖parisiGridGradientApproximation β μ n‖ ≤ 1 :=
  norm_parisiFiniteStripGradient_le_one _ _

theorem parisiGridGradientApproximation_terminal (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (x : ℝ) :
    parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (parisiGridGradientApproximation β μ n) (1, x) =
      Real.tanh x := by
  rw [parisiGridGradientApproximation, parisiFiniteStripGradient_extend]
  exact parisiFiniteGradient_terminal _ _ _

theorem parisiGridGradientApproximation_mild (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) :
    IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (parisiGridGradientApproximation β μ n) := by
  intro b hb t ht x
  simp_rw [parisiGridGradientApproximation, parisiFiniteStripGradient_extend]
  exact parisiFiniteGradient_mild μ n β hβ hb ht x

theorem parisiFinitePotential_eq_duhamel_grid (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n : ℕ) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiFinitePotential (parisiGridRSBScheme μ n) β (t, x) =
      parisiDuhamelPotential β (parisiGridMeasure μ n)
        (parisiSlabExtend (by norm_num) (parisiGridGradientApproximation β μ n)) t x := by
  rw [parisiFinitePotential_mild μ n β hβ ⟨by norm_num, le_rfl⟩ ht]
  simp_rw [parisiFinitePotential_terminal]
  rw [parisiGridGradientApproximation, parisiFiniteStripGradient_extend]
  rfl

theorem exists_actual_globalParisiGradient (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ∃ V : ParisiSlabGradient 0 1,
      Tendsto (parisiGridGradientApproximation β μ) atTop (𝓝 V) ∧ ‖V‖ ≤ 1 ∧
      parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
        gaussian_continuous_tanh
        (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le) V = V :=
  exists_globalParisiGradient_of_grid_mild β μ (parisiGridGradientApproximation β μ)
    (norm_parisiGridGradientApproximation_le_one β μ)
    (parisiGridGradientApproximation_mild β hβ μ) (parisiGridGradientApproximation_terminal β μ)

/-- Existence for the genuine arbitrary probability measure in the stated
distributional solution class, now with the finite-grid premises discharged. -/
theorem exists_actual_parisiWeakSolution (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ∃ u v : ℝ × ℝ → ℝ, IsParisiWeakSolution β μ u v ∧
      Continuous u ∧ Continuous v ∧ (∀ p, ‖v p‖ ≤ 1) :=
  exists_parisiWeakSolution_of_grid_mild β hβ μ (parisiGridGradientApproximation β μ)
    (norm_parisiGridGradientApproximation_le_one β μ)
    (parisiGridGradientApproximation_mild β hβ μ) (parisiGridGradientApproximation_terminal β μ)

noncomputable def parisiGlobalExtendBCF (V : ParisiSlabGradient 0 1) : (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V)
    (continuous_parisiSlabExtend (by norm_num) V) ‖V‖
    (norm_parisiSlabExtend_le (by norm_num) V)

theorem lipschitzWith_parisiGlobalExtendBCF : LipschitzWith 1 parisiGlobalExtendBCF := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (V - W))).mpr
  intro p
  exact norm_parisiSlabExtend_sub_le (by norm_num) V W p

theorem parisiGlobalExtendBCF_finite {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    parisiGlobalExtendBCF (parisiFiniteStripGradient s β) = parisiFiniteGradientBCF s β := by
  apply BoundedContinuousFunction.ext
  intro p
  exact congrFun (parisiFiniteStripGradient_extend s β) p

theorem tendsto_parisiFiniteGradientBCF_of_strip {μ : ParisiMeasure} {β : ℝ}
    {V : ParisiSlabGradient 0 1}
    (h : Tendsto (parisiGridGradientApproximation β μ) atTop (𝓝 V)) :
    Tendsto (fun n => parisiFiniteGradientBCF (parisiGridRSBScheme μ n) β) atTop
      (𝓝 (parisiGlobalExtendBCF V)) := by
  have hh := lipschitzWith_parisiGlobalExtendBCF.continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, parisiGridGradientApproximation, parisiGlobalExtendBCF_finite] using hh

theorem norm_parisiDuhamelPotential_grid_sub_le (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1) (n : ℕ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiDuhamelPotential β μ (parisiSlabExtend (by norm_num) V) t x -
      parisiDuhamelPotential β (parisiGridMeasure μ n)
        (parisiSlabExtend (by norm_num) (parisiGridGradientApproximation β μ n)) t x‖ ≤
      β ^ 2 * ‖V - parisiGridGradientApproximation β μ n‖ +
        β ^ 2 / 2 * (1 / (n + 1 : ℕ)) := by
  have hW := norm_parisiGridGradientApproximation_le_one β μ n
  have h := norm_parisiDuhamelPotential_measure_gradient_sub_le β μ (parisiGridMeasure μ n)
    (parisiSlabExtend (by norm_num) V)
    (parisiSlabExtend (by norm_num) (parisiGridGradientApproximation β μ n))
    (continuous_parisiSlabExtend (by norm_num) V).measurable
    (continuous_parisiSlabExtend (by norm_num) (parisiGridGradientApproximation β μ n)).measurable
    1 ‖V - parisiGridGradientApproximation β μ n‖
    (fun p => (norm_parisiSlabExtend_le (by norm_num) V p).trans hV)
    (fun p => (norm_parisiSlabExtend_le (by norm_num) (parisiGridGradientApproximation β μ n) p).trans hW)
    (norm_parisiSlabExtend_sub_le (by norm_num) V (parisiGridGradientApproximation β μ n)) t x ht
  simp only [mul_one, one_pow] at h
  exact h.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (parisiCDF_grid_norm_integral_le μ n) (by positivity)))

theorem tendsto_parisiDuhamelPotential_grid (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1)
    (hlim : Tendsto (parisiGridGradientApproximation β μ) atTop (𝓝 V))
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => parisiDuhamelPotential β (parisiGridMeasure μ n)
      (parisiSlabExtend (by norm_num) (parisiGridGradientApproximation β μ n)) t x)
      atTop (𝓝 (parisiDuhamelPotential β μ (parisiSlabExtend (by norm_num) V) t x)) := by
  have hnormlim : Tendsto (fun n => ‖V - parisiGridGradientApproximation β μ n‖)
      atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun n => V - parisiGridGradientApproximation β μ n)
        atTop (𝓝 (V - V)) := tendsto_const_nhds.sub hlim
    simpa using hh.norm
  have hmeshlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have herr : Tendsto (fun n : ℕ =>
      β ^ 2 * ‖V - parisiGridGradientApproximation β μ n‖ + β ^ 2 / 2 * (1 / (n + 1 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hnormlim).add (tendsto_const_nhds.mul hmeshlim)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herr.eventually (eventually_lt_nhds hε)] with n hn
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_parisiDuhamelPotential_grid_sub_le β μ V hV n t x ht).trans_lt hn

end Paper
