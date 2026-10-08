module

public import Paper.ParisiSolutionSlabs
public import Paper.ParisiTerminalOperator

@[expose] public section

/-! # Actual global Parisi gradient continuity along probability mixtures -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

namespace Paper

/-- A fixed backward mesh propagates actual probability-mixture stability through all slabs. -/
theorem norm_globalParisi_mix_le (β : ℝ) (μ ν : ParisiMeasure)
    (U W : ParisiSlabGradient 0 1) (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hmildU : IsParisiMildOnEverySlab β μ U)
    (hmildW : IsParisiMildOnEverySlab β (parisiMix μ ν ε) W)
    (hterminalU : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (1, x) = Real.tanh x)
    (hterminalW : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) W (1, x) = Real.tanh x)
    (N : ℕ) (hN : 0 < N)
    (hmesh : |β| * gaussianAbsMoment * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8) :
    ‖U - W‖ ≤ parisiBackwardError N ε := by
  let E := ε
  have hE : 0 ≤ E := hε.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hind : ∀ j : ℕ, j ≤ N → ∀ t ∈ Icc (1 - (j : ℝ) / N) 1, ∀ x : ℝ,
      ‖parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (t, x) -
        parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) W (t, x)‖ ≤
          parisiBackwardError j E := by
    intro j
    induction j with
    | zero =>
        intro _ t ht x
        have htone : t = 1 := le_antisymm ht.2 (by simpa using ht.1)
        subst t
        simp [hterminalU, hterminalW, parisiBackwardError]
    | succ j ih =>
        intro hj t ht x
        have hj' : j ≤ N := by omega
        have hcast : (j + 1 : ℝ) ≤ N := by exact_mod_cast hj
        let a : ℝ := 1 - (j + 1 : ℝ) / N
        let b : ℝ := 1 - (j : ℝ) / N
        have ha : 0 ≤ a := by
          dsimp [a]
          linarith [(div_le_one hNpos).mpr hcast]
        have hab : a ≤ b := by
          dsimp [a, b]
          exact sub_le_sub_left (div_le_div_of_nonneg_right (by linarith) hNpos.le) 1
        have hb : b ≤ 1 := by
          dsimp [b]
          linarith [div_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hNpos.le]
        have hba : b - a = 1 / (N : ℝ) := by dsimp [a, b]; ring
        let V := parisiGlobalRestrict ha hb U
        let Z := parisiGlobalRestrict ha hb W
        let g := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (b, y)
        let k := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) W (b, y)
        have hg : Continuous g := (continuous_parisiSlabExtend (by norm_num) U).comp (by fun_prop)
        have hk : Continuous k := (continuous_parisiSlabExtend (by norm_num) W).comp (by fun_prop)
        have hgb : ∀ y, ‖g y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) U _).trans (hU)
        have hkb : ∀ y, ‖k y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) W _).trans (hW)
        have hshort : parisiSlabContractionConstant β a b ≤ 1 / 8 := by
          simpa only [parisiSlabContractionConstant, hba] using hmesh
        have hV : ‖V‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb U).trans ((hU).trans (by norm_num))
        have hZ : ‖Z‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb W).trans ((hW).trans (by norm_num))
        have hv := globalParisiRestriction_fixedPoint β μ U (hU) (hmildU) hab ha hb
        have hz := globalParisiRestriction_fixedPoint β (parisiMix μ ν ε) W (hW) (hmildW) hab ha hb
        let gB : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg 1 hgb
        let kB : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup k hk 1 hkb
        have hterminalNorm : ‖gB - kB‖ ≤ parisiBackwardError j E := by
          apply (BoundedContinuousFunction.norm_le (parisiBackwardError_nonneg j E hE)).mpr
          intro y
          exact ih hj' b ⟨le_rfl, hb⟩ y
        have hdiff0 := localParisiGradient_terminal_mix_stability β μ ν hab gB kB hgb hkb
          hshort V Z hV hZ ε hε hv hz
        have hparam := mul_le_mul_of_nonneg_right hshort hε.1
        have hdiff : ‖V - Z‖ ≤ 2 * parisiBackwardError j E + E := by
          dsimp only [E]
          dsimp only [E] at hterminalNorm
          linarith
        have ht' : t ∈ Icc a 1 := by simpa only [Nat.cast_add, Nat.cast_one] using ht
        by_cases htb : t ≤ b
        · have hp := (V - Z).norm_coe_le_norm (⟨t, ⟨ht'.1, htb⟩⟩, x)
          change ‖V (⟨t, ⟨ht'.1, htb⟩⟩, x) - Z (⟨t, ⟨ht'.1, htb⟩⟩, x)‖ ≤ _ at hp
          rw [parisiGlobalRestrict_apply, parisiGlobalRestrict_apply] at hp
          exact hp.trans hdiff
        · exact (ih hj' t ⟨(lt_of_not_ge htb).le, ht'.2⟩ x).trans
            (parisiBackwardError_le_succ j E hE)
  apply (BoundedContinuousFunction.norm_le (parisiBackwardError_nonneg N E hE)).mpr
  intro p
  have hpt : (p.1 : ℝ) ∈ Icc (1 - (N : ℝ) / N) 1 := by
    simpa only [div_self hNne, sub_self] using p.1.property
  have h := hind N le_rfl p.1 hpt p.2
  change ‖U p - W p‖ ≤ _
  simpa only [parisiSlabExtend, projIcc_of_mem _ p.1.property] using h

theorem parisiGradient_terminal (β : ℝ) (μ : ParisiMeasure) (x : ℝ) :
    parisiGradient β μ (1, x) = Real.tanh x := by
  rw [parisiGradient_equation β μ 1 x (by norm_num)]
  simp [parisiGradientCorrection, heatSemigroup, gaussianExpectation]

/-- A genuine global mixing bound, uniform in the two probability measures. -/
theorem exists_parisiGradientBCF_mix_bound (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (μ ν : ParisiMeasure) (ε : ℝ), ε ∈ Icc (0 : ℝ) 1 →
      ‖parisiGradientBCF β μ - parisiGradientBCF β (parisiMix μ ν ε)‖ ≤ M * ε := by
  let c := |β| * gaussianAbsMoment
  have hc : 0 ≤ c := mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  obtain ⟨N, hN⟩ := exists_nat_gt (64 * c ^ 2 + 1)
  have hNpos : (0 : ℝ) < N := by nlinarith [sq_nonneg c]
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hratio : c ^ 2 / (N : ℝ) < (1 / 8 : ℝ) ^ 2 :=
    (div_lt_iff₀ hNpos).mpr (by nlinarith)
  have hsquare : (c * Real.sqrt (1 / (N : ℝ))) ^ 2 = c ^ 2 / (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    ring
  have hmesh : |β| * gaussianAbsMoment * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8 := by
    change c * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8
    have hp := mul_nonneg hc (Real.sqrt_nonneg (1 / (N : ℝ)))
    nlinarith
  refine ⟨(2 : ℝ) ^ N - 1, ?_, ?_⟩
  · simpa only [parisiBackwardError_eq, mul_one] using
      parisiBackwardError_nonneg N 1 (by norm_num)
  · intro μ ν ε hε
    simpa only [parisiBackwardError_eq] using norm_globalParisi_mix_le β μ ν
      (parisiGradientBCF β μ) (parisiGradientBCF β (parisiMix μ ν ε))
      (norm_parisiGradientBCF_le_one β μ) (norm_parisiGradientBCF_le_one β (parisiMix μ ν ε)) ε hε
      (parisiGradientBCF_mildOnEverySlab_all β μ)
      (parisiGradientBCF_mildOnEverySlab_all β (parisiMix μ ν ε))
      (parisiGradient_terminal β μ) (parisiGradient_terminal β (parisiMix μ ν ε))
      N hNnat hmesh

/-- The actual globally constructed PDE gradient is continuous along probability mixtures. -/
theorem continuousWithinAt_parisiGradientBCF_mix (β : ℝ) (μ ν : ParisiMeasure) :
    ContinuousWithinAt (fun ε => parisiGradientBCF β (parisiMix μ ν ε))
      (Icc (0 : ℝ) 1) 0 := by
  obtain ⟨M, hM, hbound⟩ := exists_parisiGradientBCF_mix_bound β
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [parisiMix_zero]
  apply squeeze_zero' (.of_forall fun ε => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [norm_sub_rev] using hbound μ ν ε hε
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => M)
      (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 M)).mul nhdsWithin_le_nhds

end Paper

