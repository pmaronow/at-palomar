module

public import Paper.ParisiTerminalStability
public import Paper.ParisiMildUnique
public import Paper.ParisiGridStability
public import Paper.ParisiWeakMild

@[expose] public section

/-! # Uniform construction from genuine atomic-grid mild gradients

A fixed, finite backward time mesh propagates quantitative local stability.
This turns the actual finite-grid solutions into a Cauchy sequence in the
complete space of bounded continuous gradients on the whole strip.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Paper

noncomputable def parisiGlobalRestrict {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (V : ParisiSlabGradient 0 1) : ParisiSlabGradient a b :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => V (⟨p.1, ⟨ha.trans p.1.property.1, p.1.property.2.trans hb⟩⟩, p.2))
    (V.continuous.comp (by fun_prop)) ‖V‖ (fun p => V.norm_coe_le_norm _)

theorem parisiGlobalRestrict_apply {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (V : ParisiSlabGradient 0 1) (p : Icc a b × ℝ) :
    parisiGlobalRestrict ha hb V p =
      parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (p.1, p.2) := by
  have hp : (p.1 : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans p.1.property.1, p.1.property.2.trans hb⟩
  simp only [parisiGlobalRestrict, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    parisiSlabExtend, projIcc_of_mem _ hp]

theorem norm_parisiGlobalRestrict_le {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (V : ParisiSlabGradient 0 1) : ‖parisiGlobalRestrict ha hb V‖ ≤ ‖V‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg V)).mpr (fun _p => V.norm_coe_le_norm _)

/-- The equation is imposed at every possible terminal time in the strip,
so it can be restricted to a fixed mesh unrelated to the atomic grid. -/
def IsParisiMildOnEverySlab (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) : Prop :=
  ∀ b ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) b, ∀ x : ℝ,
    parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (t, x) =
      heatSemigroup (β ^ 2 * (b - t))
        (fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (b, y)) x +
      parisiGradientCorrection β μ
        (parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V) b t x

theorem globalParisiRestriction_fixedPoint (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1)
    (hmild : IsParisiMildOnEverySlab β μ V)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    parisiSlabGradientOperator β μ hab
      (fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (b, y))
      ((continuous_parisiSlabExtend (by norm_num) V).comp (by fun_prop))
      (fun y => (norm_parisiSlabExtend_le (by norm_num) V (b, y)).trans hV)
      (parisiGlobalRestrict ha hb V) = parisiGlobalRestrict ha hb V := by
  have hext (s : ℝ) (hs : s ∈ Icc a b) (y : ℝ) :
      parisiSlabExtend hab (parisiGlobalRestrict ha hb V) (s, y) =
        parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (s, y) := by
    unfold parisiSlabExtend
    rw [projIcc_of_mem hab hs]
    exact parisiGlobalRestrict_apply ha hb V (⟨s, hs⟩, y)
  apply BoundedContinuousFunction.ext
  intro p
  change parisiSlabGradientValue β μ hab _ (parisiGlobalRestrict ha hb V) p = _
  unfold parisiSlabGradientValue
  rw [parisiNormalizedGradientCorrection_eq β μ _ b p.1 p.2 p.1.property.2,
    parisiGlobalRestrict_apply]
  rw [parisiGradientCorrection_congr β μ _ _ b p.1 p.2 p.1.property.2
    (fun s hs y => hext s ⟨p.1.property.1.trans hs.1, hs.2⟩ y)]
  exact (hmild b ⟨ha.trans hab, hb⟩ p.1
    ⟨ha.trans p.1.property.1, p.1.property.2⟩ p.2).symm

theorem parisiCDF_grid_pair_integral_le (μ : ParisiMeasure) (n m : ℕ) (hnm : n ≤ m) :
    (∫ s in (0 : ℝ)..1,
      ‖parisiCDF (parisiGridMeasure μ n) s - parisiCDF (parisiGridMeasure μ m) s‖) ≤
      2 / (n + 1 : ℕ) := by
  have hin := parisiCDF_difference_intervalIntegrable μ (parisiGridMeasure μ n) 0 1
  have him := parisiCDF_difference_intervalIntegrable μ (parisiGridMeasure μ m) 0 1
  have hi := parisiCDF_difference_intervalIntegrable (parisiGridMeasure μ n)
    (parisiGridMeasure μ m) 0 1
  calc
    _ ≤ ∫ s in (0 : ℝ)..1,
        ‖parisiCDF μ s - parisiCDF (parisiGridMeasure μ n) s‖ +
        ‖parisiCDF μ s - parisiCDF (parisiGridMeasure μ m) s‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi (hin.add him)
      intro s _
      calc
        _ = ‖(parisiCDF μ s - parisiCDF (parisiGridMeasure μ m) s) -
            (parisiCDF μ s - parisiCDF (parisiGridMeasure μ n) s)‖ := by congr 1; ring
        _ ≤ _ := by
          simpa only [add_comm] using (norm_sub_le
            (parisiCDF μ s - parisiCDF (parisiGridMeasure μ m) s)
            (parisiCDF μ s - parisiCDF (parisiGridMeasure μ n) s))
    _ ≤ 1 / (n + 1 : ℕ) + 1 / (m + 1 : ℕ) := by
      rw [intervalIntegral.integral_add hin him]
      exact add_le_add (parisiCDF_grid_norm_integral_le μ n) (parisiCDF_grid_norm_integral_le μ m)
    _ ≤ 2 / (n + 1 : ℕ) := by
      have hm : (n + 1 : ℕ) ≤ (m + 1 : ℕ) := Nat.succ_le_succ hnm
      have hd : (1 : ℝ) / (m + 1 : ℕ) ≤ 1 / (n + 1 : ℕ) := by
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hm)
      calc
        (1 : ℝ) / (n + 1 : ℕ) + 1 / (m + 1 : ℕ) ≤
            1 / (n + 1 : ℕ) + 1 / (n + 1 : ℕ) := add_le_add (le_refl _) hd
        _ = (2 : ℝ) / (n + 1 : ℕ) := by ring

noncomputable def parisiBackwardError : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j + 1, E => 2 * parisiBackwardError j E + E

theorem parisiBackwardError_nonneg (j : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    0 ≤ parisiBackwardError j E := by
  induction j with
  | zero => simp [parisiBackwardError]
  | succ j ih => simp only [parisiBackwardError]; positivity

theorem parisiBackwardError_le_succ (j : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    parisiBackwardError j E ≤ parisiBackwardError (j + 1) E := by
  have h := parisiBackwardError_nonneg j E hE
  simp only [parisiBackwardError]
  linarith

theorem parisiBackwardError_eq (j : ℕ) (E : ℝ) :
    parisiBackwardError j E = ((2 : ℝ) ^ j - 1) * E := by
  induction j with
  | zero => simp [parisiBackwardError]
  | succ j ih => rw [parisiBackwardError, ih, pow_succ]; ring

theorem norm_globalParisi_grid_pair_le (β : ℝ) (μ : ParisiMeasure)
    (W : ℕ → ParisiSlabGradient 0 1) (hW : ∀ n, ‖W n‖ ≤ 1)
    (hmild : ∀ n, IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (W n))
    (hterminal : ∀ n x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (1, x) = Real.tanh x)
    (N : ℕ) (hN : 0 < N)
    (hmesh : |β| * gaussianAbsMoment * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8)
    (n m : ℕ) (hnm : n ≤ m) :
    ‖W n - W m‖ ≤ parisiBackwardError N
      (12 * |β| * gaussianAbsMoment * Real.sqrt (2 / (n + 1 : ℕ))) := by
  let E := 12 * |β| * gaussianAbsMoment * Real.sqrt (2 / (n + 1 : ℕ))
  have hE : 0 ≤ E := by dsimp [E]; have := gaussianAbsMoment_nonneg; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hind : ∀ j : ℕ, j ≤ N → ∀ t ∈ Icc (1 - (j : ℝ) / N) 1, ∀ x : ℝ,
      ‖parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (t, x) -
        parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W m) (t, x)‖ ≤
          parisiBackwardError j E := by
    intro j
    induction j with
    | zero =>
        intro _ t ht x
        have htone : t = 1 := le_antisymm ht.2 (by simpa using ht.1)
        subst t
        simp [hterminal, parisiBackwardError]
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
        let V := parisiGlobalRestrict ha hb (W n)
        let Z := parisiGlobalRestrict ha hb (W m)
        let g := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (b, y)
        let k := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W m) (b, y)
        have hg : Continuous g := (continuous_parisiSlabExtend (by norm_num) (W n)).comp (by fun_prop)
        have hk : Continuous k := (continuous_parisiSlabExtend (by norm_num) (W m)).comp (by fun_prop)
        have hgb : ∀ y, ‖g y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) (W n) _).trans (hW n)
        have hkb : ∀ y, ‖k y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) (W m) _).trans (hW m)
        have hshort : parisiSlabContractionConstant β a b ≤ 1 / 8 := by
          simpa only [parisiSlabContractionConstant, hba] using hmesh
        have hV : ‖V‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb (W n)).trans ((hW n).trans (by norm_num))
        have hZ : ‖Z‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb (W m)).trans ((hW m).trans (by norm_num))
        have hv := globalParisiRestriction_fixedPoint β (parisiGridMeasure μ n) (W n) (hW n) (hmild n) hab ha hb
        have hz := globalParisiRestriction_fixedPoint β (parisiGridMeasure μ m) (W m) (hW m) (hmild m) hab ha hb
        have hdiff := localParisiGradient_terminal_measure_mesh_stability β
          (parisiGridMeasure μ n) (parisiGridMeasure μ m) hab ha hb g k hg hk hgb hkb
          hshort V Z hV hZ hv hz (parisiBackwardError j E)
          (fun y => ih hj' b ⟨le_rfl, hb⟩ y) (2 / (n + 1 : ℕ)) (by positivity)
          (parisiCDF_grid_pair_integral_le μ n m hnm)
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
  change ‖W n p - W m p‖ ≤ _
  simpa only [parisiSlabExtend, projIcc_of_mem _ p.1.property] using h

theorem cauchySeq_globalParisi_grid (β : ℝ) (μ : ParisiMeasure)
    (W : ℕ → ParisiSlabGradient 0 1) (hW : ∀ n, ‖W n‖ ≤ 1)
    (hmild : ∀ n, IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (W n))
    (hterminal : ∀ n x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (1, x) = Real.tanh x) :
    CauchySeq W := by
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
  have hδ : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using hh
  have herr : Tendsto (fun n : ℕ => parisiBackwardError N
      (12 * |β| * gaussianAbsMoment * Real.sqrt (2 / (n + 1 : ℕ)))) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [parisiBackwardError_eq]
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.mul hδ.sqrt)
  apply cauchySeq_of_le_tendsto_0' _ _ herr
  intro n m hnm
  rw [dist_eq_norm]
  exact norm_globalParisi_grid_pair_le β μ W hW hmild hterminal N hNnat hmesh n m hnm

theorem globalParisi_fixedPoint_of_everySlab (β : ℝ) (μ : ParisiMeasure)
    (V : ParisiSlabGradient 0 1) (hV : ‖V‖ ≤ 1)
    (hmild : IsParisiMildOnEverySlab β μ V)
    (hterminal : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (1, x) = Real.tanh x) :
    parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
      gaussian_continuous_tanh (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le) V = V := by
  have h := globalParisiRestriction_fixedPoint β μ V hV hmild
    (by norm_num : (0 : ℝ) ≤ 1) (le_refl 0) (le_refl 1)
  have hg : (fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (1, y)) = Real.tanh :=
    funext hterminal
  have he : parisiGlobalRestrict (le_refl (0 : ℝ)) (le_refl (1 : ℝ)) V = V := by
    apply BoundedContinuousFunction.ext
    intro p
    rfl
  simpa only [hg, he] using h

theorem norm_parisiSlabGradientOperator_measure_mesh_sub_le (β : ℝ) (μ ν : ParisiMeasure)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ x, ‖g x‖ ≤ 1)
    (V : ParisiSlabGradient a b) (hV : ‖V‖ ≤ 2)
    (δ : ℝ) (hδ : 0 < δ)
    (hCDF : (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) ≤ δ) :
    ‖parisiSlabGradientOperator β μ hab g hg hgb V -
      parisiSlabGradientOperator β ν hab g hg hgb V‖ ≤
      6 * |β| * gaussianAbsMoment * Real.sqrt δ := by
  have h := norm_parisiSlabGradientOperator_measure_L1_sub_le β μ ν hab ha hb g hg hgb V δ hδ
  have hsqrtne : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have heq : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
    conv_lhs => arg 1; rw [← Real.sq_sqrt hδ.le]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hsqrtne, mul_one]
  have hscaled := mul_le_mul_of_nonneg_right hCDF (inv_nonneg.mpr (Real.sqrt_nonneg δ))
  rw [heq] at hscaled
  have hnorm : ‖V‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg V]
  have hc : 0 ≤ |β| * gaussianAbsMoment := mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  have hcoeff : |β| * gaussianAbsMoment * ‖V‖ ^ 2 / 2 ≤ 2 * (|β| * gaussianAbsMoment) := by
    nlinarith [mul_le_mul_of_nonneg_left hnorm hc]
  have hbr : 0 ≤ 2 * Real.sqrt δ +
      (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) * (Real.sqrt δ)⁻¹ := by
    have hi : 0 ≤ (∫ s in (0 : ℝ)..1, ‖parisiCDF μ s - parisiCDF ν s‖) :=
      intervalIntegral.integral_nonneg_of_forall
        (by norm_num : (0 : ℝ) ≤ 1) (fun s => norm_nonneg (parisiCDF μ s - parisiCDF ν s))
    positivity
  calc
    _ ≤ _ := h
    _ ≤ (2 * (|β| * gaussianAbsMoment)) * (3 * Real.sqrt δ) :=
      mul_le_mul hcoeff (by linarith) hbr (by positivity)
    _ = _ := by ring

/-- The actual finite-grid equations construct a bounded continuous global
gradient for the original probability measure, with the sharp unit bound.
The supplied sequence will be instantiated by the concrete Cole--Hopf grid
recursions, rather than by an existence assumption for the general PDE. -/
theorem exists_globalParisiGradient_of_grid_mild (β : ℝ) (μ : ParisiMeasure)
    (W : ℕ → ParisiSlabGradient 0 1) (hW : ∀ n, ‖W n‖ ≤ 1)
    (hmild : ∀ n, IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (W n))
    (hterminal : ∀ n x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (1, x) = Real.tanh x) :
    ∃ V : ParisiSlabGradient 0 1, Tendsto W atTop (𝓝 V) ∧ ‖V‖ ≤ 1 ∧
      parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
        gaussian_continuous_tanh
        (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le) V = V := by
  obtain ⟨V, hlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_globalParisi_grid β μ W hW hmild hterminal)
  have hV : ‖V‖ ≤ 1 := le_of_tendsto hlim.norm (.of_forall hW)
  refine ⟨V, hlim, hV, ?_⟩
  let G := parisiSlabGradientOperator β μ (by norm_num : (0 : ℝ) ≤ 1) Real.tanh
    gaussian_continuous_tanh (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
  have hnormlim : Tendsto (fun n => ‖V - W n‖) atTop (𝓝 (0 : ℝ)) := by
    have hh : Tendsto (fun n => V - W n) atTop (𝓝 (V - V)) := tendsto_const_nhds.sub hlim
    simpa using hh.norm
  have hmeshlim : Tendsto (fun n : ℕ => Real.sqrt (1 / (n + 1 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  have herrlim : Tendsto (fun n : ℕ =>
      4 * parisiSlabContractionConstant β 0 1 * ‖V - W n‖ +
      6 * |β| * gaussianAbsMoment * Real.sqrt (1 / (n + 1 : ℕ)) + ‖V - W n‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using ((tendsto_const_nhds.mul hnormlim).add
      (tendsto_const_nhds.mul hmeshlim)).add hnormlim
  have hbound (n : ℕ) : ‖G V - V‖ ≤
      4 * parisiSlabContractionConstant β 0 1 * ‖V - W n‖ +
      6 * |β| * gaussianAbsMoment * Real.sqrt (1 / (n + 1 : ℕ)) + ‖V - W n‖ := by
    have hn := globalParisi_fixedPoint_of_everySlab β (parisiGridMeasure μ n) (W n) (hW n)
      (hmild n) (hterminal n)
    have hmeasure := norm_parisiSlabGradientOperator_measure_mesh_sub_le β μ (parisiGridMeasure μ n)
      (by norm_num : (0 : ℝ) ≤ 1) (le_refl 0) (le_refl 1) Real.tanh gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      (W n) ((hW n).trans (by norm_num)) (1 / (n + 1 : ℕ)) (by positivity)
      (parisiCDF_grid_norm_integral_le μ n)
    rw [hn] at hmeasure
    have hlip := norm_parisiSlabGradientOperator_sub_le β μ (by norm_num : (0 : ℝ) ≤ 1)
      Real.tanh gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      V (W n) (hV.trans (by norm_num)) ((hW n).trans (by norm_num))
    calc
      _ ≤ ‖G V - G (W n)‖ + ‖G (W n) - V‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖G V - G (W n)‖ + (‖G (W n) - W n‖ + ‖W n - V‖) :=
        add_le_add (le_refl _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ ≤ _ := by rw [norm_sub_rev (W n) V]; linarith
  have hz : ‖G V - V‖ ≤ 0 := ge_of_tendsto herrlim (.of_forall hbound)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- The proved approximation construction and the proved weak verification
combine to give an actual weak solution once the finite-grid equations are
instantiated. The uniform bound concerns the gradient, not the potential. -/
theorem exists_parisiWeakSolution_of_grid_mild (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (W : ℕ → ParisiSlabGradient 0 1)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (hmild : ∀ n, IsParisiMildOnEverySlab β (parisiGridMeasure μ n) (W n))
    (hterminal : ∀ n x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) (W n) (1, x) = Real.tanh x) :
    ∃ u v : ℝ × ℝ → ℝ, IsParisiWeakSolution β μ u v ∧
      Continuous u ∧ Continuous v ∧ (∀ p, ‖v p‖ ≤ 1) := by
  obtain ⟨V, _hlim, hV, hfix⟩ := exists_globalParisiGradient_of_grid_mild β μ W hW hmild hterminal
  let v := parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V
  have hv : Continuous v := continuous_parisiSlabExtend (by norm_num) V
  have hb : ∀ p, ‖v p‖ ≤ 1 := fun p => (norm_parisiSlabExtend_le (by norm_num) V p).trans hV
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) Real.tanh x +
        parisiGradientCorrection β μ v 1 t x := by
    intro t ht x
    have h := localParisiGradient_equation β μ (by norm_num : (0 : ℝ) ≤ 1)
      Real.tanh gaussian_continuous_tanh
      (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
      V hfix (⟨t, ht⟩, x)
    simpa only [v, parisiSlabExtend, projIcc_of_mem _ ht] using h
  refine ⟨parisiContinuousPotential β μ v, v,
    isParisiWeakSolution_of_boundedContinuous_mildGradient β hβ μ v hv 1 hb heq,
    continuous_parisiContinuousPotential β μ v hv 1 hb, hv, hb⟩

end Paper
