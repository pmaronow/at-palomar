module

public import Paper.ParisiDiracIdentification
public import Paper.GaussianPoincare
public import StochasticCalculus.DoleansDade
public import Mathlib.Probability.CondVar

@[expose] public section

/-! # The literal conditional Gaussian identities before the Dirac interface

The future canonical Brownian increment is independent of the entire natural
filtration. Testing against past events and using its actual Gaussian law gives
the conditional heat formula, hence the displayed conditional expectation and
conditional Poincare statements used in the paper's proof of Proposition 4.1.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology

namespace Paper

/-- Conditional averaging against an actually independent real variable.
The proof tests all past events and uses the actual independent product law;
it does not assume a conditional-distribution formula. -/
theorem condExp_independent_add_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (X N : Ω → ℝ) (hX : StronglyMeasurable[m] X) (hN : Measurable[mΩ] N)
    (ν : Measure ℝ) (hLaw : HasLaw N ν P)
    (hIndep : Indep (MeasurableSpace.comap N inferInstance) m P)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (M : ℝ) (hM : ∀ x, ‖ψ x‖ ≤ M) :
    P[(fun ω => ψ (X ω + N ω)) | m] =ᵐ[P]
      fun ω => ∫ z, ψ (X ω + z) ∂ν := by
  classical
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure ν := hLaw.isProbabilityMeasure_iff.mp inferInstance
  let K : ℝ → ℝ := fun x => ∫ z, ψ (x + z) ∂ν
  have hK : StronglyMeasurable K :=
    (hψ.comp (measurable_fst.add measurable_snd)).stronglyMeasurable.integral_prod_right'
  have hKb (x : ℝ) : ‖K x‖ ≤ M := by
    simpa only [K, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ν) (.of_forall fun z => hM (x + z))
  have htarget : Integrable (fun ω => ψ (X ω + N ω)) P :=
    (integrable_const M).mono'
      (hψ.comp ((show StronglyMeasurable[mΩ] X from hX.mono hm).measurable.add hN)).aestronglyMeasurable
      (.of_forall fun ω => hM (X ω + N ω))
  have hcand : StronglyMeasurable[m] (fun ω => K (X ω)) := hK.comp_measurable hX.measurable
  have hcandInt : Integrable (fun ω => K (X ω)) P :=
    (integrable_const M).mono' (show StronglyMeasurable[mΩ] (fun ω => K (X ω)) from hcand.mono hm).aestronglyMeasurable
      (.of_forall fun ω => hKb (X ω))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm htarget
  · intro A hA _
    exact hcandInt.integrableOn
  · intro A hA _
    let Y : Ω → ℝ × Bool := fun ω => (X ω, decide (ω ∈ A))
    have hmY : Measurable[m] Y := by
      apply hX.measurable.prodMk
      apply measurable_to_bool
      convert hA using 1
      ext ω
      simp
    have hY : Measurable[mΩ] Y := hmY.mono hm le_rfl
    have hindY : IndepFun N Y P :=
      (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_right hIndep hmY.comap_le)
    let F : ℝ × (ℝ × Bool) → ℝ := fun p => if p.2.2 then ψ (p.2.1 + p.1) else 0
    have hF : Measurable F := by
      apply Measurable.ite
      · exact measurableSet_preimage (measurable_snd.comp measurable_snd) (measurableSet_singleton true)
      · exact hψ.comp ((measurable_fst.comp measurable_snd).add measurable_fst)
      · exact measurable_const
    have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
    have hFb (p : ℝ × (ℝ × Bool)) : ‖F p‖ ≤ M := by
      dsimp [F]
      split_ifs
      · exact hM _
      · simpa using hM0
    have : IsProbabilityMeasure (P.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
    have hiF : Integrable F (ν.prod (P.map Y)) :=
      (integrable_const M).mono' hF.aestronglyMeasurable (.of_forall hFb)
    have hjoint : P.map (fun ω => (N ω, Y ω)) = ν.prod (P.map Y) := by
      rw [hindY.map_prod_eq_prod_map_map hN.aemeasurable hY.aemeasurable, hLaw.map_eq]
    have he : (∫ ω, F (N ω, Y ω) ∂P) = ∫ y, ∫ z, F (z, y) ∂ν ∂P.map Y := by
      rw [← integral_map (hN.prodMk hY).aemeasurable hF.aestronglyMeasurable, hjoint,
        integral_prod_symm F hiF]
    have hinner : (fun y => ∫ z, F (z, y) ∂ν) =
        fun y : ℝ × Bool => if y.2 then K y.1 else 0 := by
      funext y
      cases hb : y.2 <;> simp [F, K, hb]
    rw [hinner, integral_map hY.aemeasurable] at he
    · rw [← integral_indicator (hm _ hA), ← integral_indicator (hm _ hA)]
      simpa [Y, F, K, indicator] using he.symm
    · exact (Measurable.ite
        (measurableSet_preimage measurable_snd (measurableSet_singleton true))
        (hK.measurable.comp measurable_fst) measurable_const).aestronglyMeasurable
  · exact hcand.aestronglyMeasurable

/-- Every bounded measurable observable has its literal conditional Gaussian
law before q, proved from independence of the actual Brownian increment. -/
theorem condExp_canonicalDiracState_before (β h q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (M : ℝ) (hM : ∀ x, ‖ψ x‖ ≤ M) :
    canonicalBrownianMeasure[(fun ω => ψ (canonicalDiracStateReal β h q hq ω q)) |
      canonicalBrownianFiltration t.toNNReal] =ᵐ[canonicalBrownianMeasure]
      fun ω => heatSemigroup (β ^ 2 * (q - t)) ψ
        (canonicalDiracStateReal β h q hq ω t) := by
  let a := t.toNNReal
  let b := q.toNNReal
  let N : BrownianSample → ℝ := fun ω => β * (canonicalBrownian b ω - canonicalBrownian a ω)
  let X : BrownianSample → ℝ := canonicalDiracItoState β h q hq a
  have hab : a ≤ b := Real.toNNReal_mono ht.2
  have hvar : NNReal.mk (β ^ 2) (sq_nonneg β) * nndist (b : ℝ) (a : ℝ) =
      (β ^ 2 * (q - t)).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, ← dist_nndist, Real.dist_eq,
      a, b, Real.coe_toNNReal _ ht.1, Real.coe_toNNReal _ hq.1,
      abs_of_nonneg (sub_nonneg.mpr ht.2),
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2))]
  have hLaw : HasLaw N (gaussianReal 0 (β ^ 2 * (q - t)).toNNReal)
      canonicalBrownianMeasure := by
    have hl := gaussianReal_const_mul
      (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_sub b a) β
    convert hl using 1
    congr 1
    · simp
    · exact hvar.symm
  have hind := indep_brownianIncrement_natural
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal
    (fun s => (measurable_canonicalBrownian s).stronglyMeasurable) hab
  have hNcomap : Measurable[MeasurableSpace.comap
      (fun ω => canonicalBrownian b ω - canonicalBrownian a ω) inferInstance] N := by
    have hraw : Measurable[MeasurableSpace.comap
        (fun ω => canonicalBrownian b ω - canonicalBrownian a ω) inferInstance]
        (fun ω => canonicalBrownian b ω - canonicalBrownian a ω) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hraw.const_mul β
  have hIndep : Indep (MeasurableSpace.comap N inferInstance)
      (canonicalBrownianFiltration a) canonicalBrownianMeasure :=
    indep_of_indep_of_le_left hind hNcomap.comap_le
  have hN : Measurable N :=
    ((measurable_canonicalBrownian b).sub (measurable_canonicalBrownian a)).const_mul β
  have he := condExp_independent_add_bounded (canonicalBrownianFiltration.le a) X N
    (stronglyAdapted_canonicalDiracItoState β h q hq a) hN
    (gaussianReal 0 (β ^ 2 * (q - t)).toNNReal) hLaw hIndep ψ hψ M hM
  have hXeq (ω : BrownianSample) : X ω = canonicalDiracStateReal β h q hq ω t := by
    dsimp only [X]
    rw [canonicalDiracItoState_eq β h q hq
      (by simpa only [a, Real.coe_toNNReal _ ht.1] using ht.2.trans hq.2) ω]
    simp only [a, Real.coe_toNNReal _ ht.1]
  have hsum : (fun ω => ψ (X ω + N ω)) =
      fun ω => ψ (canonicalDiracStateReal β h q hq ω q) := by
    funext ω
    congr 1
    rw [hXeq ω, canonicalDiracState_before β h q hq ω ht,
      canonicalDiracState_before β h q hq ω ⟨hq.1, le_rfl⟩]
    dsimp [N, a, b]
    ring
  rw [hsum] at he
  apply he.trans
  exact .of_forall fun ω => by
    dsimp only
    rw [hXeq ω, heatSemigroup_eq_gaussian_integral (β ^ 2 * (q - t))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)) ψ hψ]
    have hl := gaussianReal_const_add
      (HasLaw.id (μ := gaussianReal 0 (β ^ 2 * (q - t)).toNNReal))
      (canonicalDiracStateReal β h q hq ω t)
    have hi := hl.integral_comp hψ.aestronglyMeasurable
    simpa only [Function.comp_apply, id_eq, zero_add] using hi

/-- The paper's literal conditional-expectation representation, now with the
actual arbitrary-measure PDE and selected strong Brownian state. -/
theorem condExp_selectedParisiDirac_gradient_before (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    canonicalBrownianMeasure[(fun ω => Real.tanh
      (selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q)) |
      canonicalBrownianFiltration t.toNNReal] =ᵐ[canonicalBrownianMeasure]
      fun ω => parisiGradient β (diracOverlap q hq)
        (t, selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t) := by
  have hqeq : (fun ω => Real.tanh (selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q)) =
      fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q) := by
    funext ω
    rw [selectedParisiState_dirac_eq β h q hβ hq ω hq]
  rw [hqeq]
  have hc := condExp_canonicalDiracState_before β h q hq ht Real.tanh
    gaussian_continuous_tanh.measurable 1
    (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
  apply hc.trans
  exact .of_forall fun ω => by
    dsimp only
    rw [selectedParisiState_dirac_eq β h q hβ hq ω ⟨ht.1, ht.2.trans hq.2⟩,
      parisiGradient_dirac_soft β q hβ hq t _ ht]
    unfold heatSemigroup rsSoftDx
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]

theorem memLp_canonicalDirac_tanh_interface (β h q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    MemLp (fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q)) 2
      canonicalBrownianMeasure := by
  have he : (fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q)) =
      fun ω => Real.tanh (h + β * canonicalBrownian q.toNNReal ω) := by
    funext ω
    rw [canonicalDiracState_before β h q hq ω ⟨hq.1, le_rfl⟩]
  rw [he]
  have hm : AEStronglyMeasurable
      (fun ω => Real.tanh (h + β * canonicalBrownian q.toNNReal ω)) canonicalBrownianMeasure := by
    exact (gaussian_continuous_tanh.measurable.comp
      (measurable_const.add ((measurable_canonicalBrownian _).const_mul β))).aestronglyMeasurable
  exact MemLp.of_bound hm 1 (.of_forall fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (h + β * canonicalBrownian q.toNNReal ω)).le)

/-- Conditional Gaussian Poincare on the actual Brownian filtration, in the
literal conditional-variance form displayed in the paper. -/
theorem condVar_canonicalDirac_tanh_before (β h q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    (Var[(fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q));
      canonicalBrownianMeasure | canonicalBrownianFiltration t.toNNReal]) ≤ᵐ[canonicalBrownianMeasure]
      fun ω => β ^ 2 * (q - t) *
        canonicalBrownianMeasure[(fun ω => sech (canonicalDiracStateReal β h q hq ω q) ^ 4) |
          canonicalBrownianFiltration t.toNNReal] ω := by
  have hc := condExp_canonicalDiracState_before β h q hq ht Real.tanh
    gaussian_continuous_tanh.measurable 1
    (fun x => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le)
  have hcs := condExp_canonicalDiracState_before β h q hq ht (fun x => Real.tanh x ^ 2)
    (gaussian_continuous_tanh.pow 2).measurable 1
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact tanh_sq_le_one x)
  have hcf := condExp_canonicalDiracState_before β h q hq ht (fun x => sech x ^ 4)
    (continuous_sech.pow 4).measurable 1
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos x).le 4)]
                 exact sech_fourth_le_one x)
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (canonicalBrownianFiltration.le t.toNNReal)
    (memLp_canonicalDirac_tanh_interface β h q hq)
  have hell : 0 ≤ β ^ 2 * (q - t) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)
  filter_upwards [hv, hc, hcs, hcf] with ω hω hcω hcsω hcfω
  dsimp only [Pi.sub_apply, Pi.pow_apply] at hω
  rw [hω]
  change canonicalBrownianMeasure[(fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q) ^ 2) |
    canonicalBrownianFiltration t.toNNReal] ω -
    canonicalBrownianMeasure[(fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q)) |
      canonicalBrownianFiltration t.toNNReal] ω ^ 2 ≤ _
  rw [hcω, hcsω, hcfω]
  have hp := gaussian_poincare_tanh (canonicalDiracStateReal β h q hq ω t)
    (Real.sqrt (β ^ 2 * (q - t))) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hell] at hp
  exact hp

/-- The conditional Poincare inequality with the actual general-PDE-selected
Dirac state, rather than an unidentified diffusion representative. -/
theorem condVar_selectedParisiDirac_tanh_before (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    (Var[(fun ω => Real.tanh (selectedParisiStateReal β h hβ.ne'
      (diracOverlap q hq) ω q));
      canonicalBrownianMeasure | canonicalBrownianFiltration t.toNNReal]) ≤ᵐ[canonicalBrownianMeasure]
      fun ω => β ^ 2 * (q - t) *
        canonicalBrownianMeasure[(fun ω => sech (selectedParisiStateReal β h hβ.ne'
          (diracOverlap q hq) ω q) ^ 4) | canonicalBrownianFiltration t.toNNReal] ω := by
  have htan : (fun ω => Real.tanh (selectedParisiStateReal β h hβ.ne'
      (diracOverlap q hq) ω q)) =
      fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q) := by
    funext ω
    rw [selectedParisiState_dirac_eq β h q hβ hq ω hq]
  have hsech : (fun ω => sech (selectedParisiStateReal β h hβ.ne'
      (diracOverlap q hq) ω q) ^ 4) =
      fun ω => sech (canonicalDiracStateReal β h q hq ω q) ^ 4 := by
    funext ω
    rw [selectedParisiState_dirac_eq β h q hβ hq ω hq]
  rw [htan, hsech]
  exact condVar_canonicalDirac_tanh_before β h q hq ht

/-- The exact displayed total conditional-variance decomposition. The moment
is the actual selected PDE gradient evaluated along its actual strong state. -/
theorem selectedParisiDirac_variance_decomposition (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) q) :
    q - selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t =
      ∫ ω, (Var[(fun ω => Real.tanh (selectedParisiStateReal β h hβ.ne'
        (diracOverlap q hq) ω q));
        canonicalBrownianMeasure | canonicalBrownianFiltration t.toNNReal]) ω
          ∂canonicalBrownianMeasure := by
  let f : BrownianSample → ℝ := fun ω => Real.tanh
    (selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q)
  have he : f = fun ω => Real.tanh (canonicalDiracStateReal β h q hq ω q) := by
    funext ω
    dsimp only [f]
    rw [selectedParisiState_dirac_eq β h q hβ hq ω hq]
  have hf : MemLp f 2 canonicalBrownianMeasure := by
    rw [he]
    exact memLp_canonicalDirac_tanh_interface β h q hq
  have hCE := condExp_selectedParisiDirac_gradient_before β h q hβ hq ht
  have hv := condVar_ae_eq_condExp_sq_sub_sq_condExp (canonicalBrownianFiltration.le t.toNNReal) hf
  have hE : (∫ ω, f ω ^ 2 ∂canonicalBrownianMeasure) = q := by
    rw [he]
    change physicalHardSecondMoment β h q hq q = q
    rw [physicalHardSecondMoment_eq β h q hq ⟨le_rfl, hq.2⟩]
    exact hardSecondMoment_initial_fixed hq.1 hfixed
  have hEf : (∫ ω, canonicalBrownianMeasure[f | canonicalBrownianFiltration t.toNNReal] ω ^ 2
      ∂canonicalBrownianMeasure) = selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t := by
    apply integral_congr_ae
    filter_upwards [hCE] with ω hω
    exact congrArg (fun x : ℝ => x ^ 2) hω
  symm
  change (∫ ω, (Var[f; canonicalBrownianMeasure | canonicalBrownianFiltration t.toNNReal]) ω
    ∂canonicalBrownianMeasure) = _
  rw [integral_congr_ae hv]
  change (∫ ω, canonicalBrownianMeasure[(fun ω => f ω ^ 2) |
    canonicalBrownianFiltration t.toNNReal] ω -
    canonicalBrownianMeasure[f | canonicalBrownianFiltration t.toNNReal] ω ^ 2
      ∂canonicalBrownianMeasure) = _
  rw [integral_sub integrable_condExp
    (hf.condExp (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_sq,
    integral_condExp (canonicalBrownianFiltration.le t.toNNReal), hE, hEf]

end Paper
