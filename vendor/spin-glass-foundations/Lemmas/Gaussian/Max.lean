module

public import Lemmas.SpinGlass.gaussian_concentration
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

/-- The pointwise maximum of a nonempty finite family of centered functions. -/
noncomputable def centeredGaussianMax
    {ι I : Type*} [Fintype ι] [Fintype I]
    (hI : (Finset.univ : Finset I).Nonempty)
    (F : I → EuclideanSpace ℝ ι → ℝ) :
    EuclideanSpace ℝ ι → ℝ :=
  fun x ↦ Finset.univ.sup' hI fun v ↦
    F v x - ∫ y, F v y ∂SYK.standardGaussianMeasureOnEuclidean ι

private theorem integrable_lipschitz_standardGaussian
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hL : 0 < L) (hLip : LipschitzWith L.toNNReal F) :
    Integrable F (SYK.standardGaussianMeasureOnEuclidean ι) := by
  let μ := SYK.standardGaussianMeasureOnEuclidean ι
  have habs : Integrable (fun x ↦ |F x|) μ := by
    simpa using
      integrable_pow_abs_of_integrable_exp_mul
        (μ := μ) (X := F) (t := (1 : ℝ)) one_ne_zero
        (SYK.integrable_exp_smul_lipschitz F L hL hLip 1)
        (by simpa using
          (SYK.integrable_exp_smul_lipschitz F L hL hLip (-1))) 1
  exact (integrable_norm_iff hLip.continuous.aestronglyMeasurable).mp (by
    simpa [Real.norm_eq_abs] using habs)

private theorem gaussian_max_exponential_bound
    {ι I : Type*} [Fintype ι] [Fintype I]
    (F : I → EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L)
    (hLip : ∀ v, LipschitzWith L.toNNReal (F v))
    (hI : (Finset.univ : Finset I).Nonempty) :
    Real.exp (t * ∫ x, centeredGaussianMax hI F x
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      (Fintype.card I : ℝ) * Real.exp (L ^ 2 * t ^ 2 / 2) := by
  let μ := SYK.standardGaussianMeasureOnEuclidean ι
  let X : I → EuclideanSpace ℝ ι → ℝ := fun v x ↦ F v x - ∫ y, F v y ∂μ
  let M : EuclideanSpace ℝ ι → ℝ :=
    fun x ↦ Finset.univ.sup' hI fun v ↦ X v x
  have hsg (v : I) :
      HasSubgaussianMGF (X v) (Real.toNNReal (L ^ 2)) μ := by
    simpa [X, μ] using
      SYK.product_standardGaussian_hasSubgaussianMGF (F v) L hL (hLip v)
  have hXint (v : I) : Integrable (X v) μ := by
    have habs : Integrable (fun x ↦ |X v x|) μ := by
      simpa using
        integrable_pow_abs_of_integrable_exp_mul
          (μ := μ) (X := X v) (t := (1 : ℝ)) one_ne_zero
          ((hsg v).integrable_exp_mul 1)
          (by simpa using ((hsg v).integrable_exp_mul (-1))) 1
    exact (integrable_norm_iff (hsg v).aestronglyMeasurable).mp (by
      simpa [Real.norm_eq_abs] using habs)
  have hMint : Integrable M μ := by
    have hfun : Integrable (Finset.univ.sup' hI fun v ↦ X v) μ := by
      exact Finset.sup'_induction (s := Finset.univ) (H := hI)
        (f := fun v ↦ X v) (p := fun f ↦ Integrable f μ)
        (fun _ hf _ hg ↦ hf.sup hg)
        (fun v _ ↦ hXint v)
    refine hfun.congr ?_
    filter_upwards [] with x
    exact Finset.sup'_apply hI (fun v ↦ X v) x
  have hsumint :
      Integrable (fun x ↦ ∑ v : I, Real.exp (t * X v x)) μ := by
    exact integrable_finsetSum Finset.univ fun v _ ↦
      (hsg v).integrable_exp_mul t
  have hpoint (x : EuclideanSpace ℝ ι) :
      Real.exp (t * M x) ≤ ∑ v : I, Real.exp (t * X v x) := by
    obtain ⟨v, hv, hmax⟩ :=
      Finset.exists_mem_eq_sup' hI (fun v ↦ X v x)
    change Real.exp (t * (Finset.univ.sup' hI fun v ↦ X v x)) ≤ _
    rw [hmax]
    exact Finset.single_le_sum
      (fun w _ ↦ (Real.exp_nonneg (t * X w x))) hv
  have hexpMint : Integrable (fun x ↦ Real.exp (t * M x)) μ := by
    refine hsumint.mono'
      ((hMint.const_mul t).aemeasurable.exp.aestronglyMeasurable) ?_
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.exp_nonneg _)] using hpoint x
  have hJensen :
      Real.exp (t * ∫ x, M x ∂μ) ≤ ∫ x, Real.exp (t * M x) ∂μ := by
    rw [← integral_const_mul]
    exact convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) (hMint.const_mul t) hexpMint
  have hmgf :
      (∫ x, Real.exp (t * M x) ∂μ) ≤
        (Fintype.card I : ℝ) * Real.exp (L ^ 2 * t ^ 2 / 2) := by
    calc
      (∫ x, Real.exp (t * M x) ∂μ)
          ≤ ∫ x, ∑ v : I, Real.exp (t * X v x) ∂μ :=
        integral_mono hexpMint hsumint hpoint
      _ = ∑ v : I, ∫ x, Real.exp (t * X v x) ∂μ := by
        exact integral_finsetSum Finset.univ fun v _ ↦
          (hsg v).integrable_exp_mul t
      _ ≤ ∑ _v : I, Real.exp (L ^ 2 * t ^ 2 / 2) := by
        exact Finset.sum_le_sum fun v _ ↦ by
          have hv := (hsg v).mgf_le t
          rw [Real.coe_toNNReal _ (sq_nonneg L)] at hv
          simpa [mgf] using hv
      _ = (Fintype.card I : ℝ) * Real.exp (L ^ 2 * t ^ 2 / 2) := by
        simp
  simpa [centeredGaussianMax, M, X, μ] using hJensen.trans hmgf

private theorem gaussian_max_log_bound
    {ι I : Type*} [Fintype ι] [Fintype I]
    (F : I → EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L)
    (hLip : ∀ v, LipschitzWith L.toNNReal (F v))
    (hI : (Finset.univ : Finset I).Nonempty) :
    t * ∫ x, centeredGaussianMax hI F x
        ∂SYK.standardGaussianMeasureOnEuclidean ι ≤
      Real.log (Fintype.card I : ℝ) + L ^ 2 * t ^ 2 / 2 := by
  have hcard : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hI
  have h := gaussian_max_exponential_bound F L t hL hLip hI
  have hlog := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul hcard.ne' (Real.exp_pos _).ne',
    Real.log_exp] at hlog
  exact hlog

/-- Expected maximum estimate for a finite family of centered Lipschitz
functions of a standard Gaussian vector. -/
theorem gaussian_max_estimate_of_two_le_card
    {ι I : Type*} [Fintype ι] [Fintype I]
    (F : I → EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hL : 0 < L) (hcard : 2 ≤ Fintype.card I)
    (hLip : ∀ v, LipschitzWith L.toNNReal (F v)) :
    (∫ x, centeredGaussianMax
          (show (Finset.univ : Finset I).Nonempty by
            exact Finset.card_pos.mp (by simpa using lt_of_lt_of_le Nat.zero_lt_two hcard))
          F x ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      L * Real.sqrt (2 * Real.log (Fintype.card I : ℝ)) := by
  let hI : (Finset.univ : Finset I).Nonempty :=
    Finset.card_pos.mp (by simpa using lt_of_lt_of_le Nat.zero_lt_two hcard)
  let a := Real.log (Fintype.card I : ℝ)
  let r := Real.sqrt (2 * a)
  let t := r / L
  have hcardR : (1 : ℝ) < Fintype.card I := by exact_mod_cast hcard
  have ha : 0 < a := Real.log_pos hcardR
  have harg : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha.le
  have hr : 0 < r := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have ht : 0 < t := div_pos hr hL
  have hlog := gaussian_max_log_bound F L t hL hLip hI
  refine le_of_mul_le_mul_left (a := t) ?_ ht
  calc
    t * ∫ x, centeredGaussianMax hI F x
          ∂SYK.standardGaussianMeasureOnEuclidean ι
        ≤ a + L ^ 2 * t ^ 2 / 2 := by simpa [a] using hlog
    _ = t * (L * r) := by
      dsimp [t, r]
      have hrsq : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt harg
      field_simp [hL.ne']
      ring_nf at hrsq ⊢
      nlinarith [hrsq]
    _ = t * (L * Real.sqrt (2 * Real.log (Fintype.card I : ℝ))) := by
      rfl

/-- Expected maximum estimate for every nonempty finite family, including the
singleton-family and zero-Lipschitz cases. -/
theorem gaussian_max_estimate
    {ι I : Type*} [Fintype ι] [Fintype I] [Nonempty I]
    (F : I → EuclideanSpace ℝ ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ v, LipschitzWith L.toNNReal (F v)) :
    (∫ x, centeredGaussianMax Finset.univ_nonempty F x
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      L * Real.sqrt (2 * Real.log (Fintype.card I : ℝ)) := by
  by_cases hLzero : L = 0
  · subst L
    have hconst (v : I) (x : EuclideanSpace ℝ ι) : F v x = F v 0 := by
      have hdist := (hLip v).dist_le_mul x 0
      have hz : dist (F v x) (F v 0) = 0 := by
        apply le_antisymm
        · simpa using hdist
        · exact dist_nonneg
      exact dist_eq_zero.mp hz
    have hint (v : I) :
        (∫ x, F v x ∂SYK.standardGaussianMeasureOnEuclidean ι) = F v 0 := by
      simp_rw [hconst v]
      simp
    have hmax (x : EuclideanSpace ℝ ι) :
        centeredGaussianMax Finset.univ_nonempty F x = 0 := by
      apply Finset.sup'_eq_of_forall
      intro v _
      simp [hconst v x, hint v]
    simp_rw [hmax]
    simp
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
    by_cases hcard : Fintype.card I = 1
    · obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
      have huniv : (Finset.univ : Finset I) = {i} := by
        ext v
        simp [hi v]
      have hmax (x : EuclideanSpace ℝ ι) :
          centeredGaussianMax Finset.univ_nonempty F x =
            F i x - ∫ y, F i y
              ∂SYK.standardGaussianMeasureOnEuclidean ι := by
        simp [centeredGaussianMax, huniv]
      have hFint :=
        integrable_lipschitz_standardGaussian (F i) L hLpos (hLip i)
      simp_rw [hmax]
      rw [integral_sub hFint (integrable_const _)]
      simp [hcard]
    · have hcardpos : 0 < Fintype.card I := Fintype.card_pos
      have hcardtwo : 2 ≤ Fintype.card I := by omega
      simpa using
        gaussian_max_estimate_of_two_le_card F L hLpos hcardtwo hLip

end SpinGlass.AT
