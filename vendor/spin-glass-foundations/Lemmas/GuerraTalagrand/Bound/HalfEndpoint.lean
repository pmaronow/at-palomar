module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
public import Lemmas.GuerraTalagrand.Bound.Endpoint
public import Lemmas.GuerraTalagrand.Bound.HalfCalculus

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

noncomputable def gtHalfBaseTransform
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) : ℝ :=
  2 * Real.log (gtHalfBaseDenominator V L H)

lemma hasFDerivAt_gtHalfBaseTransform
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    HasFDerivAt (gtHalfBaseTransform V L)
      (fderiv ℝ (gtHalfBaseTransform V L) H) H := by
  have hd := hasFDerivAt_gtHalfBaseDenominator V L H
  have hc := (hd.log (gtHalfBaseDenominator_pos V L H).ne').const_mul 2
  change HasFDerivAt (fun H => 2 * Real.log (gtHalfBaseDenominator V L H))
    (fderiv ℝ (fun H => 2 * Real.log (gtHalfBaseDenominator V L H)) H) H
  exact hc.differentiableAt.hasFDerivAt

lemma fderiv_gtHalfBaseTransform_apply
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H K : GTStateSpace S) :
    fderiv ℝ (gtHalfBaseTransform V L) H K =
      ∑ ξ : S, gtHalfBaseWeight V L H ξ * K ξ := by
  let D := gtHalfBaseDenominator V L H
  have hD : D ≠ 0 := (gtHalfBaseDenominator_pos V L H).ne'
  have hd := hasFDerivAt_gtHalfBaseDenominator V L H
  have heq := congrArg (fun T : GTStateSpace S →L[ℝ] ℝ => T K) hd.fderiv
  rw [gtHalfBaseDenominator_fderiv_apply] at heq
  have ht := hasFDerivAt_gtHalfBaseTransform V L H
  have hu := ht.unique ((hd.log hD).const_mul 2)
  rw [hu]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← hd.fderiv, heq]
  unfold gtHalfBaseWeight
  field_simp [hD]
  rw [Finset.sum_div]

lemma norm_fderiv_gtHalfBaseTransform_le_one
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    ‖fderiv ℝ (gtHalfBaseTransform V L) H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro K
  rw [Real.norm_eq_abs, fderiv_gtHalfBaseTransform_apply]
  calc
    |∑ ξ : S, gtHalfBaseWeight V L H ξ * K ξ| ≤
        ∑ ξ : S, |gtHalfBaseWeight V L H ξ * K ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ξ : S, gtHalfBaseWeight V L H ξ * |K ξ| := by
      apply Finset.sum_congr rfl
      intro ξ _
      rw [abs_mul, abs_of_nonneg (gtHalfBaseWeight_nonneg V L H ξ)]
    _ ≤ ∑ ξ : S, gtHalfBaseWeight V L H ξ * ‖K‖ := by
      apply Finset.sum_le_sum
      intro ξ _
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K ξ)
        (gtHalfBaseWeight_nonneg V L H ξ)
    _ = ‖K‖ := by rw [← Finset.sum_mul, sum_gtHalfBaseWeight, one_mul]
    _ = 1 * ‖K‖ := by ring

lemma lipschitzWith_gtHalfBaseTransform
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) :
    LipschitzWith 1 (gtHalfBaseTransform V L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro H
    exact (hasFDerivAt_gtHalfBaseTransform V L H).differentiableAt
  · intro H
    rw [← NNReal.coe_le_coe]
    simpa using norm_fderiv_gtHalfBaseTransform_le_one V L H

lemma gtHalfTransform_eq_base
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) :
    gtHalfTransform V A B₀ B₁ H₀ t z₀ =
      gtHalfBaseTransform V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z₀ + H₀) := by
  unfold gtHalfTransform gtHalfBaseTransform
  rw [gtHalfDenominator_eq_base]

lemma integrable_gtHalfTransform
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S) (t : ℝ) :
    Integrable (fun z₀ : I₀ → ℝ =>
      gtHalfTransform V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀))
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
  let L := gtHalfInnerCLM B₁ t
  let M := gtHalfOuterCLM A B₀ t
  let C : ℝ := |gtHalfBaseTransform V L 0| + ‖H₀‖
  let bound : (I₀ → ℝ) → ℝ := fun z₀ =>
    C + ‖M‖ * ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ I₀)‖
  have hbound : Integrable bound
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) :=
    (integrable_const C).add
      ((integrable_norm_gaussianProduct (I := I₀)).const_mul ‖M‖)
  apply hbound.mono'
  · have hc : Continuous (fun z₀ : I₀ → ℝ =>
        gtHalfBaseTransform V L (M (WithLp.toLp 2 z₀) + H₀)) :=
      (lipschitzWith_gtHalfBaseTransform V L).continuous.comp (by fun_prop)
    apply hc.aestronglyMeasurable.congr
    filter_upwards with z₀
    simpa [L, M] using
      (gtHalfTransform_eq_base V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)).symm
  · filter_upwards with z₀
    let zE : EuclideanSpace ℝ I₀ := WithLp.toLp 2 z₀
    rw [Real.norm_eq_abs, gtHalfTransform_eq_base]
    change |gtHalfBaseTransform V L (M zE + H₀)| ≤ bound z₀
    have hlip := (lipschitzWith_gtHalfBaseTransform V L).norm_sub_le (M zE + H₀) 0
    have hM := M.le_opNorm zE
    have htri := norm_add_le (M zE) H₀
    dsimp [bound, C]
    have habs := abs_sub_abs_le_abs_sub
      (gtHalfBaseTransform V L (M zE + H₀)) (gtHalfBaseTransform V L 0)
    rw [show ‖gtHalfBaseTransform V L (M zE + H₀) - gtHalfBaseTransform V L 0‖ =
      |gtHalfBaseTransform V L (M zE + H₀) - gtHalfBaseTransform V L 0| by rfl] at hlip
    norm_num at hlip
    nlinarith

/-- Trial coordinates below `q` in the branch `q ≤ |v|`. -/
noncomputable def gtHalfOuterTrialCoefficient
    (N : ℕ) (β q s v : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (GTOrdinaryIndex N) :=
  let sign := gtPathSign v
  let e := β * Real.sqrt ((1 - s) * q)
  let a := gtIncrementScale β s 0 q
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (i, j)) =>
        if j = 0 then
          e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)
        else if j = 1 then
          a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)
        else 0

/-- The rank-one trial increment from `q` to `|v|`. -/
noncomputable def gtHalfInnerTrialCoefficient
    (N : ℕ) (β q s v : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (Fin N) :=
  let b := gtIncrementScale β s q |v|
  WithLp.toLp 2 fun i =>
    b * (SpinGlass.spin N p.1 i +
      gtPathSign v * SpinGlass.spin N p.2 i)

lemma gtHalfOuter_coefficients_orthogonal
    (N : ℕ) (β q s v : ℝ)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
      (gtHalfOuterTrialCoefficient N β q s v r) = 0 := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp [gtOrdinaryBarePhysicalCoefficient, gtHalfOuterTrialCoefficient,
    RCLike.inner_apply]

lemma gtHalfOuterTrialCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
      (gtHalfOuterTrialCoefficient N β q s v r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceMatrix β q s v q a b * pairOverlapMatrix p r a b := by
  classical
  let sign : ℝ := gtPathSign v
  let e : ℝ := β * Real.sqrt ((1 - s) * q)
  let a : ℝ := gtIncrementScale β s 0 q
  have he : e ^ 2 = β ^ 2 * (1 - s) * q := by
    dsimp [e]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hs.2) hq0)]
    ring
  have ha : a ^ 2 = β ^ 2 * s * q := by
    simpa using gtIncrementScale_sq (β := β) (s := s)
      (lower := 0) (upper := q) hs.1 hq0
  have hsignsq : sign ^ 2 = 1 := by
    simpa [sign] using gtPathSign_sq v
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [gtHalfOuterTrialCoefficient, RCLike.inner_apply, conj_trivial,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  simp only [show (0 : Fin 4) = 0 by rfl, if_true,
    show (1 : Fin 4) ≠ 0 by decide, if_false,
    show (1 : Fin 4) = 1 by rfl,
    show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide]
  simp only [zero_mul, add_zero]
  change (∑ i : Fin N, (
      e * (SpinGlass.spin N r.1 i + SpinGlass.spin N r.2 i) *
          (e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)) +
        a * (SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
          (a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)))) = _
  rw [show (∑ i : Fin N, (
      e * (SpinGlass.spin N r.1 i + SpinGlass.spin N r.2 i) *
          (e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)) +
        a * (SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
          (a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)))) =
      e ^ 2 * ((∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
        (∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.2 i) +
        (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.1 i) +
        (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) +
      a ^ 2 * ((∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
        sign * (∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.2 i) +
        sign * (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.1 i) +
        sign ^ 2 * (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) by
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [he, ha, hsignsq]
  simp_rw [spin_sum_eq_mul_overlap hN]
  simp only [pairOverlapMatrix, pairConfig, Fin.sum_univ_two]
  unfold gtCovarianceMatrix signedMatrixPath
  simp only [min_eq_left hqr, Matrix.add_apply, Matrix.smul_apply]
  simp [sign]
  ring

lemma gtHalfInnerTrialCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs0 : 0 ≤ s) (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
      (gtHalfInnerTrialCoefficient N β q s v r) =
      (N : ℝ) * (s * β ^ 2) * ∑ a : Fin 2, ∑ b : Fin 2,
        (signedMatrixPath v |v| a b - signedMatrixPath v q a b) *
          pairOverlapMatrix p r a b := by
  classical
  let sign : ℝ := gtPathSign v
  let b : ℝ := gtIncrementScale β s q |v|
  have hb : b ^ 2 = β ^ 2 * s * (|v| - q) := by
    simpa [b] using gtIncrementScale_sq (β := β) (s := s)
      (lower := q) (upper := |v|) hs0 hqr
  have hsignsq : sign ^ 2 = 1 := by
    simpa [sign] using gtPathSign_sq v
  rw [PiLp.inner_apply]
  simp only [gtHalfInnerTrialCoefficient, RCLike.inner_apply, conj_trivial]
  change (∑ i : Fin N,
      b * (SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
        (b * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i))) = _
  rw [show (∑ i : Fin N,
      b * (SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
        (b * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i))) =
      b ^ 2 * ((∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
        sign * (∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N r.2 i) +
        sign * (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.1 i) +
        sign ^ 2 * (∑ i, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) by
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [hb, hsignsq]
  simp_rw [spin_sum_eq_mul_overlap hN]
  simp only [pairOverlapMatrix, pairConfig, Fin.sum_univ_two]
  unfold signedMatrixPath
  simp only [min_eq_left (abs_nonneg v), min_eq_left hqr,
    gtPathSign_mul_abs]
  simp [sign]
  ring

lemma gtHalfTotalTrialCovariance
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
        (gtHalfOuterTrialCoefficient N β q s v r) +
      inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
        (gtHalfInnerTrialCoefficient N β q s v r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceMatrix β q s v |v| a b * pairOverlapMatrix p r a b := by
  rw [gtHalfOuterTrialCoefficient_inner hN hs hq0 hqr,
    gtHalfInnerTrialCoefficient_inner hN hs.1 hqr]
  unfold gtCovarianceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Square completion at the lower breakpoint `q`. -/
lemma gtHalfOuter_covariance_square_completion
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
        (gtOrdinaryBarePhysicalCoefficient N β q s r) +
      (N : ℝ) * gtScalarVariance β s v q -
      inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
        (gtHalfOuterTrialCoefficient N β q s v r) =
      (N : ℝ) * (s * β ^ 2 / 2) *
        ∑ a : Fin 2, ∑ b : Fin 2,
          (pairOverlapMatrix p r a b - signedMatrixPath v q a b) ^ 2 := by
  rw [gtOrdinaryBarePhysicalCoefficient_inner hN hs hq0,
    gtHalfOuterTrialCoefficient_inner hN hs hq0 hqr,
    gtScalarVariance_eq_matrix_sum hq0]
  unfold gtCovarianceFunction gtCovarianceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
  norm_num
  ring

/-- Square completion at the signed breakpoint `|v|`. -/
lemma gtHalfTotal_covariance_square_completion
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
        (gtOrdinaryBarePhysicalCoefficient N β q s r) +
      (N : ℝ) * gtScalarVariance β s v |v| -
      (inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
          (gtHalfOuterTrialCoefficient N β q s v r) +
        inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
          (gtHalfInnerTrialCoefficient N β q s v r)) =
      (N : ℝ) * (s * β ^ 2 / 2) *
        ∑ a : Fin 2, ∑ b : Fin 2,
          (pairOverlapMatrix p r a b - signedMatrixPath v |v| a b) ^ 2 := by
  rw [gtOrdinaryBarePhysicalCoefficient_inner hN hs hq0,
    gtHalfTotalTrialCovariance hN hs hq0 hqr,
    gtScalarVariance_eq_matrix_sum (abs_nonneg v)]
  unfold gtCovarianceFunction gtCovarianceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
  norm_num
  ring

lemma gtHalfUpperGap_self
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|) (hv : v ∈ attainableOverlaps N)
    (p : ConstrainedPair N v) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p.1)
        (gtOrdinaryBarePhysicalCoefficient N β q s p.1) +
      (N : ℝ) * gtScalarVariance β s v |v| -
      (inner ℝ (gtHalfOuterTrialCoefficient N β q s v p.1)
          (gtHalfOuterTrialCoefficient N β q s v p.1) +
        inner ℝ (gtHalfInnerTrialCoefficient N β q s v p.1)
          (gtHalfInnerTrialCoefficient N β q s v p.1)) =
      (N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2) := by
  rw [gtHalfTotal_covariance_square_completion hN hs hq0 hqr]
  rw [pairOverlapMatrix_self_eq_signedMatrixPath_one hN hv p]
  have hv1 : |v| ≤ 1 := abs_le.2 (gtAttainableOverlap_mem_Icc hN hv)
  have hmatrix :
      (∑ a : Fin 2, ∑ b : Fin 2,
        (signedMatrixPath v 1 a b - signedMatrixPath v |v| a b) ^ 2) =
        2 * (1 - |v|) ^ 2 := by
    unfold signedMatrixPath
    simp [Fin.sum_univ_two, min_eq_right hv1, min_eq_left hv1,
      gtPathSign_mul_abs]
    ring
  rw [hmatrix]
  ring

/-- Specialized pointwise derivative bound in the branch `q ≤ |v|`. -/
lemma gtConstrainedHalfDerivativeExpression_le
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hqr : q ≤ |v|) (hv : v ∈ attainableOverlaps N)
    (t : ℝ) (z₀ : EuclideanSpace ℝ (GTOrdinaryIndex N)) :
    letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
    gtHalfDerivativeExpression
        (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
        (fun p : ConstrainedPair N v =>
          gtOrdinaryBarePhysicalCoefficient N β q s p.1)
        (fun p : ConstrainedPair N v =>
          gtHalfOuterTrialCoefficient N β q s v p.1)
        (fun p : ConstrainedPair N v =>
          gtHalfInnerTrialCoefficient N β q s v p.1)
        0 t z₀ ≤
      ((N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2)) / 2 +
        ((N : ℝ) * gtScalarVariance β s v q -
          (N : ℝ) * gtScalarVariance β s v |v|) / 4 := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  let lowerGap : ConstrainedPair N v → ConstrainedPair N v → ℝ :=
    fun p r => (N : ℝ) * (s * β ^ 2 / 2) *
      ∑ a : Fin 2, ∑ b : Fin 2,
        (pairOverlapMatrix p.1 r.1 a b - signedMatrixPath v q a b) ^ 2
  let upperGap : ConstrainedPair N v → ConstrainedPair N v → ℝ :=
    fun p r => (N : ℝ) * (s * β ^ 2 / 2) *
      ∑ a : Fin 2, ∑ b : Fin 2,
        (pairOverlapMatrix p.1 r.1 a b - signedMatrixPath v |v| a b) ^ 2
  apply gtHalfDerivativeExpression_le
    (shiftQ := (N : ℝ) * gtScalarVariance β s v q)
    (shiftR := (N : ℝ) * gtScalarVariance β s v |v|)
    (diagGap := (N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2))
    (lowerGap := lowerGap) (upperGap := upperGap)
  · intro p r
    exact gtHalfOuter_covariance_square_completion hN hs hq0 hqr p.1 r.1
  · intro p r
    dsimp [upperGap]
    have h := gtHalfTotal_covariance_square_completion (N := N) (β := β)
      hN hs hq0 hqr p.1 r.1
    convert h using 1 <;> ring
  · intro p
    dsimp [upperGap]
    rw [pairOverlapMatrix_self_eq_signedMatrixPath_one hN hv p]
    have hv1 : |v| ≤ 1 := abs_le.2 (gtAttainableOverlap_mem_Icc hN hv)
    unfold signedMatrixPath
    simp [Fin.sum_univ_two, min_eq_right hv1, min_eq_left hv1,
      gtPathSign_mul_abs]
    ring
  · intro p r
    dsimp [lowerGap]
    apply mul_nonneg
    · exact mul_nonneg (by positivity)
        (div_nonneg (mul_nonneg hs.1 (sq_nonneg β)) (by norm_num))
    · positivity
  · intro p r
    dsimp [upperGap]
    apply mul_nonneg
    · exact mul_nonneg (by positivity)
        (div_nonneg (mul_nonneg hs.1 (sq_nonneg β)) (by norm_num))
    · positivity

lemma gtHalfTransform_one_eq_stateLogPartition
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (z₀ : EuclideanSpace ℝ I₀) :
    gtHalfTransform V A B₀ B₁ H₀ 1 z₀ =
      gtStateLogPartition V (gtCoefficientCLM A z₀ + H₀) := by
  unfold gtHalfTransform gtHalfDenominator gtHalfField
  simp only [sub_self, Real.sqrt_zero, zero_smul, add_zero, Real.sqrt_one,
    one_smul, zero_add, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul, Real.log_exp]
  ring

noncomputable def gtConstrainedHalfPressure
    (N : ℕ) (β h q s v lam : ℝ) (hv : v ∈ attainableOverlaps N)
    (t : ℝ) : ℝ := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  exact gtHalfPressure
    (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
    (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p.1)
    (fun p => gtHalfOuterTrialCoefficient N β q s v p.1)
    (fun p => gtHalfInnerTrialCoefficient N β q s v p.1) 0 t

noncomputable def gtUnconstrainedHalfPressure
    (N : ℕ) (β h q s v lam t : ℝ) : ℝ :=
  gtHalfPressure
    (fun p : SpinGlass.Config N × SpinGlass.Config N => gtPairPotential N h lam v p)
    (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
    (fun p => gtHalfOuterTrialCoefficient N β q s v p)
    (fun p => gtHalfInnerTrialCoefficient N β q s v p) 0 t

lemma gtConstrainedHalfPressure_one_eq_canonical
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    gtConstrainedHalfPressure N β h q s v lam hv 1 =
      ∫ x, coupledConstrainedLogPartition N β h q s v x
        ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  have heq : gtConstrainedHalfPressure N β h q s v lam hv 1 =
      gtConstrainedOrdinaryPressure N β h q s v lam hv 1 := by
    unfold gtConstrainedHalfPressure gtConstrainedOrdinaryPressure
    unfold gtHalfPressure gtOrdinaryPressure
    apply integral_congr_ae
    filter_upwards with z
    rw [gtHalfTransform_one_eq_stateLogPartition]
    congr 2
    simp
  rw [heq, gtOrdinaryPressure_one_eq_canonical hN hs hq hv]

lemma gtConstrainedHalfPressure_zero_le_unconstrained
    {N : ℕ} {β h q s v lam : ℝ} (hv : v ∈ attainableOverlaps N) :
    gtConstrainedHalfPressure N β h q s v lam hv 0 ≤
      gtUnconstrainedHalfPressure N β h q s v lam 0 := by
  classical
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedHalfPressure gtUnconstrainedHalfPressure gtHalfPressure
  apply integral_mono
  · exact (integrable_gtHalfTransform
      (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
      (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p.1)
      (fun p => gtHalfOuterTrialCoefficient N β q s v p.1)
      (fun p => gtHalfInnerTrialCoefficient N β q s v p.1) 0 0)
  · exact (integrable_gtHalfTransform
      (fun p : SpinGlass.Config N × SpinGlass.Config N => gtPairPotential N h lam v p)
      (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
      (fun p => gtHalfOuterTrialCoefficient N β q s v p)
      (fun p => gtHalfInnerTrialCoefficient N β q s v p) 0 0)
  · intro z₀
    unfold gtHalfTransform
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log
    · exact gtHalfDenominator_pos _ _ _ _ _ 0 (WithLp.toLp 2 z₀)
    · unfold gtHalfDenominator
      apply integral_mono
      · exact integrable_gtHalfDenominator_integrand _ _ _ _ _ 0 (WithLp.toLp 2 z₀)
      · exact integrable_gtHalfDenominator_integrand _ _ _ _ _ 0 (WithLp.toLp 2 z₀)
      · intro z₁
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        unfold gtStateLogPartition
        apply Real.log_le_log
        · exact gtStatePartition_pos _ _
        · unfold gtStatePartition
          simp only [gtHalfField, Real.sqrt_zero, zero_smul, sub_zero,
            Real.sqrt_one, one_smul, zero_add, add_zero, PiLp.add_apply,
            gtCoefficientCLM_apply]
          change (∑ x : ConstrainedPair N v,
              Real.exp
                (inner ℝ (gtHalfOuterTrialCoefficient N β q s v x.1)
                    (WithLp.toLp 2 z₀) +
                  inner ℝ (gtHalfInnerTrialCoefficient N β q s v x.1)
                    (WithLp.toLp 2 z₁) + gtPairPotential N h lam v x.1)) ≤
            ∑ p : SpinGlass.Config N × SpinGlass.Config N,
              Real.exp
                (inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
                    (WithLp.toLp 2 z₀) +
                  inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
                    (WithLp.toLp 2 z₁) + gtPairPotential N h lam v p)
          rw [← Finset.sum_subtype
            (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
              SpinGlass.overlap N p.1 p.2 = v)
            (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
              SpinGlass.overlap N p.1 p.2 = v) (by simp)
            (fun p : SpinGlass.Config N × SpinGlass.Config N =>
              Real.exp
                (inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
                    (WithLp.toLp 2 z₀) +
                  inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
                    (WithLp.toLp 2 z₁) + gtPairPotential N h lam v p))]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Real.exp_nonneg _)

noncomputable def gtHalfTrialFieldOne
    (N : ℕ) (β h q s v : ℝ) (z₀ : GTOrdinarySiteIndex N → ℝ)
    (z₁ : Fin N → ℝ) (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z₀ (i, 0) +
    gtIncrementScale β s 0 q * z₀ (i, 1) +
    gtIncrementScale β s q |v| * z₁ i

noncomputable def gtHalfTrialFieldTwo
    (N : ℕ) (β h q s v : ℝ) (z₀ : GTOrdinarySiteIndex N → ℝ)
    (z₁ : Fin N → ℝ) (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z₀ (i, 0) +
    gtPathSign v * gtIncrementScale β s 0 q * z₀ (i, 1) +
    gtPathSign v * gtIncrementScale β s q |v| * z₁ i

lemma gtUnconstrainedHalf_zero_stateLogPartition_eq_terminal_sum
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (z₀ : GTOrdinaryIndex N → ℝ) (z₁ : Fin N → ℝ) :
    gtStateLogPartition
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          gtPairPotential N h lam v p)
        (gtHalfField
          (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
          (fun p => gtHalfOuterTrialCoefficient N β q s v p)
          (fun p => gtHalfInnerTrialCoefficient N β q s v p)
          0 0 (WithLp.toLp 2 z₀) (WithLp.toLp 2 z₁)) =
      2 * (N : ℝ) * Real.log 2 +
        ∑ i : Fin N,
          gtTerminal lam
            (gtHalfTrialFieldOne N β h q s v
              (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i)
            (gtHalfTrialFieldTwo N β h q s v
              (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i) -
        lam * (N : ℝ) * v := by
  classical
  have hpart :
      gtStatePartition
          (fun p : SpinGlass.Config N × SpinGlass.Config N =>
            gtPairPotential N h lam v p)
          (gtHalfField
            (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
            (fun p => gtHalfOuterTrialCoefficient N β q s v p)
            (fun p => gtHalfInnerTrialCoefficient N β q s v p)
            0 0 (WithLp.toLp 2 z₀) (WithLp.toLp 2 z₁)) =
        pairFieldPartition N lam v
          (fun i => gtHalfTrialFieldOne N β h q s v
            (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i)
          (fun i => gtHalfTrialFieldTwo N β h q s v
            (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i) := by
    unfold gtStatePartition pairFieldPartition gtHalfField
    simp only [Real.sqrt_zero, zero_smul, sub_zero, Real.sqrt_one, one_smul,
      zero_add, add_zero, PiLp.add_apply, gtCoefficientCLM_apply]
    apply Finset.sum_congr rfl
    intro p _
    apply congrArg Real.exp
    repeat rw [PiLp.inner_apply]
    simp only [gtHalfOuterTrialCoefficient, gtHalfInnerTrialCoefficient,
      RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, gtPairPotential,
      gtHalfTrialFieldOne, gtHalfTrialFieldTwo]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) = 0 by rfl, if_true,
      show (1 : Fin 4) ≠ 0 by decide, if_false,
      show (1 : Fin 4) = 1 by rfl,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply add_left_cancel (a := lam * (N : ℝ) * v)
    ring_nf
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold gtStateLogPartition
  rw [hpart, log_pairFieldPartition]

lemma gtUnconstrainedHalfTransform_zero_eq_cascade_sum
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (z₀ : GTOrdinaryIndex N → ℝ) :
    gtHalfTransform
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          gtPairPotential N h lam v p)
        (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
        (fun p => gtHalfOuterTrialCoefficient N β q s v p)
        (fun p => gtHalfInnerTrialCoefficient N β q s v p)
        0 0 (WithLp.toLp 2 z₀) =
      2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v +
        ∑ i : Fin N,
          gtRankOneStep (1 / 2) (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtTerminal lam)
            (h + β * Real.sqrt ((1 - s) * q) *
                z₀ (Sum.inr (Sum.inr (i, 0))) +
              gtIncrementScale β s 0 q * z₀ (Sum.inr (Sum.inr (i, 1))))
            (h + β * Real.sqrt ((1 - s) * q) *
                z₀ (Sum.inr (Sum.inr (i, 0))) +
              gtPathSign v * gtIncrementScale β s 0 q *
                z₀ (Sum.inr (Sum.inr (i, 1)))) := by
  classical
  let c₀ : ℝ := 2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v
  let b : ℝ := gtIncrementScale β s q |v|
  let sign : ℝ := gtPathSign v
  let x₁ : Fin N → ℝ := fun i =>
    h + β * Real.sqrt ((1 - s) * q) * z₀ (Sum.inr (Sum.inr (i, 0))) +
      gtIncrementScale β s 0 q * z₀ (Sum.inr (Sum.inr (i, 1)))
  let x₂ : Fin N → ℝ := fun i =>
    h + β * Real.sqrt ((1 - s) * q) * z₀ (Sum.inr (Sum.inr (i, 0))) +
      sign * gtIncrementScale β s 0 q * z₀ (Sum.inr (Sum.inr (i, 1)))
  let F : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbaseD l x
  have hF : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hInt (i : Fin N) : Integrable
      (fun z => gtTerminal lam (x₁ i + b * z) (x₂ i + sign * b * z))
      (gaussianReal 0 1) := by
    simpa [F] using hF.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam b (sign * b) (x₁ i, x₂ i)
  have hExpInt (i : Fin N) : Integrable
      (fun z => Real.exp ((1 / 2 : ℝ) *
        gtTerminal lam (x₁ i + b * z) (x₂ i + sign * b * z)))
      (gaussianReal 0 1) := by
    simpa [F] using GTFrame.integrable_expShift
      (m := (1 / 2 : ℝ)) (GTFrame.expMoments_gaussianReal 0 1)
      hF (by norm_num) () lam b (sign * b) (x₁ i, x₂ i)
  have hPos (_hm : (1 / 2 : ℝ) ≠ 0) (i : Fin N) :
      0 < ∫ z, Real.exp ((1 / 2 : ℝ) *
        gtTerminal lam (x₁ i + b * z) (x₂ i + sign * b * z))
        ∂gaussianReal 0 1 := by
    simpa [F] using GTFrame.integral_expShift_pos
      (m := (1 / 2 : ℝ)) (GTFrame.expMoments_gaussianReal 0 1)
      hF (by norm_num) () lam b (sign * b) (x₁ i, x₂ i)
  have hsum := gtVectorRankStep_sum (N := N) (1 / 2 : ℝ) b sign
    (fun _ => gtTerminal lam) x₁ x₂ hInt hPos
  have hprod :
      (∫ z : Fin N → ℝ,
          Real.exp ((1 / 2 : ℝ) * ∑ i : Fin N,
            gtTerminal lam (x₁ i + b * z i) (x₂ i + sign * b * z i))
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
        ∏ i : Fin N, ∫ z : ℝ,
          Real.exp ((1 / 2 : ℝ) *
            gtTerminal lam (x₁ i + b * z) (x₂ i + sign * b * z))
          ∂gaussianReal 0 1 := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    exact MeasureTheory.integral_fintype_prod_eq_prod (fun i z =>
      Real.exp ((1 / 2 : ℝ) *
        gtTerminal lam (x₁ i + b * z) (x₂ i + sign * b * z)))
  have hvecpos : 0 < ∫ z : Fin N → ℝ,
      Real.exp ((1 / 2 : ℝ) * ∑ i : Fin N,
        gtTerminal lam (x₁ i + b * z i) (x₂ i + sign * b * z i))
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    rw [hprod]
    exact Finset.prod_pos fun i _ => hPos (by norm_num) i
  unfold gtHalfTransform gtHalfDenominator
  simp_rw [gtUnconstrainedHalf_zero_stateLogPartition_eq_terminal_sum hN]
  have hpoint (z₁ : Fin N → ℝ) :
      2 * (N : ℝ) * Real.log 2 +
          ∑ i : Fin N,
            gtTerminal lam
              (gtHalfTrialFieldOne N β h q s v
                (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i)
              (gtHalfTrialFieldTwo N β h q s v
                (fun ij => z₀ (Sum.inr (Sum.inr ij))) z₁ i) -
          lam * (N : ℝ) * v =
        c₀ + ∑ i : Fin N,
          gtTerminal lam (x₁ i + b * z₁ i) (x₂ i + sign * b * z₁ i) := by
    dsimp [c₀, x₁, x₂, b, sign, gtHalfTrialFieldOne, gtHalfTrialFieldTwo]
    ring
  simp_rw [hpoint]
  have hfactor :
      (∫ z : Fin N → ℝ,
          Real.exp ((1 / 2 : ℝ) *
            (c₀ + ∑ i : Fin N,
              gtTerminal lam (x₁ i + b * z i) (x₂ i + sign * b * z i)))
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
        Real.exp ((1 / 2 : ℝ) * c₀) *
          ∫ z : Fin N → ℝ,
            Real.exp ((1 / 2 : ℝ) * ∑ i : Fin N,
              gtTerminal lam (x₁ i + b * z i) (x₂ i + sign * b * z i))
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    simp_rw [mul_add, Real.exp_add]
    rw [integral_const_mul]
  rw [hfactor, Real.log_mul (Real.exp_ne_zero _) hvecpos.ne', Real.log_exp]
  unfold gtVectorStep at hsum
  simp only [show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false] at hsum
  norm_num at hsum
  unfold SpinGlass.GeneralizedLatala.gaussianProduct at hsum
  dsimp [c₀, x₁, x₂, b, sign] at hsum ⊢
  linarith

lemma goodFam_integrable_affine_gaussianFinTwo
    {P : Type*} [TopologicalSpace P]
    {F D : P → ℝ → ℝ × ℝ → ℝ} (hgood : GTFrame.GoodFam F D)
    (p : P) (l x₁ x₂ : ℝ)
    (c₁ c₂ : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun z : Fin 2 → ℝ =>
      F p l (x₁ + inner ℝ c₁ (WithLp.toLp 2 z),
        x₂ + inner ℝ c₂ (WithLp.toLp 2 z)))
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
  let M : ℝ := |F p l (x₁, x₂)|
  let C : ℝ := ‖c₁‖ + ‖c₂‖
  let bound : (Fin 2 → ℝ) → ℝ := fun z =>
    M + C * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖
  have hb : Integrable bound
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
    simpa [bound] using (integrable_const M).add
      ((integrable_norm_gaussianProduct (I := Fin 2)).const_mul C)
  apply hb.mono'
  · exact (hgood.contF_pt p l).comp (by fun_prop) |>.aestronglyMeasurable
  · filter_upwards with z
    let zE : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 z
    have hlip := hgood.lipx p l
      (x₁ + inner ℝ c₁ zE, x₂ + inner ℝ c₂ zE) (x₁, x₂)
    have hc₁ : |inner ℝ c₁ zE| ≤ ‖c₁‖ * ‖zE‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm c₁ zE
    have hc₂ : |inner ℝ c₂ zE| ≤ ‖c₂‖ * ‖zE‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm c₂ zE
    have habs := abs_sub_abs_le_abs_sub
      (F p l (x₁ + inner ℝ c₁ zE, x₂ + inner ℝ c₂ zE))
      (F p l (x₁, x₂))
    rw [Real.norm_eq_abs]
    dsimp [bound, M, C]
    norm_num at hlip
    dsimp [zE] at hlip hc₁ hc₂ habs ⊢
    nlinarith

noncomputable def gtTwoGaussianTuple (p : ℝ × ℝ) : Fin 2 → ℝ := ![p.1, p.2]

lemma gaussianFinTwo_eq_map_tuple :
    Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) =
      Measure.map gtTwoGaussianTuple
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  apply Measure.pi_eq
  intro sets hsets
  have hm : Measurable gtTwoGaussianTuple := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp [gtTwoGaussianTuple] <;> fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hsets)]
  rw [show gtTwoGaussianTuple ⁻¹' Set.univ.pi sets = sets 0 ×ˢ sets 1 by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_prod]
    constructor
    · intro hp
      exact ⟨by simpa [gtTwoGaussianTuple] using hp 0,
        by simpa [gtTwoGaussianTuple] using hp 1⟩
    · rintro ⟨h₀, h₁⟩ i
      fin_cases i <;> simp [gtTwoGaussianTuple, h₀, h₁]]
  simp [Fin.prod_univ_two]

lemma integral_gaussianFinTwo_eq_iterated
    (f : (Fin 2 → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) :
    (∫ z : Fin 2 → ℝ, f z ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) =
      ∫ z₀, ∫ z₁, f ![z₀, z₁]
        ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hm : Measurable gtTwoGaussianTuple := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp [gtTwoGaussianTuple] <;> fun_prop
  have hfm : Integrable f (Measure.map gtTwoGaussianTuple μ) := by
    rw [← gaussianFinTwo_eq_map_tuple]
    exact hf
  have hc : Integrable (f ∘ gtTwoGaussianTuple) μ := hfm.comp_measurable hm
  have hc' : Integrable (fun p => f (gtTwoGaussianTuple p)) μ := by
    simpa [Function.comp_def] using hc
  rw [gaussianFinTwo_eq_map_tuple]
  rw [integral_map hm.aemeasurable hfm.aestronglyMeasurable]
  rw [integral_prod _ hc']
  apply integral_congr_ae
  filter_upwards [hc'.prod_right_ae] with z₀ hz₀
  rfl

lemma gtUnconstrainedHalfPressure_zero_eq_cascade
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ} :
    gtUnconstrainedHalfPressure N β h q s v lam 0 =
      2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v +
        (N : ℝ) * standardGaussianExpectation (fun z =>
          gtRankOneStep 0 (gtIncrementScale β s 0 q) (gtPathSign v)
            (gtRankOneStep (1 / 2) (gtIncrementScale β s q |v|)
              (gtPathSign v) (gtTerminal lam))
            (h + β * Real.sqrt ((1 - s) * q) * z)
            (h + β * Real.sqrt ((1 - s) * q) * z)) := by
  classical
  let μ := Measure.pi (fun _ : GTOrdinaryIndex N => gaussianReal 0 1)
  let sign : ℝ := gtPathSign v
  let e : ℝ := β * Real.sqrt ((1 - s) * q)
  let a : ℝ := gtIncrementScale β s 0 q
  let b : ℝ := gtIncrementScale β s q |v|
  let innerF : GTTwoField := gtRankOneStep (1 / 2) b sign (gtTerminal lam)
  let cascade : GTTwoField := gtRankOneStep 0 a sign innerF
  let g : (Fin 2 → ℝ) → ℝ := fun z =>
    innerF (h + e * z 0 + a * z 1)
      (h + e * z 0 + sign * a * z 1)
  let F : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbaseD l x
  let bb : Unit → ℝ := fun _ => b
  let sg : Unit → ℝ := fun _ => sign
  have hF : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hMb := GTFrame.stepM_good (m := (1 / 2 : ℝ))
    (GTFrame.expMoments_gaussianReal 0 1) hF (by norm_num)
      (α := bb) (β := fun u => sg u * bb u) (hα := continuous_const)
      (hβ := by dsimp [sg, bb]; fun_prop)
  have hg : Integrable g
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
    let c₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![e, a]
    let c₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![e, sign * a]
    have hi := goodFam_integrable_affine_gaussianFinTwo hMb () lam h h c₁ c₂
    apply hi.congr
    filter_upwards with z
    simp only [g, innerF, GTFrame.stepM, F, bb, sg, gtRankOneStep,
      standardGaussianExpectation, c₁, c₂, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, conj_trivial,
      show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false]
    congr 2
    apply integral_congr_ae
    filter_upwards with w
    congr 2 <;> simp <;> ring
  let f : Fin N → (GTOrdinaryIndex N → ℝ) → ℝ := fun i z =>
    innerF
      (h + e * z (Sum.inr (Sum.inr (i, 0))) +
        a * z (Sum.inr (Sum.inr (i, 1))))
      (h + e * z (Sum.inr (Sum.inr (i, 0))) +
        sign * a * z (Sum.inr (Sum.inr (i, 1))))
  have hf (i : Fin N) : Integrable (f i) μ := by
    let ι : Fin 2 → GTOrdinaryIndex N := fun j =>
      Sum.inr (Sum.inr (i, (⟨j.val, by omega⟩ : Fin 4)))
    have hι : Function.Injective ι := by
      intro j k hjk
      have hjk' := congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hjk))
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) hjk')
    let φ : (GTOrdinaryIndex N → ℝ) → (Fin 2 → ℝ) := fun z j => z (ι j)
    have hmp : MeasurePreserving φ μ
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) := by
      refine ⟨by fun_prop, ?_⟩
      simpa [φ, μ] using gaussianProduct_restrict_map ι hι
    have hc : Integrable (fun z : GTOrdinaryIndex N → ℝ => g (φ z)) μ :=
      (hmp.integrable_comp hg.1).2 hg
    simpa [f, g, φ, ι] using hc
  unfold gtUnconstrainedHalfPressure gtHalfPressure
  simp_rw [gtUnconstrainedHalfTransform_zero_eq_cascade_sum hN]
  have hpoint (z : GTOrdinaryIndex N → ℝ) :
      2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v +
          ∑ i : Fin N,
            gtRankOneStep (1 / 2) (gtIncrementScale β s q |v|) (gtPathSign v)
              (gtTerminal lam)
              (h + β * Real.sqrt ((1 - s) * q) * z (Sum.inr (Sum.inr (i, 0))) +
                gtIncrementScale β s 0 q * z (Sum.inr (Sum.inr (i, 1))))
              (h + β * Real.sqrt ((1 - s) * q) * z (Sum.inr (Sum.inr (i, 0))) +
                gtPathSign v * gtIncrementScale β s 0 q *
                  z (Sum.inr (Sum.inr (i, 1)))) =
        (2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v) + ∑ i, f i z := by
    dsimp [f, innerF, e, a, b, sign]
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => hf i)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul]
  rw [integral_finset_sum Finset.univ (fun i _ => hf i)]
  have hone (i : Fin N) : (∫ z, f i z ∂μ) =
      ∫ z : Fin 2 → ℝ, g z
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) := by
    let ι : Fin 2 → GTOrdinaryIndex N := fun j =>
      Sum.inr (Sum.inr (i, (⟨j.val, by omega⟩ : Fin 4)))
    have hι : Function.Injective ι := by
      intro j k hjk
      have hjk' := congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hjk))
      exact Fin.ext (congrArg (fun x : Fin 4 => x.val) hjk')
    have hr := integral_gaussianProduct_restrict ι hι g hg.1
    simpa [μ, f, g, ι] using hr
  simp_rw [hone]
  have hgC : (∫ z : Fin 2 → ℝ, g z
      ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) =
      standardGaussianExpectation (fun z => cascade (h + e * z) (h + e * z)) := by
    rw [integral_gaussianFinTwo_eq_iterated g hg]
    simp [g, cascade, gtRankOneStep, standardGaussianExpectation]
  rw [hgC]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [cascade, innerF, a, b, e, sign]

/-! ## An ordinary comparison field stopped at `|v|`

The last coordinate below is the increment from `q` to `|v|`.  It is kept
as an ordinary Gaussian during the comparison and converted to mass `1/2`
at the independent endpoint by Jensen's inequality. -/

noncomputable def gtStoppedTrialCoefficient
    (N : ℕ) (β q s v : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (GTOrdinaryIndex N) :=
  let sign := gtPathSign v
  let e := β * Real.sqrt ((1 - s) * q)
  let a := gtIncrementScale β s 0 q
  let b := gtIncrementScale β s q |v|
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (i, j)) =>
        if j = 0 then
          e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)
        else if j = 1 then
          a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)
        else if j = 2 then
          b * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)
        else 0

lemma gtStopped_coefficients_orthogonal
    (N : ℕ) (β q s v : ℝ)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
      (gtStoppedTrialCoefficient N β q s v r) = 0 := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp [gtOrdinaryBarePhysicalCoefficient, gtStoppedTrialCoefficient,
    RCLike.inner_apply]

lemma gtStoppedTrialCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q) (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtStoppedTrialCoefficient N β q s v p)
      (gtStoppedTrialCoefficient N β q s v r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceMatrix β q s v |v| a b * pairOverlapMatrix p r a b := by
  classical
  have hsplit :
      inner ℝ (gtStoppedTrialCoefficient N β q s v p)
          (gtStoppedTrialCoefficient N β q s v r) =
        inner ℝ (gtHalfOuterTrialCoefficient N β q s v p)
            (gtHalfOuterTrialCoefficient N β q s v r) +
          inner ℝ (gtHalfInnerTrialCoefficient N β q s v p)
            (gtHalfInnerTrialCoefficient N β q s v r) := by
    rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
    repeat rw [Fintype.sum_sum_type]
    simp only [gtStoppedTrialCoefficient, gtHalfOuterTrialCoefficient,
      gtHalfInnerTrialCoefficient, RCLike.inner_apply, conj_trivial,
      mul_zero, Finset.sum_const_zero, zero_add]
    repeat rw [Fintype.sum_sum_type]
    repeat rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) = 0 by rfl, if_true,
      show (1 : Fin 4) ≠ 0 by decide, if_false,
      show (1 : Fin 4) = 1 by rfl,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
      show (2 : Fin 4) = 2 by rfl,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit, gtHalfTotalTrialCovariance hN hs hq0 hqr]

lemma gtStopped_covariance_square_completion
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q) (hqr : q ≤ |v|)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
        (gtOrdinaryBarePhysicalCoefficient N β q s r) +
      (N : ℝ) * gtScalarVariance β s v |v| -
      inner ℝ (gtStoppedTrialCoefficient N β q s v p)
        (gtStoppedTrialCoefficient N β q s v r) =
      (N : ℝ) * (s * β ^ 2 / 2) *
        ∑ a : Fin 2, ∑ b : Fin 2,
          (pairOverlapMatrix p r a b - signedMatrixPath v |v| a b) ^ 2 := by
  rw [gtOrdinaryBarePhysicalCoefficient_inner hN hs hq0,
    gtStoppedTrialCoefficient_inner hN hs hq0 hqr,
    gtScalarVariance_eq_matrix_sum (abs_nonneg v)]
  unfold gtCovarianceFunction gtCovarianceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
  norm_num
  ring

lemma gtStoppedUpperGap_self
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q) (hqr : q ≤ |v|)
    (hv : v ∈ attainableOverlaps N) (p : ConstrainedPair N v) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p.1)
        (gtOrdinaryBarePhysicalCoefficient N β q s p.1) +
      (N : ℝ) * gtScalarVariance β s v |v| -
      inner ℝ (gtStoppedTrialCoefficient N β q s v p.1)
        (gtStoppedTrialCoefficient N β q s v p.1) =
      (N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2) := by
  rw [gtStopped_covariance_square_completion hN hs hq0 hqr]
  rw [pairOverlapMatrix_self_eq_signedMatrixPath_one hN hv p]
  have hv1 : |v| ≤ 1 := abs_le.2 (gtAttainableOverlap_mem_Icc hN hv)
  unfold signedMatrixPath
  simp [Fin.sum_univ_two, min_eq_right hv1, gtPathSign_mul_abs]
  ring

noncomputable def gtConstrainedStoppedPressure
    (N : ℕ) (β h q s v lam : ℝ) (hv : v ∈ attainableOverlaps N)
    (t : ℝ) : ℝ := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  exact gtOrdinaryPressure
    (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
    (fun p : ConstrainedPair N v =>
      gtOrdinaryBarePhysicalCoefficient N β q s p.1)
    (fun p : ConstrainedPair N v => gtStoppedTrialCoefficient N β q s v p.1)
    0 t

noncomputable def gtUnconstrainedStoppedPressure
    (N : ℕ) (β h q s v lam t : ℝ) : ℝ :=
  gtOrdinaryPressure
    (fun p : SpinGlass.Config N × SpinGlass.Config N => gtPairPotential N h lam v p)
    (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
    (fun p => gtStoppedTrialCoefficient N β q s v p) 0 t

lemma gtConstrainedStoppedPressure_one_le_zero
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q) (hqr : q ≤ |v|)
    (hv : v ∈ attainableOverlaps N) :
    gtConstrainedStoppedPressure N β h q s v lam hv 1 ≤
      gtConstrainedStoppedPressure N β h q s v lam hv 0 +
        (N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2) / 2 := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedStoppedPressure
  apply gtOrdinaryPressure_one_le_zero_add_shiftedDiagonalGap
    (hAB := fun p r => gtStopped_coefficients_orthogonal N β q s v p.1 r.1)
    (shift := (N : ℝ) * gtScalarVariance β s v |v|)
    (gap := (N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2))
  · intro p
    have hself := gtStoppedUpperGap_self (β := β) hN hs hq0 hqr hv p
    linarith
  · intro p r
    have hsq := gtStopped_covariance_square_completion (β := β)
      hN hs hq0 hqr p.1 r.1
    have hnonneg : 0 ≤ (N : ℝ) * (s * β ^ 2 / 2) *
        ∑ a : Fin 2, ∑ b : Fin 2,
          (pairOverlapMatrix p.1 r.1 a b - signedMatrixPath v |v| a b) ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg N)
          (div_nonneg (mul_nonneg hs.1 (sq_nonneg β)) (by norm_num)))
        (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    linarith

lemma gtConstrainedStoppedPressure_one_eq_canonical
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    gtConstrainedStoppedPressure N β h q s v lam hv 1 =
      ∫ x, coupledConstrainedLogPartition N β h q s v x
        ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  have heq : gtConstrainedStoppedPressure N β h q s v lam hv 1 =
      gtConstrainedOrdinaryPressure N β h q s v lam hv 1 := by
    unfold gtConstrainedStoppedPressure gtConstrainedOrdinaryPressure
    unfold gtOrdinaryPressure
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    unfold gtOrdinaryField
    simp
  rw [heq, gtOrdinaryPressure_one_eq_canonical hN hs hq hv]

lemma gtConstrainedStoppedPressure_zero_le_unconstrained
    {N : ℕ} {β h q s v lam : ℝ} (hv : v ∈ attainableOverlaps N) :
    gtConstrainedStoppedPressure N β h q s v lam hv 0 ≤
      gtUnconstrainedStoppedPressure N β h q s v lam 0 := by
  classical
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedStoppedPressure gtUnconstrainedStoppedPressure
  unfold gtOrdinaryPressure
  apply integral_mono
  · exact integrable_gtStateLogPartition_gtOrdinaryField _ _ _ 0 0
  · exact integrable_gtStateLogPartition_gtOrdinaryField _ _ _ 0 0
  · intro z
    unfold gtStateLogPartition
    apply Real.log_le_log
    · exact gtStatePartition_pos _ _
    · unfold gtStatePartition
      simp only [gtOrdinaryField, Real.sqrt_zero, zero_smul, sub_zero,
        Real.sqrt_one, one_smul, zero_add, add_zero, gtCoefficientCLM_apply]
      rw [← Finset.sum_subtype
        (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
          SpinGlass.overlap N p.1 p.2 = v)
        (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
          SpinGlass.overlap N p.1 p.2 = v) (by simp)
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          Real.exp (inner ℝ (gtStoppedTrialCoefficient N β q s v p)
            (WithLp.toLp 2 z) + gtPairPotential N h lam v p))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Real.exp_nonneg _)

noncomputable def gtStoppedTrialFieldOne
    (N : ℕ) (β h q s v : ℝ) (z : GTOrdinarySiteIndex N → ℝ)
    (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z (i, 0) +
    gtIncrementScale β s 0 q * z (i, 1) +
    gtIncrementScale β s q |v| * z (i, 2)

noncomputable def gtStoppedTrialFieldTwo
    (N : ℕ) (β h q s v : ℝ) (z : GTOrdinarySiteIndex N → ℝ)
    (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z (i, 0) +
    gtPathSign v * gtIncrementScale β s 0 q * z (i, 1) +
    gtPathSign v * gtIncrementScale β s q |v| * z (i, 2)

lemma gtUnconstrainedStopped_zero_integrand_eq_terminal_sum
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (z : GTOrdinaryIndex N → ℝ) :
    gtStateLogPartition
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          gtPairPotential N h lam v p)
        (gtOrdinaryField
          (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
          (fun p => gtStoppedTrialCoefficient N β q s v p)
          0 0 (WithLp.toLp 2 z)) =
      2 * (N : ℝ) * Real.log 2 +
        ∑ i : Fin N,
          gtTerminal lam
            (gtStoppedTrialFieldOne N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i)
            (gtStoppedTrialFieldTwo N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i) -
        lam * (N : ℝ) * v := by
  classical
  have hpart :
      gtStatePartition
          (fun p : SpinGlass.Config N × SpinGlass.Config N =>
            gtPairPotential N h lam v p)
          (gtOrdinaryField
            (fun p => gtOrdinaryBarePhysicalCoefficient N β q s p)
            (fun p => gtStoppedTrialCoefficient N β q s v p)
            0 0 (WithLp.toLp 2 z)) =
        pairFieldPartition N lam v
          (gtStoppedTrialFieldOne N β h q s v
            (fun ij => z (Sum.inr (Sum.inr ij))))
          (gtStoppedTrialFieldTwo N β h q s v
            (fun ij => z (Sum.inr (Sum.inr ij)))) := by
    unfold gtStatePartition pairFieldPartition gtOrdinaryField
    simp only [Real.sqrt_zero, zero_smul, sub_zero, Real.sqrt_one, one_smul,
      zero_add, add_zero, gtCoefficientCLM_apply]
    apply Finset.sum_congr rfl
    intro p _
    apply congrArg Real.exp
    rw [PiLp.inner_apply]
    simp only [gtStoppedTrialCoefficient, RCLike.inner_apply, conj_trivial,
      PiLp.toLp_apply, gtPairPotential, gtStoppedTrialFieldOne,
      gtStoppedTrialFieldTwo]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) = 0 by rfl, if_true,
      show (1 : Fin 4) ≠ 0 by decide, if_false,
      show (1 : Fin 4) = 1 by rfl,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
      show (2 : Fin 4) = 2 by rfl,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply add_left_cancel (a := lam * (N : ℝ) * v)
    ring_nf
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold gtStateLogPartition
  rw [hpart, log_pairFieldPartition]

lemma gtUnconstrainedStoppedPressure_zero_eq_four_integrals
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ} :
    gtUnconstrainedStoppedPressure N β h q s v lam 0 =
      2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v +
        (N : ℝ) * ∫ z₀, ∫ z₁, ∫ z₂, ∫ _z₃,
          gtTerminal lam
            (h + β * Real.sqrt ((1 - s) * q) * z₀ +
              gtIncrementScale β s 0 q * z₁ +
              gtIncrementScale β s q |v| * z₂)
            (h + β * Real.sqrt ((1 - s) * q) * z₀ +
              gtPathSign v * gtIncrementScale β s 0 q * z₁ +
              gtPathSign v * gtIncrementScale β s q |v| * z₂)
          ∂gaussianReal 0 1 ∂gaussianReal 0 1
          ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  classical
  let μ := Measure.pi (fun _ : GTOrdinaryIndex N => gaussianReal 0 1)
  let g : (Fin 4 → ℝ) → ℝ := fun z =>
    gtTerminal lam
      (h + β * Real.sqrt ((1 - s) * q) * z 0 +
        gtIncrementScale β s 0 q * z 1 + gtIncrementScale β s q |v| * z 2)
      (h + β * Real.sqrt ((1 - s) * q) * z 0 +
        gtPathSign v * gtIncrementScale β s 0 q * z 1 +
        gtPathSign v * gtIncrementScale β s q |v| * z 2)
  have hg : Integrable g (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := by
    let c₁ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2
      ![β * Real.sqrt ((1 - s) * q), gtIncrementScale β s 0 q,
        gtIncrementScale β s q |v|, 0]
    let c₂ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2
      ![β * Real.sqrt ((1 - s) * q),
        gtPathSign v * gtIncrementScale β s 0 q,
        gtPathSign v * gtIncrementScale β s q |v|, 0]
    have hi := integrable_gtTerminal_affine_gaussianProduct lam h h c₁ c₂
    apply hi.congr
    filter_upwards with z
    dsimp [g, c₁, c₂]
    simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
      conj_trivial, PiLp.toLp_apply]
    apply congrArg₂ (gtTerminal lam) <;> simp [Fin.sum_univ_four] <;> ring
  let f : Fin N → (GTOrdinaryIndex N → ℝ) → ℝ := fun i z =>
    gtTerminal lam
      (gtStoppedTrialFieldOne N β h q s v
        (fun ij => z (Sum.inr (Sum.inr ij))) i)
      (gtStoppedTrialFieldTwo N β h q s v
        (fun ij => z (Sum.inr (Sum.inr ij))) i)
  have hf (i : Fin N) : Integrable (f i) μ := by
    let e : Fin 4 → GTOrdinaryIndex N := fun a => Sum.inr (Sum.inr (i, a))
    have he : Function.Injective e := by
      intro a b hab
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hab))
    let φ : (GTOrdinaryIndex N → ℝ) → (Fin 4 → ℝ) := fun z a => z (e a)
    have hmp : MeasurePreserving φ μ
        (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := by
      refine ⟨by fun_prop, ?_⟩
      simpa [φ, μ] using gaussianProduct_restrict_map e he
    have hc : Integrable (fun z : GTOrdinaryIndex N → ℝ => g (φ z)) μ :=
      (hmp.integrable_comp hg.1).2 hg
    simpa [f, g, e, φ, gtStoppedTrialFieldOne,
      gtStoppedTrialFieldTwo] using hc
  unfold gtUnconstrainedStoppedPressure gtOrdinaryPressure
  simp_rw [gtUnconstrainedStopped_zero_integrand_eq_terminal_sum hN]
  have hpoint (z : GTOrdinaryIndex N → ℝ) :
      2 * (N : ℝ) * Real.log 2 + ∑ i, f i z - lam * (N : ℝ) * v =
        (2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v) + ∑ i, f i z := by ring
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => hf i)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_finset_sum Finset.univ (fun i _ => hf i)]
  have hone (i : Fin N) : (∫ z, f i z ∂μ) =
      ∫ z : Fin 4 → ℝ, g z ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
    let e : Fin 4 → GTOrdinaryIndex N := fun a => Sum.inr (Sum.inr (i, a))
    have he : Function.Injective e := by
      intro a b hab
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hab))
    have hr := integral_gaussianProduct_restrict e he g hg.1
    simpa [μ, f, e, g, gtStoppedTrialFieldOne, gtStoppedTrialFieldTwo] using hr
  simp_rw [hone]
  rw [integral_gaussianFinFour_eq_iterated g hg]
  dsimp [g]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

lemma gaussian_terminal_expectation_le_half_step
    (lam x₁ x₂ scale sign : ℝ) :
    (∫ z, gtTerminal lam (x₁ + scale * z)
        (x₂ + sign * scale * z) ∂gaussianReal 0 1) ≤
      gtRankOneStep (1 / 2) scale sign (gtTerminal lam) x₁ x₂ := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  have hgood : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hlin : Integrable (fun z => (1 / 2 : ℝ) *
      F () lam (x₁ + scale * z, x₂ + sign * scale * z))
      (gaussianReal 0 1) :=
    (hgood.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam scale (sign * scale) (x₁, x₂)).const_mul _
  have hexp : Integrable (fun z => Real.exp ((1 / 2 : ℝ) *
      F () lam (x₁ + scale * z, x₂ + sign * scale * z)))
      (gaussianReal 0 1) :=
    GTFrame.integrable_expShift (m := (1 / 2 : ℝ))
      (GTFrame.expMoments_gaussianReal 0 1) hgood (by norm_num)
      () lam scale (sign * scale) (x₁, x₂)
  have hj :
      Real.exp (∫ z, (1 / 2 : ℝ) *
          F () lam (x₁ + scale * z, x₂ + sign * scale * z)
          ∂gaussianReal 0 1) ≤
        ∫ z, Real.exp ((1 / 2 : ℝ) *
          F () lam (x₁ + scale * z, x₂ + sign * scale * z))
          ∂gaussianReal 0 1 := by
    exact convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) hlin hexp
  have hpos : 0 < ∫ z, Real.exp ((1 / 2 : ℝ) *
      F () lam (x₁ + scale * z, x₂ + sign * scale * z))
      ∂gaussianReal 0 1 := lt_of_lt_of_le (Real.exp_pos _) hj
  have hlog := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp] at hlog
  unfold gtRankOneStep standardGaussianExpectation
  simp only [show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false]
  dsimp [F] at hlog ⊢
  rw [integral_const_mul] at hlog
  nlinarith

lemma gtStopped_four_integral_le_half_cascade
    (β h q s v lam : ℝ) :
    (∫ z₀, ∫ z₁, ∫ z₂, ∫ _z₃,
      gtTerminal lam
        (h + β * Real.sqrt ((1 - s) * q) * z₀ +
          gtIncrementScale β s 0 q * z₁ +
          gtIncrementScale β s q |v| * z₂)
        (h + β * Real.sqrt ((1 - s) * q) * z₀ +
          gtPathSign v * gtIncrementScale β s 0 q * z₁ +
          gtPathSign v * gtIncrementScale β s q |v| * z₂)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1
      ∂gaussianReal 0 1 ∂gaussianReal 0 1) ≤
    standardGaussianExpectation (fun z₀ =>
      gtRankOneStep 0 (gtIncrementScale β s 0 q) (gtPathSign v)
        (gtRankOneStep (1 / 2) (gtIncrementScale β s q |v|)
          (gtPathSign v) (gtTerminal lam))
        (h + β * Real.sqrt ((1 - s) * q) * z₀)
        (h + β * Real.sqrt ((1 - s) * q) * z₀)) := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  let a : Unit → ℝ := fun _ => gtIncrementScale β s 0 q
  let b : Unit → ℝ := fun _ => gtIncrementScale β s q |v|
  let sg : Unit → ℝ := fun _ => gtPathSign v
  let e : ℝ := β * Real.sqrt ((1 - s) * q)
  have hF : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have h0b := GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1)
    hF (α := b) (β := fun u => sg u * b u) (hα := continuous_const)
      (hβ := by dsimp [sg, b]; fun_prop)
  have hMb := GTFrame.stepM_good (m := (1 / 2 : ℝ))
    (GTFrame.expMoments_gaussianReal 0 1) hF (by norm_num)
      (α := b) (β := fun u => sg u * b u) (hα := continuous_const)
      (hβ := by dsimp [sg, b]; fun_prop)
  have h0a0b := GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1)
    h0b (α := a) (β := fun u => sg u * a u) (hα := continuous_const)
      (hβ := by dsimp [sg, a]; fun_prop)
  have h0aMb := GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1)
    hMb (α := a) (β := fun u => sg u * a u) (hα := continuous_const)
      (hβ := by dsimp [sg, a]; fun_prop)
  have hleft : Integrable (fun z₀ =>
      GTFrame.step0 (gaussianReal 0 1) a (fun u => sg u * a u)
        (GTFrame.step0 (gaussianReal 0 1) b (fun u => sg u * b u) F)
        () lam (h + e * z₀, h + e * z₀)) (gaussianReal 0 1) :=
    h0a0b.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam e e (h, h)
  have hright : Integrable (fun z₀ =>
      GTFrame.step0 (gaussianReal 0 1) a (fun u => sg u * a u)
        (GTFrame.stepM (gaussianReal 0 1) (1 / 2) b (fun u => sg u * b u) F)
        () lam (h + e * z₀, h + e * z₀)) (gaussianReal 0 1) :=
    h0aMb.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam e e (h, h)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul]
  unfold standardGaussianExpectation gtRankOneStep
  simp only [if_pos rfl, show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false]
  change (∫ z₀, GTFrame.step0 (gaussianReal 0 1) a (fun u => sg u * a u)
      (GTFrame.step0 (gaussianReal 0 1) b (fun u => sg u * b u) F)
      () lam (h + e * z₀, h + e * z₀) ∂gaussianReal 0 1) ≤
    ∫ z₀, GTFrame.step0 (gaussianReal 0 1) a (fun u => sg u * a u)
      (GTFrame.stepM (gaussianReal 0 1) (1 / 2) b (fun u => sg u * b u) F)
      () lam (h + e * z₀, h + e * z₀) ∂gaussianReal 0 1
  apply integral_mono hleft hright
  intro z₀
  unfold GTFrame.step0
  apply integral_mono
  · exact h0b.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam (a ()) (sg () * a ()) (h + e * z₀, h + e * z₀)
  · exact hMb.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam (a ()) (sg () * a ()) (h + e * z₀, h + e * z₀)
  · intro z₁
    have hj := gaussian_terminal_expectation_le_half_step lam
      (h + e * z₀ + a () * z₁)
      (h + e * z₀ + sg () * a () * z₁) (b ()) (sg ())
    unfold gtRankOneStep standardGaussianExpectation at hj
    simp only [show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false] at hj
    dsimp [GTFrame.stepM, F, a, b, sg] at hj ⊢
    norm_num at hj ⊢
    convert hj using 1 <;> ring

lemma gtRankOneStep_half_terminal_add_const
    (scale sign lam k x₁ x₂ : ℝ) :
    gtRankOneStep (1 / 2) scale sign
        (fun y₁ y₂ => gtTerminal lam y₁ y₂ + k) x₁ x₂ =
      gtRankOneStep (1 / 2) scale sign (gtTerminal lam) x₁ x₂ + k := by
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  have hgood : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hpos : 0 < ∫ z, Real.exp ((1 / 2 : ℝ) *
      gtTerminal lam (x₁ + scale * z) (x₂ + sign * scale * z))
      ∂gaussianReal 0 1 := by
    simpa [F] using GTFrame.integral_expShift_pos
      (m := (1 / 2 : ℝ)) (GTFrame.expMoments_gaussianReal 0 1)
      hgood (by norm_num) () lam scale (sign * scale) (x₁, x₂)
  unfold gtRankOneStep standardGaussianExpectation
  simp only [show (1 / 2 : ℝ) ≠ 0 by norm_num, if_false]
  have heq :
      (∫ z, Real.exp ((1 / 2 : ℝ) *
          (gtTerminal lam (x₁ + scale * z) (x₂ + sign * scale * z) + k))
          ∂gaussianReal 0 1) =
        Real.exp ((1 / 2 : ℝ) * k) *
          ∫ z, Real.exp ((1 / 2 : ℝ) *
            gtTerminal lam (x₁ + scale * z) (x₂ + sign * scale * z))
            ∂gaussianReal 0 1 := by
    simp_rw [mul_add, Real.exp_add]
    rw [integral_mul_const]
    ring
  rw [heq, Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp]
  ring

lemma gtRankOneStep_zero_half_add_const
    (outer inner sign lam k x₁ x₂ : ℝ) :
    gtRankOneStep 0 outer sign
        (fun y₁ y₂ =>
          gtRankOneStep (1 / 2) inner sign (gtTerminal lam) y₁ y₂ + k)
        x₁ x₂ =
      gtRankOneStep 0 outer sign
        (gtRankOneStep (1 / 2) inner sign (gtTerminal lam)) x₁ x₂ + k := by
  let G : GTTwoField := gtRankOneStep (1 / 2) inner sign (gtTerminal lam)
  change gtRankOneStep 0 outer sign (fun y₁ y₂ => G y₁ y₂ + k) x₁ x₂ =
    gtRankOneStep 0 outer sign G x₁ x₂ + k
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  let b : Unit → ℝ := fun _ => inner
  let sg : Unit → ℝ := fun _ => sign
  have hF : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hMb := GTFrame.stepM_good (m := (1 / 2 : ℝ))
    (GTFrame.expMoments_gaussianReal 0 1) hF (by norm_num)
      (α := b) (β := fun u => sg u * b u) (hα := continuous_const)
      (hβ := by dsimp [sg, b]; fun_prop)
  have hi : Integrable (fun z =>
      G (x₁ + outer * z) (x₂ + sign * outer * z))
      (gaussianReal 0 1) := by
    have h := hMb.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam outer (sign * outer) (x₁, x₂)
    simpa [G, GTFrame.stepM, F, b, sg, gtRankOneStep,
      standardGaussianExpectation] using h
  unfold gtRankOneStep
  simp only [if_pos rfl, standardGaussianExpectation]
  rw [integral_add hi (integrable_const k)]
  simp

lemma gtUnconstrainedHalfPressure_zero_add_derivativeGap_eq_gtFunctional
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 < q)
    (hqr : q ≤ |v|) (hr1 : |v| ≤ 1) :
    gtUnconstrainedHalfPressure N β h q s v lam 0 +
        ((N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2)) / 2 +
        ((N : ℝ) * gtScalarVariance β s v q -
          (N : ℝ) * gtScalarVariance β s v |v|) / 4 =
      (N : ℝ) * gtFunctional β h q s lam v := by
  let sign : ℝ := gtPathSign v
  let e : ℝ := β * Real.sqrt ((1 - s) * q)
  let a : ℝ := gtIncrementScale β s 0 q
  let b : ℝ := gtIncrementScale β s q |v|
  let c : ℝ := gtIncrementScale β s |v| 1
  let innerF : GTTwoField :=
    gtRankOneStep (1 / 2) b sign (gtTerminal lam)
  let cascade : GTTwoField := gtRankOneStep 0 a sign innerF
  let C : ℝ := standardGaussianExpectation fun z => cascade (h + e * z) (h + e * z)
  have hc : c ^ 2 = β ^ 2 * s * (1 - |v|) := by
    dsimp [c]
    simpa using gtIncrementScale_sq (β := β) (s := s)
      hs.1 hr1
  have hupper_fun :
      gtDiagonalStep 1 c (gtTerminal lam) =
        fun x₁ x₂ => gtTerminal lam x₁ x₂ + c ^ 2 := by
    funext x₁ x₂
    exact gtDiagonalStep_one_terminal c lam x₁ x₂
  have hqnot : ¬ q ≤ (0 : ℝ) := not_le.mpr hq0
  have hrpos : 0 < |v| := lt_of_lt_of_le hq0 hqr
  have hrnot : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  have hfunctional :
      gtFunctional β h q s lam v =
        2 * Real.log 2 +
          standardGaussianExpectation (fun z =>
            gtRankOneStep 0 a sign
              (gtRankOneStep (1 / 2) b sign
                (gtDiagonalStep 1 c (gtTerminal lam)))
              (h + e * z) (h + e * z)) -
          lam * v - gtCorrection β q s := by
    unfold gtFunctional gtSemigroupSolution
    simp [hqr, hqnot, hrnot, a, b, c, e, sign]
  have hcascade_add (x₁ x₂ : ℝ) :
      gtRankOneStep 0 a sign
          (gtRankOneStep (1 / 2) b sign
            (gtDiagonalStep 1 c (gtTerminal lam))) x₁ x₂ =
        cascade x₁ x₂ + c ^ 2 := by
    rw [hupper_fun]
    have hinner_fun :
        gtRankOneStep (1 / 2) b sign
            (fun y₁ y₂ => gtTerminal lam y₁ y₂ + c ^ 2) =
          fun y₁ y₂ => innerF y₁ y₂ + c ^ 2 := by
      funext y₁ y₂
      exact gtRankOneStep_half_terminal_add_const b sign lam (c ^ 2) y₁ y₂
    rw [hinner_fun]
    exact gtRankOneStep_zero_half_add_const a b sign lam (c ^ 2) x₁ x₂
  let F : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => gtTerminal l x.1 x.2
  let D : Unit → ℝ → ℝ × ℝ → ℝ :=
    fun _ l x => GTFrame.fLbaseD l x
  let aa : Unit → ℝ := fun _ => a
  let bb : Unit → ℝ := fun _ => b
  let sg : Unit → ℝ := fun _ => sign
  have hF : GTFrame.GoodFam F D := by
    simpa [F, D] using (GTFrame.goodFam_fLbase (P := Unit))
  have hMb := GTFrame.stepM_good (m := (1 / 2 : ℝ))
    (GTFrame.expMoments_gaussianReal 0 1) hF (by norm_num)
      (α := bb) (β := fun u => sg u * bb u) (hα := continuous_const)
      (hβ := by dsimp [sg, bb]; fun_prop)
  have h0aMb := GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1)
    hMb (α := aa) (β := fun u => sg u * aa u) (hα := continuous_const)
      (hβ := by dsimp [sg, aa]; fun_prop)
  have hCint : Integrable (fun z => cascade (h + e * z) (h + e * z))
      (gaussianReal 0 1) := by
    have hi := h0aMb.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      () lam e e (h, h)
    simpa [cascade, innerF, GTFrame.step0, GTFrame.stepM, F, aa, bb, sg,
      gtRankOneStep, standardGaussianExpectation] using hi
  have htrial :
      standardGaussianExpectation (fun z =>
          gtRankOneStep 0 a sign
            (gtRankOneStep (1 / 2) b sign
              (gtDiagonalStep 1 c (gtTerminal lam)))
            (h + e * z) (h + e * z)) = C + c ^ 2 := by
    simp_rw [hcascade_add]
    unfold standardGaussianExpectation C
    rw [integral_add hCint (integrable_const (c ^ 2))]
    simp [standardGaussianExpectation]
  rw [gtUnconstrainedHalfPressure_zero_eq_cascade hN]
  rw [hfunctional, htrial]
  unfold gtScalarVariance gtCorrection
  simp only [if_pos hqr, if_pos le_rfl]
  rw [hc]
  ring
end SpinGlass.AT
