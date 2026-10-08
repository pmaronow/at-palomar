module

public import Lemmas.GuerraTalagrand.Bound.Comparison
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

/-!
# The single half-mass level in the GT hierarchy

When `q ≤ |v|`, the specialized GT path has exactly one nontrivial
hierarchical mass, namely `m = 1/2` on `[q, |v|]`.  This file isolates that
one level.  The outer coordinates have mass zero; `z₁` is integrated with
the half-mass logarithmic transform.
-/

/-- Exponential moments of the Euclidean norm under the raw product-Gaussian
measure.  This is the pullback form used by the coordinatewise Stein API. -/
lemma integrable_exp_mul_norm_gaussianProduct
    {I : Type*} [Fintype I] (c : ℝ) :
    Integrable (fun z : I → ℝ =>
      Real.exp (c * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  have hi := SYK.integrable_exp_mul_norm (ι := I) c
  unfold SYK.standardGaussianMeasureOnEuclidean at hi
  rw [MeasureTheory.integrable_map_measure (by fun_prop) (by fun_prop)] at hi
  exact hi

/-- Multiplying an exponential norm moment by one power of the norm remains
integrable. -/
lemma integrable_norm_mul_exp_mul_norm_gaussianProduct
    {I : Type*} [Fintype I] (c : ℝ) :
    Integrable (fun z : I → ℝ =>
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖ *
        Real.exp (c * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let d : ℝ := |c| + 1
  have hi := integrable_exp_mul_norm_gaussianProduct (I := I) d
  apply hi.mono'
  · fun_prop
  · filter_upwards with z
    let x : ℝ := ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖
    have hx : 0 ≤ x := norm_nonneg _
    have hc : c ≤ |c| := le_abs_self c
    have hxe : x ≤ Real.exp x := by
      linarith [Real.add_one_le_exp x]
    have hce : Real.exp (c * x) ≤ Real.exp (|c| * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hx)
    rw [Real.norm_of_nonneg (mul_nonneg hx (Real.exp_nonneg _))]
    dsimp [d]
    rw [add_mul, Real.exp_add]
    calc
      x * Real.exp (c * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖) =
          x * Real.exp (c * x) := by simp [x]
      _ ≤ Real.exp x * Real.exp (|c| * x) :=
        mul_le_mul hxe hce (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|c| * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖) *
          Real.exp (1 * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖) := by
        simp [x, mul_comm]

/-- A finite log-partition composed with an affine field has exponential
moments under a product Gaussian. -/
lemma integrable_exp_mul_gtStateLogPartition_affine
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (a : ℝ)
    (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H₀ : GTStateSpace S) :
    Integrable (fun z : I → ℝ =>
      Real.exp (a * gtStateLogPartition V
        (L (WithLp.toLp 2 z) + H₀)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let base := hasModerateGrowth_gtStateLogPartition_comp V L H₀
  let c : ℝ := |a| * base.C
  let M : ℝ := Real.exp c
  let bound : (I → ℝ) → ℝ := fun z =>
    M * Real.exp (c * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)
  have hb : Integrable bound
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    exact (integrable_exp_mul_norm_gaussianProduct (I := I) c).const_mul M
  apply hb.mono'
  · have hfield : Continuous (fun z : I → ℝ =>
        L (WithLp.toLp 2 z) + H₀) := by fun_prop
    exact (Real.continuous_exp.comp
      (((contDiff_gtStateLogPartition V).continuous.comp hfield).const_mul a)
      ).aestronglyMeasurable
  · filter_upwards with z
    let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
    have hm : base.m = 1 := by rfl
    have hg := base.F_bound zE
    rw [hm, pow_one] at hg
    have ha : a * gtStateLogPartition V (L zE + H₀) ≤
        |a| * (base.C * (1 + ‖zE‖)) := by
      calc
        a * gtStateLogPartition V (L zE + H₀) ≤
            |a * gtStateLogPartition V (L zE + H₀)| := le_abs_self _
        _ = |a| * |gtStateLogPartition V (L zE + H₀)| := abs_mul _ _
        _ ≤ |a| * (base.C * (1 + ‖zE‖)) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg a)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    dsimp [bound, M, c]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [zE] at ha ⊢
    convert ha using 1 <;> ring

/-- The state field in the one-half-mass Gaussian interpolation. -/
noncomputable def gtHalfField
    {S I₀ I₁ : Type*} [Fintype S] [Fintype I₀] [Fintype I₁]
    (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) :
    GTStateSpace S :=
  Real.sqrt t • gtCoefficientCLM A z₀ +
    Real.sqrt (1 - t) •
      (gtCoefficientCLM B₀ z₀ + gtCoefficientCLM B₁ z₁) + H₀

/-- The positive denominator of the mass-`1/2` transform. -/
noncomputable def gtHalfDenominator
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) : ℝ :=
  ∫ z₁ : I₁ → ℝ,
    Real.exp ((1 / 2 : ℝ) * gtStateLogPartition V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)))
  ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)

lemma integrable_gtHalfDenominator_integrand
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) :
    Integrable (fun z₁ : I₁ → ℝ =>
      Real.exp ((1 / 2 : ℝ) * gtStateLogPartition V
        (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁))))
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
  let L : EuclideanSpace ℝ I₁ →L[ℝ] GTStateSpace S :=
    Real.sqrt (1 - t) • gtCoefficientCLM B₁
  let K : GTStateSpace S :=
    Real.sqrt t • gtCoefficientCLM A z₀ +
      Real.sqrt (1 - t) • gtCoefficientCLM B₀ z₀ + H₀
  have hi := integrable_exp_mul_gtStateLogPartition_affine
    V (1 / 2 : ℝ) L K
  convert hi using 1
  funext z₁
  congr 2
  simp [L, K, gtHalfField]
  abel

lemma gtHalfDenominator_pos
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) :
    0 < gtHalfDenominator V A B₀ B₁ H₀ t z₀ := by
  unfold gtHalfDenominator
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le)
    (integrable_gtHalfDenominator_integrand V A B₀ B₁ H₀ t z₀)]
  have hsupp : Function.support (fun z : I₁ → ℝ =>
      Real.exp ((1 / 2 : ℝ) * gtStateLogPartition V
        (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z)))) = Set.univ := by
    ext z
    simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [hsupp]
  simp

/-- The inner logarithmic transform at mass `1/2`. -/
noncomputable def gtHalfTransform
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) : ℝ :=
  2 * Real.log (gtHalfDenominator V A B₀ B₁ H₀ t z₀)

/-- The unnormalized half-mass density. -/
noncomputable def gtHalfDensity
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * gtStateLogPartition V
    (gtHalfField A B₀ B₁ H₀ t z₀ z₁))

/-- A Gibbs coordinate averaged under the normalized half-mass tilt. -/
noncomputable def gtHalfGibbsWeight
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi : S) : ℝ :=
  (∫ z₁ : I₁ → ℝ,
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
        gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi
      ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) /
    gtHalfDenominator V A B₀ B₁ H₀ t z₀

/-- Two Gibbs samples sharing the inner Gaussian coordinate. -/
noncomputable def gtHalfInnerPairWeight
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi eta : S) : ℝ :=
  (∫ z₁ : I₁ → ℝ,
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
        (gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi *
        gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta)
      ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) /
    gtHalfDenominator V A B₀ B₁ H₀ t z₀

lemma integrable_gtHalfDensity_mul_gibbs
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi : S) :
    Integrable (fun z₁ : I₁ → ℝ =>
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
        gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi)
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
  have hd := integrable_gtHalfDenominator_integrand V A B₀ B₁ H₀ t z₀
  apply hd.mono'
  · have hfield : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) := by
      unfold gtHalfField
      fun_prop
    exact hd.1.mul
      ((((contDiff_gtStateGibbs V xi).continuous.comp hfield)).aestronglyMeasurable)
  · filter_upwards with z₁
    have hg0 := gtStateGibbs_nonneg V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi
    have hg1 := gtStateGibbs_le_one V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi
    unfold gtHalfDensity
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) hg0)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hg1

lemma integrable_gtHalfDensity_mul_gibbs_mul_gibbs
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi eta : S) :
    Integrable (fun z₁ : I₁ → ℝ =>
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
        (gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi *
        gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta))
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
  have hi := integrable_gtHalfDensity_mul_gibbs V A B₀ B₁ H₀ t z₀ xi
  apply hi.mono'
  · have hfield : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) := by
      unfold gtHalfField
      fun_prop
    have hgeta : AEStronglyMeasurable (fun z₁ : I₁ → ℝ =>
        gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta)
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) :=
      (((contDiff_gtStateGibbs V eta).continuous.comp hfield)).aestronglyMeasurable
    have hm := hi.1.mul hgeta
    apply hm.congr
    filter_upwards with z₁
    simp only [Pi.mul_apply]
    ring
  · filter_upwards with z₁
    have hxi0 := gtStateGibbs_nonneg V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi
    have heta0 := gtStateGibbs_nonneg V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta
    have heta1 := gtStateGibbs_le_one V
      (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta
    unfold gtHalfDensity
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg hxi0 heta0))]
    calc
      Real.exp _ *
          (gtStateGibbs V _ xi * gtStateGibbs V _ eta) =
          (Real.exp _ * gtStateGibbs V _ xi) * gtStateGibbs V _ eta := by ring
      _ ≤ (Real.exp _ * gtStateGibbs V _ xi) * 1 :=
        mul_le_mul_of_nonneg_left heta1
          (mul_nonneg (Real.exp_nonneg _) hxi0)
      _ = Real.exp _ * gtStateGibbs V _ xi := by ring

lemma gtHalfGibbsWeight_nonneg
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi : S) :
    0 ≤ gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ xi := by
  unfold gtHalfGibbsWeight
  exact div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_nonneg _)
    (gtStateGibbs_nonneg V _ xi))
    (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).le

lemma sum_gtHalfGibbsWeight
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) :
    ∑ xi : S, gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ xi = 1 := by
  classical
  unfold gtHalfGibbsWeight
  rw [← Finset.sum_div, ← integral_finset_sum]
  · simp_rw [← Finset.mul_sum, sum_gtStateGibbs, mul_one]
    unfold gtHalfDenominator gtHalfDensity
    exact div_self (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).ne'
  · intro xi _
    exact integrable_gtHalfDensity_mul_gibbs V A B₀ B₁ H₀ t z₀ xi

lemma gtHalfInnerPairWeight_nonneg
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (xi eta : S) :
    0 ≤ gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ xi eta := by
  unfold gtHalfInnerPairWeight
  exact div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (gtStateGibbs_nonneg V _ xi) (gtStateGibbs_nonneg V _ eta)))
    (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).le

lemma sum_gtHalfInnerPairWeight
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) :
    ∑ xi : S, ∑ eta : S,
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ xi eta = 1 := by
  classical
  unfold gtHalfInnerPairWeight
  simp_rw [← Finset.sum_div]
  rw [div_eq_iff
    (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).ne']
  simp only [one_mul]
  calc
    (∑ xi : S, ∑ eta : S, ∫ z₁ : I₁ → ℝ,
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
          (gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi *
          gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) =
      ∑ xi : S, ∫ z₁ : I₁ → ℝ, ∑ eta : S,
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
          (gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi *
          gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1) := by
        apply Finset.sum_congr rfl
        intro xi _
        rw [integral_finset_sum]
        intro eta _
        exact integrable_gtHalfDensity_mul_gibbs_mul_gibbs
          V A B₀ B₁ H₀ t z₀ xi eta
    _ = ∫ z₁ : I₁ → ℝ, ∑ xi : S, ∑ eta : S,
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
          (gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) xi *
          gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) eta)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1) := by
        rw [integral_finset_sum]
        intro xi _
        exact integrable_finset_sum _ fun eta _ =>
          integrable_gtHalfDensity_mul_gibbs_mul_gibbs
            V A B₀ B₁ H₀ t z₀ xi eta
    _ = gtHalfDenominator V A B₀ B₁ H₀ t z₀ := by
        unfold gtHalfDenominator
        apply integral_congr_ae
        filter_upwards with z₁
        simp_rw [← mul_assoc, ← Finset.mul_sum, sum_gtStateGibbs, mul_one]
        unfold gtHalfDensity
        rw [← Finset.mul_sum, sum_gtStateGibbs, mul_one]

/-- The covariance expression produced by the one-half-mass Gaussian
integration by parts.  The two pair terms correspond respectively to samples
which split below `q` and to samples which share the inner coordinate up to
`|v|`. -/
noncomputable def gtHalfDerivativeExpression
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) : ℝ :=
  (1 / 2 : ℝ) * ∑ xi : S,
      gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ xi *
        (inner ℝ (A xi) (A xi) - inner ℝ (B₀ xi) (B₀ xi) -
          inner ℝ (B₁ xi) (B₁ xi)) -
    (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S,
      (gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ xi *
        gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ eta) *
        (inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta)) -
    (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S,
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ xi eta *
        (inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta) -
          inner ℝ (B₁ xi) (B₁ eta))

/-- Abstract sign certificate for the half-mass derivative.  In the GT
application `lowerGap` and `upperGap` are the square completions centered at
the matrices `Q(q)` and `Q(|v|)`. -/
lemma gtHalfDerivativeExpression_le
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀)
    (shiftQ shiftR diagGap : ℝ)
    (lowerGap upperGap : S → S → ℝ)
    (hlower : ∀ xi eta,
      inner ℝ (A xi) (A eta) + shiftQ - inner ℝ (B₀ xi) (B₀ eta) =
        lowerGap xi eta)
    (hupper : ∀ xi eta,
      inner ℝ (A xi) (A eta) + shiftR - inner ℝ (B₀ xi) (B₀ eta) -
        inner ℝ (B₁ xi) (B₁ eta) = upperGap xi eta)
    (hdiag : ∀ xi, upperGap xi xi = diagGap)
    (hlower0 : ∀ xi eta, 0 ≤ lowerGap xi eta)
    (hupper0 : ∀ xi eta, 0 ≤ upperGap xi eta) :
    gtHalfDerivativeExpression V A B₀ B₁ H₀ t z₀ ≤
      diagGap / 2 + (shiftQ - shiftR) / 4 := by
  classical
  let w : S → ℝ := fun xi =>
    gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ xi
  let u : S → S → ℝ := fun xi eta =>
    gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ xi eta
  have hw0 (xi : S) : 0 ≤ w xi :=
    gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ t z₀ xi
  have hu0 (xi eta : S) : 0 ≤ u xi eta :=
    gtHalfInnerPairWeight_nonneg V A B₀ B₁ H₀ t z₀ xi eta
  have hwsum : ∑ xi : S, w xi = 1 :=
    sum_gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀
  have husum : ∑ xi : S, ∑ eta : S, u xi eta = 1 :=
    sum_gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀
  have hdiagSum :
      ∑ xi : S, w xi * upperGap xi xi = diagGap := by
    simp_rw [hdiag]
    rw [← Finset.sum_mul, hwsum, one_mul]
  have houterSum :
      ∑ xi : S, ∑ eta : S, w xi * w eta = 1 := by
    calc
      (∑ xi : S, ∑ eta : S, w xi * w eta) =
          (∑ xi : S, w xi) * (∑ eta : S, w eta) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro xi _
            rw [Finset.mul_sum]
      _ = 1 := by rw [hwsum, one_mul]
  have hwShiftR : ∑ xi : S, w xi * shiftR = shiftR := by
    rw [← Finset.sum_mul, hwsum, one_mul]
  have houterShiftQ :
      ∑ xi : S, ∑ eta : S, (w xi * w eta) * shiftQ = shiftQ := by
    calc
      (∑ xi : S, ∑ eta : S, (w xi * w eta) * shiftQ) =
          (∑ xi : S, ∑ eta : S, w xi * w eta) * shiftQ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro xi _
            rw [Finset.sum_mul]
      _ = shiftQ := by rw [houterSum, one_mul]
  have hinnerShiftR :
      ∑ xi : S, ∑ eta : S, u xi eta * shiftR = shiftR := by
    calc
      (∑ xi : S, ∑ eta : S, u xi eta * shiftR) =
          (∑ xi : S, ∑ eta : S, u xi eta) * shiftR := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro xi _
            rw [Finset.sum_mul]
      _ = shiftR := by rw [husum, one_mul]
  have hlowerSum0 : 0 ≤
      ∑ xi : S, ∑ eta : S, (w xi * w eta) * lowerGap xi eta := by
    exact Finset.sum_nonneg fun xi _ => Finset.sum_nonneg fun eta _ =>
      mul_nonneg (mul_nonneg (hw0 xi) (hw0 eta)) (hlower0 xi eta)
  have hupperSum0 : 0 ≤
      ∑ xi : S, ∑ eta : S, u xi eta * upperGap xi eta := by
    exact Finset.sum_nonneg fun xi _ => Finset.sum_nonneg fun eta _ =>
      mul_nonneg (hu0 xi eta) (hupper0 xi eta)
  have hformula :
      gtHalfDerivativeExpression V A B₀ B₁ H₀ t z₀ =
        diagGap / 2 + (shiftQ - shiftR) / 4 -
          (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S,
            (w xi * w eta) * lowerGap xi eta -
          (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S,
            u xi eta * upperGap xi eta := by
    unfold gtHalfDerivativeExpression
    change (1 / 2 : ℝ) * ∑ xi : S, w xi *
        (inner ℝ (A xi) (A xi) - inner ℝ (B₀ xi) (B₀ xi) -
          inner ℝ (B₁ xi) (B₁ xi)) -
      (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S, (w xi * w eta) *
        (inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta)) -
      (1 / 4 : ℝ) * ∑ xi : S, ∑ eta : S, u xi eta *
        (inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta) -
          inner ℝ (B₁ xi) (B₁ eta)) = _
    have hU (xi eta : S) :
        inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta) -
            inner ℝ (B₁ xi) (B₁ eta) =
          upperGap xi eta - shiftR := by
      linarith [hupper xi eta]
    have hL (xi eta : S) :
        inner ℝ (A xi) (A eta) - inner ℝ (B₀ xi) (B₀ eta) =
          lowerGap xi eta - shiftQ := by
      linarith [hlower xi eta]
    simp_rw [hU, hL]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hdiagSum, hwShiftR, houterShiftQ, hinnerShiftR]
    ring
  rw [hformula]
  nlinarith [hlowerSum0, hupperSum0]

/-- The outer mass-zero expectation of the half-mass transform. -/
noncomputable def gtHalfPressure
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁)
    (H₀ : GTStateSpace S) (t : ℝ) : ℝ :=
  ∫ z₀ : I₀ → ℝ,
    gtHalfTransform V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)
    ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)

end SpinGlass.AT
