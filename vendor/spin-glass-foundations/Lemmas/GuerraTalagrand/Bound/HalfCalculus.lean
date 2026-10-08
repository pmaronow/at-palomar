module

public import Lemmas.GuerraTalagrand.Bound.HalfStep
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

/-- The half-mass density, viewed directly as a function of the finite-state
field.  This small wrapper keeps the calculus formulas readable. -/
noncomputable def gtHalfBaseDensity
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * gtStateLogPartition V H)

lemma contDiff_gtHalfBaseDensity
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) :
    ContDiff ℝ ∞ (gtHalfBaseDensity V) := by
  unfold gtHalfBaseDensity
  exact (contDiff_const.mul (contDiff_gtStateLogPartition V)).exp

lemma gtHalfBaseDensity_pos
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    0 < gtHalfBaseDensity V H := by
  unfold gtHalfBaseDensity
  positivity

lemma fderiv_gtHalfBaseDensity_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) :
    fderiv ℝ (gtHalfBaseDensity V) H K =
      gtHalfBaseDensity V H * (1 / 2 : ℝ) *
        ∑ ξ : S, gtStateGibbs V H ξ * K ξ := by
  have hd : HasFDerivAt (gtStateLogPartition V)
      (fderiv ℝ (gtStateLogPartition V) H) H :=
    ((contDiff_gtStateLogPartition V).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have he := (hd.const_mul (1 / 2 : ℝ)).exp
  have happ := congrArg
    (fun L : GTStateSpace S →L[ℝ] ℝ => L K) he.fderiv
  change fderiv ℝ (gtHalfBaseDensity V) H K = _ at happ
  rw [happ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_gtStateLogPartition_apply]
  unfold gtHalfBaseDensity
  ring

lemma contDiff_gtHalfBaseDensity_mul_gibbs
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (ξ : S) :
    ContDiff ℝ ∞ (fun H : GTStateSpace S =>
      gtHalfBaseDensity V H * gtStateGibbs V H ξ) :=
  (contDiff_gtHalfBaseDensity V).mul (contDiff_gtStateGibbs V ξ)

lemma fderiv_gtHalfBaseDensity_mul_gibbs_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) (ξ : S) :
    fderiv ℝ (fun H' : GTStateSpace S =>
        gtHalfBaseDensity V H' * gtStateGibbs V H' ξ) H K =
      gtHalfBaseDensity V H * gtStateGibbs V H ξ *
        (K ξ - (1 / 2 : ℝ) *
          ∑ η : S, gtStateGibbs V H η * K η) := by
  have hd : HasFDerivAt (gtHalfBaseDensity V)
      (fderiv ℝ (gtHalfBaseDensity V) H) H :=
    ((contDiff_gtHalfBaseDensity V).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hg : HasFDerivAt
      (fun H' : GTStateSpace S => gtStateGibbs V H' ξ)
      (fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H) H :=
    ((contDiff_gtStateGibbs V ξ).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hp := hd.mul hg
  have happ := congrArg
    (fun L : GTStateSpace S →L[ℝ] ℝ => L K) hp.fderiv
  change fderiv ℝ (fun H' : GTStateSpace S =>
      gtHalfBaseDensity V H' * gtStateGibbs V H' ξ) H K = _ at happ
  rw [happ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [fderiv_gtHalfBaseDensity_apply, fderiv_gtStateGibbs_apply]
  ring

lemma norm_fderiv_gtHalfBaseDensity_le
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    ‖fderiv ℝ (gtHalfBaseDensity V) H‖ ≤
      (1 / 2 : ℝ) * gtHalfBaseDensity V H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _))
  intro K
  rw [Real.norm_eq_abs, fderiv_gtHalfBaseDensity_apply]
  have havg : |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤ ‖K‖ := by
    simpa [fderiv_gtStateLogPartition_apply, Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (gtStateLogPartition V) H) K |>.trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_gtStateLogPartition_le_one V H) (norm_nonneg K)))
  rw [abs_mul, abs_mul, abs_of_nonneg (gtHalfBaseDensity_pos V H).le,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    gtHalfBaseDensity V H * (1 / 2) *
        |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤
      gtHalfBaseDensity V H * (1 / 2) * ‖K‖ :=
        mul_le_mul_of_nonneg_left havg
          (mul_nonneg (gtHalfBaseDensity_pos V H).le (by norm_num))
    _ = (1 / 2) * gtHalfBaseDensity V H * ‖K‖ := by ring

lemma norm_fderiv_gtHalfBaseDensity_mul_gibbs_le
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    ‖fderiv ℝ (fun H' : GTStateSpace S =>
        gtHalfBaseDensity V H' * gtStateGibbs V H' ξ) H‖ ≤
      2 * gtHalfBaseDensity V H := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (gtHalfBaseDensity_pos V H).le)
  intro K
  rw [Real.norm_eq_abs, fderiv_gtHalfBaseDensity_mul_gibbs_apply]
  have hKξ : |K ξ| ≤ ‖K‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (p := (2 : ENNReal)) K ξ
  have havg : |∑ η : S, gtStateGibbs V H η * K η| ≤ ‖K‖ := by
    simpa [fderiv_gtStateLogPartition_apply, Real.norm_eq_abs] using
      (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (gtStateLogPartition V) H) K |>.trans
          (mul_le_mul_of_nonneg_right
            (norm_fderiv_gtStateLogPartition_le_one V H) (norm_nonneg K)))
  have hg0 := gtStateGibbs_nonneg V H ξ
  have hg1 := gtStateGibbs_le_one V H ξ
  rw [abs_mul, abs_mul, abs_of_nonneg (gtHalfBaseDensity_pos V H).le,
    abs_of_nonneg hg0]
  have hd := abs_sub (K ξ)
    ((1 / 2 : ℝ) * ∑ η : S, gtStateGibbs V H η * K η)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hd
  have hd2 :
      |K ξ - (1 / 2) * ∑ η : S, gtStateGibbs V H η * K η| ≤
        (3 / 2 : ℝ) * ‖K‖ := by
    linarith
  have hρ : 0 ≤ gtHalfBaseDensity V H := (gtHalfBaseDensity_pos V H).le
  calc
    gtHalfBaseDensity V H * gtStateGibbs V H ξ *
        |K ξ - (1 / 2) * ∑ η : S, gtStateGibbs V H η * K η| ≤
      (gtHalfBaseDensity V H * 1) * ((3 / 2 : ℝ) * ‖K‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg1 hρ) hd2
          (abs_nonneg _) (by positivity)
    _ ≤ (2 * gtHalfBaseDensity V H) * ‖K‖ := by
      nlinarith [norm_nonneg K]

/-- Local exponential domination for the half density along an affine
Gaussian field. -/
lemma gtHalfBaseDensity_affine_local_bound
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H H' : GTStateSpace S) (z : EuclideanSpace ℝ I)
    (hnear : ‖H' - H‖ < 1) :
    gtHalfBaseDensity V (L z + H') ≤
      Real.exp
        ((hasModerateGrowth_gtStateLogPartition V).C *
          (2 + ‖L‖ + ‖H‖) * (1 + ‖z‖)) := by
  let base := hasModerateGrowth_gtStateLogPartition V
  have hH' : ‖H'‖ ≤ ‖H‖ + 1 := by
    have heq : H' = (H' - H) + H := by abel
    calc
      ‖H'‖ = ‖(H' - H) + H‖ := congrArg norm heq
      _ ≤ ‖H' - H‖ + ‖H‖ := norm_add_le _ _
      _ ≤ ‖H‖ + 1 := by linarith
  have hL := L.le_opNorm z
  have hadd := norm_add_le (L z) H'
  have hnorm : 1 + ‖L z + H'‖ ≤
      (2 + ‖L‖ + ‖H‖) * (1 + ‖z‖) := by
    nlinarith [norm_nonneg L, norm_nonneg H, norm_nonneg z]
  have hb := base.F_bound (L z + H')
  have hm : base.m = 1 := by rfl
  rw [hm, pow_one] at hb
  unfold gtHalfBaseDensity
  apply Real.exp_le_exp.mpr
  calc
    (1 / 2 : ℝ) * gtStateLogPartition V (L z + H') ≤
        base.C * (1 + ‖L z + H'‖) := by
      have := le_abs_self (gtStateLogPartition V (L z + H'))
      have hc0 : 0 ≤ base.C * (1 + ‖L z + H'‖) :=
        mul_nonneg base.Cpos.le (by positivity)
      nlinarith
    _ ≤ base.C * ((2 + ‖L‖ + ‖H‖) * (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hnorm base.Cpos.le
    _ = base.C * (2 + ‖L‖ + ‖H‖) * (1 + ‖z‖) := by ring

lemma integrable_gtHalfBaseDensity_affine_local_bound
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    Integrable (fun z : I → ℝ =>
      Real.exp
        ((hasModerateGrowth_gtStateLogPartition V).C *
          (2 + ‖L‖ + ‖H‖) *
            (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let c : ℝ := (hasModerateGrowth_gtStateLogPartition V).C *
    (2 + ‖L‖ + ‖H‖)
  have hi := integrable_exp_mul_norm_gaussianProduct (I := I) c
  have hc : (fun z : I → ℝ => Real.exp
      (c * (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))) =
      fun z => Real.exp c * Real.exp
        (c * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖) := by
    funext z
    rw [mul_add, mul_one, Real.exp_add]
  rw [hc]
  exact hi.const_mul _

/-- Gaussian convolution of the half density as a function of its base
finite-state field. -/
noncomputable def gtHalfBaseDenominator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) : ℝ :=
  ∫ z : I → ℝ,
    gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H)
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)

noncomputable def gtHalfBaseNumerator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) : ℝ :=
  ∫ z : I → ℝ,
    gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
      gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)

noncomputable def gtHalfBasePairNumerator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ η : S) : ℝ :=
  ∫ z : I → ℝ,
    gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
      (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
        gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)

lemma integrable_gtHalfBaseDenominator_integrand
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    Integrable (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  simpa [gtHalfBaseDensity] using
    integrable_exp_mul_gtStateLogPartition_affine V (1 / 2 : ℝ) L H

lemma integrable_gtHalfBaseNumerator_integrand
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    Integrable (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
        gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  have hd := integrable_gtHalfBaseDenominator_integrand V L H
  apply hd.mono'
  · have hc : Continuous (fun z : I → ℝ =>
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ) :=
      ((contDiff_gtHalfBaseDensity V).continuous.comp (by fun_prop)).mul
        ((contDiff_gtStateGibbs V ξ).continuous.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (gtHalfBaseDensity_pos V _).le,
      abs_of_nonneg (gtStateGibbs_nonneg V _ ξ)]
    exact mul_le_of_le_one_right (gtHalfBaseDensity_pos V _).le
      (gtStateGibbs_le_one V _ ξ)

lemma integrable_gtHalfBasePairNumerator_integrand
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ η : S) :
    Integrable (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
        (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) η))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  have hi := integrable_gtHalfBaseNumerator_integrand V L H ξ
  apply hi.mono'
  · have hfield : Continuous (fun z : I → ℝ =>
        L (WithLp.toLp 2 z) + H) := by fun_prop
    exact (((contDiff_gtHalfBaseDensity V).continuous.comp hfield).mul
      (((contDiff_gtStateGibbs V ξ).continuous.comp hfield).mul
        ((contDiff_gtStateGibbs V η).continuous.comp hfield)
      )).aestronglyMeasurable
  · filter_upwards with z
    have hη0 := gtStateGibbs_nonneg V (L (WithLp.toLp 2 z) + H) η
    have hη1 := gtStateGibbs_le_one V (L (WithLp.toLp 2 z) + H) η
    have hbase0 := gtHalfBaseDensity_pos V (L (WithLp.toLp 2 z) + H)
    have hξ0 := gtStateGibbs_nonneg V (L (WithLp.toLp 2 z) + H) ξ
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hbase0.le, abs_of_nonneg hξ0, abs_of_nonneg hη0]
    calc
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) =
        (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ) *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η := by ring
      _ ≤ (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ) * 1 :=
        mul_le_mul_of_nonneg_left hη1 (mul_nonneg hbase0.le hξ0)
      _ = gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ := by ring

lemma hasFDerivAt_gtHalfBaseDenominator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    HasFDerivAt (gtHalfBaseDenominator V L)
      (∫ z : I → ℝ,
        fderiv ℝ (gtHalfBaseDensity V)
          (L (WithLp.toLp 2 z) + H)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) H := by
  let μ : Measure (I → ℝ) := Measure.pi (fun _ : I => gaussianReal 0 1)
  let F : GTStateSpace S → (I → ℝ) → ℝ := fun H' z =>
    gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H')
  let F' : GTStateSpace S → (I → ℝ) →
      (GTStateSpace S →L[ℝ] ℝ) := fun H' z =>
    fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H')
  let c : ℝ := (hasModerateGrowth_gtStateLogPartition V).C *
    (2 + ‖L‖ + ‖H‖)
  let bound : (I → ℝ) → ℝ := fun z =>
    (1 / 2 : ℝ) * Real.exp
      (c * (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))
  have hbound : Integrable bound μ := by
    have hi := integrable_gtHalfBaseDensity_affine_local_bound V L H
    exact hi.const_mul (1 / 2 : ℝ)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := F) (F' := F') (x₀ := H)
    (bound := bound) (s := Metric.ball H 1)
    (Metric.ball_mem_nhds H (by norm_num))
    (Filter.Eventually.of_forall fun H' => by
      exact (integrable_gtHalfBaseDenominator_integrand V L H').1)
    (integrable_gtHalfBaseDenominator_integrand V L H)
    (by
      have hc : Continuous (F' H) := by
        dsimp [F']
        have hfd : ContDiff ℝ 0 (fderiv ℝ (gtHalfBaseDensity V)) :=
          (contDiff_gtHalfBaseDensity V).fderiv_right
            (m := (0 : WithTop ℕ∞)) (by simp)
        exact hfd.continuous.comp (by fun_prop)
      exact (hc.measurable.comp (by fun_prop)).aestronglyMeasurable)
    (ae_of_all μ fun z H' hH' => by
      have hnear : ‖H' - H‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hH'
      calc
        ‖F' H' z‖ ≤ (1 / 2 : ℝ) *
            gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') :=
          norm_fderiv_gtHalfBaseDensity_le V _
        _ ≤ bound z := by
          dsimp [bound, c]
          gcongr
          exact gtHalfBaseDensity_affine_local_bound V L H H'
            (WithLp.toLp 2 z) hnear)
    hbound
    (ae_of_all μ fun z H' _ => by
      have hd : HasFDerivAt (gtHalfBaseDensity V)
          (fderiv ℝ (gtHalfBaseDensity V)
            (L (WithLp.toLp 2 z) + H'))
          (L (WithLp.toLp 2 z) + H') :=
        ((contDiff_gtHalfBaseDensity V).differentiable (by simp)
          ).differentiableAt.hasFDerivAt
      exact hd.comp H'
        ((ContinuousLinearMap.id ℝ (GTStateSpace S)).hasFDerivAt.const_add
          (L (WithLp.toLp 2 z))))
  change HasFDerivAt
    (fun H' => ∫ z : I → ℝ,
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H')
      ∂Measure.pi (fun _ : I => gaussianReal 0 1))
    (∫ z : I → ℝ,
      fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) H
  exact hmain

lemma hasFDerivAt_gtHalfBaseNumerator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    HasFDerivAt (fun H' => gtHalfBaseNumerator V L H' ξ)
      (∫ z : I → ℝ,
        fderiv ℝ (fun K : GTStateSpace S =>
          gtHalfBaseDensity V K * gtStateGibbs V K ξ)
          (L (WithLp.toLp 2 z) + H)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) H := by
  let μ : Measure (I → ℝ) := Measure.pi (fun _ : I => gaussianReal 0 1)
  let G : GTStateSpace S → ℝ := fun K =>
    gtHalfBaseDensity V K * gtStateGibbs V K ξ
  let F : GTStateSpace S → (I → ℝ) → ℝ := fun H' z =>
    G (L (WithLp.toLp 2 z) + H')
  let F' : GTStateSpace S → (I → ℝ) →
      (GTStateSpace S →L[ℝ] ℝ) := fun H' z =>
    fderiv ℝ G (L (WithLp.toLp 2 z) + H')
  let c : ℝ := (hasModerateGrowth_gtStateLogPartition V).C *
    (2 + ‖L‖ + ‖H‖)
  let bound : (I → ℝ) → ℝ := fun z =>
    2 * Real.exp
      (c * (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))
  have hbound : Integrable bound μ := by
    have hi := integrable_gtHalfBaseDensity_affine_local_bound V L H
    exact hi.const_mul 2
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := F) (F' := F') (x₀ := H)
    (bound := bound) (s := Metric.ball H 1)
    (Metric.ball_mem_nhds H (by norm_num))
    (Filter.Eventually.of_forall fun H' => by
      exact (integrable_gtHalfBaseNumerator_integrand V L H' ξ).1)
    (integrable_gtHalfBaseNumerator_integrand V L H ξ)
    (by
      have hfd : ContDiff ℝ 0 (fderiv ℝ G) :=
        (contDiff_gtHalfBaseDensity_mul_gibbs V ξ).fderiv_right
          (m := (0 : WithTop ℕ∞)) (by simp)
      exact ((hfd.continuous.comp (by fun_prop)).measurable.comp
        (by fun_prop)).aestronglyMeasurable)
    (ae_of_all μ fun z H' hH' => by
      have hnear : ‖H' - H‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hH'
      calc
        ‖F' H' z‖ ≤ 2 *
            gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') :=
          norm_fderiv_gtHalfBaseDensity_mul_gibbs_le V _ ξ
        _ ≤ bound z := by
          dsimp [bound, c]
          gcongr
          exact gtHalfBaseDensity_affine_local_bound V L H H'
            (WithLp.toLp 2 z) hnear)
    hbound
    (ae_of_all μ fun z H' _ => by
      have hd : HasFDerivAt G
          (fderiv ℝ G (L (WithLp.toLp 2 z) + H'))
          (L (WithLp.toLp 2 z) + H') :=
        ((contDiff_gtHalfBaseDensity_mul_gibbs V ξ).differentiable (by simp)
          ).differentiableAt.hasFDerivAt
      exact hd.comp H'
        ((ContinuousLinearMap.id ℝ (GTStateSpace S)).hasFDerivAt.const_add
          (L (WithLp.toLp 2 z))))
  change HasFDerivAt
    (fun H' => ∫ z : I → ℝ,
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') *
        gtStateGibbs V (L (WithLp.toLp 2 z) + H') ξ
      ∂Measure.pi (fun _ : I => gaussianReal 0 1))
    (∫ z : I → ℝ,
      fderiv ℝ (fun K : GTStateSpace S =>
        gtHalfBaseDensity V K * gtStateGibbs V K ξ)
        (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) H
  exact hmain

lemma gtHalfBaseDenominator_pos
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    0 < gtHalfBaseDenominator V L H := by
  unfold gtHalfBaseDenominator
  rw [integral_pos_iff_support_of_nonneg
    (fun z => (gtHalfBaseDensity_pos V _).le)
    (integrable_gtHalfBaseDenominator_integrand V L H)]
  have hsupp : Function.support (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H)) = Set.univ := by
    ext z
    simp [Function.mem_support, (gtHalfBaseDensity_pos V _).ne']
  rw [hsupp]
  simp

lemma integrable_fderiv_gtHalfBaseDensity_affine
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    Integrable (fun z : I → ℝ =>
      fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  have hd := integrable_gtHalfBaseDenominator_integrand V L H
  apply (hd.const_mul (1 / 2 : ℝ)).mono'
  · have hfd : ContDiff ℝ 0 (fderiv ℝ (gtHalfBaseDensity V)) :=
      (contDiff_gtHalfBaseDensity V).fderiv_right
        (m := (0 : WithTop ℕ∞)) (by simp)
    exact (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    simpa [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg (gtHalfBaseDensity_pos V _).le] using
      norm_fderiv_gtHalfBaseDensity_le V (L (WithLp.toLp 2 z) + H)

lemma integrable_fderiv_gtHalfBaseDensity_mul_gibbs_affine
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    Integrable (fun z : I → ℝ =>
      fderiv ℝ (fun K : GTStateSpace S =>
        gtHalfBaseDensity V K * gtStateGibbs V K ξ)
        (L (WithLp.toLp 2 z) + H))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  have hd := integrable_gtHalfBaseDenominator_integrand V L H
  apply (hd.const_mul 2).mono'
  · have hfd : ContDiff ℝ 0 (fderiv ℝ (fun K : GTStateSpace S =>
        gtHalfBaseDensity V K * gtStateGibbs V K ξ)) :=
      (contDiff_gtHalfBaseDensity_mul_gibbs V ξ).fderiv_right
        (m := (0 : WithTop ℕ∞)) (by simp)
    exact (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    simpa [Real.norm_eq_abs, abs_of_nonneg (gtHalfBaseDensity_pos V _).le] using
      norm_fderiv_gtHalfBaseDensity_mul_gibbs_le V
        (L (WithLp.toLp 2 z) + H) ξ

lemma gtHalfBaseDenominator_fderiv_apply
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H K : GTStateSpace S) :
    (∫ z : I → ℝ,
      fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) K =
      (1 / 2 : ℝ) * ∑ η : S,
        gtHalfBaseNumerator V L H η * K η := by
  let ev : (GTStateSpace S →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ K
  have hi := integrable_fderiv_gtHalfBaseDensity_affine V L H
  change ev (∫ z : I → ℝ,
    fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H)
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)) = _
  rw [← ev.integral_comp_comm hi]
  dsimp [ev]
  simp_rw [fderiv_gtHalfBaseDensity_apply]
  rw [show (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) * (1 / 2 : ℝ) *
        ∑ η : S, gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * K η) =
      fun z => ∑ η : S, ((1 / 2 : ℝ) * K η) *
        (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    unfold gtHalfBaseNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring
  · intro η _
    exact (integrable_gtHalfBaseNumerator_integrand V L H η
      ).const_mul ((1 / 2 : ℝ) * K η)

lemma gtHalfBaseNumerator_fderiv_apply
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H K : GTStateSpace S) (ξ : S) :
    (∫ z : I → ℝ,
      fderiv ℝ (fun J : GTStateSpace S =>
        gtHalfBaseDensity V J * gtStateGibbs V J ξ)
        (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) K =
      gtHalfBaseNumerator V L H ξ * K ξ -
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfBasePairNumerator V L H ξ η * K η := by
  let ev : (GTStateSpace S →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ K
  have hi := integrable_fderiv_gtHalfBaseDensity_mul_gibbs_affine V L H ξ
  change ev (∫ z : I → ℝ,
    fderiv ℝ (fun J : GTStateSpace S =>
      gtHalfBaseDensity V J * gtStateGibbs V J ξ)
      (L (WithLp.toLp 2 z) + H)
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)) = _
  rw [← ev.integral_comp_comm hi]
  dsimp [ev]
  simp_rw [fderiv_gtHalfBaseDensity_mul_gibbs_apply]
  have hfirst :
      (∫ z : I → ℝ,
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ * K ξ
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
        gtHalfBaseNumerator V L H ξ * K ξ := by
    rw [integral_mul_const]
    rfl
  have hsecond :
      (∫ z : I → ℝ,
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
          ((1 / 2 : ℝ) * ∑ η : S,
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * K η)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfBasePairNumerator V L H ξ η * K η := by
    rw [show (fun z : I → ℝ =>
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
          ((1 / 2 : ℝ) * ∑ η : S,
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * K η)) =
        fun z => ∑ η : S, ((1 / 2 : ℝ) * K η) *
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
            (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)) by
      funext z
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring]
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
      unfold gtHalfBasePairNumerator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring
    · intro η _
      exact (integrable_gtHalfBasePairNumerator_integrand V L H ξ η
        ).const_mul ((1 / 2 : ℝ) * K η)
  rw [show (fun z : I → ℝ =>
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
        gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
          (K ξ - (1 / 2 : ℝ) * ∑ η : S,
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * K η)) =
      fun z =>
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ * K ξ -
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            ((1 / 2 : ℝ) * ∑ η : S,
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * K η) by
        funext z
        ring]
  rw [integral_sub]
  · rw [hfirst, hsecond]
  · exact (integrable_gtHalfBaseNumerator_integrand V L H ξ).mul_const (K ξ)
  · have hs : Integrable (fun z : I → ℝ =>
        ∑ η : S, (1 / 2 : ℝ) * K η *
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
            (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)))
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
      integrable_finset_sum _ fun η _ =>
        (integrable_gtHalfBasePairNumerator_integrand V L H ξ η
          ).const_mul ((1 / 2 : ℝ) * K η)
    convert hs using 1
    funext z
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring

/-- A Gibbs coordinate after the normalized inner half-mass tilt, expressed
as a function of the deterministic base field. -/
noncomputable def gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) : ℝ :=
  gtHalfBaseNumerator V L H ξ / gtHalfBaseDenominator V L H

noncomputable def gtHalfBasePairWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ η : S) : ℝ :=
  gtHalfBasePairNumerator V L H ξ η / gtHalfBaseDenominator V L H

lemma hasFDerivAt_gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    HasFDerivAt (fun H' => gtHalfBaseWeight V L H' ξ)
      (fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H) H := by
  have hn := hasFDerivAt_gtHalfBaseNumerator V L H ξ
  have hd := hasFDerivAt_gtHalfBaseDenominator V L H
  have hi := hd.differentiableAt.inv (gtHalfBaseDenominator_pos V L H).ne'
  have hm := hn.differentiableAt.mul hi
  change HasFDerivAt
    ((fun H' => gtHalfBaseNumerator V L H' ξ) *
      (gtHalfBaseDenominator V L)⁻¹)
    (fderiv ℝ ((fun H' => gtHalfBaseNumerator V L H' ξ) *
      (gtHalfBaseDenominator V L)⁻¹) H) H
  exact hm.hasFDerivAt

lemma fderiv_gtHalfBaseWeight_apply
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H K : GTStateSpace S) (ξ : S) :
    fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H K =
      gtHalfBaseWeight V L H ξ * K ξ -
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfBasePairWeight V L H ξ η * K η -
        (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
          ∑ η : S, gtHalfBaseWeight V L H η * K η := by
  let D : ℝ := gtHalfBaseDenominator V L H
  let Nξ : ℝ := gtHalfBaseNumerator V L H ξ
  let DN : GTStateSpace S →L[ℝ] ℝ :=
    ∫ z : I → ℝ,
      fderiv ℝ (fun J : GTStateSpace S =>
        gtHalfBaseDensity V J * gtStateGibbs V J ξ)
        (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)
  let DD : GTStateSpace S →L[ℝ] ℝ :=
    ∫ z : I → ℝ,
      fderiv ℝ (gtHalfBaseDensity V) (L (WithLp.toLp 2 z) + H)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)
  have hD : 0 < D := gtHalfBaseDenominator_pos V L H
  have ha : HasDerivAt (fun t : ℝ => H + t • K) K 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add H
  have hn : HasFDerivAt (fun H' => gtHalfBaseNumerator V L H' ξ) DN H :=
    hasFDerivAt_gtHalfBaseNumerator V L H ξ
  have hd : HasFDerivAt (gtHalfBaseDenominator V L) DD H :=
    hasFDerivAt_gtHalfBaseDenominator V L H
  have hnline := by
    have hn0 : HasFDerivAt (fun H' => gtHalfBaseNumerator V L H' ξ) DN
        (H + (0 : ℝ) • K) := by simpa using hn
    exact hn0.comp_hasDerivAt 0 ha
  have hdline := by
    have hd0 : HasFDerivAt (gtHalfBaseDenominator V L) DD
        (H + (0 : ℝ) • K) := by simpa using hd
    exact hd0.comp_hasDerivAt 0 ha
  have hD0 : gtHalfBaseDenominator V L (H + (0 : ℝ) • K) ≠ 0 := by
    simpa using hD.ne'
  have hquot := hnline.div hdline hD0
  have hwline := by
      have hw0 : HasFDerivAt (fun H' => gtHalfBaseWeight V L H' ξ)
          (fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H)
          (H + (0 : ℝ) • K) := by
        simpa using hasFDerivAt_gtHalfBaseWeight V L H ξ
      exact hw0.comp_hasDerivAt 0 ha
  have heq := hwline.unique hquot
  have hDN : DN K = Nξ * K ξ - (1 / 2 : ℝ) * ∑ η : S,
      gtHalfBasePairNumerator V L H ξ η * K η :=
    gtHalfBaseNumerator_fderiv_apply V L H K ξ
  have hDD : DD K = (1 / 2 : ℝ) * ∑ η : S,
      gtHalfBaseNumerator V L H η * K η :=
    gtHalfBaseDenominator_fderiv_apply V L H K
  rw [hDN, hDD] at heq
  rw [heq]
  unfold gtHalfBaseWeight gtHalfBasePairWeight
  dsimp [D, Nξ] at hD ⊢
  simp only [zero_smul, add_zero] at heq ⊢
  simp_rw [Finset.mul_sum]
  field_simp [hD.ne']
  simp_rw [Finset.mul_sum]
  field_simp [hD.ne']
  have hcancel :
      gtHalfBaseDenominator V L H *
          ∑ x : S,
            gtHalfBaseNumerator V L H ξ * gtHalfBaseNumerator V L H x * K x /
              (2 * gtHalfBaseDenominator V L H) =
        ∑ x : S,
          gtHalfBaseNumerator V L H ξ * gtHalfBaseNumerator V L H x * K x / 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    field_simp [hD.ne']
  conv_rhs => rw [mul_sub, mul_sub]
  rw [hcancel]
  ring

lemma continuous_gtHalfBaseDenominator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) :
    Continuous (gtHalfBaseDenominator V L) := by
  exact continuous_iff_continuousAt.2 fun H =>
    (hasFDerivAt_gtHalfBaseDenominator V L H).continuousAt

lemma continuous_gtHalfBaseNumerator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ : S) :
    Continuous (fun H => gtHalfBaseNumerator V L H ξ) := by
  exact continuous_iff_continuousAt.2 fun H =>
    (hasFDerivAt_gtHalfBaseNumerator V L H ξ).continuousAt

lemma continuous_gtHalfBasePairNumerator
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ η : S) :
    Continuous (fun H => gtHalfBasePairNumerator V L H ξ η) := by
  rw [continuous_iff_continuousAt]
  intro H
  let bound : (I → ℝ) → ℝ := fun z =>
    Real.exp ((hasModerateGrowth_gtStateLogPartition V).C *
      (2 + ‖L‖ + ‖H‖) *
        (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖))
  apply MeasureTheory.continuousAt_of_dominated
  · filter_upwards with H'
    exact (integrable_gtHalfBasePairNumerator_integrand V L H' ξ η).1
  · filter_upwards [Metric.ball_mem_nhds H one_pos] with H' hH'
    filter_upwards with z
    have hnear : ‖H' - H‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hH'
    have hd := gtHalfBaseDensity_affine_local_bound V L H H'
      (WithLp.toLp 2 z) hnear
    have hξ0 := gtStateGibbs_nonneg V (L (WithLp.toLp 2 z) + H') ξ
    have hξ1 := gtStateGibbs_le_one V (L (WithLp.toLp 2 z) + H') ξ
    have hη0 := gtStateGibbs_nonneg V (L (WithLp.toLp 2 z) + H') η
    have hη1 := gtStateGibbs_le_one V (L (WithLp.toLp 2 z) + H') η
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (gtHalfBaseDensity_pos V _).le,
      abs_of_nonneg hξ0, abs_of_nonneg hη0]
    calc
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') *
          (gtStateGibbs V (L (WithLp.toLp 2 z) + H') ξ *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H') η) ≤
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') * 1 := by
          apply mul_le_mul_of_nonneg_left _
            (gtHalfBaseDensity_pos V (L (WithLp.toLp 2 z) + H')).le
          calc
            gtStateGibbs V (L (WithLp.toLp 2 z) + H') ξ *
                gtStateGibbs V (L (WithLp.toLp 2 z) + H') η ≤
              1 * gtStateGibbs V (L (WithLp.toLp 2 z) + H') η :=
                mul_le_mul_of_nonneg_right hξ1 hη0
            _ ≤ 1 := by simpa using hη1
      _ = gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H') := mul_one _
      _ ≤ bound z := hd
  · exact integrable_gtHalfBaseDensity_affine_local_bound V L H
  · filter_upwards with z
    exact (((contDiff_gtHalfBaseDensity V).continuous.comp (by fun_prop)).mul
      (((contDiff_gtStateGibbs V ξ).continuous.comp (by fun_prop)).mul
        ((contDiff_gtStateGibbs V η).continuous.comp (by fun_prop)))).continuousAt

lemma continuous_gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ : S) :
    Continuous (fun H => gtHalfBaseWeight V L H ξ) := by
  unfold gtHalfBaseWeight
  exact (continuous_gtHalfBaseNumerator V L ξ).div
    (continuous_gtHalfBaseDenominator V L)
    (fun H => (gtHalfBaseDenominator_pos V L H).ne')

lemma continuous_gtHalfBasePairWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ η : S) :
    Continuous (fun H => gtHalfBasePairWeight V L H ξ η) := by
  unfold gtHalfBasePairWeight
  exact (continuous_gtHalfBasePairNumerator V L ξ η).div
    (continuous_gtHalfBaseDenominator V L)
    (fun H => (gtHalfBaseDenominator_pos V L H).ne')

lemma contDiff_gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ : S) :
    ContDiff ℝ 1 (fun H => gtHalfBaseWeight V L H ξ) := by
  classical
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun H => (hasFDerivAt_gtHalfBaseWeight V L H ξ).differentiableAt, ?_⟩
  change Continuous (fun H =>
    fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H)
  rw [show (fun H => fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H) =
      fun H => ∑ κ : S,
        (gtHalfBaseWeight V L H ξ * (if κ = ξ then 1 else 0) -
          (1 / 2 : ℝ) * gtHalfBasePairWeight V L H ξ κ -
          (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
            gtHalfBaseWeight V L H κ) •
          (EuclideanSpace.proj κ : GTStateSpace S →L[ℝ] ℝ) by
    funext H
    ext K
    rw [fderiv_gtHalfBaseWeight_apply]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [PiLp.proj_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hite : (∑ x : S, (if x = ξ then (1 : ℝ) else 0) * K x) = K ξ := by
      rw [Finset.sum_eq_single ξ]
      · simp
      · intro b hb hbξ
        simp [hbξ]
      · simp
    rw [hite]
    have hsum :
        (∑ x : S, (1 / 2 : ℝ) *
          (gtHalfBaseWeight V L H ξ *
            (gtHalfBaseWeight V L H x * K x))) =
        (1 / 2 : ℝ) * (gtHalfBaseWeight V L H ξ *
          ∑ x : S, gtHalfBaseWeight V L H x * K x) := by
      rw [show (1 / 2 : ℝ) * (gtHalfBaseWeight V L H ξ *
          ∑ x : S, gtHalfBaseWeight V L H x * K x) =
        ((1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ) *
          ∑ x : S, gtHalfBaseWeight V L H x * K x by ring]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hsum]]
  apply continuous_finset_sum
  intro κ hκ
  have hc : Continuous (fun H =>
      gtHalfBaseWeight V L H ξ * (if κ = ξ then 1 else 0) -
        (1 / 2 : ℝ) * gtHalfBasePairWeight V L H ξ κ -
        (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
          gtHalfBaseWeight V L H κ) :=
    ((((continuous_gtHalfBaseWeight V L ξ).mul continuous_const).sub
    (continuous_const.mul (continuous_gtHalfBasePairWeight V L ξ κ))).sub
      ((continuous_const.mul (continuous_gtHalfBaseWeight V L ξ)).mul
        (continuous_gtHalfBaseWeight V L κ)))
  exact hc.smul continuous_const

lemma gtHalfBaseWeight_nonneg
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) : 0 ≤ gtHalfBaseWeight V L H ξ := by
  unfold gtHalfBaseWeight gtHalfBaseNumerator
  exact div_nonneg (integral_nonneg fun z =>
    mul_nonneg (gtHalfBaseDensity_pos V _).le (gtStateGibbs_nonneg V _ ξ))
    (gtHalfBaseDenominator_pos V L H).le

lemma sum_gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) : ∑ ξ : S, gtHalfBaseWeight V L H ξ = 1 := by
  classical
  unfold gtHalfBaseWeight gtHalfBaseNumerator
  rw [← Finset.sum_div, ← integral_finset_sum]
  · simp_rw [← Finset.mul_sum, sum_gtStateGibbs, mul_one]
    exact div_self (gtHalfBaseDenominator_pos V L H).ne'
  · intro ξ hξ
    exact integrable_gtHalfBaseNumerator_integrand V L H ξ

lemma gtHalfBasePairWeight_nonneg
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ η : S) : 0 ≤ gtHalfBasePairWeight V L H ξ η := by
  unfold gtHalfBasePairWeight gtHalfBasePairNumerator
  exact div_nonneg (integral_nonneg fun z =>
    mul_nonneg (gtHalfBaseDensity_pos V _).le
      (mul_nonneg (gtStateGibbs_nonneg V _ ξ) (gtStateGibbs_nonneg V _ η)))
    (gtHalfBaseDenominator_pos V L H).le

lemma sum_gtHalfBasePairWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) :
    ∑ ξ : S, ∑ η : S, gtHalfBasePairWeight V L H ξ η = 1 := by
  classical
  unfold gtHalfBasePairWeight gtHalfBasePairNumerator
  simp_rw [← Finset.sum_div]
  rw [div_eq_iff (gtHalfBaseDenominator_pos V L H).ne']
  simp only [one_mul]
  rw [Finset.sum_comm]
  calc
    (∑ η : S, ∑ ξ : S, ∫ z : I → ℝ,
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∑ η : S, ∫ z : I → ℝ, ∑ ξ : S,
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
          apply Finset.sum_congr rfl
          intro η hη
          rw [integral_finset_sum]
          intro ξ hξ
          exact integrable_gtHalfBasePairNumerator_integrand V L H ξ η
    _ = ∫ z : I → ℝ, ∑ η : S, ∑ ξ : S,
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
          rw [integral_finset_sum]
          intro η hη
          exact integrable_finset_sum _ fun ξ hξ =>
            integrable_gtHalfBasePairNumerator_integrand V L H ξ η
    _ = gtHalfBaseDenominator V L H := by
      unfold gtHalfBaseDenominator
      apply integral_congr_ae
      filter_upwards with z
      have hinner (η : S) :
          (∑ ξ : S, gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
            (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)) =
            gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η := by
        rw [show (∑ ξ : S, gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)) =
            (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) *
                ∑ ξ : S, gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ξ hξ
          ring]
        rw [sum_gtStateGibbs, mul_one]
      simp_rw [hinner]
      rw [← Finset.mul_sum, sum_gtStateGibbs, mul_one]

lemma gtHalfBaseWeight_le_one
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) : gtHalfBaseWeight V L H ξ ≤ 1 := by
  rw [← sum_gtHalfBaseWeight V L H]
  exact Finset.single_le_sum (fun η hη => gtHalfBaseWeight_nonneg V L H η)
    (Finset.mem_univ ξ)

lemma gtHalfBasePairWeight_le_one
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ η : S) : gtHalfBasePairWeight V L H ξ η ≤ 1 := by
  rw [← sum_gtHalfBasePairWeight V L H]
  calc
    gtHalfBasePairWeight V L H ξ η ≤
        ∑ η' : S, gtHalfBasePairWeight V L H ξ η' :=
      Finset.single_le_sum (fun η' hη' => gtHalfBasePairWeight_nonneg V L H ξ η')
        (Finset.mem_univ η)
    _ ≤ ∑ ξ' : S, ∑ η' : S, gtHalfBasePairWeight V L H ξ' η' :=
      Finset.single_le_sum (fun ξ' hξ' => Finset.sum_nonneg fun η' hη' =>
        gtHalfBasePairWeight_nonneg V L H ξ' η') (Finset.mem_univ ξ)

lemma norm_fderiv_gtHalfBaseWeight_le_two
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    ‖fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) H‖ ≤ 2 := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro K
  rw [Real.norm_eq_abs, fderiv_gtHalfBaseWeight_apply]
  have hcoord (η : S) : |K η| ≤ ‖K‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K η
  have hwavg : |∑ η : S, gtHalfBaseWeight V L H η * K η| ≤ ‖K‖ := by
    calc
      |∑ η : S, gtHalfBaseWeight V L H η * K η| ≤
          ∑ η : S, |gtHalfBaseWeight V L H η * K η| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ η : S, gtHalfBaseWeight V L H η * |K η| := by
        apply Finset.sum_congr rfl
        intro η hη
        rw [abs_mul, abs_of_nonneg (gtHalfBaseWeight_nonneg V L H η)]
      _ ≤ ∑ η : S, gtHalfBaseWeight V L H η * ‖K‖ := by
        exact Finset.sum_le_sum fun η hη =>
          mul_le_mul_of_nonneg_left (hcoord η) (gtHalfBaseWeight_nonneg V L H η)
      _ = ‖K‖ := by rw [← Finset.sum_mul, sum_gtHalfBaseWeight, one_mul]
  have hpavg : |∑ η : S, gtHalfBasePairWeight V L H ξ η * K η| ≤ ‖K‖ := by
    have hrow : ∑ η : S, gtHalfBasePairWeight V L H ξ η ≤ 1 := by
      rw [← sum_gtHalfBasePairWeight V L H]
      exact Finset.single_le_sum (fun ξ' hξ' => Finset.sum_nonneg fun η hη =>
        gtHalfBasePairWeight_nonneg V L H ξ' η) (Finset.mem_univ ξ)
    calc
      |∑ η : S, gtHalfBasePairWeight V L H ξ η * K η| ≤
          ∑ η : S, |gtHalfBasePairWeight V L H ξ η * K η| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ η : S, gtHalfBasePairWeight V L H ξ η * |K η| := by
        apply Finset.sum_congr rfl
        intro η hη
        rw [abs_mul, abs_of_nonneg (gtHalfBasePairWeight_nonneg V L H ξ η)]
      _ ≤ ∑ η : S, gtHalfBasePairWeight V L H ξ η * ‖K‖ := by
        exact Finset.sum_le_sum fun η hη =>
          mul_le_mul_of_nonneg_left (hcoord η)
            (gtHalfBasePairWeight_nonneg V L H ξ η)
      _ = (∑ η : S, gtHalfBasePairWeight V L H ξ η) * ‖K‖ :=
        (Finset.sum_mul ..).symm
      _ ≤ ‖K‖ := by
        simpa using mul_le_mul_of_nonneg_right hrow (norm_nonneg K)
  have hw0 := gtHalfBaseWeight_nonneg V L H ξ
  have hw1 := gtHalfBaseWeight_le_one V L H ξ
  calc
    |gtHalfBaseWeight V L H ξ * K ξ -
        (1 / 2 : ℝ) * ∑ η : S, gtHalfBasePairWeight V L H ξ η * K η -
        (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
          ∑ η : S, gtHalfBaseWeight V L H η * K η| ≤
      |gtHalfBaseWeight V L H ξ * K ξ| +
        |(1 / 2 : ℝ) * ∑ η : S, gtHalfBasePairWeight V L H ξ η * K η| +
        |(1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
          ∑ η : S, gtHalfBaseWeight V L H η * K η| := by
            exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ ‖K‖ + (1 / 2 : ℝ) * ‖K‖ + (1 / 2 : ℝ) * ‖K‖ := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hw0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have ht1 : gtHalfBaseWeight V L H ξ * |K ξ| ≤ ‖K‖ := by
        calc
          gtHalfBaseWeight V L H ξ * |K ξ| ≤ 1 * |K ξ| :=
            mul_le_mul_of_nonneg_right hw1 (abs_nonneg _)
          _ ≤ ‖K‖ := by simpa using hcoord ξ
      have ht2 : (1 / 2 : ℝ) *
          |∑ η : S, gtHalfBasePairWeight V L H ξ η * K η| ≤
          (1 / 2 : ℝ) * ‖K‖ := mul_le_mul_of_nonneg_left hpavg (by norm_num)
      have ht3 : (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
          |∑ η : S, gtHalfBaseWeight V L H η * K η| ≤
          (1 / 2 : ℝ) * ‖K‖ := by
        calc
          (1 / 2 : ℝ) * gtHalfBaseWeight V L H ξ *
              |∑ η : S, gtHalfBaseWeight V L H η * K η| ≤
            (1 / 2 : ℝ) * 1 *
              |∑ η : S, gtHalfBaseWeight V L H η * K η| := by
                gcongr
          _ ≤ (1 / 2 : ℝ) * ‖K‖ := by
            simpa using mul_le_mul_of_nonneg_left hwavg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact add_le_add (add_le_add ht1 ht2) ht3
    _ = 2 * ‖K‖ := by ring

noncomputable def hasModerateGrowth_gtHalfBaseWeight
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S) (ξ : S) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun H => gtHalfBaseWeight V L H ξ) := by
  refine ⟨3, 0, by norm_num, ?_, ?_⟩
  · intro H
    rw [pow_zero, mul_one, abs_of_nonneg (gtHalfBaseWeight_nonneg V L H ξ)]
    exact (gtHalfBaseWeight_le_one V L H ξ).trans (by norm_num)
  · intro H
    rw [pow_zero, mul_one]
    exact (norm_fderiv_gtHalfBaseWeight_le_two V L H ξ).trans (by norm_num)

noncomputable def hasModerateGrowth_gtHalfBaseWeight_comp
    {S I J : Type*} [Fintype S] [Nonempty S] [Fintype I] [Fintype J]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (M : EuclideanSpace ℝ J →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (ξ : S) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun z => gtHalfBaseWeight V L (M z + H) ξ) := by
  let C : ℝ := 3 * (‖M‖ + 1)
  refine ⟨C, 0, by dsimp [C]; positivity, ?_, ?_⟩
  · intro z
    rw [pow_zero, mul_one, abs_of_nonneg (gtHalfBaseWeight_nonneg V L _ ξ)]
    calc
      gtHalfBaseWeight V L (M z + H) ξ ≤ 1 := gtHalfBaseWeight_le_one V L _ ξ
      _ ≤ C := by dsimp [C]; nlinarith [norm_nonneg M]
  · intro z
    have hg := hasFDerivAt_gtHalfBaseWeight V L (M z + H) ξ
    have hc := hg.comp z (M.hasFDerivAt.add_const H)
    have hf := hc.fderiv
    change fderiv ℝ (fun z => gtHalfBaseWeight V L (M z + H) ξ) z = _ at hf
    rw [hf, pow_zero, mul_one]
    calc
      ‖(fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) (M z + H)).comp M‖ ≤
          ‖fderiv ℝ (fun H' => gtHalfBaseWeight V L H' ξ) (M z + H)‖ * ‖M‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * ‖M‖ := by
        gcongr
        exact norm_fderiv_gtHalfBaseWeight_le_two V L (M z + H) ξ
      _ ≤ C := by dsimp [C]; nlinarith [norm_nonneg M]

/-- Directional Stein identity for a half-mass averaged Gibbs coordinate in
an affine outer Gaussian field. -/
lemma gtHalfBaseWeight_stein
    {S I J : Type*} [Fintype S] [Nonempty S] [Fintype I] [Fintype J]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (M : EuclideanSpace ℝ J →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (a : EuclideanSpace ℝ J) (ξ : S) :
    (∫ z : J → ℝ,
        inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ J) a *
          gtHalfBaseWeight V L (M (WithLp.toLp 2 z) + H) ξ
        ∂Measure.pi (fun _ : J => gaussianReal 0 1)) =
      ∫ z : J → ℝ,
        (gtHalfBaseWeight V L (M (WithLp.toLp 2 z) + H) ξ * (M a) ξ -
          (1 / 2 : ℝ) * ∑ η : S,
            gtHalfBasePairWeight V L (M (WithLp.toLp 2 z) + H) ξ η * (M a) η -
          (1 / 2 : ℝ) * gtHalfBaseWeight V L (M (WithLp.toLp 2 z) + H) ξ *
            ∑ η : S,
              gtHalfBaseWeight V L (M (WithLp.toLp 2 z) + H) η * (M a) η)
        ∂Measure.pi (fun _ : J => gaussianReal 0 1) := by
  let F : EuclideanSpace ℝ J → ℝ := fun z =>
    gtHalfBaseWeight V L (M z + H) ξ
  have hFdiff : ContDiff ℝ 1 F :=
    (contDiff_gtHalfBaseWeight V L ξ).comp
      (M.contDiff.add (contDiff_const : ContDiff ℝ 1
        (fun _ : EuclideanSpace ℝ J => H)))
  have hibp := gaussianProduct_stein_inner a F hFdiff
    (hasModerateGrowth_gtHalfBaseWeight_comp V L M H ξ)
  rw [hibp]
  apply integral_congr_ae
  filter_upwards with z
  have hg := hasFDerivAt_gtHalfBaseWeight V L (M (WithLp.toLp 2 z) + H) ξ
  have hc := hg.comp (WithLp.toLp 2 z) (M.hasFDerivAt.add_const H)
  have hf := hc.fderiv
  change fderiv ℝ F (WithLp.toLp 2 z) = _ at hf
  rw [hf]
  exact fderiv_gtHalfBaseWeight_apply V L (M (WithLp.toLp 2 z) + H) (M a) ξ

lemma euclidean_norm_toLp_le_sum_abs
    {I : Type*} [Fintype I] (z : I → ℝ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖ ≤ ∑ i : I, |z i| := by
  rw [EuclideanSpace.norm_eq]
  have hsum0 : (0 : ℝ) ≤ ∑ i : I, |z i| :=
    Finset.sum_nonneg fun i hi => abs_nonneg _
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i hi => abs_nonneg (z i))

/-- Stein identity in the inner Gaussian coordinate.  The tilted density has
exponential (rather than polynomial) growth, so this uses the product-Gaussian
Stein theorem with exponential domination. -/
lemma gtHalfBase_inner_stein
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H : GTStateSpace S) (a : EuclideanSpace ℝ I) (ξ : S) :
    (∫ z : I → ℝ,
        inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a *
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
              gtHalfBaseDenominator V L H)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      gtHalfBaseWeight V L H ξ * (L a) ξ -
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfBasePairWeight V L H ξ η * (L a) η := by
  classical
  let D : ℝ := gtHalfBaseDenominator V L H
  let hfun : (I → ℝ) → ℝ := fun z =>
    gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
      gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D
  let c : ℝ := (hasModerateGrowth_gtStateLogPartition V).C *
    (2 + ‖L‖ + ‖H‖)
  let C : ℝ := Real.exp c * (2 * ‖L‖ + 1) / D
  have hD : 0 < D := gtHalfBaseDenominator_pos V L H
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (hasModerateGrowth_gtStateLogPartition V).Cpos.le (by
      nlinarith [norm_nonneg L, norm_nonneg H])
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdensity (z : I → ℝ) :
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) ≤
        Real.exp c * Real.exp (c * ∑ i : I, |z i|) := by
    have hd := gtHalfBaseDensity_affine_local_bound V L H H
      (WithLp.toLp 2 z) (by simp)
    have hn := euclidean_norm_toLp_le_sum_abs z
    have he : c * (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖) ≤
        c + c * ∑ i : I, |z i| := by
      nlinarith
    calc
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) ≤
          Real.exp (c * (1 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)) := hd
      _ ≤ Real.exp (c + c * ∑ i : I, |z i|) := Real.exp_le_exp.mpr he
      _ = Real.exp c * Real.exp (c * ∑ i : I, |z i|) := Real.exp_add _ _
  have hcont : ContDiff ℝ 1 hfun := by
    dsimp [hfun]
    have hc : ContDiff ℝ ∞ (fun z : I → ℝ =>
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D) :=
      ((contDiff_gtHalfBaseDensity_mul_gibbs V ξ).comp
      ((L.contDiff.comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.contDiff).add
          (contDiff_const : ContDiff ℝ ∞ (fun _ : I → ℝ => H)))).div_const D
    exact hc.of_le (by norm_num)
  have hvalue (z : I → ℝ) :
      |hfun z| ≤ C * Real.exp (c * ∑ i : I, |z i|) := by
    have hg0 := gtStateGibbs_nonneg V (L (WithLp.toLp 2 z) + H) ξ
    have hg1 := gtStateGibbs_le_one V (L (WithLp.toLp 2 z) + H) ξ
    have hρ0 := (gtHalfBaseDensity_pos V (L (WithLp.toLp 2 z) + H)).le
    rw [show |hfun z| =
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D by
      dsimp [hfun]
      rw [abs_of_nonneg (div_nonneg (mul_nonneg hρ0 hg0) hD.le)]]
    have hfac : 1 ≤ 2 * ‖L‖ + 1 := by nlinarith [norm_nonneg L]
    calc
      gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D ≤
        gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) / D := by
          exact div_le_div_of_nonneg_right
            (mul_le_of_le_one_right hρ0 hg1) hD.le
      _ ≤ (Real.exp c * Real.exp (c * ∑ i : I, |z i|)) / D :=
        div_le_div_of_nonneg_right (hdensity z) hD.le
      _ ≤ (Real.exp c * (2 * ‖L‖ + 1) / D) *
          Real.exp (c * ∑ i : I, |z i|) := by
            have he0 := Real.exp_pos (c * ∑ i : I, |z i|)
            calc
              Real.exp c * Real.exp (c * ∑ i : I, |z i|) / D =
                  (Real.exp c / D) * Real.exp (c * ∑ i : I, |z i|) := by ring
              _ ≤ (Real.exp c * (2 * ‖L‖ + 1) / D) *
                  Real.exp (c * ∑ i : I, |z i|) := by
                    gcongr
                    exact (le_mul_of_one_le_right (Real.exp_pos c).le hfac)
      _ = C * Real.exp (c * ∑ i : I, |z i|) := rfl
  have hfderiv (z k : I → ℝ) :
      fderiv ℝ hfun z k =
        (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
            D) *
          ((L (WithLp.toLp 2 k)) ξ -
            (1 / 2 : ℝ) * ∑ η : S,
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η *
                (L (WithLp.toLp 2 k)) η) := by
    have hg : HasFDerivAt
        (fun J : GTStateSpace S =>
          gtHalfBaseDensity V J * gtStateGibbs V J ξ)
        (fderiv ℝ (fun J : GTStateSpace S =>
          gtHalfBaseDensity V J * gtStateGibbs V J ξ)
          (L (WithLp.toLp 2 z) + H)) (L (WithLp.toLp 2 z) + H) :=
      ((contDiff_gtHalfBaseDensity_mul_gibbs V ξ).differentiable (by simp)
        ).differentiableAt.hasFDerivAt
    have haff : HasFDerivAt (fun z : I → ℝ => L (WithLp.toLp 2 z) + H)
        (L.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap) z :=
      (L.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap
        ).hasFDerivAt.add_const H
    have hcomp := (hg.comp z haff).mul_const D⁻¹
    have heq := hcomp.fderiv
    change fderiv ℝ hfun z = _ at heq
    rw [heq]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul]
    rw [fderiv_gtHalfBaseDensity_mul_gibbs_apply]
    change D⁻¹ *
        (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            ((L (WithLp.toLp 2 k)) ξ -
              (1 / 2 : ℝ) * ∑ η : S,
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) η *
                  (L (WithLp.toLp 2 k)) η)) = _
    ring
  have hderiv (z : I → ℝ) (i : I) :
      |fderiv ℝ hfun z (Pi.single i 1)| ≤
        C * Real.exp (c * ∑ j : I, |z j|) := by
    have hk : ‖(WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ I)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [Pi.single_apply]
    have hLK := L.le_opNorm
      (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ I)
    rw [hk, mul_one] at hLK
    have hraw : |fderiv ℝ hfun z (Pi.single i 1)| ≤
        2 * gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) * ‖L‖ / D := by
      rw [hfderiv]
      rw [show
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D) *
            ((L (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ξ -
              (1 / 2 : ℝ) * ∑ η : S,
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) η *
                  (L (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) η) =
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
            ((L (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ξ -
              (1 / 2 : ℝ) * ∑ η : S,
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) η *
                  (L (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) η)) / D by ring]
      rw [← fderiv_gtHalfBaseDensity_mul_gibbs_apply]
      rw [abs_div, abs_of_pos hD, ← Real.norm_eq_abs]
      calc
        ‖(fderiv ℝ (fun J : GTStateSpace S =>
            gtHalfBaseDensity V J * gtStateGibbs V J ξ)
              (L (WithLp.toLp 2 z) + H))
            (L (WithLp.toLp 2 (Pi.single i (1 : ℝ))))‖ / D ≤
          (‖fderiv ℝ (fun J : GTStateSpace S =>
            gtHalfBaseDensity V J * gtStateGibbs V J ξ)
              (L (WithLp.toLp 2 z) + H)‖ *
            ‖L (WithLp.toLp 2 (Pi.single i (1 : ℝ)))‖) / D := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (2 * gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) * ‖L‖) / D := by
          apply div_le_div_of_nonneg_right _ hD.le
          exact mul_le_mul
            (norm_fderiv_gtHalfBaseDensity_mul_gibbs_le V
              (L (WithLp.toLp 2 z) + H) ξ) hLK
            (norm_nonneg _) (mul_nonneg (by positivity) (gtHalfBaseDensity_pos V _).le)
        _ = 2 * gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) * ‖L‖ / D := rfl
    calc
      |fderiv ℝ hfun z (Pi.single i 1)| ≤
          2 * gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) * ‖L‖ / D := hraw
      _ ≤ 2 * (Real.exp c * Real.exp (c * ∑ j : I, |z j|)) * ‖L‖ / D := by
        gcongr
        exact hdensity z
      _ ≤ C * Real.exp (c * ∑ j : I, |z j|) := by
        dsimp [C]
        have hden := hD.le
        have hexp := (Real.exp_pos (c * ∑ j : I, |z j|)).le
        calc
          2 * (Real.exp c * Real.exp (c * ∑ j : I, |z j|)) * ‖L‖ / D =
              (Real.exp c * (2 * ‖L‖) / D) *
                Real.exp (c * ∑ j : I, |z j|) := by ring
          _ ≤ (Real.exp c * (2 * ‖L‖ + 1) / D) *
                Real.exp (c * ∑ j : I, |z j|) := by
                  apply mul_le_mul_of_nonneg_right _ hexp
                  apply div_le_div_of_nonneg_right _ hden
                  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos c).le
                  linarith
  have hcoord (i : I) := SYK.pi_gaussian_stein_coord hfun i hcont C c hc0 hC0 hvalue hderiv
  rw [show (∫ z : I → ℝ,
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a * hfun z
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∑ i : I, a i * ∫ z : I → ℝ, z i * hfun z
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) by
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with z
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · intro i hi
      apply ((SYK.integrable_abs_coord_mul_exp_c_sum_abs_pi c i).const_mul
        (|a i| * C)).mono'
      · exact (continuous_const.mul ((continuous_apply i).mul hcont.continuous)
          ).aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc
          |a i| * (|z i| * |hfun z|) ≤
              |a i| * (|z i| * (C * Real.exp (c * ∑ j : I, |z j|))) := by
                gcongr
                exact hvalue z
          _ = (|a i| * C) *
              (|z i| * Real.exp (c * ∑ j : I, |z j|)) := by ring
          _ = |(|a i| * C) *
              (|z i| * Real.exp (c * ∑ j : I, |z j|))| := by
            have hnon : 0 ≤ (|a i| * C) *
                (|z i| * Real.exp (c * ∑ j : I, |z j|)) := by positivity
            exact (abs_of_nonneg hnon).symm
        rw [abs_of_nonneg]
        positivity
    ]
  simp_rw [hcoord]
  have hspan : WithLp.toLp 2 (∑ i : I, a i • Pi.single i (1 : ℝ)) = a := by
    ext j
    simp [Pi.single_apply]
  have hintDeriv (i : I) : Integrable
      (fun z : I → ℝ => a i * fderiv ℝ hfun z (Pi.single i 1))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    apply ((SYK.integrable_exp_c_sum_abs_pi c).const_mul (|a i| * C)).mono'
    · exact (continuous_const.mul
        ((hcont.continuous_fderiv (by norm_num)).clm_apply continuous_const)
          ).aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |a i| * |fderiv ℝ hfun z (Pi.single i 1)| ≤
            |a i| * (C * Real.exp (c * ∑ j : I, |z j|)) := by
              gcongr
              exact hderiv z i
        _ = |(|a i| * C) * Real.exp (c * ∑ j : I, |z j|)| := by
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hC0)
            (Real.exp_pos _).le)]
          ring
      rw [abs_of_nonneg]
      positivity
  calc
    (∑ i : I, a i * ∫ z : I → ℝ, fderiv ℝ hfun z (Pi.single i 1)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z : I → ℝ, ∑ i : I, a i * fderiv ℝ hfun z (Pi.single i 1)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
          simp_rw [← integral_const_mul]
          rw [integral_finset_sum]
          exact fun i hi => hintDeriv i
    _ = ∫ z : I → ℝ,
        (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
          gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ / D) *
          ((L a) ξ - (1 / 2 : ℝ) * ∑ η : S,
            gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * (L a) η)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [show ∑ i : I, a i * fderiv ℝ hfun z (Pi.single i 1) =
              fderiv ℝ hfun z (∑ i : I, a i • Pi.single i (1 : ℝ)) by
            simp_rw [map_sum, map_smul, smul_eq_mul]]
          rw [hfderiv, hspan]
    _ = gtHalfBaseWeight V L H ξ * (L a) ξ -
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfBasePairWeight V L H ξ η * (L a) η := by
      unfold gtHalfBaseWeight gtHalfBasePairWeight gtHalfBaseNumerator
        gtHalfBasePairNumerator
      dsimp [D]
      have hpoint (z : I → ℝ) :
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
                gtHalfBaseDenominator V L H) *
            ((L a) ξ - (1 / 2 : ℝ) * ∑ η : S,
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * (L a) η) =
          (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
              gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
                gtHalfBaseDenominator V L H) * (L a) ξ -
            (1 / 2 : ℝ) * ∑ η : S,
              (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
                  gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) /
                    gtHalfBaseDenominator V L H) * (L a) η := by
        have hsum :
            (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
                  gtHalfBaseDenominator V L H) *
              ((1 / 2 : ℝ) * ∑ η : S,
                gtStateGibbs V (L (WithLp.toLp 2 z) + H) η * (L a) η) =
            (1 / 2 : ℝ) * ∑ η : S,
              (gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
                  gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) /
                    gtHalfBaseDenominator V L H) * (L a) η := by
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro η hη
          ring
        rw [mul_sub, hsum]
      rw [integral_congr_ae (ae_of_all _ hpoint)]
      rw [integral_sub, integral_const_mul]
      · simp_rw [integral_finset_sum Finset.univ (fun η _ =>
          ((integrable_gtHalfBasePairNumerator_integrand V L H ξ η).div_const _
            ).mul_const _)]
        simp_rw [integral_mul_const]
        have hnum :
            (∫ z : I → ℝ,
                gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                  gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ /
                    gtHalfBaseDenominator V L H
              ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
              (∫ z : I → ℝ,
                gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                  gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ
              ∂Measure.pi (fun _ : I => gaussianReal 0 1)) /
                gtHalfBaseDenominator V L H := by
          rw [integral_div]
        have hpair (η : S) :
            (∫ z : I → ℝ,
                gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                  (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
                    gtStateGibbs V (L (WithLp.toLp 2 z) + H) η) /
                  gtHalfBaseDenominator V L H
              ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
              (∫ z : I → ℝ,
                  gtHalfBaseDensity V (L (WithLp.toLp 2 z) + H) *
                    (gtStateGibbs V (L (WithLp.toLp 2 z) + H) ξ *
                      gtStateGibbs V (L (WithLp.toLp 2 z) + H) η)
                ∂Measure.pi (fun _ : I => gaussianReal 0 1)) /
                  gtHalfBaseDenominator V L H := by
          rw [integral_div]
        rw [hnum]
        simp_rw [hpair]
      · exact ((integrable_gtHalfBaseNumerator_integrand V L H ξ).div_const _).mul_const _
      · exact (integrable_finset_sum _ fun η _ =>
          ((integrable_gtHalfBasePairNumerator_integrand V L H ξ η).div_const _).mul_const _
          ).const_mul _

noncomputable def gtHalfOuterCLM
    {S I₀ : Type*} [Fintype S] [Fintype I₀]
    (A B₀ : S → EuclideanSpace ℝ I₀) (t : ℝ) :
    EuclideanSpace ℝ I₀ →L[ℝ] GTStateSpace S :=
  Real.sqrt t • gtCoefficientCLM A +
    Real.sqrt (1 - t) • gtCoefficientCLM B₀

noncomputable def gtHalfInnerCLM
    {S I₁ : Type*} [Fintype S] [Fintype I₁]
    (B₁ : S → EuclideanSpace ℝ I₁) (t : ℝ) :
    EuclideanSpace ℝ I₁ →L[ℝ] GTStateSpace S :=
  Real.sqrt (1 - t) • gtCoefficientCLM B₁

lemma gtHalfField_eq_base_affine
    {S I₀ I₁ : Type*} [Fintype S] [Fintype I₀] [Fintype I₁]
    (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) :
    gtHalfField A B₀ B₁ H₀ t z₀ z₁ =
      gtHalfInnerCLM B₁ t z₁ + (gtHalfOuterCLM A B₀ t z₀ + H₀) := by
  simp [gtHalfField, gtHalfInnerCLM, gtHalfOuterCLM]
  abel

lemma gtHalfDenominator_eq_base
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) :
    gtHalfDenominator V A B₀ B₁ H₀ t z₀ =
      gtHalfBaseDenominator V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z₀ + H₀) := by
  unfold gtHalfDenominator gtHalfBaseDenominator gtHalfBaseDensity
  apply integral_congr_ae
  filter_upwards with z₁
  rw [gtHalfField_eq_base_affine]

lemma gtHalfGibbsWeight_eq_base
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) (ξ : S) :
    gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ =
      gtHalfBaseWeight V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z₀ + H₀) ξ := by
  unfold gtHalfGibbsWeight gtHalfBaseWeight gtHalfBaseNumerator gtHalfDensity
  rw [gtHalfDenominator_eq_base]
  congr 1
  apply integral_congr_ae
  filter_upwards with z₁
  unfold gtHalfBaseDensity
  rw [gtHalfField_eq_base_affine]

lemma gtHalfInnerPairWeight_eq_base
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) (ξ η : S) :
    gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η =
      gtHalfBasePairWeight V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z₀ + H₀) ξ η := by
  unfold gtHalfInnerPairWeight gtHalfBasePairWeight gtHalfBasePairNumerator
    gtHalfDensity
  rw [gtHalfDenominator_eq_base]
  congr 1
  apply integral_congr_ae
  filter_upwards with z₁
  rw [gtHalfField_eq_base_affine]
  rfl

lemma gtHalf_outer_stein
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ C : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (ξ : S) :
    (∫ z₀ : I₀ → ℝ,
        inner ℝ (WithLp.toLp 2 z₀ : EuclideanSpace ℝ I₀) (C ξ) *
          gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀) ξ
        ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)) =
      ∫ z₀ : I₀ → ℝ,
        let H := gtHalfOuterCLM A B₀ t (WithLp.toLp 2 z₀) + H₀
        gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀) ξ *
            (gtHalfOuterCLM A B₀ t (C ξ)) ξ -
          (1 / 2 : ℝ) * ∑ η : S,
            gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀) ξ η *
              (gtHalfOuterCLM A B₀ t (C ξ)) η -
          (1 / 2 : ℝ) *
            gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀) ξ *
              ∑ η : S,
                gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀) η *
                  (gtHalfOuterCLM A B₀ t (C ξ)) η
        ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1) := by
  have h := gtHalfBaseWeight_stein V (gtHalfInnerCLM B₁ t)
    (gtHalfOuterCLM A B₀ t) H₀ (C ξ) ξ
  simpa only [gtHalfGibbsWeight_eq_base, gtHalfInnerPairWeight_eq_base] using h

lemma gtHalf_inner_stein
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) (ξ : S) :
    (∫ z₁ : I₁ → ℝ,
        inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ) *
          (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
            gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ /
                gtHalfDenominator V A B₀ B₁ H₀ t z₀)
        ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) =
      gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
          (gtHalfInnerCLM B₁ t (B₁ ξ)) ξ -
        (1 / 2 : ℝ) * ∑ η : S,
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
            (gtHalfInnerCLM B₁ t (B₁ ξ)) η := by
  have h := gtHalfBase_inner_stein V (gtHalfInnerCLM B₁ t)
    (gtHalfOuterCLM A B₀ t z₀ + H₀) (B₁ ξ) ξ
  rw [← gtHalfDenominator_eq_base] at h
  rw [← gtHalfGibbsWeight_eq_base] at h
  simp_rw [← gtHalfInnerPairWeight_eq_base] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with z₁
  unfold gtHalfDensity gtHalfBaseDensity
  rw [gtHalfField_eq_base_affine]

end SpinGlass.AT
