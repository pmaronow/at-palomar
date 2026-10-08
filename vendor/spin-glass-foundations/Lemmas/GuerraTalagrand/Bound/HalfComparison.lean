module

public import Lemmas.GuerraTalagrand.Bound.HalfCalculus
public import Lemmas.GuerraTalagrand.Bound.HalfEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

lemma continuous_gtHalfTransform_parameter
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (z₀ : EuclideanSpace ℝ I₀) :
    Continuous (fun t => gtHalfTransform V A B₀ B₁ H₀ t z₀) := by
  have hden : Continuous (fun t => gtHalfDenominator V A B₀ B₁ H₀ t z₀) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    unfold gtHalfDenominator
    let base := hasModerateGrowth_gtStateLogPartition V
    let RA : ℝ := Real.sqrt (|t₀| + 1)
    let RB : ℝ := Real.sqrt (|t₀| + 2)
    let K : ℝ := RA * (‖gtCoefficientCLM A‖ * ‖z₀‖) +
      RB * (‖gtCoefficientCLM B₀‖ * ‖z₀‖) + ‖H₀‖
    let c : ℝ := (1 / 2 : ℝ) * base.C * RB * ‖gtCoefficientCLM B₁‖
    let M : ℝ := Real.exp ((1 / 2 : ℝ) * base.C * (1 + K))
    let bound : (I₁ → ℝ) → ℝ := fun z₁ =>
      M * Real.exp (c * ‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖)
    have hbi : Integrable bound
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) :=
      (integrable_exp_mul_norm_gaussianProduct (I := I₁) c).const_mul M
    apply MeasureTheory.continuousAt_of_dominated (bound := bound)
    · filter_upwards with u
      exact (integrable_gtHalfDenominator_integrand V A B₀ B₁ H₀ u z₀).1
    · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with u hu
      filter_upwards with z₁
      have hut : |u - t₀| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hu
      have huA : u ≤ |t₀| + 1 := by
        have := (abs_lt.1 hut).2
        linarith [le_abs_self t₀]
      have huB : 1 - u ≤ |t₀| + 2 := by
        have := (abs_lt.1 hut).1
        linarith [neg_le_abs t₀]
      have hsA : Real.sqrt u ≤ RA := by
        dsimp [RA]
        exact Real.sqrt_le_sqrt huA
      have hsB : Real.sqrt (1 - u) ≤ RB := by
        dsimp [RB]
        exact Real.sqrt_le_sqrt huB
      let z₁E : EuclideanSpace ℝ I₁ := WithLp.toLp 2 z₁
      have hfield : ‖gtHalfField A B₀ B₁ H₀ u z₀ z₁E‖ ≤
          K + RB * ‖gtCoefficientCLM B₁‖ * ‖z₁E‖ := by
        calc
          ‖gtHalfField A B₀ B₁ H₀ u z₀ z₁E‖ ≤
              Real.sqrt u * (‖gtCoefficientCLM A‖ * ‖z₀‖) +
                Real.sqrt (1 - u) *
                  (‖gtCoefficientCLM B₀‖ * ‖z₀‖ +
                    ‖gtCoefficientCLM B₁‖ * ‖z₁E‖) + ‖H₀‖ := by
            unfold gtHalfField
            calc
              _ ≤ ‖Real.sqrt u • gtCoefficientCLM A z₀ +
                    Real.sqrt (1 - u) •
                      (gtCoefficientCLM B₀ z₀ + gtCoefficientCLM B₁ z₁E)‖ + ‖H₀‖ :=
                norm_add_le _ _
              _ ≤ _ := by
                gcongr
                refine (norm_add_le _ _).trans ?_
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
                gcongr
                · exact (gtCoefficientCLM A).le_opNorm z₀
                · exact (norm_add_le _ _).trans (add_le_add
                    ((gtCoefficientCLM B₀).le_opNorm z₀)
                    ((gtCoefficientCLM B₁).le_opNorm z₁E))
          _ ≤ K + RB * ‖gtCoefficientCLM B₁‖ * ‖z₁E‖ := by
            have hA := mul_le_mul_of_nonneg_right hsA
              (mul_nonneg (norm_nonneg (gtCoefficientCLM A)) (norm_nonneg z₀))
            have hB := mul_le_mul_of_nonneg_right hsB
              (add_nonneg
                (mul_nonneg (norm_nonneg (gtCoefficientCLM B₀)) (norm_nonneg z₀))
                (mul_nonneg (norm_nonneg (gtCoefficientCLM B₁)) (norm_nonneg z₁E)))
            dsimp [K]
            nlinarith
      have hg := base.F_bound (gtHalfField A B₀ B₁ H₀ u z₀ z₁E)
      have hm : base.m = 1 := by rfl
      rw [hm, pow_one] at hg
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      dsimp [bound, M, c]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlog : gtStateLogPartition V
          (gtHalfField A B₀ B₁ H₀ u z₀ z₁E) ≤
          base.C * (1 + ‖gtHalfField A B₀ B₁ H₀ u z₀ z₁E‖) :=
        (le_abs_self _).trans hg
      dsimp [z₁E] at hfield ⊢
      nlinarith [base.Cpos.le]
    · exact hbi
    · filter_upwards with z₁
      have hf : Continuous (fun u =>
          gtHalfField A B₀ B₁ H₀ u z₀ (WithLp.toLp 2 z₁)) := by
        unfold gtHalfField
        fun_prop
      exact (Real.continuous_exp.comp
        (continuous_const.mul ((contDiff_gtStateLogPartition V).continuous.comp hf))).continuousAt
  unfold gtHalfTransform
  exact continuous_const.mul
    (hden.log (fun t => (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).ne'))

lemma continuous_gtHalfPressure
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S) :
    Continuous (gtHalfPressure V A B₀ B₁ H₀) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let RA : ℝ := Real.sqrt (|t₀| + 1)
  let RB : ℝ := Real.sqrt (|t₀| + 2)
  let R : ℝ := RA * ‖gtCoefficientCLM A‖ + RB * ‖gtCoefficientCLM B₀‖
  let C : ℝ := |gtHalfTransform V A B₀ B₁ H₀ t₀ 0| + 1
  let bound : (I₀ → ℝ) → ℝ := fun z =>
    C + R * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I₀)‖
  have hR : 0 ≤ R := by dsimp [R, RA, RB]; positivity
  have hbi : Integrable bound (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) :=
    (integrable_const C).add
      ((integrable_norm_gaussianProduct (I := I₀)).const_mul R)
  unfold gtHalfPressure
  apply MeasureTheory.continuousAt_of_dominated (bound := bound)
  · filter_upwards with u
    exact (integrable_gtHalfTransform V A B₀ B₁ H₀ u).1
  · filter_upwards [Metric.ball_mem_nhds t₀ one_pos,
      (continuous_gtHalfTransform_parameter V A B₀ B₁ H₀ 0).continuousAt
        (Metric.ball_mem_nhds
          (gtHalfTransform V A B₀ B₁ H₀ t₀ 0) one_pos)] with u hu hzero
    filter_upwards with z
    have hut : |u - t₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hu
    have huA : u ≤ |t₀| + 1 := by
      have := (abs_lt.1 hut).2
      linarith [le_abs_self t₀]
    have huB : 1 - u ≤ |t₀| + 2 := by
      have := (abs_lt.1 hut).1
      linarith [neg_le_abs t₀]
    have hsA : Real.sqrt u ≤ RA := Real.sqrt_le_sqrt huA
    have hsB : Real.sqrt (1 - u) ≤ RB := Real.sqrt_le_sqrt huB
    let zE : EuclideanSpace ℝ I₀ := WithLp.toLp 2 z
    have hM : ‖gtHalfOuterCLM A B₀ u zE‖ ≤ R * ‖zE‖ := by
      have hop : ‖gtHalfOuterCLM A B₀ u‖ ≤ R := by
        unfold gtHalfOuterCLM
        calc
          _ ≤ ‖Real.sqrt u • gtCoefficientCLM A‖ +
              ‖Real.sqrt (1 - u) • gtCoefficientCLM B₀‖ := norm_add_le _ _
          _ = Real.sqrt u * ‖gtCoefficientCLM A‖ +
              Real.sqrt (1 - u) * ‖gtCoefficientCLM B₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
          _ ≤ RA * ‖gtCoefficientCLM A‖ + RB * ‖gtCoefficientCLM B₀‖ := by
            gcongr
          _ = R := by rfl
      calc
        _ ≤ ‖gtHalfOuterCLM A B₀ u‖ * ‖zE‖ :=
          (gtHalfOuterCLM A B₀ u).le_opNorm zE
        _ ≤ R * ‖zE‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg zE)
    rw [Real.norm_eq_abs]
    have hlip := (lipschitzWith_gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)).norm_sub_le
      (gtHalfOuterCLM A B₀ u zE + H₀) (gtHalfOuterCLM A B₀ u 0 + H₀)
    norm_num at hlip
    have habs := abs_sub_abs_le_abs_sub
      (gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)
        (gtHalfOuterCLM A B₀ u zE + H₀))
      (gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)
        (gtHalfOuterCLM A B₀ u 0 + H₀))
    have hz0 : |gtHalfTransform V A B₀ B₁ H₀ u 0| < C := by
      dsimp [C]
      have hzero' : |gtHalfTransform V A B₀ B₁ H₀ u 0 -
          gtHalfTransform V A B₀ B₁ H₀ t₀ 0| < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hzero
      calc
        |gtHalfTransform V A B₀ B₁ H₀ u 0| =
            |(gtHalfTransform V A B₀ B₁ H₀ u 0 -
                gtHalfTransform V A B₀ B₁ H₀ t₀ 0) +
              gtHalfTransform V A B₀ B₁ H₀ t₀ 0| := by ring_nf
        _ ≤ |gtHalfTransform V A B₀ B₁ H₀ u 0 -
                gtHalfTransform V A B₀ B₁ H₀ t₀ 0| +
              |gtHalfTransform V A B₀ B₁ H₀ t₀ 0| := by
          simpa [Real.norm_eq_abs] using norm_add_le
            (gtHalfTransform V A B₀ B₁ H₀ u 0 -
              gtHalfTransform V A B₀ B₁ H₀ t₀ 0)
            (gtHalfTransform V A B₀ B₁ H₀ t₀ 0)
        _ < 1 + |gtHalfTransform V A B₀ B₁ H₀ t₀ 0| := by
          linarith
        _ = |gtHalfTransform V A B₀ B₁ H₀ t₀ 0| + 1 := by ring
    have hzbase : |gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀| < C := by
      have heq := gtHalfTransform_eq_base V A B₀ B₁ H₀ u 0
      have heq' : gtHalfTransform V A B₀ B₁ H₀ u 0 =
          gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀ := by
        simpa using heq
      rw [← heq']
      exact hz0
    dsimp [bound]
    rw [gtHalfTransform_eq_base]
    change |gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)
        (gtHalfOuterCLM A B₀ u zE + H₀)| ≤ C + R * ‖zE‖
    calc
      _ ≤ |gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)
              (gtHalfOuterCLM A B₀ u zE + H₀) -
            gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀| +
          |gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀| := by
            simpa [Real.norm_eq_abs] using norm_add_le
              (gtHalfBaseTransform V (gtHalfInnerCLM B₁ u)
                (gtHalfOuterCLM A B₀ u zE + H₀) -
                gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀)
              (gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀)
      _ ≤ ‖gtHalfOuterCLM A B₀ u zE‖ +
          |gtHalfBaseTransform V (gtHalfInnerCLM B₁ u) H₀| :=
            add_le_add hlip (le_refl _)
      _ ≤ R * ‖zE‖ + C :=
            add_le_add hM hzbase.le
      _ = C + R * ‖zE‖ := by ring
  · exact hbi
  · filter_upwards with z
    exact (continuous_gtHalfTransform_parameter V A B₀ B₁ H₀
      (WithLp.toLp 2 z)).continuousAt

/-- Derivative of the two-level field on the open interpolation interval. -/
noncomputable def gtHalfFieldDeriv
    {S I₀ I₁ : Type*} [Fintype S] [Fintype I₀] [Fintype I₁]
    (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (t : ℝ)
    (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) :
    GTStateSpace S :=
  (1 / (2 * Real.sqrt t)) • gtCoefficientCLM A z₀ -
    (1 / (2 * Real.sqrt (1 - t))) • gtCoefficientCLM B₀ z₀ -
    (1 / (2 * Real.sqrt (1 - t))) • gtCoefficientCLM B₁ z₁

lemma hasDerivAt_gtHalfField
    {S I₀ I₁ : Type*} [Fintype S] [Fintype I₀] [Fintype I₁]
    (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) :
    HasDerivAt (fun u => gtHalfField A B₀ B₁ H₀ u z₀ z₁)
      (gtHalfFieldDeriv A B₀ B₁ t z₀ z₁) t := by
  have hA := (Real.hasDerivAt_sqrt ht.1.ne').smul_const
    (gtCoefficientCLM A z₀)
  have hsub : HasDerivAt (fun u : ℝ => (1 : ℝ) - u) (-1) t := by
    simpa using HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id t)
  have hB := ((Real.hasDerivAt_sqrt (ne_of_gt (sub_pos.mpr ht.2))).comp t hsub
    ).smul_const (gtCoefficientCLM B₀ z₀ + gtCoefficientCLM B₁ z₁)
  have hsum := (hA.add hB).add_const H₀
  have hd :
      (1 / (2 * Real.sqrt t)) • gtCoefficientCLM A z₀ +
          (1 / (2 * Real.sqrt (1 - t)) * (-1)) •
            (gtCoefficientCLM B₀ z₀ + gtCoefficientCLM B₁ z₁) =
        gtHalfFieldDeriv A B₀ B₁ t z₀ z₁ := by
    ext ξ
    simp [gtHalfFieldDeriv]
    ring
  have hout := hsum.congr_deriv hd
  simpa [gtHalfField] using hout

lemma hasDerivAt_gtHalfDensity
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) (z₁ : EuclideanSpace ℝ I₁) :
    HasDerivAt
      (fun u => gtHalfDensity V A B₀ B₁ H₀ u z₀ z₁)
      (gtHalfDensity V A B₀ B₁ H₀ t z₀ z₁ * (1 / 2 : ℝ) *
        ∑ ξ : S,
          gtStateGibbs V (gtHalfField A B₀ B₁ H₀ t z₀ z₁) ξ *
            gtHalfFieldDeriv A B₀ B₁ t z₀ z₁ ξ) t := by
  have hlog : HasFDerivAt (gtStateLogPartition V)
      (fderiv ℝ (gtStateLogPartition V)
        (gtHalfField A B₀ B₁ H₀ t z₀ z₁))
      (gtHalfField A B₀ B₁ H₀ t z₀ z₁) :=
    ((contDiff_gtStateLogPartition V).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hc := hlog.comp_hasDerivAt t
    (hasDerivAt_gtHalfField A B₀ B₁ H₀ ht z₀ z₁)
  have he := (hc.const_mul (1 / 2 : ℝ)).exp
  rw [fderiv_gtStateLogPartition_apply] at he
  convert he using 1 <;> simp [gtHalfDensity] <;> ring

/-- Differentiate the inner half-mass normalizing integral. -/
lemma hasDerivAt_gtHalfDenominator
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) :
    HasDerivAt (fun u => gtHalfDenominator V A B₀ B₁ H₀ u z₀)
      (∫ z₁ : I₁ → ℝ,
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
          ∑ ξ : S,
            gtStateGibbs V
                (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ
        ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) t := by
  classical
  let ε : ℝ := min t (1 - t) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have hm : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
    linarith
  have hball : ∀ x ∈ Metric.ball t ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hεt : ε ≤ t / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_left _ _
    have hε1t : ε ≤ (1 - t) / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_right _ _
    constructor
    · have := (abs_sub_lt_iff.1 hxt).2
      nlinarith
    · have := (abs_sub_lt_iff.1 hxt).1
      nlinarith
  let cA : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cB : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  have hcA : 0 ≤ cA := by dsimp [cA]; positivity
  have hcB : 0 ≤ cB := by dsimp [cB]; positivity
  have hcoeffA : ∀ x ∈ Metric.ball t ε,
      |1 / (2 * Real.sqrt x)| ≤ cA := by
    intro x hx
    have hxI := hball x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hεt : ε ≤ t / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_left _ _
    have htx : t / 2 ≤ x := by
      have := (abs_sub_lt_iff.1 hxt).2
      nlinarith
    have ht2 : 0 < t / 2 := by linarith [ht.1]
    have hp : 0 < 2 * Real.sqrt (t / 2) := by
      exact mul_pos (by norm_num) (Real.sqrt_pos.2 ht2)
    have hle : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by
      nlinarith [Real.sqrt_le_sqrt htx]
    have hi : 1 / (2 * Real.sqrt x) ≤ cA := by
      dsimp [cA]
      simpa [one_div] using one_div_le_one_div_of_le hp hle
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt x))]
    exact hi
  have hcoeffB : ∀ x ∈ Metric.ball t ε,
      |1 / (2 * Real.sqrt (1 - x))| ≤ cB := by
    intro x hx
    have hxI := hball x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hε1t : ε ≤ (1 - t) / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_right _ _
    have htx : (1 - t) / 2 ≤ 1 - x := by
      have := (abs_sub_lt_iff.1 hxt).1
      nlinarith
    have ht2 : 0 < (1 - t) / 2 := by linarith [ht.2]
    have hp : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
      exact mul_pos (by norm_num) (Real.sqrt_pos.2 ht2)
    have hle : 2 * Real.sqrt ((1 - t) / 2) ≤
        2 * Real.sqrt (1 - x) := by
      nlinarith [Real.sqrt_le_sqrt htx]
    have hi : 1 / (2 * Real.sqrt (1 - x)) ≤ cB := by
      dsimp [cB]
      simpa [one_div] using one_div_le_one_div_of_le hp hle
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - x)))]
    exact hi
  let LA := gtCoefficientCLM A
  let LB₀ := gtCoefficientCLM B₀
  let LB₁ := gtCoefficientCLM B₁
  let R₀ : ℝ := ‖LA z₀‖ + ‖LB₀ z₀‖ + ‖H₀‖
  let R₁ : ℝ := ‖LB₁‖
  let D₀ : ℝ := cA * ‖LA z₀‖ + cB * ‖LB₀ z₀‖
  let D₁ : ℝ := cB * ‖LB₁‖
  let C : ℝ := (hasModerateGrowth_gtStateLogPartition V).C / 2
  let E₀ : ℝ := Real.exp (C * (1 + R₀))
  let bound : (I₁ → ℝ) → ℝ := fun z₁ =>
    (1 / 2 : ℝ) * (D₀ + D₁ * ‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖) *
      (E₀ * Real.exp ((C * R₁) *
        ‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (hasModerateGrowth_gtStateLogPartition V).Cpos.le (by norm_num)
  have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hbound_int : Integrable bound
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
    let c := C * R₁
    have he := integrable_exp_mul_norm_gaussianProduct (I := I₁) c
    have hne := integrable_norm_mul_exp_mul_norm_gaussianProduct (I := I₁) c
    have hs := (he.const_mul D₀).add (hne.const_mul D₁)
    have hs' := (hs.const_mul E₀).const_mul (1 / 2 : ℝ)
    convert hs' using 1
    funext z₁
    dsimp [bound, c]
    ring
  let F : ℝ → (I₁ → ℝ) → ℝ := fun x z₁ =>
    gtHalfDensity V A B₀ B₁ H₀ x z₀ (WithLp.toLp 2 z₁)
  let F' : ℝ → (I₁ → ℝ) → ℝ := fun x z₁ =>
    gtHalfDensity V A B₀ B₁ H₀ x z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
      ∑ ξ : S,
        gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ x z₀ (WithLp.toLp 2 z₁)) ξ *
          gtHalfFieldDeriv A B₀ B₁ x z₀ (WithLp.toLp 2 z₁) ξ
  have hF_meas : ∀ᶠ x in nhds t,
      AEStronglyMeasurable (F x)
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact (integrable_gtHalfDenominator_integrand V A B₀ B₁ H₀ x z₀).1
  have hF_int : Integrable (F t)
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) :=
    integrable_gtHalfDenominator_integrand V A B₀ B₁ H₀ t z₀
  have hF'_meas : AEStronglyMeasurable (F' t)
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
    have hfield : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) := by
      unfold gtHalfField
      fun_prop
    have hderiv : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁)) := by
      unfold gtHalfFieldDeriv
      fun_prop
    have hdensity : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) := by
      unfold gtHalfDensity
      exact Real.continuous_exp.comp
        (continuous_const.mul ((contDiff_gtStateLogPartition V).continuous.comp hfield))
    have hc : Continuous (fun z₁ : I₁ → ℝ =>
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
          ∑ ξ : S,
            gtStateGibbs V
                (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ) := by
      apply (hdensity.mul continuous_const).mul
      apply continuous_finset_sum
      intro ξ _
      exact (((contDiff_gtStateGibbs V ξ).continuous.comp hfield).mul
        ((EuclideanSpace.proj ξ).continuous.comp hderiv))
    exact hc.aestronglyMeasurable
  have h_bound : ∀ᵐ z₁ ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, ‖F' x z₁‖ ≤ bound z₁ := by
    refine ae_of_all _ (fun z₁ x hx => ?_)
    let zE : EuclideanSpace ℝ I₁ := WithLp.toLp 2 z₁
    let H := gtHalfField A B₀ B₁ H₀ x z₀ zE
    let K := gtHalfFieldDeriv A B₀ B₁ x z₀ zE
    have hxI := hball x hx
    have hH : ‖H‖ ≤ R₀ + R₁ * ‖zE‖ := by
      have hsx : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hxI.2.le
      have hs1x : Real.sqrt (1 - x) ≤ 1 :=
        Real.sqrt_le_one.mpr (by linarith [hxI.1])
      calc
        ‖H‖ ≤ ‖Real.sqrt x • LA z₀‖ +
              ‖Real.sqrt (1-x) • (LB₀ z₀ + LB₁ zE)‖ + ‖H₀‖ := by
          dsimp [H, gtHalfField, LA, LB₀, LB₁]
          calc
            _ ≤ ‖Real.sqrt x • LA z₀ +
                Real.sqrt (1-x) • (LB₀ z₀ + LB₁ zE)‖ + ‖H₀‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖LA z₀‖ + (‖LB₀ z₀‖ + ‖LB₁‖ * ‖zE‖) + ‖H₀‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
          have hinner : ‖LB₀ z₀ + LB₁ zE‖ ≤
              ‖LB₀ z₀‖ + ‖LB₁‖ * ‖zE‖ := by
            calc
              _ ≤ ‖LB₀ z₀‖ + ‖LB₁ zE‖ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact LB₁.le_opNorm zE
          have hfirst : Real.sqrt x * ‖LA z₀‖ ≤ ‖LA z₀‖ := by
            nlinarith [norm_nonneg (LA z₀)]
          have hsecond : Real.sqrt (1-x) * ‖LB₀ z₀ + LB₁ zE‖ ≤
              ‖LB₀ z₀‖ + ‖LB₁‖ * ‖zE‖ := by
            calc
              _ ≤ 1 * ‖LB₀ z₀ + LB₁ zE‖ :=
                mul_le_mul_of_nonneg_right hs1x (norm_nonneg _)
              _ ≤ _ := by simpa using hinner
          linarith
        _ = R₀ + R₁ * ‖zE‖ := by dsimp [R₀, R₁]; ring
    have hK : ‖K‖ ≤ D₀ + D₁ * ‖zE‖ := by
      calc
        ‖K‖ ≤ |1 / (2 * Real.sqrt x)| * ‖LA z₀‖ +
              |1 / (2 * Real.sqrt (1-x))| * ‖LB₀ z₀‖ +
              |1 / (2 * Real.sqrt (1-x))| * ‖LB₁ zE‖ := by
          dsimp [K, gtHalfFieldDeriv, LA, LB₀, LB₁]
          let a := (1 / (2 * Real.sqrt x)) • LA z₀
          let b := (1 / (2 * Real.sqrt (1-x))) • LB₀ z₀
          let c := (1 / (2 * Real.sqrt (1-x))) • LB₁ zE
          calc
            ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
            _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
              gcongr
              exact norm_sub_le _ _
            _ = _ := by
              dsimp [a, b, c]
              simp only [norm_smul, Real.norm_eq_abs]
              ring
        _ ≤ cA * ‖LA z₀‖ + cB * ‖LB₀ z₀‖ +
              cB * (‖LB₁‖ * ‖zE‖) := by
          gcongr
          · exact hcoeffA x hx
          · exact hcoeffB x hx
          · exact hcoeffB x hx
          · exact LB₁.le_opNorm zE
        _ = D₀ + D₁ * ‖zE‖ := by dsimp [D₀, D₁]; ring
    have havg : |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤ ‖K‖ := by
      simpa [fderiv_gtStateLogPartition_apply, Real.norm_eq_abs] using
        (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (gtStateLogPartition V) H) K |>.trans
            (mul_le_mul_of_nonneg_right
              (norm_fderiv_gtStateLogPartition_le_one V H) (norm_nonneg K)))
    have hdensity : gtHalfDensity V A B₀ B₁ H₀ x z₀ zE ≤
        E₀ * Real.exp ((C * R₁) * ‖zE‖) := by
      let base := hasModerateGrowth_gtStateLogPartition V
      have hg := base.F_bound H
      have hm : base.m = 1 := by rfl
      rw [hm, pow_one] at hg
      unfold gtHalfDensity
      rw [show gtHalfField A B₀ B₁ H₀ x z₀ zE = H by rfl]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlog : (1 / 2 : ℝ) * gtStateLogPartition V H ≤ C * (1 + ‖H‖) := by
        have := le_abs_self (gtStateLogPartition V H)
        dsimp [C]
        nlinarith
      calc
        (1 / 2 : ℝ) * gtStateLogPartition V H ≤ C * (1 + ‖H‖) := hlog
        _ ≤ C * (1 + (R₀ + R₁ * ‖zE‖)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
        _ = C * (1 + R₀) + C * R₁ * ‖zE‖ := by ring
    rw [Real.norm_eq_abs]
    dsimp [F', bound]
    rw [abs_mul, abs_mul]
    change |gtHalfDensity V A B₀ B₁ H₀ x z₀ zE| * |(1 / 2 : ℝ)| *
        |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤ _
    have hdensity0 : 0 ≤ gtHalfDensity V A B₀ B₁ H₀ x z₀ zE := by
      unfold gtHalfDensity
      exact Real.exp_nonneg _
    rw [abs_of_nonneg hdensity0,
      abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    calc
      gtHalfDensity V A B₀ B₁ H₀ x z₀ zE * (1 / 2) *
          |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤
        gtHalfDensity V A B₀ B₁ H₀ x z₀ zE * (1 / 2) *
          (D₀ + D₁ * ‖zE‖) := by
            gcongr
            exact havg.trans hK
      _ ≤
        (E₀ * Real.exp ((C * R₁) * ‖zE‖)) * (1 / 2) *
          (D₀ + D₁ * ‖zE‖) := by gcongr
      _ = (1 / 2) * (D₀ + D₁ * ‖zE‖) *
          (E₀ * Real.exp (C * R₁ * ‖zE‖)) := by ring
  have h_diff : ∀ᵐ z₁ ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, HasDerivAt (fun u => F u z₁) (F' x z₁) x := by
    refine ae_of_all _ (fun z₁ x hx => ?_)
    exact hasDerivAt_gtHalfDensity V A B₀ B₁ H₀ (hball x hx) z₀
      (WithLp.toLp 2 z₁)
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := Measure.pi (fun _ : I₁ => gaussianReal 0 1))
      (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (Metric.ball_mem_nhds t hε)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  change HasDerivAt
    (fun u => gtHalfDenominator V A B₀ B₁ H₀ u z₀) _ t
  exact hmain

/-- Pointwise derivative of the half transform, before either Gaussian
integration by parts. -/
lemma hasDerivAt_gtHalfTransform_raw
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) :
    HasDerivAt (fun u => gtHalfTransform V A B₀ B₁ H₀ u z₀)
      (2 * ((∫ z₁ : I₁ → ℝ,
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
            ∑ ξ : S,
              gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
                gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) /
          gtHalfDenominator V A B₀ B₁ H₀ t z₀)) t := by
  have hd := hasDerivAt_gtHalfDenominator V A B₀ B₁ H₀ ht z₀
  have hl := hd.log (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).ne'
  have hout := hl.const_mul 2
  simpa [gtHalfTransform] using hout

/-- The same pointwise derivative, separated into the outer coordinates and
the normalized inner Gaussian expectation. -/
lemma hasDerivAt_gtHalfTransform_before_ibp
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) :
    HasDerivAt (fun u => gtHalfTransform V A B₀ B₁ H₀ u z₀)
      (∑ ξ : S,
          gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
            ((1 / (2 * Real.sqrt t)) * inner ℝ (A ξ) z₀ -
              (1 / (2 * Real.sqrt (1-t))) * inner ℝ (B₀ ξ) z₀) -
        (1 / (2 * Real.sqrt (1-t))) * ∑ ξ : S,
          ∫ z₁ : I₁ → ℝ,
            inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ) *
              (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
                gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ /
                    gtHalfDenominator V A B₀ B₁ H₀ t z₀)
            ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) t := by
  classical
  have hraw := hasDerivAt_gtHalfTransform_raw V A B₀ B₁ H₀ ht z₀
  apply hraw.congr_deriv
  let D := gtHalfDenominator V A B₀ B₁ H₀ t z₀
  have hD : D ≠ 0 := (gtHalfDenominator_pos V A B₀ B₁ H₀ t z₀).ne'
  have hcoord (ξ : S) : Integrable (fun z₁ : I₁ → ℝ =>
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
        (gtStateGibbs V
          (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
          gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ))
      (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
    let LA := gtCoefficientCLM A
    let LB₀ := gtCoefficientCLM B₀
    let LB₁ := gtCoefficientCLM B₁
    let R₀ : ℝ := Real.sqrt t * ‖LA z₀‖ +
      Real.sqrt (1-t) * ‖LB₀ z₀‖ + ‖H₀‖
    let R₁ : ℝ := Real.sqrt (1-t) * ‖LB₁‖
    let D₀ : ℝ := |1 / (2 * Real.sqrt t)| * ‖LA z₀‖ +
      |1 / (2 * Real.sqrt (1-t))| * ‖LB₀ z₀‖
    let D₁ : ℝ := |1 / (2 * Real.sqrt (1-t))| * ‖LB₁‖
    let C : ℝ := (hasModerateGrowth_gtStateLogPartition V).C / 2
    let M : ℝ := Real.exp (C * (1 + R₀))
    let c : ℝ := C * R₁
    let bound : (I₁ → ℝ) → ℝ := fun z₁ =>
      (1 / 2 : ℝ) * M *
        (D₀ * Real.exp (c * ‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖) +
          D₁ * (‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖ *
            Real.exp (c * ‖(WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁)‖)))
    have hbound : Integrable bound
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
      have he := integrable_exp_mul_norm_gaussianProduct (I := I₁) c
      have hne := integrable_norm_mul_exp_mul_norm_gaussianProduct (I := I₁) c
      have hi := ((he.const_mul D₀).add (hne.const_mul D₁)).const_mul M |>.const_mul (1/2)
      convert hi using 1
      funext z₁
      dsimp [bound]
      ring
    apply hbound.mono'
    · have hfield : Continuous (fun z₁ : I₁ → ℝ =>
          gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) := by
        unfold gtHalfField
        fun_prop
      have hderiv : Continuous (fun z₁ : I₁ → ℝ =>
          gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁)) := by
        unfold gtHalfFieldDeriv
        fun_prop
      exact ((((Real.continuous_exp.comp
        (continuous_const.mul ((contDiff_gtStateLogPartition V).continuous.comp hfield))).mul
          continuous_const).mul
            (((contDiff_gtStateGibbs V ξ).continuous.comp hfield).mul
              ((EuclideanSpace.proj ξ).continuous.comp hderiv))).aestronglyMeasurable)
    · filter_upwards with z₁
      let zE : EuclideanSpace ℝ I₁ := WithLp.toLp 2 z₁
      let H := gtHalfField A B₀ B₁ H₀ t z₀ zE
      let K := gtHalfFieldDeriv A B₀ B₁ t z₀ zE
      have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
      have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
      have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
      have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
      have hC : 0 ≤ C := by
        dsimp [C]
        exact div_nonneg (hasModerateGrowth_gtStateLogPartition V).Cpos.le (by norm_num)
      have hH : ‖H‖ ≤ R₀ + R₁ * ‖zE‖ := by
        calc
          ‖H‖ ≤ (‖Real.sqrt t • LA z₀‖ +
                ‖Real.sqrt (1-t) • (LB₀ z₀ + LB₁ zE)‖) + ‖H₀‖ := by
            dsimp [H, gtHalfField, LA, LB₀, LB₁]
            calc
              _ ≤ ‖Real.sqrt t • gtCoefficientCLM A z₀ +
                    Real.sqrt (1-t) •
                      (gtCoefficientCLM B₀ z₀ + gtCoefficientCLM B₁ zE)‖ +
                    ‖H₀‖ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
          _ ≤ ‖Real.sqrt t • LA z₀‖ +
                (‖Real.sqrt (1-t) • LB₀ z₀‖ +
                  Real.sqrt (1-t) * (‖LB₁‖ * ‖zE‖)) + ‖H₀‖ := by
            have hinner := norm_add_le (LB₀ z₀) (LB₁ zE)
            have hop := LB₁.le_opNorm zE
            have hscaled : ‖Real.sqrt (1-t) • (LB₀ z₀ + LB₁ zE)‖ ≤
                ‖Real.sqrt (1-t) • LB₀ z₀‖ +
                  Real.sqrt (1-t) * (‖LB₁‖ * ‖zE‖) := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _)]
              exact mul_le_mul_of_nonneg_left
                (hinner.trans (add_le_add_right hop _)) (Real.sqrt_nonneg _) |>.trans_eq (by
                  rw [mul_add])
            linarith
          _ = R₀ + R₁ * ‖zE‖ := by
            dsimp [R₀, R₁]
            simp only [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
      have hKξ : |K ξ| ≤ D₀ + D₁ * ‖zE‖ := by
        have hcξ : |K ξ| ≤ ‖K‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K ξ
        have hKn : ‖K‖ ≤ D₀ + D₁ * ‖zE‖ := by
          calc
            ‖K‖ ≤ |1 / (2 * Real.sqrt t)| * ‖LA z₀‖ +
                |1 / (2 * Real.sqrt (1-t))| * ‖LB₀ z₀‖ +
                |1 / (2 * Real.sqrt (1-t))| * ‖LB₁ zE‖ := by
              dsimp [K, gtHalfFieldDeriv, LA, LB₀, LB₁]
              calc
                _ ≤ ‖(1 / (2 * Real.sqrt t)) • gtCoefficientCLM A z₀ -
                      (1 / (2 * Real.sqrt (1-t))) • gtCoefficientCLM B₀ z₀‖ +
                    ‖(1 / (2 * Real.sqrt (1-t))) • gtCoefficientCLM B₁ zE‖ :=
                  norm_sub_le _ _
                _ ≤ (‖(1 / (2 * Real.sqrt t)) • gtCoefficientCLM A z₀‖ +
                      ‖(1 / (2 * Real.sqrt (1-t))) • gtCoefficientCLM B₀ z₀‖) +
                    ‖(1 / (2 * Real.sqrt (1-t))) • gtCoefficientCLM B₁ zE‖ := by
                  gcongr
                  exact norm_sub_le _ _
                _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
            _ ≤ D₀ + D₁ * ‖zE‖ := by
              dsimp [D₀, D₁]
              nlinarith [LB₁.le_opNorm zE,
                abs_nonneg (1 / (2 * Real.sqrt (1-t)))]
        exact hcξ.trans hKn
      have hdensity : gtHalfDensity V A B₀ B₁ H₀ t z₀ zE ≤
          M * Real.exp (c * ‖zE‖) := by
        let base := hasModerateGrowth_gtStateLogPartition V
        have hg := base.F_bound H
        have hm : base.m = 1 := by rfl
        rw [hm, pow_one] at hg
        unfold gtHalfDensity
        rw [show gtHalfField A B₀ B₁ H₀ t z₀ zE = H by rfl, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlog : (1 / 2 : ℝ) * gtStateLogPartition V H ≤ C * (1 + ‖H‖) := by
          have := le_abs_self (gtStateLogPartition V H)
          dsimp [C]
          nlinarith
        calc
          _ ≤ C * (1 + ‖H‖) := hlog
          _ ≤ C * (1 + (R₀ + R₁ * ‖zE‖)) :=
            mul_le_mul_of_nonneg_left (by linarith) hC
          _ = C * (1 + R₀) + c * ‖zE‖ := by dsimp [c]; ring
      have hg0 := gtStateGibbs_nonneg V H ξ
      have hg1 := gtStateGibbs_le_one V H ξ
      have hd0 : 0 ≤ gtHalfDensity V A B₀ B₁ H₀ t z₀ zE := by
        unfold gtHalfDensity
        positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hd0, abs_of_nonneg (by norm_num : (0:ℝ)≤1/2),
        abs_of_nonneg hg0]
      dsimp [bound]
      have hprod : gtHalfDensity V A B₀ B₁ H₀ t z₀ zE *
          gtStateGibbs V H ξ * |K ξ| ≤
          (M * Real.exp (c * ‖zE‖)) * (D₀ + D₁ * ‖zE‖) := by
        calc
          _ ≤ gtHalfDensity V A B₀ B₁ H₀ t z₀ zE * 1 *
              (D₀ + D₁ * ‖zE‖) := by gcongr
          _ ≤ _ := by
            simpa using mul_le_mul_of_nonneg_right hdensity
              (by positivity : 0 ≤ D₀ + D₁ * ‖zE‖)
      calc
        gtHalfDensity V A B₀ B₁ H₀ t z₀ zE * (1/2) *
            (gtStateGibbs V H ξ * |K ξ|) ≤
          (1/2) * ((M * Real.exp (c * ‖zE‖)) *
            (D₀ + D₁ * ‖zE‖)) := by nlinarith
        _ = (1/2) * M *
            (D₀ * Real.exp (c * ‖zE‖) +
              D₁ * (‖zE‖ * Real.exp (c * ‖zE‖))) := by ring
  rw [show (fun z₁ : I₁ → ℝ =>
      gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
        ∑ ξ : S,
          gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
            gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ) =
      fun z₁ => ∑ ξ : S,
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
          (gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
            gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ) by
        funext z₁
        simp only [Finset.mul_sum]]
  rw [integral_finset_sum]
  · have hbase (ξ : S) : Integrable (fun z₁ : I₁ → ℝ =>
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
          gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ)
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) :=
      integrable_gtHalfDensity_mul_gibbs V A B₀ B₁ H₀ t z₀ ξ
    let cA : ℝ := 1 / (2 * Real.sqrt t)
    let cB : ℝ := 1 / (2 * Real.sqrt (1-t))
    have hsqrtB : Real.sqrt (1-t) ≠ 0 :=
      (Real.sqrt_pos.2 (sub_pos.mpr ht.2)).ne'
    have hcB : cB ≠ 0 := by
      dsimp [cB]
      exact one_div_ne_zero (mul_ne_zero (by norm_num) hsqrtB)
    have hinner (ξ : S) : Integrable (fun z₁ : I₁ → ℝ =>
        gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
          gtStateGibbs V
            (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
          inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ))
        (Measure.pi (fun _ : I₁ => gaussianReal 0 1)) := by
      let outer : ℝ := cA * inner ℝ (A ξ) z₀ - cB * inner ℝ (B₀ ξ) z₀
      have ho := (hbase ξ).mul_const ((1 / 2 : ℝ) * outer)
      have hd := (hcoord ξ).sub ho
      have hs := hd.const_mul (-2 / cB)
      apply hs.congr
      filter_upwards with z₁
      simp [gtHalfFieldDeriv, gtCoefficientCLM_apply, cA, cB, outer]
      field_simp [hcB, hsqrtB]
      ring_nf
      rw [real_inner_comm]
    have hone (ξ : S) :
        2 * ((∫ z₁ : I₁ → ℝ,
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
            (gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) / D) =
          ((∫ z₁ : I₁ → ℝ,
              gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
                gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ
              ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) / D) *
            (cA * inner ℝ (A ξ) z₀ - cB * inner ℝ (B₀ ξ) z₀) -
          cB * ∫ z₁ : I₁ → ℝ,
            inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ) *
              (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
                gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ / D)
            ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1) := by
      let outer : ℝ := cA * inner ℝ (A ξ) z₀ - cB * inner ℝ (B₀ ξ) z₀
      rw [show (fun z₁ : I₁ → ℝ =>
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
            (gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ)) =
          fun z₁ => (1 / 2 : ℝ) * outer *
              (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
                gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ) -
            (1 / 2 : ℝ) * cB *
              (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
                gtStateGibbs V
                  (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
                inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ)) by
            funext z₁
            simp [gtHalfFieldDeriv, gtCoefficientCLM_apply, outer, cA, cB]
            rw [real_inner_comm (B₁ ξ) (WithLp.toLp 2 z₁)]
            ring]
      rw [integral_sub ((hbase ξ).const_mul ((1/2) * outer))
        ((hinner ξ).const_mul ((1/2) * cB))]
      rw [integral_const_mul, integral_const_mul]
      rw [show (∫ z₁ : I₁ → ℝ,
          inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ) *
            (gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
              gtStateGibbs V
                (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ / D)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) =
        (∫ z₁ : I₁ → ℝ,
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) *
            gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
            inner ℝ (WithLp.toLp 2 z₁ : EuclideanSpace ℝ I₁) (B₁ ξ)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) / D by
          rw [← integral_div]
          apply integral_congr_ae
          filter_upwards with z₁
          ring]
      field_simp [hD]
      ring
    rw [show 2 * ((∑ ξ : S, ∫ z₁ : I₁ → ℝ,
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
            (gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) / D) =
        ∑ ξ : S, 2 * ((∫ z₁ : I₁ → ℝ,
          gtHalfDensity V A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁) * (1 / 2 : ℝ) *
            (gtStateGibbs V
              (gtHalfField A B₀ B₁ H₀ t z₀ (WithLp.toLp 2 z₁)) ξ *
              gtHalfFieldDeriv A B₀ B₁ t z₀ (WithLp.toLp 2 z₁) ξ)
          ∂Measure.pi (fun _ : I₁ => gaussianReal 0 1)) / D) by
            rw [Finset.sum_div, Finset.mul_sum]]
    simp_rw [hone]
    unfold gtHalfGibbsWeight
    dsimp [cA, cB]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  · intro ξ _
    exact hcoord ξ

/-- The pointwise derivative after integration by parts in the inner
one-half-mass coordinate, but before integration by parts in the outer
mass-zero coordinate. -/
noncomputable def gtHalfDerivativeBeforeOuterIBP
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (z₀ : EuclideanSpace ℝ I₀) : ℝ :=
  ∑ ξ : S,
      gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
        ((1 / (2 * Real.sqrt t)) * inner ℝ (A ξ) z₀ -
          (1 / (2 * Real.sqrt (1-t))) * inner ℝ (B₀ ξ) z₀) -
    (1 / 2 : ℝ) * ∑ ξ : S,
      gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ * inner ℝ (B₁ ξ) (B₁ ξ) +
    (1 / 4 : ℝ) * ∑ ξ : S, ∑ η : S,
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
        inner ℝ (B₁ ξ) (B₁ η)

lemma hasDerivAt_gtHalfTransform_inner_ibp
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z₀ : EuclideanSpace ℝ I₀) :
    HasDerivAt (fun u => gtHalfTransform V A B₀ B₁ H₀ u z₀)
      (gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ t z₀) t := by
  classical
  apply (hasDerivAt_gtHalfTransform_before_ibp V A B₀ B₁ H₀ ht z₀).congr_deriv
  have hs : Real.sqrt (1 - t) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr ht.2)).ne'
  have hinner (ξ η : S) :
      (gtHalfInnerCLM B₁ t (B₁ ξ)) η =
        Real.sqrt (1 - t) * inner ℝ (B₁ η) (B₁ ξ) := by
    simp [gtHalfInnerCLM, gtCoefficientCLM_apply]
  simp_rw [gtHalf_inner_stein V A B₀ B₁ H₀ t z₀]
  simp_rw [hinner]
  unfold gtHalfDerivativeBeforeOuterIBP
  field_simp [hs]
  ring_nf
  have hsumcomm (ξ : S) :
      (∑ η : S,
        Real.sqrt (1-t) * gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
          inner ℝ (B₁ η) (B₁ ξ)) =
      ∑ η : S,
        Real.sqrt (1-t) * gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
          inner ℝ (B₁ ξ) (B₁ η) := by
    apply Finset.sum_congr rfl
    intro η _
    rw [real_inner_comm]
  simp_rw [hsumcomm]
  have hdist :
      (∑ ξ : S,
        (Real.sqrt (1-t) * gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
            inner ℝ (B₁ ξ) (B₁ ξ) +
          (∑ η : S, Real.sqrt (1-t) *
            gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
              inner ℝ (B₁ ξ) (B₁ η)) * (-1/2))) =
        Real.sqrt (1-t) * ∑ ξ : S,
          gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ * inner ℝ (B₁ ξ) (B₁ ξ) +
        (-1/2) * Real.sqrt (1-t) * ∑ ξ : S, ∑ η : S,
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t z₀ ξ η *
            inner ℝ (B₁ ξ) (B₁ η) := by
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    ring
  rw [hdist]
  have hout :
      (∑ ξ : S,
        (Real.sqrt (1-t) * gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
              inner ℝ (A ξ) z₀ * (Real.sqrt t)⁻¹ *
              (Real.sqrt (1-t))⁻¹ * (1/2) +
          gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
              inner ℝ (B₀ ξ) z₀ * (Real.sqrt (1-t))⁻¹ * (-1/2))) =
      ∑ ξ : S,
        (Real.sqrt (1-t) * (Real.sqrt t)⁻¹ * (Real.sqrt (1-t))⁻¹ *
              gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
              inner ℝ (A ξ) z₀ * (1/2) +
          (Real.sqrt (1-t))⁻¹ *
              gtHalfGibbsWeight V A B₀ B₁ H₀ t z₀ ξ *
              inner ℝ (B₀ ξ) z₀ * (-1/2)) := by
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  rw [hout]
  ring

lemma hasDerivAt_gtHalfPressure_before_outer_ibp
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gtHalfPressure V A B₀ B₁ H₀)
      (∫ z₀ : I₀ → ℝ,
        gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)
        ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)) t := by
  classical
  let ε : ℝ := min t (1 - t) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
    linarith
  have hball : ∀ x ∈ Metric.ball t ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hεt : ε ≤ t / 2 := by dsimp [ε]; gcongr; exact min_le_left _ _
    have hε1t : ε ≤ (1 - t) / 2 := by
      dsimp [ε]; gcongr; exact min_le_right _ _
    constructor
    · have := (abs_sub_lt_iff.1 hxt).2
      nlinarith
    · have := (abs_sub_lt_iff.1 hxt).1
      nlinarith
  let cA : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cB : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let C₀ : ℝ := ∑ ξ : S, (cA * ‖A ξ‖ + cB * ‖B₀ ξ‖)
  let C₁ : ℝ := (1 / 2 : ℝ) * ∑ ξ : S, |inner ℝ (B₁ ξ) (B₁ ξ)| +
    (1 / 4 : ℝ) * ∑ ξ : S, ∑ η : S, |inner ℝ (B₁ ξ) (B₁ η)|
  let bound : (I₀ → ℝ) → ℝ := fun z =>
    C₀ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I₀)‖ + C₁
  have hcA : 0 ≤ cA := by dsimp [cA]; positivity
  have hcB : 0 ≤ cB := by dsimp [cB]; positivity
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact Finset.sum_nonneg fun ξ _ => add_nonneg
      (mul_nonneg hcA (norm_nonneg _)) (mul_nonneg hcB (norm_nonneg _))
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hbound : Integrable bound
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
    exact ((integrable_norm_gaussianProduct (I := I₀)).const_mul C₀).add
      (integrable_const C₁)
  have hcoeffA : ∀ x ∈ Metric.ball t ε,
      |1 / (2 * Real.sqrt x)| ≤ cA := by
    intro x hx
    have hxI := hball x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hεt : ε ≤ t / 2 := by dsimp [ε]; gcongr; exact min_le_left _ _
    have htx : t / 2 ≤ x := by
      have := (abs_sub_lt_iff.1 hxt).2
      nlinarith
    have hp : 0 < 2 * Real.sqrt (t / 2) := by
      have : 0 < t / 2 := by linarith [ht.1]
      positivity
    have hi : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
      simpa [one_div] using one_div_le_one_div_of_le hp
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htx) (by norm_num))
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt x))]
    exact hi
  have hcoeffB : ∀ x ∈ Metric.ball t ε,
      |1 / (2 * Real.sqrt (1-x))| ≤ cB := by
    intro x hx
    have hxI := hball x hx
    have hxt : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
    have hε1t : ε ≤ (1 - t) / 2 := by
      dsimp [ε]; gcongr; exact min_le_right _ _
    have htx : (1 - t) / 2 ≤ 1 - x := by
      have := (abs_sub_lt_iff.1 hxt).1
      nlinarith
    have hp : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
      have : 0 < (1 - t) / 2 := by linarith [ht.2]
      positivity
    have hi : 1 / (2 * Real.sqrt (1-x)) ≤
        1 / (2 * Real.sqrt ((1-t)/2)) := by
      simpa [one_div] using one_div_le_one_div_of_le hp
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htx) (by norm_num))
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1-x)))]
    exact hi
  let F : ℝ → (I₀ → ℝ) → ℝ := fun x z =>
    gtHalfTransform V A B₀ B₁ H₀ x (WithLp.toLp 2 z)
  let F' : ℝ → (I₀ → ℝ) → ℝ := fun x z =>
    gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ x (WithLp.toLp 2 z)
  have hFmeas : ∀ᶠ x in nhds t, AEStronglyMeasurable (F x)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
    filter_upwards with x
    exact (integrable_gtHalfTransform V A B₀ B₁ H₀ x).1
  have hFint : Integrable (F t)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) :=
    integrable_gtHalfTransform V A B₀ B₁ H₀ t
  have hF'meas : AEStronglyMeasurable (F' t)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
    have hw (ξ : S) : Continuous (fun z : EuclideanSpace ℝ I₀ =>
        gtHalfGibbsWeight V A B₀ B₁ H₀ t z ξ) := by
      rw [show (fun z : EuclideanSpace ℝ I₀ =>
          gtHalfGibbsWeight V A B₀ B₁ H₀ t z ξ) =
        fun z => gtHalfBaseWeight V (gtHalfInnerCLM B₁ t)
          (gtHalfOuterCLM A B₀ t z + H₀) ξ by
            funext z; rw [gtHalfGibbsWeight_eq_base]]
      exact (continuous_gtHalfBaseWeight V (gtHalfInnerCLM B₁ t) ξ).comp
        ((gtHalfOuterCLM A B₀ t).continuous.add continuous_const)
    have hu (ξ η : S) : Continuous (fun z : EuclideanSpace ℝ I₀ =>
        gtHalfInnerPairWeight V A B₀ B₁ H₀ t z ξ η) := by
      rw [show (fun z : EuclideanSpace ℝ I₀ =>
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t z ξ η) =
        fun z => gtHalfBasePairWeight V (gtHalfInnerCLM B₁ t)
          (gtHalfOuterCLM A B₀ t z + H₀) ξ η by
            funext z; rw [gtHalfInnerPairWeight_eq_base]]
      exact (continuous_gtHalfBasePairWeight V (gtHalfInnerCLM B₁ t) ξ η).comp
        ((gtHalfOuterCLM A B₀ t).continuous.add continuous_const)
    have hc : Continuous (fun z : EuclideanSpace ℝ I₀ =>
        gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ t z) := by
      unfold gtHalfDerivativeBeforeOuterIBP
      fun_prop
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hdom : ∀ᵐ z ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, ‖F' x z‖ ≤ bound z := by
    refine ae_of_all _ (fun z x hx => ?_)
    let zE : EuclideanSpace ℝ I₀ := WithLp.toLp 2 z
    have hw0 (ξ : S) : 0 ≤ gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ :=
      gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ x zE ξ
    have hw1 (ξ : S) : gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ ≤ 1 := by
      rw [gtHalfGibbsWeight_eq_base]
      exact gtHalfBaseWeight_le_one V _ _ ξ
    have hu0 (ξ η : S) : 0 ≤ gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η :=
      gtHalfInnerPairWeight_nonneg V A B₀ B₁ H₀ x zE ξ η
    have hu1 (ξ η : S) : gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η ≤ 1 := by
      rw [gtHalfInnerPairWeight_eq_base]
      exact gtHalfBasePairWeight_le_one V _ _ ξ η
    rw [Real.norm_eq_abs]
    dsimp [F', gtHalfDerivativeBeforeOuterIBP]
    let X := ∑ ξ : S, gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
      ((1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
        (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE)
    let Y := (1/2:ℝ) * ∑ ξ : S,
      gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ * inner ℝ (B₁ ξ) (B₁ ξ)
    let Z := (1/4:ℝ) * ∑ ξ : S, ∑ η : S,
      gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η * inner ℝ (B₁ ξ) (B₁ η)
    change |X - Y + Z| ≤ bound z
    calc
      |X - Y + Z| ≤ |X| + |Y| + |Z| := by
        linarith [abs_add_le (X - Y) Z, abs_sub X Y]
      _ ≤ C₀ * ‖zE‖ + C₁ := by
        dsimp [X, Y, Z]
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
        have hX :
            |∑ ξ : S, gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
              ((1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE)| ≤
              C₀ * ‖zE‖ := by
          calc
            |∑ ξ : S, _| ≤ ∑ ξ : S, |gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
                ((1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                  (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ ξ : S, (cA * ‖A ξ‖ + cB * ‖B₀ ξ‖) * ‖zE‖ := by
              apply Finset.sum_le_sum
              intro ξ _
              rw [abs_mul, abs_of_nonneg (hw0 ξ)]
              have hfield :
                  |(1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                    (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE| ≤
                    |1 / (2 * Real.sqrt x)| * |inner ℝ (A ξ) zE| +
                    |1 / (2 * Real.sqrt (1-x))| * |inner ℝ (B₀ ξ) zE| := by
                simpa [abs_mul] using abs_sub
                  ((1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE)
                  ((1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE)
              have hw := mul_le_mul_of_nonneg_right (hw1 ξ) (abs_nonneg
                ((1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                  (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE))
              calc
                gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
                    |(1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                      (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE| ≤
                    |(1 / (2 * Real.sqrt x)) * inner ℝ (A ξ) zE -
                      (1 / (2 * Real.sqrt (1-x))) * inner ℝ (B₀ ξ) zE| := by
                        simpa using hw
                _ ≤ |1 / (2 * Real.sqrt x)| * |inner ℝ (A ξ) zE| +
                      |1 / (2 * Real.sqrt (1-x))| * |inner ℝ (B₀ ξ) zE| := hfield
                _ ≤ (cA * ‖A ξ‖ + cB * ‖B₀ ξ‖) * ‖zE‖ := by
                  have hA := abs_real_inner_le_norm (A ξ) zE
                  have hB := abs_real_inner_le_norm (B₀ ξ) zE
                  have hmulA := mul_le_mul (hcoeffA x hx) hA
                    (abs_nonneg _) hcA
                  have hmulB := mul_le_mul (hcoeffB x hx) hB
                    (abs_nonneg _) hcB
                  nlinarith
            _ = C₀ * ‖zE‖ := by
              rw [← Finset.sum_mul]
        have hY : (1/2:ℝ) *
            |∑ ξ : S, gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
              inner ℝ (B₁ ξ) (B₁ ξ)| ≤
            (1/2:ℝ) * ∑ ξ : S, |inner ℝ (B₁ ξ) (B₁ ξ)| := by
          gcongr
          calc
              |∑ ξ : S, _| ≤ ∑ ξ : S,
                  |gtHalfGibbsWeight V A B₀ B₁ H₀ x zE ξ *
                    inner ℝ (B₁ ξ) (B₁ ξ)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ ξ : S, |inner ℝ (B₁ ξ) (B₁ ξ)| := by
                apply Finset.sum_le_sum
                intro ξ _
                rw [abs_mul, abs_of_nonneg (hw0 ξ)]
                exact mul_le_of_le_one_left (abs_nonneg _) (hw1 ξ)
        have hZ : (1/4:ℝ) *
            |∑ ξ : S, ∑ η : S,
              gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η *
                inner ℝ (B₁ ξ) (B₁ η)| ≤
            (1/4:ℝ) * ∑ ξ : S, ∑ η : S,
              |inner ℝ (B₁ ξ) (B₁ η)| := by
          gcongr
          calc
              |∑ ξ : S, ∑ η : S, _| ≤ ∑ ξ : S, |∑ η : S,
                  gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η *
                    inner ℝ (B₁ ξ) (B₁ η)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ ξ : S, ∑ η : S, |inner ℝ (B₁ ξ) (B₁ η)| := by
                apply Finset.sum_le_sum
                intro ξ _
                calc
                  |∑ η : S, _| ≤ ∑ η : S,
                      |gtHalfInnerPairWeight V A B₀ B₁ H₀ x zE ξ η *
                        inner ℝ (B₁ ξ) (B₁ η)| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ _ := by
                    apply Finset.sum_le_sum
                    intro η _
                    rw [abs_mul, abs_of_nonneg (hu0 ξ η)]
                    exact mul_le_of_le_one_left (abs_nonneg _) (hu1 ξ η)
        dsimp [C₁]
        calc
          _ ≤ (C₀ * ‖zE‖ + (1/2:ℝ) * ∑ ξ : S,
                |inner ℝ (B₁ ξ) (B₁ ξ)|) +
              (1/4:ℝ) * ∑ ξ : S, ∑ η : S,
                |inner ℝ (B₁ ξ) (B₁ η)| :=
            add_le_add (add_le_add hX hY) hZ
          _ = _ := by ring
      _ = bound z := by rfl
  have hdiff : ∀ᵐ z ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, HasDerivAt (fun u => F u z) (F' x z) x := by
    refine ae_of_all _ (fun z x hx => ?_)
    exact hasDerivAt_gtHalfTransform_inner_ibp V A B₀ B₁ H₀ (hball x hx)
      (WithLp.toLp 2 z)
  have hm := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Measure.pi (fun _ : I₀ => gaussianReal 0 1))
    (F := F) (F' := F') (x₀ := t) (bound := bound)
    (s := Metric.ball t ε) (Metric.ball_mem_nhds t hε)
    hFmeas hFint hF'meas hdom hbound hdiff).2
  exact hm

lemma integrable_gtHalfGibbsWeight_outer
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (ξ : S) :
    Integrable (fun z : I₀ → ℝ =>
      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ I₀ =>
      gtHalfGibbsWeight V A B₀ B₁ H₀ t z ξ) := by
    rw [show (fun z : EuclideanSpace ℝ I₀ =>
        gtHalfGibbsWeight V A B₀ B₁ H₀ t z ξ) =
      fun z => gtHalfBaseWeight V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z + H₀) ξ by
          funext z; rw [gtHalfGibbsWeight_eq_base]]
    exact (continuous_gtHalfBaseWeight V (gtHalfInnerCLM B₁ t) ξ).comp
      ((gtHalfOuterCLM A B₀ t).continuous.add continuous_const)
  apply (integrable_const (1 : ℝ)).mono'
  · exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ t _ ξ)]
    simpa using (show gtHalfGibbsWeight V A B₀ B₁ H₀ t
      (WithLp.toLp 2 z) ξ ≤ 1 by
        rw [gtHalfGibbsWeight_eq_base]
        exact gtHalfBaseWeight_le_one V _ _ ξ)

lemma integrable_gtHalfInnerPairWeight_outer
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (ξ η : S) :
    Integrable (fun z : I₀ → ℝ =>
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ I₀ =>
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t z ξ η) := by
    rw [show (fun z : EuclideanSpace ℝ I₀ =>
        gtHalfInnerPairWeight V A B₀ B₁ H₀ t z ξ η) =
      fun z => gtHalfBasePairWeight V (gtHalfInnerCLM B₁ t)
        (gtHalfOuterCLM A B₀ t z + H₀) ξ η by
          funext z; rw [gtHalfInnerPairWeight_eq_base]]
    exact (continuous_gtHalfBasePairWeight V (gtHalfInnerCLM B₁ t) ξ η).comp
      ((gtHalfOuterCLM A B₀ t).continuous.add continuous_const)
  apply (integrable_const (1 : ℝ)).mono'
  · exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gtHalfInnerPairWeight_nonneg V A B₀ B₁ H₀ t _ ξ η)]
    simpa using (show gtHalfInnerPairWeight V A B₀ B₁ H₀ t
      (WithLp.toLp 2 z) ξ η ≤ 1 by
        rw [gtHalfInnerPairWeight_eq_base]
        exact gtHalfBasePairWeight_le_one V _ _ ξ η)

lemma integrable_inner_mul_gtHalfGibbsWeight_outer
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ C : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (t : ℝ) (ξ : S) :
    Integrable (fun z : I₀ → ℝ =>
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (C ξ) *
        gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ)
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
  let bound : (I₀ → ℝ) → ℝ := fun z =>
    ‖C ξ‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I₀)‖
  have hb : Integrable bound (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) :=
    (integrable_norm_gaussianProduct (I := I₀)).const_mul ‖C ξ‖
  apply hb.mono'
  · have hi := integrable_gtHalfGibbsWeight_outer V A B₀ B₁ H₀ t ξ
    have hm : AEStronglyMeasurable (fun z : I₀ → ℝ =>
        inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (C ξ))
        (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
      fun_prop
    exact hm.mul hi.1
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    have hw0 := gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ t
      (WithLp.toLp 2 z) ξ
    rw [abs_of_nonneg hw0]
    have hw1 : gtHalfGibbsWeight V A B₀ B₁ H₀ t
        (WithLp.toLp 2 z) ξ ≤ 1 := by
      rw [gtHalfGibbsWeight_eq_base]
      exact gtHalfBaseWeight_le_one V _ _ ξ
    have hi := abs_real_inner_le_norm
      (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (C ξ)
    dsimp [bound]
    nlinarith [mul_le_mul_of_nonneg_left hw1 (abs_nonneg
      (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (C ξ)))]

lemma integrable_gtHalfDerivativeExpression_outer
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S) (t : ℝ) :
    Integrable (fun z : I₀ → ℝ =>
      gtHalfDerivativeExpression V A B₀ B₁ H₀ t (WithLp.toLp 2 z))
      (Measure.pi (fun _ : I₀ => gaussianReal 0 1)) := by
  let μ := Measure.pi (fun _ : I₀ => gaussianReal 0 1)
  have hw (ξ : S) := integrable_gtHalfGibbsWeight_outer V A B₀ B₁ H₀ t ξ
  have hu (ξ η : S) := integrable_gtHalfInnerPairWeight_outer
    V A B₀ B₁ H₀ t ξ η
  have hww (ξ η : S) : Integrable (fun z : I₀ → ℝ =>
      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
        gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) η) μ := by
    apply (hw η).bdd_mul (hw ξ).1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ)]
    rw [gtHalfGibbsWeight_eq_base]
    exact gtHalfBaseWeight_le_one V _ _ ξ
  have hdiag : Integrable (fun z : I₀ → ℝ =>
      ∑ ξ : S, gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
        (inner ℝ (A ξ) (A ξ) - inner ℝ (B₀ ξ) (B₀ ξ) -
          inner ℝ (B₁ ξ) (B₁ ξ))) μ := by
    exact integrable_finset_sum _ fun ξ _ => (hw ξ).mul_const _
  have houter : Integrable (fun z : I₀ → ℝ =>
      ∑ ξ : S, ∑ η : S,
        (gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
          gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) η) *
          (inner ℝ (A ξ) (A η) - inner ℝ (B₀ ξ) (B₀ η))) μ := by
    exact integrable_finset_sum _ fun ξ _ => integrable_finset_sum _ fun η _ =>
      (hww ξ η).mul_const _
  have hinner : Integrable (fun z : I₀ → ℝ =>
      ∑ ξ : S, ∑ η : S,
        gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η *
          (inner ℝ (A ξ) (A η) - inner ℝ (B₀ ξ) (B₀ η) -
            inner ℝ (B₁ ξ) (B₁ η))) μ := by
    exact integrable_finset_sum _ fun ξ _ => integrable_finset_sum _ fun η _ =>
      (hu ξ η).mul_const _
  unfold gtHalfDerivativeExpression
  exact ((hdiag.const_mul (1 / 2 : ℝ)).sub
    (houter.const_mul (1 / 4 : ℝ))).sub (hinner.const_mul (1 / 4 : ℝ))

lemma hasDerivAt_gtHalfPressure_ibp
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B₀ η) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gtHalfPressure V A B₀ B₁ H₀)
      (∫ z₀ : I₀ → ℝ,
        gtHalfDerivativeExpression V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)
        ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)) t := by
  classical
  apply (hasDerivAt_gtHalfPressure_before_outer_ibp V A B₀ B₁ H₀ ht).congr_deriv
  let μ := Measure.pi (fun _ : I₀ => gaussianReal 0 1)
  have hsA : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
  have hsB : Real.sqrt (1-t) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr ht.2)).ne'
  have hMA (ξ η : S) :
      (gtHalfOuterCLM A B₀ t (A ξ)) η =
        Real.sqrt t * inner ℝ (A η) (A ξ) := by
    simp [gtHalfOuterCLM, gtCoefficientCLM_apply,
      show inner ℝ (B₀ η) (A ξ) = 0 by
        rw [real_inner_comm]; exact hAB ξ η]
  have hMB (ξ η : S) :
      (gtHalfOuterCLM A B₀ t (B₀ ξ)) η =
        Real.sqrt (1-t) * inner ℝ (B₀ η) (B₀ ξ) := by
    simp [gtHalfOuterCLM, gtCoefficientCLM_apply, hAB η ξ]
  have hsteinA (ξ : S) := gtHalf_outer_stein V A B₀ A B₁ H₀ t ξ
  have hsteinB (ξ : S) := gtHalf_outer_stein V A B₀ B₀ B₁ H₀ t ξ
  simp_rw [hMA] at hsteinA
  simp_rw [hMB] at hsteinB
  have hw (ξ : S) := integrable_gtHalfGibbsWeight_outer V A B₀ B₁ H₀ t ξ
  have hu (ξ η : S) := integrable_gtHalfInnerPairWeight_outer
    V A B₀ B₁ H₀ t ξ η
  have hzA (ξ : S) := integrable_inner_mul_gtHalfGibbsWeight_outer
    V A B₀ A B₁ H₀ t ξ
  have hzB (ξ : S) := integrable_inner_mul_gtHalfGibbsWeight_outer
    V A B₀ B₀ B₁ H₀ t ξ
  have hx (ξ : S) : Integrable (fun z : I₀ → ℝ =>
      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
        (1 / (2 * Real.sqrt t) * inner ℝ (A ξ) (WithLp.toLp 2 z) -
          1 / (2 * Real.sqrt (1-t)) * inner ℝ (B₀ ξ) (WithLp.toLp 2 z))) μ := by
    apply (((hzA ξ).const_mul (1 / (2 * Real.sqrt t))).sub
      ((hzB ξ).const_mul (1 / (2 * Real.sqrt (1-t))))).congr
    filter_upwards with z
    simp only [Pi.sub_apply]
    rw [real_inner_comm (WithLp.toLp 2 z) (A ξ),
      real_inner_comm (WithLp.toLp 2 z) (B₀ ξ)]
    ring
  have hy (ξ : S) : Integrable (fun z : I₀ → ℝ =>
      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
        inner ℝ (B₁ ξ) (B₁ ξ)) μ := by
    apply ((hw ξ).const_mul (inner ℝ (B₁ ξ) (B₁ ξ))).congr
    filter_upwards with z
    ring
  have huv (ξ η : S) : Integrable (fun z : I₀ → ℝ =>
      gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η *
        inner ℝ (B₁ ξ) (B₁ η)) μ := by
    apply ((hu ξ η).const_mul (inner ℝ (B₁ ξ) (B₁ η))).congr
    filter_upwards with z
    ring
  have hbefore :
      (∫ z : I₀ → ℝ,
          gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ∂μ) =
        ∑ ξ : S,
          ((1 / (2 * Real.sqrt t)) *
              ∫ z : I₀ → ℝ, inner ℝ (WithLp.toLp 2 z) (A ξ) *
                gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ ∂μ -
            (1 / (2 * Real.sqrt (1-t))) *
              ∫ z : I₀ → ℝ, inner ℝ (WithLp.toLp 2 z) (B₀ ξ) *
                gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ ∂μ) -
          (1/2:ℝ) * ∑ ξ : S, inner ℝ (B₁ ξ) (B₁ ξ) *
            ∫ z : I₀ → ℝ,
              gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ ∂μ +
          (1/4:ℝ) * ∑ ξ : S, ∑ η : S, inner ℝ (B₁ ξ) (B₁ η) *
            ∫ z : I₀ → ℝ,
              gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η ∂μ := by
    have hpoint : (fun z : I₀ → ℝ =>
        gtHalfDerivativeBeforeOuterIBP V A B₀ B₁ H₀ t (WithLp.toLp 2 z)) =
      fun z =>
        (∑ ξ : S,
          ((1 / (2 * Real.sqrt t)) *
              (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (A ξ) *
                gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ) -
            (1 / (2 * Real.sqrt (1-t))) *
              (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (B₀ ξ) *
                gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ))) -
        (1/2:ℝ) * ∑ ξ : S, inner ℝ (B₁ ξ) (B₁ ξ) *
          gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ +
        (1/4:ℝ) * ∑ ξ : S, ∑ η : S, inner ℝ (B₁ ξ) (B₁ η) *
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η := by
      funext z
      unfold gtHalfDerivativeBeforeOuterIBP
      simp_rw [real_inner_comm (A _) (WithLp.toLp 2 z),
        real_inner_comm (B₀ _) (WithLp.toLp 2 z)]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· - ·)
        · apply Finset.sum_congr rfl
          intro ξ _
          ring
        · apply congrArg (fun x : ℝ => (1 / 2) * x)
          apply Finset.sum_congr rfl
          intro ξ _
          ring
      · apply congrArg (fun x : ℝ => (1 / 4) * x)
        apply Finset.sum_congr rfl
        intro ξ _
        apply Finset.sum_congr rfl
        intro η _
        ring
    rw [hpoint]
    rw [integral_add]
    · rw [integral_sub]
      · rw [integral_finset_sum]
        · rw [show (∑ ξ : S, ∫ z : I₀ → ℝ,
                (1 / (2 * Real.sqrt t)) *
                    (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (A ξ) *
                      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ) -
                  (1 / (2 * Real.sqrt (1-t))) *
                    (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (B₀ ξ) *
                      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ) ∂μ) =
              ∑ ξ : S,
                ((∫ z : I₀ → ℝ, (1 / (2 * Real.sqrt t)) *
                    (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (A ξ) *
                      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ) ∂μ) -
                 (∫ z : I₀ → ℝ, (1 / (2 * Real.sqrt (1-t))) *
                    (inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I₀) (B₀ ξ) *
                      gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ) ∂μ)) by
            apply Finset.sum_congr rfl
            intro ξ _
            rw [integral_sub ((hzA ξ).const_mul _) ((hzB ξ).const_mul _)]]
          rw [Finset.sum_sub_distrib]
          simp_rw [integral_const_mul]
          rw [integral_finset_sum Finset.univ (fun ξ _ => (hw ξ).const_mul _)]
          simp_rw [integral_const_mul]
          rw [integral_finset_sum Finset.univ (fun ξ _ =>
            integrable_finset_sum Finset.univ (fun η _ => (hu ξ η).const_mul _))]
          simp_rw [integral_finset_sum Finset.univ
            (fun η _ => (hu _ η).const_mul _), integral_const_mul]
          rw [Finset.sum_sub_distrib]
        · intro ξ _
          exact ((hzA ξ).const_mul _).sub ((hzB ξ).const_mul _)
      · exact integrable_finset_sum _ fun ξ _ =>
          ((hzA ξ).const_mul _).sub ((hzB ξ).const_mul _)
      · exact (integrable_finset_sum _ fun ξ _ =>
          (hw ξ).const_mul _).const_mul _
    · exact (integrable_finset_sum _ fun ξ _ =>
          ((hzA ξ).const_mul _).sub ((hzB ξ).const_mul _)).sub
        ((integrable_finset_sum _ fun ξ _ => (hw ξ).const_mul _).const_mul _)
    · exact (integrable_finset_sum _ fun ξ _ =>
        integrable_finset_sum _ fun η _ => (hu ξ η).const_mul _).const_mul _
  rw [hbefore]
  -- Substitute the two outer Stein identities and normalize the square-root
  -- coefficients.  All remaining terms are finite sums of real scalars.
  dsimp [μ]
  simp_rw [hsteinA, hsteinB]
  let μ₀ := Measure.pi (fun _ : I₀ => gaussianReal 0 1)
  let w : (I₀ → ℝ) → S → ℝ := fun z ξ =>
    gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ
  let u : (I₀ → ℝ) → S → S → ℝ := fun z ξ η =>
    gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η
  have hw0 (z : I₀ → ℝ) (ξ : S) : 0 ≤ w z ξ :=
    gtHalfGibbsWeight_nonneg V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ
  have hw1 (z : I₀ → ℝ) (ξ : S) : w z ξ ≤ 1 := by
    dsimp [w]
    rw [gtHalfGibbsWeight_eq_base]
    exact gtHalfBaseWeight_le_one V _ _ ξ
  have hww (ξ η : S) : Integrable (fun z => w z ξ * w z η) μ₀ := by
    apply (hw ξ).mono'
    · exact (hw ξ).1.mul (hw η).1
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 z ξ),
        abs_of_nonneg (hw0 z η)]
      change w z ξ * w z η ≤ w z ξ
      exact mul_le_of_le_one_right (hw0 z ξ) (hw1 z η)
  let RA : S → (I₀ → ℝ) → ℝ := fun ξ z =>
    w z ξ * (Real.sqrt t * inner ℝ (A ξ) (A ξ)) -
      (1 / 2 : ℝ) * ∑ η : S,
        u z ξ η * (Real.sqrt t * inner ℝ (A η) (A ξ)) -
      (1 / 2 : ℝ) * w z ξ * ∑ η : S,
        w z η * (Real.sqrt t * inner ℝ (A η) (A ξ))
  let RB : S → (I₀ → ℝ) → ℝ := fun ξ z =>
    w z ξ * (Real.sqrt (1 - t) * inner ℝ (B₀ ξ) (B₀ ξ)) -
      (1 / 2 : ℝ) * ∑ η : S,
        u z ξ η * (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ)) -
      (1 / 2 : ℝ) * w z ξ * ∑ η : S,
        w z η * (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ))
  have hRA (ξ : S) : Integrable (RA ξ) μ₀ := by
    have h1 := (hw ξ).const_mul (Real.sqrt t * inner ℝ (A ξ) (A ξ))
    have h2 := (integrable_finset_sum Finset.univ fun η _ =>
      (hu ξ η).const_mul (Real.sqrt t * inner ℝ (A η) (A ξ))).const_mul (1 / 2 : ℝ)
    have h3 := (integrable_finset_sum Finset.univ fun η _ =>
      (hww ξ η).const_mul (Real.sqrt t * inner ℝ (A η) (A ξ))).const_mul
        (1 / 2 : ℝ)
    apply (h1.sub h2 |>.sub h3).congr
    filter_upwards with z
    dsimp [RA, w, u]
    simp_rw [Finset.mul_sum]
    apply congrArg₂ (· - ·)
    · apply congrArg₂ (· - ·)
      · ring
      · apply Finset.sum_congr rfl
        intro η _
        ring
    · apply Finset.sum_congr rfl
      intro η _
      ring
  have hRB (ξ : S) : Integrable (RB ξ) μ₀ := by
    have h1 := (hw ξ).const_mul
      (Real.sqrt (1 - t) * inner ℝ (B₀ ξ) (B₀ ξ))
    have h2 := (integrable_finset_sum Finset.univ fun η _ =>
      (hu ξ η).const_mul
        (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ))).const_mul (1 / 2 : ℝ)
    have h3 := (integrable_finset_sum Finset.univ fun η _ =>
      (hww ξ η).const_mul
        (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ))).const_mul (1 / 2 : ℝ)
    apply (h1.sub h2 |>.sub h3).congr
    filter_upwards with z
    dsimp [RB, w, u]
    simp_rw [Finset.mul_sum]
    apply congrArg₂ (· - ·)
    · apply congrArg₂ (· - ·)
      · ring
      · apply Finset.sum_congr rfl
        intro η _
        ring
    · apply Finset.sum_congr rfl
      intro η _
      ring
  let F : S → (I₀ → ℝ) → ℝ := fun ξ z =>
    (1 / (2 * Real.sqrt t)) * RA ξ z -
      (1 / (2 * Real.sqrt (1 - t))) * RB ξ z -
      (1 / 2 : ℝ) * inner ℝ (B₁ ξ) (B₁ ξ) * w z ξ +
      (1 / 4 : ℝ) * ∑ η : S, inner ℝ (B₁ ξ) (B₁ η) * u z ξ η
  have hF (ξ : S) : Integrable (F ξ) μ₀ := by
    have hFa := (hRA ξ).const_mul (1 / (2 * Real.sqrt t))
    have hFb := (hRB ξ).const_mul (1 / (2 * Real.sqrt (1 - t)))
    have hFc := (hw ξ).const_mul
      ((1 / 2 : ℝ) * inner ℝ (B₁ ξ) (B₁ ξ))
    have hFd := (integrable_finset_sum Finset.univ fun η _ =>
      (hu ξ η).const_mul (inner ℝ (B₁ ξ) (B₁ η))).const_mul (1 / 4 : ℝ)
    apply (((hFa.sub hFb).sub hFc).add hFd).congr
    filter_upwards with z
    dsimp [F, w, u]
  have hFint (ξ : S) :
      (∫ z, F ξ z ∂μ₀) =
        (1 / (2 * Real.sqrt t)) * (∫ z, RA ξ z ∂μ₀) -
          (1 / (2 * Real.sqrt (1 - t))) * (∫ z, RB ξ z ∂μ₀) -
          (1 / 2 : ℝ) * inner ℝ (B₁ ξ) (B₁ ξ) * (∫ z, w z ξ ∂μ₀) +
          (1 / 4 : ℝ) * ∑ η : S,
            inner ℝ (B₁ ξ) (B₁ η) * (∫ z, u z ξ η ∂μ₀) := by
    let fA := fun z => (1 / (2 * Real.sqrt t)) * RA ξ z
    let fB := fun z => (1 / (2 * Real.sqrt (1 - t))) * RB ξ z
    let fC := fun z => (1 / 2 : ℝ) * inner ℝ (B₁ ξ) (B₁ ξ) * w z ξ
    let fD := fun z => (1 / 4 : ℝ) * ∑ η : S,
      inner ℝ (B₁ ξ) (B₁ η) * u z ξ η
    have hA : Integrable fA μ₀ := (hRA ξ).const_mul _
    have hB : Integrable fB μ₀ := (hRB ξ).const_mul _
    have hC : Integrable fC μ₀ := (hw ξ).const_mul _
    have hD : Integrable fD μ₀ :=
      (integrable_finset_sum Finset.univ fun η _ =>
        (hu ξ η).const_mul _).const_mul _
    change (∫ z, (fA - fB - fC) z + fD z ∂μ₀) = _
    rw [integral_add ((hA.sub hB).sub hC) hD]
    change (∫ z, (fA - fB) z - fC z ∂μ₀) + (∫ z, fD z ∂μ₀) = _
    rw [integral_sub (hA.sub hB) hC]
    change ((∫ z, fA z - fB z ∂μ₀) - (∫ z, fC z ∂μ₀)) +
      (∫ z, fD z ∂μ₀) = _
    rw [integral_sub hA hB]
    dsimp [fA, fB, fC, fD]
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro η _
      exact (hu ξ η).const_mul _
  change
    (∑ ξ : S, ((1 / (2 * Real.sqrt t)) * (∫ z, RA ξ z ∂μ₀) -
      (1 / (2 * Real.sqrt (1 - t))) * (∫ z, RB ξ z ∂μ₀))) -
      (1 / 2 : ℝ) * ∑ ξ : S,
        inner ℝ (B₁ ξ) (B₁ ξ) * (∫ z, w z ξ ∂μ₀) +
      (1 / 4 : ℝ) * ∑ ξ : S, ∑ η : S,
        inner ℝ (B₁ ξ) (B₁ η) * (∫ z, u z ξ η ∂μ₀) =
      ∫ z, gtHalfDerivativeExpression V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ∂μ₀
  have hcollect :
      (∑ ξ : S, ((1 / (2 * Real.sqrt t)) * (∫ z, RA ξ z ∂μ₀) -
        (1 / (2 * Real.sqrt (1 - t))) * (∫ z, RB ξ z ∂μ₀))) -
        (1 / 2 : ℝ) * ∑ ξ : S,
          inner ℝ (B₁ ξ) (B₁ ξ) * (∫ z, w z ξ ∂μ₀) +
        (1 / 4 : ℝ) * ∑ ξ : S, ∑ η : S,
          inner ℝ (B₁ ξ) (B₁ η) * (∫ z, u z ξ η ∂μ₀) =
        ∑ ξ : S, ∫ z, F ξ z ∂μ₀ := by
    simp_rw [hFint, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  rw [hcollect, ← integral_finset_sum Finset.univ (fun ξ _ => hF ξ)]
  apply integral_congr_ae
  filter_upwards with z
  have hAu (ξ : S) :
      (∑ η : S, u z ξ η * (Real.sqrt t * inner ℝ (A η) (A ξ))) =
        Real.sqrt t * ∑ η : S, u z ξ η * inner ℝ (A ξ) (A η) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [real_inner_comm]
    ring
  have hAw (ξ : S) :
      (1 / 2 : ℝ) * w z ξ *
          (∑ η : S, w z η * (Real.sqrt t * inner ℝ (A η) (A ξ))) =
        (1 / 2 : ℝ) * Real.sqrt t *
          ∑ η : S, (w z ξ * w z η) * inner ℝ (A ξ) (A η) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [real_inner_comm]
    ring
  have hBu (ξ : S) :
      (∑ η : S, u z ξ η * (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ))) =
        Real.sqrt (1 - t) * ∑ η : S, u z ξ η * inner ℝ (B₀ ξ) (B₀ η) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [real_inner_comm]
    ring
  have hBw (ξ : S) :
      (1 / 2 : ℝ) * w z ξ *
          (∑ η : S, w z η * (Real.sqrt (1 - t) * inner ℝ (B₀ η) (B₀ ξ))) =
        (1 / 2 : ℝ) * Real.sqrt (1 - t) *
          ∑ η : S, (w z ξ * w z η) * inner ℝ (B₀ ξ) (B₀ η) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [real_inner_comm]
    ring
  have hRAnorm (ξ : S) :
      (1 / (2 * Real.sqrt t)) * RA ξ z =
        (1 / 2 : ℝ) * w z ξ * inner ℝ (A ξ) (A ξ) -
          (1 / 4 : ℝ) * ∑ η : S, u z ξ η * inner ℝ (A ξ) (A η) -
          (1 / 4 : ℝ) * ∑ η : S,
            (w z ξ * w z η) * inner ℝ (A ξ) (A η) := by
    dsimp [RA]
    rw [hAu, hAw]
    field_simp [hsA]
    ring
  have hRBnorm (ξ : S) :
      (1 / (2 * Real.sqrt (1 - t))) * RB ξ z =
        (1 / 2 : ℝ) * w z ξ * inner ℝ (B₀ ξ) (B₀ ξ) -
          (1 / 4 : ℝ) * ∑ η : S, u z ξ η * inner ℝ (B₀ ξ) (B₀ η) -
          (1 / 4 : ℝ) * ∑ η : S,
            (w z ξ * w z η) * inner ℝ (B₀ ξ) (B₀ η) := by
    dsimp [RB]
    rw [hBu, hBw]
    field_simp [hsB]
    ring
  dsimp [F]
  simp_rw [hRAnorm, hRBnorm]
  dsimp [w, u]
  unfold gtHalfDerivativeExpression
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiagB₁ :
      (∑ ξ : S, inner ℝ (B₁ ξ) (B₁ ξ) *
          gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ * (1 / 2 : ℝ)) =
        ∑ ξ : S, gtHalfGibbsWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ *
          inner ℝ (B₁ ξ) (B₁ ξ) * (1 / 2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  have hpairB₁ :
      (∑ ξ : S, ∑ η : S, inner ℝ (B₁ ξ) (B₁ η) *
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η * (1 / 4 : ℝ)) =
        ∑ ξ : S, ∑ η : S,
          gtHalfInnerPairWeight V A B₀ B₁ H₀ t (WithLp.toLp 2 z) ξ η *
            inner ℝ (B₁ ξ) (B₁ η) * (1 / 4 : ℝ) := by
    apply Finset.sum_congr rfl
    intro ξ _
    apply Finset.sum_congr rfl
    intro η _
    ring
  rw [hdiagB₁, hpairB₁]
  have hnegHalf (a : ℝ) : a * (-1 / 2 : ℝ) = -(a * (1 / 2 : ℝ)) := by ring
  have hnegQuarter (a : ℝ) : a * (-1 / 4 : ℝ) = -(a * (1 / 4 : ℝ)) := by ring
  simp_rw [hnegHalf, hnegQuarter, Finset.sum_neg_distrib]
  ring

/-- Integrating a uniform bound on the half-mass interpolation derivative. -/
theorem gtHalfPressure_one_le_zero_add
    {S I₀ I₁ : Type*} [Fintype S] [Nonempty S]
    [Fintype I₀] [Fintype I₁]
    (V : S → ℝ) (A B₀ : S → EuclideanSpace ℝ I₀)
    (B₁ : S → EuclideanSpace ℝ I₁) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B₀ η) = 0) (K : ℝ)
    (hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ z₀,
      gtHalfDerivativeExpression V A B₀ B₁ H₀ t z₀ ≤ K) :
    gtHalfPressure V A B₀ B₁ H₀ 1 ≤
      gtHalfPressure V A B₀ B₁ H₀ 0 + K := by
  let g : ℝ → ℝ := gtHalfPressure V A B₀ B₁ H₀ - fun t => K * t
  have hgcont : Continuous g :=
    (continuous_gtHalfPressure V A B₀ B₁ H₀).sub
      (continuous_const.mul continuous_id)
  have hgderiv (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt g
        ((∫ z₀ : I₀ → ℝ,
          gtHalfDerivativeExpression V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)
          ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)) - K) t := by
    simpa [g] using
      (hasDerivAt_gtHalfPressure_ibp V A B₀ B₁ H₀ hAB ht).sub
        ((hasDerivAt_id t).const_mul K)
  have hganti : AntitoneOn g (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
      hgcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hgderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgderiv t ht).deriv]
      apply sub_nonpos.mpr
      calc
        (∫ z₀ : I₀ → ℝ,
            gtHalfDerivativeExpression V A B₀ B₁ H₀ t (WithLp.toLp 2 z₀)
            ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1)) ≤
            ∫ _z₀ : I₀ → ℝ, K
              ∂Measure.pi (fun _ : I₀ => gaussianReal 0 1) := by
          apply integral_mono
          · exact integrable_gtHalfDerivativeExpression_outer V A B₀ B₁ H₀ t
          · exact integrable_const K
          · intro z₀
            exact hbound t ht (WithLp.toLp 2 z₀)
        _ = K := by simp
  have hends := hganti
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (0 : ℝ) ≤ 1 by norm_num)
  dsimp [g] at hends
  linarith

theorem gtConstrainedHalfPressure_one_le_zero
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q) (hqr : q ≤ |v|)
    (hv : v ∈ attainableOverlaps N) :
    gtConstrainedHalfPressure N β h q s v lam hv 1 ≤
      gtConstrainedHalfPressure N β h q s v lam hv 0 +
        ((N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2)) / 2 +
        ((N : ℝ) * gtScalarVariance β s v q -
          (N : ℝ) * gtScalarVariance β s v |v|) / 4 := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedHalfPressure
  have hcomp := gtHalfPressure_one_le_zero_add
    (V := fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
    (A := fun p => gtOrdinaryBarePhysicalCoefficient N β q s p.1)
    (B₀ := fun p => gtHalfOuterTrialCoefficient N β q s v p.1)
    (B₁ := fun p => gtHalfInnerTrialCoefficient N β q s v p.1)
    (H₀ := 0)
    (hAB := fun p r =>
      gtHalfOuter_coefficients_orthogonal N β q s v p.1 r.1)
    (K := ((N : ℝ) * (s * β ^ 2 * (1 - |v|) ^ 2)) / 2 +
      ((N : ℝ) * gtScalarVariance β s v q -
        (N : ℝ) * gtScalarVariance β s v |v|) / 4)
    (hbound := fun t ht z₀ =>
      gtConstrainedHalfDerivativeExpression_le hN hs hq0 hqr hv t z₀)
  convert hcomp using 1 <;> ring

end SpinGlass.AT
