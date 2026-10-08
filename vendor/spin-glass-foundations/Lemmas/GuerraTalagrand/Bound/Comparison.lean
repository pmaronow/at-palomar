module

public import Lemmas.GuerraTalagrand.Bound.FiniteState

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped ContDiff ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

/-- The linear field whose value at state `ξ` is `⟪A ξ, z⟫`. -/
noncomputable def gtCoefficientCLM
    {S I : Type*} [Fintype S] [Fintype I]
    (A : S → EuclideanSpace ℝ I) :
    EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
  ∑ ξ : S, (ContinuousLinearMap.innerSL ℝ (A ξ)).smulRight
    ((EuclideanSpace.basisFun S ℝ) ξ)

lemma gtCoefficientCLM_apply
    {S I : Type*} [Fintype S] [Fintype I]
    (A : S → EuclideanSpace ℝ I) (z : EuclideanSpace ℝ I) (ξ : S) :
    gtCoefficientCLM A z ξ = inner ℝ (A ξ) z := by
  classical
  simp [gtCoefficientCLM]
  rw [Finset.sum_eq_single ξ]
  · simp
  · intro b _ hb
    exact mul_eq_zero_of_right _ (by simp [Pi.single_apply, hb])
  · simp

/-- The ordinary finite-state Gaussian interpolation field. -/
noncomputable def gtOrdinaryField
    {S I : Type*} [Fintype S] [Fintype I]
    (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) (z : EuclideanSpace ℝ I) : GTStateSpace S :=
  Real.sqrt t • gtCoefficientCLM A z +
    Real.sqrt (1 - t) • gtCoefficientCLM B z + H₀

/-- Derivative field on the open interpolation interval. -/
noncomputable def gtOrdinaryFieldDeriv
    {S I : Type*} [Fintype S] [Fintype I]
    (A B : S → EuclideanSpace ℝ I) (t : ℝ)
    (z : EuclideanSpace ℝ I) : GTStateSpace S :=
  (1 / (2 * Real.sqrt t)) • gtCoefficientCLM A z -
    (1 / (2 * Real.sqrt (1 - t))) • gtCoefficientCLM B z

lemma hasDerivAt_gtOrdinaryField
    {S I : Type*} [Fintype S] [Fintype I]
    (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z : EuclideanSpace ℝ I) :
    HasDerivAt (fun u => gtOrdinaryField A B H₀ u z)
      (gtOrdinaryFieldDeriv A B t z) t := by
  have hA := (Real.hasDerivAt_sqrt ht.1.ne').smul_const (gtCoefficientCLM A z)
  have hsub : HasDerivAt (fun u : ℝ => (1 : ℝ) - u) (-1) t := by
    simpa using HasDerivAt.const_sub (c := (1 : ℝ)) (hasDerivAt_id t)
  have hB := ((Real.hasDerivAt_sqrt (ne_of_gt (sub_pos.mpr ht.2))).comp t hsub
    ).smul_const (gtCoefficientCLM B z)
  have hsum := (hA.add hB).add_const H₀
  simpa [gtOrdinaryField, gtOrdinaryFieldDeriv, sub_eq_add_neg,
    mul_smul] using hsum

lemma hasDerivAt_gtStateLogPartition_field
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (z : EuclideanSpace ℝ I) :
    HasDerivAt
      (fun u => gtStateLogPartition V (gtOrdinaryField A B H₀ u z))
      (∑ ξ : S, gtStateGibbs V (gtOrdinaryField A B H₀ t z) ξ *
        gtOrdinaryFieldDeriv A B t z ξ) t := by
  have hlog : HasFDerivAt (gtStateLogPartition V)
      (fderiv ℝ (gtStateLogPartition V) (gtOrdinaryField A B H₀ t z))
      (gtOrdinaryField A B H₀ t z) :=
    ((contDiff_gtStateLogPartition V).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hcomp := hlog.comp_hasDerivAt t
    (hasDerivAt_gtOrdinaryField A B H₀ ht z)
  rw [fderiv_gtStateLogPartition_apply] at hcomp
  exact hcomp

/-- The pressure along the ordinary finite-state Gaussian interpolation. -/
noncomputable def gtOrdinaryPressure
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) : ℝ :=
  ∫ z, gtStateLogPartition V
      (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z))
    ∂Measure.pi (fun _ : I => gaussianReal 0 1)

lemma gtOrdinaryField_eq_affine
    {S I : Type*} [Fintype S] [Fintype I]
    (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) (z : EuclideanSpace ℝ I) :
    gtOrdinaryField A B H₀ t z =
      ((Real.sqrt t) • gtCoefficientCLM A +
        (Real.sqrt (1 - t)) • gtCoefficientCLM B) z + H₀ := by
  simp [gtOrdinaryField]

lemma contDiff_gtStateLogPartition_gtOrdinaryField
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) :
    ContDiff ℝ 1 (fun z : EuclideanSpace ℝ I =>
      gtStateLogPartition V (gtOrdinaryField A B H₀ t z)) := by
  rw [show (fun z : EuclideanSpace ℝ I =>
      gtStateLogPartition V (gtOrdinaryField A B H₀ t z)) =
      fun z => gtStateLogPartition V
        (((Real.sqrt t) • gtCoefficientCLM A +
          (Real.sqrt (1 - t)) • gtCoefficientCLM B) z + H₀) by
    funext z
    rw [gtOrdinaryField_eq_affine]]
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  have hc : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ I =>
      gtStateLogPartition V (L z + H₀)) :=
    (contDiff_gtStateLogPartition V).comp
      (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
        (fun _ : EuclideanSpace ℝ I => H₀)))
  simpa [L, Function.comp_def] using hc.of_le (by simp)

lemma integrable_gtStateLogPartition_gtOrdinaryField
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) :
    Integrable (fun z : I → ℝ => gtStateLogPartition V
        (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  have hcd : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ I =>
      gtStateLogPartition V (L z + H₀)) := by
    have hc : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ I =>
        gtStateLogPartition V (L z + H₀)) :=
      (contDiff_gtStateLogPartition V).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hint := integrable_moderate_gaussianProduct
    (fun z : EuclideanSpace ℝ I => gtStateLogPartition V (L z + H₀)) hcd
    (hasModerateGrowth_gtStateLogPartition_comp V L H₀)
  simpa [L, gtOrdinaryField_eq_affine] using hint

/-- Differentiation of the ordinary pressure before Gaussian integration by parts. -/
lemma hasDerivAt_gtOrdinaryPressure_before_ibp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gtOrdinaryPressure V A B H₀)
      (∫ z, ∑ ξ : S,
          gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
            gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) t := by
  classical
  let ε : ℝ := min t (1 - t) / 2
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
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
  let F : ℝ → (I → ℝ) → ℝ := fun x z =>
    gtStateLogPartition V
      (gtOrdinaryField A B H₀ x (WithLp.toLp 2 z))
  let F' : ℝ → (I → ℝ) → ℝ := fun x z =>
    ∑ ξ : S,
      gtStateGibbs V
          (gtOrdinaryField A B H₀ x (WithLp.toLp 2 z)) ξ *
        gtOrdinaryFieldDeriv A B x (WithLp.toLp 2 z) ξ
  let cA : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cB : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let C : ℝ := cA * ‖gtCoefficientCLM A‖ + cB * ‖gtCoefficientCLM B‖
  let bound : (I → ℝ) → ℝ := fun z =>
    C * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖
  have hcA : 0 ≤ cA := by dsimp [cA]; positivity
  have hcB : 0 ≤ cB := by dsimp [cB]; positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound_int : Integrable bound
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hi := integrable_norm_gaussianProduct (I := I)
    simpa [bound] using hi.const_mul C
  have hF_meas : ∀ᶠ x in nhds t,
      AEStronglyMeasurable (F x)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact (integrable_gtStateLogPartition_gtOrdinaryField V A B H₀ x).1
  have hF_int : Integrable (F t)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    integrable_gtStateLogPartition_gtOrdinaryField V A B H₀ t
  have hF'_meas : AEStronglyMeasurable (F' t)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hfield : Continuous (fun z : EuclideanSpace ℝ I =>
        gtOrdinaryField A B H₀ t z) := by
      rw [show (fun z : EuclideanSpace ℝ I => gtOrdinaryField A B H₀ t z) =
          fun z => ((Real.sqrt t) • gtCoefficientCLM A +
            (Real.sqrt (1 - t)) • gtCoefficientCLM B) z + H₀ by
        funext z
        rw [gtOrdinaryField_eq_affine]]
      fun_prop
    have hfieldDeriv : Continuous (fun z : EuclideanSpace ℝ I =>
        gtOrdinaryFieldDeriv A B t z) := by
      rw [show (fun z : EuclideanSpace ℝ I => gtOrdinaryFieldDeriv A B t z) =
          fun z => ((1 / (2 * Real.sqrt t)) • gtCoefficientCLM A -
            (1 / (2 * Real.sqrt (1 - t))) • gtCoefficientCLM B) z by
        funext z
        simp [gtOrdinaryFieldDeriv]]
      exact ((1 / (2 * Real.sqrt t)) • gtCoefficientCLM A -
        (1 / (2 * Real.sqrt (1 - t))) • gtCoefficientCLM B).continuous
    have hc : Continuous (fun z : EuclideanSpace ℝ I =>
        ∑ ξ : S,
          gtStateGibbs V (gtOrdinaryField A B H₀ t z) ξ *
            gtOrdinaryFieldDeriv A B t z ξ) := by
      apply continuous_finset_sum
      intro ξ _
      have hcoord : Continuous (fun z : EuclideanSpace ℝ I =>
          gtOrdinaryFieldDeriv A B t z ξ) := by
        exact (EuclideanSpace.proj ξ).continuous.comp hfieldDeriv
      exact (((contDiff_gtStateGibbs V ξ).continuous).comp hfield).mul hcoord
    exact (hc.measurable.comp (by fun_prop : Measurable
      (fun z : I → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ I)))).aestronglyMeasurable
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
    have hs := Real.sqrt_le_sqrt htx
    have hp : 0 < 2 * Real.sqrt (t / 2) := by positivity
    have hle : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith
    have hi : 1 / (2 * Real.sqrt x) ≤
        1 / (2 * Real.sqrt (t / 2)) := by
      simpa [one_div] using one_div_le_one_div_of_le hp hle
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt x))]
    exact_mod_cast hi
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
    have hs := Real.sqrt_le_sqrt htx
    have hp : 0 < 2 * Real.sqrt ((1 - t) / 2) := by positivity
    have hle : 2 * Real.sqrt ((1 - t) / 2) ≤
        2 * Real.sqrt (1 - x) := by nlinarith
    have hi : 1 / (2 * Real.sqrt (1 - x)) ≤
        1 / (2 * Real.sqrt ((1 - t) / 2)) := by
      simpa [one_div] using one_div_le_one_div_of_le hp hle
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (1 - x)))]
    exact_mod_cast hi
  have h_bound : ∀ᵐ z ∂Measure.pi (fun _ : I => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, ‖F' x z‖ ≤ bound z := by
    refine ae_of_all _ (fun z x hx => ?_)
    let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
    let D : GTStateSpace S := gtOrdinaryFieldDeriv A B x zE
    have hrepr : F' x z =
        (fderiv ℝ (gtStateLogPartition V)
          (gtOrdinaryField A B H₀ x zE)) D := by
      simp [F', D, zE, fderiv_gtStateLogPartition_apply]
    have hD : ‖D‖ ≤ C * ‖zE‖ := by
      have htri : ‖D‖ ≤
          |1 / (2 * Real.sqrt x)| * ‖gtCoefficientCLM A zE‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖gtCoefficientCLM B zE‖ := by
        dsimp [D, gtOrdinaryFieldDeriv]
        simpa [norm_smul] using
          norm_sub_le
            ((1 / (2 * Real.sqrt x)) • gtCoefficientCLM A zE)
            ((1 / (2 * Real.sqrt (1 - x))) • gtCoefficientCLM B zE)
      calc
        ‖D‖ ≤ |1 / (2 * Real.sqrt x)| * ‖gtCoefficientCLM A zE‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖gtCoefficientCLM B zE‖ := htri
        _ ≤ cA * (‖gtCoefficientCLM A‖ * ‖zE‖) +
            cB * (‖gtCoefficientCLM B‖ * ‖zE‖) := by
          gcongr
          · exact hcoeffA x hx
          · exact (gtCoefficientCLM A).le_opNorm zE
          · exact hcoeffB x hx
          · exact (gtCoefficientCLM B).le_opNorm zE
        _ = C * ‖zE‖ := by
          dsimp [C]
          ring
    calc
      ‖F' x z‖ = ‖(fderiv ℝ (gtStateLogPartition V)
          (gtOrdinaryField A B H₀ x zE)) D‖ := by rw [hrepr]
      _ ≤ ‖fderiv ℝ (gtStateLogPartition V)
          (gtOrdinaryField A B H₀ x zE)‖ * ‖D‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖D‖ := by
        gcongr
        exact norm_fderiv_gtStateLogPartition_le_one V _
      _ ≤ C * ‖zE‖ := by simpa using hD
      _ = bound z := rfl
  have h_diff : ∀ᵐ z ∂Measure.pi (fun _ : I => gaussianReal 0 1),
      ∀ x ∈ Metric.ball t ε, HasDerivAt (fun u => F u z) (F' x z) x := by
    refine ae_of_all _ (fun z x hx => ?_)
    exact hasDerivAt_gtStateLogPartition_field V A B H₀ (hball x hx)
      (WithLp.toLp 2 z)
  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := Measure.pi (fun _ : I => gaussianReal 0 1))
      (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (Metric.ball_mem_nhds t hε)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  change HasDerivAt
    (fun x => ∫ z, gtStateLogPartition V
      (gtOrdinaryField A B H₀ x (WithLp.toLp 2 z))
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) _ t
  exact hmain

/-- Derivative of a Gibbs coordinate along the ordinary affine Gaussian field. -/
lemma fderiv_gtStateGibbs_gtOrdinaryField_apply
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) (z K : EuclideanSpace ℝ I) (ξ : S) :
    fderiv ℝ (fun z' : EuclideanSpace ℝ I =>
        gtStateGibbs V (gtOrdinaryField A B H₀ t z') ξ) z K =
      gtStateGibbs V (gtOrdinaryField A B H₀ t z) ξ *
        ((((Real.sqrt t) • gtCoefficientCLM A +
            (Real.sqrt (1 - t)) • gtCoefficientCLM B) K) ξ -
          ∑ η : S,
            gtStateGibbs V (gtOrdinaryField A B H₀ t z) η *
              (((Real.sqrt t) • gtCoefficientCLM A +
                (Real.sqrt (1 - t)) • gtCoefficientCLM B) K) η) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  have hfield : HasFDerivAt (fun z' : EuclideanSpace ℝ I =>
      gtOrdinaryField A B H₀ t z') L z := by
    rw [show (fun z' : EuclideanSpace ℝ I => gtOrdinaryField A B H₀ t z') =
        fun z' => L z' + H₀ by
      funext z'
      simp [L, gtOrdinaryField]]
    exact L.hasFDerivAt.add_const H₀
  have hg : HasFDerivAt
      (fun H : GTStateSpace S => gtStateGibbs V H ξ)
      (fderiv ℝ (fun H : GTStateSpace S => gtStateGibbs V H ξ)
        (gtOrdinaryField A B H₀ t z))
      (gtOrdinaryField A B H₀ t z) :=
    ((contDiff_gtStateGibbs V ξ).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hc := hg.comp z hfield
  have hf := hc.fderiv
  change fderiv ℝ (fun z' : EuclideanSpace ℝ I =>
      gtStateGibbs V (gtOrdinaryField A B H₀ t z') ξ) z = _ at hf
  rw [hf]
  simp [L, fderiv_gtStateGibbs_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsumA :
      (∑ x : S, gtStateGibbs V (gtOrdinaryField A B H₀ t z) x *
        (Real.sqrt t * gtCoefficientCLM A K x)) =
      Real.sqrt t * ∑ x : S,
        gtStateGibbs V (gtOrdinaryField A B H₀ t z) x *
          gtCoefficientCLM A K x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsumB :
      (∑ x : S, gtStateGibbs V (gtOrdinaryField A B H₀ t z) x *
        (Real.sqrt (1 - t) * gtCoefficientCLM B K x)) =
      Real.sqrt (1 - t) * ∑ x : S,
        gtStateGibbs V (gtOrdinaryField A B H₀ t z) x *
          gtCoefficientCLM B K x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsumA, hsumB]
  ring

/-- Stein identity for the `A` part of the ordinary interpolation. -/
lemma gtOrdinary_stein_A
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (t : ℝ) (ξ : S) :
    (∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
    ∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        (Real.sqrt t *
          (inner ℝ (A ξ) (A ξ) -
            ∑ η : S, gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
                inner ℝ (A η) (A ξ)))
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  let F : EuclideanSpace ℝ I → ℝ := fun z =>
    gtStateGibbs V (L z + H₀) ξ
  have hFdiff : ContDiff ℝ 1 F := by
    have hc : ContDiff ℝ ∞ F :=
      (contDiff_gtStateGibbs V ξ).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hFgrowth : HasModerateGrowth F :=
    hasModerateGrowth_gtStateGibbs_comp V L H₀ ξ
  have hibp := gaussianProduct_stein_inner (A ξ) F hFdiff hFgrowth
  have hfield (z : EuclideanSpace ℝ I) :
      L z + H₀ = gtOrdinaryField A B H₀ t z := by
    simp [L, gtOrdinaryField]
  have hcross (η : S) : inner ℝ (B η) (A ξ) = 0 := by
    rw [real_inner_comm]
    exact hAB ξ η
  rw [show (∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z, inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) (A ξ) *
        F (WithLp.toLp 2 z)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) by
    apply integral_congr_ae
    filter_upwards with z
    rw [real_inner_comm]
    simp [F, hfield]
    ring]
  rw [hibp]
  apply integral_congr_ae
  filter_upwards with z
  have hfun : (fun z' : EuclideanSpace ℝ I =>
      gtStateGibbs V (L z' + H₀) ξ) =
      fun z' => gtStateGibbs V (gtOrdinaryField A B H₀ t z') ξ := by
    funext z'
    rw [hfield]
  change (fderiv ℝ (fun z' : EuclideanSpace ℝ I =>
      gtStateGibbs V (L z' + H₀) ξ) (WithLp.toLp 2 z)) (A ξ) = _
  rw [hfun]
  rw [fderiv_gtStateGibbs_gtOrdinaryField_apply]
  simp [gtCoefficientCLM_apply, hfield, hcross]
  have hsum :
      (∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            (Real.sqrt t * inner ℝ (A η) (A ξ))) =
        Real.sqrt t * ∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            inner ℝ (A η) (A ξ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring
  rw [hsum]
  ring_nf
  simp

/-- Stein identity for the `B` part of the ordinary interpolation. -/
lemma gtOrdinary_stein_B
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (t : ℝ) (ξ : S) :
    (∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
    ∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        (Real.sqrt (1 - t) *
          (inner ℝ (B ξ) (B ξ) -
            ∑ η : S, gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
                inner ℝ (B η) (B ξ)))
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  let F : EuclideanSpace ℝ I → ℝ := fun z =>
    gtStateGibbs V (L z + H₀) ξ
  have hFdiff : ContDiff ℝ 1 F := by
    have hc : ContDiff ℝ ∞ F :=
      (contDiff_gtStateGibbs V ξ).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hFgrowth : HasModerateGrowth F :=
    hasModerateGrowth_gtStateGibbs_comp V L H₀ ξ
  have hibp := gaussianProduct_stein_inner (B ξ) F hFdiff hFgrowth
  have hfield (z : EuclideanSpace ℝ I) :
      L z + H₀ = gtOrdinaryField A B H₀ t z := by
    simp [L, gtOrdinaryField]
  have hcross (η : S) : inner ℝ (A η) (B ξ) = 0 := hAB η ξ
  rw [show (∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z, inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) (B ξ) *
        F (WithLp.toLp 2 z)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) by
    apply integral_congr_ae
    filter_upwards with z
    rw [real_inner_comm]
    simp [F, hfield]
    ring]
  rw [hibp]
  apply integral_congr_ae
  filter_upwards with z
  have hfun : (fun z' : EuclideanSpace ℝ I =>
      gtStateGibbs V (L z' + H₀) ξ) =
      fun z' => gtStateGibbs V (gtOrdinaryField A B H₀ t z') ξ := by
    funext z'
    rw [hfield]
  change (fderiv ℝ (fun z' : EuclideanSpace ℝ I =>
      gtStateGibbs V (L z' + H₀) ξ) (WithLp.toLp 2 z)) (B ξ) = _
  rw [hfun]
  rw [fderiv_gtStateGibbs_gtOrdinaryField_apply]
  simp [gtCoefficientCLM_apply, hfield, hcross]
  have hsum :
      (∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            (Real.sqrt (1 - t) * inner ℝ (B η) (B ξ))) =
        Real.sqrt (1 - t) * ∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            inner ℝ (B η) (B ξ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring
  rw [hsum]
  ring_nf
  simp

/-- The one-replica covariance term associated with a coefficient family. -/
noncomputable def gtOrdinaryCovarianceTerm
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B C : S → EuclideanSpace ℝ I)
    (H₀ : GTStateSpace S) (t : ℝ) (ξ : S)
    (z : EuclideanSpace ℝ I) : ℝ :=
  gtStateGibbs V (gtOrdinaryField A B H₀ t z) ξ *
    (inner ℝ (C ξ) (C ξ) -
      ∑ η : S, gtStateGibbs V (gtOrdinaryField A B H₀ t z) η *
        inner ℝ (C η) (C ξ))

lemma integrable_gtOrdinaryCovarianceTerm
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B C : S → EuclideanSpace ℝ I)
    (H₀ : GTStateSpace S) (t : ℝ) (ξ : S) :
    Integrable (fun z : I → ℝ =>
      gtOrdinaryCovarianceTerm V A B C H₀ t ξ (WithLp.toLp 2 z))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let M : ℝ := |inner ℝ (C ξ) (C ξ)| +
    ∑ η : S, |inner ℝ (C η) (C ξ)|
  have hfield : Continuous (fun z : EuclideanSpace ℝ I =>
      gtOrdinaryField A B H₀ t z) := by
    rw [show (fun z : EuclideanSpace ℝ I => gtOrdinaryField A B H₀ t z) =
        fun z => ((Real.sqrt t) • gtCoefficientCLM A +
          (Real.sqrt (1 - t)) • gtCoefficientCLM B) z + H₀ by
      funext z
      rw [gtOrdinaryField_eq_affine]]
    fun_prop
  have hc : Continuous (fun z : EuclideanSpace ℝ I =>
      gtOrdinaryCovarianceTerm V A B C H₀ t ξ z) := by
    unfold gtOrdinaryCovarianceTerm
    apply (((contDiff_gtStateGibbs V ξ).continuous).comp hfield).mul
    apply continuous_const.sub
    apply continuous_finset_sum
    intro η _
    exact (((contDiff_gtStateGibbs V η).continuous).comp hfield).mul continuous_const
  have hm : AEStronglyMeasurable (fun z : I → ℝ =>
      gtOrdinaryCovarianceTerm V A B C H₀ t ξ (WithLp.toLp 2 z))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    (hc.measurable.comp (by fun_prop : Measurable
      (fun z : I → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ I)))).aestronglyMeasurable
  refine Integrable.mono' (integrable_const M) hm ?_
  filter_upwards with z
  have hgξ := gtStateGibbs_nonneg V
    (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
  have hgξ1 := gtStateGibbs_le_one V
    (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
  have hsum :
      |∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            inner ℝ (C η) (C ξ)| ≤
        ∑ η : S, |inner ℝ (C η) (C ξ)| := by
    calc
      |∑ η : S, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
            inner ℝ (C η) (C ξ)| ≤
          ∑ η : S, |gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
              inner ℝ (C η) (C ξ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ η : S, |inner ℝ (C η) (C ξ)| := by
        apply Finset.sum_le_sum
        intro η _
        rw [abs_mul, abs_of_nonneg (gtStateGibbs_nonneg V _ η)]
        exact mul_le_of_le_one_left (abs_nonneg _) (gtStateGibbs_le_one V _ η)
  rw [Real.norm_eq_abs]
  unfold gtOrdinaryCovarianceTerm
  rw [abs_mul, abs_of_nonneg hgξ]
  have hdiff := abs_sub (inner ℝ (C ξ) (C ξ))
    (∑ η : S, gtStateGibbs V
      (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
        inner ℝ (C η) (C ξ))
  calc
    gtStateGibbs V (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        |inner ℝ (C ξ) (C ξ) -
          ∑ η : S, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
              inner ℝ (C η) (C ξ)|
      ≤ 1 * (|inner ℝ (C ξ) (C ξ)| +
          |∑ η : S, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
              inner ℝ (C η) (C ξ)|) := by gcongr
    _ ≤ M := by
      dsimp [M]
      linarith

/-- Coordinatewise covariance formula for the ordinary interpolation derivative. -/
lemma gtOrdinary_derivative_coordinate_ibp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (ξ : S) :
    (∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      (1 / 2 : ℝ) *
        ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
          ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  let F : EuclideanSpace ℝ I → ℝ := fun z =>
    gtStateGibbs V (L z + H₀) ξ
  have hFdiff : ContDiff ℝ 1 F := by
    have hc : ContDiff ℝ ∞ F :=
      (contDiff_gtStateGibbs V ξ).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hFgrowth : HasModerateGrowth F :=
    hasModerateGrowth_gtStateGibbs_comp V L H₀ ξ
  have hfield (z : EuclideanSpace ℝ I) :
      L z + H₀ = gtOrdinaryField A B H₀ t z := by
    simp [L, gtOrdinaryField]
  have hIntA : Integrable (fun z : I → ℝ =>
      gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hi := integrable_inner_mul_gaussianProduct (A ξ) F hFdiff hFgrowth
    convert hi using 1
    funext z
    rw [real_inner_comm]
    simp [F, hfield]
    ring
  have hIntB : Integrable (fun z : I → ℝ =>
      gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hi := integrable_inner_mul_gaussianProduct (B ξ) F hFdiff hFgrowth
    convert hi using 1
    funext z
    rw [real_inner_comm]
    simp [F, hfield]
    ring
  let cA : ℝ := 1 / (2 * Real.sqrt t)
  let cB : ℝ := 1 / (2 * Real.sqrt (1 - t))
  have hpoint (z : I → ℝ) :
      gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ =
      cA * (gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)) -
      cB * (gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)) := by
    simp [cA, cB, gtOrdinaryFieldDeriv, gtCoefficientCLM_apply]
    ring
  have hsplit :
      (∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
          gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      cA * (∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
          inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
      cB * (∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
          inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    rw [integral_sub (hIntA.const_mul cA) (hIntB.const_mul cB),
      integral_const_mul, integral_const_mul]
  rw [hsplit, gtOrdinary_stein_A V A B H₀ hAB t ξ,
    gtOrdinary_stein_B V A B H₀ hAB t ξ]
  have hscaleA :
      (∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
          (Real.sqrt t *
            (inner ℝ (A ξ) (A ξ) -
              ∑ η : S, gtStateGibbs V
                (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
                  inner ℝ (A η) (A ξ)))
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      Real.sqrt t *
        ∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp [gtOrdinaryCovarianceTerm]
    ring
  have hscaleB :
      (∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
          (Real.sqrt (1 - t) *
            (inner ℝ (B ξ) (B ξ) -
              ∑ η : S, gtStateGibbs V
                (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) η *
                  inner ℝ (B η) (B ξ)))
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      Real.sqrt (1 - t) *
        ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp [gtOrdinaryCovarianceTerm]
    ring
  rw [hscaleA, hscaleB]
  have hsA : cA * Real.sqrt t = 1 / 2 := by
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
    dsimp [cA]
    field_simp
  have hsB : cB * Real.sqrt (1 - t) = 1 / 2 := by
    have hs : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 (by linarith [ht.2])).ne'
    dsimp [cB]
    field_simp
  rw [← mul_assoc, hsA, ← mul_assoc, hsB]
  ring

lemma integrable_gtOrdinaryDerivativeCoordinate
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (ξ : S) :
    Integrable (fun z : I → ℝ =>
      gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  let F : EuclideanSpace ℝ I → ℝ := fun z => gtStateGibbs V (L z + H₀) ξ
  have hFdiff : ContDiff ℝ 1 F := by
    have hc : ContDiff ℝ ∞ F :=
      (contDiff_gtStateGibbs V ξ).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hFgrowth : HasModerateGrowth F :=
    hasModerateGrowth_gtStateGibbs_comp V L H₀ ξ
  have hfield (z : EuclideanSpace ℝ I) :
      L z + H₀ = gtOrdinaryField A B H₀ t z := by
    simp [L, gtOrdinaryField]
  have hIntA : Integrable (fun z : I → ℝ =>
      gtStateGibbs V (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (A ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hi := integrable_inner_mul_gaussianProduct (A ξ) F hFdiff hFgrowth
    convert hi using 1
    funext z
    rw [real_inner_comm]
    simp [F, hfield]
    ring
  have hIntB : Integrable (fun z : I → ℝ =>
      gtStateGibbs V (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
        inner ℝ (B ξ) (WithLp.toLp 2 z : EuclideanSpace ℝ I))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hi := integrable_inner_mul_gaussianProduct (B ξ) F hFdiff hFgrowth
    convert hi using 1
    funext z
    rw [real_inner_comm]
    simp [F, hfield]
    ring
  let cA : ℝ := 1 / (2 * Real.sqrt t)
  let cB : ℝ := 1 / (2 * Real.sqrt (1 - t))
  have hbase := (hIntA.const_mul cA).sub (hIntB.const_mul cB)
  apply hbase.congr
  filter_upwards with z
  simp [cA, cB, gtOrdinaryFieldDeriv, gtCoefficientCLM_apply]
  ring

/-- Full covariance formula for the derivative of the ordinary pressure. -/
lemma hasDerivAt_gtOrdinaryPressure_ibp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gtOrdinaryPressure V A B H₀)
      (∑ ξ : S, (1 / 2 : ℝ) *
        ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
          ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1))) t := by
  have hbefore := hasDerivAt_gtOrdinaryPressure_before_ibp V A B H₀ ht
  have hsum :
      (∫ z, ∑ ξ : S,
          gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
            gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∑ ξ : S, ∫ z,
          gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ *
            gtOrdinaryFieldDeriv A B t (WithLp.toLp 2 z) ξ
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
    rw [integral_finset_sum]
    intro ξ _
    exact integrable_gtOrdinaryDerivativeCoordinate V A B H₀ ht ξ
  rw [hsum] at hbefore
  simp_rw [gtOrdinary_derivative_coordinate_ibp V A B H₀ hAB ht] at hbefore
  exact hbefore

lemma hasDerivAt_gtOrdinaryPressure_nonpos
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (hdiag : ∀ ξ, inner ℝ (A ξ) (A ξ) = inner ℝ (B ξ) (B ξ))
    (hcov : ∀ ξ η, inner ℝ (B ξ) (B η) ≤ inner ℝ (A ξ) (A η))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (gtOrdinaryPressure V A B H₀) d t ∧ d ≤ 0 := by
  let d : ℝ := ∑ ξ : S, (1 / 2 : ℝ) *
    ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
        (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
      ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
        (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1))
  refine ⟨d, hasDerivAt_gtOrdinaryPressure_ibp V A B H₀ hAB ht, ?_⟩
  dsimp [d]
  apply Finset.sum_nonpos
  intro ξ _
  have hIA := integrable_gtOrdinaryCovarianceTerm V A B A H₀ t ξ
  have hIB := integrable_gtOrdinaryCovarianceTerm V A B B H₀ t ξ
  have hle :
      (∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) ≤
        ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
    apply integral_mono hIA hIB
    intro z
    let H := gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)
    have hgξ : 0 ≤ gtStateGibbs V H ξ := gtStateGibbs_nonneg V H ξ
    have hsum :
        (∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
          ∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ) := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_left _ (gtStateGibbs_nonneg V H η)
      simpa [real_inner_comm] using hcov ξ η
    unfold gtOrdinaryCovarianceTerm
    change gtStateGibbs V H ξ *
        (inner ℝ (A ξ) (A ξ) -
          ∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ)) ≤
      gtStateGibbs V H ξ *
        (inner ℝ (B ξ) (B ξ) -
          ∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ))
    apply mul_le_mul_of_nonneg_left _ hgξ
    rw [hdiag ξ]
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hle)

lemma continuous_gtOrdinaryPressure
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S) :
    Continuous (gtOrdinaryPressure V A B H₀) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let base := hasModerateGrowth_gtStateLogPartition V
  let RA : ℝ := Real.sqrt (|t₀| + 1)
  let RB : ℝ := Real.sqrt (|t₀| + 2)
  let R : ℝ := RA * ‖gtCoefficientCLM A‖ + RB * ‖gtCoefficientCLM B‖
  let bound : (I → ℝ) → ℝ := fun z =>
    base.C * (1 + ‖H₀‖ + R *
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)
  have hR : 0 ≤ R := by
    dsimp [R, RA, RB]
    positivity
  have hbound : Integrable bound
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hn := integrable_norm_gaussianProduct (I := I)
    have hrn : Integrable (fun z : I → ℝ =>
        R * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) := hn.const_mul R
    have hc : Integrable (fun _ : I → ℝ => 1 + ‖H₀‖)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) := integrable_const _
    simpa [bound] using (hc.add hrn).const_mul base.C
  apply MeasureTheory.continuousAt_of_dominated
  · filter_upwards with s
    exact (integrable_gtStateLogPartition_gtOrdinaryField V A B H₀ s).1
  · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with s hs
    filter_upwards with z
    have hst : |s - t₀| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hsA : s ≤ |t₀| + 1 := by
      have hslt : s < t₀ + 1 := by
        have := (abs_lt.1 hst).2
        linarith
      linarith [le_abs_self t₀]
    have hsB : 1 - s ≤ |t₀| + 2 := by
      have hslt : t₀ - 1 < s := by
        have := (abs_lt.1 hst).1
        linarith
      linarith [neg_le_abs t₀]
    have hsqrtA : Real.sqrt s ≤ RA := by
      dsimp [RA]
      exact Real.sqrt_le_sqrt hsA
    have hsqrtB : Real.sqrt (1 - s) ≤ RB := by
      dsimp [RB]
      exact Real.sqrt_le_sqrt hsB
    let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
    have hfield : ‖gtOrdinaryField A B H₀ s zE‖ ≤ R * ‖zE‖ + ‖H₀‖ := by
      calc
        ‖gtOrdinaryField A B H₀ s zE‖ ≤
            ‖(Real.sqrt s) • gtCoefficientCLM A zE‖ +
              ‖(Real.sqrt (1 - s)) • gtCoefficientCLM B zE‖ + ‖H₀‖ := by
          dsimp [gtOrdinaryField]
          exact (norm_add_le _ H₀).trans (by
            gcongr
            exact norm_add_le _ _)
        _ ≤ RA * (‖gtCoefficientCLM A‖ * ‖zE‖) +
              RB * (‖gtCoefficientCLM B‖ * ‖zE‖) + ‖H₀‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
          · exact (gtCoefficientCLM A).le_opNorm zE
          · exact (gtCoefficientCLM B).le_opNorm zE
        _ = R * ‖zE‖ + ‖H₀‖ := by
          dsimp [R]
          ring
    have hgrowth := base.F_bound (gtOrdinaryField A B H₀ s zE)
    have hm : base.m = 1 := by rfl
    rw [hm, pow_one] at hgrowth
    rw [Real.norm_eq_abs]
    calc
      |gtStateLogPartition V (gtOrdinaryField A B H₀ s zE)| ≤
          base.C * (1 + ‖gtOrdinaryField A B H₀ s zE‖) := hgrowth
      _ ≤ base.C * (1 + ‖H₀‖ + R * ‖zE‖) := by
        apply mul_le_mul_of_nonneg_left _ base.Cpos.le
        linarith
      _ = ‖bound z‖ := by
        have hb0 : 0 ≤ bound z := by
          dsimp [bound]
          exact mul_nonneg base.Cpos.le (by positivity)
        change base.C * (1 + ‖H₀‖ + R * ‖zE‖) = |bound z|
        rw [abs_of_nonneg hb0]
  · exact hbound.norm
  · filter_upwards with z
    have hfield : Continuous (fun s : ℝ =>
        gtOrdinaryField A B H₀ s (WithLp.toLp 2 z)) := by
      unfold gtOrdinaryField
      fun_prop
    exact ((contDiff_gtStateLogPartition V).continuous.comp hfield).continuousAt

/-- Ordinary finite-state Gaussian comparison. -/
theorem gtOrdinaryPressure_one_le_zero
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (hdiag : ∀ ξ, inner ℝ (A ξ) (A ξ) = inner ℝ (B ξ) (B ξ))
    (hcov : ∀ ξ η, inner ℝ (B ξ) (B η) ≤ inner ℝ (A ξ) (A η)) :
    gtOrdinaryPressure V A B H₀ 1 ≤ gtOrdinaryPressure V A B H₀ 0 := by
  have hanti : AntitoneOn (gtOrdinaryPressure V A B H₀) (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
      (continuous_gtOrdinaryPressure V A B H₀).continuousOn ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, _⟩ :=
        hasDerivAt_gtOrdinaryPressure_nonpos V A B H₀ hAB hdiag hcov ht
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, hd0⟩ :=
        hasDerivAt_gtOrdinaryPressure_nonpos V A B H₀ hAB hdiag hcov ht
      rw [hd.deriv]
      exact hd0
  exact hanti (by norm_num) (by norm_num) (by norm_num)

lemma integrable_gtOrdinaryGibbsCoordinate
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (t : ℝ) (ξ : S) :
    Integrable (fun z : I → ℝ =>
      gtStateGibbs V (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
    (Real.sqrt t) • gtCoefficientCLM A +
      (Real.sqrt (1 - t)) • gtCoefficientCLM B
  have hcd : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ I =>
      gtStateGibbs V (L z + H₀) ξ) := by
    have hc : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ I =>
        gtStateGibbs V (L z + H₀) ξ) :=
      (contDiff_gtStateGibbs V ξ).comp
        (L.contDiff.add (contDiff_const : ContDiff ℝ ∞
          (fun _ : EuclideanSpace ℝ I => H₀)))
    exact hc.of_le (by simp)
  have hi := integrable_moderate_gaussianProduct
    (fun z : EuclideanSpace ℝ I => gtStateGibbs V (L z + H₀) ξ) hcd
    (hasModerateGrowth_gtStateGibbs_comp V L H₀ ξ)
  simpa [L, gtOrdinaryField] using hi

lemma hasDerivAt_gtOrdinaryPressure_le_diagonalGap
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (gap : ℝ)
    (hdiag : ∀ ξ, inner ℝ (A ξ) (A ξ) - inner ℝ (B ξ) (B ξ) = gap)
    (hcov : ∀ ξ η, inner ℝ (B ξ) (B η) ≤ inner ℝ (A ξ) (A η))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (gtOrdinaryPressure V A B H₀) d t ∧
      d ≤ gap / 2 := by
  let d : ℝ := ∑ ξ : S, (1 / 2 : ℝ) *
    ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
        (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
      ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
        (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1))
  refine ⟨d, hasDerivAt_gtOrdinaryPressure_ibp V A B H₀ hAB ht, ?_⟩
  have hcoord (ξ : S) :
      (∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
        ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) ≤
      gap * ∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
    have hIA := integrable_gtOrdinaryCovarianceTerm V A B A H₀ t ξ
    have hIB := integrable_gtOrdinaryCovarianceTerm V A B B H₀ t ξ
    have hIg := integrable_gtOrdinaryGibbsCoordinate V A B H₀ t ξ
    rw [← integral_const_mul]
    rw [← integral_sub hIA hIB]
    apply integral_mono (hIA.sub hIB) (hIg.const_mul gap)
    intro z
    let H := gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)
    have hgξ : 0 ≤ gtStateGibbs V H ξ := gtStateGibbs_nonneg V H ξ
    have hsum :
        (∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
          ∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ) := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_left _ (gtStateGibbs_nonneg V H η)
      simpa [real_inner_comm] using hcov ξ η
    unfold gtOrdinaryCovarianceTerm
    change gtStateGibbs V H ξ *
          (inner ℝ (A ξ) (A ξ) -
            ∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ)) -
        gtStateGibbs V H ξ *
          (inner ℝ (B ξ) (B ξ) -
            ∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
      gap * gtStateGibbs V H ξ
    have hd := hdiag ξ
    nlinarith
  have hsumg :
      (∑ ξ : S, ∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
    rw [← integral_finset_sum]
    · simp_rw [sum_gtStateGibbs]
      simp
    · intro ξ _
      exact integrable_gtOrdinaryGibbsCoordinate V A B H₀ t ξ
  dsimp [d]
  calc
    (∑ ξ : S, (1 / 2 : ℝ) *
      ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
        ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1))) ≤
      ∑ ξ : S, (1 / 2 : ℝ) *
        (gap * ∫ z, gtStateGibbs V
          (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left (hcoord ξ) (by norm_num)
    _ = gap / 2 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsumg]
      ring

/-- Ordinary comparison with a constant self-variance gap. -/
theorem gtOrdinaryPressure_one_le_zero_add_diagonalGap
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (gap : ℝ)
    (hdiag : ∀ ξ, inner ℝ (A ξ) (A ξ) - inner ℝ (B ξ) (B ξ) = gap)
    (hcov : ∀ ξ η, inner ℝ (B ξ) (B η) ≤ inner ℝ (A ξ) (A η)) :
    gtOrdinaryPressure V A B H₀ 1 ≤
      gtOrdinaryPressure V A B H₀ 0 + gap / 2 := by
  let g : ℝ → ℝ := fun t => gtOrdinaryPressure V A B H₀ t - (gap / 2) * t
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_gtOrdinaryPressure V A B H₀).continuousOn.sub
      (continuous_const.mul continuous_id).continuousOn
  have hganti : AntitoneOn g (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1) hgcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, _⟩ :=
        hasDerivAt_gtOrdinaryPressure_le_diagonalGap
          V A B H₀ hAB gap hdiag hcov ht
      exact (hd.sub ((hasDerivAt_id t).const_mul (gap / 2))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, hdle⟩ :=
        hasDerivAt_gtOrdinaryPressure_le_diagonalGap
          V A B H₀ hAB gap hdiag hcov ht
      have hgd : HasDerivAt g (d - gap / 2) t := by
        exact (hd.sub ((hasDerivAt_id t).const_mul (gap / 2))).congr_deriv (by ring)
      rw [hgd.deriv]
      linarith
  have hend : g 1 ≤ g 0 := hganti
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (by norm_num)
  dsimp [g] at hend
  linarith

/-- Ordinary comparison when the covariance order holds after adding a
state-independent constant. Such a constant cancels from every Gibbs
covariance, while `gap` records the resulting self-variance bound. -/
theorem gtOrdinaryPressure_one_le_zero_add_shiftedDiagonalGap
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (A B : S → EuclideanSpace ℝ I) (H₀ : GTStateSpace S)
    (hAB : ∀ ξ η, inner ℝ (A ξ) (B η) = 0)
    (shift gap : ℝ)
    (hdiag : ∀ ξ,
      inner ℝ (A ξ) (A ξ) - inner ℝ (B ξ) (B ξ) =
        gap - shift)
    (hcov : ∀ ξ η,
      inner ℝ (B ξ) (B η) ≤ inner ℝ (A ξ) (A η) + shift) :
    gtOrdinaryPressure V A B H₀ 1 ≤
      gtOrdinaryPressure V A B H₀ 0 + gap / 2 := by
  have hderiv : ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ d : ℝ, HasDerivAt (gtOrdinaryPressure V A B H₀) d t ∧
        d ≤ gap / 2 := by
    intro t ht
    let d : ℝ := ∑ ξ : S, (1 / 2 : ℝ) *
      ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
        ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
          (WithLp.toLp 2 z)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1))
    refine ⟨d, hasDerivAt_gtOrdinaryPressure_ibp V A B H₀ hAB ht, ?_⟩
    have hcoord (ξ : S) :
        (∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
          ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
            (WithLp.toLp 2 z)
            ∂Measure.pi (fun _ : I => gaussianReal 0 1) ≤
        gap * ∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
            ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
      have hIA := integrable_gtOrdinaryCovarianceTerm V A B A H₀ t ξ
      have hIB := integrable_gtOrdinaryCovarianceTerm V A B B H₀ t ξ
      have hIg := integrable_gtOrdinaryGibbsCoordinate V A B H₀ t ξ
      rw [← integral_const_mul, ← integral_sub hIA hIB]
      apply integral_mono (hIA.sub hIB) (hIg.const_mul gap)
      intro z
      let H := gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)
      have hsumg : ∑ η : S, gtStateGibbs V H η = 1 :=
        sum_gtStateGibbs V H
      have hsum :
          (∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
            (∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ)) +
              shift := by
        calc
          (∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
              ∑ η : S, gtStateGibbs V H η *
                (inner ℝ (A η) (A ξ) + shift) := by
            apply Finset.sum_le_sum
            intro η _
            apply mul_le_mul_of_nonneg_left _ (gtStateGibbs_nonneg V H η)
            simpa [real_inner_comm] using hcov ξ η
          _ = (∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ)) +
                shift := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            rw [hsumg]
            ring
      unfold gtOrdinaryCovarianceTerm
      change gtStateGibbs V H ξ *
            (inner ℝ (A ξ) (A ξ) -
              ∑ η : S, gtStateGibbs V H η * inner ℝ (A η) (A ξ)) -
          gtStateGibbs V H ξ *
            (inner ℝ (B ξ) (B ξ) -
              ∑ η : S, gtStateGibbs V H η * inner ℝ (B η) (B ξ)) ≤
        gap * gtStateGibbs V H ξ
      have hgξ := gtStateGibbs_nonneg V H ξ
      have hd := hdiag ξ
      nlinarith
    have hsumg :
        (∑ ξ : S, ∫ z, gtStateGibbs V
            (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
            ∂Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
      rw [← integral_finset_sum]
      · simp_rw [sum_gtStateGibbs]
        simp
      · intro ξ _
        exact integrable_gtOrdinaryGibbsCoordinate V A B H₀ t ξ
    dsimp [d]
    calc
      (∑ ξ : S, (1 / 2 : ℝ) *
          ((∫ z, gtOrdinaryCovarianceTerm V A B A H₀ t ξ
              (WithLp.toLp 2 z)
              ∂Measure.pi (fun _ : I => gaussianReal 0 1)) -
            ∫ z, gtOrdinaryCovarianceTerm V A B B H₀ t ξ
              (WithLp.toLp 2 z)
              ∂Measure.pi (fun _ : I => gaussianReal 0 1))) ≤
          ∑ ξ : S, (1 / 2 : ℝ) *
            (gap * ∫ z, gtStateGibbs V
              (gtOrdinaryField A B H₀ t (WithLp.toLp 2 z)) ξ
              ∂Measure.pi (fun _ : I => gaussianReal 0 1)) := by
        apply Finset.sum_le_sum
        intro ξ _
        exact mul_le_mul_of_nonneg_left (hcoord ξ) (by norm_num)
      _ = gap / 2 := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, hsumg]
        ring
  let g : ℝ → ℝ := fun t => gtOrdinaryPressure V A B H₀ t - (gap / 2) * t
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_gtOrdinaryPressure V A B H₀).continuousOn.sub
      (continuous_const.mul continuous_id).continuousOn
  have hganti : AntitoneOn g (Set.Icc (0 : ℝ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1) hgcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, _⟩ := hderiv ht
      exact (hd.sub ((hasDerivAt_id t).const_mul (gap / 2))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨d, hd, hdle⟩ := hderiv ht
      have hgd : HasDerivAt g (d - gap / 2) t := by
        exact (hd.sub ((hasDerivAt_id t).const_mul (gap / 2))).congr_deriv (by ring)
      rw [hgd.deriv]
      linarith
  have hend : g 1 ≤ g 0 := hganti
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (by norm_num)
  dsimp [g] at hend
  linarith

end SpinGlass.AT
