module

public import Lemmas.Price.Gaussian
public import Lemmas.Price.Taylor
public import Lemmas.Price.Moments

@[expose] public section

/-!
# The key estimates

This file contains the two analytic estimates driving the proof of Price's theorem.  Both
compare a centered Gaussian integral at covariance `S` with the one at covariance `S + T`,
where `T` is a positive semidefinite matrix of small trace, and both are *uniform* over the
base covariance `S` subject to a trace bound.
-/

open Matrix MeasureTheory Filter PriceFourier
open scoped RealInnerProductSpace ENNReal NNReal

namespace ProbabilityTheory

open PriceGaussian

local notation "stdGaussian" => PriceGaussian.stdGaussian
local notation "multivariateGaussian" => PriceGaussian.multivariateGaussian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The integral of `h` against the centered Gaussian with covariance matrix `S`. -/
noncomputable def Gint (h : EuclideanSpace ℝ n → ℝ) (S : Matrix n n ℝ) : ℝ :=
  ∫ z, h z ∂(multivariateGaussian 0 S)

theorem norm_matCLM_psdSqrt_le {T : Matrix n n ℝ} (hT : T.PosSemidef) (w : EuclideanSpace ℝ n) :
    ‖matCLM (psdSqrt T) w‖ ≤ Real.sqrt T.trace * ‖w‖ := by
  have := norm_matCLM_le (psdSqrt T) w
  rwa [frob_psdSqrt hT] at this

theorem inner_euclidBasis_euclidBasis (i j : n) :
    ⟪euclidBasis (n := n) i, euclidBasis j⟫ = if i = j then (1 : ℝ) else 0 := by
  rw [inner_euclidBasis]
  simp [euclidBasis, EuclideanSpace.single_apply]

theorem integral_norm_sq_matCLM_psdSqrt {T : Matrix n n ℝ} (hT : T.PosSemidef) :
    ∫ w, ‖matCLM (psdSqrt T) w‖ ^ 2 ∂(stdGaussian n) = T.trace := by
  have hB : ∀ w : EuclideanSpace ℝ n,
      ‖matCLM (psdSqrt T) w‖ ^ 2
        = ∑ i, (matCLM (psdSqrt T) w) i * (matCLM (psdSqrt T) w) i := by
    intro w
    rw [euclid_norm_sq]
    exact Finset.sum_congr rfl fun i _ => sq _
  simp_rw [hB]
  rw [integral_finset_sum _ (fun i _ => integrable_coord_mul_coord (psdSqrt T) i i)]
  simp_rw [integral_coord_mul_coord, psdSqrt_mul_transpose hT]
  rfl

/-! ### Integrals over a pair of independent standard Gaussians -/

omit [DecidableEq n] in
theorem integral_fst_stdGaussian {f : EuclideanSpace ℝ n → ℝ}
    (hf : AEStronglyMeasurable f (stdGaussian n)) :
    ∫ p, f p.1 ∂((stdGaussian n).prod (stdGaussian n)) = ∫ w, f w ∂(stdGaussian n) := by
  have hmap : Measure.map Prod.fst ((stdGaussian n).prod (stdGaussian n)) = stdGaussian n := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hf' : AEStronglyMeasurable f
      (Measure.map Prod.fst ((stdGaussian n).prod (stdGaussian n))) := by rw [hmap]; exact hf
  rw [← integral_map measurable_fst.aemeasurable hf', hmap]

omit [DecidableEq n] in
theorem integral_snd_stdGaussian {f : EuclideanSpace ℝ n → ℝ}
    (hf : AEStronglyMeasurable f (stdGaussian n)) :
    ∫ p, f p.2 ∂((stdGaussian n).prod (stdGaussian n)) = ∫ w, f w ∂(stdGaussian n) := by
  have hmap : Measure.map Prod.snd ((stdGaussian n).prod (stdGaussian n)) = stdGaussian n := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hf' : AEStronglyMeasurable f
      (Measure.map Prod.snd ((stdGaussian n).prod (stdGaussian n))) := by rw [hmap]; exact hf
  rw [← integral_map measurable_snd.aemeasurable hf', hmap]

/-- A bounded a.e.-strongly-measurable function is integrable for a finite measure. -/
theorem integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (hm : AEStronglyMeasurable F μ) {M : ℝ} (hb : ∀ x, |F x| ≤ M) :
    Integrable F μ :=
  (integrable_const M).mono' hm (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)

/-! ### The difference of two Gaussian integrals as a single integral over the pair -/

theorem Gint_add_sub_eq {S T : Matrix n n ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {u : EuclideanSpace ℝ n → ℝ} (hu : Continuous u) {M : ℝ} (hb : ∀ z, |u z| ≤ M) :
    Gint u (S + T) - Gint u S
      = ∫ p, (u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
            - u (matCLM (psdSqrt S) p.1)) ∂((stdGaussian n).prod (stdGaussian n)) := by
  have hc1 : Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) := by fun_prop
  have hc2 : Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      u (matCLM (psdSqrt S) p.1) := by fun_prop
  rw [integral_sub (integrable_of_bound hc1.aestronglyMeasurable (fun p => hb _))
    (integrable_of_bound hc2.aestronglyMeasurable (fun p => hb _))]
  congr 1
  · rw [Gint, integral_multivariateGaussian_add hS hT u hu]
  · rw [Gint, integral_multivariateGaussian_eq S u hu,
      integral_fst_stdGaussian (f := fun w => u (matCLM (psdSqrt S) w))
        (by fun_prop : Continuous _).aestronglyMeasurable]

/-! ### A modulus of continuity on a ball -/

omit [DecidableEq n] in
/-- A continuous function is uniformly continuous on a ball: the increment over displacements of
size at most `η` is at most `ε`, uniformly over base points of norm at most `R`. -/
theorem exists_modulus {F : Type*} [NormedAddCommGroup F] {u : EuclideanSpace ℝ n → F}
    (hu : Continuous u) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η, 0 < η ∧ η ≤ 1 ∧
      ∀ x v : EuclideanSpace ℝ n, ‖x‖ ≤ R → ‖v‖ ≤ η → ‖u (x + v) - u x‖ ≤ ε := by
  have hcpt : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ n) (R + 1)) :=
    isCompact_closedBall _ _
  have huc : UniformContinuousOn u (Metric.closedBall (0 : EuclideanSpace ℝ n) (R + 1)) :=
    hcpt.uniformContinuousOn_of_continuous hu.continuousOn
  obtain ⟨η0, hη0, hmod⟩ := (Metric.uniformContinuousOn_iff_le.1 huc) ε hε
  refine ⟨min η0 1, lt_min hη0 zero_lt_one, min_le_right _ _, fun x v hx hv => ?_⟩
  have hv1 : ‖v‖ ≤ 1 := hv.trans (min_le_right _ _)
  have hxmem : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ n) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hxvmem : x + v ∈ Metric.closedBall (0 : EuclideanSpace ℝ n) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le x v).trans (by linarith)
  have hd : dist (x + v) x ≤ η0 := by
    rw [dist_eq_norm]
    simpa using hv.trans (min_le_left _ _)
  have := hmod (x + v) hxvmem x hxmem hd
  rwa [dist_eq_norm] at this

/-! ### The zeroth-order estimate -/

/-- Uniform continuity of `S ↦ ∫ u dN(0,S)` in the direction of positive semidefinite
increments, uniformly over base covariances of bounded trace. -/
theorem exists_delta_order0 {u : EuclideanSpace ℝ n → ℝ} (hu : Continuous u)
    {M : ℝ} (hb : ∀ z, |u z| ≤ M) {K ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ S T : Matrix n n ℝ, S.PosSemidef → T.PosSemidef →
      S.trace ≤ K → T.trace ≤ δ → |Gint u (S + T) - Gint u S| ≤ ε := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  obtain ⟨A, hA, hAtail⟩ := exists_tail_bound (n := n) (fun _ => (1 : ℝ)) (integrable_const 1)
    (fun _ => zero_le_one) (show (0 : ℝ) < ε / (8 * (M + 1)) by positivity)
  set J : EuclideanSpace ℝ n → ℝ :=
    Set.indicator {w : EuclideanSpace ℝ n | A < ‖w‖} (fun _ => (1 : ℝ)) with hJdef
  have hJint : Integrable J (stdGaussian n) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_norm_gt A)
  have hJ0 : ∀ w, 0 ≤ J w := fun w => Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hJ1 : ∀ w : EuclideanSpace ℝ n, A < ‖w‖ → J w = 1 := by
    intro w hw
    have hmem : w ∈ {w : EuclideanSpace ℝ n | A < ‖w‖} := hw
    rw [hJdef, Set.indicator_of_mem hmem]
  obtain ⟨η, hη, hη1, hmod⟩ :=
    exists_modulus hu (Real.sqrt K * A) (show (0 : ℝ) < ε / 2 by positivity)
  refine ⟨(η / (A + 1)) ^ 2, by positivity, ?_⟩
  intro S T hS hT hStr hTtr
  rw [Gint_add_sub_eq hS hT hu hb]
  have hDcont : Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
        - u (matCLM (psdSqrt S) p.1) := by fun_prop
  have hDabs : ∀ p : EuclideanSpace ℝ n × EuclideanSpace ℝ n,
      |u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
        - u (matCLM (psdSqrt S) p.1)| ≤ 2 * M := by
    intro p
    calc |u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
            - u (matCLM (psdSqrt S) p.1)|
        ≤ |u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)|
          + |u (matCLM (psdSqrt S) p.1)| := abs_sub _ _
      _ ≤ M + M := add_le_add (hb _) (hb _)
      _ = 2 * M := by ring
  have hpt : ∀ p : EuclideanSpace ℝ n × EuclideanSpace ℝ n,
      |u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
        - u (matCLM (psdSqrt S) p.1)| ≤ ε / 2 + 2 * M * J p.1 + 2 * M * J p.2 := by
    intro p
    have h01 := hJ0 p.1
    have h02 := hJ0 p.2
    by_cases h1 : A < ‖p.1‖
    · rw [hJ1 _ h1]
      nlinarith [hDabs p, hM, hε]
    by_cases h2 : A < ‖p.2‖
    · rw [hJ1 _ h2]
      nlinarith [hDabs p, hM, hε]
    push_neg at h1 h2
    have hx : ‖matCLM (psdSqrt S) p.1‖ ≤ Real.sqrt K * A := by
      refine (norm_matCLM_psdSqrt_le hS p.1).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt hStr) h1 (norm_nonneg _) (Real.sqrt_nonneg _)
    have hv : ‖matCLM (psdSqrt T) p.2‖ ≤ η := by
      refine (norm_matCLM_psdSqrt_le hT p.2).trans ?_
      have hsq : Real.sqrt T.trace ≤ η / (A + 1) := by
        refine (Real.sqrt_le_sqrt hTtr).trans ?_
        rw [Real.sqrt_sq (by positivity)]
      calc Real.sqrt T.trace * ‖p.2‖ ≤ (η / (A + 1)) * A :=
            mul_le_mul hsq h2 (norm_nonneg _) (by positivity)
        _ ≤ η := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [hη.le]
    have hgood := hmod _ _ hx hv
    rw [Real.norm_eq_abs] at hgood
    nlinarith [hM]
  have hDint : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      u (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
        - u (matCLM (psdSqrt S) p.1)) ((stdGaussian n).prod (stdGaussian n)) :=
    integrable_of_bound hDcont.aestronglyMeasurable hDabs
  have hb1 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n => 2 * M * J p.1)
      ((stdGaussian n).prod (stdGaussian n)) := (hJint.const_mul (2 * M)).comp_fst _
  have hb2 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n => 2 * M * J p.2)
      ((stdGaussian n).prod (stdGaussian n)) := (hJint.const_mul (2 * M)).comp_snd _
  have hbc : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      ε / 2 + 2 * M * J p.1) ((stdGaussian n).prod (stdGaussian n)) :=
    (integrable_const (ε / 2)).add hb1
  have hbndint : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      ε / 2 + 2 * M * J p.1 + 2 * M * J p.2) ((stdGaussian n).prod (stdGaussian n)) :=
    hbc.add hb2
  refine (abs_integral_le_integral_abs.trans (integral_mono hDint.abs hbndint hpt)).trans ?_
  have hcalc : ∫ p, (ε / 2 + 2 * M * J p.1 + 2 * M * J p.2)
        ∂((stdGaussian n).prod (stdGaussian n))
      = ε / 2 + 2 * M * (∫ w, J w ∂(stdGaussian n))
        + 2 * M * (∫ w, J w ∂(stdGaussian n)) := by
    rw [integral_add hbc hb2,
      integral_add (integrable_const (ε / 2)) hb1, integral_const_mul, integral_const_mul,
      integral_fst_stdGaussian (f := J) hJint.aestronglyMeasurable,
      integral_snd_stdGaussian (f := J) hJint.aestronglyMeasurable]
    simp
  rw [hcalc]
  have hrho : ∫ w, J w ∂(stdGaussian n) ≤ ε / (8 * (M + 1)) := hAtail
  have hrho0 : 0 ≤ ∫ w, J w ∂(stdGaussian n) := integral_nonneg hJ0
  have hpos : (0 : ℝ) < 8 * (M + 1) := by positivity
  have hstep2 : 4 * M * (∫ w, J w ∂(stdGaussian n)) ≤ 4 * M * (ε / (8 * (M + 1))) :=
    mul_le_mul_of_nonneg_left hrho (by positivity)
  have hfin : 4 * M * (ε / (8 * (M + 1))) ≤ ε / 2 := by
    rw [show 4 * M * (ε / (8 * (M + 1))) = (4 * M * ε) / (8 * (M + 1)) by ring,
      div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε.le, hM]
  linarith


/-! ### Auxiliary continuity and integrability for the second-order estimate -/

theorem integrable_norm_sq_matCLM (N : Matrix n n ℝ) :
    Integrable (fun w : EuclideanSpace ℝ n => ‖matCLM N w‖ ^ 2) (stdGaussian n) := by
  have he : (fun w : EuclideanSpace ℝ n => ‖matCLM N w‖ ^ 2)
      = fun w => ∑ i, (matCLM N w) i * (matCLM N w) i := by
    funext w
    rw [euclid_norm_sq]
    exact Finset.sum_congr rfl fun i _ => sq _
  rw [he]
  exact integrable_finset_sum _ (fun i _ => integrable_coord_mul_coord N i i)

theorem indicator_le_indicator_of_le {α : Type*} {s : Set α} {f g : α → ℝ}
    (hfg : ∀ a, f a ≤ g a) (a : α) : s.indicator f a ≤ s.indicator g a := by
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    exact hfg a
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

variable {h : EuclideanSpace ℝ n → ℝ}

theorem continuous_fderiv_pair (hC : ContDiff ℝ 2 h) (N N' : Matrix n n ℝ) :
    Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      fderiv ℝ h (matCLM N p.1) (matCLM N' p.2) := by
  have hev : Continuous
      fun q : (EuclideanSpace ℝ n →L[ℝ] ℝ) × EuclideanSpace ℝ n => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  exact hev.comp ((((continuous_fderiv_of_contDiff_two hC).comp
    (matCLM N).continuous).comp continuous_fst).prodMk
      ((matCLM N').continuous.comp continuous_snd))

theorem continuous_hess_pair (hC : ContDiff ℝ 2 h) (N N' : Matrix n n ℝ) :
    Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      (hess h (matCLM N p.1) (matCLM N' p.2)) (matCLM N' p.2) := by
  have hev1 : Continuous fun q :
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ) × EuclideanSpace ℝ n => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have hev2 : Continuous
      fun q : (EuclideanSpace ℝ n →L[ℝ] ℝ) × EuclideanSpace ℝ n => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have hsnd : Continuous fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n => matCLM N' p.2 :=
    (matCLM N').continuous.comp continuous_snd
  exact hev2.comp ((hev1.comp ((((continuous_hess hC).comp
    (matCLM N).continuous).comp continuous_fst).prodMk hsnd)).prodMk hsnd)

theorem integrable_fderiv_pair (hC : ContDiff ℝ 2 h) {M1 : ℝ}
    (hb1 : ∀ z, ‖fderiv ℝ h z‖ ≤ M1) (N N' : Matrix n n ℝ) :
    Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      fderiv ℝ h (matCLM N p.1) (matCLM N' p.2)) ((stdGaussian n).prod (stdGaussian n)) := by
  have hM1 : 0 ≤ M1 := le_trans (norm_nonneg _) (hb1 0)
  have hdom : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      (M1 * frob N') * ‖p.2‖) ((stdGaussian n).prod (stdGaussian n)) :=
    (integrable_norm_stdGaussian.const_mul (M1 * frob N')).comp_snd _
  refine hdom.mono' (continuous_fderiv_pair hC N N').aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  calc ‖fderiv ℝ h (matCLM N p.1) (matCLM N' p.2)‖
      ≤ ‖fderiv ℝ h (matCLM N p.1)‖ * ‖matCLM N' p.2‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M1 * (frob N' * ‖p.2‖) :=
        mul_le_mul (hb1 _) (norm_matCLM_le N' p.2) (norm_nonneg _) hM1
    _ = M1 * frob N' * ‖p.2‖ := by ring

theorem integrable_hess_pair (hC : ContDiff ℝ 2 h) {M2 : ℝ}
    (hb2 : ∀ z, ‖hess h z‖ ≤ M2) (N N' : Matrix n n ℝ) :
    Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      (hess h (matCLM N p.1) (matCLM N' p.2)) (matCLM N' p.2))
      ((stdGaussian n).prod (stdGaussian n)) := by
  have hM2 : 0 ≤ M2 := (norm_nonneg (hess h 0)).trans (hb2 0)
  have hfr : 0 ≤ frob N' := frob_nonneg N'
  have hdom : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      (M2 * frob N' ^ 2) * ‖p.2‖ ^ 2) ((stdGaussian n).prod (stdGaussian n)) :=
    (integrable_norm_sq_stdGaussian.const_mul (M2 * frob N' ^ 2)).comp_snd _
  refine hdom.mono' (continuous_hess_pair hC N N').aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  have hstep : ‖(hess h (matCLM N p.1) (matCLM N' p.2)) (matCLM N' p.2)‖
      ≤ M2 * (frob N' * ‖p.2‖) * (frob N' * ‖p.2‖) := by
    calc ‖(hess h (matCLM N p.1) (matCLM N' p.2)) (matCLM N' p.2)‖
        ≤ ‖hess h (matCLM N p.1) (matCLM N' p.2)‖ * ‖matCLM N' p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖hess h (matCLM N p.1)‖ * ‖matCLM N' p.2‖) * ‖matCLM N' p.2‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M2 * (frob N' * ‖p.2‖)) * (frob N' * ‖p.2‖) := by
          have h1 := norm_matCLM_le N' p.2
          have h2 := hb2 (matCLM N p.1)
          have h3 : (0:ℝ) ≤ ‖matCLM N' p.2‖ := norm_nonneg _
          have h5 : (0:ℝ) ≤ frob N' * ‖p.2‖ := mul_nonneg hfr (norm_nonneg p.2)
          exact mul_le_mul (mul_le_mul h2 h1 h3 hM2) h1 h3 (mul_nonneg hM2 h5)
      _ = M2 * (frob N' * ‖p.2‖) * (frob N' * ‖p.2‖) := by ring
  exact hstep.trans (le_of_eq (by ring))

/-! ### The first and second moment terms -/

theorem norm_euclidBasis (i : n) : ‖euclidBasis (n := n) i‖ = 1 := by
  simp [euclidBasis]

theorem abs_hess_coord_le {M2 : ℝ} (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    (x : EuclideanSpace ℝ n) (i j : n) :
    |(hess h x) (euclidBasis i) (euclidBasis j)| ≤ M2 := by
  have h1 : ‖(hess h x) (euclidBasis i) (euclidBasis j)‖
      ≤ ‖(hess h x) (euclidBasis i)‖ * ‖euclidBasis (n := n) j‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖(hess h x) (euclidBasis i)‖ ≤ ‖hess h x‖ * ‖euclidBasis (n := n) i‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [norm_euclidBasis] at h1 h2
  rw [Real.norm_eq_abs] at h1
  calc |(hess h x) (euclidBasis i) (euclidBasis j)| ≤ ‖(hess h x) (euclidBasis i)‖ := by
        simpa using h1
    _ ≤ ‖hess h x‖ := by simpa using h2
    _ ≤ M2 := hb2 x

theorem continuous_hess_coord (hC : ContDiff ℝ 2 h) (i j : n) :
    Continuous fun x : EuclideanSpace ℝ n => (hess h x) (euclidBasis i) (euclidBasis j) :=
  (ContinuousLinearMap.apply ℝ ℝ (euclidBasis j)).continuous.comp
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ n →L[ℝ] ℝ)
      (euclidBasis i)).continuous.comp (continuous_hess hC))

theorem integral_fderiv_pair_eq_zero (hC : ContDiff ℝ 2 h) {M1 : ℝ}
    (hb1 : ∀ z, ‖fderiv ℝ h z‖ ≤ M1) (N N' : Matrix n n ℝ) :
    ∫ p, fderiv ℝ h (matCLM N p.1) (matCLM N' p.2)
      ∂((stdGaussian n).prod (stdGaussian n)) = 0 := by
  rw [integral_prod _ (integrable_fderiv_pair hC hb1 N N')]
  have hz : ∀ w : EuclideanSpace ℝ n,
      ∫ w', fderiv ℝ h (matCLM N w) (matCLM N' w') ∂(stdGaussian n) = 0 := fun w =>
    integral_clm_matCLM (fderiv ℝ h (matCLM N w)) N'
  simp [hz]

theorem integral_hess_pair_eq (hC : ContDiff ℝ 2 h) {M2 : ℝ} (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    (S : Matrix n n ℝ) {T : Matrix n n ℝ} (hT : T.PosSemidef) :
    ∫ p, (hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)) (matCLM (psdSqrt T) p.2)
        ∂((stdGaussian n).prod (stdGaussian n))
      = ∑ i, ∑ j, T i j * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) S := by
  rw [integral_prod _ (integrable_hess_pair hC hb2 (psdSqrt S) (psdSqrt T))]
  have hinner : ∀ w : EuclideanSpace ℝ n,
      ∫ w', (hess h (matCLM (psdSqrt S) w) (matCLM (psdSqrt T) w')) (matCLM (psdSqrt T) w')
          ∂(stdGaussian n)
        = ∑ i, ∑ j, T i j
            * (hess h (matCLM (psdSqrt S) w)) (euclidBasis i) (euclidBasis j) := by
    intro w
    rw [integral_bilin_matCLM (hess h (matCLM (psdSqrt S) w)) (psdSqrt T),
      psdSqrt_mul_transpose hT]
  simp_rw [hinner]
  have hcont : ∀ i j : n, Continuous fun w : EuclideanSpace ℝ n =>
      (hess h (matCLM (psdSqrt S) w)) (euclidBasis i) (euclidBasis j) := fun i j =>
    (continuous_hess_coord hC i j).comp (matCLM (psdSqrt S)).continuous
  have hint : ∀ i j : n, Integrable (fun w : EuclideanSpace ℝ n => T i j
      * (hess h (matCLM (psdSqrt S) w)) (euclidBasis i) (euclidBasis j)) (stdGaussian n) :=
    fun i j => (integrable_of_bound (hcont i j).aestronglyMeasurable
      (fun w => abs_hess_coord_le hb2 _ i j)).const_mul _
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, Gint, integral_multivariateGaussian_eq S _ (continuous_hess_coord hC i j)]

/-! ### Second-order Taylor representation of the increment -/

theorem Gint_add_sub_taylor_eq (hC : ContDiff ℝ 2 h) {M0 M1 M2 : ℝ}
    (hb0 : ∀ z, |h z| ≤ M0) (hb1 : ∀ z, ‖fderiv ℝ h z‖ ≤ M1) (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    {S T : Matrix n n ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef) :
    Gint h (S + T) - Gint h S
        - (1 / 2) * ∑ i, ∑ j, T i j
            * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) S
      = ∫ p, (h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
          - h (matCLM (psdSqrt S) p.1)
          - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)
          - (1 / 2) * ((hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
              (matCLM (psdSqrt T) p.2))) ∂((stdGaussian n).prod (stdGaussian n)) := by
  have hcont : Continuous h := hC.continuous
  have hF1int : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1))
      ((stdGaussian n).prod (stdGaussian n)) := by
    refine integrable_of_bound (by fun_prop) (M := 2 * M0) fun p => ?_
    calc |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)|
        ≤ |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)|
          + |h (matCLM (psdSqrt S) p.1)| := abs_sub _ _
      _ ≤ M0 + M0 := add_le_add (hb0 _) (hb0 _)
      _ = 2 * M0 := by ring
  have hF2int := integrable_fderiv_pair hC hb1 (psdSqrt S) (psdSqrt T)
  have hF3int := integrable_hess_pair hC hb2 (psdSqrt S) (psdSqrt T)
  have hAint : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)
        - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
      ((stdGaussian n).prod (stdGaussian n)) := hF1int.sub hF2int
  rw [integral_sub hAint (hF3int.const_mul (1 / 2)), integral_sub hF1int hF2int,
    integral_const_mul, integral_fderiv_pair_eq_zero hC hb1,
    integral_hess_pair_eq hC hb2 S hT, ← Gint_add_sub_eq hS hT hcont hb0]
  ring

/-! ### The second-order estimate -/

omit [DecidableEq n] in
theorem norm_hess_sub_le {M2 : ℝ} (hb2 : ∀ z, ‖hess h z‖ ≤ M2) (x y : EuclideanSpace ℝ n) :
    ‖hess h x - hess h y‖ ≤ M2 + M2 :=
  (norm_sub_le (hess h x) (hess h y)).trans (add_le_add (hb2 x) (hb2 y))


/-- The key estimate: uniformly over base covariances of trace at most `K`, the Gaussian
integral of `h` is differentiable in the covariance with derivative given by the expected
Hessian. -/
theorem exists_delta_order2 (hC : ContDiff ℝ 2 h) {M0 M1 M2 : ℝ}
    (hb0 : ∀ z, |h z| ≤ M0) (hb1 : ∀ z, ‖fderiv ℝ h z‖ ≤ M1) (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    {K ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ S T : Matrix n n ℝ, S.PosSemidef → T.PosSemidef →
      S.trace ≤ K → T.trace ≤ δ →
      |Gint h (S + T) - Gint h S
        - (1 / 2) * ∑ i, ∑ j, T i j
            * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) S| ≤ ε * T.trace := by
  have hM2 : 0 ≤ M2 := (norm_nonneg (hess h 0)).trans (hb2 0)
  obtain ⟨A, hA, hAtail⟩ := exists_tail_bound (n := n) (fun w => ‖w‖ ^ 2 + 1)
    (integrable_norm_sq_stdGaussian.add (integrable_const 1)) (fun w => by positivity)
    (show (0 : ℝ) < ε / (3 * (2 * M2 + 1)) by positivity)
  set J : EuclideanSpace ℝ n → ℝ :=
    Set.indicator {w : EuclideanSpace ℝ n | A < ‖w‖} (fun _ => (1 : ℝ)) with hJdef
  set Jsq : EuclideanSpace ℝ n → ℝ :=
    Set.indicator {w : EuclideanSpace ℝ n | A < ‖w‖} (fun w => ‖w‖ ^ 2) with hJsqdef
  have hJint : Integrable J (stdGaussian n) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_norm_gt A)
  have hJsqint : Integrable Jsq (stdGaussian n) :=
    integrable_norm_sq_stdGaussian.indicator (measurableSet_norm_gt A)
  have htailint : Integrable
      (Set.indicator {w : EuclideanSpace ℝ n | A < ‖w‖} (fun w => ‖w‖ ^ 2 + 1))
      (stdGaussian n) :=
    (integrable_norm_sq_stdGaussian.add (integrable_const 1)).indicator (measurableSet_norm_gt A)
  have hJ0 : ∀ w, 0 ≤ J w := fun w => Set.indicator_nonneg (fun _ _ => zero_le_one) w
  have hJsq0 : ∀ w, 0 ≤ Jsq w := fun w =>
    Set.indicator_nonneg (fun a _ => by positivity) w
  have hJ1 : ∀ w : EuclideanSpace ℝ n, A < ‖w‖ → J w = 1 := by
    intro w hw
    have hmem : w ∈ {w : EuclideanSpace ℝ n | A < ‖w‖} := hw
    rw [hJdef, Set.indicator_of_mem hmem]
  have hJsq1 : ∀ w : EuclideanSpace ℝ n, A < ‖w‖ → Jsq w = ‖w‖ ^ 2 := by
    intro w hw
    have hmem : w ∈ {w : EuclideanSpace ℝ n | A < ‖w‖} := hw
    rw [hJsqdef, Set.indicator_of_mem hmem]
  have hJle : ∫ w, J w ∂(stdGaussian n) ≤ ε / (3 * (2 * M2 + 1)) := by
    refine le_trans (integral_mono hJint htailint fun w => ?_) hAtail
    exact indicator_le_indicator_of_le (fun a => by nlinarith [sq_nonneg ‖a‖]) w
  have hJsqle : ∫ w, Jsq w ∂(stdGaussian n) ≤ ε / (3 * (2 * M2 + 1)) := by
    refine le_trans (integral_mono hJsqint htailint fun w => ?_) hAtail
    exact indicator_le_indicator_of_le (fun a => by nlinarith) w
  obtain ⟨η, hη, hη1, hmod⟩ :=
    exists_modulus (n := n) (F := EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ)
      (continuous_hess hC) (Real.sqrt K * A) (show (0 : ℝ) < ε / 3 by positivity)
  refine ⟨(η / (A + 1)) ^ 2, by positivity, ?_⟩
  intro S T hS hT hStr hTtr
  have hTtr0 : 0 ≤ T.trace := by
    rw [← integral_norm_sq_matCLM_psdSqrt hT]
    exact integral_nonneg fun w => by positivity
  have hvsq : ∀ w : EuclideanSpace ℝ n,
      ‖matCLM (psdSqrt T) w‖ ^ 2 ≤ T.trace * ‖w‖ ^ 2 := by
    intro w
    have h1 := norm_matCLM_psdSqrt_le hT w
    have h2 : (0 : ℝ) ≤ Real.sqrt T.trace * ‖w‖ := by positivity
    calc ‖matCLM (psdSqrt T) w‖ ^ 2 ≤ (Real.sqrt T.trace * ‖w‖) ^ 2 := by
          nlinarith [norm_nonneg (matCLM (psdSqrt T) w)]
      _ = T.trace * ‖w‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hTtr0]
  rw [Gint_add_sub_taylor_eq hC hb0 hb1 hb2 hS hT]
  -- the pointwise Taylor bound
  have hcrude : ∀ p : EuclideanSpace ℝ n × EuclideanSpace ℝ n,
      |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)
        - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)
        - (1 / 2) * ((hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
            (matCLM (psdSqrt T) p.2))|
      ≤ (M2 + M2) * ‖matCLM (psdSqrt T) p.2‖ ^ 2 := by
    intro p
    exact taylor_two_bound hC _ _ fun θ _ => norm_hess_sub_le hb2 _ _
  have hpt : ∀ p : EuclideanSpace ℝ n × EuclideanSpace ℝ n,
      |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)
        - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)
        - (1 / 2) * ((hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
            (matCLM (psdSqrt T) p.2))|
      ≤ ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * T.trace * Jsq p.2 := by
    intro p
    have h01 := hJ0 p.1
    have h02 := hJsq0 p.2
    have hnn : (0 : ℝ) ≤ ‖matCLM (psdSqrt T) p.2‖ ^ 2 := by positivity
    have hM2' : (0 : ℝ) ≤ 2 * M2 := by linarith
    by_cases h1 : A < ‖p.1‖
    · rw [hJ1 _ h1]
      have t1 : 0 ≤ ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2 := by positivity
      have t3 : 0 ≤ 2 * M2 * T.trace * Jsq p.2 :=
        mul_nonneg (mul_nonneg hM2' hTtr0) h02
      linarith [hcrude p]
    by_cases h2 : A < ‖p.2‖
    · rw [hJsq1 _ h2]
      have t1 : 0 ≤ ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2 := by positivity
      have t2 : 0 ≤ 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2 :=
        mul_nonneg (mul_nonneg hM2' h01) hnn
      have t3 := mul_le_mul_of_nonneg_left (hvsq p.2) hM2'
      linarith [hcrude p]
    push_neg at h1 h2
    have hx : ‖matCLM (psdSqrt S) p.1‖ ≤ Real.sqrt K * A := by
      refine (norm_matCLM_psdSqrt_le hS p.1).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt hStr) h1 (norm_nonneg _) (Real.sqrt_nonneg _)
    have hv : ‖matCLM (psdSqrt T) p.2‖ ≤ η := by
      refine (norm_matCLM_psdSqrt_le hT p.2).trans ?_
      have hsq : Real.sqrt T.trace ≤ η / (A + 1) := by
        refine (Real.sqrt_le_sqrt hTtr).trans ?_
        rw [Real.sqrt_sq (by positivity)]
      calc Real.sqrt T.trace * ‖p.2‖ ≤ (η / (A + 1)) * A :=
            mul_le_mul hsq h2 (norm_nonneg _) (by positivity)
        _ ≤ η := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [hη.le]
    have hgood : |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)
        - h (matCLM (psdSqrt S) p.1)
        - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)
        - (1 / 2) * ((hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
            (matCLM (psdSqrt T) p.2))| ≤ ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2 := by
      refine taylor_two_bound hC _ _ fun θ hθ => ?_
      refine hmod _ _ hx ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖matCLM (psdSqrt T) p.2‖ ≤ 1 * ‖matCLM (psdSqrt T) p.2‖ := by
            exact mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ ≤ η := by rw [one_mul]; exact hv
    have t2 : 0 ≤ 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2 :=
      mul_nonneg (mul_nonneg hM2' h01) hnn
    have t3 : 0 ≤ 2 * M2 * T.trace * Jsq p.2 :=
      mul_nonneg (mul_nonneg hM2' hTtr0) h02
    linarith [hgood]
  -- integrability of the bound
  have hbb1 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2) ((stdGaussian n).prod (stdGaussian n)) :=
    ((integrable_norm_sq_matCLM (psdSqrt T)).const_mul (ε / 3)).comp_snd _
  have hbb2 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2)
      ((stdGaussian n).prod (stdGaussian n)) :=
    (hJint.const_mul (2 * M2)).mul_prod (integrable_norm_sq_matCLM (psdSqrt T))
  have hbb3 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      2 * M2 * T.trace * Jsq p.2) ((stdGaussian n).prod (stdGaussian n)) :=
    (hJsqint.const_mul (2 * M2 * T.trace)).comp_snd _
  have hbb12 : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2)
      ((stdGaussian n).prod (stdGaussian n)) := hbb1.add hbb2
  have hbndint : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * T.trace * Jsq p.2) ((stdGaussian n).prod (stdGaussian n)) := hbb12.add hbb3
  have hPhiint : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
      h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)
        - fderiv ℝ h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2)
        - (1 / 2) * ((hess h (matCLM (psdSqrt S) p.1) (matCLM (psdSqrt T) p.2))
            (matCLM (psdSqrt T) p.2))) ((stdGaussian n).prod (stdGaussian n)) := by
    have hcont : Continuous h := hC.continuous
    have hF1int : Integrable (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
        h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1))
        ((stdGaussian n).prod (stdGaussian n)) := by
      refine integrable_of_bound (by fun_prop) (M := 2 * M0) fun p => ?_
      calc |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2) - h (matCLM (psdSqrt S) p.1)|
          ≤ |h (matCLM (psdSqrt S) p.1 + matCLM (psdSqrt T) p.2)|
            + |h (matCLM (psdSqrt S) p.1)| := abs_sub _ _
        _ ≤ M0 + M0 := add_le_add (hb0 _) (hb0 _)
        _ = 2 * M0 := by ring
    exact (hF1int.sub (integrable_fderiv_pair hC hb1 (psdSqrt S) (psdSqrt T))).sub
      ((integrable_hess_pair hC hb2 (psdSqrt S) (psdSqrt T)).const_mul (1 / 2))
  refine (abs_integral_le_integral_abs.trans
    (integral_mono hPhiint.abs hbndint hpt)).trans ?_
  have hcalc : ∫ p, (ε / 3 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * J p.1 * ‖matCLM (psdSqrt T) p.2‖ ^ 2
        + 2 * M2 * T.trace * Jsq p.2) ∂((stdGaussian n).prod (stdGaussian n))
      = ε / 3 * T.trace + (2 * M2 * ∫ w, J w ∂(stdGaussian n)) * T.trace
        + 2 * M2 * T.trace * ∫ w, Jsq w ∂(stdGaussian n) := by
    rw [integral_add hbb12 hbb3, integral_add hbb1 hbb2]
    congr 1
    · congr 1
      · rw [integral_snd_stdGaussian
          (f := fun w => ε / 3 * ‖matCLM (psdSqrt T) w‖ ^ 2)
          ((by fun_prop : Continuous fun w : EuclideanSpace ℝ n =>
            ε / 3 * ‖matCLM (psdSqrt T) w‖ ^ 2)).aestronglyMeasurable,
          integral_const_mul, integral_norm_sq_matCLM_psdSqrt hT]
      · rw [integral_prod_mul (fun w : EuclideanSpace ℝ n => 2 * M2 * J w)
          (fun w : EuclideanSpace ℝ n => ‖matCLM (psdSqrt T) w‖ ^ 2),
          integral_const_mul, integral_norm_sq_matCLM_psdSqrt hT]
    · rw [integral_snd_stdGaussian (f := fun w => 2 * M2 * T.trace * Jsq w)
        ((hJsqint.const_mul (2 * M2 * T.trace)).aestronglyMeasurable),
        integral_const_mul]
  rw [hcalc]
  have hJ0' : 0 ≤ ∫ w, J w ∂(stdGaussian n) := integral_nonneg hJ0
  have hJsq0' : 0 ≤ ∫ w, Jsq w ∂(stdGaussian n) := integral_nonneg hJsq0
  have hkey : 2 * M2 * (ε / (3 * (2 * M2 + 1))) ≤ ε / 3 := by
    rw [show 2 * M2 * (ε / (3 * (2 * M2 + 1))) = (2 * M2 * ε) / (3 * (2 * M2 + 1)) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hε.le, hM2]
  nlinarith [mul_le_mul_of_nonneg_left hJle (by positivity : (0:ℝ) ≤ 2 * M2),
    mul_le_mul_of_nonneg_left hJsqle (by positivity : (0:ℝ) ≤ 2 * M2), hTtr0, hkey]

end ProbabilityTheory
