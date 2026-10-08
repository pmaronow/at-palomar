module

public import Lemmas.SpinGlass.SKModel
public import Lemmas.SpinGlass.Calculus
public import Lemmas.SpinGlass.Replicas

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace GeneralizedLatala

universe uΩ uι

variable {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
A self-contained proof of `independent_gaussian_affine_ibp`.

The proof packages `(sk.U, sim.V)` as the joint Gaussian Hilbert vector `UV`, applies
coordinatewise Hilbert-space Gaussian integration by parts, splits the resulting eigenbasis
trace into its `U` and `V` blocks, and finally rewrites both traces in the canonical
configuration basis using `sk.cov_eq` and `sim.cov_eq`.
-/

section GenericHelpers

variable {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E]

private lemma affineIBP_fderiv_firstVariation_affine
    [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N) (field v : EnergySpace N) (x y : E) :
    fderiv ℝ
        (fun z : E =>
          fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (A z + field) v) x y =
      (hessian_free_energy_fderiv (N := N) (A x + field)) (A y) v := by
  have hc : HasFDerivAt
      (fun z : E =>
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (A z + field))
      ((hessian_free_energy_fderiv (N := N) (A x + field)).comp A) x := by
    apply HasFDerivAt.comp x
    · have hcf : ContDiff ℝ 1
          (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)) :=
        (contDiff_free_energy_density (N := N)).fderiv_right
          (m := (1 : WithTop ℕ∞)) (by
            change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
            exact WithTop.coe_le_coe.mpr le_top)
      exact (hcf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    · simpa using A.hasFDerivAt.add_const field
  have hv := hc.clm_apply (hasFDerivAt_const (x := x) (c := v))
  rw [hv.fderiv]
  simp

private lemma affineIBP_abs_hessian_free_energy_le
    (H u v : EnergySpace N) :
    |hessian_free_energy N H u v| ≤
      2 * (1 / (N : ℝ)) * ‖u‖ * ‖v‖ := by
  classical
  have hp_sum :
      ∑ σ : Config N, gibbs_pmf N H σ = 1 :=
    sum_gibbs_pmf N H
  have hfirst :
      |∑ σ : Config N, gibbs_pmf N H σ * u σ * v σ| ≤
        ‖u‖ * ‖v‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * u σ * v σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * u σ * v σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * (‖u‖ * ‖v‖) := by
        gcongr with σ
        rw [abs_mul, abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        have huv : |u σ| * |v σ| ≤ ‖u‖ * ‖v‖ :=
          mul_le_mul
            (abs_apply_le_norm N u σ)
            (abs_apply_le_norm N v σ)
            (abs_nonneg _) (norm_nonneg _)
        calc
          gibbs_pmf N H σ * |u σ| * |v σ| =
              gibbs_pmf N H σ * (|u σ| * |v σ|) := by
                ring
          _ ≤ gibbs_pmf N H σ * (‖u‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left huv
              (gibbs_pmf_nonneg N H σ)
      _ = ‖u‖ * ‖v‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  have hu :
      |∑ σ : Config N, gibbs_pmf N H σ * u σ| ≤ ‖u‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * u σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * u σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * ‖u‖ := by
        gcongr with σ
        rw [abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        exact mul_le_mul_of_nonneg_left
          (abs_apply_le_norm N u σ)
          (gibbs_pmf_nonneg N H σ)
      _ = ‖u‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  have hv :
      |∑ σ : Config N, gibbs_pmf N H σ * v σ| ≤ ‖v‖ := by
    calc
      |∑ σ : Config N, gibbs_pmf N H σ * v σ|
          ≤ ∑ σ : Config N,
              |gibbs_pmf N H σ * v σ| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Config N,
            gibbs_pmf N H σ * ‖v‖ := by
        gcongr with σ
        rw [abs_mul,
          abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
        exact mul_le_mul_of_nonneg_left
          (abs_apply_le_norm N v σ)
          (gibbs_pmf_nonneg N H σ)
      _ = ‖v‖ := by
        rw [← Finset.sum_mul, hp_sum, one_mul]
  rw [hessian_free_energy, abs_mul]
  have hN0 : 0 ≤ (1 / (N : ℝ)) :=
    one_div_nonneg.mpr (Nat.cast_nonneg N)
  rw [abs_of_nonneg hN0]
  calc
    1 / (N : ℝ) *
        |(∑ σ : Config N,
            gibbs_pmf N H σ * u σ * v σ) -
          (∑ σ : Config N,
            gibbs_pmf N H σ * u σ) *
            ∑ τ : Config N,
              gibbs_pmf N H τ * v τ|
      ≤ 1 / (N : ℝ) *
          (|(∑ σ : Config N,
              gibbs_pmf N H σ * u σ * v σ)| +
            |(∑ σ : Config N,
              gibbs_pmf N H σ * u σ) *
              ∑ τ : Config N,
                gibbs_pmf N H τ * v τ|) := by
        gcongr
        exact abs_sub _ _
    _ ≤ 1 / (N : ℝ) *
        (‖u‖ * ‖v‖ + ‖u‖ * ‖v‖) := by
      gcongr
      rw [abs_mul]
      exact mul_le_mul hu hv (abs_nonneg _) (norm_nonneg _)
    _ = 2 * (1 / (N : ℝ)) * ‖u‖ * ‖v‖ := by
      ring

private noncomputable def
    affineIBP_hasModerateGrowth_firstVariation_affine
    [NormedSpace ℝ E]
    (A : E →L[ℝ] EnergySpace N)
    (field v : EnergySpace N) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun x : E =>
        fderiv ℝ
          (fun H : EnergySpace N =>
            free_energy_density (N := N) H)
          (A x + field) v) := by
  let C0 :=
    (SpinGlass.hasModerateGrowth_free_energy_density N).C
  let C1 := C0 * (1 + ‖field‖ + ‖A‖) * ‖v‖
  let C2 := 2 * (1 / (N : ℝ)) * ‖A‖ * ‖v‖
  let C := 1 + C1 + C2
  refine ⟨C, 1, ?_, ?_, ?_⟩
  · have hC0 : 0 < C0 :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos
    have hC1 : 0 ≤ C1 := by positivity
    have hC2 : 0 ≤ C2 := by positivity
    dsimp [C]
    positivity
  · intro x
    have hbase :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).bound_dF_apply
        (A x + field) v
    have hm :
        (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 :=
      rfl
    rw [hm, pow_one] at hbase
    have hAx : ‖A x‖ ≤ ‖A‖ * ‖x‖ :=
      A.le_opNorm x
    have hsum :
        1 + ‖A x + field‖ ≤
          (1 + ‖field‖ + ‖A‖) * (1 + ‖x‖) := by
      have hadd := norm_add_le (A x) field
      nlinarith [norm_nonneg x, norm_nonneg field, norm_nonneg A]
    have hC0 : 0 ≤ C0 :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos.le
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hmul :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hC0) hv0
    have hC1 : 0 ≤ C1 := by positivity
    have hC2 : 0 ≤ C2 := by positivity
    have hx1 : 0 ≤ 1 + ‖x‖ := by positivity
    calc
      |fderiv ℝ
          (fun H : EnergySpace N =>
            free_energy_density (N := N) H)
          (A x + field) v| =
          ‖fderiv ℝ
            (fun H : EnergySpace N =>
              free_energy_density (N := N) H)
            (A x + field) v‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ C0 * (1 + ‖A x + field‖) * ‖v‖ :=
        hbase
      _ ≤ C1 * (1 + ‖x‖) := by
        simpa [C1, mul_assoc, mul_comm, mul_left_comm]
          using hmul
      _ ≤ C * (1 + ‖x‖) := by
        apply mul_le_mul_of_nonneg_right _ hx1
        dsimp [C]
        linarith
      _ = C * (1 + ‖x‖) ^ 1 := by
        rw [pow_one]
  · intro x
    have hC2 : 0 ≤ C2 := by positivity
    have hop :
        ‖fderiv ℝ
          (fun z : E =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                free_energy_density (N := N) H)
              (A z + field) v) x‖ ≤ C2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC2 ?_
      intro y
      rw [affineIBP_fderiv_firstVariation_affine
        A field v x y,
        hessian_free_energy_fderiv_eq_hessian_free_energy]
      rw [Real.norm_eq_abs]
      have hh :=
        affineIBP_abs_hessian_free_energy_le
          (N := N) (A x + field) (A y) v
      calc
        |hessian_free_energy N
            (A x + field) (A y) v|
            ≤ 2 * (1 / (N : ℝ)) * ‖A y‖ * ‖v‖ :=
          hh
        _ ≤ C2 * ‖y‖ := by
          have hAy := A.le_opNorm y
          have hfac : 0 ≤ 2 * (1 / (N : ℝ)) := by
            positivity
          have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
          have hmul :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAy hfac) hv0
          simpa [C2, mul_assoc, mul_comm, mul_left_comm]
            using hmul
    have hC1 : 0 ≤ C1 := by
      have hC0 : 0 ≤ C0 :=
        (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos.le
      dsimp [C1]
      positivity
    have hx1 : 1 ≤ 1 + ‖x‖ := by
      linarith [norm_nonneg x]
    calc
      ‖fderiv ℝ
          (fun z : E =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                free_energy_density (N := N) H)
              (A z + field) v) x‖
          ≤ C2 :=
        hop
      _ ≤ C * (1 + ‖x‖) := by
        have hC2C : C2 ≤ C := by
          dsimp [C]
          linarith
        exact hC2C.trans
          (le_mul_of_one_le_right
            (by dsimp [C]; positivity) hx1)
      _ = C * (1 + ‖x‖) ^ 1 := by
        rw [pow_one]

private lemma affineIBP_gaussian_ibp_gradient_linear
    {K : Type*}
    [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] K) (field : K) (F : K → ℝ)
    (hFi_diff : ∀ i : hg.ι, ContDiff ℝ 1
      (fun x : E =>
        fderiv ℝ F (A x + field) (B (hg.w i))))
    (hFi_growth : ∀ i : hg.ι,
      PhysLean.Probability.GaussianIBP.HasModerateGrowth
        (fun x : E =>
          fderiv ℝ F (A x + field) (B (hg.w i)))) :
    (∫ w,
      fderiv ℝ F (A (g w) + field) (B (g w)) ∂ℙ) =
      ∫ w, ∑ i : hg.ι, (hg.τ i : ℝ) *
        fderiv ℝ
          (fun x : E =>
            fderiv ℝ F
              (A x + field) (B (hg.w i)))
          (g w) (hg.w i) ∂ℙ := by
  classical
  let Fi : hg.ι → E → ℝ := fun i x =>
    fderiv ℝ F (A x + field) (B (hg.w i))
  have hleft (w : Ω) :
      fderiv ℝ F (A (g w) + field) (B (g w)) =
        ∑ i : hg.ι,
          PhysLean.Probability.GaussianIBP.coord
              hg.w g i w *
            Fi i (g w) := by
    rw [show g w =
        ∑ i : hg.ι,
          ((PhysLean.Probability.GaussianIBP.coord
            hg.w g i w : ℝ) • hg.w i) by
      simpa [
        PhysLean.Probability.GaussianIBP.coord,
        hg.w.repr_apply_apply,
        real_inner_comm
      ] using (hg.w.sum_repr (g w)).symm]
    simp only [map_sum, map_smul, smul_eq_mul, Fi]
  have hLint : ∀ i : hg.ι, Integrable
      (fun w =>
        PhysLean.Probability.GaussianIBP.coord
            hg.w g i w *
          Fi i (g w)) ℙ := by
    intro i
    exact
      PhysLean.Probability.GaussianIBP.integrable_coord_mul_F
        hg (by simpa only [Fi] using hFi_diff i)
          (by simpa only [Fi] using hFi_growth i) i
  have hRint : ∀ i : hg.ι, Integrable
      (fun w =>
        fderiv ℝ (Fi i) (g w) (hg.w i)) ℙ := by
    intro i
    exact
      PhysLean.Probability.GaussianIBP.integrable_fderiv_apply
        hg (by simpa only [Fi] using hFi_diff i)
          (by simpa only [Fi] using hFi_growth i) (hg.w i)
  calc
    (∫ w,
      fderiv ℝ F
        (A (g w) + field) (B (g w)) ∂ℙ) =
        ∑ i : hg.ι, ∫ w,
          PhysLean.Probability.GaussianIBP.coord
              hg.w g i w *
            Fi i (g w) ∂ℙ := by
      rw [MeasureTheory.integral_congr_ae
        (ae_of_all _ hleft)]
      exact MeasureTheory.integral_finset_sum _
        (fun i _ => hLint i)
    _ = ∑ i : hg.ι, (hg.τ i : ℝ) *
          ∫ w,
            fderiv ℝ (Fi i)
              (g w) (hg.w i) ∂ℙ := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        PhysLean.Probability.GaussianIBP.ProbabilityTheory.coord_IBP
          hg (by simpa only [Fi] using hFi_diff i)
            (by simpa only [Fi] using hFi_growth i) i
    _ = ∫ w, ∑ i : hg.ι, (hg.τ i : ℝ) *
          fderiv ℝ (Fi i)
            (g w) (hg.w i) ∂ℙ := by
      rw [MeasureTheory.integral_finset_sum _]
      · simp only [MeasureTheory.integral_const_mul]
      · intro i _
        exact (hRint i).const_mul _
    _ = _ := by
      rfl

/-- Gaussian integration by parts for the gradient of a function evaluated along
two linear images of the same finite-dimensional Gaussian Hilbert variable. -/
lemma gaussian_ibp_gradient_linear
    {K : Type*}
    [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    (g : Ω → E)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : E →L[ℝ] K) (field : K) (F : K → ℝ)
    (hFi_diff : ∀ i : hg.ι, ContDiff ℝ 1
      (fun x : E =>
        fderiv ℝ F (A x + field) (B (hg.w i))))
    (hFi_growth : ∀ i : hg.ι,
      PhysLean.Probability.GaussianIBP.HasModerateGrowth
        (fun x : E =>
          fderiv ℝ F (A x + field) (B (hg.w i)))) :
    (∫ w,
      fderiv ℝ F (A (g w) + field) (B (g w)) ∂ℙ) =
      ∫ w, ∑ i : hg.ι, (hg.τ i : ℝ) *
        fderiv ℝ
          (fun x : E =>
            fderiv ℝ F
              (A x + field) (B (hg.w i)))
          (g w) (hg.w i) ∂ℙ := by
  exact affineIBP_gaussian_ibp_gradient_linear
    g hg A B field F hFi_diff hFi_growth

end GenericHelpers

section JointDisorder

variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder.{uΩ} (Ω := Ω) N β h)
variable (sim : SimpleDisorder.{uΩ} (Ω := Ω) N β q)

private noncomputable def affineIBP_jointAffineCLM
    (a b : ℝ) :
    WithLp 2
        (EnergySpace N × EnergySpace N) →L[ℝ]
      EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        a • (WithLp.ofLp p).1 +
          b • (WithLp.ofLp p).2
      map_add' := by
        intro x y
        simp
        abel
      map_smul' := by
        intro c x
        simp [smul_add, smul_smul, mul_comm] }

private lemma
    affineIBP_joint_gaussian_affine_ibp_eigenbasis
    (hIndep :
      IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ
        (fun H : EnergySpace N =>
          free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field)
        (a' • sk.U w + b' • sim.V w) ∂ℙ) =
      ∫ w,
        ∑ i :
            (isGaussianHilbert_UV
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) hIndep).ι,
          (((isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) hIndep).τ i :
              NNReal) : ℝ) *
            hessian_free_energy N
              (a • sk.U w + b • sim.V w + field)
              (affineIBP_jointAffineCLM
                (N := N) a b
                ((isGaussianHilbert_UV
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := sk) (sim := sim) hIndep).w i))
              (affineIBP_jointAffineCLM
                (N := N) a' b'
                ((isGaussianHilbert_UV
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := sk) (sim := sim) hIndep).w i))
        ∂ℙ := by
  let hg :=
    isGaussianHilbert_UV
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep
  let A := affineIBP_jointAffineCLM (N := N) a b
  let B := affineIBP_jointAffineCLM (N := N) a' b'
  have hFi_diff :
      ∀ i : hg.ι, ContDiff ℝ 1
        (fun x =>
          fderiv ℝ
            (fun H : EnergySpace N =>
              free_energy_density (N := N) H)
            (A x + field) (B (hg.w i))) := by
    intro i
    have hgrad : ContDiff ℝ 1
        (fderiv ℝ
          (fun H : EnergySpace N =>
            free_energy_density (N := N) H)) :=
      (contDiff_free_energy_density
        (N := N)).fderiv_right
        (m := (1 : WithTop ℕ∞)) (by
          change
            (↑(2 : ℕ∞) : WithTop ℕ∞) ≤
              ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)
    exact
      (hgrad.comp
        (A.contDiff.add contDiff_const)).clm_apply
        contDiff_const
  have hFi_growth :
      ∀ i : hg.ι,
        PhysLean.Probability.GaussianIBP.HasModerateGrowth
          (fun x =>
            fderiv ℝ
              (fun H : EnergySpace N =>
                free_energy_density (N := N) H)
              (A x + field) (B (hg.w i))) := by
    intro i
    exact
      affineIBP_hasModerateGrowth_firstVariation_affine
        A field (B (hg.w i))
  have hmain :=
    affineIBP_gaussian_ibp_gradient_linear
      (g := UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim))
      (hg := hg) A B field
      (fun H : EnergySpace N =>
        free_energy_density (N := N) H)
      hFi_diff hFi_growth
  change
    (∫ w,
      fderiv ℝ
        (fun H : EnergySpace N =>
          free_energy_density (N := N) H)
        (A
          (UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) w) + field)
        (B
          (UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) w))
      ∂ℙ) = _
  rw [hmain]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  simp only [
    hg, A, B, UV, affineIBP_jointAffineCLM
  ]
  apply Finset.sum_congr rfl
  intro i _
  rw [
    affineIBP_fderiv_firstVariation_affine,
    hessian_free_energy_fderiv_eq_hessian_free_energy
  ]
  rfl

private lemma affineIBP_joint_trace_split
    (hIndep :
      IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (H : EnergySpace N) :
    (∑ i :
        (isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) hIndep).ι,
      (((isGaussianHilbert_UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) hIndep).τ i :
          NNReal) : ℝ) *
        hessian_free_energy N H
          (affineIBP_jointAffineCLM
            (N := N) a b
            ((isGaussianHilbert_UV
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) hIndep).w i))
          (affineIBP_jointAffineCLM
            (N := N) a' b'
            ((isGaussianHilbert_UV
              (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) hIndep).w i))) =
      (a * a') *
          ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
            hessian_free_energy N H
              (sk.hU.w i) (sk.hU.w i) +
      (b * b') *
          ∑ i : sim.hV.ι, (sim.hV.τ i : ℝ) *
            hessian_free_energy N H
              (sim.hV.w i) (sim.hV.w i) := by
  classical
  rw [show
    @Finset.univ
        (isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) hIndep).ι
        (isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) hIndep).fintype_ι =
      @Finset.univ (sk.hU.ι ⊕ sim.hV.ι) inferInstance by
    ext i
    simp only [Finset.mem_univ]]
  simp only [
    isGaussianHilbert_UV,
    affineIBP_jointAffineCLM,
    OrthonormalBasis.prod_apply,
    Fintype.sum_sum_type
  ]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [LinearMap.inl_apply, LinearMap.inr_apply, Function.comp_apply]
  have map_add' : ∀ (x y : WithLp 2 (EnergySpace N × EnergySpace N)),
      a • (x + y).ofLp.1 + b • (x + y).ofLp.2 = a • x.ofLp.1 + b • x.ofLp.2 + (a • y.ofLp.1 + b • y.ofLp.2) := by
    intro x y
    simp [Prod.fst_add, Prod.snd_add]
    abel
  have map_smul' : ∀ (m : ℝ) (x : WithLp 2 (EnergySpace N × EnergySpace N)),
      a • (m • x).ofLp.1 + b • (m • x).ofLp.2 = (RingHom.id ℝ) m • (a • x.ofLp.1 + b • x.ofLp.2) := by
    intro m x
    simp only [smul_add, RingHom.id_apply]
    simp only [smul_comm m a, smul_comm m b]
    rfl
  -- Simplify CLM applications on basis elements
  have hCLM_U : ∀ x : sk.hU.ι,
      affineIBP_jointAffineCLM (N := N) a b (WithLp.toLp 2 (sk.hU.w x, 0)) = a • sk.hU.w x := by
    intro x
    simp [affineIBP_jointAffineCLM]
  have hCLM_V : ∀ x : sim.hV.ι,
      affineIBP_jointAffineCLM (N := N) a b (WithLp.toLp 2 (0, sim.hV.w x)) = b • sim.hV.w x := by
    intro x
    simp [affineIBP_jointAffineCLM]
  have hCLM_U' : ∀ x : sk.hU.ι,
      affineIBP_jointAffineCLM (N := N) a' b' (WithLp.toLp 2 (sk.hU.w x, 0)) = a' • sk.hU.w x := by
    intro x
    simp [affineIBP_jointAffineCLM]
  have hCLM_V' : ∀ x : sim.hV.ι,
      affineIBP_jointAffineCLM (N := N) a' b' (WithLp.toLp 2 (0, sim.hV.w x)) = b' • sim.hV.w x := by
    intro x
    simp [affineIBP_jointAffineCLM]
  simp only [affineIBP_jointAffineCLM] at *
  simp_rw [hCLM_U, hCLM_V, hCLM_U', hCLM_V']
  -- Use bilinearity: hessian_free_energy N H (a • u) (a' • v) = a * a' * hessian_free_energy N H u v
  have bilin : ∀ (a a' : ℝ) (u v : EnergySpace N),
      hessian_free_energy N H (a • u) (a' • v) = a * a' * hessian_free_energy N H u v := by
    intro a a' u v
    show (1 / (N : ℝ)) * (∑ σ, gibbs_pmf N H σ * (a • u) σ * (a' • v) σ -
        (∑ σ, gibbs_pmf N H σ * (a • u) σ) * (∑ τ, gibbs_pmf N H τ * (a' • v) τ)) =
        a * a' * ((1 / (N : ℝ)) * (∑ σ, gibbs_pmf N H σ * u σ * v σ -
        (∑ σ, gibbs_pmf N H σ * u σ) * (∑ τ, gibbs_pmf N H τ * v τ)))
    have h1 : ∀ x, (a • u).ofLp x = a * u.ofLp x := fun x => rfl
    have h2 : ∀ x, (a' • v).ofLp x = a' * v.ofLp x := fun x => rfl
    simp [h1, h2]
    ring_nf
    have eq1 : ∀ x, gibbs_pmf N H x * a * u.ofLp x * a' * v.ofLp x = a * a' * (gibbs_pmf N H x * u.ofLp x * v.ofLp x) := by intro x; ring
    have eq2 : ∀ x, a * gibbs_pmf N H x * u.ofLp x = a * (gibbs_pmf N H x * u.ofLp x) := by intro x; ring
    have eq3 : ∀ x, a' * gibbs_pmf N H x * v.ofLp x = a' * (gibbs_pmf N H x * v.ofLp x) := by intro x; ring
    simp_rw [eq1, eq2, eq3]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    ring
  simp_rw [bilin]
  ring_nf
  have eq1 : ∀ x, ↑(sk.hU.τ x) * a * a' * hessian_free_energy N H (sk.hU.w x) (sk.hU.w x) = a * a' * (↑(sk.hU.τ x) * hessian_free_energy N H (sk.hU.w x) (sk.hU.w x)) := by intro x; ring
  have eq2 : ∀ x, ↑(sim.hV.τ x) * b * b' * hessian_free_energy N H (sim.hV.w x) (sim.hV.w x) = b * b' * (↑(sim.hV.τ x) * hessian_free_energy N H (sim.hV.w x) (sim.hV.w x)) := by intro x; ring
  simp_rw [eq1, eq2]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]

private lemma
    affineIBP_gaussian_hessian_trace_eq_std_basis
    {Ω' : Type*}
    [MeasureSpace Ω']
    [IsProbabilityMeasure (volume : Measure Ω')]
    (g : Ω' → EnergySpace N)
    (hg :
      PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (H : EnergySpace N) :
    (∑ i : hg.ι, (hg.τ i : ℝ) *
      hessian_free_energy N H
        (hg.w i) (hg.w i)) =
      ∑ σ : Config N, ∑ τ : Config N,
        inner ℝ
            ((PhysLean.Probability.GaussianIBP.covOp
              (g := g) hg) (std_basis N σ))
            (std_basis N τ) *
          hessian_free_energy N H
            (std_basis N σ) (std_basis N τ) := by
  -- Expand covOp using covOp_apply
  simp_rw [PhysLean.Probability.GaussianIBP.covOp_apply]
  -- Simplify inner product with sum
  have hinner : ∀ σ τ : Config N,
      inner (𝕜 := ℝ) (∑ i : hg.ι, ((hg.τ i : ℝ) * inner (𝕜 := ℝ) (std_basis N σ) (hg.w i)) • hg.w i) (std_basis N τ)
    = ∑ i : hg.ι, (hg.τ i : ℝ) * inner (𝕜 := ℝ) (std_basis N σ) (hg.w i) * inner (𝕜 := ℝ) (hg.w i) (std_basis N τ) := by
    intro σ τ
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    simp
  -- Rewrite RHS using hinner
  simp_rw [hinner]
  -- Rearrange the sums
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  -- Swap sums: ∑ x, ∑ x_1, ∑ i → ∑ i, ∑ x, ∑ x_1
  symm
  rw [Finset.sum_comm]
  -- Now we have ∑ x_1, ∑ x, ∑ i where inner term has std_basis N x (the outer one)
  -- Need to swap the inner ∑ x, ∑ i to ∑ i, ∑ x
  have h1 : ∀ y ∈ Finset.univ, ∑ x, ∑ i, ↑(hg.τ i) * inner ℝ (std_basis N y) (hg.w i) * inner ℝ (hg.w i) (std_basis N x) * hessian_free_energy N H (std_basis N y) (std_basis N x) =
            ∑ i, ∑ x, ↑(hg.τ i) * inner ℝ (std_basis N y) (hg.w i) * inner ℝ (hg.w i) (std_basis N x) * hessian_free_energy N H (std_basis N y) (std_basis N x) := by
    intro y _; exact Finset.sum_comm
  rw [Finset.sum_congr rfl h1]
  -- Now swap outer ∑ x, ∑ i to ∑ i, ∑ x
  rw [Finset.sum_comm]
  -- Pull out τ factor using congruence
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_assoc]
  -- Now use completeness of standard basis
  have hcomplete : ∀ v : EnergySpace N, ∑ x : Config N, inner ℝ (std_basis N x) v • std_basis N x = v := by
    intro v
    ext i
    simp [inner_std_basis_apply]
    have hstd : ∀ σ τ : Config N, (std_basis N σ).ofLp τ = if σ = τ then 1 else 0 := by
      intro σ τ
      simp [std_basis]
    simp [hstd]
  -- Use bilinearity of hessian and completeness
  have hinner_eq : ∀ v : EnergySpace N, ∀ σ : Config N, inner ℝ (std_basis N σ) v = v σ := by
    intro v σ
    exact inner_std_basis_apply N σ v
  have hinner_eq_symm : ∀ v : EnergySpace N, ∀ σ : Config N, inner ℝ v (std_basis N σ) = v σ := by
    intro v σ
    rw [real_inner_comm]
    exact hinner_eq v σ
  simp_rw [hinner_eq, hinner_eq_symm]
  -- Factor out tau and rearrange
  ring_nf
  -- Helper: hessian_free_energy is bilinear
  have hlin1 : ∀ (H : EnergySpace N) (u v w : EnergySpace N) (a b : ℝ),
    hessian_free_energy N H (a • u + b • v) w = a * hessian_free_energy N H u w + b * hessian_free_energy N H v w := by
    intro H u v w a b
    simp [hessian_free_energy, PiLp.add_apply, PiLp.smul_apply]
    ring_nf
    simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm, mul_left_comm]
    ring_nf
  have hsym : ∀ (H u v : EnergySpace N), hessian_free_energy N H u v = hessian_free_energy N H v u := by
    intro H u v
    rw [hessian_free_energy, hessian_free_energy]
    have : (fun x => gibbs_pmf N H x * u.ofLp x * v.ofLp x) = (fun x => gibbs_pmf N H x * v.ofLp x * u.ofLp x) := by
      ext x; ring
    simp_all [mul_comm, mul_assoc, mul_left_comm]
  have hlin2 : ∀ (H : EnergySpace N) (u v w : EnergySpace N) (a b : ℝ),
    hessian_free_energy N H u (a • v + b • w) = a * hessian_free_energy N H u v + b * hessian_free_energy N H u w := by
    intro H u v w a b
    rw [hsym, hlin1]
    rw [← hsym H v u, ← hsym H w u]
  -- Use completeness: hg.w y = ∑ x, (hg.w y).ofLp x • std_basis N x
  have hcomplete_y : hg.w y = ∑ x : Config N, (hg.w y).ofLp x • std_basis N x := by
    have h := hcomplete (hg.w y)
    simp_rw [hinner_eq (hg.w y)] at h
    exact h.symm
  -- Helper: apply .ofLp to a linear combination of standard basis vectors
  have hofLp_sum : ∀ (c : Config N → ℝ) (y : Config N),
      (∑ x : Config N, c x • std_basis N x).ofLp y = c y := by
    intro c y
    have hstd : ∀ σ τ : Config N, (std_basis N σ).ofLp τ = if σ = τ then (1 : ℝ) else 0 := by
      intro σ τ
      simp [std_basis]
    calc (∑ x : Config N, c x • std_basis N x).ofLp y
        = ∑ x : Config N, c x * (std_basis N x).ofLp y := by
          simp
      _ = ∑ x : Config N, c x * (if x = y then 1 else 0) := by
          simp [hstd]
      _ = c y := by simp
  -- Expand a finite sum in the first argument
  have hlin1_finset : ∀ (H : EnergySpace N) (s : Finset (Config N))
      (c : Config N → ℝ) (w : Config N → EnergySpace N) (u : EnergySpace N),
    hessian_free_energy N H (∑ x ∈ s, c x • w x) u = ∑ x ∈ s, c x * hessian_free_energy N H (w x) u := by
    intro H s c w u
    induction s using Finset.induction_on with
    | empty => simp [hessian_free_energy]
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have := @hlin1 H (w a) (∑ x ∈ s, c x • w x) u (c a) 1
      simp at this
      rw [this, ih]
  -- Expand a finite sum in the second argument
  have hlin2_finset : ∀ (H : EnergySpace N) (s : Finset (Config N))
      (c : Config N → ℝ) (w : Config N → EnergySpace N) (u : EnergySpace N),
    hessian_free_energy N H u (∑ x ∈ s, c x • w x) = ∑ x ∈ s, c x * hessian_free_energy N H u (w x) := by
    intro H s c w u
    induction s using Finset.induction_on with
    | empty => simp [hessian_free_energy]
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have := @hlin2 H u (∑ x ∈ s, c x • w x) (w a) 1 (c a)
      simp at this
      rw [add_comm, this, ih]
      ring
  -- Expand hessian_free_energy N H (hg.w y) (hg.w y) using bilinearity
  have hexpand : hessian_free_energy N H (hg.w y) (hg.w y) =
    ∑ x : Config N, ∑ x_1 : Config N, (hg.w y).ofLp x * (hg.w y).ofLp x_1 *
      hessian_free_energy N H (std_basis N x) (std_basis N x_1) := by
    rw [hcomplete_y, hcomplete_y]
    rw [hlin1_finset]
    simp_rw [hlin2_finset]
    simp_rw [hofLp_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro _ _
    ring
  simp_rw [hexpand]
  calc ∑ x : Config N, ∑ x_1 : Config N, ↑(hg.τ y) * (hg.w y).ofLp x * (hg.w y).ofLp x_1 *
        hessian_free_energy N H (std_basis N x) (std_basis N x_1)
      = ∑ x : Config N, ↑(hg.τ y) * ∑ x_1 : Config N, (hg.w y).ofLp x * (hg.w y).ofLp x_1 *
          hessian_free_energy N H (std_basis N x) (std_basis N x_1) := by
          congr 1; ext x; rw [Finset.mul_sum]; congr 1; ext x_1; ring
      _ = ↑(hg.τ y) * ∑ x : Config N, ∑ x_1 : Config N, (hg.w y).ofLp x * (hg.w y).ofLp x_1 *
          hessian_free_energy N H (std_basis N x) (std_basis N x_1) := by
          rw [Finset.mul_sum]

private lemma affineIBP_measurable_hessian_std_basis
    (σ τ : Config N) :
    Measurable
      (fun H : EnergySpace N =>
        hessian_free_energy N H
          (std_basis N σ) (std_basis N τ)) := by
  simp_rw [hessian_free_energy]
  apply Measurable.mul measurable_const
  apply Measurable.sub
  · exact Finset.measurable_sum _ fun x _ => by
      apply Measurable.mul _ measurable_const
      apply Measurable.mul _ measurable_const
      exact
        (contDiff_gibbs_pmf
          (N := N) (σ := x)).continuous.measurable
  · apply Measurable.mul
    · exact Finset.measurable_sum _ fun x _ => by
        apply Measurable.mul
        · exact
            (contDiff_gibbs_pmf
              (N := N) (σ := x)).continuous.measurable
        · exact measurable_const
    · exact Finset.measurable_sum _ fun x _ => by
        apply Measurable.mul
        · exact
            (contDiff_gibbs_pmf
              (N := N) (σ := x)).continuous.measurable
        · exact measurable_const

private lemma affineIBP_abs_hessian_std_basis_le
    (H : EnergySpace N) (σ τ : Config N) :
    |hessian_free_energy N H
        (std_basis N σ) (std_basis N τ)| ≤
      1 / (N : ℝ) := by
  classical
  have hσ0 :
      0 ≤ gibbs_pmf N H σ :=
    gibbs_pmf_nonneg N H σ
  have hτ0 :
      0 ≤ gibbs_pmf N H τ :=
    gibbs_pmf_nonneg N H τ
  have hσ1 :
      gibbs_pmf N H σ ≤ 1 :=
    gibbs_pmf_le_one N H σ
  have hτ1 :
      gibbs_pmf N H τ ≤ 1 :=
    gibbs_pmf_le_one N H τ
  by_cases hστ : σ = τ
  · subst τ
    simp [hessian_free_energy, std_basis]
    have hp :
        0 ≤ gibbs_pmf N H σ -
          gibbs_pmf N H σ * gibbs_pmf N H σ := by
      nlinarith
    rw [abs_of_nonneg hp]
    have hN0 :
        (0 : ℝ) ≤ (N : ℝ) :=
      Nat.cast_nonneg N
    have hp1 :
        gibbs_pmf N H σ -
            gibbs_pmf N H σ * gibbs_pmf N H σ
          ≤ 1 := by
      nlinarith
    calc
      (N : ℝ)⁻¹ *
          (gibbs_pmf N H σ -
            gibbs_pmf N H σ * gibbs_pmf N H σ)
        ≤ (N : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hp1
            (inv_nonneg.mpr hN0)
      _ = (N : ℝ)⁻¹ := mul_one _
  · simp [hessian_free_energy, std_basis, hστ]
    rw [abs_of_nonneg hσ0, abs_of_nonneg hτ0]
    calc
      (N : ℝ)⁻¹ *
          (gibbs_pmf N H σ * gibbs_pmf N H τ)
        ≤ (N : ℝ)⁻¹ * 1 := by
          have hN0 :
              (0 : ℝ) ≤ (N : ℝ) :=
            Nat.cast_nonneg N
          exact
            mul_le_mul_of_nonneg_left
              (by nlinarith)
              (inv_nonneg.mpr hN0)
      _ = (N : ℝ)⁻¹ := by
        ring

private lemma
    affineIBP_integrable_kernel_hessian_trace
    (K : Config N → Config N → ℝ)
    (a b : ℝ) (field : EnergySpace N) :
    Integrable
      (fun w =>
        ∑ σ : Config N, ∑ τ : Config N,
          K σ τ *
            hessian_free_energy N
              (a • sk.U w + b • sim.V w + field)
              (std_basis N σ) (std_basis N τ))
      ℙ := by
  have hH_meas :
      Measurable
        (fun w =>
          a • sk.U w + b • sim.V w + field) := by
    exact
      ((sk.hU.repr_measurable.const_smul a).add
        (sim.hV.repr_measurable.const_smul b)).add
        measurable_const
  apply MeasureTheory.integrable_finset_sum
  intro σ _
  apply MeasureTheory.integrable_finset_sum
  intro τ _
  refine
    MeasureTheory.Integrable.const_mul ?_ (K σ τ)
  refine
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (1 / (N : ℝ)))
      ?_ ?_
  · exact
      ((affineIBP_measurable_hessian_std_basis
        (N := N) σ τ).comp hH_meas).aestronglyMeasurable
  · filter_upwards with w
    exact
      affineIBP_abs_hessian_std_basis_le
        (N := N)
        (a • sk.U w + b • sim.V w + field)
        σ τ

/-- Gaussian integration by parts for an affine combination of two independent Gaussian
Hamiltonians, expressed in the canonical configuration basis. -/
lemma independent_gaussian_affine_ibp_reproved
    (hIndep :
      IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ
        (fun H : EnergySpace N =>
          free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field)
        (a' • sk.U w + b' • sim.V w)
      ∂ℙ) =
      (a * a') *
        ∫ w,
          (∑ σ : Config N, ∑ τ : Config N,
            sk_cov_kernel N β σ τ *
              hessian_free_energy N
                (a • sk.U w + b • sim.V w + field)
                (std_basis N σ) (std_basis N τ))
        ∂ℙ +
      (b * b') *
        ∫ w,
          (∑ σ : Config N, ∑ τ : Config N,
            simple_cov_kernel N β
                (fun x => q * x) σ τ *
              hessian_free_energy N
                (a • sk.U w + b • sim.V w + field)
                (std_basis N σ) (std_basis N τ))
        ∂ℙ := by
  classical
  have hmain :=
    affineIBP_joint_gaussian_affine_ibp_eigenbasis
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim)
      hIndep a b a' b' field
  rw [hmain]
  have hpoint (w : Ω) :
      (∑ i :
          (isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) hIndep).ι,
        (((isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) hIndep).τ i :
            NNReal) : ℝ) *
          hessian_free_energy N
            (a • sk.U w + b • sim.V w + field)
            (affineIBP_jointAffineCLM
              (N := N) a b
              ((isGaussianHilbert_UV
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) hIndep).w i))
            (affineIBP_jointAffineCLM
              (N := N) a' b'
              ((isGaussianHilbert_UV
                (N := N) (β := β) (h := h) (q := q)
                (sk := sk) (sim := sim) hIndep).w i))) =
        (a * a') *
          (∑ σ : Config N, ∑ τ : Config N,
            sk_cov_kernel N β σ τ *
              hessian_free_energy N
                (a • sk.U w + b • sim.V w + field)
                (std_basis N σ) (std_basis N τ)) +
        (b * b') *
          (∑ σ : Config N, ∑ τ : Config N,
            simple_cov_kernel N β
                (fun x => q * x) σ τ *
              hessian_free_energy N
                (a • sk.U w + b • sim.V w + field)
                (std_basis N σ) (std_basis N τ)) := by
    rw [
      affineIBP_joint_trace_split
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim)
        hIndep a b a' b'
        (a • sk.U w + b • sim.V w + field)
    ]
    rw [
      affineIBP_gaussian_hessian_trace_eq_std_basis
        (N := N) sk.U sk.hU
        (a • sk.U w + b • sim.V w + field)
    ]
    rw [
      affineIBP_gaussian_hessian_trace_eq_std_basis
        (N := N) sim.V sim.hV
        (a • sk.U w + b • sim.V w + field)
    ]
    simp_rw [sk.cov_eq, sim.cov_eq]
  rw [
    MeasureTheory.integral_congr_ae
      (ae_of_all _ hpoint)
  ]
  have hsk : Integrable
      (fun w =>
        ∑ σ : Config N, ∑ τ : Config N,
          sk_cov_kernel N β σ τ *
            hessian_free_energy N
              (a • sk.U w + b • sim.V w + field)
              (std_basis N σ) (std_basis N τ))
      ℙ :=
    affineIBP_integrable_kernel_hessian_trace
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim)
      (sk_cov_kernel N β) a b field
  have hsim : Integrable
      (fun w =>
        ∑ σ : Config N, ∑ τ : Config N,
          simple_cov_kernel N β
              (fun x => q * x) σ τ *
            hessian_free_energy N
              (a • sk.U w + b • sim.V w + field)
              (std_basis N σ) (std_basis N τ))
      ℙ :=
    affineIBP_integrable_kernel_hessian_trace
      (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim)
      (simple_cov_kernel N β (fun x => q * x))
      a b field
  rw [
    MeasureTheory.integral_add
      (hsk.const_mul (a * a'))
      (hsim.const_mul (b * b')),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul
  ]

end JointDisorder

end GeneralizedLatala
end SpinGlass
