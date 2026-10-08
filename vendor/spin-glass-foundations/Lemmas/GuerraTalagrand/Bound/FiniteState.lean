module

public import Lemmas.GuerraTalagrand.Bound.Basic
public import Lemmas.SmartPath.IndependentEndpoint

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open PhysLean.Probability.GaussianIBP
open scoped ContDiff

set_option autoImplicit false

namespace SpinGlass.AT

/-- Euclidean space of real fields indexed by a finite state type. -/
abbrev GTStateSpace (S : Type*) [Fintype S] := EuclideanSpace ℝ S

/-- A finite-state partition function with a fixed deterministic potential. -/
noncomputable def gtStatePartition
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) : ℝ :=
  ∑ ξ : S, Real.exp (H ξ + V ξ)

/-- The Gibbs probability associated with `gtStatePartition`. -/
noncomputable def gtStateGibbs
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) (ξ : S) : ℝ :=
  Real.exp (H ξ + V ξ) / gtStatePartition V H

/-- The finite-state log-partition function. -/
noncomputable def gtStateLogPartition
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) : ℝ :=
  Real.log (gtStatePartition V H)

lemma gtStatePartition_pos
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    0 < gtStatePartition V H := by
  classical
  exact Finset.sum_pos' (fun ξ _ => (Real.exp_pos (H ξ + V ξ)).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩

lemma gtStatePartition_ne_zero
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    gtStatePartition V H ≠ 0 :=
  (gtStatePartition_pos V H).ne'

lemma gtStateGibbs_nonneg
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    0 ≤ gtStateGibbs V H ξ := by
  exact div_nonneg (Real.exp_pos _).le (gtStatePartition_pos V H).le

lemma gtStateGibbs_le_one
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    gtStateGibbs V H ξ ≤ 1 := by
  classical
  unfold gtStateGibbs gtStatePartition
  rw [div_le_one (Finset.sum_pos' (fun η _ => (Real.exp_pos _).le)
    ⟨ξ, Finset.mem_univ _, Real.exp_pos _⟩)]
  exact Finset.single_le_sum
    (f := fun η : S => Real.exp (H η + V η))
    (fun η _ => (Real.exp_pos _).le) (Finset.mem_univ ξ)

lemma sum_gtStateGibbs
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    ∑ ξ : S, gtStateGibbs V H ξ = 1 := by
  classical
  rw [show (∑ ξ : S, gtStateGibbs V H ξ) =
      (∑ ξ : S, Real.exp (H ξ + V ξ)) / gtStatePartition V H by
    simp only [gtStateGibbs, Finset.sum_div]]
  exact div_self (gtStatePartition_ne_zero V H)

lemma contDiff_gtStatePartition
    {S : Type*} [Fintype S] (V : S → ℝ) :
    ContDiff ℝ ∞ (gtStatePartition V) := by
  classical
  unfold gtStatePartition
  fun_prop

lemma contDiff_gtStateLogPartition
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) :
    ContDiff ℝ ∞ (gtStateLogPartition V) := by
  unfold gtStateLogPartition
  exact (contDiff_gtStatePartition V).log (fun H => gtStatePartition_ne_zero V H)

lemma contDiff_gtStateGibbs
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) (ξ : S) :
    ContDiff ℝ ∞ (fun H : GTStateSpace S => gtStateGibbs V H ξ) := by
  unfold gtStateGibbs
  apply ContDiff.div
  · fun_prop
  · exact contDiff_gtStatePartition V
  · exact fun H => gtStatePartition_ne_zero V H

lemma fderiv_gtStatePartition_apply
    {S : Type*} [Fintype S]
    (V : S → ℝ) (H K : GTStateSpace S) :
    fderiv ℝ (gtStatePartition V) H K =
      ∑ ξ : S, Real.exp (H ξ + V ξ) * K ξ := by
  classical
  unfold gtStatePartition
  rw [fderiv_fun_sum]
  · simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro ξ _
    have hd : HasFDerivAt
        (fun H' : GTStateSpace S => Real.exp (H' ξ + V ξ))
        (Real.exp (H ξ + V ξ) •
          (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ)) H :=
      (((EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ).hasFDerivAt
        ).add_const (V ξ)).exp
    have hf := hd.fderiv
    have happ := congrArg (fun L : GTStateSpace S →L[ℝ] ℝ => L K) hf
    simpa using happ
  · intro ξ _
    fun_prop

lemma fderiv_gtStateLogPartition_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) :
    fderiv ℝ (gtStateLogPartition V) H K =
      ∑ ξ : S, gtStateGibbs V H ξ * K ξ := by
  classical
  have hlog := ((contDiff_gtStatePartition V).differentiable (by simp)
    ).differentiableAt.hasFDerivAt.log
    (gtStatePartition_ne_zero V H)
  have hf := hlog.fderiv
  change fderiv ℝ (fun x : GTStateSpace S => Real.log (gtStatePartition V x)) H K = _
  rw [hf]
  simp only [ContinuousLinearMap.smul_apply]
  rw [fderiv_gtStatePartition_apply]
  unfold gtStateGibbs
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  field_simp [gtStatePartition_ne_zero V H]

lemma fderiv_gtStateGibbs_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) (ξ : S) :
    fderiv ℝ (fun H : GTStateSpace S => gtStateGibbs V H ξ) H K =
      gtStateGibbs V H ξ *
        (K ξ - ∑ η : S, gtStateGibbs V H η * K η) := by
  classical
  have hlin : HasFDerivAt (fun H : GTStateSpace S => H ξ + V ξ)
      (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ) H :=
    (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ).hasFDerivAt.add_const (V ξ)
  have hlog : HasFDerivAt (gtStateLogPartition V)
      (fderiv ℝ (gtStateLogPartition V) H) H :=
    ((contDiff_gtStateLogPartition V).differentiable (by simp)
      ).differentiableAt.hasFDerivAt
  have hexp := (hlin.sub hlog).exp
  have hfun : (fun H : GTStateSpace S => gtStateGibbs V H ξ) =
      fun H => Real.exp (H ξ + V ξ - gtStateLogPartition V H) := by
    funext H'
    unfold gtStateGibbs gtStateLogPartition
    rw [Real.exp_sub, Real.exp_log (gtStatePartition_pos V H')]
  rw [hfun]
  have heq := congrArg (fun L : GTStateSpace S →L[ℝ] ℝ => L K) hexp.fderiv
  change (fderiv ℝ (fun H' : GTStateSpace S =>
      Real.exp (H' ξ + V ξ - gtStateLogPartition V H')) H) K = _ at heq
  rw [heq]
  have happ :
      (((Real.exp (H ξ + V ξ - gtStateLogPartition V H)) •
        ((EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ) -
          fderiv ℝ (gtStateLogPartition V) H)) : GTStateSpace S →L[ℝ] ℝ) K =
      gtStateGibbs V H ξ *
        (K ξ - ∑ η : S, gtStateGibbs V H η * K η) := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
    rw [fderiv_gtStateLogPartition_apply]
    have hfunH := congrFun hfun H
    rw [← hfunH]
    simp
  exact happ

lemma abs_fderiv_gtStateGibbs_apply_le
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) (ξ : S) :
    |fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H K| ≤
      2 * ‖K‖ := by
  classical
  rw [fderiv_gtStateGibbs_apply]
  have hξ0 := gtStateGibbs_nonneg V H ξ
  have hξ1 := gtStateGibbs_le_one V H ξ
  have hK (η : S) : |K η| ≤ ‖K‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K η
  have havg : |∑ η : S, gtStateGibbs V H η * K η| ≤ ‖K‖ := by
    calc
      |∑ η : S, gtStateGibbs V H η * K η| ≤
          ∑ η : S, |gtStateGibbs V H η * K η| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ η : S, gtStateGibbs V H η * |K η| := by
        apply Finset.sum_congr rfl
        intro η _
        rw [abs_mul, abs_of_nonneg (gtStateGibbs_nonneg V H η)]
      _ ≤ ∑ η : S, gtStateGibbs V H η * ‖K‖ := by
        exact Finset.sum_le_sum fun η _ =>
          mul_le_mul_of_nonneg_left (hK η) (gtStateGibbs_nonneg V H η)
      _ = ‖K‖ := by rw [← Finset.sum_mul, sum_gtStateGibbs, one_mul]
  calc
    |gtStateGibbs V H ξ *
        (K ξ - ∑ η : S, gtStateGibbs V H η * K η)| =
        gtStateGibbs V H ξ *
          |K ξ - ∑ η : S, gtStateGibbs V H η * K η| := by
      rw [abs_mul, abs_of_nonneg hξ0]
    _ ≤ 1 * (|K ξ| + |∑ η : S, gtStateGibbs V H η * K η|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ 2 * ‖K‖ := by nlinarith [hK ξ, havg, norm_nonneg K]

lemma norm_fderiv_gtStateGibbs_le_two
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    ‖fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro K
  simpa [Real.norm_eq_abs] using abs_fderiv_gtStateGibbs_apply_le V H K ξ

lemma norm_fderiv_gtStateLogPartition_le_one
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    ‖fderiv ℝ (gtStateLogPartition V) H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro K
  rw [fderiv_gtStateLogPartition_apply]
  have hK (ξ : S) : |K ξ| ≤ ‖K‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K ξ
  rw [Real.norm_eq_abs]
  calc
    |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤
        ∑ ξ : S, |gtStateGibbs V H ξ * K ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ξ : S, gtStateGibbs V H ξ * |K ξ| := by
      apply Finset.sum_congr rfl
      intro ξ _
      rw [abs_mul, abs_of_nonneg (gtStateGibbs_nonneg V H ξ)]
    _ ≤ ∑ ξ : S, gtStateGibbs V H ξ * ‖K‖ := by
      exact Finset.sum_le_sum fun ξ _ =>
        mul_le_mul_of_nonneg_left (hK ξ) (gtStateGibbs_nonneg V H ξ)
    _ ≤ 1 * ‖K‖ := by rw [← Finset.sum_mul, sum_gtStateGibbs, one_mul]

/-- Finite log-sum-exp has at most linear growth in its field. -/
noncomputable def hasModerateGrowth_gtStateLogPartition
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) :
    HasModerateGrowth (gtStateLogPartition V) := by
  classical
  let D : ℝ := ∑ ξ : S, |V ξ|
  let C : ℝ := Real.log (Fintype.card S : ℝ) + D + 1
  have hcard : 0 < Fintype.card S := Fintype.card_pos
  have hcard1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast hcard
  have hlog0 : 0 ≤ Real.log (Fintype.card S : ℝ) := Real.log_nonneg hcard1
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun ξ _ => abs_nonneg _
  refine ⟨C, 1, by dsimp [C]; linarith, ?_, ?_⟩
  · intro H
    have hH (ξ : S) : |H ξ| ≤ ‖H‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) H ξ
    let ξ₀ : S := Classical.choice inferInstance
    have hterm : Real.exp (H ξ₀ + V ξ₀) ≤ gtStatePartition V H := by
      unfold gtStatePartition
      exact Finset.single_le_sum
        (f := fun ξ : S => Real.exp (H ξ + V ξ))
        (fun ξ _ => (Real.exp_pos _).le) (Finset.mem_univ ξ₀)
    have hlower : -(‖H‖ + D) ≤ gtStateLogPartition V H := by
      have hlogterm := Real.log_le_log (Real.exp_pos _) hterm
      rw [Real.log_exp] at hlogterm
      have hV : |V ξ₀| ≤ D := Finset.single_le_sum
        (fun ξ _ => abs_nonneg (V ξ)) (Finset.mem_univ ξ₀)
      unfold gtStateLogPartition
      linarith [neg_le_abs (H ξ₀), neg_le_abs (V ξ₀), hH ξ₀]
    have hupperZ : gtStatePartition V H ≤
        (Fintype.card S : ℝ) * Real.exp (‖H‖ + D) := by
      unfold gtStatePartition
      calc
        (∑ ξ : S, Real.exp (H ξ + V ξ)) ≤
            ∑ _ξ : S, Real.exp (‖H‖ + D) := by
          apply Finset.sum_le_sum
          intro ξ _
          apply Real.exp_le_exp.mpr
          have hV : |V ξ| ≤ D := Finset.single_le_sum
            (fun η _ => abs_nonneg (V η)) (Finset.mem_univ ξ)
          linarith [le_abs_self (H ξ), le_abs_self (V ξ), hH ξ]
        _ = (Fintype.card S : ℝ) * Real.exp (‖H‖ + D) := by simp
    have hupper : gtStateLogPartition V H ≤
        Real.log (Fintype.card S : ℝ) + ‖H‖ + D := by
      have hlog := Real.log_le_log (gtStatePartition_pos V H) hupperZ
      have hcard0 : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
      rw [Real.log_mul hcard0 (Real.exp_ne_zero _), Real.log_exp] at hlog
      simpa [gtStateLogPartition, add_assoc] using hlog
    have habs : |gtStateLogPartition V H| ≤
        Real.log (Fintype.card S : ℝ) + D + ‖H‖ := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |gtStateLogPartition V H| ≤
          Real.log (Fintype.card S : ℝ) + D + ‖H‖ := habs
      _ ≤ C * (1 + ‖H‖) ^ 1 := by
        dsimp [C]
        rw [pow_one]
        nlinarith [norm_nonneg H]
  · intro H
    calc
      ‖fderiv ℝ (gtStateLogPartition V) H‖ ≤ 1 :=
        norm_fderiv_gtStateLogPartition_le_one V H
      _ ≤ C * (1 + ‖H‖) ^ 1 := by
        dsimp [C]
        rw [pow_one]
        nlinarith [norm_nonneg H]

/-- Affine pullback preserves moderate growth for a finite log-partition. -/
noncomputable def hasModerateGrowth_gtStateLogPartition_comp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H₀ : GTStateSpace S) :
    HasModerateGrowth (fun z => gtStateLogPartition V (L z + H₀)) := by
  let base := hasModerateGrowth_gtStateLogPartition V
  let C : ℝ := (base.C + 1) * (1 + ‖L‖ + ‖H₀‖) + 1
  refine ⟨C, 1, by
    dsimp [C]
    nlinarith [base.Cpos, norm_nonneg L, norm_nonneg H₀], ?_, ?_⟩
  · intro z
    have hb := base.F_bound (L z + H₀)
    have hnorm : 1 + ‖L z + H₀‖ ≤
        (1 + ‖L‖ + ‖H₀‖) * (1 + ‖z‖) := by
      have hL := L.le_opNorm z
      have hadd := norm_add_le (L z) H₀
      nlinarith [norm_nonneg L, norm_nonneg H₀, norm_nonneg z]
    rw [show base.m = 1 by rfl, pow_one] at hb
    rw [pow_one]
    calc
      |gtStateLogPartition V (L z + H₀)| ≤ base.C * (1 + ‖L z + H₀‖) := hb
      _ ≤ base.C * ((1 + ‖L‖ + ‖H₀‖) * (1 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hnorm base.Cpos.le
      _ ≤ C * (1 + ‖z‖) := by
        dsimp [C]
        nlinarith [base.Cpos, norm_nonneg L, norm_nonneg H₀, norm_nonneg z]
  · intro z
    have hg : HasFDerivAt (gtStateLogPartition V)
        (fderiv ℝ (gtStateLogPartition V) (L z + H₀)) (L z + H₀) :=
      ((contDiff_gtStateLogPartition V).differentiable (by simp)
        ).differentiableAt.hasFDerivAt
    have hcomp := hg.comp z (L.hasFDerivAt.add_const H₀)
    have hf := hcomp.fderiv
    change fderiv ℝ (fun z => gtStateLogPartition V (L z + H₀)) z = _ at hf
    rw [hf, pow_one]
    calc
      ‖(fderiv ℝ (gtStateLogPartition V) (L z + H₀)).comp L‖ ≤
          ‖fderiv ℝ (gtStateLogPartition V) (L z + H₀)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖L‖ := by
        gcongr
        exact norm_fderiv_gtStateLogPartition_le_one V (L z + H₀)
      _ ≤ C * (1 + ‖z‖) := by
        have hbase : 1 ≤ base.C + 1 := by linarith [base.Cpos]
        have hfactor : 0 ≤ 1 + ‖L‖ + ‖H₀‖ := by positivity
        have hprod : 1 + ‖L‖ + ‖H₀‖ ≤
            (base.C + 1) * (1 + ‖L‖ + ‖H₀‖) := by
          simpa [one_mul] using mul_le_mul_of_nonneg_right hbase hfactor
        have hLC : ‖L‖ ≤ C := by
          dsimp [C]
          linarith [norm_nonneg H₀]
        have hC0 : 0 ≤ C := by
          dsimp [C]
          positivity
        calc
          1 * ‖L‖ = ‖L‖ := one_mul _
          _ ≤ C := hLC
          _ ≤ C * (1 + ‖z‖) := by
            simpa [mul_one] using
              mul_le_mul_of_nonneg_left
                (show 1 ≤ 1 + ‖z‖ by linarith [norm_nonneg z]) hC0

/-- A Gibbs coordinate composed with an affine field has uniform moderate growth. -/
noncomputable def hasModerateGrowth_gtStateGibbs_comp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H₀ : GTStateSpace S) (ξ : S) :
    HasModerateGrowth (fun z => gtStateGibbs V (L z + H₀) ξ) := by
  let C : ℝ := 2 * (‖L‖ + 1)
  refine ⟨C, 0, by dsimp [C]; positivity, ?_, ?_⟩
  · intro z
    rw [pow_zero, mul_one]
    have h0 := gtStateGibbs_nonneg V (L z + H₀) ξ
    rw [abs_of_nonneg h0]
    exact (gtStateGibbs_le_one V (L z + H₀) ξ).trans (by
      dsimp [C]
      nlinarith [norm_nonneg L])
  · intro z
    have hg : HasFDerivAt
        (fun H : GTStateSpace S => gtStateGibbs V H ξ)
        (fderiv ℝ (fun H : GTStateSpace S => gtStateGibbs V H ξ) (L z + H₀))
        (L z + H₀) :=
      ((contDiff_gtStateGibbs V ξ).differentiable (by simp)
        ).differentiableAt.hasFDerivAt
    have haff : HasFDerivAt (fun z' => L z' + H₀) L z :=
      L.hasFDerivAt.add_const H₀
    have hcomp := hg.comp z haff
    have hf := hcomp.fderiv
    change fderiv ℝ (fun z => gtStateGibbs V (L z + H₀) ξ) z = _ at hf
    rw [hf]
    rw [pow_zero, mul_one]
    apply ContinuousLinearMap.opNorm_le_bound _ (by
      dsimp [C]
      positivity)
    intro K
    have hder := abs_fderiv_gtStateGibbs_apply_le V (L z + H₀) (L K) ξ
    calc
      ‖(fderiv ℝ (fun H : GTStateSpace S => gtStateGibbs V H ξ) (L z + H₀)) (L K)‖ =
          |(fderiv ℝ (fun H : GTStateSpace S => gtStateGibbs V H ξ)
            (L z + H₀)) (L K)| := Real.norm_eq_abs _
      _ ≤ 2 * ‖L K‖ := hder
      _ ≤ 2 * (‖L‖ * ‖K‖) := by gcongr; exact L.le_opNorm K
      _ ≤ C * ‖K‖ := by
        dsimp [C]
        nlinarith [norm_nonneg L, norm_nonneg K]

/-- Hessian of finite-state log-sum-exp as a Gibbs covariance. -/
lemma second_fderiv_gtStateLogPartition_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K L : GTStateSpace S) :
    fderiv ℝ (fun H' : GTStateSpace S =>
        fderiv ℝ (gtStateLogPartition V) H') H K L =
      (∑ ξ : S, gtStateGibbs V H ξ * K ξ * L ξ) -
        (∑ ξ : S, gtStateGibbs V H ξ * K ξ) *
          (∑ η : S, gtStateGibbs V H η * L η) := by
  classical
  have hfirst : (fun H' : GTStateSpace S =>
      fderiv ℝ (gtStateLogPartition V) H') =
      fun H' => ∑ ξ : S,
        (gtStateGibbs V H' ξ) • EuclideanSpace.proj ξ := by
    funext H'
    ext K'
    simp [fderiv_gtStateLogPartition_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  rw [hfirst, fderiv_fun_sum]
  · simp only [ContinuousLinearMap.sum_apply]
    have hterm (ξ : S) :
        ((fderiv ℝ (fun H' : GTStateSpace S =>
            gtStateGibbs V H' ξ • EuclideanSpace.proj ξ) H) K) L =
          (fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H K) * L ξ := by
      have hg : HasFDerivAt
          (fun H' : GTStateSpace S => gtStateGibbs V H' ξ)
          (fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H) H :=
        ((contDiff_gtStateGibbs V ξ).differentiable (by simp)
          ).differentiableAt.hasFDerivAt
      have hd := hg.smul_const (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ)
      rw [hd.fderiv]
      simp
    simp_rw [hterm, fderiv_gtStateGibbs_apply, mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib]
    have hpull :
        (∑ ξ : S, gtStateGibbs V H ξ *
            (∑ η : S, gtStateGibbs V H η * K η) * L ξ) =
          (∑ η : S, gtStateGibbs V H η * K η) *
            (∑ ξ : S, gtStateGibbs V H ξ * L ξ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    rw [hpull]
  · intro ξ _
    have hg : HasFDerivAt
        (fun H' : GTStateSpace S => gtStateGibbs V H' ξ)
        (fderiv ℝ (fun H' : GTStateSpace S => gtStateGibbs V H' ξ) H) H :=
      ((contDiff_gtStateGibbs V ξ).differentiable (by simp)
        ).differentiableAt.hasFDerivAt
    exact (hg.smul_const
      (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ)).differentiableAt

/-- Coordinatewise Stein identity for the standard product Gaussian. -/
lemma gaussianProduct_stein
    {I : Type*} [Fintype I] (i : I)
    (F : EuclideanSpace ℝ I → ℝ)
    (hFdiff : ContDiff ℝ 1 F) (hFgrowth : HasModerateGrowth F) :
    (∫ z, z i * F (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z, (fderiv ℝ F (WithLp.toLp 2 z))
          ((EuclideanSpace.basisFun I ℝ) i)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
  classical
  let pull : (I → ℝ) → EuclideanSpace ℝ I := fun z => WithLp.toLp 2 z
  letI : MeasureSpace (I → ℝ) :=
    ⟨Measure.pi (fun _ : I => gaussianReal 0 1)⟩
  letI : IsProbabilityMeasure (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    inferInstance
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi (fun _ : I => gaussianReal 0 1)) =
        gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      change iIndepFun (fun j (z : I → ℝ) => z j)
        (Measure.pi (fun _ : I => gaussianReal 0 1))
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
    }
  have hibp :=
    PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_integration_by_parts_hilbert_std
      hg (fun _ => rfl) ((EuclideanSpace.basisFun I ℝ) i) hFdiff hFgrowth
  have hinner (z : I → ℝ) :
      inner ℝ (pull z) ((EuclideanSpace.basisFun I ℝ) i) = z i := by
    change inner ℝ (pull z) (EuclideanSpace.single i 1) = z i
    rw [EuclideanSpace.inner_single_right]
    simp [pull]
  simp_rw [hinner] at hibp
  change (∫ z, z i * F (WithLp.toLp 2 z)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
    ∫ z, (fderiv ℝ F (WithLp.toLp 2 z))
      ((EuclideanSpace.basisFun I ℝ) i)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) at hibp
  exact hibp

/-- Directional Stein identity for the standard product Gaussian. -/
lemma gaussianProduct_stein_inner
    {I : Type*} [Fintype I] (a : EuclideanSpace ℝ I)
    (F : EuclideanSpace ℝ I → ℝ)
    (hFdiff : ContDiff ℝ 1 F) (hFgrowth : HasModerateGrowth F) :
    (∫ z, inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a *
          F (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z, (fderiv ℝ F (WithLp.toLp 2 z)) a
        ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
  classical
  let pull : (I → ℝ) → EuclideanSpace ℝ I := fun z => WithLp.toLp 2 z
  letI : MeasureSpace (I → ℝ) :=
    ⟨Measure.pi (fun _ : I => gaussianReal 0 1)⟩
  letI : IsProbabilityMeasure (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    inferInstance
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi (fun _ : I => gaussianReal 0 1)) =
        gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      change iIndepFun (fun j (z : I → ℝ) => z j)
        (Measure.pi (fun _ : I => gaussianReal 0 1))
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
    }
  have hibp :=
    PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_integration_by_parts_hilbert_std
      hg (fun _ => rfl) a hFdiff hFgrowth
  change (∫ z, inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a *
        F (WithLp.toLp 2 z)
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
    ∫ z, (fderiv ℝ F (WithLp.toLp 2 z)) a
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) at hibp
  exact hibp

/-- A directional Gaussian coordinate times a moderate-growth test function is integrable. -/
lemma integrable_inner_mul_gaussianProduct
    {I : Type*} [Fintype I] (a : EuclideanSpace ℝ I)
    (F : EuclideanSpace ℝ I → ℝ)
    (hFdiff : ContDiff ℝ 1 F) (hFgrowth : HasModerateGrowth F) :
    Integrable (fun z : I → ℝ =>
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a *
        F (WithLp.toLp 2 z))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  classical
  let pull : (I → ℝ) → EuclideanSpace ℝ I := fun z => WithLp.toLp 2 z
  letI : MeasureSpace (I → ℝ) :=
    ⟨Measure.pi (fun _ : I => gaussianReal 0 1)⟩
  letI : IsProbabilityMeasure (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    inferInstance
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi (fun _ : I => gaussianReal 0 1)) =
        gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      change iIndepFun (fun j (z : I → ℝ) => z j)
        (Measure.pi (fun _ : I => gaussianReal 0 1))
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
    }
  have hi (i : I) : Integrable (fun z : I → ℝ =>
      (a i) * (z i * F (WithLp.toLp 2 z)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hbase := integrable_coord_mul_F hg hFdiff hFgrowth i
    have hcoord (z : I → ℝ) : coord hg.w pull i z = z i := by
      change inner ℝ (pull z) (EuclideanSpace.single i 1) = z i
      rw [EuclideanSpace.inner_single_right]
      simp [pull]
    simp_rw [hcoord] at hbase
    exact hbase.const_mul (a i)
  have hsum : Integrable (fun z : I → ℝ =>
      ∑ i : I, (a i) * (z i * F (WithLp.toLp 2 z)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    integrable_finset_sum _ (fun i _ => hi i)
  convert hsum using 1
  funext z
  have hinner : inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I) a =
      ∑ i : I, z i * a i := by
    rw [Aux.inner_decomp (w := EuclideanSpace.basisFun I ℝ)]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ I)
        (EuclideanSpace.single i 1) *
      inner ℝ a (EuclideanSpace.single i 1) = z i * a i
    rw [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
    simp
  rw [hinner, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Moderate-growth functions are integrable under the standard product Gaussian. -/
lemma integrable_moderate_gaussianProduct
    {I : Type*} [Fintype I]
    (F : EuclideanSpace ℝ I → ℝ)
    (hFdiff : ContDiff ℝ 1 F) (hFgrowth : HasModerateGrowth F) :
    Integrable (fun z => F (WithLp.toLp 2 z))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  classical
  let pull : (I → ℝ) → EuclideanSpace ℝ I := fun z => WithLp.toLp 2 z
  letI : MeasureSpace (I → ℝ) :=
    ⟨Measure.pi (fun _ : I => gaussianReal 0 1)⟩
  letI : IsProbabilityMeasure (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    inferInstance
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi (fun _ : I => gaussianReal 0 1)) = gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      change iIndepFun (fun j (z : I → ℝ) => z j)
        (Measure.pi (fun _ : I => gaussianReal 0 1))
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
    }
  have hint := integrable_F_of_growth hg hFdiff hFgrowth
  change Integrable (fun z => F (WithLp.toLp 2 z))
    (Measure.pi (fun _ : I => gaussianReal 0 1)) at hint
  exact hint

lemma integrable_norm_gaussianProduct
    {I : Type*} [Fintype I] :
    Integrable (fun z : I → ℝ => ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  classical
  let pull : (I → ℝ) → EuclideanSpace ℝ I := fun z => WithLp.toLp 2 z
  letI : MeasureSpace (I → ℝ) :=
    ⟨Measure.pi (fun _ : I => gaussianReal 0 1)⟩
  letI : IsProbabilityMeasure (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    inferInstance
  let hg : IsGaussianHilbert pull := {
    ι := I
    fintype_ι := inferInstance
    w := EuclideanSpace.basisFun I ℝ
    τ := fun _ => 1
    c := fun j z => z j
    c_meas := fun j => measurable_pi_apply j
    c_gauss := fun j => by
      change Measure.map (fun z : I → ℝ => z j)
          (Measure.pi (fun _ : I => gaussianReal 0 1)) = gaussianReal 0 1
      exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) j).map_eq
    c_indep := by
      change iIndepFun (fun j (z : I → ℝ) => z j)
        (Measure.pi (fun _ : I => gaussianReal 0 1))
      exact iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1)
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    repr := by
      funext z
      ext j
      simp [pull, Pi.single_apply]
    }
  have hint := integrable_norm_of_gaussian hg
  change Integrable
    (fun z : I → ℝ => ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖)
    (Measure.pi (fun _ : I => gaussianReal 0 1)) at hint
  exact hint

end SpinGlass.AT
