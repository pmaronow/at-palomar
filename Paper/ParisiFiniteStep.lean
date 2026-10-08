module

public import Targets.Section4Variance
public import Common.Mathlib.Probability.Distributions.Gaussian.ColeHopf

@[expose] public section

/-!
# Actual finite Parisi smoothing on a time slab

The discrete Parisi operator agrees with the independently audited Cole--Hopf
operator at every mass, including mass zero.  The time-dependent slab below
uses the genuine Gaussian recursion and satisfies the nonlinear Parisi PDE;
its spatial derivatives retain the sharp unit-gradient invariant.

This is a finite-step foundation for Propositions 2.1 and 2.2.  Global gluing
and the passage to arbitrary probability measures are separate obligations.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace Paper

open SpinGlass SpinGlass.Targets

theorem parisiStep_eq_coleHopf (m : ℝ) (v : ℝ≥0) {A : ℝ → ℝ}
    (hA : Measurable A) (x : ℝ) :
    parisiStep m (v : ℝ) A x =
      ColeHopfFoundation.ProbabilityTheory.coleHopf m v A x := by
  by_cases hm : m = 0
  · subst m
    simp only [parisiStep, ite_true,
      ColeHopfFoundation.ProbabilityTheory.coleHopf_zero]
    exact integral_comp_sqrt_mul_gaussianReal v hA x
  · simp only [parisiStep, ite_eq_right hm,
      ColeHopfFoundation.ProbabilityTheory.coleHopf_of_ne hm]
    have he := integral_comp_sqrt_mul_gaussianReal v
      (f := fun y => Real.exp (m * A y))
      (Real.measurable_exp.comp (hA.const_mul m)) x
    rw [he]

/-- A genuine backward Parisi step with terminal value the `j`th recursion level. -/
noncomputable def parisiSlabPotential {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) : ℝ :=
  parisiStep m (β ^ 2 * (b - t)) (parisiF s β j) x

noncomputable def parisiSlabGradient {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) : ℝ :=
  stepD1 (parisiF s β j) (parisiFDeriv s β j) m (β ^ 2 * (b - t)) x

noncomputable def parisiSlabHessian {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) : ℝ :=
  stepD2 (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
    m (β ^ 2 * (b - t)) x

theorem hasDerivAt_parisiSlabPotential_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) :
    HasDerivAt (parisiSlabPotential s β j m b t)
      (parisiSlabGradient s β j m b t x) x :=
  hasDerivAt_parisiStep_spatial (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1
    (parisiF_C2_props s β j).1.1 (parisiF_C2_props s β j).1.abs_first_le_one
    m (β ^ 2 * (b - t)) x

theorem hasDerivAt_parisiSlabGradient_spatial {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) :
    HasDerivAt (parisiSlabGradient s β j m b t)
      (parisiSlabHessian s β j m b t x) x :=
  hasDerivAt_parisiStep_spatial_second (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1
    (parisiF_C2_props s β j).2.2 (parisiF_C2_props s β j).1
    m (β ^ 2 * (b - t)) x

theorem parisiSlab_C2 {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (b t : ℝ) :
    HasParisiC2 (parisiSlabPotential s β j m b t)
      (parisiSlabGradient s β j m b t) (parisiSlabHessian s β j m b t) :=
  hasParisiC2_parisiStep_nonneg hm.1 hm.2 (parisiF_C2_props s β j).1
    (parisiF_hasLinearGrowth s β j) (parisiF_measurable s β j)
    (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2

theorem abs_parisiSlabGradient_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (b t x : ℝ) :
    |parisiSlabGradient s β j m b t x| ≤ 1 :=
  (parisiSlab_C2 s β j hm b t).abs_first_le_one x

theorem parisiSlabHessian_nonneg {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (b t x : ℝ) :
    0 ≤ parisiSlabHessian s β j m b t x :=
  (parisiSlab_C2 s β j hm b t).2.2.1 x

theorem parisiSlabHessian_add_sq_le_one {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (b t x : ℝ) :
    parisiSlabHessian s β j m b t x + (parisiSlabGradient s β j m b t x) ^ 2 ≤ 1 := by
  have h := (parisiSlab_C2 s β j hm b t).2.2.2 x
  linarith

theorem hasDerivAt_parisiSlabPotential_time {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (j : ℕ) (m b x : ℝ) {t : ℝ} (ht : t < b) :
    HasDerivAt (fun r => parisiSlabPotential s β j m b r x)
      (-(β ^ 2 / 2) * (parisiSlabHessian s β j m b t x +
        m * (parisiSlabGradient s β j m b t x) ^ 2)) t := by
  have hv : 0 < β ^ 2 * (b - t) := mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr ht)
  have hd := hasDerivAt_parisiStep_variance (parisiF_hasLinearGrowth s β j)
    (parisiF_C2_props s β j).1 (parisiF_measurable s β j)
    (parisiF_C2_props s β j).2.1 (parisiF_C2_props s β j).2.2 m x hv
  convert hd.comp t (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul (β ^ 2)) using 1
  · rfl
  · dsimp [parisiSlabGradient, parisiSlabHessian]
    ring

theorem continuous_parisiSlab {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) {m : ℝ} (hm : 0 ≤ m) (b : ℝ) :
    Continuous (fun p : ℝ × ℝ => parisiSlabPotential s β j m b p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => parisiSlabGradient s β j m b p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => parisiSlabHessian s β j m b p.1 p.2) := by
  have hc := continuous_parisiStep_variance_spatial (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm
  have hmap : Continuous (fun p : ℝ × ℝ => (β ^ 2 * (b - p.1), p.2)) := by fun_prop
  exact ⟨hc.1.comp hmap, hc.2.1.comp hmap, hc.2.2.comp hmap⟩

end Paper
