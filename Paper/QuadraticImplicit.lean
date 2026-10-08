module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Tactic

@[expose] public section

/-! # Smooth parameter dependence of Banach quadratic fixed points

The invertibility hypothesis needed by the implicit-function theorem follows
from the concrete norm of the quadratic linearization. This applies both to
spatial translations and to an affine change of the Gaussian Duhamel operator.
-/

open Filter
open scoped Topology ContDiff

namespace Paper

/-- The operator norm expressed through a generic Banach carrier avoids
competing inherited module instances in concrete nested BCF operator types. -/
noncomputable def bilinearOperatorNorm {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) : ℝ := ‖B‖

def quadraticLinearizationIsInvertible {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) (x : X) : Prop :=
  (1 - (B x + B.flip x)).IsInvertible

theorem one_sub_clm_isInvertible {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (L : X →L[ℝ] X) (hL : ‖L‖ < 1) :
    (1 - L).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hL
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

theorem hasFDerivAt_quadratic_residual {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) (g x : X) :
    HasFDerivAt (fun y => y - g - B y y) (1 - (B x + B.flip x)) x := by
  have hB := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  convert ((hasFDerivAt_id x).sub_const g).sub hB using 1
  ext y
  simp
  abel

/-- A continuous chosen quadratic fixed point inherits the proved smoothness
of its actual forcing and bilinear operator. No smoothness of the selector
or invertibility premise is supplied. -/
theorem contDiffAt_quadratic_fixedPoint_of_invertible {A X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (g v : A → X) (a : A)
    (hB : ContDiffAt ℝ ∞ B a) (hg : ContDiffAt ℝ ∞ g a)
    (hv : ContinuousAt v a) (hfix : ∀ p, v p = g p + B p (v p) (v p))
    (hinvertible : quadraticLinearizationIsInvertible (B a) (v a)) :
    ContDiffAt ℝ ∞ v a := by
  let F : A × X → X := fun p => p.2 - g p.1 - B p.1 p.2 p.2
  have hF : ContDiffAt ℝ ∞ F (a, v a) :=
    (contDiffAt_snd.sub (hg.comp (a, v a) contDiffAt_fst)).sub
      (((hB.comp (a, v a) contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hpartialJoint : HasFDerivAt (fun y => F (a, y))
      (fderiv ℝ F (a, v a) ∘L ContinuousLinearMap.inr ℝ A X) (v a) := by
    convert (hF.differentiableAt (by simp)).hasFDerivAt.comp (v a)
      ((hasFDerivAt_const a (v a)).prodMk (hasFDerivAt_id (v a))) using 1
    all_goals (ext y; rfl)
  have hpartial := hasFDerivAt_quadratic_residual (B a) (g a) (v a)
  have hmap : fderiv ℝ F (a, v a) ∘L ContinuousLinearMap.inr ℝ A X =
      1 - (B a (v a) + (B a).flip (v a)) := hpartialJoint.unique hpartial
  have hinv : (fderiv ℝ F (a, v a) ∘L ContinuousLinearMap.inr ℝ A X).IsInvertible := by
    rw [hmap]
    exact hinvertible
  let ψ := hF.implicitFunction hn hinv
  have hpair : Tendsto (fun p => (p, v p)) (𝓝 a) (𝓝 (a, v a)) :=
    tendsto_id.prodMk_nhds hv.tendsto
  have hevent := hpair.eventually (hF.eventually_apply_eq_iff_implicitFunction hn hinv)
  have hzero (p : A) : F (p, v p) = 0 := by
    dsimp only [F]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr ((hfix p).trans (add_comm _ _)))
  have heq : v =ᶠ[𝓝 a] ψ := by
    filter_upwards [hevent] with p hp
    exact (hp.mp (by rw [hzero p, hzero a])).symm
  exact (hF.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq heq

theorem contDiffAt_quadratic_fixedPoint {A X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (g v : A → X) (a : A)
    (hB : ContDiffAt ℝ ∞ B a) (hg : ContDiffAt ℝ ∞ g a)
    (hv : ContinuousAt v a) (hfix : ∀ p, v p = g p + B p (v p) (v p))
    (hsmall : ‖B a (v a) + (B a).flip (v a)‖ < 1) :
    ContDiffAt ℝ ∞ v a :=
  contDiffAt_quadratic_fixedPoint_of_invertible B g v a hB hg hv hfix
    (one_sub_clm_isInvertible _ hsmall)

/-- The operator smallness condition can be read directly from the norm of
the bilinear correction and the chosen fixed point. -/
theorem norm_quadratic_linearization_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (B : X →L[ℝ] X →L[ℝ] X) (x : X) :
    ‖B x + B.flip x‖ ≤ 2 * ‖B‖ * ‖x‖ := by
  calc
    ‖B x + B.flip x‖ ≤ ‖B x‖ + ‖B.flip x‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖x‖ + ‖B.flip‖ * ‖x‖ := add_le_add (B.le_opNorm x) (B.flip.le_opNorm x)
    _ = 2 * ‖B‖ * ‖x‖ := by rw [ContinuousLinearMap.opNorm_flip]; ring

theorem contDiffAt_quadratic_fixedPoint_of_norm {A X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (g v : A → X) (a : A)
    (hB : ContDiffAt ℝ ∞ B a) (hg : ContDiffAt ℝ ∞ g a)
    (hv : ContinuousAt v a) (hfix : ∀ p, v p = g p + B p (v p) (v p))
    (hsmall : 2 * ‖B a‖ * ‖v a‖ < 1) : ContDiffAt ℝ ∞ v a :=
  contDiffAt_quadratic_fixedPoint B g v a hB hg hv hfix
    ((norm_quadratic_linearization_le (B a) (v a)).trans_lt hsmall)

/-- A smooth local selector exists before any parameter family of solutions
is constructed. Its local uniqueness identity also applies to one-sided
families and varying terminal data. -/
theorem quadratic_local_solution_of_invertible {A X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (g : A → X) (a : A) (x : X)
    (hB : ContDiffAt ℝ ∞ B a) (hg : ContDiffAt ℝ ∞ g a)
    (hfix : x = g a + B a x x)
    (hinvertible : quadraticLinearizationIsInvertible (B a) x) :
    ∃ ψ : A → X, ψ a = x ∧ ContDiffAt ℝ ∞ ψ a ∧
      ∀ᶠ p : A × X in 𝓝 (a, x), p.2 = g p.1 + B p.1 p.2 p.2 ↔ ψ p.1 = p.2 := by
  let F : A × X → X := fun p => p.2 - g p.1 - B p.1 p.2 p.2
  have hF : ContDiffAt ℝ ∞ F (a, x) :=
    (contDiffAt_snd.sub (hg.comp (a, x) contDiffAt_fst)).sub
      (((hB.comp (a, x) contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hpartialJoint : HasFDerivAt (fun y => F (a, y))
      (fderiv ℝ F (a, x) ∘L ContinuousLinearMap.inr ℝ A X) x := by
    convert (hF.differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)) using 1
    all_goals (ext y; rfl)
  have hpartial := hasFDerivAt_quadratic_residual (B a) (g a) x
  have hmap : fderiv ℝ F (a, x) ∘L ContinuousLinearMap.inr ℝ A X =
      1 - (B a x + (B a).flip x) := hpartialJoint.unique hpartial
  have hinv : (fderiv ℝ F (a, x) ∘L ContinuousLinearMap.inr ℝ A X).IsInvertible := by
    rw [hmap]
    exact hinvertible
  refine ⟨hF.implicitFunction hn hinv, hF.implicitFunction_apply_self hn hinv,
    hF.contDiffAt_implicitFunction hn hinv, ?_⟩
  have hzero : F (a, x) = 0 := by
    dsimp only [F]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (hfix.trans (add_comm _ _)))
  filter_upwards [hF.eventually_apply_eq_iff_implicitFunction hn hinv] with p hp
  rw [hzero] at hp
  simpa only [F, sub_sub, sub_eq_zero] using hp

theorem quadratic_local_solution {A X : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (B : A → X →L[ℝ] X →L[ℝ] X) (g : A → X) (a : A) (x : X)
    (hB : ContDiffAt ℝ ∞ B a) (hg : ContDiffAt ℝ ∞ g a)
    (hfix : x = g a + B a x x) (hsmall : 2 * ‖B a‖ * ‖x‖ < 1) :
    ∃ ψ : A → X, ψ a = x ∧ ContDiffAt ℝ ∞ ψ a ∧
      ∀ᶠ p : A × X in 𝓝 (a, x), p.2 = g p.1 + B p.1 p.2 p.2 ↔ ψ p.1 = p.2 :=
  quadratic_local_solution_of_invertible B g a x hB hg hfix
    (one_sub_clm_isInvertible _ ((norm_quadratic_linearization_le (B a) x).trans_lt hsmall))

end Paper
