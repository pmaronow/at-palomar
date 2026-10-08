module

public import Paper.HeatTest
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Genuine smooth compact tests for the weak Parisi equation

All joint continuity, derivative bounds, section derivative identities, and
support statements required by the heat-test argument are derived from a
single `ContDiff ℝ ∞` test with compact support.
-/

open Set MeasureTheory
open scoped Topology ContDiff

namespace Paper

theorem hasDerivAt_test_spatial_fderiv (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun y => φ (t, y)) (fderiv ℝ φ (t, x) (0, 1)) x := by
  have hd := ((contDiff_infty_iff_fderiv.mp hφ).1 (t, x)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  simpa only [id_eq, Function.comp_def] using hd

theorem hasDerivAt_test_time_fderiv (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) (1, 0)) t := by
  have hd := ((contDiff_infty_iff_fderiv.mp hφ).1 (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [id_eq, Function.comp_def] using hd

theorem parisiTestX_eq_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    parisiTestX φ = fun p => fderiv ℝ φ p (0, 1) := by
  funext p
  exact (hasDerivAt_test_spatial_fderiv φ hφ p.1 p.2).deriv

theorem parisiTestT_eq_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    parisiTestT φ = fun p => fderiv ℝ φ p (1, 0) := by
  funext p
  exact (hasDerivAt_test_time_fderiv φ hφ p.1 p.2).deriv

theorem contDiff_parisiTestX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (parisiTestX φ) := by
  rw [parisiTestX_eq_fderiv φ hφ]
  exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const

theorem contDiff_parisiTestT (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (parisiTestT φ) := by
  rw [parisiTestT_eq_fderiv φ hφ]
  exact (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const

theorem parisiTestXX_eq_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    parisiTestXX φ = fun p => fderiv ℝ (parisiTestX φ) p (0, 1) := by
  funext p
  exact (hasDerivAt_test_spatial_fderiv (parisiTestX φ)
    (contDiff_parisiTestX φ hφ) p.1 p.2).deriv

theorem contDiff_parisiTestXX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (parisiTestXX φ) := by
  rw [parisiTestXX_eq_fderiv φ hφ]
  exact (contDiff_infty_iff_fderiv.mp (contDiff_parisiTestX φ hφ)).2.clm_apply contDiff_const

theorem continuous_parisiTestX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (parisiTestX φ) := (contDiff_parisiTestX φ hφ).continuous

theorem continuous_parisiTestT (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (parisiTestT φ) := (contDiff_parisiTestT φ hφ).continuous

theorem continuous_parisiTestXX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (parisiTestXX φ) := (contDiff_parisiTestXX φ hφ).continuous

theorem tsupport_parisiTestX_subset (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    tsupport (parisiTestX φ) ⊆ tsupport φ := by
  rw [parisiTestX_eq_fderiv φ hφ]
  exact tsupport_fderiv_apply_subset ℝ (0, 1)

theorem tsupport_parisiTestT_subset (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    tsupport (parisiTestT φ) ⊆ tsupport φ := by
  rw [parisiTestT_eq_fderiv φ hφ]
  exact tsupport_fderiv_apply_subset ℝ (1, 0)

theorem tsupport_parisiTestXX_subset (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    tsupport (parisiTestXX φ) ⊆ tsupport φ := by
  rw [parisiTestXX_eq_fderiv φ hφ]
  exact (tsupport_fderiv_apply_subset ℝ (0, 1)).trans (tsupport_parisiTestX_subset φ hφ)

theorem hasCompactSupport_parisiTestX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (parisiTestX φ) := by
  rw [parisiTestX_eq_fderiv φ hφ]
  exact hc.fderiv_apply ℝ (0, 1)

theorem hasCompactSupport_parisiTestT (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (parisiTestT φ) := by
  rw [parisiTestT_eq_fderiv φ hφ]
  exact hc.fderiv_apply ℝ (1, 0)

theorem hasCompactSupport_parisiTestXX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (parisiTestXX φ) := by
  rw [parisiTestXX_eq_fderiv φ hφ]
  exact (hasCompactSupport_parisiTestX φ hφ hc).fderiv_apply ℝ (0, 1)

/-- Every fixed-time section of a compactly supported plane test is
compactly supported on the real line. -/
theorem hasCompactSupport_parisiTest_section (φ : ℝ × ℝ → ℝ)
    (hc : HasCompactSupport φ) (t : ℝ) : HasCompactSupport (fun x => φ (t, x)) := by
  obtain ⟨R, hR⟩ := (hc.image continuous_snd).isBounded.exists_norm_le
  have hsub : Function.support (fun x : ℝ => φ (t, x)) ⊆ Icc (-R) R := by
    intro x hx
    have hp : (t, x) ∈ tsupport φ := subset_tsupport φ hx
    have hnorm : ‖x‖ ≤ R := hR x (mem_image_of_mem Prod.snd hp)
    simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hnorm
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hsub isClosed_Icc)

/-- The terminal test against the unbounded `log cosh` datum is genuinely
integrable because its smooth test factor has compact support. -/
theorem integrable_parisiTest_logCosh_terminal (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (t : ℝ) :
    Integrable (fun x : ℝ => φ (t, x) * Real.log (Real.cosh x)) := by
  have hsection : Continuous (fun x : ℝ => φ (t, x)) :=
    hφ.continuous.comp (by fun_prop)
  have hlog : Continuous (fun x : ℝ => Real.log (Real.cosh x)) :=
    (Real.continuous_cosh).log (fun x => ne_of_gt (Real.cosh_pos x))
  exact (hsection.mul hlog).integrable_of_hasCompactSupport
    (hasCompactSupport_parisiTest_section φ hc t).mul_right

/-- A joint bound for the test and all derivatives used by the weak equation. -/
theorem parisiTest_global_bounds (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ M L J K : ℝ, (∀ p, ‖φ p‖ ≤ M) ∧ (∀ p, ‖parisiTestT φ p‖ ≤ L) ∧
      (∀ p, ‖parisiTestX φ p‖ ≤ J) ∧ (∀ p, ‖parisiTestXX φ p‖ ≤ K) := by
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hc
  obtain ⟨L, hL⟩ := (continuous_parisiTestT φ hφ).bounded_above_of_compact_support
    (hasCompactSupport_parisiTestT φ hφ hc)
  obtain ⟨J, hJ⟩ := (continuous_parisiTestX φ hφ).bounded_above_of_compact_support
    (hasCompactSupport_parisiTestX φ hφ hc)
  obtain ⟨K, hK⟩ := (continuous_parisiTestXX φ hφ).bounded_above_of_compact_support
    (hasCompactSupport_parisiTestXX φ hφ hc)
  exact ⟨M, L, J, K, hM, hL, hJ, hK⟩

theorem hasDerivAt_parisiTestX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun y => φ (t, y)) (parisiTestX φ (t, x)) x := by
  rw [parisiTestX_eq_fderiv φ hφ]
  exact hasDerivAt_test_spatial_fderiv φ hφ t x

theorem hasDerivAt_parisiTestT (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun s => φ (s, x)) (parisiTestT φ (t, x)) t := by
  rw [parisiTestT_eq_fderiv φ hφ]
  exact hasDerivAt_test_time_fderiv φ hφ t x

theorem hasDerivAt_parisiTestXX (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (t x : ℝ) :
    HasDerivAt (fun y => parisiTestX φ (t, y)) (parisiTestXX φ (t, x)) x := by
  rw [parisiTestXX_eq_fderiv φ hφ]
  exact hasDerivAt_test_spatial_fderiv (parisiTestX φ) (contDiff_parisiTestX φ hφ) t x

/-- The adjoint heat-test identity with every analytic test hypothesis
discharged by actual smoothness and compact support. -/
theorem integral_heat_adjointSource_compactTest (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (β s x : ℝ) (hβ : β ≠ 0) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, heatSemigroup (β ^ 2 * (s - t))
      (fun y => -parisiTestT φ (t, y) + β ^ 2 / 2 * parisiTestXX φ (t, y)) x) =
        -φ (s, x) + heatSemigroup (β ^ 2 * s) (fun y => φ (0, y)) x := by
  obtain ⟨M, L, J, K, hM, hL, hJ, hK⟩ := parisiTest_global_bounds φ hφ hc
  exact integral_heat_adjointSource φ (parisiTestT φ) (parisiTestX φ) (parisiTestXX φ)
    hφ.continuous (continuous_parisiTestT φ hφ) (continuous_parisiTestX φ hφ)
    (continuous_parisiTestXX φ hφ) M L J K hM hL hJ hK
    (hasDerivAt_parisiTestT φ hφ) (hasDerivAt_parisiTestX φ hφ)
    (hasDerivAt_parisiTestXX φ hφ) β s x hβ hs

theorem parisiTest_zero_time_trace (φ : ℝ × ℝ → ℝ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1}) (x : ℝ) : φ (0, x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hpos := hsupp hx
  exact (lt_irrefl (0 : ℝ)) hpos

/-- Positive-time compact tests remove the initial heat term, exactly as
required by the distributional terminal-value formulation. -/
theorem integral_heat_adjointSource_positiveTimeTest (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1})
    (β s x : ℝ) (hβ : β ≠ 0) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, heatSemigroup (β ^ 2 * (s - t))
      (fun y => -parisiTestT φ (t, y) + β ^ 2 / 2 * parisiTestXX φ (t, y)) x) =
        -φ (s, x) := by
  rw [integral_heat_adjointSource_compactTest φ hφ hc β s x hβ hs]
  have hzero : (fun y : ℝ => φ (0, y)) = fun _ => (0 : ℝ) := by
    funext y
    exact parisiTest_zero_time_trace φ hsupp y
  rw [hzero]
  simp only [heatSemigroup, gaussianExpectation, integral_zero, add_zero]

end Paper
