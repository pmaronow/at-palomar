module

public import Paper.ATGraph
public import Paper.GaussianSmooth

@[expose] public section

/-!
# Completed smooth AT boundary theorem

The Gaussian regularity theorem, the implicit-function theorem, and the
inverse-function theorem establish all regularity claims for the concrete
curves. No smoothness assumption or curve-existence premise remains.
-/

open Filter
open scoped Topology ContDiff

namespace Paper

theorem contDiffAt_atFieldRoot (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ atFieldRoot t := by
  have hswap : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) (t, atFieldRoot t) :=
    contDiffAt_snd.prodMk contDiffAt_fst
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => atZeroFunction p.2 p.1)
      (t, atFieldRoot t) := by
    simpa only [Function.comp_def] using
      (atZeroFunction_contDiffAt (atFieldRoot t) t ht).comp (t, atFieldRoot t) hswap
  exact contDiffAt_atFieldRoot_of_zeroFunction t ht hF

theorem contDiffOn_atFieldRoot : ContDiffOn ℝ ∞ atFieldRoot (Set.Ioi 0) :=
  fun t ht => (contDiffAt_atFieldRoot t ht).contDiffWithinAt

theorem contDiffAt_atBetaCurve (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ ∞ atBetaCurve t := by
  have hpair : ContDiffAt ℝ ∞ (fun s : ℝ => (atFieldRoot s, s)) t :=
    (contDiffAt_atFieldRoot t ht).prodMk contDiffAt_id
  have hC : ContDiffAt ℝ ∞ (fun s => gaussianC (atFieldRoot s) s) t :=
    (gaussianC_contDiffAt (atFieldRoot t) t ht).comp t
      (f := fun s : ℝ => (atFieldRoot s, s)) hpair
  have hInv : ContDiffAt ℝ ∞ (fun s : ℝ => (1 : ℝ) / gaussianC (atFieldRoot s) s) t :=
    (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1 : ℝ)) t).div hC
      (ne_of_gt (gaussianC_pos (atFieldRoot t) t))
  exact hInv.sqrt (ne_of_gt (one_div_pos.mpr (gaussianC_pos (atFieldRoot t) t)))

theorem contDiffOn_atBetaCurve : ContDiffOn ℝ ∞ atBetaCurve (Set.Ioi 0) :=
  fun t ht => (contDiffAt_atBetaCurve t ht).contDiffWithinAt

/-- The global time inverse agrees locally with the smooth inverse supplied
by the inverse-function theorem. Its positive beta derivative discharges
the invertibility hypothesis. -/
theorem contDiffAt_atTimeFromBeta (β : ℝ) (hβ : 1 < β) :
    ContDiffAt ℝ ∞ atTimeFromBeta β := by
  let t := atTimeFromBeta β
  have ht : 0 < t := atTimeFromBeta_pos β hβ
  have hd : HasDerivAt atBetaCurve (deriv atBetaCurve t) t :=
    (hasDerivAt_atBetaCurve t ht).differentiableAt.hasDerivAt
  have hdne : deriv atBetaCurve t ≠ 0 := ne_of_gt (atBetaCurve_derivative_pos t ht)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (deriv atBetaCurve t) hdne)
  have hde : HasFDerivAt atBetaCurve (e : ℝ →L[ℝ] ℝ) t := hd.hasFDerivAt_equiv hdne
  have hcdf := contDiffAt_atBetaCurve t ht
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let ψ := hcdf.localInverse hde hn
  have hleft : ∀ᶠ s in 𝓝 t, ψ (atBetaCurve s) = s :=
    (hcdf.hasStrictFDerivAt' hde hn).eventually_left_inverse
  have htime : Tendsto atTimeFromBeta (𝓝 β) (𝓝 t) :=
    (continuousAt_atTimeFromBeta β hβ).tendsto
  have hevent := htime.eventually hleft
  have heq : atTimeFromBeta =ᶠ[𝓝 β] ψ := by
    filter_upwards [hevent, eventually_gt_nhds hβ] with b hb hbone
    rw [atBetaCurve_atTimeFromBeta b hbone] at hb
    exact hb.symm
  have hψ : ContDiffAt ℝ ∞ ψ β := by
    simpa only [t, atBetaCurve_atTimeFromBeta β hβ] using hcdf.to_localInverse hde hn
  exact hψ.congr_of_eventuallyEq heq

theorem contDiffOn_atTimeFromBeta : ContDiffOn ℝ ∞ atTimeFromBeta (Set.Ioi 1) :=
  fun β hβ => (contDiffAt_atTimeFromBeta β hβ).contDiffWithinAt

theorem contDiffAt_atBoundaryField (β : ℝ) (hβ : 1 < β) :
    ContDiffAt ℝ ∞ atBoundaryField β :=
  (contDiffAt_atFieldRoot (atTimeFromBeta β) (atTimeFromBeta_pos β hβ)).comp β
    (contDiffAt_atTimeFromBeta β hβ)

theorem contDiffOn_atBoundaryField : ContDiffOn ℝ ∞ atBoundaryField (Set.Ioi 1) :=
  fun β hβ => (contDiffAt_atBoundaryField β hβ).contDiffWithinAt

/-- Proposition 1.2 of arXiv:2604.11921v2, with the actual Gaussian AT set:
its positive-field boundary is a positive, strictly increasing, smooth graph
on `(1,∞)`, and the graph tends to `(1,0)` at its left endpoint. -/
theorem smoothATBoundary : SmoothATBoundaryTarget := by
  exact ⟨atBoundaryField, atBoundaryField_pos, contDiffOn_atBoundaryField,
    atBoundaryField_strictMonoOn, tendsto_atBoundaryField_one_right, atBoundary_eq_field_graph⟩

end Paper
