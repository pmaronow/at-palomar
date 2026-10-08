module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.LocalExtr

@[expose] public section

/-!
# Necessary curvature at a one-sided stationary minimum

At the left endpoint of a nondegenerate interval, a genuine local minimum
with vanishing first derivative has nonnegative inward second derivative.
Only that second derivative at the endpoint is needed. The proof reuses
Mathlib's derivative-as-slope limit and scalar mean value theorem; it does
not assume a second derivative throughout the interval or a Taylor bound.
-/

open Real Filter Topology

namespace SpinGlass.Targets

/-- The necessary second-derivative condition at a one-sided local minimum.
The interval is explicitly nondegenerate; the first derivatives are genuine
within-interval derivatives, including the endpoint value zero. -/
theorem oneSidedCurvature_nonneg_of_localMin
    {f f' : ℝ → ℝ} {a c : ℝ} (ha : 0 < a)
    (hmin : IsLocalMinOn f (Set.Icc 0 a) 0)
    (hf : ∀ x ∈ Set.Icc 0 a, HasDerivWithinAt f (f' x) (Set.Icc 0 a) x)
    (hzero : f' 0 = 0) (hsecond : HasDerivWithinAt f' c (Set.Icc 0 a) 0) :
    0 ≤ c := by
  by_contra hn
  have hcneg : c < 0 := lt_of_not_ge hn
  have Hmin : ∀ᶠ z in 𝓝[Set.Icc 0 a \ {0}] 0, f 0 ≤ f z :=
    hmin.filter_mono (nhdsWithin_mono _ Set.sdiff_subset)
  have H := Hmin.and (hsecond.limsup_slope_le hcneg)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhdsWithin_iff.mp H
  let b := min a (δ / 2)
  have hb : 0 < b := lt_min ha (half_pos hδ)
  have hba : b ≤ a := min_le_left _ _
  have hbδ : b < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hmem {z : ℝ} (hz : z ∈ Set.Ioc 0 b) :
      z ∈ Metric.ball (0 : ℝ) δ ∩ (Set.Icc 0 a \ {0}) := by
    refine ⟨?_, ⟨⟨hz.1.le, hz.2.trans hba⟩, ?_⟩⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hz.1] using
        hz.2.trans_lt hbδ
    · simpa only [Set.mem_singleton_iff] using ne_of_gt hz.1
  have hsub : Set.Icc 0 b ⊆ Set.Icc 0 a := Set.Icc_subset_Icc le_rfl hba
  have hcont : ContinuousOn f (Set.Icc 0 b) :=
    fun x hx => ((hf x (hsub hx)).mono hsub).continuousWithinAt
  obtain ⟨z, hz, heq⟩ := exists_hasDerivAt_eq_slope f f' hb hcont
    (fun z hz => (hf z ⟨hz.1.le, hz.2.le.trans hba⟩).hasDerivAt
      (Icc_mem_nhds hz.1 (hz.2.trans_le hba)))
  have Hzneg := (hδbound (hmem ⟨hz.1, hz.2.le⟩)).2
  rw [slope_def_field, hzero, sub_zero, sub_zero, div_lt_iff₀ hz.1, zero_mul] at Hzneg
  have Hbmin := (hδbound (hmem ⟨hb, le_rfl⟩)).1
  have Hznonneg : 0 ≤ f' z := by
    rw [heq, sub_zero]
    exact div_nonneg (sub_nonneg.mpr Hbmin) hb.le
  exact (not_lt_of_ge Hznonneg) Hzneg

/-- Fixed-interval minimum version of the one-sided second-derivative test,
suited to a genuine fixed-level scheme comparator. -/
theorem oneSidedCurvature_nonneg_of_min
    {f f' : ℝ → ℝ} {a c : ℝ} (ha : 0 < a)
    (hmin : ∀ x ∈ Set.Icc 0 a, f 0 ≤ f x)
    (hf : ∀ x ∈ Set.Icc 0 a, HasDerivWithinAt f (f' x) (Set.Icc 0 a) x)
    (hzero : f' 0 = 0) (hsecond : HasDerivWithinAt f' c (Set.Icc 0 a) 0) :
    0 ≤ c :=
  oneSidedCurvature_nonneg_of_localMin ha
    (show IsMinOn f (Set.Icc 0 a) 0 from hmin).localize hf hzero hsecond

end SpinGlass.Targets
