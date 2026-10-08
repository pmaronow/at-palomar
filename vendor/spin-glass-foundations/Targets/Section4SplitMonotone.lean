module

public import Targets.Section4SplitDerivative

@[expose] public section

/-!
# Closed-interval split-variance comparison

RSAT's finite-step continuity theorem applies to the already checked inner
Parisi family. Continuity includes both variance endpoints; the derivative is
used only in the interior. Thus (4.11) gives monotonicity on the closed interval
without assuming an endpoint derivative.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Joint continuity of the actual two-step split transform, including both
split-variance endpoints. -/
theorem continuous_split_parisiStep {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m m' : ℝ} (hm : m ∈ Set.Icc 0 1) (hm' : 0 ≤ m') (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => parisiStep m' (a - p.1) (parisiStep m p.1 A) p.2) := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hj := continuous_parisiStep_variance_spatial hC2 hc'' hm.1
  have hB2 (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hmap0 : Continuous (fun w : ℝ × ℝ × (ℝ × ℝ) => (w.1, w.2.1 + w.2.2.1)) := by
    fun_prop
  have hgood : GTFrame.GoodTriple
      (fun p l y => parisiStep m p A (l + y.1))
      (fun p l y => stepD1 A A' m p (l + y.1))
      (fun p l y => stepD2 A A' A'' m p (l + y.1)) 1 := by
    refine ⟨⟨hj.1.comp hmap0, hj.2.1.comp hmap0, ?_, ?_,
      fun p l y => (hB2 p).abs_first_le_one _⟩, hj.2.2.comp hmap0, ?_,
      fun p l y => (hB2 p).2.2.1 _,
      fun p l y => (le_abs_self _).trans ((hB2 p).abs_second_le_one _)⟩
    · intro p l y
      simpa only [Function.comp_def, id_eq, mul_one] using!
        ((hB2 p).1 (l + y.1)).comp l ((hasDerivAt_id l).add_const y.1)
    · intro p l y z
      have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := parisiStep m p A) (f' := stepD1 A A' m p) (s := Set.univ) (C := 1)
        (fun t _ => ((hB2 p).1 t).hasDerivWithinAt)
        (fun t _ => by simpa only [Real.norm_eq_abs] using (hB2 p).abs_first_le_one t)
        convex_univ (Set.mem_univ (l + z.1)) (Set.mem_univ (l + y.1))
      have hh : |parisiStep m p A (l + y.1) - parisiStep m p A (l + z.1)| ≤ |y.1 - z.1| := by
        simpa only [Real.norm_eq_abs, one_mul, add_sub_add_left_eq_sub] using H
      exact hh.trans (le_add_of_nonneg_right (abs_nonneg _))
    · intro p l y
      simpa only [Function.comp_def, id_eq, mul_one] using!
        ((hB2 p).2.1 (l + y.1)).comp l ((hasDerivAt_id l).add_const y.1)
  have H := GTFrame.goodTriple_finiteStep
    (α := fun p => Real.sqrt (a - p)) (β := fun _ : ℝ => 0)
    (GTFrame.expMoments_gaussianReal 0 1) hgood hm' (by fun_prop) continuous_const
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1, p.2, ((0 : ℝ), (0 : ℝ)))) := by fun_prop
  have hh := H.good.contF.comp hmap
  by_cases hm0 : m' = 0
  · subst m'
    simpa [GTFrame.finiteStep, GTFrame.step0, parisiStep, Function.comp_def] using! hh
  · simpa [GTFrame.finiteStep, GTFrame.stepM, parisiStep, hm0, Function.comp_def] using! hh

/-- The actual split transform is monotone on the closed variance interval.
Only the already checked interior derivative is used. -/
theorem monotoneOn_split_parisiStep {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m m' : ℝ} (hm : m ∈ Set.Icc 0 1) (hm' : 0 ≤ m') (hmm' : m' ≤ m) (a x : ℝ) :
    MonotoneOn (fun v => parisiStep m' (a - v) (parisiStep m v A) x) (Set.Icc 0 a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
    ((continuous_split_parisiStep hA hC2 hc'' hm hm' a).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro v hv
    have hv' : v ∈ Set.Ioo 0 a := by simpa only [interior_Icc] using hv
    exact (hasDerivAt_split_parisiStep hA hC2 hc'' hm m' a x hv').differentiableAt.differentiableWithinAt
  · intro v hv
    exact deriv_split_parisiStep_nonneg hA hC2 hc'' hm hmm' a x
      (by simpa only [interior_Icc] using hv)

/-- Closed-interval monotonicity for every actual Parisi input, with no extra
analytic hypotheses. -/
theorem monotoneOn_split_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m m' : ℝ} (hm : m ∈ Set.Icc 0 1) (hm' : 0 ≤ m') (hmm' : m' ≤ m) (a x : ℝ) :
    MonotoneOn (fun v => parisiStep m' (a - v) (parisiStep m v (parisiF s β j)) x)
      (Set.Icc 0 a) :=
  monotoneOn_split_parisiStep (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm hm' hmm' a x

end SpinGlass.Targets
