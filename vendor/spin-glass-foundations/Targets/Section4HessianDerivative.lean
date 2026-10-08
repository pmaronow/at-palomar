module

public import Targets.Section4USecond

@[expose] public section

/-!
# No-loss propagation of the Hessian-square variance derivative

At the baseline mass, each unchanged outer potential has zero split-variance
velocity. The existing normalized-observable differentiation rule therefore
propagates an actual initial Hessian-square derivative by fixed positive
normalized means. Its uniform bound does not grow with the outer depth.

The scalar initial derivative, its measurability and its bound are explicit
inputs here. They are not inferred from a Lipschitz bound or postulated for the
final factor. Differentiation is only asserted on the open physical interval.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Propagation of a specified initial Hessian-square derivative through the
actual unchanged outer averages at the baseline mass. -/
noncomputable def section4VarianceRDerivative {k : ℕ} (s : RSBScheme k) (β : ℝ) (r : ℕ)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ) :
    ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ
  | 0 => dR
  | j + 1 => fun v =>
      pairedSecondMean (s.m (k + 2 - (k + 2 - r + 2 + j)))
        (β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) -
          s.q (k + 2 - (k + 2 - r + 2 + j))))
        (fun _ y => scalarFieldCascade
          (fun l => section4Mass s r (s.m (r - 1)) (k + 2 - l))
          (fun l => section5Variance s β r (k + 2 - l) v)
          (k + 2 - r + 2 + j) (y 0))
        (section4VarianceRDerivative s β r dR j v)

/-- Genuine variance differentiation through every unchanged outer level,
with exactly the same bound as the given scalar initial derivative. -/
theorem section4VarianceR_baseline_deriv_props {k : ℕ} (s : RSBScheme k) (β L : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hderiv : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (dR v x y) v)
    (hmeas : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => dR v p.1 p.2))
    (hbound : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y, |dR v x y| ≤ L)
    {j : ℕ} (hj : j ≤ r - 1) :
    CoupledParamDeriv (section4VarianceR s β r (s.m (r - 1)) j)
      (section4VarianceRDerivative s β r dR j)
      (Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) L := by
  have hm : s.m (r - 1) ∈ Set.Icc 0 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hRb (j : ℕ) (v : ℝ) (x y : Fin 1 → ℝ) :
      |section4VarianceR s β r (s.m (r - 1)) j v x y| ≤ 1 := by
    have H := section4VarianceR_mem_Icc s β r hm j v x y
    simpa only [abs_of_nonneg H.1] using H.2
  induction j with
  | zero =>
    exact ⟨hderiv, fun v _ => measurable_section4VarianceR s β r _ 0 v, hmeas,
      ⟨1, 0, le_rfl, fun v _ x y => by simpa using hRb 0 v x y⟩, hbound⟩
  | succ j ih =>
    have hprev := ih (by omega)
    have hp := section4VarianceD_props s β hr0 hr hm le_rfl (j := j) (by omega)
    have he : section4VarianceD s β r (s.m (r - 1)) j = fun _ _ _ => 0 := by
      funext v x y
      simp only [section4VarianceD_eq_massGap_mul, sub_self, zero_div, zero_mul]
    rw [he] at hp
    refine ⟨?_, fun v _ => measurable_section4VarianceR s β r _ (j + 1) v, ?_,
      ⟨1, 0, le_rfl, fun v _ x y => by simpa using hRb (j + 1) v x y⟩, ?_⟩
    · intro v hv x y
      have H := hasDerivAt_pairedSecondMean hp hprev
        (fun w _ x y => hRb j w x y) (Ioo_mem_nhds hv.1 hv.2) x y
        (m := s.m (k + 2 - (k + 2 - r + 2 + j)))
        (v := β ^ 2 * (s.q (k + 2 - (k + 2 - r + 2 + j) + 1) -
          s.q (k + 2 - (k + 2 - r + 2 + j))))
      simpa only [section4VarianceR, section4VarianceRDerivative, mul_zero, add_zero,
        pairedSecondMean, pairedTiltMean, zero_mul, integral_zero, sub_zero] using! H
    · intro v hv
      unfold section4VarianceRDerivative
      apply measurable_pairedSecondMean
      · exact hp.measurable v hv
      · exact hprev.measurable_deriv v hv
    · intro v hv x y
      exact pairedTiltMean_abs_le ((hp.growth_at hv).section_right x)
        ((hprev.measurable_deriv v hv).comp (measurable_const.prodMk measurable_id))
        (hprev.bound v hv x) y

/-- The specified initial derivative, averaged through all unchanged outer
levels, is the genuine derivative of the final factor in (4.45). -/
theorem hasDerivAt_section4THessianSquare_of_initial_derivative
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hderiv : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (dR v x y) v)
    (hmeas : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => dR v p.1 p.2))
    (hbound : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y, |dR v x y| ≤ L)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivAt (section4THessianSquare s β h r)
      (section4VarianceRDerivative s β r dR (r - 1) v 0 (fun _ => h)) v :=
  (section4VarianceR_baseline_deriv_props s β L hr0 hr dR hderiv hmeas hbound le_rfl).deriv
    v hv 0 (fun _ => h)

/-- The genuine derivative's bound is unchanged by all outer recursion
levels. No field, depth or system-size factor appears. -/
theorem abs_deriv_section4THessianSquare_le_of_initial_derivative
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hderiv : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (dR v x y) v)
    (hmeas : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => dR v p.1 p.2))
    (hbound : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y, |dR v x y| ≤ L)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |deriv (section4THessianSquare s β h r) v| ≤ L := by
  rw [(hasDerivAt_section4THessianSquare_of_initial_derivative s β h L hr0 hr
    dR hderiv hmeas hbound hv).deriv]
  exact (section4VarianceR_baseline_deriv_props s β L hr0 hr dR hderiv hmeas hbound le_rfl).bound
    v hv 0 (fun _ => h)

end SpinGlass.Targets
