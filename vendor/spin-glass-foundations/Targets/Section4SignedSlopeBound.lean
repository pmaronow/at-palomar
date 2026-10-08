module

public import Targets.Section4SignedHessianBound

@[expose] public section

/-!
# Endpoint-safe lower bounds for the signed initial factor

The signed factor has nonnegative independent endpoint and its actual
derivative is bounded by the original initial Hessian square. The closed
interval mean-value estimate retains both endpoints and degenerate intervals.
-/

open Real

namespace SpinGlass.Targets

/-- Generic signed-factor lower bound, including both variance endpoints.
The external field may be shifted, so this also applies after conditioning
on an additional independent Gaussian field. -/
theorem signedSplitSlope_lower_bound {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    {a v : ℝ} (hv : v ∈ Set.Icc 0 a) (h : ℝ) :
    -parisiStep 0 a (fun x => A'' x ^ 2) h * (a - v) ≤
      signedSplitSlope A A' a h v := by
  let W := signedSplitSlope A A' a h
  have hc : ContinuousOn W (Set.Icc v a) :=
    (continuous_signedSplitSlope hA hC2 hcA'' a h).continuousOn
  have hd (z : ℝ) (hz : z ∈ Set.Ioo v a) :=
    hasDerivAt_signedSplitSlope hA hC2 hcA'' a h ⟨hv.1.trans_lt hz.1, hz.2⟩
  have hdiff : DifferentiableOn ℝ W (interior (Set.Icc v a)) := by
    rw [interior_Icc]
    exact fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
  have hbound : ∀ z ∈ interior (Set.Icc v a),
      deriv W z ≤ parisiStep 0 a (fun x => A'' x ^ 2) h := by
    rw [interior_Icc]
    intro z hz
    rw [(hd z hz).deriv]
    exact signedSplitHessian_le_unsplit hcA''.measurable hC2.abs_second_le_one
      ⟨hv.1.trans hz.1.le, hz.2.le⟩ h
  have H := (convex_Icc v a).image_sub_le_mul_sub_of_deriv_le hc hdiff hbound
    v ⟨le_rfl, hv.2⟩ a ⟨hv.2, le_rfl⟩ hv.2
  have Htop : 0 ≤ W a := signedSplitSlope_top_nonneg _ _ _ _
  change _ ≤ W v
  nlinarith only [H, Htop]

/-- The signed factor lies above the line from its nonnegative independent
endpoint, with slope controlled by the actual initial Hessian-square factor. -/
theorem signedSplitSlope_parisiF_lower_bound {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {v : ℝ} (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1)) :
    -section4THessianSquare s β h 1 0 * (β ^ 2 * s.q 1 - v) ≤
      signedSplitSlope (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1))
        (β ^ 2 * s.q 1) h v := by
  have H := signedSplitSlope_lower_bound (parisiF_hasLinearGrowth s β (k + 1))
    (parisiF_C2_props s β (k + 1)).1 (continuous_parisiFSecond s β (k + 1)) hv h
  have he : section4THessianSquare s β h 1 0 =
      parisiStep 0 (β ^ 2 * s.q 1) (fun x => parisiFSecond s β (k+1) x ^ 2) h := by
    simp only [section4THessianSquare, Nat.sub_self, s.m_zero,
      section4VarianceR_initial_eq_scalar_integral, s.q_zero, sub_zero]
    simp [stepD2_zero_mass_eq_parisiStep, tiltWeight, parisiStep]
  rwa [he]

/-- A signed initial slope lower bound under the actual endpoint curvature.
The split coordinate may include additional frozen positive covariance: only
`a + t β²u ≤ v ≤ a` is needed. No pressure identification is assumed here. -/
theorem signedSplitSlope_sub_overlap_lower_bound {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {v u t t₀ e : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ≤ 0) (hv : v ∈ Set.Icc 0 (β ^ 2 * s.q 1))
    (hv_lower : β ^ 2 * s.q 1 + t * β ^ 2 * u ≤ v)
    (he : 0 ≤ e) (he_small : e ≤ (1 - t₀) / 2)
    (hR : β ^ 2 * section4THessianSquare s β h 1 0 ≤ 1 + e) :
    (1 - t₀) / 2 * (-u) ≤
      signedSplitSlope (parisiF s β (k + 1)) (parisiFDeriv s β (k + 1))
        (β ^ 2 * s.q 1) h v - u := by
  have hR0 := (section4THessianSquare_mem_Icc s β h (r := 1) (by omega) 0).1
  have H := signedSplitSlope_parisiF_lower_bound s β h hv
  have hwidth := mul_le_mul_of_nonneg_left hv_lower hR0
  have hcurv := mul_le_mul_of_nonneg_left hR ht.1
  have hte : t * e ≤ e := mul_le_of_le_one_left he (ht.2.trans ht₀.le)
  have hcoef : 1 - t * β ^ 2 * section4THessianSquare s β h 1 0 ≥ (1 - t₀) / 2 := by
    nlinarith only [hcurv, hte, ht.2, he_small]
  have Hcoef := mul_le_mul_of_nonneg_right hcoef (neg_nonneg.mpr hu)
  nlinarith only [H, hwidth, Hcoef]

end SpinGlass.Targets
