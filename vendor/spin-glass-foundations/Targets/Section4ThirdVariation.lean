module

public import Targets.Section4Curvature
public import Targets.Section4HessianDerivative

@[expose] public section

/-!
# The actual third overlap derivative of the Section 4 first variation

On the open physical overlap interval the already proved inward derivatives
are ordinary derivatives. If the actual Hessian-square factor has derivative
`R'` at the corresponding variance, the chain rule gives
`f'''(u) = beta^6 / 2 * R'(beta^2 * (q_r - u))`.

The sign is positive: the minus sign in the curvature formula cancels the
minus sign from reversing the variance coordinate. No ordinary derivative at
either clamped endpoint is asserted. The initial scalar derivative remains
an explicit input in the transport adapter; beta zero is treated separately.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual first variation's ordinary second derivative at interior
overlaps is the already established inward curvature coefficient. -/
theorem hasDerivAt_deriv_section4FirstVariation {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r)) :
    HasDerivAt (deriv (section4FirstVariation s β h r))
      (section4FirstVariationD2 s β h r u) u := by
  apply ((hasDerivWithinAt_section4FirstVariationD_D2 s β h hr0 hr
    ⟨hu.1.le, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw
  exact ((hasDerivWithinAt_section4FirstVariation_D s β h hr0 hr hm
    ⟨hw.1.le, hw.2.le⟩).hasDerivAt (Icc_mem_nhds hw.1 hw.2)).deriv

/-- Chain rule for the explicit curvature factor. This is a pointwise
statement about a genuine derivative of the actual Hessian-square factor. -/
theorem hasDerivAt_section4FirstVariationD2_of_hessian_derivative
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) {u d : ℝ}
    (hR : HasDerivAt (section4THessianSquare s β h r) d (β ^ 2 * (s.q r - u))) :
    HasDerivAt (section4FirstVariationD2 s β h r) (β ^ 6 / 2 * d) u := by
  have H := hR.comp u (((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2))
  convert! ((H.const_mul (β ^ 2)).const_sub 1).const_mul (β ^ 2 / 2) using 1
  ring

private theorem hasDerivAt_deriv2_section4FirstVariation_of_D2
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u d : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r))
    (hD2 : HasDerivAt (section4FirstVariationD2 s β h r) d u) :
    HasDerivAt (deriv (deriv (section4FirstVariation s β h r))) d u := by
  apply hD2.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw
  exact (hasDerivAt_deriv_section4FirstVariation s β h hr0 hr hm hw).deriv

/-- Genuine third differentiation of the actual first variation on the open
physical overlap interval, with the correct positive variance-chain factor. -/
theorem hasDerivAt_deriv2_section4FirstVariation_of_hessian_derivative
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u d : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r))
    (hR : HasDerivAt (section4THessianSquare s β h r) d (β ^ 2 * (s.q r - u))) :
    HasDerivAt (deriv (deriv (section4FirstVariation s β h r))) (β ^ 6 / 2 * d) u :=
  hasDerivAt_deriv2_section4FirstVariation_of_D2 s β h hr0 hr hm hu
    (hasDerivAt_section4FirstVariationD2_of_hessian_derivative s β h r hR)

/-- A bound for the genuine Hessian-square derivative gives the actual third
derivative bound `beta^6 * L / 2`, without any depth-dependent factor. -/
theorem abs_deriv3_section4FirstVariation_le_of_hessian_derivative
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u d L : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r))
    (hR : HasDerivAt (section4THessianSquare s β h r) d (β ^ 2 * (s.q r - u)))
    (hb : |d| ≤ L) :
    |deriv (deriv (deriv (section4FirstVariation s β h r))) u| ≤ β ^ 6 * L / 2 := by
  rw [(hasDerivAt_deriv2_section4FirstVariation_of_hessian_derivative s β h hr0 hr hm hu hR).deriv,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ β ^ 6 / 2)]
  calc
    _ ≤ β ^ 6 / 2 * L := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The beta-zero case of the actual interior third
derivative is zero, without requiring a derivative on an empty variance
interval. Here beta is zero; no endpoint differentiability is claimed. -/
theorem hasDerivAt_deriv2_section4FirstVariation_beta_zero
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1) {u : ℝ}
    (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r)) :
    HasDerivAt (deriv (deriv (section4FirstVariation s 0 h r))) 0 u := by
  apply hasDerivAt_deriv2_section4FirstVariation_of_D2 s 0 h hr0 hr hm hu
  have he : section4FirstVariationD2 s 0 h r = fun _ => 0 := by
    funext z
    simp only [section4FirstVariationD2, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul]
  rw [he]
  exact hasDerivAt_const u 0

/-- An actual bounded initial scalar Hessian-square derivative implies the
actual interior third-derivative estimate after every outer average. The
scalar input is explicit and beta zero is included without vacuous inference. -/
theorem abs_deriv3_section4FirstVariation_le_of_initial_derivative
    {k : ℕ} (s : RSBScheme k) (β h L : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hm : s.m (r - 1) < 1)
    (dR : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hderiv : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y,
      HasDerivAt (fun w => section4VarianceR s β r (s.m (r - 1)) 0 w x y)
        (dR v x y) v)
    (hmeas : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))),
      Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => dR v p.1 p.2))
    (hbound : ∀ v ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))), ∀ x y, |dR v x y| ≤ L)
    {u : ℝ} (hu : u ∈ Set.Ioo (s.q (r - 1)) (s.q r)) :
    |deriv (deriv (deriv (section4FirstVariation s β h r))) u| ≤ β ^ 6 * L / 2 := by
  by_cases hβ : β = 0
  · subst β
    rw [(hasDerivAt_deriv2_section4FirstVariation_beta_zero s h hr0 hr hm hu).deriv]
    simp only [abs_zero, zero_pow (by norm_num : 6 ≠ 0), zero_mul, zero_div, le_refl]
  · have hv : β ^ 2 * (s.q r - u) ∈ Set.Ioo 0 (β ^ 2 * (s.q r - s.q (r - 1))) :=
      ⟨mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hu.2),
        mul_lt_mul_of_pos_left (by linarith [hu.1]) (sq_pos_of_ne_zero hβ)⟩
    apply abs_deriv3_section4FirstVariation_le_of_hessian_derivative s β h hr0 hr hm hu
      (hasDerivAt_section4THessianSquare_of_initial_derivative s β h L hr0 hr
        dR hderiv hmeas hbound hv)
    exact (section4VarianceR_baseline_deriv_props s β L hr0 hr dR hderiv hmeas hbound le_rfl).bound
      _ hv 0 (fun _ => h)

end SpinGlass.Targets
