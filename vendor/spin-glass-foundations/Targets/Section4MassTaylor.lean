module

public import Targets.Section4MassSecond

@[expose] public section

/-!
# Uniform quadratic mass remainders for the actual Section 4 functions

Two applications of Mathlib's mean-value bound give an endpoint-safe quadratic
remainder. We do not optimize the constant: the bound is `C * (m - m₀)^2`, with
the same beta-only second-derivative constant `C`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

theorem quadratic_remainder_of_second_bound {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv f) x)
    (hb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv f) x| ≤ C)
    {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb' : b ∈ Set.Icc 0 1) :
    |f b - f a - deriv f a * (b - a)| ≤ C * (b - a) ^ 2 := by
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 1 := Set.uIcc_subset_Icc ha hb'
  have hD (x : ℝ) (hx : x ∈ Set.uIcc a b) : |deriv f x - deriv f a| ≤ C * |b - a| := by
    have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hf'
      (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx) ha (hsub hx)
    have H' : |deriv f x - deriv f a| ≤ C * |x - a| := by simpa only [Real.norm_eq_abs] using H
    exact H'.trans (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx) hC)
  let R := fun x => f x - f a - deriv f a * (x - a)
  have hR (x : ℝ) (hx : x ∈ Set.uIcc a b) : HasDerivAt R (deriv f x - deriv f a) x := by
    simpa only [R, Pi.sub_def, id_eq, mul_one] using ((hf x (hsub hx)).hasDerivAt.sub_const (f a)).sub
      (((hasDerivAt_id x).sub_const a).const_mul (deriv f a))
  have H := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hR x hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hD x hx)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simpa only [R, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, mul_assoc, ← sq,
    sq_abs] using H

private theorem differentiableAt_section4T_mass_physical {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m v : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    DifferentiableAt ℝ (fun a => section4T s β h r a v) m := by
  have H := (section4MassE_deriv_props s β hr hv (V := v) le_rfl (j := r) le_rfl).1.deriv m
    ⟨by linarith [hm.1], by linarith [hm.2]⟩ 0 (fun _ => h)
  have hi : k + 2 - r + 1 + r = k + 3 := by omega
  simpa only [section4T, hi] using H.differentiableAt

/-- The actual mass derivative of `T` is uniformly Lipschitz on `[0,1]`. -/
theorem section4T_mass_derivative_lipschitz {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {a b v : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |deriv (fun m => section4T s β h r m v) b - deriv (fun m => section4T s β h r m v) a| ≤
      section4MassSecondBound (β ^ 2) * |b - a| := by
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hasDerivAt_deriv_section4T_mass s β h hr
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ hv).differentiableAt)
    (fun x hx => by simpa only [Real.norm_eq_abs, iteratedDeriv_succ, iteratedDeriv_zero] using
      abs_second_deriv_section4T_mass_le_uniform s β h hr hx hv) ha hb
  simpa only [Real.norm_eq_abs] using H

/-- Endpoint-inclusive quadratic Taylor bound for the actual full transform,
uniform in the level count, field, variance and adjacent mass gap. -/
theorem section4T_mass_taylor_bound {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {a b v : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4T s β h r b v - section4T s β h r a v -
      deriv (fun m => section4T s β h r m v) a * (b - a)| ≤
      section4MassSecondBound (β ^ 2) * (b - a) ^ 2 := by
  apply quadratic_remainder_of_second_bound (section4MassSecondBound_nonneg _)
    (fun x hx => differentiableAt_section4T_mass_physical s β h hr hx hv)
    (fun x hx => (hasDerivAt_deriv_section4T_mass s β h hr
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ hv).differentiableAt)
    (fun x hx => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      abs_second_deriv_section4T_mass_le_uniform s β h hr hx hv) ha hb

private theorem differentiableAt_section4Phi_mass_physical {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m u : ℝ} (hm : m ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    DifferentiableAt ℝ (fun a => section4Phi s β h r a u) m := by
  have hv := section5SplitVariance_mem s β (t := 1) ⟨by norm_num, le_rfl⟩ hu
  simp only [one_mul] at hv
  unfold section4Phi
  exact (((differentiableAt_section4T_mass_physical s β h hr hm hv).const_add _).sub_const _).add
    (((differentiableAt_id).const_sub _).mul_const _)

/-- The actual inserted functional has a depth-uniform Lipschitz mass derivative. -/
theorem section4Phi_mass_derivative_lipschitz {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {a b u : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |deriv (fun m => section4Phi s β h r m u) b - deriv (fun m => section4Phi s β h r m u) a| ≤
      section4MassSecondBound (β ^ 2) * |b - a| := by
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => by
      obtain ⟨e, he, _⟩ := section4Phi_second_mass_derivative_uniform s β h hr hx hu
      exact he.differentiableAt)
    (fun x hx => by simpa only [Real.norm_eq_abs, iteratedDeriv_succ, iteratedDeriv_zero] using
      abs_second_deriv_section4Phi_mass_le_uniform s β h hr hx hu) ha hb
  simpa only [Real.norm_eq_abs] using H

/-- The deterministic affine correction contributes no Taylor remainder.
The actual inserted functional satisfies the same uniform quadratic bound as `T`. -/
theorem section4Phi_mass_taylor_bound {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {a b u : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4Phi s β h r b u - section4Phi s β h r a u -
      deriv (fun m => section4Phi s β h r m u) a * (b - a)| ≤
      section4MassSecondBound (β ^ 2) * (b - a) ^ 2 := by
  apply quadratic_remainder_of_second_bound (section4MassSecondBound_nonneg _)
    (fun x hx => differentiableAt_section4Phi_mass_physical s β h hr hx hu)
    (fun x hx => by
      obtain ⟨e, he, _⟩ := section4Phi_second_mass_derivative_uniform s β h hr hx hu
      exact he.differentiableAt)
    (fun x hx => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      abs_second_deriv_section4Phi_mass_le_uniform s β h hr hx hu) ha hb

/-- Baseline expansion in the notation of Talagrand (4.42). The mass gap may
vanish, and the baseline mass may be zero. -/
theorem section4T_mass_taylor_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m v : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    |section4T s β h r m v - section4T s β h r (s.m (r - 1)) v -
      section4U s β h r v / 2 * (m - s.m (r - 1))| ≤
      section4MassSecondBound (β ^ 2) * (m - s.m (r - 1)) ^ 2 := by
  have ha : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have H := section4T_mass_taylor_bound s β h hr ha ⟨ha.1.trans hm.1, hm.2⟩ hv
  rwa [(hasDerivAt_section4T_mass_baseline s β h hr0 hr hv).deriv] at H

/-- The actual inserted functional admits the uniform expansion with the
already identified first variation (4.46) and the original Parisi functional.
No optimality or missing lower-bound conclusion is assumed. -/
theorem section4Phi_mass_taylor_baseline {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    |section4Phi s β h r m u - parisiFunctional s β h -
      section4FirstVariation s β h r u * (m - s.m (r - 1))| ≤
      section4MassSecondBound (β ^ 2) * (m - s.m (r - 1)) ^ 2 := by
  have ha : s.m (r - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have H := section4Phi_mass_taylor_bound s β h hr ha ⟨ha.1.trans hm.1, hm.2⟩ hu
  rwa [(hasDerivAt_section4Phi_mass_baseline s β h hr0 hr hu).deriv,
    section4Phi_baseline s β h hr0 hr hu] at H

end SpinGlass.Targets
