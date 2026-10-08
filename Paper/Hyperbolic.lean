module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

@[expose] public section

/-!
# Hyperbolic identities and pointwise inequalities

The pointwise analytic ingredients of arXiv:2604.11921v2, Sections 3 and 4.
All hyperbolic functions are the actual real functions from mathlib.
-/

namespace Paper

noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

@[simp]theorem sech_zero : sech 0 = 1 := by simp [sech]
@[simp]theorem sech_neg (x : ℝ) : sech (-x) = sech x := by simp [sech]

theorem sech_pos (x : ℝ) : 0 < sech x := one_div_pos.mpr (Real.cosh_pos x)

theorem sech_le_one (x : ℝ) : sech x ≤ 1 := by
  rw [sech, div_le_one (Real.cosh_pos x)]
  exact Real.one_le_cosh x

theorem sech_sq_pos (x : ℝ) : 0 < sech x ^ 2 := sq_pos_of_pos (sech_pos x)

theorem sech_sq_le_one (x : ℝ) : sech x ^ 2 ≤ 1 := by
  have hp := sech_pos x
  have hl := sech_le_one x
  nlinarith

theorem tanh_sq_add_sech_sq (x : ℝ) : Real.tanh x ^ 2 + sech x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  have h := Real.cosh_sq_sub_sinh_sq x
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith

theorem sech_fourth_pos (x : ℝ) : 0 < sech x ^ 4 := pow_pos (sech_pos x) 4

theorem sech_fourth_le_one (x : ℝ) : sech x ^ 4 ≤ 1 := by
  simpa using pow_le_pow_left₀ (sech_pos x).le (sech_le_one x) 4

theorem tanh_sq_lt_one (x : ℝ) : Real.tanh x ^ 2 < 1 := by
  have hi := tanh_sq_add_sech_sq x
  have hp := sech_sq_pos x
  nlinarith

theorem tanh_sq_le_one (x : ℝ) : Real.tanh x ^ 2 ≤ 1 := (tanh_sq_lt_one x).le

theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

theorem tanh_neg_of_neg {x : ℝ} (hx : x < 0) : Real.tanh x < 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr hx) (Real.cosh_pos x)

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (sech x ^ 2) x := by
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · dsimp [sech]
    have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
    have h := Real.cosh_sq_sub_sinh_sq x
    field_simp
    nlinarith

theorem hasDerivAt_sech (x : ℝ) :
    HasDerivAt sech (-(Real.tanh x * sech x)) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · rfl
  · simp only [sech, Real.tanh_eq_sinh_div_cosh]
    ring

theorem hasDerivAt_sech_sq (x : ℝ) :
    HasDerivAt (fun y => sech y ^ 2) (-2 * Real.tanh x * sech x ^ 2) x := by
  convert (hasDerivAt_sech x).pow 2 using 1
  ring

theorem tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh x).deriv]
  exact sech_sq_pos x

theorem tanh_monotone : Monotone Real.tanh := tanh_strictMono.monotone

/-- The comparison used to prove decay of the symmetrized Gaussian weight. -/
theorem scaled_tanh_le {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    c * Real.tanh (c * x) ≤ Real.tanh x := by
  calc
    c * Real.tanh (c * x) ≤ c * Real.tanh x :=
      mul_le_mul_of_nonneg_left (tanh_monotone (by nlinarith)) hc0
    _ ≤ Real.tanh x := by nlinarith [tanh_nonneg hx]

/-- A strict pointwise inequality underlying `B - T > 0` in Appendix Proposition 1.2. -/
theorem tanh_sub_mul_sech_sq_pos {y : ℝ} (hy : 0 < y) :
    0 < Real.tanh y - y * sech y ^ 2 := by
  have hs : 2 * y < Real.sinh (2 * y) := Real.self_lt_sinh_iff.mpr (by linarith)
  have hdouble : Real.sinh (2 * y) = 2 * Real.sinh y * Real.cosh y := by
    rw [two_mul, Real.sinh_add]
    ring
  rw [hdouble] at hs
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  have hc : Real.cosh y ≠ 0 := ne_of_gt (Real.cosh_pos y)
  have heq : Real.sinh y / Real.cosh y - y * (1 / Real.cosh y) ^ 2 =
      (Real.sinh y * Real.cosh y - y) / Real.cosh y ^ 2 := by
    field_simp
  rw [heq]
  exact div_pos (by nlinarith) (sq_pos_of_pos (Real.cosh_pos y))

theorem tanh_mul_tanh_sub_mul_sech_sq_pos {y : ℝ} (hy : y ≠ 0) :
    0 < Real.tanh y * (Real.tanh y - y * sech y ^ 2) := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have h := mul_pos (tanh_pos (neg_pos.mpr hneg))
      (tanh_sub_mul_sech_sq_pos (neg_pos.mpr hneg))
    convert h using 1
    simp only [Real.tanh_neg, sech_neg]
    ring
  · exact mul_pos (tanh_pos hpos) (tanh_sub_mul_sech_sq_pos hpos)

theorem mul_tanh_pos {y : ℝ} (hy : y ≠ 0) : 0 < y * Real.tanh y := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · exact mul_pos_of_neg_of_neg hneg (tanh_neg_of_neg hneg)
  · exact mul_pos hpos (tanh_pos hpos)

/-- The scalar double-integrand in the paper's heat-kernel comparison is nonnegative. -/
theorem even_radial_comonotone {f g : ℝ → ℝ}
    (hf_even : ∀ x, f (-x) = f x) (hg_even : ∀ x, g (-x) = g x)
    (hf : AntitoneOn f (Set.Ici 0)) (hg : AntitoneOn g (Set.Ici 0))
    (x y : ℝ) : 0 ≤ (f x - f y) * (g x - g y) := by
  have habsf : ∀ z, f |z| = f z := by
    intro z
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, hf_even]
  have habsg : ∀ z, g |z| = g z := by
    intro z
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_nonpos hz, hg_even]
  rcases le_total |x| |y| with hxy | hyx
  · have hfx := hf (abs_nonneg x) (abs_nonneg y) hxy
    have hgx := hg (abs_nonneg x) (abs_nonneg y) hxy
    rw [habsf, habsf] at hfx
    rw [habsg, habsg] at hgx
    exact mul_nonneg (sub_nonneg.mpr hfx) (sub_nonneg.mpr hgx)
  · have hfx := hf (abs_nonneg y) (abs_nonneg x) hyx
    have hgx := hg (abs_nonneg y) (abs_nonneg x) hyx
    rw [habsf, habsf] at hfx
    rw [habsg, habsg] at hgx
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfx) (sub_nonpos.mpr hgx)

theorem sech_antitoneOn : AntitoneOn sech (Set.Ici 0) := by
  intro x hx y hy hxy
  dsimp [sech]
  exact one_div_le_one_div_of_le (Real.cosh_pos x)
    (Real.cosh_strictMonoOn.monotoneOn hx hy hxy)

theorem sech_cube_antitoneOn : AntitoneOn (fun x => sech x ^ 3) (Set.Ici 0) := by
  intro x hx y hy hxy
  exact pow_le_pow_left₀ (sech_pos y).le (sech_antitoneOn hx hy hxy) 3

theorem sech_cube_comonotone {f : ℝ → ℝ}
    (hf_even : ∀ x, f (-x) = f x) (hf : AntitoneOn f (Set.Ici 0))
    (x y : ℝ) : 0 ≤ (f x - f y) * (sech x ^ 3 - sech y ^ 3) :=
  even_radial_comonotone hf_even (by intro z; simp) hf sech_cube_antitoneOn x y

theorem hasDerivAt_sech_fourth (x : ℝ) :
    HasDerivAt (fun y => sech y ^ 4) (-4 * Real.tanh x * sech x ^ 4) x := by
  convert (hasDerivAt_sech x).pow 4 using 1
  ring

theorem hasDerivAt_tanh_mul_sech_sq (x : ℝ) :
    HasDerivAt (fun y => Real.tanh y * sech y ^ 2)
      (3 * sech x ^ 4 - 2 * sech x ^ 2) x := by
  convert (hasDerivAt_tanh x).mul (hasDerivAt_sech_sq x) using 1
  have hi := tanh_sq_add_sech_sq x
  nlinarith [sq_nonneg (sech x)]

/-- The Gaussian factor of the paper's even weight, with the positive normalizing
constant removed. The parameters are variance `v` and tilt `c = h / v`. -/
noncomputable def radialWeight (v c x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (2 * v)) * Real.cosh (c * x) / Real.cosh x

theorem radialWeight_pos (v c x : ℝ) : 0 < radialWeight v c x := by
  exact div_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)) (Real.cosh_pos _)

@[simp]theorem radialWeight_neg (v c x : ℝ) :
    radialWeight v c (-x) = radialWeight v c x := by
  simp [radialWeight]

theorem hasDerivAt_radialWeight {v : ℝ} (hv : 0 < v) (c x : ℝ) :
    HasDerivAt (radialWeight v c)
      (radialWeight v c x * (-x / v + c * Real.tanh (c * x) - Real.tanh x)) x := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  have he : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * v)) (-x / v) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (2 * v) using 1
    · ext y
      dsimp
    · dsimp
      field_simp

  have hcosh := (Real.hasDerivAt_cosh (c * x)).comp x ((hasDerivAt_id x).const_mul c)
  convert (he.exp.mul hcosh).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · rfl
  · dsimp [radialWeight]
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp

theorem radialWeight_log_derivative {v : ℝ} (hv : 0 < v) (c x : ℝ) :
    deriv (radialWeight v c) x / radialWeight v c x =
      -x / v + c * Real.tanh (c * x) - Real.tanh x := by
  rw [(hasDerivAt_radialWeight hv c x).deriv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (radialWeight_pos v c x))

theorem radialWeight_log_derivative_le {v c x : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    deriv (radialWeight v c) x / radialWeight v c x ≤ -x / v := by
  rw [radialWeight_log_derivative hv]
  linarith [scaled_tanh_le hc0 hc1 hx]

theorem radialWeight_strictAntiOn {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    StrictAntiOn (radialWeight v c) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_radialWeight hv c x).continuousAt)).continuousOn
  · intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hasDerivAt_radialWeight hv c x).deriv]
    apply mul_neg_of_pos_of_neg (radialWeight_pos v c x)
    have hbound := scaled_tanh_le hc0 hc1 hx.le
    have hneg : -x / v < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hx) hv
    linarith

theorem radialWeight_sech_cube_comonotone {v c : ℝ} (hv : 0 < v)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x y : ℝ) :
    0 ≤ (radialWeight v c x - radialWeight v c y) * (sech x ^ 3 - sech y ^ 3) :=
  sech_cube_comonotone (radialWeight_neg v c)
    (radialWeight_strictAntiOn hv hc0 hc1).antitoneOn x y

@[simp] theorem deriv_tanh (x : ℝ) : deriv Real.tanh x = sech x ^ 2 :=
  (hasDerivAt_tanh x).deriv

@[simp] theorem deriv_sech_sq (x : ℝ) :
    deriv (fun y => sech y ^ 2) x = -2 * Real.tanh x * sech x ^ 2 :=
  (hasDerivAt_sech_sq x).deriv

@[simp] theorem deriv_sech_fourth (x : ℝ) :
    deriv (fun y => sech y ^ 4) x = -4 * Real.tanh x * sech x ^ 4 :=
  (hasDerivAt_sech_fourth x).deriv

theorem hasDerivAt_deriv_tanh (x : ℝ) :
    HasDerivAt (deriv Real.tanh) (-2 * Real.tanh x * sech x ^ 2) x := by
  simpa only [show deriv Real.tanh = (fun y => sech y ^ 2) from funext deriv_tanh]
    using hasDerivAt_sech_sq x

/-- The pointwise drift cancellation in Itô's formula for the magnetization. -/
theorem tanh_diffusion_drift_zero (x : ℝ) :
    Real.tanh x * deriv Real.tanh x + (1 / 2 : ℝ) * deriv (deriv Real.tanh) x = 0 := by
  rw [deriv_tanh, (hasDerivAt_deriv_tanh x).deriv]
  ring

theorem hasDerivAt_deriv_sech_sq (x : ℝ) :
    HasDerivAt (deriv (fun y => sech y ^ 2))
      (4 * sech x ^ 2 - 6 * sech x ^ 4) x := by
  convert (hasDerivAt_tanh_mul_sech_sq x).const_mul (-2) using 1
  · ext y
    rw [deriv_sech_sq]
    ring
  · ring

theorem hasDerivAt_tanh_mul_sech_fourth (x : ℝ) :
    HasDerivAt (fun y => Real.tanh y * sech y ^ 4)
      (5 * sech x ^ 6 - 4 * sech x ^ 4) x := by
  convert (hasDerivAt_tanh x).mul (hasDerivAt_sech_fourth x) using 1
  have hi := tanh_sq_add_sech_sq x
  nlinarith [sq_nonneg (sech x), sq_nonneg (sech x ^ 2)]

theorem hasDerivAt_deriv_sech_fourth (x : ℝ) :
    HasDerivAt (deriv (fun y => sech y ^ 4))
      (16 * sech x ^ 4 - 20 * sech x ^ 6) x := by
  convert (hasDerivAt_tanh_mul_sech_fourth x).const_mul (-4) using 1
  · ext y
    rw [deriv_sech_fourth]
    ring
  · ring

/-- Product differentiation used in the cosh conjugation of the diffusion generator. -/
theorem hasDerivAt_cosh_mul {φ φ' : ℝ → ℝ} {x : ℝ}
    (hφ : HasDerivAt φ (φ' x) x) :
    HasDerivAt (fun y => Real.cosh y * φ y)
      (Real.sinh x * φ x + Real.cosh x * φ' x) x :=
  (Real.hasDerivAt_cosh x).mul hφ

theorem hasDerivAt_cosh_mul_first {φ φ' : ℝ → ℝ} {φ'' x : ℝ}
    (hφ : HasDerivAt φ (φ' x) x) (hφ' : HasDerivAt φ' φ'' x) :
    HasDerivAt (fun y => Real.sinh y * φ y + Real.cosh y * φ' y)
      (Real.cosh x * φ x + 2 * Real.sinh x * φ' x + Real.cosh x * φ'') x := by
  convert ((Real.hasDerivAt_sinh x).mul hφ).add
    ((Real.hasDerivAt_cosh x).mul hφ') using 1
  ring

theorem cosh_generator_conjugation (x a b d : ℝ) :
    (Real.cosh x * a + 2 * Real.sinh x * b + Real.cosh x * d) /
        (2 * Real.cosh x) - a / 2 =
      d / 2 + Real.tanh x * b := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

end Paper
