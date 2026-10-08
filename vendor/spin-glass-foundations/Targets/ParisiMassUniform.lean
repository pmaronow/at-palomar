module

public import Targets.ParisiMassLocal
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Uniform mass derivatives of the actual scalar transform

The analytic zero-mass extension removes the apparent inverse powers of mass.
Weighted derivative identities reduce uniform first and second mass estimates
to bounded second and third cumulants of the centered Gaussian input.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

private theorem weighted_derivative_bound {F : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hF : Differentiable ℝ F) {K : ℝ}
    (hb : ∀ m ∈ Set.Icc (0 : ℝ) 1,
      |(n : ℝ) * F m + m * deriv F m| ≤ K) {m : ℝ} (hm : m ∈ Set.Icc 0 1) :
    |F m| ≤ K / n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      |t ^ n * F t| ≤ K / n * t ^ n := by
    let H : ℝ → ℝ := fun u => u ^ n * F u
    have hD (u : ℝ) : HasDerivAt H
        (u ^ (n - 1) * ((n : ℝ) * F u + u * deriv F u)) u := by
      have hpow : u ^ (n - 1) * u = u ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      convert! ((hasDerivAt_pow n u).mul (hF u).hasDerivAt) using 1
      rw [mul_add, ← mul_assoc _ u, hpow]
      ring
    have hup : H t ≤ K / n * t ^ n := by
      have hanti : AntitoneOn (fun u => H u - K / n * u ^ n) (Set.Icc 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
        · exact ((continuous_iff_continuousAt.mpr fun u => (hD u).continuousAt).sub (by fun_prop)).continuousOn
        · exact fun u _ => ((hD u).sub ((hasDerivAt_pow n u).const_mul (K / n))).differentiableAt.differentiableWithinAt
        · intro u hu
          have HH := ((hD u).sub ((hasDerivAt_pow n u).const_mul (K / n))).deriv
          simp only [Pi.sub_def] at HH
          rw [HH]
          have hbu := (abs_le.mp (hb u (interior_subset hu))).2
          have hpow : 0 ≤ u ^ (n - 1) := pow_nonneg (interior_subset hu).1 _
          have halg : u ^ (n - 1) * ((n : ℝ) * F u + u * deriv F u) -
              K / n * ((n : ℝ) * u ^ (n - 1)) =
              u ^ (n - 1) * ((n : ℝ) * F u + u * deriv F u - K) := by
            field_simp [hnR.ne']
          rw [halg]
          exact mul_nonpos_of_nonneg_of_nonpos hpow (sub_nonpos.mpr hbu)
      have HH := hanti ⟨le_rfl, by norm_num⟩ ht ht.1
      simpa only [H, zero_pow (Nat.ne_of_gt hn), zero_mul, mul_zero, sub_self, sub_nonpos] using HH
    have hlo : -(K / n * t ^ n) ≤ H t := by
      have hmono : MonotoneOn (fun u => H u + K / n * u ^ n) (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · exact ((continuous_iff_continuousAt.mpr fun u => (hD u).continuousAt).add (by fun_prop)).continuousOn
        · exact fun u _ => ((hD u).add ((hasDerivAt_pow n u).const_mul (K / n))).differentiableAt.differentiableWithinAt
        · intro u hu
          have HH := ((hD u).add ((hasDerivAt_pow n u).const_mul (K / n))).deriv
          simp only [Pi.add_def] at HH
          rw [HH]
          have hbu := (abs_le.mp (hb u (interior_subset hu))).1
          have hpow : 0 ≤ u ^ (n - 1) := pow_nonneg (interior_subset hu).1 _
          have halg : u ^ (n - 1) * ((n : ℝ) * F u + u * deriv F u) +
              K / n * ((n : ℝ) * u ^ (n - 1)) =
              u ^ (n - 1) * ((n : ℝ) * F u + u * deriv F u + K) := by
            field_simp [hnR.ne']
          rw [halg]
          exact mul_nonneg hpow (by linarith)
      have HH := hmono ⟨le_rfl, by norm_num⟩ ht ht.1
      simp only [H, zero_pow (Nat.ne_of_gt hn), zero_mul, zero_add] at HH
      linarith
    exact abs_le.mpr ⟨hlo, hup⟩
  rcases eq_or_lt_of_le hm.1 with he | hp
  · subst m
    simpa only [zero_mul, add_zero, abs_mul, abs_of_pos hnR, mul_div_cancel_left₀ _ hnR.ne'] using
      (div_le_div_of_nonneg_right (hb 0 ⟨le_rfl, by norm_num⟩) hnR.le)
  · have H := hbound m hm
    rw [abs_mul, abs_of_pos (pow_pos hp n)] at H
    exact (mul_le_mul_iff_right₀ (pow_pos hp n)).mp (by simpa only [mul_comm (m ^ n)] using H)

private theorem mass_derivatives_of_cumulant_bounds {M : ℝ → ℝ}
    (hM : ∀ m, AnalyticAt ℝ M m) {K₂ K₃ : ℝ}
    (h₂ : ∀ m ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 (fun u => u * M u) m| ≤ K₂)
    (h₃ : ∀ m ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 (fun u => u * M u) m| ≤ K₃)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) :
    |deriv M m| ≤ K₂ / 2 ∧ |iteratedDeriv 2 M m| ≤ K₃ / 3 := by
  have he₂ (u : ℝ) : iteratedDeriv 2 (fun z => z * M z) u =
      2 * deriv M u + u * deriv (deriv M) u := by
    rw [iteratedDeriv_fun_mul (by fun_prop) (hM u).contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  have he₃ (u : ℝ) : iteratedDeriv 3 (fun z => z * M z) u =
      3 * iteratedDeriv 2 M u + u * deriv (iteratedDeriv 2 M) u := by
    rw [iteratedDeriv_fun_mul (by fun_prop) (hM u).contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_succ, iteratedDeriv_one]
    ring
  constructor
  · exact weighted_derivative_bound (n := 2) (by omega) (fun u => (hM u).deriv.differentiableAt)
      (by simpa only [he₂, Nat.cast_ofNat] using h₂) hm
  · exact weighted_derivative_bound (n := 3) (by omega)
      (fun u => by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using! (hM u).deriv.deriv.differentiableAt)
      (by simpa only [he₃, Nat.cast_ofNat] using h₃) hm

/-- Third derivative of the actual scalar-input cumulant generating function,
using Mathlib's moment derivative theorem rather than a formal differentiation. -/
theorem iteratedDeriv_three_cgf_scalar {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v x m : ℝ) :
    iteratedDeriv 3 (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) m =
      (∫ z, A (x + Real.sqrt v * z) ^ 3 * Real.exp (m * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1) /
        mgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) m -
      3 * ((∫ z, A (x + Real.sqrt v * z) ^ 2 * Real.exp (m * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1) /
        mgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) m) *
        deriv (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) m +
      2 * (deriv (cgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1)) m) ^ 3 := by
  let Y := fun z => A (x + Real.sqrt v * z)
  have hmem (t : ℝ) : t ∈ interior (integrableExpSet Y (gaussianReal 0 1)) := by
    rw [parisiStep_integrableExpSet hA hAm, interior_univ]
    trivial
  have hpos : mgf Y (gaussianReal 0 1) m ≠ 0 := (smoothing_integral_pos hA hAm x).ne'
  have H := ((hasDerivAt_integral_pow_mul_exp_real (hmem m) 2).div (hasDerivAt_mgf (hmem m)) hpos).sub
    (((analyticAt_cgf (hmem m)).deriv.differentiableAt.hasDerivAt).pow 2)
  have he : iteratedDeriv 2 (cgf Y (gaussianReal 0 1)) =
      fun t => (∫ z, Y z ^ 2 * Real.exp (t * Y z) ∂gaussianReal 0 1) /
        mgf Y (gaussianReal 0 1) t - (deriv (cgf Y (gaussianReal 0 1)) t) ^ 2 := by
    funext t
    exact iteratedDeriv_two_cgf (hmem t)
  have HD := H.deriv
  simp only [Pi.sub_def, Pi.div_def, Pi.pow_def] at HD
  rw [iteratedDeriv_succ, he, HD]
  change _ = _
  have he' := iteratedDeriv_two_cgf (hmem m)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he'
  rw [he', deriv_cgf (hmem m)]
  dsimp only [Y] at hpos ⊢
  simp only [show (2 + 1 : ℕ) = 3 from rfl, show (2 - 1 : ℕ) = 1 from rfl, pow_one,
    Nat.cast_ofNat]
  field_simp [hpos]
  ring_nf
  simp only [mul_comm m]

/-- A field-independent Gaussian bound for the first three centered tilted
moments on the mass/variance rectangle `[0,1] × [0,V]`. -/
noncomputable def massGaussianMomentBound (V : ℝ) : ℝ :=
  6 * Real.exp (Real.sqrt V * gAbsMoment) *
    ∫ z, Real.exp ((2 * Real.sqrt V) * |z|) ∂gaussianReal 0 1

theorem massGaussianMomentBound_nonneg (V : ℝ) : 0 ≤ massGaussianMomentBound V := by
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => (Real.exp_pos _).le)

private theorem tilt_moment_eq_ratio (A : ℝ → ℝ) (n : ℕ) (m v x : ℝ) :
    (∫ z, A (x + Real.sqrt v * z) ^ n * tiltWeight m v A x z ∂gaussianReal 0 1) =
      (∫ z, A (x + Real.sqrt v * z) ^ n * Real.exp (m * A (x + Real.sqrt v * z)) ∂gaussianReal 0 1) /
        mgf (fun z => A (x + Real.sqrt v * z)) (gaussianReal 0 1) m := by
  by_cases hm : m = 0
  · simp [hm, tiltWeight, mgf]
  · simp only [tiltWeight, if_neg hm, ← mul_div_assoc, integral_div, mgf]

/-- Centering at the spatial field gives uniform tilted moments, without any
bound on the input's additive constant or on the number of cascade levels. -/
theorem abs_centered_tilt_moment_le {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V)
    {n : ℕ} (hn : n ≤ 3) (x : ℝ) :
    |∫ z, (-A x + A (x + Real.sqrt v * z)) ^ n *
      tiltWeight m v (fun y => -A x + A y) x z ∂gaussianReal 0 1| ≤
      massGaussianMomentBound V := by
  let B : ℝ → ℝ := fun y => -A x + A y
  have hB := hasLinearGrowth_const_add (-A x) hA
  have hBm : Measurable B := measurable_const.add hAm
  have hBL : ∀ y y', |B y - B y'| ≤ 1 * |y - y'| := by
    intro y y'
    simpa only [B, neg_add_cancel_left, add_sub_add_left_eq_sub, one_mul] using hLip y y'
  have hdev (z : ℝ) : |B (x + Real.sqrt v * z)| ≤ Real.sqrt V * |z| := by
    have HH := hLip (x + Real.sqrt v * z) x
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg v)] at HH
    have HH' : |B (x + Real.sqrt v * z)| ≤ Real.sqrt v * |z| := by
      simpa only [B, neg_add_eq_sub] using HH
    exact HH'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv.2) (abs_nonneg z))
  have hc : |m| * 1 * Real.sqrt v ≤ Real.sqrt V := by
    rw [abs_of_nonneg hm.1, mul_one]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg v) hm.2).trans (Real.sqrt_le_sqrt hv.2)
  have hw (z : ℝ) : tiltWeight m v B x z ≤
      Real.exp (Real.sqrt V * gAbsMoment) * Real.exp (Real.sqrt V * |z|) := by
    exact (tiltWeight_le zero_le_one hBL hB hBm x z).trans
      (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc gAbsMoment_nonneg))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (abs_nonneg z)))
        (Real.exp_pos _).le (Real.exp_pos _).le)
  have hfac : (Nat.factorial n : ℝ) ≤ 6 := by interval_cases n <;> norm_num
  have hpow (z : ℝ) : |B (x + Real.sqrt v * z)| ^ n ≤ 6 * Real.exp (Real.sqrt V * |z|) := by
    have H := Real.pow_div_factorial_le_exp |B (x + Real.sqrt v * z)| (abs_nonneg _) n
    have hnf : (0 : ℝ) < Nat.factorial n := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have H' := (div_le_iff₀ hnf).mp H
    exact H'.trans (by
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul hfac (Real.exp_le_exp.mpr (hdev z)) (Real.exp_pos _).le (by norm_num))
  have hb (z : ℝ) : |B (x + Real.sqrt v * z) ^ n * tiltWeight m v B x z| ≤
      (6 * Real.exp (Real.sqrt V * gAbsMoment)) * Real.exp ((2 * Real.sqrt V) * |z|) := by
    rw [abs_mul, abs_pow, abs_of_nonneg (tiltWeight_nonneg hB hBm x z)]
    calc
      _ ≤ (6 * Real.exp (Real.sqrt V * |z|)) *
          (Real.exp (Real.sqrt V * gAbsMoment) * Real.exp (Real.sqrt V * |z|)) :=
        mul_le_mul (hpow z) (hw z) (tiltWeight_nonneg hB hBm x z) (by positivity)
      _ = _ := by rw [show (2 * Real.sqrt V) * |z| = Real.sqrt V * |z| + Real.sqrt V * |z| by ring,
        Real.exp_add]; ring
  have hi := (integrable_exp_abs_mul_stdGaussian (2 * Real.sqrt V)).const_mul
    (6 * Real.exp (Real.sqrt V * gAbsMoment))
  have hmeas : Measurable (fun z => B (x + Real.sqrt v * z) ^ n * tiltWeight m v B x z) :=
    ((hBm.comp (by fun_prop)).pow_const n).mul (measurable_tiltWeight hBm x)
  have hI : Integrable (fun z => B (x + Real.sqrt v * z) ^ n * tiltWeight m v B x z)
      (gaussianReal 0 1) := hi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall hb)
  calc
    _ ≤ ∫ z, |B (x + Real.sqrt v * z) ^ n * tiltWeight m v B x z| ∂gaussianReal 0 1 :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, (6 * Real.exp (Real.sqrt V * gAbsMoment)) * Real.exp ((2 * Real.sqrt V) * |z|)
        ∂gaussianReal 0 1 := integral_mono hI.abs hi hb
    _ = massGaussianMomentBound V := by rw [integral_const_mul]; rfl

private theorem centered_cumulant_bounds {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x : ℝ) :
    |iteratedDeriv 2 (cgf (fun z => -A x + A (x + Real.sqrt v * z)) (gaussianReal 0 1)) m| ≤
        massGaussianMomentBound V + massGaussianMomentBound V ^ 2 ∧
      |iteratedDeriv 3 (cgf (fun z => -A x + A (x + Real.sqrt v * z)) (gaussianReal 0 1)) m| ≤
        massGaussianMomentBound V + 3 * massGaussianMomentBound V ^ 2 +
          2 * massGaussianMomentBound V ^ 3 := by
  let B : ℝ → ℝ := fun y => -A x + A y
  let J (n : ℕ) := ∫ z, B (x + Real.sqrt v * z) ^ n * tiltWeight m v B x z ∂gaussianReal 0 1
  let C := massGaussianMomentBound V
  have hC : 0 ≤ C := massGaussianMomentBound_nonneg V
  have hb (n : ℕ) (hn : n ≤ 3) : |J n| ≤ C := abs_centered_tilt_moment_le hA hAm hLip hm hv hn x
  have hB := hasLinearGrowth_const_add (-A x) hA
  have hBm : Measurable B := measurable_const.add hAm
  have hmem : m ∈ interior (integrableExpSet (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) := by
    rw [parisiStep_integrableExpSet hB hBm, interior_univ]
    trivial
  have h₁ : deriv (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) m = J 1 := by
    dsimp only [J]
    rw [deriv_cgf hmem, tilt_moment_eq_ratio]
    simp only [pow_one]
  have h₂ : iteratedDeriv 2 (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) m =
      J 2 - (J 1) ^ 2 := by
    rw [iteratedDeriv_two_cgf hmem, h₁]
    simp only [J, tilt_moment_eq_ratio]
  have h₃ : iteratedDeriv 3 (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) m =
      J 3 - 3 * J 2 * J 1 + 2 * (J 1) ^ 3 := by
    rw [iteratedDeriv_three_cgf_scalar hB hBm, h₁]
    simp only [J]
    simp only [tilt_moment_eq_ratio]
    rfl
  change |iteratedDeriv 2 (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) m| ≤ C + C ^ 2 ∧
    |iteratedDeriv 3 (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) m| ≤ C + 3 * C ^ 2 + 2 * C ^ 3
  rw [h₂, h₃]
  constructor
  · calc
      _ ≤ |J 2| + |(J 1) ^ 2| := abs_sub _ _
      _ ≤ C + C ^ 2 := by rw [abs_pow]; gcongr; exacts [hb 2 (by omega), hb 1 (by omega)]
  · calc
      _ ≤ |J 3| + |3 * J 2 * J 1| + |2 * (J 1) ^ 3| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = |J 3| + 3 * |J 2| * |J 1| + 2 * |J 1| ^ 3 := by
        norm_num only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ C + 3 * C * C + 2 * C ^ 3 := by
        gcongr
        all_goals first | exact hC | exact hb 1 (by omega) | exact hb 2 (by omega) | exact hb 3 (by omega)
      _ = C + 3 * C ^ 2 + 2 * C ^ 3 := by ring

/-- Explicit uniform first-derivative constant. -/
noncomputable def parisiMassFirstBound (V : ℝ) : ℝ :=
  (massGaussianMomentBound V + massGaussianMomentBound V ^ 2) / 2

/-- Explicit uniform second-derivative constant. -/
noncomputable def parisiMassSecondBound (V : ℝ) : ℝ :=
  (massGaussianMomentBound V + 3 * massGaussianMomentBound V ^ 2 +
    2 * massGaussianMomentBound V ^ 3) / 3

theorem parisiMassFirstBound_nonneg (V : ℝ) : 0 ≤ parisiMassFirstBound V :=
  div_nonneg (add_nonneg (massGaussianMomentBound_nonneg V) (sq_nonneg _)) (by norm_num)

theorem parisiMassSecondBound_nonneg (V : ℝ) : 0 ≤ parisiMassSecondBound V := by
  have H := massGaussianMomentBound_nonneg V
  unfold parisiMassSecondBound
  positivity

/-- Actual scalar mass derivatives are uniformly bounded through mass zero.
The constants depend only on the variance cap, not the field, additive input
constant, or recursion depth. The input's genuine Lipschitz/growth hypotheses
hold for every actual Parisi input. -/
theorem parisiStep_mass_derivatives_uniform {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A)
    (hLip : ∀ x y, |A x - A y| ≤ |x - y|)
    {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x : ℝ) :
    |deriv (fun a => parisiStep a v A x) m| ≤ parisiMassFirstBound V ∧
      |iteratedDeriv 2 (fun a => parisiStep a v A x) m| ≤ parisiMassSecondBound V := by
  let B : ℝ → ℝ := fun y => -A x + A y
  have hB := hasLinearGrowth_const_add (-A x) hA
  have hBm : Measurable B := measurable_const.add hAm
  have he : (fun u => u * parisiStep u v B x) =
      cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1) := by
    funext u
    have hs := congrFun (parisiStep_eq_dslope_cgf hB hBm v x) u
    rw [hs]
    simpa only [sub_zero, smul_eq_mul, cgf_zero] using
      sub_smul_dslope (cgf (fun z => B (x + Real.sqrt v * z)) (gaussianReal 0 1)) 0 u
  have H := mass_derivatives_of_cumulant_bounds (fun u => analyticAt_parisiStep_mass hB hBm v x u)
    (by rw [he]; exact fun u hu => (centered_cumulant_bounds hA hAm hLip hu hv x).1)
    (by rw [he]; exact fun u hu => (centered_cumulant_bounds hA hAm hLip hu hv x).2) hm
  have heB : (fun u => parisiStep u v B x) = fun u => -A x + parisiStep u v A x := by
    funext u
    exact parisiStep_const_add (-A x) u v hA hAm x
  rw [heB, deriv_const_add, iteratedDeriv_const_add (by omega)] at H
  exact H

/-- The zero-inclusive uniform estimate specialized to every actual Parisi
recursion level; no analytic or moment assumptions remain to discharge. -/
theorem parisiStep_parisiF_mass_derivatives_uniform {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) {m v V : ℝ} (hm : m ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 V) (x : ℝ) :
    |deriv (fun a => parisiStep a v (parisiF s β j) x) m| ≤ parisiMassFirstBound V ∧
      |iteratedDeriv 2 (fun a => parisiStep a v (parisiF s β j) x) m| ≤ parisiMassSecondBound V :=
  parisiStep_mass_derivatives_uniform (parisiF_hasLinearGrowth s β j) (parisiF_measurable s β j)
    (parisiF_lipschitz s β j) hm hv x

end SpinGlass.Targets
