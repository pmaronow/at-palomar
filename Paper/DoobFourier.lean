module

public import Paper.StateDiffusion
public import Paper.Hyperbolic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

@[expose] public section

/-!
# Explicit Fourier solutions for the cosh Doob generator

The real and imaginary Fourier modes have elementary closed forms. Their
actual time and first/second spatial derivatives satisfy the backward equation
for the generator `(1/2)∂xx + tanh(x)∂x` after the physical β² time rescaling.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace Paper

@[fun_prop] theorem doobFourier_continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)

@[fun_prop] theorem doobFourier_continuous_sech : Continuous sech := by
  unfold sech
  exact continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- Real Fourier mode of the cosh transform at remaining variance `ell`. -/
def doobFourierCos (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (Real.cos (ξ * x) * Real.cos (ξ * ell) -
      Real.tanh x * Real.sin (ξ * x) * Real.sin (ξ * ell))

/-- Imaginary Fourier mode of the cosh transform. -/
def doobFourierSin (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (Real.sin (ξ * x) * Real.cos (ξ * ell) +
      Real.tanh x * Real.cos (ξ * x) * Real.sin (ξ * ell))

def doobFourierCosDx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ * Real.sin (ξ * x) * Real.cos (ξ * ell) -
      (sech x ^ 2 * Real.sin (ξ * x) + ξ * Real.tanh x * Real.cos (ξ * x)) * Real.sin (ξ * ell))

def doobFourierSinDx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (ξ * Real.cos (ξ * x) * Real.cos (ξ * ell) +
      (sech x ^ 2 * Real.cos (ξ * x) - ξ * Real.tanh x * Real.sin (ξ * x)) * Real.sin (ξ * ell))

def doobFourierCosDxx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ ^ 2 * Real.cos (ξ * x) * Real.cos (ξ * ell) -
      ((-2 * Real.tanh x * sech x ^ 2 - ξ ^ 2 * Real.tanh x) * Real.sin (ξ * x) +
        2 * ξ * sech x ^ 2 * Real.cos (ξ * x)) * Real.sin (ξ * ell))

def doobFourierSinDxx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ ^ 2 * Real.sin (ξ * x) * Real.cos (ξ * ell) +
      ((-2 * Real.tanh x * sech x ^ 2 - ξ ^ 2 * Real.tanh x) * Real.cos (ξ * x) -
        2 * ξ * sech x ^ 2 * Real.sin (ξ * x)) * Real.sin (ξ * ell))

def doobFourierCosDell (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-(ξ ^ 2) / 2 * (Real.cos (ξ * x) * Real.cos (ξ * ell) -
      Real.tanh x * Real.sin (ξ * x) * Real.sin (ξ * ell)) -
      ξ * Real.cos (ξ * x) * Real.sin (ξ * ell) -
      ξ * Real.tanh x * Real.sin (ξ * x) * Real.cos (ξ * ell))

def doobFourierSinDell (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-(ξ ^ 2) / 2 * (Real.sin (ξ * x) * Real.cos (ξ * ell) +
      Real.tanh x * Real.cos (ξ * x) * Real.sin (ξ * ell)) -
      ξ * Real.sin (ξ * x) * Real.sin (ξ * ell) +
      ξ * Real.tanh x * Real.cos (ξ * x) * Real.cos (ξ * ell))

private theorem fourierCos_deriv (ξ x : ℝ) :
    HasDerivAt (fun y => Real.cos (ξ * y)) (-ξ * Real.sin (ξ * x)) x := by
  convert (Real.hasDerivAt_cos (ξ * x)).comp x ((hasDerivAt_id x).const_mul ξ) using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

private theorem fourierSin_deriv (ξ x : ℝ) :
    HasDerivAt (fun y => Real.sin (ξ * y)) (ξ * Real.cos (ξ * x)) x := by
  convert (Real.hasDerivAt_sin (ξ * x)).comp x ((hasDerivAt_id x).const_mul ξ) using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

/-- Actual first spatial derivative of the real Fourier mode. -/
theorem hasDerivAt_doobFourierCos_spatial (ξ ell x : ℝ) :
    HasDerivAt (doobFourierCos ξ ell) (doobFourierCosDx ξ ell x) x := by
  have hd := ((fourierCos_deriv ξ x).mul_const (Real.cos (ξ * ell))).sub
    (((hasDerivAt_tanh x).mul (fourierSin_deriv ξ x)).mul_const (Real.sin (ξ * ell)))
  convert hd.const_mul (Real.exp (-(ξ ^ 2 * ell) / 2)) using 1 <;>
    first | (funext y; simp only [doobFourierCos, doobFourierCosDx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierCos, doobFourierCosDx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

theorem hasDerivAt_doobFourierSin_spatial (ξ ell x : ℝ) :
    HasDerivAt (doobFourierSin ξ ell) (doobFourierSinDx ξ ell x) x := by
  have hd := ((fourierSin_deriv ξ x).mul_const (Real.cos (ξ * ell))).add
    (((hasDerivAt_tanh x).mul (fourierCos_deriv ξ x)).mul_const (Real.sin (ξ * ell)))
  convert hd.const_mul (Real.exp (-(ξ ^ 2 * ell) / 2)) using 1 <;>
    first | (funext y; simp only [doobFourierSin, doobFourierSinDx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierSin, doobFourierSinDx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

/-- Actual second spatial derivative of the real Fourier mode. -/
theorem hasDerivAt_doobFourierCosDx (ξ ell x : ℝ) :
    HasDerivAt (doobFourierCosDx ξ ell) (doobFourierCosDxx ξ ell x) x := by
  have hd1 := ((fourierSin_deriv ξ x).const_mul (-ξ)).mul_const (Real.cos (ξ * ell))
  have hd2 := ((hasDerivAt_sech_sq x).mul (fourierSin_deriv ξ x)).add
    (((hasDerivAt_tanh x).mul (fourierCos_deriv ξ x)).const_mul ξ)
  convert (hd1.sub (hd2.mul_const (Real.sin (ξ * ell)))).const_mul
    (Real.exp (-(ξ ^ 2 * ell) / 2)) using 1 <;>
    first | (funext y; simp only [doobFourierCosDx, doobFourierCosDxx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierCosDx, doobFourierCosDxx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

theorem hasDerivAt_doobFourierSinDx (ξ ell x : ℝ) :
    HasDerivAt (doobFourierSinDx ξ ell) (doobFourierSinDxx ξ ell x) x := by
  have hd1 := ((fourierCos_deriv ξ x).const_mul ξ).mul_const (Real.cos (ξ * ell))
  have hd2 := ((hasDerivAt_sech_sq x).mul (fourierCos_deriv ξ x)).sub
    (((hasDerivAt_tanh x).mul (fourierSin_deriv ξ x)).const_mul ξ)
  convert (hd1.add (hd2.mul_const (Real.sin (ξ * ell)))).const_mul
    (Real.exp (-(ξ ^ 2 * ell) / 2)) using 1 <;>
    first | (funext y; simp only [doobFourierSinDx, doobFourierSinDxx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierSinDx, doobFourierSinDxx, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

private theorem fourierFactor_deriv (ξ ell : ℝ) :
    HasDerivAt (fun u => Real.exp (-(ξ ^ 2 * u) / 2))
      (Real.exp (-(ξ ^ 2 * ell) / 2) * (-(ξ ^ 2) / 2)) ell := by
  convert (((hasDerivAt_id ell).const_mul (-(ξ ^ 2))).div_const 2).exp using 1
  · funext u
    simp only [id_eq, neg_mul]
  · simp only [id_eq, neg_mul]
    ring

/-- Actual remaining-variance derivative of the real Fourier mode. -/
theorem hasDerivAt_doobFourierCos_variance (ξ ell x : ℝ) :
    HasDerivAt (fun u => doobFourierCos ξ u x) (doobFourierCosDell ξ ell x) ell := by
  have hd := ((fourierCos_deriv ξ ell).const_mul (Real.cos (ξ * x))).sub
    ((fourierSin_deriv ξ ell).const_mul (Real.tanh x * Real.sin (ξ * x)))
  convert (fourierFactor_deriv ξ ell).mul hd using 1 <;>
    first | (funext y; simp only [doobFourierCos, doobFourierCosDell, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierCos, doobFourierCosDell, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

theorem hasDerivAt_doobFourierSin_variance (ξ ell x : ℝ) :
    HasDerivAt (fun u => doobFourierSin ξ u x) (doobFourierSinDell ξ ell x) ell := by
  have hd := ((fourierCos_deriv ξ ell).const_mul (Real.sin (ξ * x))).add
    ((fourierSin_deriv ξ ell).const_mul (Real.tanh x * Real.cos (ξ * x)))
  convert (fourierFactor_deriv ξ ell).mul hd using 1 <;>
    first | (funext y; simp only [doobFourierSin, doobFourierSinDell, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring) |
      (simp only [doobFourierSin, doobFourierSinDell, Function.comp_def, id_eq, Pi.mul_apply, Pi.sub_apply, Pi.add_apply] <;> ring)

/-- Exact generator cancellation for the real Fourier mode. -/
theorem doobFourierCos_generator (ξ ell x : ℝ) :
    doobFourierCosDell ξ ell x = doobFourierCosDxx ξ ell x / 2 +
      Real.tanh x * doobFourierCosDx ξ ell x := by
  dsimp [doobFourierCosDell, doobFourierCosDxx, doobFourierCosDx]
  linear_combination Real.exp (-(ξ ^ 2 * ell) / 2) * ξ * Real.cos (ξ * x) *
    Real.sin (ξ * ell) * tanh_sq_add_sech_sq x

theorem doobFourierSin_generator (ξ ell x : ℝ) :
    doobFourierSinDell ξ ell x = doobFourierSinDxx ξ ell x / 2 +
      Real.tanh x * doobFourierSinDx ξ ell x := by
  dsimp [doobFourierSinDell, doobFourierSinDxx, doobFourierSinDx]
  linear_combination Real.exp (-(ξ ^ 2 * ell) / 2) * ξ * Real.sin (ξ * x) *
    Real.sin (ξ * ell) * tanh_sq_add_sech_sq x

/-- The real backward Fourier solution in physical time. -/
def backwardDoobCos (β T ξ t x : ℝ) : ℝ := doobFourierCos ξ (β ^ 2 * (T - t)) x

/-- The imaginary backward Fourier solution in physical time. -/
def backwardDoobSin (β T ξ t x : ℝ) : ℝ := doobFourierSin ξ (β ^ 2 * (T - t)) x

@[simp] theorem backwardDoobCos_terminal (β T ξ x : ℝ) : backwardDoobCos β T ξ T x = Real.cos (ξ * x) := by
  simp [backwardDoobCos, doobFourierCos]

@[simp] theorem backwardDoobSin_terminal (β T ξ x : ℝ) : backwardDoobSin β T ξ T x = Real.sin (ξ * x) := by
  simp [backwardDoobSin, doobFourierSin]

theorem hasDerivAt_backwardDoobCos_time (β T ξ t x : ℝ) :
    HasDerivAt (fun s => backwardDoobCos β T ξ s x)
      (-(β ^ 2) * doobFourierCosDell ξ (β ^ 2 * (T - t)) x) t := by
  convert (hasDerivAt_doobFourierCos_variance ξ (β ^ 2 * (T - t)) x).comp t
    (((hasDerivAt_id t).const_sub T).const_mul (β ^ 2)) using 1
  · rfl
  · ring

theorem hasDerivAt_backwardDoobSin_time (β T ξ t x : ℝ) :
    HasDerivAt (fun s => backwardDoobSin β T ξ s x)
      (-(β ^ 2) * doobFourierSinDell ξ (β ^ 2 * (T - t)) x) t := by
  convert (hasDerivAt_doobFourierSin_variance ξ (β ^ 2 * (T - t)) x).comp t
    (((hasDerivAt_id t).const_sub T).const_mul (β ^ 2)) using 1
  · rfl
  · ring

/-- Exact backward PDE in actual derivatives for the real Fourier mode. -/
theorem backwardDoobCos_pde (β T ξ t x : ℝ) :
    deriv (fun s => backwardDoobCos β T ξ s x) t +
      β ^ 2 * Real.tanh x * deriv (backwardDoobCos β T ξ t) x +
      β ^ 2 / 2 * deriv (deriv (backwardDoobCos β T ξ t)) x = 0 := by
  rw [(hasDerivAt_backwardDoobCos_time β T ξ t x).deriv]
  have hder : deriv (backwardDoobCos β T ξ t) = doobFourierCosDx ξ (β ^ 2 * (T - t)) :=
    funext (fun x => (hasDerivAt_doobFourierCos_spatial ξ (β ^ 2 * (T - t)) x).deriv)
  rw [hder, (hasDerivAt_doobFourierCosDx ξ (β ^ 2 * (T - t)) x).deriv,
    doobFourierCos_generator]
  ring

theorem backwardDoobSin_pde (β T ξ t x : ℝ) :
    deriv (fun s => backwardDoobSin β T ξ s x) t +
      β ^ 2 * Real.tanh x * deriv (backwardDoobSin β T ξ t) x +
      β ^ 2 / 2 * deriv (deriv (backwardDoobSin β T ξ t)) x = 0 := by
  rw [(hasDerivAt_backwardDoobSin_time β T ξ t x).deriv]
  have hder : deriv (backwardDoobSin β T ξ t) = doobFourierSinDx ξ (β ^ 2 * (T - t)) :=
    funext (fun x => (hasDerivAt_doobFourierSin_spatial ξ (β ^ 2 * (T - t)) x).deriv)
  rw [hder, (hasDerivAt_doobFourierSinDx ξ (β ^ 2 * (T - t)) x).deriv,
    doobFourierSin_generator]
  ring

@[fun_prop] theorem doobFourier_contDiff_tanh {n : ℕ∞ω} : ContDiff ℝ n Real.tanh := by
  have he : Real.tanh = (fun x => Real.sinh x / Real.cosh x) := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

@[fun_prop] theorem doobFourier_contDiff_sech {n : ℕ∞ω} : ContDiff ℝ n sech := by
  unfold sech
  exact contDiff_const.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

/-- The Fourier backward solutions are smooth jointly in time and space. -/
theorem contDiff_backwardDoobCos_joint (β T ξ : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ => backwardDoobCos β T ξ p.1 p.2) := by
  unfold backwardDoobCos doobFourierCos
  fun_prop

theorem contDiff_backwardDoobSin_joint (β T ξ : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ => backwardDoobSin β T ξ p.1 p.2) := by
  unfold backwardDoobSin doobFourierSin
  fun_prop

theorem contDiff_backwardDoobCos_spatial (β T ξ t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (backwardDoobCos β T ξ t) := by
  unfold backwardDoobCos doobFourierCos
  fun_prop

theorem contDiff_backwardDoobSin_spatial (β T ξ t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (backwardDoobSin β T ξ t) := by
  unfold backwardDoobSin doobFourierSin
  fun_prop

theorem deriv_backwardDoobCos_spatial (β T ξ t x : ℝ) :
    deriv (backwardDoobCos β T ξ t) x = doobFourierCosDx ξ (β ^ 2 * (T - t)) x :=
  (hasDerivAt_doobFourierCos_spatial ξ _ x).deriv

theorem deriv_backwardDoobSin_spatial (β T ξ t x : ℝ) :
    deriv (backwardDoobSin β T ξ t) x = doobFourierSinDx ξ (β ^ 2 * (T - t)) x :=
  (hasDerivAt_doobFourierSin_spatial ξ _ x).deriv

theorem deriv_backwardDoobCos_spatial_second (β T ξ t x : ℝ) :
    deriv (deriv (backwardDoobCos β T ξ t)) x = doobFourierCosDxx ξ (β ^ 2 * (T - t)) x := by
  have he : deriv (backwardDoobCos β T ξ t) = doobFourierCosDx ξ (β ^ 2 * (T - t)) :=
    funext (deriv_backwardDoobCos_spatial β T ξ t)
  rw [he, (hasDerivAt_doobFourierCosDx ξ _ x).deriv]

theorem deriv_backwardDoobSin_spatial_second (β T ξ t x : ℝ) :
    deriv (deriv (backwardDoobSin β T ξ t)) x = doobFourierSinDxx ξ (β ^ 2 * (T - t)) x := by
  have he : deriv (backwardDoobSin β T ξ t) = doobFourierSinDx ξ (β ^ 2 * (T - t)) :=
    funext (deriv_backwardDoobSin_spatial β T ξ t)
  rw [he, (hasDerivAt_doobFourierSinDx ξ _ x).deriv]

theorem continuous_backwardDoobCos_timeDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => backwardDoobCos β T ξ s p.2) p.1) := by
  simp_rw [(hasDerivAt_backwardDoobCos_time β T ξ _ _).deriv]
  unfold doobFourierCosDell
  fun_prop

theorem continuous_backwardDoobSin_timeDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => backwardDoobSin β T ξ s p.2) p.1) := by
  simp_rw [(hasDerivAt_backwardDoobSin_time β T ξ _ _).deriv]
  unfold doobFourierSinDell
  fun_prop

theorem continuous_backwardDoobCos_spaceDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (backwardDoobCos β T ξ p.1) p.2) := by
  simp_rw [deriv_backwardDoobCos_spatial]
  unfold doobFourierCosDx
  fun_prop

theorem continuous_backwardDoobSin_spaceDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (backwardDoobSin β T ξ p.1) p.2) := by
  simp_rw [deriv_backwardDoobSin_spatial]
  unfold doobFourierSinDx
  fun_prop

theorem continuous_backwardDoobCos_spaceSecondDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (backwardDoobCos β T ξ p.1)) p.2) := by
  simp_rw [deriv_backwardDoobCos_spatial_second]
  unfold doobFourierCosDxx
  fun_prop

theorem continuous_backwardDoobSin_spaceSecondDerivative (β T ξ : ℝ) :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (backwardDoobSin β T ξ p.1)) p.2) := by
  simp_rw [deriv_backwardDoobSin_spatial_second]
  unfold doobFourierSinDxx
  fun_prop

private theorem doobFourier_norm_cos_le (y : ℝ) : ‖Real.cos y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one y

private theorem doobFourier_norm_sin_le (y : ℝ) : ‖Real.sin y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one y

private theorem doobFourier_norm_tanh_le (y : ℝ) : ‖Real.tanh y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le

private theorem doobFourier_factor_bound (ξ ell : ℝ) (hell : 0 ≤ ell) :
    ‖Real.exp (-(ξ ^ 2 * ell) / 2)‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg ξ) hell)) (by norm_num)

private theorem norm_prod_le_one {u v : ℝ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖u * v‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hu hv (norm_nonneg _) zero_le_one

/-- A global spatial bound for the Fourier modes on nonnegative remaining variance. -/
theorem norm_doobFourierCos_le_two (ξ ell x : ℝ) (hell : 0 ≤ ell) : ‖doobFourierCos ξ ell x‖ ≤ 2 := by
  have h1 := norm_prod_le_one (doobFourier_norm_cos_le (ξ * x)) (doobFourier_norm_cos_le (ξ * ell))
  have h2 := norm_prod_le_one
    (norm_prod_le_one (doobFourier_norm_tanh_le x) (doobFourier_norm_sin_le (ξ * x)))
    (doobFourier_norm_sin_le (ξ * ell))
  unfold doobFourierCos
  rw [norm_mul]
  have hb := (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hmul := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simpa only [one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using hmul

theorem norm_doobFourierSin_le_two (ξ ell x : ℝ) (hell : 0 ≤ ell) : ‖doobFourierSin ξ ell x‖ ≤ 2 := by
  have h1 := norm_prod_le_one (doobFourier_norm_sin_le (ξ * x)) (doobFourier_norm_cos_le (ξ * ell))
  have h2 := norm_prod_le_one
    (norm_prod_le_one (doobFourier_norm_tanh_le x) (doobFourier_norm_cos_le (ξ * x)))
    (doobFourier_norm_sin_le (ξ * ell))
  unfold doobFourierSin
  rw [norm_mul]
  have hb := (norm_add_le _ _).trans (add_le_add h1 h2)
  have hmul := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simpa only [one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using hmul

/-- The spatial derivatives are bounded uniformly in space and nonnegative variance. -/
theorem norm_doobFourierCosDx_le (ξ ell x : ℝ) (hell : 0 ≤ ell) :
    ‖doobFourierCosDx ξ ell x‖ ≤ 1 + 2 * |ξ| := by
  have ht : ‖Real.tanh x‖ ≤ 1 := doobFourier_norm_tanh_le x
  have hs : ‖sech x ^ 2‖ ≤ 1 := by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one x
  have h1 : ‖-ξ * Real.sin (ξ * x) * Real.cos (ξ * ell)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact doobFourier_norm_sin_le _ | exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h2 : ‖sech x ^ 2 * Real.sin (ξ * x)‖ ≤ 1 := norm_prod_le_one hs (doobFourier_norm_sin_le _)
  have h3 : ‖ξ * Real.tanh x * Real.cos (ξ * x)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact ht | exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h4 : ‖(sech x ^ 2 * Real.sin (ξ * x) + ξ * Real.tanh x * Real.cos (ξ * x)) * Real.sin (ξ * ell)‖ ≤
      1 + |ξ| := by
    rw [norm_mul]
    calc
      _ ≤ (1 + |ξ|) * 1 := mul_le_mul ((norm_add_le _ _).trans (add_le_add h2 h3))
        (doobFourier_norm_sin_le _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold doobFourierCosDx
  rw [norm_mul]
  have hb := (norm_sub_le _ _).trans (add_le_add h1 h4)
  have hm := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simp only [one_mul] at hm
  linarith

theorem norm_doobFourierSinDx_le (ξ ell x : ℝ) (hell : 0 ≤ ell) :
    ‖doobFourierSinDx ξ ell x‖ ≤ 1 + 2 * |ξ| := by
  have ht : ‖Real.tanh x‖ ≤ 1 := doobFourier_norm_tanh_le x
  have hs : ‖sech x ^ 2‖ ≤ 1 := by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one x
  have h1 : ‖ξ * Real.cos (ξ * x) * Real.cos (ξ * ell)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h2 : ‖sech x ^ 2 * Real.cos (ξ * x)‖ ≤ 1 := norm_prod_le_one hs (doobFourier_norm_cos_le _)
  have h3 : ‖ξ * Real.tanh x * Real.sin (ξ * x)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact ht | exact doobFourier_norm_sin_le _
      _ = _ := by ring
  have h4 : ‖(sech x ^ 2 * Real.cos (ξ * x) - ξ * Real.tanh x * Real.sin (ξ * x)) * Real.sin (ξ * ell)‖ ≤
      1 + |ξ| := by
    rw [norm_mul]
    calc
      _ ≤ (1 + |ξ|) * 1 := mul_le_mul ((norm_sub_le _ _).trans (add_le_add h2 h3))
        (doobFourier_norm_sin_le _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold doobFourierSinDx
  rw [norm_mul]
  have hb := (norm_add_le _ _).trans (add_le_add h1 h4)
  have hm := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simp only [one_mul] at hm
  linarith

theorem norm_backwardDoobCos_le (β T ξ t x : ℝ) (ht : t ≤ T) : ‖backwardDoobCos β T ξ t x‖ ≤ 2 :=
  norm_doobFourierCos_le_two ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

theorem norm_backwardDoobSin_le (β T ξ t x : ℝ) (ht : t ≤ T) : ‖backwardDoobSin β T ξ t x‖ ≤ 2 :=
  norm_doobFourierSin_le_two ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

theorem norm_backwardDoobCos_spaceDerivative_le (β T ξ t x : ℝ) (ht : t ≤ T) :
    ‖deriv (backwardDoobCos β T ξ t) x‖ ≤ 1 + 2 * |ξ| := by
  rw [deriv_backwardDoobCos_spatial]
  exact norm_doobFourierCosDx_le ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

theorem norm_backwardDoobSin_spaceDerivative_le (β T ξ t x : ℝ) (ht : t ≤ T) :
    ‖deriv (backwardDoobSin β T ξ t) x‖ ≤ 1 + 2 * |ξ| := by
  rw [deriv_backwardDoobSin_spatial]
  exact norm_doobFourierSinDx_le ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

private theorem int_char (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with y
  simpa only [← Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (ξ * y)).le

theorem gaussianIntegral_cos (μ ξ : ℝ) (v : ℝ≥0) :
    (∫ y, Real.cos (ξ * y) ∂gaussianReal μ v) =
      Real.exp (-(v : ℝ) * ξ ^ 2 / 2) * Real.cos (ξ * μ) := by
  have hr := congrArg (RCLike.re : ℂ → ℝ) (charFun_gaussianReal (μ := μ) (v := v) ξ)
  rw [charFun_apply_real, ← integral_re (int_char μ ξ v)] at hr
  simpa [Complex.exp_re, ← Complex.ofReal_pow, neg_div] using hr

theorem gaussianIntegral_sin (μ ξ : ℝ) (v : ℝ≥0) :
    (∫ y, Real.sin (ξ * y) ∂gaussianReal μ v) =
      Real.exp (-(v : ℝ) * ξ ^ 2 / 2) * Real.sin (ξ * μ) := by
  have hr := congrArg (RCLike.im : ℂ → ℝ) (charFun_gaussianReal (μ := μ) (v := v) ξ)
  rw [charFun_apply_real, ← integral_im (int_char μ ξ v)] at hr
  simpa [Complex.exp_im, ← Complex.ofReal_pow, neg_div] using hr
theorem integral_doobOperator_mixture (v : ℝ≥0) (x : ℝ) (ψ : ℝ → ℝ)
    (hp : Integrable ψ (gaussianReal (x + (v : ℝ)) v))
    (hn : Integrable ψ (gaussianReal (x - (v : ℝ)) v)) :
    doobOperator v ψ x =
      positiveDriftWeight x * (∫ y, ψ y ∂gaussianReal (x + (v : ℝ)) v) +
      negativeDriftWeight x * (∫ y, ψ y ∂gaussianReal (x - (v : ℝ)) v) := by
  rw [← integral_coshStateKernel, coshStateKernel_gaussian_mixture,
    integral_add_measure (hp.smul_measure ENNReal.ofReal_ne_top)
      (hn.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  obtain ⟨hp0, hn0⟩ := driftWeights_nonneg x
  rw [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hn0, smul_eq_mul, smul_eq_mul]

private theorem integral_gaussian_cos_integrable (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y => Real.cos (ξ * y)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * y))

private theorem integral_gaussian_sin_integrable (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y => Real.sin (ξ * y)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * y))

theorem driftWeights_sub (x : ℝ) : positiveDriftWeight x - negativeDriftWeight x = Real.tanh x := by
  unfold positiveDriftWeight negativeDriftWeight
  rw [← sub_div, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
  field_simp

/-- The actual cosh-transform expectation of a real Fourier mode. -/
theorem doobOperator_cos (v : ℝ≥0) (x ξ : ℝ) :
    doobOperator v (fun y => Real.cos (ξ * y)) x = doobFourierCos ξ (v : ℝ) x := by
  rw [integral_doobOperator_mixture v x _ (integral_gaussian_cos_integrable _ _ _)
    (integral_gaussian_cos_integrable _ _ _), gaussianIntegral_cos, gaussianIntegral_cos]
  unfold doobFourierCos
  rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  have he : -(v : ℝ) * ξ ^ 2 / 2 = -(ξ ^ 2 * (v : ℝ)) / 2 := by ring
  rw [he]
  have hsum := driftWeights_sum x
  have hdiff := driftWeights_sub x
  linear_combination Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.cos (ξ * x) * Real.cos (ξ * (v : ℝ)) * hsum -
    Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.sin (ξ * x) * Real.sin (ξ * (v : ℝ)) * hdiff

/-- The actual cosh-transform expectation of an imaginary Fourier mode. -/
theorem doobOperator_sin (v : ℝ≥0) (x ξ : ℝ) :
    doobOperator v (fun y => Real.sin (ξ * y)) x = doobFourierSin ξ (v : ℝ) x := by
  rw [integral_doobOperator_mixture v x _ (integral_gaussian_sin_integrable _ _ _)
    (integral_gaussian_sin_integrable _ _ _), gaussianIntegral_sin, gaussianIntegral_sin]
  unfold doobFourierSin
  rw [mul_add, mul_sub, Real.sin_add, Real.sin_sub]
  have he : -(v : ℝ) * ξ ^ 2 / 2 = -(ξ ^ 2 * (v : ℝ)) / 2 := by ring
  rw [he]
  have hsum := driftWeights_sum x
  have hdiff := driftWeights_sub x
  linear_combination Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.sin (ξ * x) * Real.cos (ξ * (v : ℝ)) * hsum +
    Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.cos (ξ * x) * Real.sin (ξ * (v : ℝ)) * hdiff

end Paper
