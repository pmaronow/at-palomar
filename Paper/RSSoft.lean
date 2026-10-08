module

public import Paper.RSFunctional
public import Paper.GaussianDifferentiation
public import Paper.GaussianHeat

@[expose] public section

/-!
# The explicit replica-symmetric heat solution before the interface

Both spatial derivatives and the backward heat PDE are verified for the
paper's actual Gaussian formula. Identifying this explicit formula with the
weak Parisi solution still requires the separately cited uniqueness theory.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

noncomputable def rsSoftDx (β q t x : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (x + β * Real.sqrt (q - t) * z))

noncomputable def rsSoftDxx (β q t x : ℝ) : ℝ :=
  gaussianExpectation (fun z => sech (x + β * Real.sqrt (q - t) * z) ^ 2)

 theorem integrable_gaussian_tanh_affine (x a : ℝ) :
    Integrable (fun z => Real.tanh (x + a * z)) (gaussianReal 0 1) := by
  have hc : Continuous (fun z : ℝ => x + a * z) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' (gaussian_continuous_tanh.comp hc).aestronglyMeasurable
  filter_upwards [] with z
  change |Real.tanh (x + a * z)| ≤ 1
  exact (Real.abs_tanh_lt_one _).le

 theorem hasDerivAt_rsSoftPotential_spatial (β q t x : ℝ) :
    HasDerivAt (rsSoftPotential β q t) (rsSoftDx β q t x) x := by
  have hc : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))
  have hd := hasDerivAt_gaussian_shift (fun y => Real.log (Real.cosh y)) Real.tanh
    (β * Real.sqrt (q - t)) x 1 hc gaussian_continuous_tanh
    (integrable_gaussian_logcosh_affine x (β * Real.sqrt (q - t))) hasDerivAt_log_cosh
    (fun y => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le)
  exact hd.const_add (β ^ 2 / 2 * (1 - q))

@[simp] theorem deriv_rsSoftPotential_spatial (β q t x : ℝ) :
    deriv (rsSoftPotential β q t) x = rsSoftDx β q t x :=
  (hasDerivAt_rsSoftPotential_spatial β q t x).deriv

 theorem hasDerivAt_rsSoftDx_spatial (β q t x : ℝ) :
    HasDerivAt (rsSoftDx β q t) (rsSoftDxx β q t x) x := by
  exact hasDerivAt_gaussian_shift Real.tanh (fun y => sech y ^ 2)
    (β * Real.sqrt (q - t)) x 1 gaussian_continuous_tanh (gaussian_continuous_sech.pow 2)
    (integrable_gaussian_tanh_affine x (β * Real.sqrt (q - t))) hasDerivAt_tanh
    (fun y => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one y)

@[simp] theorem deriv2_rsSoftPotential_spatial (β q t x : ℝ) :
    deriv (deriv (rsSoftPotential β q t)) x = rsSoftDxx β q t x := by
  have he : deriv (rsSoftPotential β q t) = rsSoftDx β q t := by
    ext y
    exact deriv_rsSoftPotential_spatial β q t y
  rw [he]
  exact (hasDerivAt_rsSoftDx_spatial β q t x).deriv

 theorem rsSoftDxx_pos (β q t x : ℝ) : 0 < rsSoftDxx β q t x :=
  gaussian_sech_pow_pos x (β * Real.sqrt (q - t)) 2

 theorem rsSoftDxx_le_one (β q t x : ℝ) : rsSoftDxx β q t x ≤ 1 := by
  have hi := integral_mono (integrable_gaussian_sech_pow x (β * Real.sqrt (q - t)) 2)
    (integrable_const (1 : ℝ)) (fun z => sech_sq_le_one (x + β * Real.sqrt (q - t) * z))
  simpa [rsSoftDxx, gaussianExpectation] using hi

 theorem norm_rsSoftDx_le_one (β q t x : ℝ) : ‖rsSoftDx β q t x‖ ≤ 1 := by
  have hb : ∀ᵐ z ∂gaussianReal 0 1,
      ‖Real.tanh (x + β * Real.sqrt (q - t) * z)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact (Real.abs_tanh_lt_one _).le
  simpa [rsSoftDx, gaussianExpectation] using
    norm_integral_le_of_norm_le_const hb

@[simp] theorem rsSoftDx_interface (β q x : ℝ) : rsSoftDx β q q x = Real.tanh x := by
  simp [rsSoftDx]

@[simp] theorem rsSoftDxx_interface (β q x : ℝ) : rsSoftDxx β q q x = sech x ^ 2 := by
  simp [rsSoftDxx]

 theorem rsSoftPotential_eq_variance (β q t x : ℝ) (hβ : 0 ≤ β) :
    rsSoftPotential β q t x = β ^ 2 / 2 * (1 - q) + gaussianExpectation
      (fun z => Real.log (Real.cosh (x + Real.sqrt (β ^ 2 * (q - t)) * z))) := by
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]
  rfl

 theorem hasDerivAt_rsSoftPotential_time {β q t x : ℝ} (hβ : 0 < β) (ht : t < q) :
    HasDerivAt (fun s => rsSoftPotential β q s x)
      (-(β ^ 2 / 2) * rsSoftDxx β q t x) t := by
  have hv : 0 < β ^ 2 * (q - t) := mul_pos (sq_pos_of_pos hβ) (sub_pos.mpr ht)
  have hc : Continuous (fun y : ℝ => Real.log (Real.cosh y)) :=
    Real.continuous_cosh.log (fun y => ne_of_gt (Real.cosh_pos y))
  have hd := hasDerivAt_gaussian_variance (fun y => Real.log (Real.cosh y)) Real.tanh
    (fun y => sech y ^ 2) x (β ^ 2 * (q - t)) 1 1 hv hc gaussian_continuous_tanh
    (gaussian_continuous_sech.pow 2)
    (integrable_gaussian_logcosh_affine x (Real.sqrt (β ^ 2 * (q - t))))
    hasDerivAt_log_cosh hasDerivAt_tanh
    (fun y => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le)
    (fun y => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one y)
  have hinner : HasDerivAt (fun s : ℝ => β ^ 2 * (q - s)) (-β ^ 2) t := by
    convert ((hasDerivAt_id t).const_sub q).const_mul (β ^ 2) using 1
    · ext s
      simp only [id_eq]
    · ring
  have hh := (hd.comp t hinner).const_add (β ^ 2 / 2 * (1 - q))
  convert hh using 1
  · ext s
    exact rsSoftPotential_eq_variance β q s x hβ.le
  · dsimp [rsSoftDxx]
    rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]
    ring

/-- Direct classical backward-heat PDE verification on `t<q`. -/
theorem rsSoftPotential_PDE {β q t x : ℝ} (hβ : 0 < β) (ht : t < q) :
    deriv (fun s => rsSoftPotential β q s x) t + β ^ 2 / 2 *
      deriv (deriv (rsSoftPotential β q t)) x = 0 := by
  rw [(hasDerivAt_rsSoftPotential_time hβ ht).deriv, deriv2_rsSoftPotential_spatial]
  ring

/-- Joint continuity of the actual soft spatial derivative, including `t=q`. -/
theorem continuous_rsSoftDx_joint (β q : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun p : ℝ × ℝ => rsSoftDx β q p.1 p.2) := by
  have hg := continuous_gaussian_affine_joint Real.tanh 1 gaussian_continuous_tanh
    (fun y => by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le)
  have hc : Continuous (fun p : ℝ × ℝ => (p.2, β ^ 2 * (q - p.1))) := by fun_prop
  convert hg.comp hc using 1
  ext p
  dsimp [rsSoftDx]
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]

 theorem continuous_rsSoftDxx_joint (β q : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun p : ℝ × ℝ => rsSoftDxx β q p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => (p.2, β ^ 2 * (q - p.1))) := by fun_prop
  convert (continuous_gaussian_sech_pow_joint 2).comp hc using 1
  ext p
  dsimp [rsSoftDxx]
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ]

private theorem tendsto_pair_slice {g : ℝ × ℝ → ℝ} (hg : Continuous g) (q x : ℝ) :
    Tendsto (fun t => g (t, x)) (𝓝 q) (𝓝 (g (q, x))) := by
  exact (hg.tendsto (q, x)).comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 q) (𝓝 q)).prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) (𝓝 q) (𝓝 x)))

/-- The spatial derivatives extend continuously across the interface. -/
theorem tendsto_rsSoftDx_interface (β q x : ℝ) (hβ : 0 ≤ β) :
    Tendsto (fun t => rsSoftDx β q t x) (𝓝 q) (𝓝 (Real.tanh x)) := by
  have hh := tendsto_pair_slice (continuous_rsSoftDx_joint β q hβ) q x
  rw [rsSoftDx_interface] at hh
  exact hh

 theorem tendsto_rsSoftDxx_interface (β q x : ℝ) (hβ : 0 ≤ β) :
    Tendsto (fun t => rsSoftDxx β q t x) (𝓝 q) (𝓝 (sech x ^ 2)) := by
  have hh := tendsto_pair_slice (continuous_rsSoftDxx_joint β q hβ) q x
  rw [rsSoftDxx_interface] at hh
  exact hh

end Paper
