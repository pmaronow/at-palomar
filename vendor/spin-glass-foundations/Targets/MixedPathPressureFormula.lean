module

public import Targets.MixedPathPressure
public import Targets.MixedPathDecomposition
public import Targets.MixedVariancePressure

@[expose] public section

/-!
# The averaged trace-plus-heat formula for the actual moving cascade

The proved simultaneous derivative is decomposed into the actual disorder
direction and individual variance derivatives. Their integrability permits
splitting the Gaussian expectation, and the existing radial Stein identity
gives the disorder Hessian trace. Replica-overlap identification is not assumed.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- Scalar linearity in the actual recursively tilted disorder direction. -/
theorem mixedConstrainedDirection_smul
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (j : ℕ) (x y : Fin n → ℝ) (c : ℝ) :
    mixedConstrainedDirection mode m v j U (c • V) u x y =
      c * mixedConstrainedDirection mode m v j U V u x y := by
  simpa using mixedConstrainedDirection_sum (I := Unit) U u mode m v hm hv j
    (fun _ => c) (fun _ => V) x y

section GaussianDisorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The actual radial disorder direction is integrable at every amplitude. -/
theorem integrable_mixedConstrainedDirection_radial {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l) (hv : ∀ l, 0 ≤ v l)
    (j : ℕ) (x y : Fin n → ℝ) :
    Integrable (fun ω => mixedConstrainedDirection mode m v j
      (a • Z ω) (Z ω) u x y) ℙ := by
  apply ((integrable_norm_of_gaussian hZ).const_mul (2 * Fintype.card (Config n))).mono'
    (measurable_mixedConstrainedDirection_radial hZ a u mode m v hm hv j x y).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (mixedConstrainedCascadeD_disorder_abs_le (a • Z ω) (Z ω) u mode m v hm hv j x y).trans
    (by nlinarith [uAbs_le_card_mul_norm n (Z ω)])

/-- The actual averaged simultaneous derivative, explicitly split into the
Gaussian Hessian trace and the finite sum of original-level heat contributions.
Inactive zero variances contribute zero; no heat derivative at zero is used. -/
theorem hasDerivAt_mixedConstrainedGaussian_path_trace {Z : Ω → EnergySpace n}
    (hZ : IsGaussianHilbert Z) (a : ℝ → ℝ) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → ℝ → ℝ) (hm : ∀ l, 0 ≤ m l) (j : ℕ)
    {w a' : ℝ} {v' : ℕ → ℝ} (ha : HasDerivAt a a' w)
    (hv : ∀ l < j, HasDerivAt (v l) (v' l) w)
    (hnonneg : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ v l z)
    (hface : ∀ l < j, 0 < v l w ∨ (v l =ᶠ[𝓝 w] fun _ => 0))
    (x y : Fin n → ℝ) :
    HasDerivAt (fun z => ∫ ω, mixedVectorCascade n mode m (fun l => v l z)
      (constrainedPairFieldBase n (a z • Z ω) u) j x y ∂ℙ)
      (a' * a w * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        mixedConstrainedSecond mode m (fun l => v l w) j
          (a w • Z ω) (hZ.w i) (hZ.w i) u x y ∂ℙ) +
        ∑ l : Fin j, v' l *
          (if 0 < v l w then ∫ ω, mixedLevelVarianceD (a w • Z ω) u mode m
            (fun i => v i w) l (j - (l + 1)) (v l w) x y ∂ℙ else 0)) w := by
  classical
  have hv0 : ∀ l, 0 ≤ v l w := hnonneg.self_of_nhds
  let G := fun (l : Fin j) ω =>
    if 0 < v l w then mixedLevelVarianceD (a w • Z ω) u mode m
      (fun i => v i w) l (j - (l + 1)) (v l w) x y else 0
  have hG (l : Fin j) : Integrable (G l) ℙ := by
    by_cases hl : 0 < v l w
    · simpa only [G, if_pos hl] using
        integrable_mixedLevelVarianceD hZ (a w) u mode m (fun i => v i w) hm hv0
          l (j - (l + 1)) x y hl
    · simpa only [G, if_neg hl] using (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) ℙ)
  have hR := integrable_mixedConstrainedDirection_radial hZ (a w) u mode m
    (fun l => v l w) hm hv0 j x y
  have hS : Integrable (fun ω => ∑ l : Fin j, v' l * G l ω) ℙ :=
    integrable_finsetSum _ fun l _ => (hG l).const_mul (v' l)
  have he (ω : Ω) :
      mixedConstrainedCascadePathD (fun z => a z • Z ω) u mode m v j x y w =
      a' * mixedConstrainedDirection mode m (fun l => v l w) j
        (a w • Z ω) (Z ω) u x y + ∑ l : Fin j, v' l * G l ω := by
    rw [mixedConstrainedCascadePathD,
      mixedConstrainedCascade_path_fderiv_eq_decomposition (fun z => a z • Z ω)
        u mode m v hm j (ha.smul_const (Z ω)) hv hnonneg hface x y,
      mixedConstrainedDirection_smul (a w • Z ω) (Z ω) u mode m
        (fun l => v l w) hm hv0 j x y a']
  have H := hasDerivAt_mixedConstrainedGaussian_path hZ a u mode m v hm j ha.differentiableAt
    (fun l hl => (hv l hl).differentiableAt) hnonneg hface x y
  apply H.congr_deriv
  simp_rw [he]
  rw [integral_add (hR.const_mul a') hS, integral_const_mul,
    integral_finsetSum _ (fun l _ => (hG l).const_mul (v' l)),
    stein_mixedConstrainedCascade_radial hZ (a w) u mode m (fun l => v l w) hm hv0 j x y,
    ← mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul]
  by_cases hl : 0 < v l w <;> simp only [G, hl, if_true, if_false, integral_zero]

end GaussianDisorder

end SpinGlass.Targets
