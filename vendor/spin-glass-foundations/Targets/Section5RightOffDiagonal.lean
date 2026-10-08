module

public import Targets.Section5OffDiagonalAlgebra
public import Targets.Section5ScalarComparisonContinuity
public import Targets.TalagrandRightInterpolation

@[expose] public section

/-!
# Right-trial overlap mismatch

The generic covariance calculation is independent of the direction of the
inserted trial.  This file specializes it to Talagrand's right interpolation:
the constrained overlap is `u`, while the right-trial overlap is `v` in the
physical interval `[q_r,q_(r+1)]`.  The specialization is deliberately kept
at the derivative level, so it can be reused by either scalar or actual
endpoint comparisons without duplicating the covariance telescope.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]

/- The two endpoint mismatch terms from the covariance telescope combine into
the nonnegative square used in the physical-neighbor crossing estimate. -/
theorem right_offDiagonal_quadratic_error (β t u v : ℝ) :
    t * (β ^ 2 / 2) * (v ^ 2 - u ^ 2) +
        t * β ^ 2 * u * (u - v) =
      t * (β ^ 2 / 2) * (u - v) ^ 2 := by
  ring

/- The scalar endpoint comparison with the constrained overlap `u` and the
right trial overlap `v` kept distinct. -/
noncomputable def section5RightOffDiagonalComparison
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ : ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * Real.log 2 + section5RightV s β h r m
      (p.1 * (β ^ 2 * (p.2.2 - s.q r))) ℓ - ℓ * p.2.1 -
    p.1 * (2 * parisiCorrection s β +
      (m - s.m r) * (β ^ 2 / 2 * (p.2.1 ^ 2 - s.q r ^ 2)))

noncomputable def section5RightOffDiagonalComparisonDeficit
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ : ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ :=
  2 * guerraPsi s β h p.1 -
    section5RightOffDiagonalComparison s β h r m ℓ p

theorem section5RightOffDiagonalComparisonDeficit_diag
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r : ℕ) (m ℓ t v : ℝ) :
    section5RightOffDiagonalComparisonDeficit s β h r m ℓ (t, (v, v)) =
      section5RightComparisonDeficit s β h r m ℓ (t, v) := by
  rfl

theorem continuous_section5RightOffDiagonalComparison
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5RightOffDiagonalComparison s β h r m ℓ) := by
  have H := (continuous_section5RightV_variance_lambda s β h hr hm).comp
    (show Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (p.1 * (β ^ 2 * (p.2.2 - s.q r)), ℓ)) by fun_prop)
  unfold section5RightOffDiagonalComparison
  exact ((continuous_const.add H).sub
      (continuous_const.mul continuous_snd.fst)).sub
    (continuous_fst.mul (by fun_prop))

theorem continuous_section5RightOffDiagonalComparisonDeficit
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5RightOffDiagonalComparisonDeficit s β h r m ℓ) := by
  have H : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      2 * guerraPsi s β h p.1) := by
    unfold guerraPsi
    fun_prop
  exact H.sub (continuous_section5RightOffDiagonalComparison s β h hr hm ℓ)

theorem section5RightFieldEndpoint_le_offDiagonal
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m t u v ℓ : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5RightFieldEndpoint n s β h u r m
        (t * (β ^ 2 * (v - s.q r))) ≤
      2 * Real.log 2 + section5RightV s β h r m
          (t * (β ^ 2 * (v - s.q r))) ℓ - ℓ * u := by
  have hv' : t * (β ^ 2 * (v - s.q r)) ∈
      Set.Icc 0 (β ^ 2 * (s.q (r + 1) - s.q r)) :=
    section5RightSplitVariance_mem s β ht hv
  exact section5RightFieldEndpoint_le hn s β h u hr hm hv' hu ℓ

theorem averagedReplicaPressureDerivative_eq_right_covariance_mismatch
    {n k : ℕ} (s : RSBScheme k) (Z : Ω → EnergySpace n)
    (r : ℕ) (u v β t : ℝ) (m wvar : ℕ → ℝ)
    (hr : r ≤ k + 1) (_hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hm0 : m 0 = 0) (hmκ : m (k + 2) = 1)
    (x y : Fin n → ℝ) :
    averagedReplicaPressureDerivative Z u β t
        (fun j => m (k + 2 - j)) wvar
        (fun j => -(t * β ^ 2 *
          (section5RightRho s r v (k + 2 - j + 1) -
            section5RightRho s r v (k + 2 - j))))
        (k + 2 - r) (k + 3) x y =
      pairCovarianceExpression β t u m (section5RightRho s r v)
        (fun p => section5RightRho s r v (min p (r + 1))) (k + 2)
        (fun p => averagedConstrainedCascadeReplica Z u
          (fun j => m (k + 2 - j)) wvar (k + 2 - r)
          (k + 2 - p) (k + 3 - (k + 2 - p)) x y) +
        t * β ^ 2 * u * (u - v) := by
  have hρ0 : section5RightRho s r v 0 = 0 :=
    (section5RightRho_endpoints s hr v).1
  have hρ1 : section5RightRho s r v ((k + 2) + 1) = 1 := by
    simpa only [show (k + 2) + 1 = k + 3 by omega] using
      (section5RightRho_endpoints s hr v).2
  have hτ : r + 1 ≤ (k + 2) + 1 := by omega
  have hvρ : section5RightRho s r v (r + 1) = v := by
    simp [section5RightRho, section5Rho]
  simpa only [show (k + 2) + 1 - (r + 1) = k + 2 - r by omega,
    show (k + 2) + 1 = k + 3 by omega] using
      (averagedReplicaPressureDerivative_eq_covariance_mismatch
      (Z := Z) u v β t m (section5RightRho s r v) wvar (r + 1) (k + 2)
      hm0 hmκ hρ0 hρ1 hτ hvρ x y)

end SpinGlass.Targets
