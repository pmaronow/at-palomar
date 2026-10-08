module

public import Targets.Section5InterpolationBound

@[expose] public section

/-!
# Continuous scalar comparisons with fixed mass and lambda witnesses

The scalar comparison functions are continuous jointly in physical time and
overlap, with the auxiliary mass and lambda held fixed. This follows directly
from the checked good-family theorem for the split scalar cascade, including
zero variance. It does not assert overlap continuity of the finite-system
overlap-constrained free energy.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Joint variance/lambda continuity of the actual left scalar family, for
one fixed nonnegative mass. All real variances are allowed by the actual
square-root convention, so physical variance endpoints are included. -/
theorem continuous_section5V_variance_lambda {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun p : ℝ × ℝ => section5V s β h r m p.1 p.2) := by
  have H := splitScalarCascade_good
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5Variance_continuous s β r (k + 2 - j))
    (k + 3 - r) (k + 3)
  exact H.contF.comp (show Continuous (fun p : ℝ × ℝ => (p.1, p.2, (h, h))) by fun_prop)

/-- The dual family has the same fixed-mass joint continuity, including the
terminal baseline mass one and every zero variance. -/
theorem continuous_section5RightV_variance_lambda {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) :
    Continuous (fun p : ℝ × ℝ => section5RightV s β h r m p.1 p.2) := by
  have H := splitScalarCascade_good
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightVariance s β r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightVariance_continuous s β r (k + 2 - j))
    (k + 2 - r) (k + 3)
  exact H.contF.comp (show Continuous (fun p : ℝ × ℝ => (p.1, p.2, (h, h))) by fun_prop)

/-- Genuine left scalar upper comparison after endpoint transport. The
argument is `(physical time, overlap)`; mass and lambda are fixed witnesses. -/
noncomputable def section5LeftComparison {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * Real.log 2 + section5V s β h r m (p.1 * (β ^ 2 * (s.q r - p.2))) ℓ - ℓ * p.2 -
    p.1 * (2 * parisiCorrection s β +
      (m - s.m (r - 1)) * (β ^ 2 / 2 * (s.q r ^ 2 - p.2 ^ 2)))

/-- Genuine right scalar upper comparison, with its original raw mass and
right-side correction sign. No reflection of a variable-mass family is used. -/
noncomputable def section5RightComparison {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * Real.log 2 + section5RightV s β h r m (p.1 * (β ^ 2 * (p.2 - s.q r))) ℓ - ℓ * p.2 -
    p.1 * (2 * parisiCorrection s β +
      (m - s.m r) * (β ^ 2 / 2 * (p.2 ^ 2 - s.q r ^ 2)))

theorem continuous_section5LeftComparison {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5LeftComparison s β h r m ℓ) := by
  have H := (continuous_section5V_variance_lambda s β h hr hm).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1 * (β ^ 2 * (s.q r - p.2)), ℓ)) by fun_prop)
  unfold section5LeftComparison
  exact ((continuous_const.add H).sub (continuous_const.mul continuous_snd)).sub
    (continuous_fst.mul (by fun_prop))

theorem continuous_section5RightComparison {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5RightComparison s β h r m ℓ) := by
  have H := (continuous_section5RightV_variance_lambda s β h hr hm).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1 * (β ^ 2 * (p.2 - s.q r)), ℓ)) by fun_prop)
  unfold section5RightComparison
  exact ((continuous_const.add H).sub (continuous_const.mul continuous_snd)).sub
    (continuous_fst.mul (by fun_prop))

/-- Scalar margin below the original comparison function `2ψ`, not below
the interacting free energy. It is independent of system size/disorder. -/
noncomputable def section5LeftComparisonDeficit {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * guerraPsi s β h p.1 - section5LeftComparison s β h r m ℓ p

noncomputable def section5RightComparisonDeficit {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) (m ℓ : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * guerraPsi s β h p.1 - section5RightComparison s β h r m ℓ p

theorem continuous_section5LeftComparisonDeficit {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5LeftComparisonDeficit s β h r m ℓ) := by
  have H : Continuous (fun p : ℝ × ℝ => 2 * guerraPsi s β h p.1) := by
    unfold guerraPsi
    fun_prop
  exact H.sub (continuous_section5LeftComparison s β h hr hm ℓ)

theorem continuous_section5RightComparisonDeficit {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : 0 ≤ m) (ℓ : ℝ) :
    Continuous (section5RightComparisonDeficit s β h r m ℓ) := by
  have H : Continuous (fun p : ℝ × ℝ => 2 * guerraPsi s β h p.1) := by
    unfold guerraPsi
    fun_prop
  exact H.sub (continuous_section5RightComparison s β h hr hm ℓ)

section Pressure

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Every admissible fixed left witness bounds the actual constrained free
energy throughout its physical rectangle. -/
theorem constrainedPhi_le_section5LeftComparison
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] (ℓ : ℝ) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ section5LeftComparison s β h r m ℓ (t, u) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have H := section5Interpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have H0 := section5Interpolation_zero_le hn s β h sk.U hr0 hr hm0 ht hu
    ⟨p.1.1, p.1.2, p.2⟩ ℓ
  dsimp only [section5LeftComparison]
  linarith

/-- The right witness interval includes auxiliary masses above one; only
nonnegativity, not an artificial upper bound one, is used for continuity. -/
theorem constrainedPhi_le_section5RightComparison
    (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] (ℓ : ℝ) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ section5RightComparison s β h r m ℓ (t, u) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have H := section5RightInterpolation_endpoint_bound hn s β h sk hr0 hr hm ht hu
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  have H0 := section5RightInterpolation_zero_le hn s β h sk.U hr hm0 ht hu
    ⟨p.1.1, p.1.2, p.2⟩ ℓ
  dsimp only [section5RightComparison]
  linarith

end Pressure

end SpinGlass.Targets
