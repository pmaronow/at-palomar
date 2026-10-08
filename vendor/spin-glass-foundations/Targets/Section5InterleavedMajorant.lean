module

public import Targets.Section5InterleavedBound

@[expose] public section

/-!
# Arbitrary-lambda scalar upper comparisons for compactness

The actual mixed interpolation transports every scalar lambda witness to
the original constrained free energy. The witness is independent of system
size and disorder. This retains the nonzero-lambda comparisons needed near
physical time zero, where the zero-lambda scalar deficit can vanish.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- The actual scalar gap at an arbitrary fixed lambda. -/
noncomputable def section5InterleavedLambdaDeficit {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r j : ℕ) (t u ℓ : ℝ) : ℝ :=
  2 * parisiF s β (k + 2) h - section5InterleavedScalarV s β h r j t u ℓ + ℓ * u

/-- At zero lambda this is exactly the already checked strict scalar gap. -/
theorem section5InterleavedLambdaDeficit_zero {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r j : ℕ) (t u : ℝ) :
    section5InterleavedLambdaDeficit s β h r j t u 0 =
      section5InterleavedScalarDeficit s β h r j t u := by
  simp [section5InterleavedLambdaDeficit, section5InterleavedScalarDeficit]

/-- Every lambda supplies a genuine upper comparison for the original
free energy. No scalar strictness or continuity is assumed in this bound. -/
theorem constrainedPhi_le_guerraPsi_sub_interleavedLambdaDeficit
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t - section5InterleavedLambdaDeficit s β h r j t u ℓ := by
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have H := section5InterleavedInterpolation_endpoint_bound hn s β h sk hr0 hr hj0 hj ht hu
  have H0 := section5InterleavedInterpolation_zero_le_lambda hn s β h sk.U r hj ht hu
    ⟨σ, τ, hστ⟩ ℓ
  dsimp only [guerraPsi, section5InterleavedLambdaDeficit]
  linarith

end SpinGlass.Targets
