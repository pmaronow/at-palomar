module

public import Targets.Section5InterleavedScalarCore
public import Targets.Section5ScalarEqualityOrder
public import Targets.Section5InterleavedZero

@[expose] public section

/-!
# Joint strictness of the actual interleaved scalar endpoint

The actual paired equality condition gives (5.44), and the actual scalar
sorting equality gives (5.51). Talagrand's positive-variance witnesses in the
outside-neighbor regimes make these two conditions incompatible. Both signs
of the target overlap are included, with the original field `h` unchanged.
This is the strict zero-time scalar endpoint, not the full interpolation
inequality for the constrained free energy.
-/

namespace SpinGlass.Targets

open MeasureTheory ProbabilityTheory

/-- Equality of the actual paired endpoint with its scalar reference forces
Talagrand's order condition (5.44), in the original forward tagged order. -/
theorem section5InterleavedScalarV_eq_reference_implies_order {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (t u : ℝ)
    (he : section5InterleavedScalarV s β h r j t u 0 =
      2 * section5InterleavedScalarReference s β r j t u h) :
    Section5InterleavingEqualityOrder s β t |u| r j := by
  intro b c hbv hcv hb hc hc0
  let bi := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm b).val
  let ci := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm c).val
  have hbi : bi < (k + 2) + (k + 3) := by dsimp [bi]; omega
  have hci : ci < (k + 2) + (k + 3) := by dsimp [ci]; omega
  have hbt : section5ReverseTag s r j bi = b := section5ReverseTag_at_tag s r j b
  have hct : section5ReverseTag s r j ci = c := section5ReverseTag_at_tag s r j c
  have hbm : section5ReverseMode s r j (decide (u < 0)) bi = .independent := by
    rw [section5ReverseMode, hbt]
    exact (section5TaggedMode_eq_independent_iff _ _ _ _).mpr hb
  have hcm : section5ReverseMode s r j (decide (u < 0)) ci ≠ .independent := by
    rw [section5ReverseMode, hct]
    exact fun he => (section5TaggedMode_eq_independent_iff _ _ _ _).mp he hc
  have hcmpos : 0 < section5ReverseMass s r j ci := by
    rw [section5ReverseMass, hct]
    simp only [section5TagScalarMass, if_pos hc] at hc0
    linarith
  have hbvar : 0 < section5ReverseVariance s β t |u| r j bi := by
    simpa only [section5ReverseVariance, hbt] using hbv
  have hcvar : 0 < section5ReverseVariance s β t |u| r j ci := by
    simpa only [section5ReverseVariance, hct] using hcv
  have H := mixedScalarCascade_eq_implies_order
    (section5ReverseMode s r j (decide (u < 0))) (section5ReverseMass s r j)
    (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    (section5ReverseMass_nonneg s r hj) (fun _ => continuous_const)
    (section5ReverseMode_scalarMass_mem_Icc s r hj (decide (u < 0)))
    ((k + 2) + (k + 3)) () h he hbi hci hbm hbvar hcm hcmpos hcvar
  change ((section5Interleaving s r j).symm c).val <
    ((section5Interleaving s r j).symm b).val
  dsimp [bi, ci] at H
  omega

/-- Non-strict comparison of the genuine mixed lambda-zero endpoint with the
original recursion, using its exact scalar sorting identification. -/
theorem section5InterleavedScalarV_zero_le_parisiF {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 ≤ 2 * parisiF s β (k + 2) h := by
  have H := section5InterleavedScalarV_zero_le_reference s β h r hj t u
  rw [section5InterleavedScalarReference_eq_list] at H
  exact H.trans (mul_le_mul_of_nonneg_left
    (section5InterleavedScalarSteps_cascade_le_parisiF s β r ht hj0 hj hu h) (by norm_num))

theorem strict_of_order_obstruction {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hn : ¬(Section5InterleavingEqualityOrder s β t |u| r j ∧
      Section5InterleavingScalarOrder s β t |u| r j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  apply lt_of_le_of_ne (section5InterleavedScalarV_zero_le_parisiF s β h r ht hj0 hj hu)
  intro he
  have Hpaired := section5InterleavedScalarV_zero_le_reference s β h r hj t u
  have Hscalar := section5InterleavedScalarSteps_cascade_le_parisiF s β r ht hj0 hj hu h
  rw [← section5InterleavedScalarReference_eq_list s β r j t u] at Hscalar
  have hs : section5InterleavedScalarReference s β r j t u h = parisiF s β (k + 2) h := by
    linarith
  have hp : section5InterleavedScalarV s β h r j t u 0 =
      2 * section5InterleavedScalarReference s β r j t u h := by linarith
  apply hn
  constructor
  · exact section5InterleavedScalarV_eq_reference_implies_order s β h r hj t u hp
  · apply section5InterleavedScalarSteps_eq_implies_order s β r ht hj0 hj hu h
    simpa only [section5InterleavedScalarReference_eq_list] using hs

/-- Genuine strict zero-time comparison in the left outside-neighbor regime.
The two witness variances are explicitly positive; all other variances may
vanish, and either sign of the target overlap is allowed. -/
theorem section5InterleavedScalarV_zero_lt_left_outside {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - |u|)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1)))) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h :=
  strict_of_order_obstruction s β h r ht hj0 (by omega) hu
    (section5Interleaving_left_outside_obstruction s β t |u| hr hj0 hjr hm hbv hcv)

/-- Genuine strict zero-time comparison in the right outside-neighbor regime,
again with exactly the positive variances used by Talagrand's witnesses. -/
theorem section5InterleavedScalarV_zero_lt_right_outside {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {r j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1)))) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h :=
  strict_of_order_obstruction s β h r ht (by omega) hj hu
    (section5Interleaving_right_outside_obstruction s β t |u| hj hrj hm hbv hcv)

/-- The actual scalar deficit, which has no system-size or disorder argument. -/
noncomputable def section5InterleavedScalarDeficit {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r j : ℕ) (t u : ℝ) : ℝ :=
  2 * parisiF s β (k + 2) h - section5InterleavedScalarV s β h r j t u 0

/-- Exact transport of the scalar deficit to the actual zero-time endpoint.
Its strict positivity is proved separately in the outside-neighbor regimes. -/
theorem section5InterleavedInterpolation_zero_le_sub_deficit
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolation n s β h U r j t u 0 ≤
      2 * Real.log 2 + 2 * parisiF s β (k + 2) h -
        section5InterleavedScalarDeficit s β h r j t u := by
  have H := section5InterleavedInterpolation_zero_le hn s β h U r hj ht hu hatt
  dsimp only [section5InterleavedScalarDeficit]
  linarith

/-- A strictly positive left outside-neighbor deficit is chosen before the
system size and disorder. This is a zero-time endpoint bound, not a statement
of the full varying-time interpolation comparison. -/
theorem exists_section5Interleaved_zero_gap_left_outside
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - |u|)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1)))) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ} (_hn : 0 < n) (U : Ω → EnergySpace n),
        (∃ σ τ : Config n, overlap n σ τ = u) →
        section5InterleavedInterpolation n s β h U r j t u 0 ≤
          2 * Real.log 2 + 2 * parisiF s β (k + 2) h - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_left_outside s β h ht hr hj0
      hjr hu hm hbv hcv)
  · intro n hn U hatt
    exact section5InterleavedInterpolation_zero_le_sub_deficit hn s β h U r (by omega)
      ht hu hatt

/-- The analogous uniform-in-size and disorder right outside-neighbor gap. -/
theorem exists_section5Interleaved_zero_gap_right_outside
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1)))) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ} (_hn : 0 < n) (U : Ω → EnergySpace n),
        (∃ σ τ : Config n, overlap n σ τ = u) →
        section5InterleavedInterpolation n s β h U r j t u 0 ≤
          2 * Real.log 2 + 2 * parisiF s β (k + 2) h - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_right_outside s β h ht hj
      hrj hu hm hbv hcv)
  · intro n hn U hatt
    exact section5InterleavedInterpolation_zero_le_sub_deficit hn s β h U r hj ht hu hatt

/-- Actual strict zero-time endpoint in the left outside-neighbor regime. -/
theorem section5InterleavedInterpolation_zero_lt_left_outside
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < t * (β ^ 2 * (s.q j - |u|)))
    (hcv : 0 < (1 - t) * (β ^ 2 * (s.q r - s.q (r - 1))))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolation n s β h U r j t u 0 <
      2 * Real.log 2 + 2 * parisiF s β (k + 2) h := by
  have H := section5InterleavedInterpolation_zero_le hn s β h U r (by omega) ht hu hatt
  have H' := section5InterleavedScalarV_zero_lt_left_outside s β h ht hr hj0
    hjr hu hm hbv hcv
  linarith

/-- Actual strict zero-time endpoint in the right outside-neighbor regime. -/
theorem section5InterleavedInterpolation_zero_lt_right_outside
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1))))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolation n s β h U r j t u 0 <
      2 * Real.log 2 + 2 * parisiF s β (k + 2) h := by
  have H := section5InterleavedInterpolation_zero_le hn s β h U r hj ht hu hatt
  have H' := section5InterleavedScalarV_zero_lt_right_outside s β h ht hj hrj hu hm hbv hcv
  linarith

end SpinGlass.Targets
