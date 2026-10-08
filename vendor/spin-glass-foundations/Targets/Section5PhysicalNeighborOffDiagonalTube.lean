module

public import Targets.Section5InterleavedOffDiagonalBound
public import Targets.Section5InterleavedScalarContinuity
public import Targets.Section5InitialLeft
public import Targets.Section5CompactTube

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The correct scalar deficit for an off-diagonal trial: `v` is the endpoint
used by the scalar path, whereas `u` is the constrained overlap. -/
noncomputable def section5InterleavedOffDiagonalLambdaDeficit
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) (r j : ℕ)
    (t u v ℓ : ℝ) : ℝ :=
  2 * parisiF s β (k + 2) h - section5InterleavedScalarV s β h r j t v ℓ +
    ℓ * u - t * (β ^ 2 / 2) * (u - v) ^ 2

theorem constrainedPhi_le_guerraPsi_sub_offDiagonalLambdaDeficit
    {k n : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) {r : ℕ} (hr0 : 1 ≤ r)
    (hr : r ≤ k + 1) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {t u v ℓ : ℝ} (ht : t ∈ Icc 0 1)
    (hv : |v| ∈ Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        section5InterleavedOffDiagonalLambdaDeficit s β h r j t u v ℓ := by
  have H := constrainedPhi_le_interleavedOffDiagonalMajorant (ℓ := ℓ) hn s β h sk
    hr0 hr hj0 hj ht hv hatt
  dsimp only [section5InterleavedOffDiagonalLambdaDeficit, guerraPsi]
  linarith

/-- Uniform physical-left tube from a genuine endpoint off-diagonal scalar
witness.  The only scalar input is pointwise positivity at the physical
endpoint; all finite-volume transport is supplied by the proved integrated
off-diagonal bound above. -/
theorem exists_uniform_constrainedPhi_offDiagonal_physical_left_tube
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {v t₀ : ℝ} (hvsign : 0 ≤ v)
    (hv : |v| ∈ Icc (s.q (j - 1)) (s.q j))
    (ht₀ : t₀ < 1)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ ℓ,
      0 < section5InterleavedOffDiagonalLambdaDeficit s β h r j t v v ℓ) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u - v| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let f : ℝ → (ℝ × ℝ) → ℝ := fun ℓ z =>
    section5InterleavedOffDiagonalLambdaDeficit s β h r j z.1 z.2 v ℓ
  have hf : ∀ ℓ, Continuous (f ℓ) := by
    intro ℓ
    have H := continuousOn_section5InterleavedScalarV_nonneg s β h r hj ℓ
    have hmap : Continuous (fun z : ℝ × ℝ => (z.1, v)) :=
      continuous_fst.prodMk continuous_const
    have H' := H.comp (s := (Set.univ : Set (ℝ × ℝ))) hmap.continuousOn
      (fun z _ => by
        change 0 ≤ v
        exact hvsign)
    have Hs : Continuous (fun z : ℝ × ℝ =>
        section5InterleavedScalarV s β h r j z.1 v ℓ) :=
      continuousOn_univ.mp H'
    unfold f section5InterleavedOffDiagonalLambdaDeficit
    have Hlin : Continuous (fun z : ℝ × ℝ =>
        2 * parisiF s β (k + 2) h -
          section5InterleavedScalarV s β h r j z.1 v ℓ + ℓ * z.2) :=
      (continuous_const.sub Hs).add (continuous_const.mul continuous_snd)
    have Hquad : Continuous (fun z : ℝ × ℝ =>
        z.1 * (β ^ 2 / 2) * (z.2 - v) ^ 2) := by fun_prop
    exact Hlin.sub Hquad
  have hpos : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ ℓ, 0 < f ℓ (t, v) := by
    intro t ht
    obtain ⟨ℓ, hℓ⟩ := hboundary t ht
    exact ⟨ℓ, hℓ⟩
  obtain ⟨ρ, hρ, δ, hδ, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Icc (0 : ℝ) t₀)
      isCompact_Icc f hf v hpos
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro t ht u hu n hn sk hatt
  obtain ⟨ℓ, hℓ⟩ := Htube t ht u hu
  have HB := constrainedPhi_le_guerraPsi_sub_offDiagonalLambdaDeficit
    (ℓ := ℓ) (t := t) (u := u) (v := v) hn s β h sk hr0 hr hj0 hj
    (⟨ht.1, ht.2.trans ht₀.le⟩) hv hatt
  dsimp [f] at hℓ
  linarith

/- The initial physical-left interval is already unconditional once the
uniform Hessian estimate is supplied: it gives a concrete tube around the
endpoint `q₀ = 0` without any small physical-gap assumption. -/
theorem exists_uniform_constrainedPhi_initial_left_tube
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t₀ L : ℝ} (ht₀ : t₀ < 1) (hL : 0 ≤ L)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β L * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hLip : ∀ v ∈ Icc 0 (β ^ 2 * s.q 1),
      ∀ w ∈ Icc 0 (β ^ 2 * s.q 1),
        |section4THessianSquare s β h 1 v - section4THessianSquare s β h 1 w| ≤
          L * |v - w|)
    (hq1 : 0 < s.q 1) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (0 : ℝ) ρ,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  let A : ℝ := (1 - t₀) ^ 2 / section5LocalLeftConstant β L
  let ρ : ℝ := s.q 1 / 2
  let δ : ℝ := A * (s.q 1) ^ 2 / 4
  have hA : 0 < A := by
    dsimp [A]
    have hc := section5LocalLeftConstant_pos β L hL
    exact div_pos (sq_pos_of_ne_zero (by linarith [ht₀])) hc
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨ρ, hρ, δ, hδ, ?_⟩
  intro n hn sk t ht u hu hatt
  obtain ⟨σ, τ, hστ⟩ := hatt
  letI : Nonempty (AT.ConstrainedPair n u) := ⟨⟨(σ, τ), hστ⟩⟩
  have hρq : ρ ≤ s.q 1 := by
    dsimp [ρ]
    linarith
  have huq : u ∈ Icc (0 : ℝ) (s.q 1) :=
    ⟨hu.1, hu.2.trans hρq⟩
  have H := constrainedPhi_initial_left_of_hessian_lipschitz hn s β h ε sk hβ hm
    hright ht ht₀ hL huq hmin hnear hsmall hLip
  have hsq : (s.q 1) ^ 2 / 4 ≤ (u - s.q 1) ^ 2 := by
    have huupper : u ≤ s.q 1 / 2 := by dsimp [ρ] at hu; exact hu.2
    nlinarith [sq_nonneg (u - s.q 1)]
  dsimp [A, δ] at *
  nlinarith

end SpinGlass.Targets
