module

public import Targets.Section5FiniteCompactCover
public import Targets.TalagrandOverlapTail

@[expose] public section

/-!
# Finite compact-cover assembly for additive gaps

This is the direct companion to the finite witness lemma.  It is useful when
the scalar comparison has already been transported to the original finite-size
free energy on each compact piece: finitely many positive piecewise gaps have
one positive common gap.  No continuity of the finite-size constrained free
energy is used here.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

theorem exists_uniform_gap_of_finite_compact_cover
    {J X : Type*} [Fintype J] [TopologicalSpace X]
    (S : J → Set X) (B F : X → ℝ)
    (hS : ∀ j, IsCompact (S j))
    (hcover : ∀ x, ∃ j, x ∈ S j)
    (hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ x ∈ S j, F x ≤ B x - δ) :
    ∃ δ > (0 : ℝ), ∀ x, F x ≤ B x - δ := by
  classical
  let d : J → ℝ := fun j => Classical.choose (hgap j)
  have hd : ∀ j, 0 < d j := fun j => (Classical.choose_spec (hgap j)).1
  have hFd : ∀ j x, x ∈ S j → F x ≤ B x - d j := by
    intro j x hx
    exact (Classical.choose_spec (hgap j)).2 x hx
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_finite_compact_witnesses
    (S := S) (f := fun j (_ : Unit) (_x : X) => d j) hS
    (fun _ _ => continuousOn_const) (fun j x _ => ⟨(), hd j⟩)
  refine ⟨δ, hδ, ?_⟩
  intro x
  obtain ⟨j, hx⟩ := hcover x
  obtain ⟨_, hδj⟩ := Hδ j x hx
  have hbound := hFd j x hx
  linarith

variable {Ω : Type*} [MeasureSpace Ω]

/-- The same finite-cover bookkeeping for the actual constrained free-energy
comparison.  Each compact piece may use its own positive deficit, but the
resulting deficit is uniform over all pieces, system sizes, disorders and
attainable overlaps. -/
theorem exists_uniform_constrainedPhi_gap_of_finite_compact_cover
    {J : Type*} [Fintype J] {k : ℕ} [IsProbabilityMeasure (ℙ : Measure Ω)]
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (X : Set (ℝ × ℝ))
    (S : J → Set (ℝ × ℝ))
    (hS : ∀ j, IsCompact (S j))
    (hcover : ∀ z ∈ X, ∃ j, z ∈ S j)
    (hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ z ∈ S j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ) :
    ∃ δ > (0 : ℝ), ∀ z ∈ X, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  classical
  let d : J → ℝ := fun j => Classical.choose (hgap j)
  have hd : ∀ j, 0 < d j := fun j => (Classical.choose_spec (hgap j)).1
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_finite_compact_witnesses
    (S := S) (f := fun j (_ : Unit) (_z : ℝ × ℝ) => d j) hS
    (fun _ _ => continuousOn_const) (fun j z _ => ⟨(), hd j⟩)
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨j, hzj⟩ := hcover z hz
  obtain ⟨_, hδj⟩ := Hδ j z hzj
  have hbound := (Classical.choose_spec (hgap j)).2 z hzj hn sk hatt
  linarith

/- The level-indexed form avoids dependent casts when the physical replica
level is already supplied as `d` (rather than represented as `k+2-r`). -/
theorem exists_uniform_constrainedPhi_gap_of_finite_compact_cover_at_level
    {J : Type*} [Fintype J] {k : ℕ} [IsProbabilityMeasure (ℙ : Measure Ω)]
    (s : RSBScheme k) (β h : ℝ) (d : ℕ) (X : Set (ℝ × ℝ))
    (S : J → Set (ℝ × ℝ))
    (hS : ∀ j, IsCompact (S j))
    (hcover : ∀ z ∈ X, ∃ j, z ∈ S j)
    (hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ z ∈ S j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U d z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ) :
    ∃ δ > (0 : ℝ), ∀ z ∈ X, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U d z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  classical
  let c : J → ℝ := fun j => Classical.choose (hgap j)
  have hc : ∀ j, 0 < c j := fun j => (Classical.choose_spec (hgap j)).1
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_finite_compact_witnesses
    (S := S) (f := fun j (_ : Unit) (_z : ℝ × ℝ) => c j) hS
    (fun _ _ => continuousOn_const) (fun j _ _ => ⟨(), hc j⟩)
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨j, hzj⟩ := hcover z hz
  obtain ⟨_, hδj⟩ := Hδ j z hzj
  have H := (Classical.choose_spec (hgap j)).2 z hzj hn sk hatt
  linarith

/- The same finite minimum argument also preserves an eventual-in-`n`
bound.  This is the form needed after each compact region has supplied its
own finite-size threshold. -/
theorem exists_eventually_uniform_gap_of_finite_compact_cover
    {J X : Type*} [Fintype J] [TopologicalSpace X]
    (S : J → Set X) (B F : ℕ → X → ℝ)
    (hcover : ∀ x, ∃ j, x ∈ S j)
    (hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ S j, F n x ≤ B n x - δ) :
    ∃ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ x,
      F n x ≤ B n x - δ := by
  classical
  let d : J → ℝ := fun j => Classical.choose (hgap j)
  have hd : ∀ j, 0 < d j := fun j => (Classical.choose_spec (hgap j)).1
  have hFd : ∀ j, ∀ᶠ n in atTop, ∀ x ∈ S j,
      F n x ≤ B n x - d j := by
    intro j
    exact (Classical.choose_spec (hgap j)).2
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_finite_compact_witnesses
    (S := fun _ : J => (Set.univ : Set Unit))
    (f := fun j (_ : Unit) (_x : Unit) => d j)
    (fun _ => isCompact_univ) (fun _ _ => continuousOn_const)
    (fun j _ _ => ⟨(), hd j⟩)
  have hevent : ∀ᶠ n in atTop, ∀ j : J, ∀ x ∈ S j,
      F n x ≤ B n x - d j :=
    (Filter.eventually_all).2 hFd
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hevent] with n hn x
  obtain ⟨j, hx⟩ := hcover x
  have hδj : δ ≤ d j := by
    obtain ⟨_, h⟩ := Hδ j () (by simp)
    exact h
  have hbound := hn j x hx
  linarith

/- The constrained-free-energy specialization keeps the natural `z ∈ X`
restriction of the parameter domain.  This avoids introducing a subtype when
the compact pieces have already been chosen in the ambient overlap plane. -/
theorem exists_eventually_uniform_constrainedPhi_gap_of_finite_compact_cover
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {J : Type*} [Fintype J] {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) (X : Set (ℝ × ℝ))
    (S : J → Set (ℝ × ℝ))
    (hcover : ∀ z ∈ X, ∃ j, z ∈ S j)
    (hgap : ∀ j, ∃ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ z ∈ S j,
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ) :
    ∃ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ z ∈ X,
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  classical
  let d : J → ℝ := fun j => Classical.choose (hgap j)
  have hd : ∀ j, 0 < d j := fun j => (Classical.choose_spec (hgap j)).1
  have hFd : ∀ j, ∀ᶠ n in atTop, ∀ z ∈ S j,
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - d j := by
    intro j
    exact (Classical.choose_spec (hgap j)).2
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_finite_compact_witnesses
    (S := fun _ : J => (Set.univ : Set Unit))
    (f := fun j (_ : Unit) (_z : Unit) => d j)
    (fun _ => isCompact_univ) (fun _ _ => continuousOn_const)
    (fun j _ _ => ⟨(), hd j⟩)
  have hevent : ∀ᶠ n in atTop, ∀ j : J, ∀ z ∈ S j,
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - d j :=
    (Filter.eventually_all).2 hFd
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hevent] with n hn z hz sk hatt
  obtain ⟨j, hzj⟩ := hcover z hz
  obtain ⟨_, hδj⟩ := Hδ j () (by simp)
  have hbound := hn j z hzj sk hatt
  linarith

end SpinGlass.Targets
