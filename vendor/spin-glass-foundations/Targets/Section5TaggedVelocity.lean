module

public import Targets.Section5InterleavedEndpoint

@[expose] public section

/-!
# Active variance velocities in the actual tagged interpolation

A zero visited variance before the final interpolation time belongs to an
identically-zero path. Uniqueness of its genuine derivative makes its actual
trial-increment coefficient vanish. Physical levels stay frozen throughout.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- Each tagged path has positive variance or zero actual variance velocity.
This includes zero physical time, zero beta, and coincident overlap levels. -/
theorem section5TaggedPathVariance_pos_or_velocity_zero {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {t u w : ℝ} {j : ℕ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w < 1)
    (i : Fin ((k + 2) + (k + 3))) :
    0 < section5TaggedPathVariance s β t u j w (section5Interleaving s r j i) ∨
      -(t * β ^ 2 * (section5InterleavedRho s r j u (i + 1) -
        section5InterleavedRho s r j u i)) = 0 := by
  rcases section5TaggedPathVariance_pos_or_eq_zero s β ht hj hu hw (section5Interleaving s r j i) with hp | hz
  · exact Or.inl hp
  · right
    have H := hasDerivAt_section5TaggedPathVariance s β t u r hj i w
    have H0 : HasDerivAt
        (fun w' => section5TaggedPathVariance s β t u j w' (section5Interleaving s r j i)) 0 w := by
      simp only [hz]
      exact hasDerivAt_const w 0
    exact H.unique H0

/-- A nonpositive visited variance has zero actual trial-increment velocity;
its heat contribution may therefore be omitted without evaluating a boundary
variance derivative. -/
theorem section5TaggedPathVelocity_eq_zero_of_nonpos {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {t u w : ℝ} {j : ℕ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w < 1)
    (i : Fin ((k + 2) + (k + 3)))
    (hvar : section5TaggedPathVariance s β t u j w (section5Interleaving s r j i) ≤ 0) :
    -(t * β ^ 2 * (section5InterleavedRho s r j u (i + 1) -
      section5InterleavedRho s r j u i)) = 0 := by
  exact (section5TaggedPathVariance_pos_or_velocity_zero s β r ht hj hu hw i).resolve_left (not_lt.mpr hvar)

/-- The positive-or-zero-velocity alternative removes the active-face
indicator from any actual heat contribution. -/
theorem section5TaggedPathVelocity_mul_ite {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {t u w : ℝ} {j : ℕ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1)
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hw : w < 1)
    (i : Fin ((k + 2) + (k + 3))) (H : ℝ) :
    -(t * β ^ 2 * (section5InterleavedRho s r j u (i + 1) -
      section5InterleavedRho s r j u i)) *
        (if 0 < section5TaggedPathVariance s β t u j w (section5Interleaving s r j i) then H else 0) =
      -(t * β ^ 2 * (section5InterleavedRho s r j u (i + 1) -
        section5InterleavedRho s r j u i)) * H := by
  rcases section5TaggedPathVariance_pos_or_velocity_zero s β r ht hj hu hw i with hp | hz
  · rw [if_pos hp]
  · rw [hz, zero_mul, zero_mul]

end SpinGlass.Targets
