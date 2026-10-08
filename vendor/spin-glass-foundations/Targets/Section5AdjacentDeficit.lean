module

public import Targets.Section5AdjacentScalarFamily
public import Targets.Section5InterleavedMajorant

@[expose] public section

/-!
# Adjacent scalar deficits at trial breakpoints

The scalar breakpoint identity transports immediately to the arbitrary-lambda
deficit used by the compact witness argument.  This is the exact gluing datum
needed at a common trial boundary; it does not by itself provide a global
compact cover.
-/

namespace SpinGlass.Targets

theorem section5InterleavedLambdaDeficit_adjacent_boundary {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ}
    (hj : j + 1 ≤ k + 1) (t l : ℝ) :
    section5InterleavedLambdaDeficit s β h r j t (s.q j) l =
      section5InterleavedLambdaDeficit s β h r (j + 1) t (s.q j) l := by
  dsimp only [section5InterleavedLambdaDeficit]
  rw [section5InterleavedScalarV_adjacent_boundary s β h r hj t l]

end SpinGlass.Targets
