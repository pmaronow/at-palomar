module

public import Targets.Section4CurvatureUniform
public import Targets.Section5InitialLeft

@[expose] public section

/-!
# Propositions 5.1 and 5.3 with proved regularity

The actual constrained free energy has the local-left quadratic deficit,
and the same deficit on the entire initial interval. The beta-only constant
is explicit. Neither statement assumes a derivative or Lipschitz estimate.
The dual, signed and remaining far-overlap cases of Theorem 2.4 are separate.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Proposition 5.1 for the actual SK constrained free energy, with a
beta-only constant and no unproved regularity input. -/
theorem constrainedPhi_local_left_uniform
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hlocal : section5LocalLeftConstant β 535 * (s.q r - u) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * (u - s.q r) ^ 2 :=
  constrainedPhi_local_left_of_hessian_lipschitz hn s β h ε sk hr0 hr hβ hm hright
    ht ht₀ (by norm_num : (0 : ℝ) ≤ 535) hu hmin hnear hsmall hlocal
    (fun v hv w hw => section4THessianSquare_lipschitz_uniform s β h hr0 hr hv hw)

/-- Proposition 5.3: the initial mass-zero interval needs no local-overlap
smallness hypothesis. Jensen supplies the global initial comparison, and
the near-optimality condition uses the same explicit beta-only constant. -/
theorem constrainedPhi_initial_left_uniform
    (hn : 0 < n) (s : RSBScheme k) (β h ε : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1) (hright : s.q 1 < s.q 2 ∨ s.q 1 = 1)
    {t t₀ u : ℝ} (ht : t ∈ Set.Icc 0 t₀) (ht₀ : t₀ < 1)
    (hu : u ∈ Set.Icc 0 (s.q 1)) [Nonempty (AT.ConstrainedPair n u)]
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    constrainedPhi n s β h sk.U (k + 1) t u ≤
      2 * guerraPsi s β h t -
        (1 - t₀) ^ 2 / section5LocalLeftConstant β 535 * (u - s.q 1) ^ 2 := by
  apply constrainedPhi_initial_left_of_hessian_lipschitz hn s β h ε sk hβ hm hright
    ht ht₀ (by norm_num : (0 : ℝ) ≤ 535) hu hmin hnear hsmall
  intro v hv w hw
  exact section4THessianSquare_lipschitz_uniform s β h (r := 1) le_rfl (by omega)
    (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hv)
    (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hw)

end SpinGlass.Targets
