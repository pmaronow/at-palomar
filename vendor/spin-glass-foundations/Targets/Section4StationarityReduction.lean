module

public import Targets.RSBSchemeOverlapReduction
public import Targets.Section4StationarityTerminal

@[expose] public section

/-!
# Stationarity after exact mass and overlap reduction

Strict interior overlaps provide both variational directions, except at the
fixed endpoints zero and one where a single inward direction suffices. Thus
the original fixed-level minimizer can be reduced to a scheme satisfying the
actual Proposition 4.7 at every level, without changing its functional or
N-site interpolation. No strictness is imposed on the original scheme.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A strictly ordered interior overlap list has all the physical inward
directions used by the actual stationarity theorem. Boundary overlaps may
still equal zero or one. -/
theorem RSBScheme.overlap_directions_of_strict {k : ℕ} (s : RSBScheme k)
    (hq : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    (s.q (r - 1) < s.q r ∨ s.q r = 0) ∧
      (s.q r < s.q (r + 1) ∨ s.q r = 1) := by
  constructor
  · by_cases hr1 : r = 1
    · subst r
      simpa only [Nat.sub_self, s.q_zero] using
        (lt_or_eq_of_le (s.q_nonneg (p := 1) (by omega))).imp id Eq.symm
    · exact Or.inl (by simpa only [Nat.sub_add_cancel hr0] using hq (r - 1) (by omega) (by omega))
  · by_cases hrk : r ≤ k
    · exact Or.inl (hq r hr0 hrk)
    · have he : r + 1 = k + 2 := by omega
      simpa only [he, s.q_top] using lt_or_eq_of_le (s.q_le_one (p := r) (by omega))

/-- Proposition 4.7 for every level of a reduced fixed-level minimizer. -/
theorem section4TVarianceQ_zero_eq_overlap_of_reduced_min {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hq : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) :
    section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r := by
  have hd := s.overlap_directions_of_strict hq hr0 hr
  exact section4TVarianceQ_zero_eq_overlap_of_min_all_levels s β h hr0 hr hβ
    (by simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega)) hd.1 hd.2 hmin

variable {Ω : Type*} [MeasureSpace Ω]

/-- Every original fixed-level minimizer has an exactly equivalent reduced
minimizer satisfying the genuine endpoint stationarity at every physical
level. The original statement is not restricted to distinct overlap levels. -/
theorem exists_stationary_reduction_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hβ : β ≠ 0)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    ∃ l ≤ k, ∃ s' : RSBScheme l,
      (∀ p, p ≤ l → s'.m p < s'.m (p + 1)) ∧
      (∀ p, 1 ≤ p → p ≤ l → s'.q p < s'.q (p + 1)) ∧
      parisiFunctional s' β h = parisiFunctional s β h ∧
      (∀ t, guerraPsi s' β h t = guerraPsi s β h t) ∧
      (∀ n (U : Ω → EnergySpace n) t, t ∈ Set.Icc (0 : ℝ) 1 →
        guerraPhi n s' β h U t = guerraPhi n s β h U t) ∧
      (∀ s'' : RSBScheme l, parisiFunctional s' β h ≤ parisiFunctional s'' β h) ∧
      (∀ r, 1 ≤ r → r ≤ l + 1 →
        section4TVarianceQ s' β h r (s'.m (r - 1)) 0 = s'.q r) := by
  obtain ⟨l, hl, s', hm, hq, hfunc, hpsi, hphi, hmin'⟩ :=
    exists_strict_mass_overlap_reduction (Ω := Ω) s β h
  exact ⟨l, hl, s', hm, hq, hfunc, hpsi, hphi, hmin' hmin,
    fun _ hr0 hr => section4TVarianceQ_zero_eq_overlap_of_reduced_min s' β h hβ hm hq
      (hmin' hmin) hr0 hr⟩

end SpinGlass.Targets
