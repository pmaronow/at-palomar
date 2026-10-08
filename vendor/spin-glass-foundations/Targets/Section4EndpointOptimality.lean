module

public import Targets.Section4FirstVariation

@[expose] public section

/-!
# Fixed-level optimality at the lower Section 4 endpoint

At `u=q_(r-1)`, the inserted interval has a redundant zero-variance level.
For `r≥2` this level can be removed without changing the compulsory mass
`m_0=0`. Thus fixed-level minimality really does apply to the mass variation
at this endpoint. The first interval `r=1` is deliberately not included.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

/-- Raise one nonboundary mass, preserving the number of levels. -/
noncomputable def RSBScheme.raiseMass {k : ℕ} (s : RSBScheme k) (p : ℕ)
    (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1))) : RSBScheme k where
  m j := if j = p then m else s.m j
  q := s.q
  m_zero := by simp [show (0 : ℕ) ≠ p by omega, s.m_zero]
  m_top := by simp [show k + 1 ≠ p by omega, s.m_top]
  m_mono j hj := by
    by_cases he : j = p
    · subst j
      simpa [show p + 1 ≠ p by omega] using hm.2
    · by_cases he' : j + 1 = p
      · simp only [if_neg he, if_pos he']
        exact (he' ▸ s.m_mono j hj).trans hm.1
      · simpa only [if_neg he, if_neg he'] using s.m_mono j hj
  q_zero := s.q_zero
  q_top := s.q_top
  q_mono := s.q_mono

/-- The actual scalar recursion ignores a mass on a zero-variance interval. -/
theorem parisiF_raiseMass_zero_variance {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) {j : ℕ} (hj : j ≤ k + 2) :
    parisiF (s.raiseMass p hp0 hp m hm) β j = parisiF s β j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parisiF, parisiF, ih (by omega)]
    change parisiStep (if k + 1 - j = p then m else s.m (k + 1 - j))
      (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) _ = _
    by_cases he : k + 1 - j = p
    · have he' : k + 2 - j = p + 1 := by omega
      simp only [he, he', hq, sub_self, mul_zero]
      funext x
      simp only [parisiStep_zero_var]
    · rw [if_neg he]

/-- Both the recursion and the correction ignore the same zero-variance mass. -/
theorem parisiFunctional_raiseMass_zero_variance {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (p : ℕ) (hp0 : 1 ≤ p) (hp : p ≤ k) (m : ℝ)
    (hm : m ∈ Set.Icc (s.m p) (s.m (p + 1)))
    (hq : s.q (p + 1) = s.q p) :
    parisiFunctional (s.raiseMass p hp0 hp m hm) β h = parisiFunctional s β h := by
  unfold parisiFunctional
  rw [parisiF_raiseMass_zero_variance s β p hp0 hp m hm hq le_rfl]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  change (if j + 1 = p then m else s.m (j + 1)) *
    (s.q (j + 2) ^ 2 - s.q (j + 1) ^ 2) = _
  by_cases he : j + 1 = p
  · have he' : j + 2 = p + 1 := by omega
    simp [he, he', hq]
  · rw [if_neg he]

/-- An actual fixed-level competitor at the lower overlap endpoint.
The hypothesis `r≥2` ensures that deleting the redundant level preserves `m_0=0`. -/
theorem section4Phi_lower_overlap_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (s.m r))
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    section4Phi s β h r (s.m (r - 1)) (s.q (r - 1)) ≤
      section4Phi s β h r m (s.q (r - 1)) := by
  have hu : s.q (r - 1) ∈ Set.Icc (s.q (r - 1)) (s.q r) :=
    ⟨le_rfl, s.q_mono' r (by omega) (r - 1) (by omega)⟩
  let si := s.insertLevel r (by omega) hr m (s.q (r - 1)) hm hu
  have hm' : m ∈ Set.Icc (si.m (r - 1)) (si.m (r - 1 + 1)) := by
    simpa [si, RSBScheme.insertLevel, section4Mass, show r - 1 < r by omega,
      show r - 1 + 1 = r by omega] using (⟨hm.1, le_rfl⟩ : m ∈ Set.Icc (s.m (r - 1)) m)
  let sj := si.raiseMass (r - 1) (by omega) (by omega) m hm'
  have hq : si.q (r - 1 + 1) = si.q (r - 1) := by
    simp [si, RSBScheme.insertLevel, section5Rho, show r - 1 + 1 = r by omega,
      show r - 1 < r by omega]
  have he : sj.m (r - 1) = sj.m (r - 1 + 1) := by
    simp [sj, RSBScheme.raiseMass, si, RSBScheme.insertLevel, section4Mass,
      show r - 1 + 1 = r by omega]
  have H := hmin (sj.mergeEqualMass (r - 1) (by omega) he)
  rw [parisiFunctional_mergeEqualMass] at H
  change parisiFunctional s β h ≤ parisiFunctional
    (si.raiseMass (r - 1) (by omega) (by omega) m hm') β h at H
  rw [parisiFunctional_raiseMass_zero_variance si β h (r - 1) (by omega) (by omega) m hm' hq] at H
  change parisiFunctional s β h ≤ parisiFunctional
    (s.insertLevel r (by omega) hr m (s.q (r - 1)) hm hu) β h at H
  rwa [parisiFunctional_insertLevel, ← section4Phi_baseline s β h (by omega) hr hu] at H

/-- The lower-endpoint part of Proposition 4.8 for noninitial intervals.
Strictness of the adjacent mass gap provides actual admissible right variations;
near-global minimality is not substituted for fixed-level minimality. -/
theorem section4FirstVariation_lower_nonneg {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < s.m r)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    0 ≤ section4FirstVariation s β h r (s.q (r - 1)) := by
  have hu : s.q (r - 1) ∈ Set.Icc (s.q (r - 1)) (s.q r) :=
    ⟨le_rfl, s.q_mono' r (by omega) (r - 1) (by omega)⟩
  have H := (hasDerivAt_section4Phi_mass_baseline s β h (by omega) hr hu).tendsto_slope_zero_right
  apply ge_of_tendsto H
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hm)] with t ht
  have hm' : s.m (r - 1) + t ∈ Set.Icc (s.m (r - 1)) (s.m r) := by
    constructor <;> linarith [ht.1, ht.2]
  have hcomp := section4Phi_lower_overlap_min s β h hr0 hr hm' hmin
  exact smul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr hcomp)

end SpinGlass.Targets
