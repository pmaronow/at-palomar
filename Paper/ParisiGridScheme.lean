module

public import Paper.ParisiCDFGrid
public import Targets.Milestones

@[expose] public section

/-!
# Uniform-grid Parisi schemes from actual probability measures

The grid CDF determines an actual admissible finite RSB scheme.  Repeated
endpoint overlaps are intentional: they retain atoms at zero and one while
respecting the compulsory endpoint masses of the finite Parisi recursion.
-/

open Set MeasureTheory

namespace Paper

open SpinGlass.Targets

theorem parisiCDF_eq_one_of_one_le (μ : ParisiMeasure) {t : ℝ} (ht : 1 ≤ t) :
    parisiCDF μ t = 1 := by
  have he : {q : Overlap | (q : ℝ) ≤ t} = Set.univ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact q.property.2.trans ht
  simp [parisiCDF, he]

/-- The endpoint list `0,0,1/d,...,1,1`, where `d=n+1`. -/
noncomputable def parisiGridSchemeOverlap (n p : ℕ) : ℝ :=
  ((min (p - 1) (n + 1) : ℕ) : ℝ) / (n + 1 : ℕ)

theorem parisiGridSchemeOverlap_monotone (n : ℕ) :
    Monotone (parisiGridSchemeOverlap n) := by
  intro p q hpq
  unfold parisiGridSchemeOverlap
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast min_le_min_right (n + 1) (Nat.sub_le_sub_right hpq 1)

@[simp] theorem parisiGridSchemeOverlap_zero (n : ℕ) :
    parisiGridSchemeOverlap n 0 = 0 := by simp [parisiGridSchemeOverlap]

@[simp] theorem parisiGridSchemeOverlap_one (n : ℕ) :
    parisiGridSchemeOverlap n 1 = 0 := by simp [parisiGridSchemeOverlap]

@[simp] theorem parisiGridSchemeOverlap_top (n : ℕ) :
    parisiGridSchemeOverlap n (n + 3) = 1 := by
  have he : n + 3 - 1 = n + 2 := by omega
  simp [parisiGridSchemeOverlap, he]
  positivity

@[simp] theorem parisiGridSchemeOverlap_penultimate (n : ℕ) :
    parisiGridSchemeOverlap n (n + 2) = 1 := by
  have he : n + 2 - 1 = n + 1 := by omega
  simp [parisiGridSchemeOverlap, he]
  positivity

noncomputable def parisiGridSchemeMass (μ : ParisiMeasure) (n p : ℕ) : ℝ :=
  if p = 0 then 0 else parisiCDF (parisiGridMeasure μ n) (parisiGridSchemeOverlap n p)

theorem parisiGridSchemeMass_monotone (μ : ParisiMeasure) (n : ℕ) :
    Monotone (parisiGridSchemeMass μ n) := by
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · simp [parisiGridSchemeMass, hq]
    · simpa [parisiGridSchemeMass, hq] using
        parisiCDF_nonneg (parisiGridMeasure μ n) (parisiGridSchemeOverlap n q)
  · have hq : q ≠ 0 := by omega
    simpa [parisiGridSchemeMass, hp, hq] using
      parisiCDF_monotone (parisiGridMeasure μ n)
        (parisiGridSchemeOverlap_monotone n hpq)

/-- The genuine finite RSB scheme determined by a finite grid probability law. -/
noncomputable def parisiGridRSBScheme (μ : ParisiMeasure) (n : ℕ) : RSBScheme (n + 1) where
  m := parisiGridSchemeMass μ n
  m_zero := by simp [parisiGridSchemeMass]
  m_top := by
    simp only [parisiGridSchemeMass, show n + 1 + 1 ≠ 0 by omega, ite_false]
    convert parisiCDF_eq_one_of_one_le (parisiGridMeasure μ n) (t := 1) le_rfl using 1
    simp
  m_mono := fun p _ => parisiGridSchemeMass_monotone μ n (Nat.le_succ p)
  q := parisiGridSchemeOverlap n
  q_zero := parisiGridSchemeOverlap_zero n
  q_top := by convert parisiGridSchemeOverlap_top n using 1 <;> omega
  q_mono := fun p _ => parisiGridSchemeOverlap_monotone n (Nat.le_succ p)

end Paper
