module

public import Paper.ParisiFiniteCells
public import Mathlib.MeasureTheory.Measure.Module

@[expose] public section

/-! Actual finite atomic probability laws represented by arbitrary finite RSB
schemes.  The compulsory endpoint masses telescope to total probability one. -/

open Set MeasureTheory
open scoped ENNReal

namespace Paper

open SpinGlass.Targets

noncomputable def parisiSchemeAtom {k : ℕ} (s : RSBScheme k) (i : Fin (k + 1)) : Overlap :=
  ⟨s.q (i + 1), s.q_nonneg (by omega), s.q_le_one (by omega)⟩

noncomputable def parisiSchemeRawMeasure {k : ℕ} (s : RSBScheme k) : Measure Overlap :=
  ∑ i : Fin (k + 1), ENNReal.ofReal (s.m (i + 1) - s.m i) • Measure.dirac (parisiSchemeAtom s i)

theorem parisiScheme_mass_telescope {k : ℕ} (s : RSBScheme k) (p : ℕ) :
    (∑ i ∈ Finset.range p, (s.m (i + 1) - s.m i)) = s.m p - s.m 0 := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih]; ring

theorem parisiSchemeRawMeasure_univ {k : ℕ} (s : RSBScheme k) :
    parisiSchemeRawMeasure s Set.univ = 1 := by
  simp only [parisiSchemeRawMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun (i : Fin (k + 1)) _ => sub_nonneg.mpr (s.m_mono i (by omega)))]
  have hsum : (∑ i : Fin (k + 1), (s.m (i + 1) - s.m i)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => s.m (i + 1) - s.m i),
      parisiScheme_mass_telescope, s.m_top, s.m_zero]
    norm_num
  rw [hsum, ENNReal.ofReal_one]

noncomputable def parisiSchemeMeasure {k : ℕ} (s : RSBScheme k) : ParisiMeasure :=
  ⟨parisiSchemeRawMeasure s, ⟨parisiSchemeRawMeasure_univ s⟩⟩

theorem parisiCDF_scheme_cell {k : ℕ} (s : RSBScheme k)
    {p : ℕ} (hp : p ≤ k + 1) {t : ℝ} (ht : t ∈ Ico (s.q p) (s.q (p + 1))) :
    parisiCDF (parisiSchemeMeasure s) t = s.m p := by
  have hmem (i : Fin (k + 1)) : (parisiSchemeAtom s i : ℝ) ≤ t ↔ (i : ℕ) < p := by
    constructor
    · intro hi
      by_contra hn
      have hpi : p + 1 ≤ (i : ℕ) + 1 := by omega
      have hq : s.q (p + 1) ≤ s.q ((i : ℕ) + 1) :=
        s.q_mono' ((i : ℕ) + 1) (by omega) (p + 1) hpi
      change s.q ((i : ℕ) + 1) ≤ t at hi
      linarith [ht.2]
    · intro hi
      change s.q ((i : ℕ) + 1) ≤ t
      exact (s.q_mono' p (by omega) ((i : ℕ) + 1) (by omega)).trans ht.1
  have he : (parisiSchemeRawMeasure s) {q : Overlap | (q : ℝ) ≤ t} =
      ∑ i ∈ Finset.range p, ENNReal.ofReal (s.m (i + 1) - s.m i) := by
    simp only [parisiSchemeRawMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (isClosed_le continuous_subtype_val continuous_const).measurableSet,
      smul_eq_mul, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, hmem]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < p then
      ENNReal.ofReal (s.m (i + 1) - s.m i) else 0)]
    calc
      (∑ i ∈ Finset.range (k + 1), if i < p then ENNReal.ofReal (s.m (i + 1) - s.m i) else 0) =
          ∑ i ∈ Finset.range p, if i < p then ENNReal.ofReal (s.m (i + 1) - s.m i) else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hp)
        intro i hi hni
        simp only [Finset.mem_range] at hni
        simp [hni]
      _ = ∑ i ∈ Finset.range p, ENNReal.ofReal (s.m (i + 1) - s.m i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ite_eq_left (Finset.mem_range.mp hi)]
  have hnonneg : ∀ i ∈ Finset.range p, 0 ≤ s.m (i + 1) - s.m i := by
    intro i hi
    exact sub_nonneg.mpr (s.m_mono i (by have := Finset.mem_range.mp hi; omega))
  change ((parisiSchemeRawMeasure s) {q : Overlap | (q : ℝ) ≤ t}).toReal = _
  rw [he, ← ENNReal.ofReal_sum_of_nonneg hnonneg, parisiScheme_mass_telescope,
    s.m_zero, sub_zero, ENNReal.toReal_ofReal (s.m_nonneg (by omega))]

/-- On every finite slab, the correction is the integral of the scheme's
literal constant CDF coefficient, including empty slabs and repeated nodes. -/
theorem parisiSchemeCorrection_cell {k : ℕ} (s : RSBScheme k)
    {p : ℕ} (hp : p ≤ k + 1) :
    (∫ t in s.q p..s.q (p + 1), t * parisiCDF (parisiSchemeMeasure s) t) =
      s.m p * (s.q (p + 1) ^ 2 - s.q p ^ 2) / 2 := by
  have he : EqOn (fun t => t * parisiCDF (parisiSchemeMeasure s) t)
      (fun t => t * s.m p) (uIoo (s.q p) (s.q (p + 1))) := by
    rw [uIoo_of_le (s.q_mono p hp)]
    intro t ht
    dsimp only
    rw [parisiCDF_scheme_cell s hp ⟨ht.1.le, ht.2⟩]
  rw [intervalIntegral.integral_congr_uIoo he, intervalIntegral.integral_mul_const,
    integral_id]
  ring

/-- Exact representation of the actual CDF correction by the finite RSB
sum. No measure-representation hypothesis is supplied. -/
theorem parisiScheme_cdf_integral {k : ℕ} (s : RSBScheme k) :
    (∫ t in (0 : ℝ)..1, t * parisiCDF (parisiSchemeMeasure s) t) =
      (∑ p ∈ Finset.range (k + 1),
        s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2)) / 2 := by
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (a := s.q) (n := k + 2)
    (fun p _ => parisiCorrection_intervalIntegrable (parisiSchemeMeasure s) _ _)
  rw [s.q_zero, s.q_top] at hpartition
  rw [← hpartition]
  have hcells : (∑ p ∈ Finset.range (k + 2),
      ∫ t in s.q p..s.q (p + 1), t * parisiCDF (parisiSchemeMeasure s) t) =
      ∑ p ∈ Finset.range (k + 2),
        s.m p * (s.q (p + 1) ^ 2 - s.q p ^ 2) / 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact parisiSchemeCorrection_cell s (by have := Finset.mem_range.mp hp; omega)
  rw [hcells, show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [s.m_zero, zero_mul, zero_div, add_zero]
  rw [Finset.sum_div]

/-- The correction term agrees exactly with the finite backend's functional
normalization, with coefficient beta squared over four. -/
theorem parisiScheme_correction_eq {k : ℕ} (s : RSBScheme k) (β : ℝ) :
    β ^ 2 / 2 * (∫ t in (0 : ℝ)..1, t * parisiCDF (parisiSchemeMeasure s) t) =
      β ^ 2 / 4 * ∑ p ∈ Finset.range (k + 1),
        s.m (p + 1) * (s.q (p + 2) ^ 2 - s.q (p + 1) ^ 2) := by
  rw [parisiScheme_cdf_integral]
  ring

end Paper
