module

public import Paper.ParisiGridScheme

@[expose] public section

/-! The actual rounded probability law has precisely the CDF coefficient
used by each nonempty finite Parisi slab.  Endpoint atoms use the right cell. -/

open Set MeasureTheory

namespace Paper

theorem parisiCDF_grid_eq_node (μ : ParisiMeasure) (n i : ℕ) {t : ℝ}
    (ht : t ∈ Ico ((i : ℝ) / (n + 1 : ℕ)) ((i + 1 : ℕ) / (n + 1 : ℕ))) :
    parisiCDF (parisiGridMeasure μ n) t =
      parisiCDF (parisiGridMeasure μ n) ((i : ℝ) / (n + 1 : ℕ)) := by
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have he : {q : Overlap | (parisiGridRound n q : ℝ) ≤ t} =
      {q : Overlap | (parisiGridRound n q : ℝ) ≤ (i : ℝ) / (n + 1 : ℕ)} := by
    ext q
    simp only [mem_setOf_eq]
    constructor
    · intro hq
      have hb : (Nat.ceil ((n + 1 : ℕ) * (q : ℝ)) : ℝ) / (n + 1 : ℕ) <
          (i + 1 : ℕ) / (n + 1 : ℕ) := hq.trans_lt ht.2
      have hb' : (Nat.ceil ((n + 1 : ℕ) * (q : ℝ)) : ℝ) < (i + 1 : ℕ) :=
        (div_lt_div_iff_of_pos_right hd).mp hb
      have hi : Nat.ceil ((n + 1 : ℕ) * (q : ℝ)) ≤ i := by
        exact Nat.lt_succ_iff.mp (by exact_mod_cast hb')
      change (Nat.ceil ((n + 1 : ℕ) * (q : ℝ)) : ℝ) / (n + 1 : ℕ) ≤ _
      apply div_le_div_of_nonneg_right _ hd.le
      exact_mod_cast hi
    · intro hq
      exact hq.trans ht.1
  unfold parisiCDF parisiGridMeasure
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_parisiGridRound n)
      (isClosed_le continuous_subtype_val continuous_const).measurableSet,
    Measure.map_apply (measurable_parisiGridRound n)
      (isClosed_le continuous_subtype_val continuous_const).measurableSet]
  exact congrArg (fun E : Set Overlap => ((μ : Measure Overlap) E).toReal) he

theorem parisiCDF_grid_eq_scheme_mass (μ : ParisiMeasure) (n p : ℕ)
    (hp0 : 1 ≤ p) (hp : p ≤ n + 1) {t : ℝ}
    (ht : t ∈ Ico ((parisiGridRSBScheme μ n).q p)
      ((parisiGridRSBScheme μ n).q (p + 1))) :
    parisiCDF (parisiGridMeasure μ n) t = (parisiGridRSBScheme μ n).m p := by
  have hi : p - 1 ≤ n + 1 := by omega
  have he : p + 1 - 1 = p := by omega
  have he' : p - 1 + 1 = p := by omega
  have hq0 : (parisiGridRSBScheme μ n).q p = (p - 1 : ℕ) / (n + 1 : ℕ) := by
    simp [parisiGridRSBScheme, parisiGridSchemeOverlap, Nat.min_eq_left hi]
  have hq1 : (parisiGridRSBScheme μ n).q (p + 1) = (p : ℝ) / (n + 1 : ℕ) := by
    simp [parisiGridRSBScheme, parisiGridSchemeOverlap, he, Nat.min_eq_left hp]
  have hh := parisiCDF_grid_eq_node μ n (p - 1) (t := t)
    (by simpa only [hq0, hq1, he'] using ht)
  simpa [parisiGridRSBScheme, parisiGridSchemeMass, show p ≠ 0 by omega,
    parisiGridSchemeOverlap, Nat.min_eq_left hi] using hh

theorem exists_parisiGrid_right_cell (μ : ParisiMeasure) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ico 0 1) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ n + 1 ∧
      t ∈ Ico ((parisiGridRSBScheme μ n).q p) ((parisiGridRSBScheme μ n).q (p + 1)) ∧
      (parisiGridRSBScheme μ n).q p < (parisiGridRSBScheme μ n).q (p + 1) := by
  have hd : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hdt : 0 ≤ (n + 1 : ℕ) * t := mul_nonneg hd.le ht.1
  let p : ℕ := Nat.floor ((n + 1 : ℕ) * t) + 1
  have hp0 : 1 ≤ p := by dsimp [p]; omega
  have hp : p ≤ n + 1 := by
    have hh : (n + 1 : ℕ) * t < (n + 1 : ℕ) := by nlinarith [ht.2]
    have hf : Nat.floor ((n + 1 : ℕ) * t) < n + 1 := (Nat.floor_lt hdt).mpr hh
    dsimp [p]
    omega
  have hq0 : (parisiGridRSBScheme μ n).q p = (p - 1 : ℕ) / (n + 1 : ℕ) := by
    simp [parisiGridRSBScheme, parisiGridSchemeOverlap,
      Nat.min_eq_left (by omega : p - 1 ≤ n + 1)]
  have hq1 : (parisiGridRSBScheme μ n).q (p + 1) = (p : ℝ) / (n + 1 : ℕ) := by
    simp [parisiGridRSBScheme, parisiGridSchemeOverlap, Nat.add_sub_cancel, Nat.min_eq_left hp]
  have hcell : t ∈ Ico ((parisiGridRSBScheme μ n).q p)
      ((parisiGridRSBScheme μ n).q (p + 1)) := by
    rw [hq0, hq1]
    constructor
    · apply (div_le_iff₀ hd).mpr
      simpa only [p, Nat.add_sub_cancel, mul_comm] using Nat.floor_le hdt
    · apply (lt_div_iff₀ hd).mpr
      simpa only [p, Nat.cast_add, Nat.cast_one, mul_comm] using
        Nat.lt_floor_add_one ((n + 1 : ℕ) * t)
  exact ⟨p, hp0, hp, hcell, hcell.1.trans_lt hcell.2⟩

end Paper
