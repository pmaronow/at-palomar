module

public import Targets.Section5Interleaving
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-!
# Cumulative overlaps for the tagged construction of Proposition 5.7

The overlap advances exactly at interpolation tags. Physical tags leave it
unchanged, including ties of physical and interpolation masses. Counting tags
before a position avoids identifying distinct entries with equal mass.
-/

open scoped BigOperators

namespace SpinGlass.Targets

/-- Number of interpolation tags strictly before the given merged position. -/
noncomputable def section5InterleavingRank {k : ℕ} (s : RSBScheme k)
    (r j i : ℕ) : ℕ :=
  ∑ p : Fin (k + 3), if ((section5Interleaving s r j).symm (Sum.inr p)).val < i
    then 1 else 0

theorem section5InterleavingRank_zero {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    section5InterleavingRank s r j 0 = 0 := by
  simp [section5InterleavingRank]

theorem section5InterleavingRank_last {k : ℕ} (s : RSBScheme k) (r j : ℕ) :
    section5InterleavingRank s r j ((k + 2) + (k + 3)) = k + 3 := by
  simp only [section5InterleavingRank, Fin.is_lt, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem section5InterleavingRank_at_interpolating {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (p : Fin (k + 3)) :
    section5InterleavingRank s r j
      ((section5Interleaving s r j).symm (Sum.inr p)) = p := by
  have he (q : Fin (k + 3)) :
      ((section5Interleaving s r j).symm (Sum.inr q)).val <
        ((section5Interleaving s r j).symm (Sum.inr p)).val ↔ q < p :=
    (strictMono_section5Interleaving_interpolating s r hj).lt_iff_lt
  simp only [section5InterleavingRank, he]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun q : Fin (k + 3) => q < p) = Finset.Iio p := by
    ext q
    simp
  rw [hf]
  simp

theorem section5InterleavingRank_succ {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavingRank s r j (i + 1) = section5InterleavingRank s r j i +
      (match section5Interleaving s r j i with | Sum.inl _ => 0 | Sum.inr _ => 1) := by
  classical
  have hsplit (p : Fin (k + 3)) :
      (if ((section5Interleaving s r j).symm (Sum.inr p)).val < i.val + 1
        then 1 else 0) =
      (if ((section5Interleaving s r j).symm (Sum.inr p)).val < i.val
        then 1 else 0) +
      (if (section5Interleaving s r j).symm (Sum.inr p) = i then 1 else 0) := by
    by_cases h : (section5Interleaving s r j).symm (Sum.inr p) = i
    · simp [h]
    · have hn : ((section5Interleaving s r j).symm (Sum.inr p)).val ≠ i.val :=
        fun he => h (Fin.ext he)
      by_cases hlt : ((section5Interleaving s r j).symm (Sum.inr p)).val < i.val
      · simp [h, hlt, show ((section5Interleaving s r j).symm (Sum.inr p)).val <
          i.val + 1 by omega]
      · simp [h, hlt, show ¬((section5Interleaving s r j).symm (Sum.inr p)).val <
          i.val + 1 by omega]
  simp only [section5InterleavingRank, hsplit, Finset.sum_add_distrib]
  congr 1
  have he (p : Fin (k + 3)) : (section5Interleaving s r j).symm (Sum.inr p) = i ↔
      Sum.inr p = section5Interleaving s r j i := Equiv.symm_apply_eq _
  simp_rw [he]
  cases h : section5Interleaving s r j i with
  | inl p => simp
  | inr p => simp

/-- Cumulative trial overlap, extended constantly after the last merged step. -/
noncomputable def section5InterleavedRho {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  section5Rho s j u (section5InterleavingRank s r j i)

theorem section5InterleavedRho_endpoints {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (u : ℝ) :
    section5InterleavedRho s r j u 0 = 0 ∧
      section5InterleavedRho s r j u ((k + 2) + (k + 3)) = 1 := by
  simpa only [section5InterleavedRho, section5InterleavingRank_zero,
    section5InterleavingRank_last] using section5Rho_endpoints s hj0 hj u

theorem section5InterleavedRho_at_interpolating {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) (p : Fin (k + 3)) :
    section5InterleavedRho s r j u
      ((section5Interleaving s r j).symm (Sum.inr p)) = section5Rho s j u p := by
  simp only [section5InterleavedRho, section5InterleavingRank_at_interpolating s r hj]

theorem section5InterleavedRho_at_cutoff {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) :
    section5InterleavedRho s r j u (section5InterleavingCutoff s r hj) = u := by
  rw [section5InterleavingCutoff, section5InterleavedRho_at_interpolating s r hj]
  simp [section5Rho]

/-- Each physical tag is an exact zero increment of the cumulative trial overlap. -/
theorem section5InterleavedRho_physical_succ {k : ℕ} (s : RSBScheme k)
    (r j : ℕ) (u : ℝ) (p : Fin (k + 2)) :
    section5InterleavedRho s r j u
        (((section5Interleaving s r j).symm (Sum.inl p)).val + 1) =
      section5InterleavedRho s r j u
        ((section5Interleaving s r j).symm (Sum.inl p)) := by
  simp only [section5InterleavedRho, section5InterleavingRank_succ,
    Equiv.apply_symm_apply, add_zero]

/-- At an interpolation tag the original inserted overlap advances by one level. -/
theorem section5InterleavedRho_interpolating_succ {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) (p : Fin (k + 3)) :
    section5InterleavedRho s r j u
        (((section5Interleaving s r j).symm (Sum.inr p)).val + 1) =
      section5Rho s j u (p + 1) := by
  simp only [section5InterleavedRho, section5InterleavingRank_succ,
    Equiv.apply_symm_apply, section5InterleavingRank_at_interpolating s r hj]

theorem section5InterleavedRho_mono {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavedRho s r j u i ≤ section5InterleavedRho s r j u (i + 1) := by
  have he : i = (section5Interleaving s r j).symm (section5Interleaving s r j i) :=
    (Equiv.symm_apply_apply _ _).symm
  cases h : section5Interleaving s r j i with
  | inl p =>
    rw [h] at he
    rw [he, section5InterleavedRho_physical_succ]
  | inr p =>
    rw [h] at he
    rw [he, section5InterleavedRho_interpolating_succ s r hj,
      section5InterleavedRho_at_interpolating s r hj]
    exact section5Rho_mono s hj hu (by omega)

/-- The tagged correction is the actual difference of squared cumulative overlaps. -/
theorem section5InterleavedRho_trial_increment {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (β u : ℝ)
    (i : Fin ((k + 2) + (k + 3))) :
    β ^ 2 / 2 * ((section5InterleavedRho s r j u (i + 1)) ^ 2 -
      (section5InterleavedRho s r j u i) ^ 2) =
      section5TaggedTrialIncrement s β u j (section5Interleaving s r j i) := by
  have he : i = (section5Interleaving s r j).symm (section5Interleaving s r j i) :=
    (Equiv.symm_apply_apply _ _).symm
  cases h : section5Interleaving s r j i with
  | inl p =>
    rw [h] at he
    rw [he, section5InterleavedRho_physical_succ]
    simp [section5TaggedTrialIncrement]
  | inr p =>
    rw [h] at he
    rw [he, section5InterleavedRho_interpolating_succ s r hj,
      section5InterleavedRho_at_interpolating s r hj]
    simp [section5TaggedTrialIncrement]

/-- Equation (5.36), now for the cumulative merged overlaps rather than formal increments. -/
theorem section5InterleavedRho_correction {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ) :
    (∑ i, (if i < section5InterleavingCutoff s r hj then (2 : ℝ) else 1) *
      section5InterleavedMass s r j i *
        (β ^ 2 / 2 * ((section5InterleavedRho s r j u (i + 1)) ^ 2 -
          (section5InterleavedRho s r j u i) ^ 2))) = 2 * parisiCorrection s β := by
  simp_rw [section5InterleavedRho_trial_increment s r hj]
  exact section5Interleaving_correction s β u r hj0 hj

/-- Natural-indexed masses for the finite interpolation, extended by the terminal mass. -/
noncomputable def section5InterleavedMassNat {k : ℕ} (s : RSBScheme k)
    (r j i : ℕ) : ℝ :=
  if hi : i < (k + 2) + (k + 3) then section5InterleavedMass s r j ⟨i, hi⟩ else 1

theorem section5InterleavedMassNat_coe {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavedMassNat s r j i = section5InterleavedMass s r j i := by
  simp [section5InterleavedMassNat]

/-- The actual two-replica deterministic correction of the merged construction.
The sign is kept explicit; it squares out only in this trial-energy identity. -/
theorem section5Interleaved_pairCorrection {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ)
    {e : ℝ} (he : e ^ 2 = 1) :
    pairCascadeCorrection β (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j u)
      (fun l => e * section5InterleavedRho s r j u
        (min l (section5InterleavingCutoff s r hj))) (2 * k + 4) =
        2 * parisiCorrection s β := by
  rw [pairCascadeCorrection_eq_signed_split β _ _ _ _ he]
  have hN : 2 * k + 4 + 1 = (k + 2) + (k + 3) := by omega
  rw [hN, ← Fin.sum_univ_eq_sum_range]
  simp only [section5InterleavedMassNat_coe]
  exact section5InterleavedRho_correction s r hj0 hj β u

/-- The actual interpolating overlap increment at a tagged position; it vanishes
on physical tags without requiring any overlap or mass to be distinct. -/
theorem section5InterleavedRho_increment {k : ℕ} (s : RSBScheme k)
    (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (u : ℝ)
    (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavedRho s r j u (i + 1) - section5InterleavedRho s r j u i =
      Sum.elim (fun _ : Fin (k + 2) => (0 : ℝ))
        (fun p : Fin (k + 3) => section5Rho s j u (p + 1) - section5Rho s j u p)
          (section5Interleaving s r j i) := by
  have he : i = (section5Interleaving s r j).symm (section5Interleaving s r j i) :=
    (Equiv.symm_apply_apply _ _).symm
  cases h : section5Interleaving s r j i with
  | inl p =>
    rw [h] at he
    rw [he, section5InterleavedRho_physical_succ]
    simp
  | inr p =>
    rw [h] at he
    rw [he, section5InterleavedRho_interpolating_succ s r hj,
      section5InterleavedRho_at_interpolating s r hj]
    simp

end SpinGlass.Targets
