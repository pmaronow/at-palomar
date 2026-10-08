module

public import Targets.Section5AdjacentStrictCompact
public import Targets.Section5InterleavedRightCompact
public import Targets.Section5TerminalCompact
public import Targets.Section4StationarityReduction

@[expose] public section

/-!
# Concrete compact pieces for the positive outer region

Each theorem below is one member of the finite partition used in the global
positive-away assembly.  The sets are explicit compact rectangles; all gaps
come from the checked trial or padded-terminal estimates.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_positive_left_outer_piece
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr : r ≤ k + 1) (hj0 : 1 ≤ j)
    (hjr : j + 1 < r) (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q j < s.q (j + 1))
    (hqr : s.q (r - 1) < s.q r) (hqrnext : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈
      (Icc (0 : ℝ) t₀ ×ˢ Icc (s.q (j - 1)) (s.q j)),
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let S : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q (j - 1)) (s.q j)
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod isCompact_Icc
  apply exists_uniform_constrainedPhi_gap_on_adjacent_left_strict
    (Ω := Ω) s β h hβ hr hj0 (by omega) hjr hm hqj hqr hqrnext hmin ht₀ hS
  · intro z hz
    exact hz.1
  · intro z hz
    have hq0 : 0 ≤ s.q (j - 1) := s.q_nonneg (by omega)
    exact hq0.trans hz.2.1
  · intro z hz
    exact ⟨hz.2.1, lt_of_le_of_lt hz.2.2 hqj⟩
  · intro z hz
    have hltj : z.2 < s.q (j + 1) := lt_of_le_of_lt hz.2.2 hqj
    have hlt : z.2 < s.q r := lt_of_lt_of_le hltj
      ((s.q_mono' (r - 1) (by omega) (j + 1) (by omega)).trans hqr.le)
    exact hlt.ne

theorem exists_uniform_constrainedPhi_positive_right_outer_piece
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 2 ≤ j) (hj : j + 1 ≤ k + 1) (hrj : r + 1 < j)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqj : s.q (j - 1) < s.q j)
    (hqprev : s.q (r - 1) < s.q r) (hqr : s.q r < s.q (r + 1))
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈
      (Icc (0 : ℝ) t₀ ×ˢ Icc (s.q j) (s.q (j + 1))),
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let S : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ Icc (s.q j) (s.q (j + 1))
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod isCompact_Icc
  apply exists_uniform_constrainedPhi_gap_on_adjacent_right_strict
    (Ω := Ω) s β h hβ hr0 hr hj0 hj hrj hm hqj hqprev hqr hmin ht₀ hS
  · intro z hz
    exact hz.1
  · intro z hz
    have hq0 : 0 ≤ s.q j := s.q_nonneg (by omega)
    exact hq0.trans hz.2.1
  · intro z hz
    exact ⟨lt_of_lt_of_le hqj hz.2.1,
      hz.2.2⟩
  · intro z hz
    have hjlower : s.q (j - 1) < z.2 := lt_of_lt_of_le hqj hz.2.1
    have hidx : r + 1 ≤ j - 1 := by omega
    have hlt : s.q r < z.2 := lt_of_lt_of_le hqr
      ((s.q_mono' (j - 1) (by omega) (r + 1) hidx).trans hjlower.le)
    exact hlt.ne'

theorem exists_uniform_constrainedPhi_positive_terminal_outer_piece
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k)
    (hmass : s.m r < s.m (k + 1))
    (hq : s.q r < s.q (r + 1))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ a : ℝ} (ht₀ : t₀ < 1)
    (ha : s.q (k + 1) < a) (_ha1 : a ≤ 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈
      (Icc (0 : ℝ) t₀ ×ˢ Icc a 1),
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) t₀ ×ˢ Icc a 1
  have hS : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.prod isCompact_Icc
  apply exists_uniform_constrainedPhi_right_terminal_padded
    (Ω := Ω) s β h hβ hr0 hr hmass hq hQ ht₀ hS
  · intro z hz
    exact hz.1
  · intro z hz
    exact ⟨lt_of_lt_of_le ha hz.2.1, hz.2.2⟩

end SpinGlass.Targets
