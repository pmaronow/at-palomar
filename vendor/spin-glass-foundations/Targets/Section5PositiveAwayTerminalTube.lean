module

public import Targets.Section5PhysicalNeighborOffDiagonalTube
public import Targets.Section5InterleavedMassPair
public import Targets.Section5InterleavedTimeZero
public import Targets.Section4StationarityReduction

@[expose] public section

/-!
# Off-diagonal tube at the terminal lower endpoint

For a physical level strictly below the last one, the terminal endpoint is
handled by keeping the trial overlap fixed at `q (k+1)`.  The right mass-gap
obstruction supplies the scalar witness, and the proved off-diagonal
interpolation transports it to nearby constrained overlaps.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem exists_uniform_constrainedPhi_terminal_lower_tube
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hrk : r < k) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    {t₀ : ℝ} (ht₀ : t₀ < 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (_hnear : parisiFunctional s β h ≤ parisiValue β h + ε) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u,
      |u - s.q (k + 1)| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hr : r ≤ k + 1 := by omega
  have hsm : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hm : s.m r < s.m k := by
    exact hsm
      (show (⟨r, by omega⟩ : Fin (k + 2)) < ⟨k, by omega⟩ by
        exact Fin.mk_lt_mk.mpr (by omega))
  have hmr : s.m (r - 1) < s.m r := by
    simpa only [Nat.sub_add_cancel hr0] using hmass (r - 1) (by omega)
  have hqr : s.q r < s.q (r + 1) := hqstrict r (by omega) (by omega)
  have hqtop : s.q k < s.q (k + 1) := hqstrict k (by omega) (by omega)
  have hqnonneg : 0 ≤ s.q (k + 1) := s.q_nonneg (by omega)
  have hd := s.overlap_directions_of_strict hqstrict hr0 hr
  have hv : |s.q (k + 1)| ∈ Icc (s.q k) (s.q (k + 1)) := by
    rw [abs_of_nonneg hqnonneg]
    exact ⟨hqtop.le, le_rfl⟩
  have hboundary : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ ℓ,
      0 < section5InterleavedOffDiagonalLambdaDeficit s β h r (k + 1)
        t (s.q (k + 1)) (s.q (k + 1)) ℓ := by
    intro t ht
    by_cases htzero : t = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
        (r := r) (j := k + 1) s β h hr0 hr (by omega) hβ hmr hd.1 hd.2 hmin
        (s.q (k + 1))
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedOffDiagonalLambdaDeficit]
      rw [htzero]
      have hsep : s.q r < s.q (k + 1) :=
        lt_of_lt_of_le hqr (s.q_mono' (k + 1) (by omega) (r + 1) (by omega))
      have hsquare : 0 < (s.q (k + 1) - s.q r) ^ 2 / 2 :=
        div_pos (sq_pos_of_pos (sub_pos.mpr hsep)) (by norm_num)
      linarith
    · have htpos : t ∈ Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2.trans_lt ht₀⟩
      have hmass' : s.m r < s.m ((k + 1) - 1) := by
        simpa only [show (k + 1) - 1 = k by omega] using hm
      have hbv : 0 < (1 - t) *
          (β ^ 2 * (s.q (r + 1) - s.q r)) :=
        mul_pos (sub_pos.mpr htpos.2)
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqr))
      have hcv : 0 < t *
          (β ^ 2 * (|s.q (k + 1)| - s.q ((k + 1) - 1))) := by
        rw [abs_of_nonneg hqnonneg, show (k + 1) - 1 = k by omega]
        exact mul_pos htpos.1
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqtop))
      have H := section5InterleavedScalarV_zero_lt_right_of_mass_lt
        (r := r) (j := k + 1) (t := t) (u := s.q (k + 1))
        s β h ⟨ht.1, ht.2.trans ht₀.le⟩ (by omega) (by omega)
          hv hmass' hbv hcv
      refine ⟨0, ?_⟩
      dsimp only [section5InterleavedOffDiagonalLambdaDeficit]
      simp only [zero_mul, add_zero]
      have hz : (s.q (k + 1) - s.q (k + 1)) ^ 2 = 0 := by ring
      rw [hz, mul_zero, sub_zero]
      exact sub_pos.mpr H
  exact exists_uniform_constrainedPhi_offDiagonal_physical_left_tube
    (r := r) (j := k + 1) s β h hr0 hr (by omega) (by omega)
    hqnonneg hv ht₀ hboundary

end SpinGlass.Targets
