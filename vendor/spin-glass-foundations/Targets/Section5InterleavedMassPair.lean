module

public import Targets.Section5InterleavedBound

@[expose] public section

/-!
# Right outside-neighbor strictness from the actual witness mass pair

The equality-order contradiction uses only the strict inequality between
the physical witness mass and the interpolating witness mass. No strictness
of every mass in the scheme is needed. In particular this argument remains
available after exact redundant terminal padding.
-/

namespace SpinGlass.Targets

open MeasureTheory ProbabilityTheory

/-- The two genuine right-side witnesses require only their own strict mass
inequality; every other mass may coincide, including a redundant top mass. -/
theorem section5Interleaving_right_outside_obstruction_of_mass_lt {k : ℕ}
    (s : RSBScheme k) (β t u : ℝ) {r j : ℕ} (hj : j ≤ k + 1)
    (hrj : r + 1 < j) (hm : s.m r < s.m (j - 1))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (u - s.q (j - 1)))) :
    ¬(Section5InterleavingEqualityOrder s β t u r j ∧
      Section5InterleavingScalarOrder s β t u r j) := by
  let b : Section5MassTag k := Sum.inl ⟨r, by omega⟩
  let c : Section5MassTag k := Sum.inr ⟨j - 1, by omega⟩
  have hb : ¬section5TagShared r j b := lt_irrefl r
  have hc : section5TagShared r j c := by change j - 1 < j; omega
  have hcb : section5TagScalarMass s r j b = s.m r := by
    rw [section5TagScalarMass_eq_original]
    rfl
  have hcc : section5TagScalarMass s r j c = s.m (j - 1) := by
    rw [section5TagScalarMass_eq_original]
    simp only [c, section5TagOriginalLevel, Sum.elim_inr, if_pos (show j - 1 < j by omega)]
  refine section5Interleaving_equality_orders_incompatible s β t u r j b c ?_ ?_ hb hc ?_ ?_
  · exact hbv
  · simpa only [c, section5TaggedVariance, Sum.elim_inr, section5Rho,
      show j - 1 + 1 = j by omega, lt_self_iff_false, if_false, if_true,
      if_pos (show j - 1 < j by omega)] using hcv
  · rw [hcc]
    exact (s.m_nonneg (p := r) (by omega)).trans_lt hm
  · simpa only [hcb, hcc] using hm

/-- Genuine scalar endpoint strictness under only the witness mass gap. -/
theorem section5InterleavedScalarV_zero_lt_right_of_mass_lt {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hm : s.m r < s.m (j - 1))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1)))) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h :=
  strict_of_order_obstruction s β h r ht (by omega) hj hu
    (section5Interleaving_right_outside_obstruction_of_mass_lt s β t |u| hj hrj hm hbv hcv)

/-- The actual right-side gap with no strictness hypothesis on irrelevant
masses. Its scalar deficit is fixed before every system size and disorder. -/
theorem exists_constrainedPhi_interleaved_gap_right_of_mass_lt
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (ht : t ∈ Set.Icc 0 1) (hr0 : 1 ≤ r) (hj : j ≤ k + 1) (hrj : r + 1 < j)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) (hm : s.m r < s.m (j - 1))
    (hbv : 0 < (1 - t) * (β ^ 2 * (s.q (r + 1) - s.q r)))
    (hcv : 0 < t * (β ^ 2 * (|u| - s.q (j - 1)))) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = u) →
        constrainedPhi n s β h sk.U (k + 2 - r) t u ≤ 2 * guerraPsi s β h t - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr
      (section5InterleavedScalarV_zero_lt_right_of_mass_lt s β h ht hj hrj hu hm hbv hcv)
  · intro n hn sk hatt
    exact constrainedPhi_le_guerraPsi_sub_interleavedDeficit hn s β h sk hr0 (by omega)
      (by omega) hj ht hu hatt

end SpinGlass.Targets
