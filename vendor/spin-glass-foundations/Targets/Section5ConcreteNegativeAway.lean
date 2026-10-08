module

public import Targets.Section5SignCrossing
public import Targets.Section5LeftOffDiagonalTube
public import Targets.Section5SignedInitialOffDiagonalEndpoint
public import Targets.Section5NegativeInitialCompact
public import Targets.Section5NegativeInitialBeyondCompact
public import Targets.Section5NegativeInitialTerminalCompact
public import Targets.Section5SignedAwayAssembly

@[expose] public section

/-! Concrete assembly of the full negative away region at one physical level. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- When the last genuine breakpoint is strictly above `q₁`, the padded
terminal comparison is already strict at its closed left endpoint. -/
theorem exists_uniform_constrainedPhi_negative_initial_terminal_closed
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hβ : β ≠ 0) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2)
    (hqlast : s.q 1 < s.q (k + 1))
    (hQ : section4TVarianceQ s β h 1 (s.m 0) 0 = s.q 1)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 < 0 ∧ |z.2| ∈ Icc (s.q (k + 1)) 1) :
    ∃ δ > (0 : ℝ), ∀ z ∈ S, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
  let sp := s.padOneLast
  have hmp : 0 < sp.m 1 := by
    simpa only [sp, s.padOneLast_m (p := 1) (by omega)] using hm
  have hq1p : 0 < sp.q 1 := by
    simpa only [sp, s.padOneLast_q (p := 1) (by omega)] using hq1
  have hqp : sp.q 1 < sp.q 2 := by
    simpa only [sp, s.padOneLast_q (p := 1) (by omega),
      s.padOneLast_q (p := 2) (by omega)] using hq
  have hQp : section4TVarianceQ sp β h 1 (sp.m 0) 0 = sp.q 1 := by
    dsimp only [sp]
    rw [s.padOneLast_m (p := 0) (by omega),
      section4TVarianceQ_padOneLast s β h (by omega) (by omega), hQ,
      s.padOneLast_q (p := 1) (by omega)]
  have htrial : ∀ z ∈ S, |z.2| ∈
      Icc (sp.q ((k + 2) - 1)) (sp.q (k + 2)) := by
    intro z hz
    have H := (hu z hz).2
    simpa only [show k + 2 - 1 = k + 1 by omega, sp,
      s.padOneLast_q (p := k + 1) (by omega),
      s.padOneLast_q (p := k + 2) (by omega), s.q_top, Set.mem_Icc] using H
  have hpos : ∀ z ∈ S, ∃ ℓ,
      0 < section5InterleavedLambdaDeficit sp β h 1 (k + 2) z.1 z.2 ℓ := by
    intro z hz
    have hbelow : sp.q 1 < |z.2| := by
      have H := hqlast.trans_le (hu z hz).2.1
      simpa only [sp, s.padOneLast_q (p := 1) (by omega)] using H
    by_cases htzero : z.1 = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q
        sp β h (r := 1) (j := k + 2) le_rfl (by omega) (by omega) z.2
      rw [hQp] at H
      have hsub : 0 < (sp.q 1 - z.2) ^ 2 / 2 := by
        exact div_pos (sq_pos_of_pos (sub_pos.mpr
          (lt_of_lt_of_le (hu z hz).1 (sp.q_nonneg (by omega))))) (by norm_num)
      refine ⟨ℓ, ?_⟩
      dsimp only [section5InterleavedLambdaDeficit]
      rw [htzero]
      linarith
    · have htime : z.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero),
          (ht z hz).2.trans_lt ht₀⟩
      have H := section5InterleavedScalarV_zero_lt_negative_of_q1_pos
        sp β h hβ htime (r := 1) le_rfl (j := k + 2) (by omega) (by omega)
          hmp hq1p hqp (hu z hz).1 hbelow (htrial z hz)
      refine ⟨0, ?_⟩
      simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
      exact sub_pos.mpr H
  obtain ⟨δ, hδ, H⟩ := exists_uniform_constrainedPhi_gap_on_compact_trial
    (Ω := Ω) sp β h (r := 1) (j := k + 2) le_rfl (by omega)
      (by omega) (by omega) hS
      (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  have Hp := H z hz hn sk hatt
  simpa only [show (k + 1) + 2 - 1 = (k + 1) + 1 by omega,
    sp, constrainedPhi_padOneLast, guerraPsi_padOneLast] using Hp

/-- Full negative half-line at the first physical level when `q₁>0`.
The two explicit tubes remove the only sign/breakpoint boundary problems;
the remaining closed bands are handled by the existing compact modules. -/
theorem exists_uniform_constrainedPhi_negative_all_initial_q1_pos
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ)
    (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hq1 : 0 < s.q 1)
    (hQ : section4TVarianceQ s β h 1 (s.m 0) 0 = s.q 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    {t₀ : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hm01 : s.m 0 < s.m 1 := hmass 0 (by omega)
  have hright : s.q 1 < s.q 2 ∨ s.q 1 = 1 := by
    by_cases hk : 1 ≤ k
    · exact Or.inl (hqstrict 1 (by omega) hk)
    · have hk0 : k = 0 := by omega
      have htop : s.q 2 = 1 := by simpa only [hk0] using s.q_top
      rcases (s.q_mono' 2 (by omega) 1 (by omega)).lt_or_eq with H | H
      · exact Or.inl H
      · exact Or.inr (H.trans htop)
  obtain ⟨ρ0, hρ0, δ0, hδ0, Hzero⟩ :=
    exists_uniform_constrainedPhi_initial_left_two_sided (Ω := Ω)
      s β h ε hβ hm01 hright ht₀ (by norm_num : (0 : ℝ) ≤ 535)
      hmin hnear hsmall
      (fun v hv w hw => section4THessianSquare_lipschitz_uniform
        s β h (r := 1) le_rfl (by omega)
        (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hv)
        (by simpa only [Nat.sub_self, s.q_zero, sub_zero] using hw)) hq1
  obtain ⟨ρb, hρb, δb, hδb, Hbreak⟩ :=
    exists_uniform_constrainedPhi_signed_initial_breakpoint_tube
      (Ω := Ω) s β h ε hβ hm01 hright ht₀ hq1 hmin hnear hsmall
  let Sreg : Fin (k + 1) → Set (ℝ × ℝ) := fun p =>
    Icc (0 : ℝ) t₀ ×ˢ
      (Icc (-1 : ℝ) 0 ∩ {u : ℝ | ρ0 / 2 ≤ |u|} ∩
        {u : ℝ | ρb / 2 ≤ |u - (-s.q 1)|} ∩
        {u : ℝ | |u| ∈ Icc (s.q (p : ℕ)) (s.q ((p : ℕ) + 1))})
  have hSreg (p : Fin (k + 1)) : IsCompact (Sreg p) := by
    apply isCompact_Icc.prod
    apply ((isCompact_Icc.inter_right
      (isClosed_le continuous_const continuous_abs)).inter_right
      (isClosed_le continuous_const (by fun_prop))).inter_right
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hureg (p : Fin (k + 1)) : ∀ z ∈ Sreg p, z.2 < 0 := by
    intro z hz
    have ha : 0 < |z.2| := (half_pos hρ0).trans_le hz.2.1.1.2
    exact lt_of_le_of_ne hz.2.1.1.1.2 (abs_pos.mp ha)
  have Hreg (p : Fin (k + 1)) : ∃ δ > (0 : ℝ),
      ∀ z ∈ Sreg p, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
    by_cases hp0 : (p : ℕ) = 0
    · exact exists_uniform_constrainedPhi_negative_initial_trial (Ω := Ω)
        s β h ε hβ hm01 hright ht₀ (hSreg p)
          (fun z hz => hz.1) (fun z hz => ⟨hureg p z hz, by
            have H : |z.2| ∈ Icc (s.q (p : ℕ)) (s.q ((p : ℕ) + 1)) := hz.2.2
            simpa only [hp0, s.q_zero] using H⟩) hmin hnear hsmall
    · have hj0 : 2 ≤ (p : ℕ) + 1 := by omega
      have hj : (p : ℕ) + 1 ≤ k + 1 := by omega
      have hq12 : s.q 1 < s.q 2 := hqstrict 1 (by omega) (by omega)
      apply exists_uniform_constrainedPhi_negative_initial_beyond_compact
        (Ω := Ω) s β h hβ hm01 hq1 hq12 hj0 hj ht₀ (hSreg p)
          (fun z hz => hz.1) (hureg p)
      · intro z hz
        have hqle : s.q 1 ≤ |z.2| :=
          (s.q_mono' (p : ℕ) (by omega) 1 (by omega)).trans hz.2.2.1
        have hne : |z.2| ≠ s.q 1 := by
          intro heq
          have hu_eq : z.2 = -s.q 1 := by
            rw [abs_of_neg (hureg p z hz)] at heq
            linarith
          have : 0 < |z.2 - -s.q 1| := (half_pos hρb).trans_le hz.2.1.2
          rw [hu_eq, sub_self, abs_zero] at this
          exact lt_irrefl 0 this
        exact lt_of_le_of_ne hqle (Ne.symm hne)
      · intro z hz
        exact hz.2.2
      · exact hmin
  choose δreg hδreg Hδreg using Hreg
  have hne : (Finset.univ : Finset (Fin (k + 1))).Nonempty := Finset.univ_nonempty
  let δr : ℝ := Finset.univ.inf' hne δreg
  have hδr : 0 < δr := by
    dsimp [δr]
    exact (Finset.lt_inf'_iff hne).mpr (fun p _ => hδreg p)
  let Sterm : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ
      (Icc (-1 : ℝ) 0 ∩ {u : ℝ | ρ0 / 2 ≤ |u|} ∩
        {u : ℝ | ρb / 2 ≤ |u - (-s.q 1)|} ∩
        {u : ℝ | |u| ∈ Icc (s.q (k + 1)) 1})
  have hSterm : IsCompact Sterm := by
    apply isCompact_Icc.prod
    apply ((isCompact_Icc.inter_right
      (isClosed_le continuous_const continuous_abs)).inter_right
      (isClosed_le continuous_const (by fun_prop))).inter_right
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have huterm : ∀ z ∈ Sterm, z.2 < 0 := by
    intro z hz
    have ha : 0 < |z.2| := (half_pos hρ0).trans_le hz.2.1.1.2
    exact lt_of_le_of_ne hz.2.1.1.1.2 (abs_pos.mp ha)
  have hq12_of_lt (hk : 1 ≤ k) : s.q 1 < s.q 2 := hqstrict 1 (by omega) hk
  obtain ⟨δt, hδt, Hterm⟩ : ∃ δ > (0 : ℝ),
      ∀ z ∈ Sterm, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 1) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
    by_cases hk : 1 ≤ k
    · apply exists_uniform_constrainedPhi_negative_initial_terminal_closed
        (Ω := Ω) s β h hβ (by simpa [s.m_zero] using hm01)
          hq1 (hq12_of_lt hk)
      · exact (hq12_of_lt hk).trans_le (s.q_mono' (k + 1) (by omega) 2 (by omega))
      · exact hQ
      · exact ht₀
      · exact hSterm
      · exact fun z hz => hz.1
      · exact fun z hz => ⟨huterm z hz, hz.2.2⟩
    · have hk0 : k = 0 := by omega
      rcases hright with hq12 | hqone
      · apply exists_uniform_constrainedPhi_negative_initial_terminal_padded
          (Ω := Ω) s β h hβ (by simpa [s.m_zero] using hm01) hq1 hq12 hQ ht₀ hSterm
            (fun z hz => hz.1)
        intro z hz
        refine ⟨huterm z hz, ?_⟩
        have hfar : 0 < |z.2 - (-s.q 1)| :=
          (half_pos hρb).trans_le hz.2.1.2
        have hge := hz.2.2.1
        have hstrict : s.q 1 < |z.2| := by
          by_contra H
          have heq : |z.2| = s.q 1 :=
            le_antisymm (le_of_not_gt H) (by simpa [hk0] using hge)
          have hueq : z.2 = -s.q 1 := by
            rw [abs_of_neg (huterm z hz)] at heq
            linarith
          rw [hueq, sub_self, abs_zero] at hfar
          exact lt_irrefl 0 hfar
        exact ⟨by simpa only [hk0, show 0 + 1 = 1 by omega] using hstrict,
          hz.2.2.2⟩
      · refine ⟨1, by norm_num, ?_⟩
        intro z hz
        have habs : |z.2| = 1 :=
          le_antisymm hz.2.2.2 (by simpa [hk0, hqone] using hz.2.2.1)
        have hueq : z.2 = -s.q 1 := by
          rw [abs_of_neg (huterm z hz)] at habs
          linarith
        have hfar : 0 < |z.2 - (-s.q 1)| :=
          (half_pos hρb).trans_le hz.2.1.2
        rw [hueq, sub_self, abs_zero] at hfar
        exact (lt_irrefl 0 hfar).elim
  refine ⟨min δ0 (min δb (min δr δt)),
    lt_min hδ0 (lt_min hδb (lt_min hδr hδt)), ?_⟩
  intro t ht u hu n hn sk hatt
  by_cases hzero : |u| ≤ ρ0
  · have H := Hzero t ht u hzero hn sk hatt
    linarith [min_le_left δ0 (min δb (min δr δt))]
  by_cases hbreak : |u - (-s.q 1)| ≤ ρb
  · have H := Hbreak t ht u hu hbreak hn sk hatt
    linarith [min_le_right δ0 (min δb (min δr δt)),
      min_le_left δb (min δr δt)]
  have hfar0 : ρ0 / 2 ≤ |u| := by linarith [lt_of_not_ge hzero, hρ0]
  have hfarb : ρb / 2 ≤ |u - (-s.q 1)| := by
    linarith [lt_of_not_ge hbreak, hρb]
  obtain ⟨j, hj0, hj, hjleft, hjright⟩ := exists_nat_adjacent_Ioc s.q
    (by simpa only [s.q_zero] using (half_pos hρ0).trans_le hfar0)
    (show |u| ≤ s.q (k + 2) by
      rw [s.q_top]
      exact abs_le.mpr ⟨hu.1, hu.2.trans zero_le_one⟩)
  by_cases hjord : j ≤ k + 1
  · let p : Fin (k + 1) := ⟨j - 1, by omega⟩
    have hpj : (p : ℕ) + 1 = j := by dsimp [p]; omega
    have hz : (t, u) ∈ Sreg p := by
      refine ⟨ht, ⟨⟨⟨hu, hfar0⟩, hfarb⟩, ?_⟩⟩
      rw [hpj, show (p : ℕ) = j - 1 by rfl]
      exact ⟨hjleft.le, hjright⟩
    have H := Hδreg p (t, u) hz hn sk hatt
    have hd : δr ≤ δreg p := Finset.inf'_le _ (Finset.mem_univ p)
    linarith [min_le_right δ0 (min δb (min δr δt)),
      min_le_right δb (min δr δt), min_le_left δr δt]
  · have hjeq : j = k + 2 := by omega
    have hz : (t, u) ∈ Sterm := by
      refine ⟨ht, ⟨⟨⟨hu, hfar0⟩, hfarb⟩, ?_⟩⟩
      rw [hjeq, show k + 2 - 1 = k + 1 by omega] at hjleft
      rw [hjeq, s.q_top] at hjright
      exact ⟨hjleft.le, hjright⟩
    have H := Hterm (t, u) hz hn sk hatt
    linarith [min_le_right δ0 (min δb (min δr δt)),
      min_le_right δb (min δr δt), min_le_right δr δt]

/-- Exact concrete negative-away input at every physical level.  The only
cross-sign reuse is the forced-even `r=1,q₁=0` case, where the supplied
positive-away estimate reflects without loss. -/
theorem exists_uniform_constrainedPhi_negative_away_concrete_at_level
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ η : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2)
    (hη : 0 < η)
    (hpos : ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  have hmmono : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hq12_of_zero (hq1z : s.q 1 = 0) : s.q 1 < s.q 2 := by
    by_cases hk : 1 ≤ k
    · exact hqstrict 1 (by omega) hk
    · have hk0 : k = 0 := by omega
      rw [hq1z]
      have : s.q 2 = 1 := by simpa only [hk0] using s.q_top
      linarith
  by_cases hrone : r = 1
  · subst r
    simp only [show k + 2 - 1 = k + 1 by omega] at hpos ⊢
    rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hq1z | hq1p
    · have hq1z' : s.q 1 = 0 := hq1z.symm
      exact exists_uniform_constrainedPhi_negative_initial_zero_of_positive_away
        (Ω := Ω) s β h hβ (hmass 0 (by omega)) hq1z'
          (hq12_of_zero hq1z') hmin hpos
    · obtain ⟨c, hc, Hc⟩ := exists_uniform_constrainedPhi_negative_all_initial_q1_pos
        (Ω := Ω) s β h ε hβ hmass hqstrict hq1p
          (section4TVarianceQ_zero_eq_overlap_of_min_all_levels
            s β h le_rfl (by omega) hβ (hmass 0 (by omega))
              (Or.inl (by simpa only [s.q_zero] using hq1p))
              (by
                by_cases hk : 1 ≤ k
                · exact Or.inl (hqstrict 1 (by omega) hk)
                · have hk0 : k = 0 := by omega
                  have htop : s.q 2 = 1 := by simpa only [hk0] using s.q_top
                  rcases (s.q_mono' 2 (by omega) 1 (by omega)).lt_or_eq with H | H
                  · exact Or.inl H
                  · exact Or.inr (H.trans htop)) hmin)
          hmin hnear ht₀nonneg ht₀ hsmall
      refine ⟨c, hc, ?_⟩
      intro t ht u hu haway n hn sk hatt
      exact Hc t ht u hu hn sk hatt
  · have hr2 : 2 ≤ r := by omega
    have hqphys : s.q (r - 1) < s.q r := by
      simpa only [Nat.sub_add_cancel hr0] using
        hqstrict (r - 1) (by omega) (by omega)
    have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := by
      by_cases hrk : r ≤ k
      · exact Or.inl (hqstrict r hr0 hrk)
      · have hre : r = k + 1 := by omega
        have htop : s.q (r + 1) = 1 := by
          simpa only [hre, show k + 1 + 1 = k + 2 by omega] using s.q_top
        rcases (s.q_mono' (r + 1) (by omega) r (by omega)).lt_or_eq with H | H
        · exact Or.inl H
        · exact Or.inr (H.trans htop)
    have hQ := section4TVarianceQ_zero_eq_overlap_of_min_all_levels
      s β h (show 1 ≤ r by omega) hr hβ
        (by simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
          hmass (r - 1) (by omega))
        (Or.inl hqphys) hright hmin
    rcases (s.q_nonneg (p := 1) (by omega)).eq_or_lt with hq1z | hq1p
    · have hq1z' : s.q 1 = 0 := hq1z.symm
      by_cases hrthree : 3 ≤ r
      · obtain ⟨c, hc, Hc⟩ :=
          exists_uniform_constrainedPhi_negative_all_of_q1_zero_three_le
            (Ω := Ω) s β h hβ hrthree hr hmass hqstrict hq1z' hQ hmin
              ht₀nonneg ht₀
        refine ⟨c, hc, ?_⟩
        intro t ht u hu haway n hn sk hatt
        exact Hc t ht u hu hn sk hatt
      · have hre : r = 2 := by omega
        subst r
        have hq2 : s.q 1 < s.q 2 := hq12_of_zero hq1z'
        obtain ⟨ρ, hρ, δ, hδ, Htube⟩ :=
          exists_uniform_constrainedPhi_physical_left_two_sided
            (Ω := Ω) s β h ε (r := 2) (by omega) (by omega) hβ hmass
              hq2 hright ht₀ hmin hnear hsmall hfar
        have hsign : ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
            ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
            |u| ≤ ρ → ∀ {n : ℕ}, 0 < n →
            ∀ sk : SKDisorder (Ω := Ω) n β h,
            (∃ σ τ : Config n, overlap n σ τ = u) →
            constrainedPhi n s β h sk.U k t u ≤
              2 * guerraPsi s β h t - δ := by
          refine ⟨ρ, hρ, δ, hδ, ?_⟩
          intro t ht u hu hzero n hn sk hatt
          have hu0 : |u - s.q (2 - 1)| ≤ ρ := by
            simpa only [show 2 - 1 = 1 by omega, hq1z', sub_zero] using hzero
          simpa only [show k + 2 - 2 = k by omega] using
            Htube t ht u hu0 hn sk hatt
        obtain ⟨c, hc, Hc⟩ :=
          exists_uniform_constrainedPhi_negative_all_of_sign_crossing
            (Ω := Ω) s β h hβ (r := 2) (by omega) (by omega)
              hmass hqstrict hQ ht₀nonneg ht₀ hsign
        refine ⟨c, hc, ?_⟩
        intro t ht u hu haway n hn sk hatt
        simpa only [show k + 2 - 2 = k by omega] using Hc t ht u hu hn sk hatt
    · obtain ⟨c, hc, Hc⟩ := exists_uniform_constrainedPhi_negative_all_of_q1_pos
        (Ω := Ω) s β h hβ hr2 hr hmass hqstrict hq1p hQ hmin
          ht₀nonneg ht₀
      refine ⟨c, hc, ?_⟩
      intro t ht u hu haway n hn sk hatt
      exact Hc t ht u hu hn sk hatt

/-- Once the concrete positive-away estimate is supplied, all negative cases
are now discharged and the exact signed hlevel conclusion follows. -/
theorem exists_uniform_constrainedPhi_signed_away_of_positive_concrete
    {k : ℕ} (s : RSBScheme k) (β h ε : ℝ) {r : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hnear : parisiFunctional s β h ≤ parisiValue β h + ε)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ η : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hsmall : section5LocalLeftConstant β 535 * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀)
    (hfar : section5FarLeftBound β * Real.sqrt ε ≤
      (1 - t₀) * (β ^ 2 / 2) *
        ((1 - t₀) / section5LocalLeftConstant β 535) ^ 2)
    (hη : 0 < η)
    (hpos : ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c) :
    ∃ c > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 1, η ≤ |u - s.q r| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - c := by
  have hneg := exists_uniform_constrainedPhi_negative_away_concrete_at_level
    (Ω := Ω) s β h ε hr0 hr hβ hmass hqstrict hnear hmin
      ht₀nonneg ht₀ hsmall hfar hη hpos
  exact exists_uniform_constrainedPhi_signed_away_at_level
    (Ω := Ω) s β h hr0 hr hpos hneg

end SpinGlass.Targets
