module

public import Targets.Section5InterleavedOffDiagonalBound
public import Targets.Section5CompactTube
public import Targets.Section5InterleavedTimeZero
public import Targets.Section5InterleavedStrict
public import Targets.Section5InterleavedScalarContinuity
public import Targets.Section5NegativeCompact
public import Targets.Section5NegativeTerminalCompact
public import Targets.Section5OutsideIntervals
public import Targets.Section5ZeroInitialReflection

@[expose] public section

/-!
# Crossing the overlap-sign boundary

For an outside trial interval whose left endpoint is zero, keep the trial
overlap fixed at `v = 0` while the constrained overlap crosses zero.  The
off-diagonal interpolation loses only the explicit quadratic mismatch.  The
strict scalar endpoint at `v = 0` therefore persists on a whole two-sided
tube, uniformly in physical time.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A trial interval starting at zero and lying strictly to the left of the
physical interval gives a uniform finite-volume gap on both sides of `u=0`.
At positive time the gap is Talagrand's strict interleaving obstruction; at
time zero it is the stationary nonzero-lambda gain. -/
theorem exists_uniform_constrainedPhi_sign_crossing_left_outside
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hjr : j < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hqzero : s.q (j - 1) = 0) (hqpos : 0 < s.q j)
    (hqphys : s.q (r - 1) < s.q r)
    (hright : s.q r < s.q (r + 1) ∨ s.q r = 1)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      |u| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  let f : ℝ → (ℝ × ℝ) → ℝ := fun ℓ z =>
    section5InterleavedLambdaDeficit s β h r j z.1 0 ℓ + ℓ * z.2 -
      z.1 * (β ^ 2 / 2) * z.2 ^ 2
  have hf : ∀ ℓ, Continuous (f ℓ) := by
    intro ℓ
    have hchart := continuous_section5InterleavedScalarChart s β r hj false
    have hmap : Continuous (fun z : ℝ × ℝ =>
        (((z.1, (0 : ℝ)), (ℓ, (h, h))) : (ℝ × ℝ) × ℝ × (ℝ × ℝ))) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_const
    have hVchart : Continuous (fun z : ℝ × ℝ =>
        section5InterleavedScalarChart s β r j false (z.1, 0) ℓ (h, h)) :=
      hchart.comp hmap
    have hV : Continuous (fun z : ℝ × ℝ =>
        section5InterleavedScalarV s β h r j z.1 0 ℓ) := by
      apply hVchart.congr
      intro z
      rw [section5InterleavedScalarV_eq_chart]
      simp only [lt_self_iff_false, decide_false]
    unfold f section5InterleavedLambdaDeficit
    exact ((((continuous_const.sub hV).add continuous_const).add
      (continuous_const.mul continuous_snd)).sub
      ((continuous_fst.mul continuous_const).mul (continuous_snd.pow 2)))
  have hmass : s.m (r - 1) < s.m r := by
    have hfin : (⟨r - 1, by omega⟩ : Fin (k + 2)) < ⟨r, by omega⟩ := by
      apply Fin.mk_lt_mk.mpr
      omega
    exact hm hfin
  have hqrpos : 0 < s.q r := by
    have hmono : s.q j ≤ s.q r := s.q_mono' r (by omega) j hjr.le
    exact hqpos.trans_le hmono
  have htrial0 : |(0 : ℝ)| ∈ Icc (s.q (j - 1)) (s.q j) := by
    simp only [abs_zero, hqzero, mem_Icc, le_refl, true_and]
    exact hqpos.le
  have hpos : ∀ t ∈ Icc (0 : ℝ) t₀, ∃ ℓ, 0 < f ℓ (t, 0) := by
    intro t ht
    by_cases htzero : t = 0
    · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_of_min
        s β h hr0 hr hj hβ hmass (Or.inl hqphys) hright hmin 0
      refine ⟨ℓ, ?_⟩
      dsimp only [f, section5InterleavedLambdaDeficit]
      rw [htzero]
      simp only [mul_zero, add_zero, zero_mul, sub_zero]
      have hsq : 0 < ((0 : ℝ) - s.q r) ^ 2 / 2 := by
        exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hqrpos.ne)) (by norm_num)
      linarith
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      have htone : t < 1 := ht.2.trans_lt ht₀
      have H := section5InterleavedScalarV_zero_lt_left_outside
        s β h (r := r) (j := j) ⟨htpos.le, htone.le⟩ hr hj0 hjr htrial0 hm
        (by simpa only [abs_zero, sub_zero] using
          mul_pos htpos (mul_pos (sq_pos_of_ne_zero hβ) hqpos))
        (mul_pos (sub_pos.mpr htone)
          (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hqphys)))
      refine ⟨0, ?_⟩
      simpa [f, section5InterleavedLambdaDeficit] using (sub_pos.mpr H)
  obtain ⟨ρ, hρ, δ, hδ, Htube⟩ :=
    exists_uniform_positive_near_compact_slice (S := Icc (0 : ℝ) t₀)
      isCompact_Icc f hf 0 hpos
  refine ⟨min 1 ρ, lt_min (by norm_num) hρ, δ, hδ, ?_⟩
  intro t ht u hu htu n hn sk hatt
  have htu' : |u - 0| ≤ ρ := by
    simpa only [sub_zero] using htu.trans (min_le_right 1 ρ)
  obtain ⟨ℓ, hℓ⟩ := Htube t ht u htu'
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.le⟩
  have Hmajor := constrainedPhi_le_interleavedOffDiagonalMajorant
    hn s β h sk hr0 hr hj0 hj (t := t) (u := u) (v := 0) (ℓ := ℓ)
      ht1 htrial0 hatt
  dsimp only [f, section5InterleavedLambdaDeficit] at hℓ
  simp only [sub_zero] at Hmajor
  unfold guerraPsi
  linarith

/-- Once a two-sided zero-overlap tube is available, the ordinary negative
trial intervals and redundant terminal padding give one gap on the entire
closed negative half-line.  Thus the only remaining input in exceptional
index configurations is the physical `v = 0` crossing itself. -/
theorem exists_uniform_constrainedPhi_negative_all_of_sign_crossing
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hsign : ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-1 : ℝ) 1,
      |u| ≤ ρ → ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  obtain ⟨ρ, hρ, δ₀, hδ₀, Hzero⟩ := hsign
  have hm1 : 0 < s.m 1 := by
    simpa only [s.m_zero, zero_add] using hmass 0 (by omega)
  have hq12 : s.q 1 < s.q 2 := hqstrict 1 (by omega) (by omega)
  let Sreg : Fin (k + 1) → Set (ℝ × ℝ) := fun p =>
    Icc (0 : ℝ) t₀ ×ˢ
      (Icc (-1 : ℝ) 0 ∩ {u : ℝ | ρ / 2 ≤ |u|} ∩
        {u : ℝ | |u| ∈ Icc (s.q ((p : ℕ) + 1 - 1)) (s.q ((p : ℕ) + 1))})
  have hSreg (p : Fin (k + 1)) : IsCompact (Sreg p) := by
    apply isCompact_Icc.prod
    apply (isCompact_Icc.inter_right
      (isClosed_le continuous_const (continuous_abs))).inter_right
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have htreg (p : Fin (k + 1)) : ∀ z ∈ Sreg p, z.1 ∈ Icc (0 : ℝ) t₀ :=
    fun z hz => hz.1
  have hureg (p : Fin (k + 1)) : ∀ z ∈ Sreg p, z.2 < 0 := by
    intro z hz
    have habs : 0 < |z.2| := (half_pos hρ).trans_le hz.2.1.2
    exact lt_of_le_of_ne hz.2.1.1.2 (abs_pos.mp habs)
  have htrialreg (p : Fin (k + 1)) : ∀ z ∈ Sreg p,
      |z.2| ∈ Icc (s.q (((p : ℕ) + 1) - 1)) (s.q ((p : ℕ) + 1)) :=
    fun z hz => hz.2.2
  have Hreg (p : Fin (k + 1)) : ∃ δ > (0 : ℝ),
      ∀ z ∈ Sreg p, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ := by
    exact exists_uniform_constrainedPhi_negative_trial (Ω := Ω)
      s β h hβ hr0 hr (hj0 := by omega) (hj := by omega) hm1 hq12 hQ ht₀
        (hSreg p) (htreg p) (hureg p) (htrialreg p)
  choose δreg hδreg Hδreg using Hreg
  have hne : (Finset.univ : Finset (Fin (k + 1))).Nonempty := Finset.univ_nonempty
  let δr : ℝ := Finset.univ.inf' hne δreg
  have hδr : 0 < δr := by
    dsimp [δr]
    exact (Finset.lt_inf'_iff hne).mpr (fun p _ => hδreg p)
  let Sterm : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) t₀ ×ˢ
      (Icc (-1 : ℝ) 0 ∩ {u : ℝ | ρ / 2 ≤ |u|} ∩
        {u : ℝ | |u| ∈ Icc (s.q (k + 1)) 1})
  have hSterm : IsCompact Sterm := by
    apply isCompact_Icc.prod
    apply (isCompact_Icc.inter_right
      (isClosed_le continuous_const (continuous_abs))).inter_right
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have huterm : ∀ z ∈ Sterm, z.2 < 0 := by
    intro z hz
    have habs : 0 < |z.2| := (half_pos hρ).trans_le hz.2.1.2
    exact lt_of_le_of_ne hz.2.1.1.2 (abs_pos.mp habs)
  obtain ⟨δt, hδt, Hterm⟩ :=
    exists_uniform_constrainedPhi_negative_terminal_padded (Ω := Ω)
      s β h hβ hr0 hr hm1 hq12 hQ ht₀ hSterm
        (fun z hz => hz.1) (fun z hz => ⟨huterm z hz, hz.2.2⟩)
  refine ⟨min δ₀ (min δr δt), lt_min hδ₀ (lt_min hδr hδt), ?_⟩
  intro t ht u hu n hn sk hatt
  by_cases hnear : |u| ≤ ρ
  · have H := Hzero t ht u ⟨hu.1, hu.2.trans (by norm_num)⟩ hnear hn sk hatt
    exact H.trans (by linarith [min_le_left δ₀ (min δr δt)])
  · have hfar : ρ / 2 ≤ |u| := by linarith [lt_of_not_ge hnear, hρ]
    obtain ⟨j, hj0, hj, hjleft, hjright⟩ := exists_nat_adjacent_Ioc s.q
      (by simpa only [s.q_zero] using (half_pos hρ).trans_le hfar)
      (show |u| ≤ s.q (k + 2) by
        rw [s.q_top, abs_of_nonpos hu.2]
        linarith [hu.1])
    by_cases hjord : j ≤ k + 1
    · let p : Fin (k + 1) := ⟨j - 1, by omega⟩
      have hpj : (p : ℕ) + 1 = j := by dsimp [p]; omega
      have hz : (t, u) ∈ Sreg p := by
        refine ⟨ht, ⟨⟨hu, hfar⟩, ?_⟩⟩
        rw [hpj]
        exact ⟨hjleft.le, hjright⟩
      have H := Hδreg p (t, u) hz hn sk hatt
      have hd : δr ≤ δreg p := Finset.inf'_le _ (Finset.mem_univ p)
      exact H.trans (by linarith [min_le_right δ₀ (min δr δt), min_le_left δr δt])
    · have hjeq : j = k + 2 := by omega
      have hz : (t, u) ∈ Sterm := by
        refine ⟨ht, ⟨⟨hu, hfar⟩, ?_⟩⟩
        rw [hjeq, show k + 2 - 1 = k + 1 by omega] at hjleft
        rw [hjeq, s.q_top] at hjright
        change s.q (k + 1) ≤ |u| ∧ |u| ≤ 1
        exact ⟨hjleft.le, hjright⟩
      have H := Hterm (t, u) hz hn sk hatt
      exact H.trans (by linarith [min_le_right δ₀ (min δr δt), min_le_right δr δt])

/-- With positive first overlap, the first trial interval supplies the zero
crossing at every physical level `r ≥ 2`; hence the entire negative half is
uniformly strict without any further hypothesis. -/
theorem exists_uniform_constrainedPhi_negative_all_of_q1_pos
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 2 ≤ r) (hr : r ≤ k + 1)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hq1 : 0 < s.q 1)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hm : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hqphys : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := by
    by_cases hrk : r ≤ k
    · exact Or.inl (hqstrict r (by omega) hrk)
    · have hre : r = k + 1 := by omega
      have htop : s.q (r + 1) = 1 := by
        simpa only [hre, show k + 1 + 1 = k + 2 by omega] using s.q_top
      rcases (s.q_mono' (r + 1) (by omega) r (by omega)).lt_or_eq with H | H
      · exact Or.inl H
      · exact Or.inr (H.trans htop)
  have hsign := exists_uniform_constrainedPhi_sign_crossing_left_outside
    (Ω := Ω) s β h hβ (r := r) (j := 1) (by omega) hr (by omega) (by omega)
      (by omega) hm (by simp only [Nat.sub_self, s.q_zero]) hq1 hqphys hright hmin
      ht₀nonneg ht₀
  exact exists_uniform_constrainedPhi_negative_all_of_sign_crossing
    (Ω := Ω) s β h hβ hr0 hr hmass hqstrict hQ ht₀nonneg ht₀ hsign

/-- If `q₁ = 0` but `r ≥ 3`, the second trial interval starts at zero and
plays the same role.  The sole remaining zero-crossing configuration for
physical levels at least two is therefore `r = 2`, `q₁ = 0`. -/
theorem exists_uniform_constrainedPhi_negative_all_of_q1_zero_three_le
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r : ℕ}
    (hβ : β ≠ 0) (hr0 : 3 ≤ r) (hr : r ≤ k + 1)
    (hmass : ∀ p, p ≤ k → s.m p < s.m (p + 1))
    (hqstrict : ∀ p, 1 ≤ p → p ≤ k → s.q p < s.q (p + 1))
    (hq1 : s.q 1 = 0)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ : ℝ} (ht₀nonneg : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 2 - r) t u ≤
        2 * guerraPsi s β h t - δ := by
  have hm : StrictMono (fun p : Fin (k + 2) => s.m p) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro p
    exact hmass p (by omega)
  have hq2 : 0 < s.q 2 := by
    have H := hqstrict 1 (by omega) (by omega)
    simpa only [hq1] using H
  have hqphys : s.q (r - 1) < s.q r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      hqstrict (r - 1) (by omega) (by omega)
  have hright : s.q r < s.q (r + 1) ∨ s.q r = 1 := by
    by_cases hrk : r ≤ k
    · exact Or.inl (hqstrict r (by omega) hrk)
    · have hre : r = k + 1 := by omega
      have htop : s.q (r + 1) = 1 := by
        simpa only [hre, show k + 1 + 1 = k + 2 by omega] using s.q_top
      rcases (s.q_mono' (r + 1) (by omega) r (by omega)).lt_or_eq with H | H
      · exact Or.inl H
      · exact Or.inr (H.trans htop)
  have hsign := exists_uniform_constrainedPhi_sign_crossing_left_outside
    (Ω := Ω) s β h hβ (r := r) (j := 2) (by omega) hr (by omega) (by omega)
      (by omega) hm (by simpa only [Nat.reduceSubDiff] using hq1) hq2 hqphys hright hmin
      ht₀nonneg ht₀
  exact exists_uniform_constrainedPhi_negative_all_of_sign_crossing
    (Ω := Ω) s β h hβ (by omega) hr hmass hqstrict hQ ht₀nonneg ht₀ hsign

/-- At the first physical level with `q₁ = 0`, original minimality forces
zero field and the constrained pressure is even.  Therefore any already
assembled positive away estimate transfers verbatim to the negative side;
the deleted `η`-neighborhood excludes the sign boundary. -/
theorem exists_uniform_constrainedPhi_negative_initial_zero_of_positive_away
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (hβ : β ≠ 0) (hm : s.m 0 < s.m 1)
    (hq1 : s.q 1 = 0) (hq12 : s.q 1 < s.q 2)
    (hmin : ∀ s' : RSBScheme k,
      parisiFunctional s β h ≤ parisiFunctional s' β h)
    {t₀ η : ℝ}
    (hpos : ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (0 : ℝ) 1, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 0, η ≤ |u - s.q 1| →
      ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = u) →
      constrainedPhi n s β h sk.U (k + 1) t u ≤
        2 * guerraPsi s β h t - δ := by
  obtain ⟨δ, hδ, Hpos⟩ := hpos
  refine ⟨δ, hδ, ?_⟩
  intro t ht u hu haway n hn sk hatt
  have hnegmem : -u ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have haway' : η ≤ |-u - s.q 1| := by
    simpa only [hq1, sub_zero, abs_neg] using haway
  have hatt' : ∃ σ τ : Config n, overlap n σ τ = -u :=
    attainableOverlap_neg hatt
  have H := Hpos t ht (-u) hnegmem haway' hn sk hatt'
  rw [constrainedPhi_initial_zero_reflection_of_min s β h sk hβ hq1 hm hq12 hmin]
  simpa only [neg_neg] using H

end SpinGlass.Targets
