module

public import Lemmas.GuerraTalagrand.Flatness.Core
public import Lemmas.GuerraTalagrand.Flatness.Cases

@[expose] public section
/-!
# GT flatness

This public module collects the shared GT-flatness theory and its
case-specific consequences. Case modules use the canonical `Core` and
`Cases` hierarchy.
-/

namespace SpinGlass.AT

open Set

/-- Uniform strict improvement on the large-negative branch. -/
private lemma gtFunctional_uniform_gap_large_negative {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ κ > 0, ∀ {β h q s v : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (-1 : ℝ) (-q) →
      ∃ lam ∈ Icc (-1 : ℝ) 1,
        gtFunctional β h q s lam v ≤
          2 * rsPathValue β h q s - κ := by
  by_cases hK : K.Nonempty
  · obtain ⟨a, ha, hsep⟩ :=
      flatness_deriv_gtFunctional_zero_negative_global_separation data
    let d : ℝ := 2 * data.qmin * min a 1
    have hd : 0 < d := by
      exact mul_pos (mul_pos (by norm_num) data.qmin_pos)
        (lt_min ha zero_lt_one)
    let τ : ℝ := min 1 (d / 5)
    have hτ : 0 < τ := lt_min zero_lt_one (div_pos hd (by norm_num))
    have hτone : τ ≤ 1 := min_le_left _ _
    have hτd : τ ≤ d / 5 := min_le_right _ _
    have hτmem : τ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hτone⟩
    have hnegτmem : -τ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩

    let D : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
      K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    let qfun : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ :=
      fun x => rsQ x.1.1 x.1.2
    let vfun : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ :=
      fun x => -qfun x - x.2.2 * (1 - qfun x)
    have hDcompact : IsCompact D := by
      exact data.isCompact.prod (isCompact_Icc.prod isCompact_Icc)
    have hDnonempty : D.Nonempty := by
      obtain ⟨p, hp⟩ := hK
      exact ⟨(p, (0, 0)), hp, ⟨le_rfl, zero_le_one⟩,
        ⟨le_rfl, zero_le_one⟩⟩
    have hqcont : ContinuousOn qfun D := by
      simpa [qfun, Function.comp_def] using
        (continuousOn_rsParameters_of_subset_strictATRegion
          data.subset_strictATRegion).1.comp
          (continuousOn_fst :
            ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1) D)
          (by intro x hx; exact hx.1)
    have hvcont : ContinuousOn vfun D := by
      exact hqcont.neg.sub
        (continuousOn_snd.snd.mul (continuousOn_const.sub hqcont))
    have hqmem (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : x ∈ D) :
        qfun x ∈ Icc (0 : ℝ) 1 := by
      exact rsQ_mem_Icc x.1.1 x.1.2
    have hqpos (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : x ∈ D) :
        0 < qfun x := by
      exact rsQ_pos (data.β_pos x.1 hx.1) (data.h_pos x.1 hx.1)
    have hqlt (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : x ∈ D) :
        qfun x < 1 := by
      exact rsQ_lt_one (data.β_pos x.1 hx.1) (data.h_pos x.1 hx.1)
    have hvmem (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : x ∈ D) :
        vfun x ∈ Icc (-1 : ℝ) 1 := by
      have hq := hqmem x hx
      have ht := hx.2.2
      have hprod0 : 0 ≤ x.2.2 * (1 - qfun x) :=
        mul_nonneg ht.1 (sub_nonneg.mpr hq.2)
      have hprod1 : x.2.2 * (1 - qfun x) ≤ 1 - qfun x :=
        by simpa using mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hq.2)
      dsimp [vfun]
      constructor
      · linarith
      · linarith [hq.1]

    have hFcont (lam : ℝ) (hlam : lam ∈ Icc (-1 : ℝ) 1) :
        ContinuousOn (fun x =>
          gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 lam (vfun x)) D := by
      let B : ((ℝ × ℝ) × (ℝ × ℝ)) →
          (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) :=
        fun x => (x.1, (x.2.1, (vfun x, lam)))
      have hBcont : ContinuousOn B D := by
        exact
          (continuousOn_fst :
            ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1) D).prodMk
          (continuousOn_snd.fst.prodMk (hvcont.prodMk continuousOn_const))
      have hBmaps : MapsTo B D
          (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ
            (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))) := by
        intro x hx
        exact ⟨hx.1, hx.2.1, hvmem x hx, hlam⟩
      simpa [B, qfun, Function.comp_def] using
        (continuousOn_gtFunctional_uniformATData data).comp hBcont hBmaps

    let E : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun x =>
      gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 0 (qfun x)
    have hEcont : ContinuousOn E D := by
      let B : ((ℝ × ℝ) × (ℝ × ℝ)) →
          (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) :=
        fun x => (x.1, (x.2.1, (qfun x, 0)))
      have hBcont : ContinuousOn B D := by
        exact
          (continuousOn_fst :
            ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1) D).prodMk
          (continuousOn_snd.fst.prodMk (hqcont.prodMk continuousOn_const))
      have hBmaps : MapsTo B D
          (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ
            (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))) := by
        intro x hx
        have hq := hqmem x hx
        refine ⟨hx.1, hx.2.1, ?_, by norm_num⟩
        change -1 ≤ qfun x ∧ qfun x ≤ 1
        exact ⟨by linarith [hq.1], hq.2⟩
      simpa [B, E, qfun, Function.comp_def] using
        (continuousOn_gtFunctional_uniformATData data).comp hBcont hBmaps

    let M : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun x =>
      min (gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 0 (vfun x))
        (min (gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 (-τ) (vfun x))
          (gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 τ (vfun x)))
    have hMcont : ContinuousOn M D := by
      exact (hFcont 0 (by norm_num)).inf
        ((hFcont (-τ) hnegτmem).inf (hFcont τ hτmem))
    let G : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun x => E x - M x
    have hGcont : ContinuousOn G D := hEcont.sub hMcont

    have hstrict_of_deriv {β h q s v e : ℝ}
        (hzero : gtFunctional β h q s 0 v = 2 * rsPathValue β h q s)
        (he : e = deriv (fun lam => gtFunctional β h q s lam v) 0)
        (hgap : d ≤ |e|) :
        min (gtFunctional β h q s 0 v)
          (min (gtFunctional β h q s (-τ) v)
            (gtFunctional β h q s τ v)) <
          2 * rsPathValue β h q s := by
      have hquad : (5 / 4 : ℝ) * τ ^ 2 < d * τ := by
        have hle : (5 / 4 : ℝ) * τ ^ 2 ≤ d * τ / 4 := by
          nlinarith [hτd, hτ]
        nlinarith [hd, hτ]
      by_cases he0 : 0 ≤ e
      · have ht := flatness_gtFunctional_taylor_upper β h q s v (-τ)
        rw [← he, hzero] at ht
        rw [abs_of_nonneg he0] at hgap
        have hlt : gtFunctional β h q s (-τ) v <
            2 * rsPathValue β h q s := by nlinarith
        exact (min_le_right _ _).trans_lt (min_le_left _ _ |>.trans_lt hlt)
      · have hent : e < 0 := lt_of_not_ge he0
        have ht := flatness_gtFunctional_taylor_upper β h q s v τ
        rw [← he, hzero] at ht
        rw [abs_of_neg hent] at hgap
        have hlt : gtFunctional β h q s τ v <
            2 * rsPathValue β h q s := by nlinarith
        exact (min_le_right _ _).trans_lt (min_le_right _ _ |>.trans_lt hlt)

    have hGpos (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : x ∈ D) : 0 < G x := by
      have hp : x.1 ∈ K := hx.1
      have hs : x.2.1 ∈ Icc (0 : ℝ) 1 := hx.2.1
      have ht : x.2.2 ∈ Icc (0 : ℝ) 1 := hx.2.2
      have hqIoo : qfun x ∈ Ioo (0 : ℝ) 1 := ⟨hqpos x hx, hqlt x hx⟩
      have hv : vfun x ∈ Icc (-1 : ℝ) (-qfun x) := by
        have hfull := hvmem x hx
        have hprod0 : 0 ≤ x.2.2 * (1 - qfun x) :=
          mul_nonneg ht.1 (by linarith [hqIoo.2])
        exact ⟨hfull.1, by dsimp [vfun]; linarith⟩
      have hE : E x = 2 * rsPathValue x.1.1 x.1.2 (qfun x) x.2.1 :=
        flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
          x.1.1 x.1.2 (qfun x) x.2.1 (qfun x) hqIoo hs
            ⟨hqIoo.1.le, le_rfl⟩
      rw [show G x = E x - M x by rfl, hE]
      apply sub_pos.mpr
      by_cases hs0 : x.2.1 = 0
      · have hzero :
            gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 0 (vfun x) =
              2 * rsPathValue x.1.1 x.1.2 (qfun x) x.2.1 := by
          rw [hs0]
          exact flatness_gtFunctional_s_zero_lam_zero _ _ _ _
        let e : ℝ := qfun x - vfun x
        have he : e = deriv (fun lam =>
            gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 lam (vfun x)) 0 := by
          rw [hs0]
          exact (flatness_deriv_gtFunctional_s_zero_lam_zero_rsQ _ _ _).symm
        have hqmin : data.qmin ≤ qfun x := data.q_lower x.1 hp
        have hmin : min a 1 ≤ 1 := min_le_right _ _
        have hepos : 0 ≤ e := by
          dsimp [e]
          linarith [hv.2, hqIoo.1]
        have hgap : d ≤ |e| := by
          rw [abs_of_nonneg hepos]
          dsimp [d, e]
          have htwoq : 0 ≤ (2 : ℝ) * data.qmin :=
            mul_nonneg (by norm_num) data.qmin_pos.le
          have hmul :
              (2 * data.qmin) * min a 1 ≤ (2 * data.qmin) * 1 :=
            mul_le_mul_of_nonneg_left hmin htwoq
          nlinarith [hv.2]
        simpa [M] using hstrict_of_deriv hzero he hgap
      · by_cases ht0 : x.2.2 = 0
        · have hvq : vfun x = -qfun x := by simp [vfun, ht0]
          have hzero :
              gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 0 (vfun x) =
                2 * rsPathValue x.1.1 x.1.2 (qfun x) x.2.1 := by
            rw [hvq]
            exact flatness_gtFunctional_zero_eq_two_rsPathValue_small_negative
              x.1.1 x.1.2 (qfun x) x.2.1 (-qfun x) hqIoo hs
                ⟨le_rfl, by linarith [hqIoo.1]⟩
          let e : ℝ := deriv (fun lam =>
            gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 lam (vfun x)) 0
          have he : e = deriv (fun lam =>
              gtFunctional x.1.1 x.1.2 (qfun x) x.2.1 lam (vfun x)) 0 := rfl
          have hsep' : a * |vfun x - qfun x| ≤ |e| :=
            hsep hp rfl hs (by rw [hvq]; exact ⟨le_rfl, by linarith [hqIoo.1]⟩)
          have hqmin : data.qmin ≤ qfun x := data.q_lower x.1 hp
          have hmina : min a 1 ≤ a := min_le_left _ _
          have habs : |vfun x - qfun x| = 2 * qfun x := by
            rw [hvq, abs_of_nonpos (by linarith [hqIoo.1])]
            ring
          rw [habs] at hsep'
          have hgap : d ≤ |e| := by
            calc
              d ≤ 2 * data.qmin * a := by
                dsimp [d]
                exact mul_le_mul_of_nonneg_left hmina
                  (mul_nonneg (by norm_num) data.qmin_pos.le)
              _ ≤ 2 * qfun x * a := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hqmin (by norm_num)) ha.le
              _ ≤ |e| := by nlinarith [hsep']
          simpa [M] using hstrict_of_deriv hzero he hgap
        · have hspos : 0 < x.2.1 := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          have htpos : 0 < x.2.2 := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have hvq : vfun x < -qfun x := by
            have hq1 := hqlt x hx
            dsimp [vfun]
            nlinarith
          have hlt := flatness_gtFunctional_zero_lt_two_rsPathValue_large_negative
            (data.β_pos x.1 hp) (data.h_pos x.1 hp) rfl hs hspos hv hvq
          exact lt_of_le_of_lt (min_le_left _ _) hlt

    obtain ⟨x₀, hx₀, hmin⟩ := hDcompact.exists_isMinOn hDnonempty hGcont
    refine ⟨G x₀, hGpos x₀ hx₀, ?_⟩
    intro β h q s v hp hq hs hv
    subst q
    have hβ : 0 < β := data.β_pos (β, h) hp
    have hh : 0 < h := data.h_pos (β, h) hp
    have hq0 : 0 < rsQ β h := rsQ_pos hβ hh
    have hq1 : rsQ β h < 1 := rsQ_lt_one hβ hh
    let t : ℝ := (-rsQ β h - v) / (1 - rsQ β h)
    have hden : 0 < 1 - rsQ β h := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hv.2]) hden.le
    have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith [hv.1])
    let x : (ℝ × ℝ) × (ℝ × ℝ) := ((β, h), (s, t))
    have hx : x ∈ D := ⟨hp, hs, ht0, ht1⟩
    have hvfun : vfun x = v := by
      dsimp [vfun, qfun, x, t]
      field_simp [ne_of_gt hden]
      ring
    have hbase : E x = 2 * rsPathValue β h (rsQ β h) s := by
      exact flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
        β h (rsQ β h) s (rsQ β h) ⟨hq0, hq1⟩ hs ⟨hq0.le, le_rfl⟩
    have hgap : G x₀ ≤ G x := isMinOn_iff.mp hmin x hx
    have hchoice : ∃ lam ∈ Icc (-1 : ℝ) 1,
        M x = gtFunctional β h (rsQ β h) s lam v := by
      rw [show M x = min (gtFunctional β h (rsQ β h) s 0 v)
          (min (gtFunctional β h (rsQ β h) s (-τ) v)
            (gtFunctional β h (rsQ β h) s τ v)) by
        simp [M, x, qfun, hvfun]]
      by_cases h0 : gtFunctional β h (rsQ β h) s 0 v ≤
          min (gtFunctional β h (rsQ β h) s (-τ) v)
            (gtFunctional β h (rsQ β h) s τ v)
      · exact ⟨0, by norm_num, min_eq_left h0⟩
      · rw [min_eq_right (le_of_not_ge h0)]
        by_cases hn : gtFunctional β h (rsQ β h) s (-τ) v ≤
            gtFunctional β h (rsQ β h) s τ v
        · exact ⟨-τ, hnegτmem, min_eq_left hn⟩
        · exact ⟨τ, hτmem, min_eq_right (le_of_not_ge hn)⟩
    obtain ⟨lam, hlam, hM⟩ := hchoice
    refine ⟨lam, hlam, ?_⟩
    rw [show G x = E x - M x by rfl, hbase, hM] at hgap
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro β h q s v hp
    exact (hK ⟨(β, h), hp⟩).elim

/-- A uniform quadratic improvement of the GT functional away from the
replica-symmetric overlap.  The branchwise estimates used to establish this
statement are exported by the case modules above. -/
theorem gtFunctional_uniform_quadratic_gap {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c > 0, ∀ {β h q s v : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (-1 : ℝ) 1 →
      ∃ lam ∈ Icc (-1 : ℝ) 1, gtFunctional β h q s lam v ≤
        2 * rsPathValue β h q s - c * (v - q) ^ 2 := by
  obtain ⟨κ, hκ, hlargeNeg⟩ :=
    gtFunctional_uniform_gap_large_negative data
  obtain ⟨cNeg, hcNeg, hsmallNeg⟩ :=
    flatness_gtFunctional_quadratic_gap_small_negative data
  obtain ⟨cLo, hcLo, hLo⟩ :=
    gtFunctional_lower_positive_away_quadratic_gap data
  obtain ⟨cHi, hcHi, hHi⟩ :=
    gtFunctional_upper_positive_away_quadratic_gap data
  let c : ℝ := min (κ / 4) (min cNeg (min (cLo / 4) (cHi / 4)))
  have hc : 0 < c := by
    exact lt_min (div_pos hκ (by norm_num))
      (lt_min hcNeg (lt_min (div_pos hcLo (by norm_num))
        (div_pos hcHi (by norm_num))))
  refine ⟨c, hc, ?_⟩
  intro β h q s v hp hq hs hv
  have hβ : 0 < β := data.β_pos (β, h) hp
  have hh : 0 < h := data.h_pos (β, h) hp
  have hqIoo : q ∈ Ioo (0 : ℝ) 1 := by
    rw [hq]
    exact ⟨rsQ_pos hβ hh, rsQ_lt_one hβ hh⟩
  have hqIcc : q ∈ Icc (0 : ℝ) 1 := ⟨hqIoo.1.le, hqIoo.2.le⟩
  by_cases hlarge : v < -q
  · obtain ⟨lam, hlam, hbound⟩ := hlargeNeg hp hq hs ⟨hv.1, hlarge.le⟩
    refine ⟨lam, hlam, hbound.trans ?_⟩
    have hcκ : c ≤ κ / 4 := min_le_left _ _
    have hsq : (v - q) ^ 2 ≤ 4 := sub_sq_le_four_of_overlap hqIcc hv
    have hprod : c * (v - q) ^ 2 ≤ κ := by
      calc
        c * (v - q) ^ 2 ≤ (κ / 4) * (v - q) ^ 2 :=
          mul_le_mul_of_nonneg_right hcκ (sq_nonneg _)
        _ ≤ (κ / 4) * 4 :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg hκ.le (by norm_num))
        _ = κ := by ring
    linarith
  have hvge : -q ≤ v := le_of_not_gt hlarge
  by_cases hvneg : v < 0
  · obtain ⟨lam, hlam, hbound⟩ := hsmallNeg hp hq hs ⟨hvge, hvneg⟩
    refine ⟨lam, hlam, hbound.trans ?_⟩
    have hcNeg' : c ≤ cNeg :=
      (min_le_right (κ / 4) _).trans (min_le_left _ _)
    nlinarith [mul_le_mul_of_nonneg_right hcNeg' (sq_nonneg (v - q))]
  have hv0 : 0 ≤ v := le_of_not_gt hvneg
  by_cases hvq : v < q
  · let ε : ℝ := (q - v) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hvaway : v < q - ε := by dsimp [ε]; linarith
    obtain ⟨lam, hlam, hbound⟩ := hLo hp hq hs hε hv0 hvaway
    refine ⟨lam, hlam, hbound.trans ?_⟩
    have hcLo' : c ≤ cLo / 4 :=
      (min_le_right (κ / 4) _).trans
        ((min_le_right cNeg _).trans (min_le_left _ _))
    have hεsq : ε ^ 2 = (v - q) ^ 2 / 4 := by dsimp [ε]; ring
    rw [hεsq] at hbound ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcLo' (sq_nonneg (v - q))]
  by_cases hqv : q < v
  · let ε : ℝ := (v - q) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hvaway : q + ε < v := by dsimp [ε]; linarith
    obtain ⟨lam, hlam, hbound⟩ := hHi hp hq hs hε hvaway hv.2
    refine ⟨lam, hlam, hbound.trans ?_⟩
    have hcHi' : c ≤ cHi / 4 :=
      (min_le_right (κ / 4) _).trans
        ((min_le_right cNeg _).trans (min_le_right _ _))
    have hεsq : ε ^ 2 = (v - q) ^ 2 / 4 := by dsimp [ε]; ring
    rw [hεsq] at hbound ⊢
    nlinarith [mul_le_mul_of_nonneg_right hcHi' (sq_nonneg (v - q))]
  have hvqeq : v = q := le_antisymm (le_of_not_gt hqv) (le_of_not_gt hvq)
  subst v
  refine ⟨0, by norm_num, ?_⟩
  have hzero := flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
    β h q s q hqIoo hs ⟨hqIoo.1.le, le_rfl⟩
  simpa using hzero.le

end SpinGlass.AT
