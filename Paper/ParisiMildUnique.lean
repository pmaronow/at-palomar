module

public import Paper.ParisiLocal
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-! # Uniqueness of actual bounded continuous mild gradients

Short-time contraction applies to any common bound for the two gradients.
Backward continuation therefore does not require the sharp gradient bound
used to construct the solution.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Paper

theorem parisiGradientCorrection_congr (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (b t x : ℝ) (htb : t ≤ b)
    (he : ∀ s ∈ Icc t b, ∀ y : ℝ, v (s, y) = w (s, y)) :
    parisiGradientCorrection β μ v b t x = parisiGradientCorrection β μ w b t x := by
  unfold parisiGradientCorrection
  congr 1
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le htb]
  intro s hs
  unfold parisiGradientSource heatGradient gaussianExpectation
  simp_rw [he s hs]

theorem parisiGradientCorrection_sub_eq_of_tail (β : ℝ) (μ : ParisiMeasure)
    (v w : ℝ × ℝ → ℝ) (hv : Measurable v) (hw : Measurable w)
    (R : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (b t x : ℝ) (htb : t ≤ b) (hb : b ≤ 1)
    (he : ∀ s ∈ Icc b 1, ∀ y : ℝ, v (s, y) = w (s, y)) :
    parisiGradientCorrection β μ v 1 t x - parisiGradientCorrection β μ w 1 t x =
      parisiGradientCorrection β μ v b t x - parisiGradientCorrection β μ w b t x := by
  have hiv := parisiGradientSource_intervalIntegrable β μ v hv R hvb t x 1 (htb.trans hb)
  have hiw := parisiGradientSource_intervalIntegrable β μ w hw R hwb t x 1 (htb.trans hb)
  have hisv := parisiGradientSource_intervalIntegrable β μ v hv R hvb t x b htb
  have hisw := parisiGradientSource_intervalIntegrable β μ w hw R hwb t x b htb
  have hivtail := hiv.mono_set (by
    rw [uIcc_of_le hb, uIcc_of_le (htb.trans hb)]
    exact Icc_subset_Icc htb le_rfl)
  have hiwtail := hiw.mono_set (by
    rw [uIcc_of_le hb, uIcc_of_le (htb.trans hb)]
    exact Icc_subset_Icc htb le_rfl)
  have htail : (∫ s in b..(1 : ℝ), parisiGradientSource β μ v t x s) =
      ∫ s in b..(1 : ℝ), parisiGradientSource β μ w t x s := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hb]
    intro s hs
    unfold parisiGradientSource heatGradient gaussianExpectation
    simp_rw [he s hs]
  unfold parisiGradientCorrection
  rw [← intervalIntegral.integral_add_adjacent_intervals hisv hivtail,
    ← intervalIntegral.integral_add_adjacent_intervals hisw hiwtail, htail]
  ring

/-- Equality on a terminal tail extends across one short slab. -/
theorem parisiMildGradient_unique_step (β : ℝ) (μ : ParisiMeasure)
    (g : ℝ → ℝ) (v w : ℝ × ℝ → ℝ) (hv : Continuous v) (hw : Continuous w)
    (R : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (heqv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ v 1 t x)
    (heqw : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      w (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ w 1 t x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hsmall : 2 * |β| * gaussianAbsMoment * R * Real.sqrt (b - a) < 1)
    (htail : ∀ s ∈ Icc b 1, ∀ y : ℝ, v (s, y) = w (s, y)) :
    ∀ s ∈ Icc a b, ∀ y : ℝ, v (s, y) = w (s, y) := by
  have hR : 0 ≤ R := (norm_nonneg (v (0, 0))).trans (hvb _)
  let V : ParisiSlabGradient a b := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => v (p.1, p.2)) (hv.comp (by fun_prop)) R (fun p => hvb _)
  let W : ParisiSlabGradient a b := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => w (p.1, p.2)) (hw.comp (by fun_prop)) R (fun p => hwb _)
  have hV : ‖V‖ ≤ R := (BoundedContinuousFunction.norm_le hR).mpr (fun p => hvb _)
  have hW : ‖W‖ ≤ R := (BoundedContinuousFunction.norm_le hR).mpr (fun p => hwb _)
  have hrestrictV (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      parisiSlabExtend hab V (t, x) = v (t, x) := by
    simp only [parisiSlabExtend, projIcc_of_mem hab ht, V,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  have hrestrictW (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      parisiSlabExtend hab W (t, x) = w (t, x) := by
    simp only [parisiSlabExtend, projIcc_of_mem hab ht, W,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  have hpoint (p : Icc a b × ℝ) :
      ‖(V - W) p‖ ≤ (2 * |β| * gaussianAbsMoment * R * Real.sqrt (b - a)) * ‖V - W‖ := by
    have hpt : (p.1 : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨ha.trans p.1.property.1, p.1.property.2.trans hb⟩
    have hdiff : v (p.1, p.2) - w (p.1, p.2) =
        parisiGradientCorrection β μ (parisiSlabExtend hab V) b p.1 p.2 -
          parisiGradientCorrection β μ (parisiSlabExtend hab W) b p.1 p.2 := by
      rw [heqv p.1 hpt p.2, heqw p.1 hpt p.2, add_sub_add_left_eq_sub,
        parisiGradientCorrection_sub_eq_of_tail β μ v w hv.measurable hw.measurable
          R hvb hwb b p.1 p.2 p.1.property.2 hb htail]
      congr 1
      · exact parisiGradientCorrection_congr β μ v _ b p.1 p.2 p.1.property.2
          (fun s hs y => (hrestrictV s ⟨p.1.property.1.trans hs.1, hs.2⟩ y).symm)
      · exact parisiGradientCorrection_congr β μ w _ b p.1 p.2 p.1.property.2
          (fun s hs y => (hrestrictW s ⟨p.1.property.1.trans hs.1, hs.2⟩ y).symm)
    have hbound := norm_parisiGradientCorrection_sub_le β μ
      (parisiSlabExtend hab V) (parisiSlabExtend hab W)
      (continuous_parisiSlabExtend hab V).measurable
      (continuous_parisiSlabExtend hab W).measurable R ‖V - W‖
      (fun p => (norm_parisiSlabExtend_le hab V p).trans hV)
      (fun p => (norm_parisiSlabExtend_le hab W p).trans hW)
      (norm_parisiSlabExtend_sub_le hab V W) b p.1 p.2 p.1.property.2
    change ‖v (p.1, p.2) - w (p.1, p.2)‖ ≤ _
    rw [hdiff]
    apply hbound.trans
    have hs := Real.sqrt_le_sqrt (sub_le_sub_left p.1.property.1 b)
    have hc : 0 ≤ 2 * |β| * gaussianAbsMoment * R * ‖V - W‖ := by
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (abs_nonneg β)) gaussianAbsMoment_nonneg) hR)
        (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  have hnorm : ‖V - W‖ ≤
      (2 * |β| * gaussianAbsMoment * R * Real.sqrt (b - a)) * ‖V - W‖ :=
    (BoundedContinuousFunction.norm_le (by
      have := gaussianAbsMoment_nonneg
      positivity)).mpr hpoint
  have hzero : V - W = 0 := norm_eq_zero.mp (by
    have := norm_nonneg (V - W)
    nlinarith)
  have he : V = W := sub_eq_zero.mp hzero
  intro s hs y
  exact congrArg (fun z : ParisiSlabGradient a b => z (⟨s, hs⟩, y)) he

/-- The gradient Duhamel equation has at most one bounded continuous
solution on the full time interval, for any common terminal datum. -/
theorem parisiMildGradient_unique (β : ℝ) (μ : ParisiMeasure)
    (g : ℝ → ℝ) (v w : ℝ × ℝ → ℝ) (hv : Continuous v) (hw : Continuous w)
    (R : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (heqv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ v 1 t x)
    (heqw : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      w (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ w 1 t x) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, v (t, x) = w (t, x) := by
  have hR : 0 ≤ R := (norm_nonneg (v (0, 0))).trans (hvb _)
  let K : ℝ := 2 * |β| * gaussianAbsMoment * R
  have hK : 0 ≤ K := by
    dsimp [K]
    have := gaussianAbsMoment_nonneg
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (K ^ 2 + 1)
  have hNpos : (0 : ℝ) < N := by nlinarith [sq_nonneg K]
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hmesh : K * Real.sqrt (1 / (N : ℝ)) < 1 := by
    have hsqrt := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
    have hratio : K ^ 2 / (N : ℝ) < 1 := (div_lt_one hNpos).mpr (by linarith)
    have hsquare : (K * Real.sqrt (1 / (N : ℝ))) ^ 2 = K ^ 2 / (N : ℝ) := by
      rw [mul_pow, hsqrt]
      ring
    have hpos := mul_nonneg hK (Real.sqrt_nonneg (1 / (N : ℝ)))
    nlinarith
  have hind : ∀ n : ℕ, n ≤ N →
      ∀ t ∈ Icc (1 - (n : ℝ) / N) 1, ∀ x : ℝ, v (t, x) = w (t, x) := by
    intro n
    induction n with
    | zero =>
        intro _ t ht x
        have htone : t = 1 := by
          have htp : 1 ≤ t ∧ t ≤ 1 := by
            simpa only [Nat.cast_zero, zero_div, sub_zero, mem_Icc] using ht
          exact le_antisymm htp.2 htp.1
        subst t
        rw [heqv 1 ⟨by norm_num, le_rfl⟩ x, heqw 1 ⟨by norm_num, le_rfl⟩ x]
        simp [parisiGradientCorrection]
    | succ n ih =>
        intro hn t ht x
        have hn' : n ≤ N := by omega
        have hcast : (n + 1 : ℝ) ≤ N := by exact_mod_cast hn
        let a : ℝ := 1 - (n + 1 : ℝ) / N
        let b : ℝ := 1 - (n : ℝ) / N
        have ha : 0 ≤ a := by
          dsimp [a]
          linarith [(div_le_one hNpos).mpr hcast]
        have hab : a ≤ b := by
          dsimp [a, b]
          exact sub_le_sub_left (div_le_div_of_nonneg_right (by linarith) hNpos.le) 1
        have hb : b ≤ 1 := by
          dsimp [b]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith [div_nonneg hn0 hNpos.le]
        have hba : b - a = 1 / (N : ℝ) := by
          dsimp [a, b]
          ring
        have hshort : 2 * |β| * gaussianAbsMoment * R * Real.sqrt (b - a) < 1 := by
          rw [hba]
          exact hmesh
        have htail : ∀ s ∈ Icc b 1, ∀ y : ℝ, v (s, y) = w (s, y) := ih hn'
        have hstep := parisiMildGradient_unique_step β μ g v w hv hw R hvb hwb
          heqv heqw a b ha hab hb hshort htail
        have ht' : t ∈ Icc a 1 := by simpa only [Nat.cast_add, Nat.cast_one] using ht
        by_cases htb : t ≤ b
        · exact hstep t ⟨ht'.1, htb⟩ x
        · exact htail t ⟨(lt_of_not_ge htb).le, ht'.2⟩ x
  intro t ht x
  have htN : t ∈ Icc (1 - (N : ℝ) / N) 1 := by
    simpa only [div_self hNne, sub_self] using ht
  exact hind N le_rfl t htN x

/-- Once the mild gradient is fixed, the actual terminal-data Duhamel
potential is unique as well. -/
theorem parisiDuhamelPotential_eq_of_mildGradients (β : ℝ) (μ : ParisiMeasure)
    (g : ℝ → ℝ) (v w : ℝ × ℝ → ℝ) (hv : Continuous v) (hw : Continuous w)
    (R : ℝ) (hvb : ∀ p, ‖v p‖ ≤ R) (hwb : ∀ p, ‖w p‖ ≤ R)
    (heqv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      v (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ v 1 t x)
    (heqw : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      w (t, x) = heatSemigroup (β ^ 2 * (1 - t)) g x +
        parisiGradientCorrection β μ w 1 t x) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
      parisiDuhamelPotential β μ v t x = parisiDuhamelPotential β μ w t x := by
  have he := parisiMildGradient_unique β μ g v w hv hw R hvb hwb heqv heqw
  intro t ht x
  unfold parisiDuhamelPotential parisiDuhamelCorrection
  congr 2
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro s hs
  unfold parisiHeatSource heatSemigroup gaussianExpectation
  simp_rw [he s ⟨ht.1.trans hs.1, hs.2⟩]

end Paper
