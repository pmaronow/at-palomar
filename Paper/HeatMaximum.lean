module

public import Paper.HeatGrowth
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! # Maximum principle for the actual linear backward heat equation

The compact comparison principle includes the initial time boundary.  Its
  linear-growth extension uses a strictly positive quadratic barrier, so no
boundedness of the potential is assumed.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Paper

theorem localMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hh
  have hn := isLocalMin_of_deriv_deriv_pos (lt_of_not_ge hh) hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hn] with y hy hz
    exact le_antisymm hy hz
  have hz := he.deriv.deriv_eq
  have hconst : deriv (fun _ : ℝ => f x) = fun _ => (0 : ℝ) :=
    funext fun y => deriv_const y (f x)
  rw [hconst, deriv_const] at hz
  exact (ne_of_gt (lt_of_not_ge hh)) hz

theorem maxOn_Icc_deriv_nonpos {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hm : IsMaxOn f (Icc a b) a) (hd : HasDerivAt f d a) : d ≤ 0 := by
  have ht : (1 : ℝ) ∈ posTangentConeAt (Icc a b) a := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have hs : Ioi a ∩ Icc a b = Ioc a b := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, h.1.le, h.2⟩
    rw [hs, closure_Ioc hab.ne]
    exact ⟨le_rfl, hab.le⟩
  simpa using hm.isLocalMaxOn.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt ht

/-- A strict backward subsolution cannot have a positive maximum when the
terminal and spatial boundary values are nonpositive. -/
theorem backwardHeat_compact_nonpos (c a b R : ℝ) (hc : 0 ≤ c)
    (hab : a ≤ b) (hR : 0 < R) (w : ℝ × ℝ → ℝ)
    (hw : ContinuousOn w (Icc a b ×ˢ Icc (-R) R))
    (ht : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      DifferentiableAt ℝ (fun s => w (s, x)) t)
    (hx : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      DifferentiableAt ℝ (fun y => w (t, y)) x)
    (hPDE : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      0 < deriv (fun s => w (s, x)) t + c * deriv (deriv (fun y => w (t, y))) x)
    (hterminal : ∀ x ∈ Icc (-R) R, w (b, x) ≤ 0)
    (hleft : ∀ t ∈ Icc a b, w (t, -R) ≤ 0)
    (hright : ∀ t ∈ Icc a b, w (t, R) ≤ 0) :
    ∀ p ∈ Icc a b ×ˢ Icc (-R) R, w p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < w p := lt_of_not_ge hn
  obtain ⟨z, hz, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨p, hp⟩ hw
  have hzpos : 0 < w z := hpos.trans_le (hmax hp)
  have hzb : z.1 < b := by
    apply lt_of_le_of_ne hz.1.2
    intro he
    have hh := hterminal z.2 hz.2
    rw [← he] at hh
    exact (not_le_of_gt hzpos) hh
  have hzL : -R < z.2 := by
    apply lt_of_le_of_ne hz.2.1
    intro he
    have hh := hleft z.1 hz.1
    rw [he] at hh
    exact (not_le_of_gt hzpos) hh
  have hzR : z.2 < R := by
    apply lt_of_le_of_ne hz.2.2
    intro he
    have hh := hright z.1 hz.1
    rw [← he] at hh
    exact (not_le_of_gt hzpos) hh
  have hzt : z.1 ∈ Ico a b := ⟨hz.1.1, hzb⟩
  have hzx : z.2 ∈ Ioo (-R) R := ⟨hzL, hzR⟩
  have htm : IsMaxOn (fun s => w (s, z.2)) (Icc z.1 b) z.1 := by
    intro s hs
    exact hmax ⟨⟨hz.1.1.trans hs.1, hs.2⟩, hz.2⟩
  have htd : deriv (fun s => w (s, z.2)) z.1 ≤ 0 :=
    maxOn_Icc_deriv_nonpos hzb htm (ht z.1 hzt z.2 hzx).hasDerivAt
  have hxm : IsLocalMax (fun y => w (z.1, y)) z.2 := by
    filter_upwards [Ioo_mem_nhds hzL hzR] with y hy
    exact hmax ⟨hz.1, ⟨hy.1.le, hy.2.le⟩⟩
  have hxxd := localMax_second_deriv_nonpos hxm (hx z.1 hzt z.2 hzx).continuousAt
  have hh := hPDE z.1 hzt z.2 hzx
  have hmul := mul_nonpos_of_nonneg_of_nonpos hc hxxd
  linarith

def heatQuadraticBarrier (c b ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε * (1 + p.2 ^ 2 + (2 * c + 1) * (b - p.1))

theorem heatQuadraticBarrier_hasDerivAt_time (c b ε t x : ℝ) :
    HasDerivAt (fun s => heatQuadraticBarrier c b ε (s, x)) (-ε * (2 * c + 1)) t := by
  convert (((hasDerivAt_const t (1 + x ^ 2)).add
    (((hasDerivAt_const t b).sub (hasDerivAt_id t)).const_mul (2 * c + 1))).const_mul ε)
    using 1 <;> simp [heatQuadraticBarrier] <;> ring

theorem heatQuadraticBarrier_hasDerivAt_space (c b ε t x : ℝ) :
    HasDerivAt (fun y => heatQuadraticBarrier c b ε (t, y)) (2 * ε * x) x := by
  convert ((((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)).add
    (hasDerivAt_const x ((2 * c + 1) * (b - t)))).const_mul ε) using 1 <;>
    simp [heatQuadraticBarrier] <;> ring

theorem heatQuadraticBarrier_deriv2 (c b ε t x : ℝ) :
    deriv (deriv (fun y => heatQuadraticBarrier c b ε (t, y))) x = 2 * ε := by
  have he : deriv (fun y => heatQuadraticBarrier c b ε (t, y)) = fun y => 2 * ε * y :=
    funext fun y => (heatQuadraticBarrier_hasDerivAt_space c b ε t y).deriv
  rw [he]
  simpa using ((hasDerivAt_id x).const_mul (2 * ε)).deriv

/-- Uniqueness comparison for a classical backward heat solution with
uniform linear spatial growth. The terminal potential may be unbounded. -/
theorem classical_backwardHeat_nonpos_of_linearGrowth (c a b A L : ℝ)
    (hc : 0 ≤ c) (hab : a ≤ b) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (w : ℝ × ℝ → ℝ) (hw : ContinuousOn w (Icc a b ×ˢ univ))
    (ht : ∀ t ∈ Ico a b, ∀ x, DifferentiableAt ℝ (fun s => w (s, x)) t)
    (hx : ∀ t ∈ Ico a b, ∀ x, DifferentiableAt ℝ (fun y => w (t, y)) x)
    (hxx : ∀ t ∈ Ico a b, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => w (t, y))) x)
    (hPDE : ∀ t ∈ Ico a b, ∀ x,
      deriv (fun s => w (s, x)) t + c * deriv (deriv (fun y => w (t, y))) x = 0)
    (hgrowth : ∀ t ∈ Icc a b, ∀ x, ‖w (t, x)‖ ≤ A + L * ‖x‖)
    (hterminal : ∀ x, w (b, x) ≤ 0) :
    ∀ p ∈ Icc a b ×ˢ univ, w p ≤ 0 := by
  intro p hp
  by_contra hn
  have hpos : 0 < w p := lt_of_not_ge hn
  let E : ℝ := 1 + p.2 ^ 2 + (2 * c + 1) * (b - p.1)
  have hE : 0 < E := by
    have hh := mul_nonneg (by linarith : 0 ≤ 2 * c + 1) (sub_nonneg.mpr hp.1.2)
    dsimp [E]
    nlinarith [sq_nonneg p.2]
  let ε : ℝ := w p / (2 * E)
  have hε : 0 < ε := div_pos hpos (mul_pos (by norm_num) hE)
  have hεE : ε * E = w p / 2 := by dsimp [ε]; field_simp
  let R : ℝ := max |p.2| 1 + (A + L + 1) / ε + 1
  have hdiv : 0 < (A + L + 1) / ε := div_pos (by linarith) hε
  have hR1 : 1 ≤ R := by change 1 ≤ max |p.2| 1 + (A + L + 1) / ε + 1; linarith [le_max_right |p.2| 1]
  have hpR : |p.2| < R := by change |p.2| < max |p.2| 1 + (A + L + 1) / ε + 1; linarith [le_max_left |p.2| 1]
  have hR : 0 < R := by linarith
  have hεR : A + L + 1 < ε * R := by
    have he : ε * ((A + L + 1) / ε) = A + L + 1 := by field_simp
    change A + L + 1 < ε * (max |p.2| 1 + (A + L + 1) / ε + 1)
    rw [mul_add, mul_add, he]
    have hm := mul_nonneg hε.le (le_max_right |p.2| 1 |>.trans' (by norm_num))
    rw [mul_one]
    linarith
  have hboundary : A + L * R < ε * (1 + R ^ 2) := by
    have hh := mul_lt_mul_of_pos_right hεR hR
    have ha := mul_le_mul_of_nonneg_left hR1 hA
    nlinarith [hε, ha]
  let v : ℝ × ℝ → ℝ := fun z => w z - heatQuadraticBarrier c b ε z
  have hvcont : ContinuousOn v (Icc a b ×ˢ Icc (-R) R) := by
    exact (hw.mono (fun z hz => ⟨hz.1, mem_univ _⟩)).sub (by
      unfold heatQuadraticBarrier
      fun_prop)
  have hvt : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      DifferentiableAt ℝ (fun s => v (s, x)) t := fun t ht0 x _ =>
    (ht t ht0 x).sub (heatQuadraticBarrier_hasDerivAt_time c b ε t x).differentiableAt
  have hvx : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      DifferentiableAt ℝ (fun y => v (t, y)) x := fun t ht0 x _ =>
    (hx t ht0 x).sub (heatQuadraticBarrier_hasDerivAt_space c b ε t x).differentiableAt
  have hvPDE : ∀ t ∈ Ico a b, ∀ x ∈ Ioo (-R) R,
      0 < deriv (fun s => v (s, x)) t + c * deriv (deriv (fun y => v (t, y))) x := by
    intro t ht0 x _
    have he : deriv (fun y => v (t, y)) =
        fun y => deriv (fun z => w (t, z)) y - 2 * ε * y := by
      funext y
      exact ((hx t ht0 y).hasDerivAt.sub
        (heatQuadraticBarrier_hasDerivAt_space c b ε t y)).deriv
    have heT : deriv (fun s => v (s, x)) t = deriv (fun s => w (s, x)) t + ε * (2 * c + 1) := by
      change deriv ((fun s => w (s, x)) - (fun s => heatQuadraticBarrier c b ε (s, x))) t = _
      rw [((ht t ht0 x).hasDerivAt.sub
        (heatQuadraticBarrier_hasDerivAt_time c b ε t x)).deriv]
      ring
    have heXX : deriv (fun y => deriv (fun z => w (t, z)) y - 2 * ε * y) x =
        deriv (deriv (fun y => w (t, y))) x - 2 * ε := by
      change deriv ((deriv (fun z => w (t, z))) - (fun y => 2 * ε * y)) x = _
      simpa only [id_eq, mul_one] using ((hxx t ht0 x).hasDerivAt.sub
        ((hasDerivAt_id x).const_mul (2 * ε))).deriv
    rw [he, heXX, heT]
    have hh := hPDE t ht0 x
    nlinarith
  have hterm : ∀ x ∈ Icc (-R) R, v (b, x) ≤ 0 := by
    intro x _
    have hb0 : 0 ≤ heatQuadraticBarrier c b ε (b, x) := by
      unfold heatQuadraticBarrier
      simpa using mul_nonneg hε.le (by nlinarith [sq_nonneg x] : 0 ≤ 1 + x ^ 2)
    exact sub_nonpos.mpr ((hterminal x).trans hb0)
  have hside : ∀ t ∈ Icc a b, ∀ x : ℝ, ‖x‖ = R → v (t, x) ≤ 0 := by
    intro t ht0 x hxR
    have hh := hgrowth t ht0 x
    rw [hxR] at hh
    have hx2 : x ^ 2 = R ^ 2 := by
      rw [Real.norm_eq_abs] at hxR
      nlinarith [sq_abs x]
    have hb0 : ε * (1 + R ^ 2) ≤ heatQuadraticBarrier c b ε (t, x) := by
      unfold heatQuadraticBarrier
      rw [hx2]
      have hm := mul_nonneg (by linarith : 0 ≤ 2 * c + 1) (sub_nonneg.mpr ht0.2)
      nlinarith
    exact sub_nonpos.mpr ((le_abs_self (w (t, x))).trans
      (by simpa only [Real.norm_eq_abs] using hh) |>.trans hboundary.le |>.trans hb0)
  have hvnonpos := backwardHeat_compact_nonpos c a b R hc hab hR v hvcont hvt hvx
    hvPDE hterm (fun t ht0 => hside t ht0 (-R) (by simp [abs_of_pos hR]))
    (fun t ht0 => hside t ht0 R (by simp [abs_of_pos hR]))
  have hpbox : p ∈ Icc a b ×ˢ Icc (-R) R := by
    refine ⟨hp.1, ?_⟩
    exact ⟨(abs_lt.mp hpR).1.le, (abs_lt.mp hpR).2.le⟩
  have hh := hvnonpos p hpbox
  change w p - ε * E ≤ 0 at hh
  rw [hεE] at hh
  linarith

theorem classical_backwardHeat_eq_zero_of_linearGrowth (c a b A L : ℝ)
    (hc : 0 ≤ c) (hab : a ≤ b) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (w : ℝ × ℝ → ℝ) (hw : ContinuousOn w (Icc a b ×ˢ univ))
    (ht : ∀ t ∈ Ico a b, ∀ x, DifferentiableAt ℝ (fun s => w (s, x)) t)
    (hx : ∀ t ∈ Ico a b, ∀ x, DifferentiableAt ℝ (fun y => w (t, y)) x)
    (hxx : ∀ t ∈ Ico a b, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => w (t, y))) x)
    (hPDE : ∀ t ∈ Ico a b, ∀ x,
      deriv (fun s => w (s, x)) t + c * deriv (deriv (fun y => w (t, y))) x = 0)
    (hgrowth : ∀ t ∈ Icc a b, ∀ x, ‖w (t, x)‖ ≤ A + L * ‖x‖)
    (hterminal : ∀ x, w (b, x) = 0) :
    ∀ p ∈ Icc a b ×ˢ univ, w p = 0 := by
  have hle := classical_backwardHeat_nonpos_of_linearGrowth c a b A L hc hab hA hL
    w hw ht hx hxx hPDE hgrowth (fun x => (hterminal x).le)
  have hnegdx (t : ℝ) (ht0 : t ∈ Ico a b) :
      deriv (fun y => -w (t, y)) = fun y => -deriv (fun z => w (t, z)) y := by
    funext y
    exact (hx t ht0 y).hasDerivAt.neg.deriv
  have hnxx : ∀ t ∈ Ico a b, ∀ x,
      DifferentiableAt ℝ (deriv (fun y => -w (t, y))) x := by
    intro t ht0 x
    rw [hnegdx t ht0]
    exact (hxx t ht0 x).neg
  have hnPDE : ∀ t ∈ Ico a b, ∀ x,
      deriv (fun s => -w (s, x)) t + c * deriv (deriv (fun y => -w (t, y))) x = 0 := by
    intro t ht0 x
    rw [hnegdx t ht0]
    have heT : deriv (fun s => -w (s, x)) t = -deriv (fun s => w (s, x)) t :=
      (ht t ht0 x).hasDerivAt.neg.deriv
    have heXX : deriv (fun y => -deriv (fun z => w (t, z)) y) x =
        -deriv (deriv (fun y => w (t, y))) x := (hxx t ht0 x).hasDerivAt.neg.deriv
    rw [heT, heXX]
    linarith [hPDE t ht0 x]
  have hge := classical_backwardHeat_nonpos_of_linearGrowth c a b A L hc hab hA hL
    (fun p => -w p) hw.neg (fun t ht0 x => (ht t ht0 x).neg)
    (fun t ht0 x => (hx t ht0 x).neg) hnxx hnPDE
    (fun t ht0 x => by simpa only [norm_neg] using hgrowth t ht0 x)
    (fun x => by simp only [hterminal x, neg_zero, le_refl])
  intro p hp
  exact le_antisymm (hle p hp) (neg_nonpos.mp (hge p hp))

end Paper
