module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

open Real

namespace SpinGlass
namespace GeneralizedLatala

/-!
# Kearns--Saul inequality

This file states the scalar form of the Kearns--Saul inequality needed at the
independent endpoint of the generalized Latała argument.  It has no dependency
on the spin-glass development.
-/

/-- The sharp sub-Gaussian coefficient for a random sign of mean `q`.

The separate value at `q = 0` is the continuous extension of
`q / artanh q`.
-/
noncomputable def ksCoefficient (q : ℝ) : ℝ :=
  if q = 0 then 1 else q / Real.artanh q

/-
A convenient form of the elementary inequality `x ≤ sinh x`.
-/
private lemma le_sinh_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sinh x * Real.cosh x := by
  have h_subst : ∀ y : ℝ, 0 ≤ y → y ≤ Real.sinh y := by
    by_contra h_contra;
    -- Apply the fact that $y \leq \sinh y$ for all $y \geq 0$.
    have h_le : ∀ y : ℝ, 0 ≤ y → y ≤ Real.sinh y := by
      intro y hy; rw [ Real.sinh_eq ] ; ring_nf; norm_num [ hy ] ;
      -- Apply the inequality $e^y \geq 1 + y + \frac{y^2}{2}$ for $y \geq 0$.
      have h_exp_ineq : ∀ y : ℝ, 0 ≤ y → Real.exp y ≥ 1 + y + y^2 / 2 :=
        fun _ hy => Real.quadratic_le_exp_of_nonneg hy
      nlinarith [ h_exp_ineq y hy, Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
    contradiction;
  have := h_subst ( 2 * x ) ( mul_nonneg zero_le_two hx ) ; rw [ Real.sinh_two_mul ] at this; nlinarith [ Real.cosh_sq' x, Real.cosh_pos x ] ;

/-
The derivative of `tanh x / x` is nonpositive for positive `x`.
-/
private lemma deriv_tanh_div_nonpos {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => Real.tanh y / y) x ≤ 0 := by
  have ht : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
    have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
      (Real.cosh_pos x).ne'
    have hfun : (fun y : ℝ => Real.sinh y / Real.cosh y) = Real.tanh := by
      funext y
      exact (Real.tanh_eq_sinh_div_cosh y).symm
    change HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y) _ x at h
    rw [hfun] at h
    apply h.congr_deriv
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
  have h_deriv : deriv (fun y => Real.tanh y / y) x =
      ((1 - Real.tanh x ^ 2) * x - Real.tanh x) / x ^ 2 := by
    change deriv (Real.tanh / id) x = _
    simpa only [Pi.div_apply, id_eq, mul_one] using
      (ht.div (hasDerivAt_id x) hx.ne').deriv
  rw [ h_deriv, div_le_iff₀ ] <;> norm_num [ Real.tanh_eq_sinh_div_cosh ];
  · field_simp;
    simpa [ Real.cosh_sq' ] using le_sinh_mul_cosh hx.le;
  · positivity

/-- The quotient `tanh x / x` decreases on the positive half-line. -/
private lemma antitoneOn_tanh_div :
    AntitoneOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) := by
  have ht : Differentiable ℝ Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x]
    exact Real.differentiable_sinh.div Real.differentiable_cosh
      fun x => (Real.cosh_pos x).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · apply ContinuousOn.div ht.continuous.continuousOn continuous_id.continuousOn
    intro x hx
    exact hx.ne'
  · rw [interior_Ioi]
    apply DifferentiableOn.div ht.differentiableOn differentiable_id.differentiableOn
    intro x hx
    exact hx.ne'
  · rw [interior_Ioi]
    intro x hx
    exact deriv_tanh_div_nonpos hx

/-
The logarithm of `cosh` lies below its tangent when regarded as a
function of the squared argument.
-/
private lemma log_cosh_le_quadratic_tangent {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.log (Real.cosh x) - Real.log (Real.cosh a) ≤
      Real.tanh a / (2 * a) * (x ^ 2 - a ^ 2) := by
  let g : ℝ → ℝ := fun z => Real.log (Real.cosh z) -
    Real.tanh a / (2 * a) * z ^ 2
  have hg_deriv (y : ℝ) :
      deriv g y = Real.tanh y - (Real.tanh a / a) * y := by
    dsimp [g]
    have hlog : HasDerivAt (fun z : ℝ => Real.log (Real.cosh z)) (Real.tanh y) y := by
      convert (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne' using 1
      exact Real.tanh_eq_sinh_div_cosh y
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y)
    have hmul := hsq.const_mul (Real.tanh a / (2 * a))
    change deriv ((fun z : ℝ => Real.log (Real.cosh z)) -
      fun z : ℝ => Real.tanh a / (2 * a) * z ^ 2) y = _
    rw [(hlog.sub hmul).deriv]
    ring
  have hg_diff : Differentiable ℝ g := by
    intro y
    dsimp [g]
    exact ((Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne').differentiableAt.sub
      (((hasDerivAt_id y).pow 2).const_mul
        (Real.tanh a / (2 * a))).differentiableAt
  let b := |x|
  have hb0 : 0 ≤ b := abs_nonneg x
  have hgb : g b = g x := by
    dsimp [g, b]
    rw [Real.cosh_abs, sq_abs]
  have hga : g b ≤ g a := by
    rcases le_total b a with hba | hab
    · have hmono : MonotoneOn g (Set.Icc 0 a) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
        · exact hg_diff.continuous.continuousOn
        · exact hg_diff.differentiableOn
        · intro y hy
          rw [interior_Icc] at hy
          rw [hg_deriv]
          have hr := antitoneOn_tanh_div hy.1 ha hy.2.le
          change Real.tanh a / a ≤ Real.tanh y / y at hr
          have hmul := mul_le_mul_of_nonneg_right hr hy.1.le
          rw [div_mul_cancel₀ _ hy.1.ne'] at hmul
          linarith
      exact hmono ⟨hb0, hba⟩ ⟨ha.le, le_rfl⟩ hba
    · have hanti_g : AntitoneOn g (Set.Ici a) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici a)
        · exact hg_diff.continuous.continuousOn
        · exact hg_diff.differentiableOn
        · intro y hy
          rw [interior_Ici] at hy
          rw [hg_deriv]
          have hy0 : 0 < y := ha.trans hy
          have hr := antitoneOn_tanh_div ha hy0 hy.le
          change Real.tanh y / y ≤ Real.tanh a / a at hr
          have hmul := mul_le_mul_of_nonneg_right hr hy0.le
          rw [div_mul_cancel₀ _ hy0.ne'] at hmul
          linarith
      exact hanti_g (show a ∈ Set.Ici a by simp) (show b ∈ Set.Ici a by exact hab) hab
  rw [hgb] at hga
  dsimp [g] at hga
  linarith

/-
Kearns--Saul inequality for a random variable in `{-1, 1}` with mean `q`.

The expression on the left is the moment generating function of `X - q`, where
`P(X = 1) = (1 + q) / 2` and `P(X = -1) = (1 - q) / 2`.
-/
lemma kearns_saul_inequality
    {q u : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ((1 + q) / 2) * Real.exp (u * (1 - q)) +
        ((1 - q) / 2) * Real.exp (-u * (1 + q))
      ≤ Real.exp (ksCoefficient q * u ^ 2 / 2) := by
  by_cases hq : q = 0;
  · subst q
    calc
      _ = Real.cosh u := by rw [Real.cosh_eq]; ring
      _ ≤ Real.exp (u ^ 2 / 2) := Real.cosh_le_exp_half_sq u
      _ = _ := by simp [ksCoefficient]
  · -- Let $a = \text{artanh}(q)$, so $a > 0$ and $\tanh(a) = q$.
    set a := Real.artanh q with ha
    have ha_pos : 0 < a := by
      exact Real.artanh_pos ⟨lt_of_le_of_ne hq0 (Ne.symm hq), hq1⟩
    have h_tanh_a : Real.tanh a = q := by
      rw [ Real.tanh_eq_sinh_div_cosh, Real.sinh_artanh, Real.cosh_artanh ];
      · rw [ div_div, mul_one_div, div_eq_iff ] ; ring ; norm_num [ ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < 1 - q ^ 2 by nlinarith ) ) ];
        exact div_ne_zero ( Real.sqrt_ne_zero'.mpr ( by nlinarith ) ) ( Real.sqrt_ne_zero'.mpr ( by nlinarith ) );
      · constructor <;> linarith;
      · constructor <;> linarith;
    -- Algebraically rewrite LHS as exp(-q*u) * (cosh (u+a) / cosh a).
    have h_lhs : (1 + q) / 2 * Real.exp (u * (1 - q)) + (1 - q) / 2 * Real.exp (-u * (1 + q)) = Real.exp (-q * u) * (Real.cosh (u + a) / Real.cosh a) := by
      rw [ Real.tanh_eq_sinh_div_cosh, div_eq_iff ] at h_tanh_a <;> norm_num [ Real.sinh_add, Real.cosh_add ] at *;
      · rw [ h_tanh_a, Real.cosh_eq, Real.sinh_eq ] ; ring;
        norm_num [ Real.exp_add, Real.exp_sub, ne_of_gt ( Real.cosh_pos _ ) ] ; ring;
        norm_num [ Real.exp_neg ];
      · exact ne_of_gt ( Real.cosh_pos _ );
    -- Apply the helper lemma `log_cosh_le_quadratic_tangent` with `x = u + a`.
    have h_helper : Real.log (Real.cosh (u + a)) - Real.log (Real.cosh a) ≤ (Real.tanh a / (2 * a)) * ((u + a) ^ 2 - a ^ 2) := by
      apply log_cosh_le_quadratic_tangent ha_pos;
    convert Real.exp_le_exp.mpr ( show -q * u + Real.log ( Real.cosh ( u + a ) ) - Real.log ( Real.cosh a ) ≤ ksCoefficient q * u ^ 2 / 2 from ?_ ) using 1;
    · rw [ h_lhs, Real.exp_sub, Real.exp_add, Real.exp_log ( Real.cosh_pos _ ), Real.exp_log ( Real.cosh_pos _ ) ];
      ring;
    · unfold ksCoefficient; ring_nf at *; simp_all +decide [ ne_of_gt ] ;
      convert h_helper using 1 ; ring_nf ; norm_num [ ha_pos.ne' ]

end GeneralizedLatala
end SpinGlass
