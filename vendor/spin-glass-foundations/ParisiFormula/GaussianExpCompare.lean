module

/-
# Comparing Gaussian log-exp integrals with nearby exponents

New work for the ParisiFormula project (not vendored).

## Why this file exists

Target 2b-i (Talagrand's (2.17): the infimum of `𝒫_k` over admissible schemes is attained)
reduces to continuity of `𝒫_k` in its parameters on the compact admissible set.  Propagating
continuity through the `k+2` levels of the Parisi recursion needs, at each level, a bound on

  `log ∫ exp (m f) dγ  -  log ∫ exp (m g) dγ`

that is **uniform in the spatial variable `x`**, because level `j+1` evaluates level `j` at
every point `x + √v z` at once.

The perturbations that arise are *not* uniformly small in `z`: changing `q_p` changes the
smoothing width, so the two exponents differ by `|√v - √v'|·|z|`, which is unbounded.  That
rules out the sup-norm comparison `Targets.parisiStep_dist_le`.  What *is* available is a
bound of the shape `|f - g| ≤ c|z|` together with `|f|, |g| ≤ C|z|`, which is exactly the
hypothesis of `abs_log_integral_exp_sub_le` below.

## The estimate

Two elementary ingredients, neither needing convexity of the cumulant generating function
(Mathlib has no such lemma):

* `|e^a - e^b| ≤ |a - b| (e^a + e^b)`, giving
  `|∫ e^{mf} - ∫ e^{mg}| ≤ 2mc ∫ |z| e^{mC|z|} dγ`;
* `|log a - log b| · l ≤ |a - b|` whenever `l` is a common lower bound for `a` and `b`, with
  `∫ e^{mf} ≥ exp (m ∫ f) ≥ exp (-mC ∫|z|)` by Jensen — a lower bound depending only on `m`
  and `C`.

Together they give a bound proportional to `c` whose constant depends only on `m` and `C`.
Crucially the constant does **not** involve `f` or `g` beyond the growth bound, so after
normalising `Ã_x(u) = A(x + u) - A(x)` (which satisfies `|Ã_x(u)| ≤ |u|` for `A` 1-Lipschitz,
uniformly in `x`) the estimate is uniform in `x`.
-/
public import ParisiFormula.GaussianCosh

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped BigOperators NNReal

namespace SpinGlass

/-! ## 1. Two elementary real inequalities -/

/-- `exp t - 1 ≤ t exp t`, from `1 - t ≤ exp (-t)`. -/
theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hmul : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h (Real.exp_pos t).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  nlinarith

/-- **A Lipschitz-type bound for `exp`.**  `|e^a - e^b| ≤ |a - b| (e^a + e^b)`. -/
theorem abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ |a - b| * (Real.exp a + Real.exp b) := by
  have key : ∀ u v : ℝ, u ≤ v → Real.exp v - Real.exp u ≤ (v - u) * Real.exp v := by
    intro u v huv
    have he : Real.exp u * Real.exp (v - u) = Real.exp v := by
      rw [← Real.exp_add]; ring_nf
    have ht : Real.exp (v - u) - 1 ≤ (v - u) * Real.exp (v - u) := exp_sub_one_le_mul_exp _
    have hmul := mul_le_mul_of_nonneg_left ht (Real.exp_pos u).le
    rw [mul_sub, mul_one, he] at hmul
    calc Real.exp v - Real.exp u
        ≤ Real.exp u * ((v - u) * Real.exp (v - u)) := hmul
      _ = (v - u) * Real.exp v := by rw [← he]; ring
  rcases le_total a b with hab | hab
  · have h := key a b hab
    have habs : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.2 hab
    rw [habs, abs_le]
    constructor
    · nlinarith [Real.exp_pos a, Real.exp_pos b]
    · nlinarith [Real.exp_pos a, Real.exp_pos b]
  · have h := key b a hab
    have habs : |a - b| = a - b := abs_of_nonneg (by linarith)
    have h1 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.2 hab
    rw [habs, abs_le]
    constructor
    · nlinarith [Real.exp_pos a, Real.exp_pos b]
    · nlinarith [Real.exp_pos a, Real.exp_pos b]

/-- **A Lipschitz-type bound for `log` away from `0`.**  If `l` is a positive common lower
bound for `a` and `b`, then `|log a - log b| · l ≤ |a - b|`. -/
theorem abs_log_sub_log_le_of_pos {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l)
    (hla : l ≤ a) (hlb : l ≤ b) :
    |Real.log a - Real.log b| * l ≤ |a - b| := by
  have hone : ∀ u v : ℝ, 0 < u → 0 < v → l ≤ v → (Real.log u - Real.log v) * l ≤ |u - v| := by
    intro u v hu hv hlv
    have hstep1 : Real.log u - Real.log v ≤ (u - v) / v := by
      have hlog : Real.log u - Real.log v = Real.log (u / v) := (Real.log_div hu.ne' hv.ne').symm
      have hle : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hu hv)
      have hdiv : u / v - 1 = (u - v) / v := by field_simp
      rw [hlog, ← hdiv]
      exact hle
    have hstep2 : (Real.log u - Real.log v) * l ≤ (u - v) / v * l :=
      mul_le_mul_of_nonneg_right hstep1 hl.le
    have hvc : (u - v) / v * v = u - v := div_mul_cancel₀ _ hv.ne'
    have hstep3 : (u - v) / v * l ≤ |u - v| := by
      rcases le_or_gt v u with huv | huv
      · have hnn : 0 ≤ (u - v) / v := by nlinarith
        have hmul : (u - v) / v * l ≤ (u - v) / v * v := mul_le_mul_of_nonneg_left hlv hnn
        rw [hvc] at hmul
        exact hmul.trans (le_abs_self _)
      · have hnp : (u - v) / v ≤ 0 := by nlinarith
        have : (u - v) / v * l ≤ 0 := by nlinarith
        exact this.trans (abs_nonneg _)
    linarith
  rcases abs_cases (Real.log a - Real.log b) with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq]; exact hone a b ha hb hlb
  · rw [heq]
    have hba := hone b a hb ha hla
    rw [abs_sub_comm] at hba
    calc -(Real.log a - Real.log b) * l = (Real.log b - Real.log a) * l := by ring
      _ ≤ |a - b| := hba

/-! ## 2. Gaussian moments used as constants -/

/-- `∫ |z| dγ`. -/
noncomputable def gAbsMoment : ℝ := ∫ z : ℝ, |z| ∂(gaussianReal 0 1)

/-- `∫ |z| e^{a|z|} dγ`. -/
noncomputable def gAbsExpMoment (a : ℝ) : ℝ :=
  ∫ z : ℝ, |z| * Real.exp (a * |z|) ∂(gaussianReal 0 1)

theorem integrable_abs_stdGaussian : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
  integrable_id_stdGaussian.abs

theorem gAbsMoment_nonneg : 0 ≤ gAbsMoment :=
  integral_nonneg (fun z => abs_nonneg z)

/-- `|z| e^{a|z|} ≤ e^{(a+1)|z|}`, since `t ≤ e^t`. -/
theorem abs_mul_exp_le (a z : ℝ) :
    |z| * Real.exp (a * |z|) ≤ Real.exp ((a + 1) * |z|) := by
  have h : |z| ≤ Real.exp |z| := by
    have := Real.add_one_le_exp |z|
    linarith
  calc |z| * Real.exp (a * |z|) ≤ Real.exp |z| * Real.exp (a * |z|) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp ((a + 1) * |z|) := by rw [← Real.exp_add]; ring_nf

theorem integrable_abs_mul_exp_abs_stdGaussian (a : ℝ) :
    Integrable (fun z : ℝ => |z| * Real.exp (a * |z|)) (gaussianReal 0 1) := by
  refine Integrable.mono (integrable_exp_abs_mul_stdGaussian (a + 1)) ?_ ?_
  · exact (measurable_id.abs.mul
      (Real.continuous_exp.measurable.comp (measurable_id.abs.const_mul a))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg z) (Real.exp_pos _).le),
      abs_of_nonneg (Real.exp_pos _).le]
    exact abs_mul_exp_le a z

theorem gAbsExpMoment_nonneg (a : ℝ) : 0 ≤ gAbsExpMoment a :=
  integral_nonneg (fun z => mul_nonneg (abs_nonneg z) (Real.exp_pos _).le)

/-! ## 3. Integrability and a uniform lower bound for `∫ exp (m f)` -/

/-- A function dominated by `C|z|` is integrable against the Gaussian. -/
theorem integrable_of_abs_le_mul_abs {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ z, |f z| ≤ C * |z|) : Integrable f (gaussianReal 0 1) := by
  refine Integrable.mono (integrable_abs_stdGaussian.const_mul C) hfm.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (abs_nonneg z))]
  exact hf z

/-- Growth bound `|f z| ≤ C|z|` in the `HasLinearGrowth` packaging. -/
theorem hasLinearGrowth_of_abs_le_mul_abs {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hf : ∀ z, |f z| ≤ C * |z|) : HasLinearGrowth f :=
  ⟨0, C, le_rfl, hC, fun y => by simpa using hf y⟩

theorem integrable_exp_mul_of_abs_le_mul_abs {m C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf : ∀ z, |f z| ≤ C * |z|) :
    Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1) := by
  have h := integrable_exp_mul_of_hasLinearGrowth
    (A := f) (hasLinearGrowth_of_abs_le_mul_abs hC hf) hfm m 0 1
  simpa using h

/-- If `|f z| ≤ C |z|` then `exp (-(m C ∫|z|)) ≤ ∫ exp (m f) dγ`, by Jensen.

The bound involves only `m` and `C` — not `f` — which is what makes the comparison in §4
uniform over any family of functions sharing a growth bound. -/
theorem exp_le_integral_exp_mul_of_bound {m C : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ z, |f z| ≤ C * |z|) :
    Real.exp (-(m * C * gAbsMoment)) ≤ ∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1) := by
  have hfint : Integrable f (gaussianReal 0 1) := integrable_of_abs_le_mul_abs hC hfm hf
  have hexp : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1) :=
    integrable_exp_mul_of_abs_le_mul_abs hC hfm hf
  have hlogint : Integrable (fun z => Real.log (Real.exp (m * f z))) (gaussianReal 0 1) := by
    refine (hfint.const_mul m).congr ?_
    filter_upwards with z
    show m * f z = Real.log (Real.exp (m * f z))
    rw [Real.log_exp]
  have hJ := integral_log_le_log_integral (μ := gaussianReal 0 1)
    (W := fun z => Real.exp (m * f z)) (fun z => Real.exp_pos _) hexp hlogint
  have hLHS : (∫ z, Real.log (Real.exp (m * f z)) ∂(gaussianReal 0 1))
      = m * ∫ z, f z ∂(gaussianReal 0 1) := by
    have hfun : (fun z => Real.log (Real.exp (m * f z))) = fun z => m * f z := by
      funext z; rw [Real.log_exp]
    rw [hfun, integral_const_mul]
  rw [hLHS] at hJ
  -- `|∫ f| ≤ C ∫ |z|`
  have habs : |∫ z, f z ∂(gaussianReal 0 1)| ≤ C * gAbsMoment := by
    calc |∫ z, f z ∂(gaussianReal 0 1)| ≤ ∫ z, |f z| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, C * |z| ∂(gaussianReal 0 1) :=
          integral_mono hfint.abs (integrable_abs_stdGaussian.const_mul C) (fun z => hf z)
      _ = C * gAbsMoment := by rw [gAbsMoment, integral_const_mul]
  have hmean : -(C * gAbsMoment) ≤ ∫ z, f z ∂(gaussianReal 0 1) := (abs_le.1 habs).1
  have hpos : 0 < ∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1) := integral_exp_pos hexp
  rw [← Real.exp_log hpos]
  refine Real.exp_le_exp.2 ?_
  have hstep : -(m * C * gAbsMoment) ≤ m * ∫ z, f z ∂(gaussianReal 0 1) := by
    calc -(m * C * gAbsMoment) = m * -(C * gAbsMoment) := by ring
      _ ≤ m * ∫ z, f z ∂(gaussianReal 0 1) := mul_le_mul_of_nonneg_left hmean hm
  linarith

/-! ## 4. The comparison estimate -/

/--
**Comparison of two Gaussian log-exp integrals with nearby exponents.**

If `|f - g| ≤ c|z|` and both `|f|, |g| ≤ C|z|`, then

  `|log ∫ e^{mf} dγ - log ∫ e^{mg} dγ| ≤ 2 m c · gAbsExpMoment (mC) · exp (m C gAbsMoment)`.

The constant depends only on `m` and `C`, never on `f` and `g` themselves, so the estimate
is uniform over any family of functions obeying the same growth bound.  That uniformity is
the point: applied to `Ã_x(u) = A(x + u) - A(x)` it is uniform in `x`.
-/
theorem abs_log_integral_exp_sub_le {m c C : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (hC : 0 ≤ C)
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfg : ∀ z, |f z - g z| ≤ c * |z|)
    (hf : ∀ z, |f z| ≤ C * |z|) (hg : ∀ z, |g z| ≤ C * |z|) :
    |Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
      - Real.log (∫ z, Real.exp (m * g z) ∂(gaussianReal 0 1))|
      ≤ 2 * m * c * gAbsExpMoment (m * C) * Real.exp (m * C * gAbsMoment) := by
  have hexpf : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1) :=
    integrable_exp_mul_of_abs_le_mul_abs hC hfm hf
  have hexpg : Integrable (fun z => Real.exp (m * g z)) (gaussianReal 0 1) :=
    integrable_exp_mul_of_abs_le_mul_abs hC hgm hg
  have hIfpos : 0 < ∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1) := integral_exp_pos hexpf
  have hIgpos : 0 < ∫ z, Real.exp (m * g z) ∂(gaussianReal 0 1) := integral_exp_pos hexpg
  have hlpos : (0 : ℝ) < Real.exp (-(m * C * gAbsMoment)) := Real.exp_pos _
  have hlf := exp_le_integral_exp_mul_of_bound hm hC hfm hf
  have hlg := exp_le_integral_exp_mul_of_bound hm hC hgm hg
  -- the numerator bound
  have hnum : |(∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
      - ∫ z, Real.exp (m * g z) ∂(gaussianReal 0 1)| ≤ 2 * m * c * gAbsExpMoment (m * C) := by
    have hptw : ∀ z : ℝ, |Real.exp (m * f z) - Real.exp (m * g z)|
        ≤ (2 * m * c) * (|z| * Real.exp ((m * C) * |z|)) := by
      intro z
      have h1 := abs_exp_sub_exp_le (m * f z) (m * g z)
      have h2 : |m * f z - m * g z| ≤ m * (c * |z|) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left (hfg z) hm
      have hfb : m * f z ≤ (m * C) * |z| := by
        calc m * f z ≤ m * (C * |z|) := mul_le_mul_of_nonneg_left (abs_le.1 (hf z)).2 hm
          _ = (m * C) * |z| := by ring
      have hgb : m * g z ≤ (m * C) * |z| := by
        calc m * g z ≤ m * (C * |z|) := mul_le_mul_of_nonneg_left (abs_le.1 (hg z)).2 hm
          _ = (m * C) * |z| := by ring
      have h3 : Real.exp (m * f z) + Real.exp (m * g z) ≤ 2 * Real.exp ((m * C) * |z|) := by
        linarith [Real.exp_le_exp.2 hfb, Real.exp_le_exp.2 hgb]
      calc |Real.exp (m * f z) - Real.exp (m * g z)|
          ≤ |m * f z - m * g z| * (Real.exp (m * f z) + Real.exp (m * g z)) := h1
        _ ≤ (m * (c * |z|)) * (2 * Real.exp ((m * C) * |z|)) :=
            mul_le_mul h2 h3 (by positivity)
              (mul_nonneg hm (mul_nonneg hc (abs_nonneg z)))
        _ = (2 * m * c) * (|z| * Real.exp ((m * C) * |z|)) := by ring
    have hbdint : Integrable
        (fun z => (2 * m * c) * (|z| * Real.exp ((m * C) * |z|))) (gaussianReal 0 1) :=
      (integrable_abs_mul_exp_abs_stdGaussian (m * C)).const_mul _
    calc |(∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
            - ∫ z, Real.exp (m * g z) ∂(gaussianReal 0 1)|
        = |∫ z, (Real.exp (m * f z) - Real.exp (m * g z)) ∂(gaussianReal 0 1)| := by
          rw [integral_sub hexpf hexpg]
      _ ≤ ∫ z, |Real.exp (m * f z) - Real.exp (m * g z)| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (2 * m * c) * (|z| * Real.exp ((m * C) * |z|)) ∂(gaussianReal 0 1) :=
          integral_mono (hexpf.sub hexpg).abs hbdint hptw
      _ = 2 * m * c * gAbsExpMoment (m * C) := by
          rw [gAbsExpMoment, integral_const_mul]
  -- combine
  have hkey := abs_log_sub_log_le_of_pos hIfpos hIgpos hlpos hlf hlg
  have hfinal : |Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
      - Real.log (∫ z, Real.exp (m * g z) ∂(gaussianReal 0 1))|
      ≤ (2 * m * c * gAbsExpMoment (m * C)) / Real.exp (-(m * C * gAbsMoment)) := by
    rw [le_div_iff₀ hlpos]
    exact hkey.trans hnum
  refine hfinal.trans (le_of_eq ?_)
  rw [Real.exp_neg, div_eq_mul_inv, inv_inv]

end SpinGlass
