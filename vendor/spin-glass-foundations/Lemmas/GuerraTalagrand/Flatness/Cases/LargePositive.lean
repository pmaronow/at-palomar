module

public import Lemmas.GuerraTalagrand.Flatness.Cases.SmallPositive

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory NNReal

noncomputable section

namespace SpinGlass.AT

/-! ### Large positive overlaps `q < v ≤ 1` -/

private lemma flatness_largepos_log_cosh_nonneg
    (x : ℝ) :
    0 ≤ Real.log (Real.cosh x) := by
  exact Real.log_nonneg (Real.one_le_cosh x)

private lemma flatness_largepos_log_cosh_le_abs
    (x : ℝ) :
    Real.log (Real.cosh x) ≤ |x| := by
  have hcosh :
      Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    have h₁ :
        Real.exp x ≤ Real.exp |x| :=
      Real.exp_le_exp.mpr (le_abs_self x)
    have h₂ :
        Real.exp (-x) ≤ Real.exp |x| :=
      Real.exp_le_exp.mpr (neg_le_abs x)
    linarith
  exact
    (Real.log_le_iff_le_exp (Real.cosh_pos x)).2 hcosh

private lemma flatness_largepos_integrable_log_cosh_affine
    (h a m : ℝ) (v : ℝ≥0) :
    Integrable
      (fun z : ℝ => Real.log (Real.cosh (h + a * z)))
      (gaussianReal m v) := by
  have hz :
      Integrable
        (fun z : ℝ => |z|)
        (gaussianReal m v) :=
    (GTFrame.expMoments_gaussianReal m v).integrable_abs
  have hdom :
      Integrable
        (fun z : ℝ => |h| + |a| * |z|)
        (gaussianReal m v) :=
    (integrable_const |h|).add (hz.const_mul |a|)
  have hc :
      Continuous
        (fun z : ℝ => Real.log (Real.cosh (h + a * z))) := by
    have hcosh :
        Continuous
          (fun z : ℝ => Real.cosh (h + a * z)) := by
      fun_prop
    exact hcosh.log fun z => (Real.cosh_pos (h + a * z)).ne'
  refine hdom.mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with z
  have hbound :
      Real.log (Real.cosh (h + a * z)) ≤ |h| + |a| * |z| := by
    calc
      Real.log (Real.cosh (h + a * z)) ≤ |h + a * z| :=
        flatness_largepos_log_cosh_le_abs _
      _ ≤ |h| + |a * z| := abs_add_le _ _
      _ = |h| + |a| * |z| := by rw [abs_mul]
  have hright : 0 ≤ |h| + |a| * |z| := by positivity
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (flatness_largepos_log_cosh_nonneg (h + a * z)),
    abs_of_nonneg hright] using hbound

private lemma flatness_largepos_rank_one_half_terminal_zero
    (a b x : ℝ) :
    gtRankOneStep (1 / 2) a 1
        (gtDiagonalStep 1 b (gtTerminal 0)) x x =
      a ^ 2 + b ^ 2 + 2 * Real.log (Real.cosh x) := by
  have hterminal (z : ℝ) :
      gtDiagonalStep 1 b (gtTerminal 0)
          (x + a * z) (x + a * z) =
        b ^ 2 + 2 * Real.log (Real.cosh (x + a * z)) := by
    rw [gtDiagonalStep_one_terminal, gtTerminal_zero]
    ring
  rw [gtRankOneStep, if_neg (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  norm_num
  simp_rw [hterminal]
  have hexp (z : ℝ) :
      Real.exp ((b ^ 2 + 2 * Real.log (Real.cosh (x + a * z))) / 2) =
        Real.exp (b ^ 2 / 2) * Real.cosh (x + a * z) := by
    rw [show
      (b ^ 2 + 2 * Real.log (Real.cosh (x + a * z))) / 2 =
        b ^ 2 / 2 + Real.log (Real.cosh (x + a * z)) by ring,
      Real.exp_add, Real.exp_log (Real.cosh_pos _)]
  have hexp' (z : ℝ) :
      Real.exp (1 / 2 *
        (b ^ 2 + 2 * Real.log (Real.cosh (x + a * z)))) =
        Real.exp (b ^ 2 / 2) * Real.cosh (x + a * z) := by
    rw [show
      1 / 2 * (b ^ 2 + 2 * Real.log (Real.cosh (x + a * z))) =
        (b ^ 2 + 2 * Real.log (Real.cosh (x + a * z))) / 2 by ring,
      hexp]
  simp_rw [hexp']
  unfold standardGaussianExpectation
  rw [integral_const_mul]
  change
    2 * Real.log
      (Real.exp (b ^ 2 / 2) *
        standardGaussianExpectation (fun z => Real.cosh (x + a * z))) = _
  rw [standardGaussianExpectation_cosh_shift]
  rw [Real.log_mul (Real.exp_pos _).ne'
    (mul_ne_zero (Real.exp_pos _).ne' (Real.cosh_pos _).ne')]
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.cosh_pos _).ne']
  rw [Real.log_exp, Real.log_exp]
  ring

/-- Uniform quadratic gap on the upper positive-away region `q + ε < v ≤ 1`. -/
lemma gtFunctional_upper_positive_away_quadratic_gap
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c > 0, ∀ {β h q s v ε : ℝ},
      (β, h) ∈ K →
      q = rsQ β h →
      s ∈ Icc (0 : ℝ) 1 →
      0 < ε →
      q + ε < v →
      v ≤ 1 →
      ∃ lam ∈ Icc (-1 : ℝ) 1,
        gtFunctional β h q s lam v ≤
          2 * rsPathValue β h q s - c * ε ^ 2 := by
  obtain ⟨a, ha, haway⟩ :=
    flatness_deriv_gtFunctional_zero_upper_away data

  refine ⟨a ^ 2 / 5, by positivity, ?_⟩
  intro β h q s v ε hp hq hs hε hqεv hv1

  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp

  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp

  have hq0 : 0 ≤ q := by
    rw [hq]
    exact (rsQ_mem_Icc β h).1

  have hq1 : q ≤ 1 := by
    rw [hq]
    exact (rsQ_mem_Icc β h).2

  have hqpos : 0 < q := by
    rw [hq]
    exact rsQ_pos hβ hh

  have hq_lt_one : q < 1 := by
    rw [hq]
    exact rsQ_lt_one hβ hh

  have hv0 : 0 ≤ v := by
    linarith

  have hvpos : 0 < v := by
    linarith

  have hqv : q < v := by
    linarith

  have hvIcc : v ∈ Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith, hv1⟩

  have hvIcc01 : v ∈ Icc (0 : ℝ) 1 := by
    exact ⟨hv0, hv1⟩

  let F : ℝ → ℝ := fun l =>
    gtFunctional β h q s l v

  let d : ℝ := deriv F 0

  let lam : ℝ := -(2 / 5 : ℝ) * d

  have hgap : a * ε ≤ -d := by
    simpa [d, F] using
      haway hp hq hs hε hqεv hv1

  have hdneg : d < 0 := by
    have hae : 0 < a * ε := mul_pos ha hε
    linarith

  have hd : |d| ≤ 2 := by
    dsimp [d, F]
    exact
      abs_deriv_gtFunctional_le_two β h q s 0 v
        (by simpa [abs_le] using hvIcc)

  have hd_bounds : -2 ≤ d ∧ d ≤ 2 :=
    abs_le.mp hd

  have hlam : lam ∈ Icc (-1 : ℝ) 1 := by
    dsimp [lam]
    constructor <;>
      nlinarith [hd_bounds.1, hd_bounds.2]

  have ht :=
    flatness_gtFunctional_taylor_upper
      β h q s v lam

  change
    F lam ≤
      F 0 + d * lam + (5 / 4 : ℝ) * lam ^ 2
    at ht

  have hopt :
      d * lam + (5 / 4 : ℝ) * lam ^ 2 =
        -(d ^ 2) / 5 := by
    dsimp [lam]
    ring

  have ht' :
      F lam ≤ F 0 - d ^ 2 / 5 := by
    nlinarith [ht, hopt]

  have hsq :
      a ^ 2 * ε ^ 2 ≤ d ^ 2 := by
    have hmul :=
      mul_self_le_mul_self
        (mul_nonneg ha.le hε.le)
        hgap
    calc
      a ^ 2 * ε ^ 2
          = (a * ε) * (a * ε) := by
              ring
      _ ≤ (-d) * (-d) := hmul
      _ = d ^ 2 := by
              ring

  have hzero0 :
      gtFunctional β h q s 0 v =
        2 * rsPathValue β h q s := by
    exact flatness_gtFunctional_zero_eq_two_rsPathValue_large_positive
      β h q s v ⟨hqpos, hq_lt_one⟩ hs ⟨hqv.le, hv1⟩

  have hzero :
      F 0 = 2 * rsPathValue β h q s := by
    simpa [F] using hzero0

  refine ⟨lam, hlam, ?_⟩

  change F lam ≤
    2 * rsPathValue β h q s -
      (a ^ 2 / 5) * ε ^ 2

  nlinarith [ht', hsq]

end SpinGlass.AT
