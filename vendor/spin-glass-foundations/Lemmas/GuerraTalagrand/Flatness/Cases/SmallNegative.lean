module

public import Lemmas.GuerraTalagrand.Flatness.Core

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory NNReal

noncomputable section

namespace SpinGlass.AT

/-! ### Small negative overlaps `-q ≤ v ≤ 0` -/

private lemma flatness_smallneg_log_cosh_nonneg
    (x : ℝ) :
    0 ≤ Real.log (Real.cosh x) := by
  exact Real.log_nonneg (Real.one_le_cosh x)

private lemma flatness_smallneg_log_cosh_le_abs
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

private lemma flatness_smallneg_integrable_log_cosh_affine
    (h a m : ℝ) (v : ℝ≥0) :
    Integrable
      (fun z : ℝ =>
        Real.log (Real.cosh (h + a * z)))
      (gaussianReal m v) := by
  have hz :
      Integrable
        (fun z : ℝ => |z|)
        (gaussianReal m v) :=
    (GTFrame.expMoments_gaussianReal m v).integrable_abs

  have hdom :
      Integrable
        (fun z : ℝ =>
          |h| + |a| * |z|)
        (gaussianReal m v) :=
    (integrable_const |h|).add
      (hz.const_mul |a|)

  have hc :
      Continuous
        (fun z : ℝ =>
          Real.log (Real.cosh (h + a * z))) := by
    have hcosh :
        Continuous
          (fun z : ℝ =>
            Real.cosh (h + a * z)) := by
      fun_prop
    exact
      hcosh.log
        (fun z =>
          (Real.cosh_pos (h + a * z)).ne')

  refine hdom.mono' hc.aestronglyMeasurable ?_

  filter_upwards [] with z

  have hbound :
      Real.log (Real.cosh (h + a * z))
        ≤ |h| + |a| * |z| := by
    calc
      Real.log (Real.cosh (h + a * z))
          ≤ |h + a * z| :=
        flatness_smallneg_log_cosh_le_abs _
      _ ≤ |h| + |a * z| :=
        abs_add_le _ _
      _ = |h| + |a| * |z| := by
        rw [abs_mul]

  have hright :
      0 ≤ |h| + |a| * |z| := by
    positivity

  simpa [
      Real.norm_eq_abs,
      abs_of_nonneg
        (flatness_smallneg_log_cosh_nonneg
          (h + a * z)),
      abs_of_nonneg hright
    ] using hbound

private lemma flatness_smallneg_integrable_log_cosh_two_affine
    (h a b : ℝ) :
    Integrable
      (fun p : ℝ × ℝ =>
        Real.log
          (Real.cosh
            (h + a * p.1 + b * p.2)))
      ((gaussianReal 0 1).prod
        (gaussianReal 0 1)) := by
  have hz :
      Integrable
        (fun z : ℝ => |z|)
        (gaussianReal 0 1) :=
    (GTFrame.expMoments_gaussianReal 0 1).integrable_abs

  have hz₁ :
      Integrable
        (fun p : ℝ × ℝ => |p.1|)
        ((gaussianReal 0 1).prod
          (gaussianReal 0 1)) :=
    hz.comp_fst (gaussianReal 0 1)

  have hz₂ :
      Integrable
        (fun p : ℝ × ℝ => |p.2|)
        ((gaussianReal 0 1).prod
          (gaussianReal 0 1)) :=
    hz.comp_snd (gaussianReal 0 1)

  have hdom :
      Integrable
        (fun p : ℝ × ℝ =>
          (|h| + |a| * |p.1|) +
            |b| * |p.2|)
        ((gaussianReal 0 1).prod
          (gaussianReal 0 1)) :=
    ((integrable_const |h|).add
      (hz₁.const_mul |a|)).add
        (hz₂.const_mul |b|)

  have hc :
      Continuous
        (fun p : ℝ × ℝ =>
          Real.log
            (Real.cosh
              (h + a * p.1 + b * p.2))) := by
    have hcosh :
        Continuous
          (fun p : ℝ × ℝ =>
            Real.cosh
              (h + a * p.1 + b * p.2)) := by
      fun_prop
    exact
      hcosh.log
        (fun p =>
          (Real.cosh_pos
            (h + a * p.1 + b * p.2)).ne')

  refine hdom.mono' hc.aestronglyMeasurable ?_

  filter_upwards [] with p

  have hbound :
      Real.log
          (Real.cosh
            (h + a * p.1 + b * p.2))
        ≤
      (|h| + |a| * |p.1|) +
        |b| * |p.2| := by
    calc
      Real.log
          (Real.cosh
            (h + a * p.1 + b * p.2))
          ≤ |h + a * p.1 + b * p.2| :=
        flatness_smallneg_log_cosh_le_abs _
      _ ≤ |h + a * p.1| + |b * p.2| :=
        abs_add_le _ _
      _ ≤ (|h| + |a * p.1|) + |b * p.2| := by
        gcongr
        exact abs_add_le _ _
      _ =
          (|h| + |a| * |p.1|) +
            |b| * |p.2| := by
        rw [abs_mul, abs_mul]

  have hright :
      0 ≤
        (|h| + |a| * |p.1|) +
          |b| * |p.2| := by
    positivity

  simpa [
      Real.norm_eq_abs,
      abs_of_nonneg
        (flatness_smallneg_log_cosh_nonneg
          (h + a * p.1 + b * p.2)),
      abs_of_nonneg hright
    ] using hbound

private lemma flatness_smallneg_gaussian_convolution_log_cosh_add_const
    (h k a b c : ℝ)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    standardGaussianExpectation (fun x =>
      standardGaussianExpectation (fun y =>
        Real.log
            (Real.cosh
              (h + a * x + b * y)) + k))
      =
    standardGaussianExpectation (fun z =>
      Real.log
          (Real.cosh (h + c * z)) + k) := by
  let va : ℝ≥0 :=
    NNReal.mk (a ^ 2) (sq_nonneg a) * 1

  let vb : ℝ≥0 :=
    NNReal.mk (b ^ 2) (sq_nonneg b) * 1

  let vc : ℝ≥0 :=
    NNReal.mk (c ^ 2) (sq_nonneg c) * 1

  have hma :
      Measure.map (fun x : ℝ => a * x)
          (gaussianReal 0 1) =
        gaussianReal 0 va := by
    simpa [va] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : ℝ≥0)) a)

  have hmb :
      Measure.map (fun x : ℝ => b * x)
          (gaussianReal 0 1) =
        gaussianReal 0 vb := by
    simpa [vb] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : ℝ≥0)) b)

  have hmc :
      Measure.map (fun x : ℝ => c * x)
          (gaussianReal 0 1) =
        gaussianReal 0 vc := by
    simpa [vc] using
      (gaussianReal_map_const_mul
        (μ := 0) (v := (1 : ℝ≥0)) c)

  have hv :
      va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]

  have hf :
      Integrable
        (fun z : ℝ =>
          Real.log (Real.cosh (h + z)) + k)
        (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [
      gaussianReal_conv_gaussianReal,
      hv,
      zero_add
    ]

    simpa using
      (flatness_smallneg_integrable_log_cosh_affine
        h 1 0 vc).add
        (integrable_const k)

  have hprod :
      Integrable
        (fun p : ℝ × ℝ =>
          Real.log
              (Real.cosh
                (h + (p.1 + p.2))) + k)
        ((gaussianReal 0 va).prod
          (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hf
    exact
      (integrable_map_measure
        hf.1 (by fun_prop)).mp hf

  have houter :
      AEStronglyMeasurable
        (fun x : ℝ =>
          ∫ y,
            Real.log
                (Real.cosh
                  (h + (x + y))) + k
            ∂gaussianReal 0 vb)
        (gaussianReal 0 va) :=
    hprod.integral_prod_left.1

  have hinner (x : ℝ) :
      (∫ y,
          Real.log
              (Real.cosh
                (h + a * x + b * y)) + k
        ∂gaussianReal 0 1)
        =
      ∫ y,
        Real.log
            (Real.cosh
              (h + a * x + y)) + k
        ∂gaussianReal 0 vb := by
    have hc' :
        Continuous
          (fun y : ℝ =>
            Real.log
              (Real.cosh
                (h + a * x + y)) + k) := by
      have hcosh :
          Continuous
            (fun y : ℝ =>
              Real.cosh
                (h + a * x + y)) := by
        fun_prop
      exact
        (hcosh.log
          (fun y =>
            (Real.cosh_pos
              (h + a * x + y)).ne')).add
          continuous_const

    have hm :
        AEStronglyMeasurable
          (fun y : ℝ =>
            Real.log
              (Real.cosh
                (h + a * x + y)) + k)
          (Measure.map
            (fun y : ℝ => b * y)
            (gaussianReal 0 1)) :=
      hc'.aestronglyMeasurable

    rw [← hmb,
      integral_map (by fun_prop) hm]

  have houter_map :
      (∫ x,
          ∫ y,
            Real.log
                (Real.cosh
                  (h + a * x + y)) + k
            ∂gaussianReal 0 vb
        ∂gaussianReal 0 1)
        =
      ∫ x,
        ∫ y,
          Real.log
              (Real.cosh
                (h + x + y)) + k
          ∂gaussianReal 0 vb
        ∂gaussianReal 0 va := by
    have hm :
        AEStronglyMeasurable
          (fun x : ℝ =>
            ∫ y,
              Real.log
                  (Real.cosh
                    (h + (x + y))) + k
              ∂gaussianReal 0 vb)
          (Measure.map
            (fun x : ℝ => a * x)
            (gaussianReal 0 1)) := by
      simpa [hma] using houter

    rw [← hma]

    simpa only [add_assoc] using
      (integral_map (by fun_prop) hm).symm

  unfold standardGaussianExpectation

  calc
    (∫ x,
        ∫ y,
          Real.log
              (Real.cosh
                (h + a * x + b * y)) + k
          ∂gaussianReal 0 1
      ∂gaussianReal 0 1)
        =
      ∫ x,
        ∫ y,
          Real.log
              (Real.cosh
                (h + x + y)) + k
          ∂gaussianReal 0 vb
        ∂gaussianReal 0 va := by
          rw [
            integral_congr_ae
              (Filter.Eventually.of_forall hinner)
          ]
          exact houter_map

    _ =
      ∫ z,
        Real.log
            (Real.cosh (h + z)) + k
        ∂(gaussianReal 0 va ∗
          gaussianReal 0 vb) := by
          simpa only [add_assoc] using
            (integral_conv hf).symm

    _ =
      ∫ z,
        Real.log
            (Real.cosh (h + z)) + k
        ∂gaussianReal 0 vc := by
          rw [
            gaussianReal_conv_gaussianReal,
            hv,
            zero_add
          ]

    _ =
      ∫ z,
        Real.log
            (Real.cosh (h + c * z)) + k
        ∂gaussianReal 0 1 := by
          rw [
            ← hmc,
            integral_map (by fun_prop)
          ]

          have hcosh :
              Continuous
                (fun z : ℝ =>
                  Real.cosh (h + z)) := by
            fun_prop

          exact
            ((hcosh.log
              (fun z =>
                (Real.cosh_pos
                  (h + z)).ne')).add
              continuous_const).aestronglyMeasurable

/-- Extracts the numerical derivative from a supplied derivative formula for
the negative-overlap correlation. -/
lemma flatnessTildeGDeriv_eq_deriv
    (β h s v D : ℝ)
    (hD :
      HasDerivAt
        (fun u => flatnessTildeG β h (rsQ β h) s u)
        D v) :
    deriv
        (fun u => flatnessTildeG β h (rsQ β h) s u) v = D := by
  exact hD.deriv

/-- On `-q ≤ v < 0`, the endpoint multiplier derivative is
`flatnessTildeG β h q s v - v`. -/
lemma flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg_of_mem_Ico
    (β h q s v : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ico (-q) 0) :
    deriv (fun lam => gtFunctional β h q s lam v) 0 =
      flatnessTildeG β h q s v - v := by
  by_cases hvleft : v = -q
  · subst v
    have habs : |(-q : ℝ)| = q := by
      rw [abs_neg, abs_of_pos hq.1]
    have hqabs : q ≤ |(-q : ℝ)| := by
      rw [habs]
    have habs1 : |(-q : ℝ)| < 1 := by
      rw [habs]
      exact hq.2
    rw [flatness_deriv_gtFunctional_zero_q_le_abs_v_lt_one
      β h q s (-q) hq.1 hqabs habs1]
    apply congrArg (fun y : ℝ => y - (-q))
    unfold flatnessTildeG
    rw [habs]
    have hzero : gtIncrementScale β s q q = 0 := by
      simp [gtIncrementScale]
    rw [hzero]
    simp [standardGaussianExpectation]
  · have hvneg : v < 0 := hv.2
    have hvne : v ≠ 0 := ne_of_lt hvneg
    have hv0 : 0 < |v| := by
      exact abs_pos.mpr hvne
    have hminusqv : -q < v := by
      exact lt_of_le_of_ne hv.1 (Ne.symm hvleft)
    have hvq : |v| < q := by
      rw [abs_of_neg hvneg]
      linarith
    simpa [flatnessTildeG] using
      (flatness_deriv_gtFunctional_zero_abs_v_lt_q
        β h q s v hv0 hvq)

/-- Canonical form of the small-negative-overlap derivative formula. -/
lemma flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg_rsQ
    (β h s v : ℝ)
    (hβ : 0 < β) (hh : 0 < h)
    (hv : v ∈ Set.Ico (-(rsQ β h)) 0) :
    deriv
        (fun lam =>
          gtFunctional β h (rsQ β h) s lam v) 0 =
      flatnessTildeG β h (rsQ β h) s v - v := by
  exact
    flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg_of_mem_Ico
      β h (rsQ β h) s v
      ⟨rsQ_pos hβ hh, rsQ_lt_one hβ hh⟩
      hv

/-- On `-q ≤ v ≤ 0`, the endpoint multiplier derivative is
`flatnessTildeG β h q s v - v`. -/
lemma flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg
    (β h q s v : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (_hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (-q) 0) :
    deriv (fun lam => gtFunctional β h q s lam v) 0 =
      flatnessTildeG β h q s v - v := by
  by_cases hvzero : v = 0
  · subst v
    rw [flatness_deriv_gtFunctional_zero_abs_v_eq_zero β h q s 0 hq.1 abs_zero]
    simp [flatnessTildeG, gtIncrementScale, standardGaussianExpectation]
  by_cases hvleft : v = -q
  · subst v
    have habs : |(-q : ℝ)| = q := by
      rw [abs_neg, abs_of_pos hq.1]
    have hqabs : q ≤ |(-q : ℝ)| := by
      rw [habs]
    have habs1 : |(-q : ℝ)| < 1 := by
      rw [habs]
      exact hq.2
    rw [flatness_deriv_gtFunctional_zero_q_le_abs_v_lt_one
      β h q s (-q) hq.1 hqabs habs1]
    apply congrArg (fun y : ℝ => y - (-q))
    unfold flatnessTildeG
    rw [habs]
    have hzero : gtIncrementScale β s q q = 0 := by
      simp [gtIncrementScale]
    rw [hzero]
    simp [standardGaussianExpectation]
  · have hvneg : v < 0 := lt_of_le_of_ne hv.2 hvzero
    have hvne : v ≠ 0 := ne_of_lt hvneg
    have hv0 : 0 < |v| := abs_pos.mpr hvne
    have hminusqv : -q < v := lt_of_le_of_ne hv.1 (Ne.symm hvleft)
    have hvq : |v| < q := by
      rw [abs_of_neg hvneg]
      linarith
    simpa [flatnessTildeG] using
      (flatness_deriv_gtFunctional_zero_abs_v_lt_q
        β h q s v hv0 hvq)

/-- At the boundary `v = 0`, `flatnessTildeG` is the multiplier derivative
of the GT functional. -/
lemma flatnessTildeG_zero_eq_deriv_gtFunctional_zero
    (β h q s : ℝ)
    (hq : 0 < q) :
    flatnessTildeG β h q s 0 =
      deriv
        (fun lam => gtFunctional β h q s lam 0) 0 := by
  rw [flatness_deriv_gtFunctional_zero_abs_v_eq_zero
    β h q s 0 hq abs_zero]
  simp [flatnessTildeG, gtIncrementScale, standardGaussianExpectation]

/-- Uniform linear separation of the endpoint multiplier derivative from zero
on the negative-overlap branch. -/
lemma flatness_deriv_gtFunctional_zero_negative_global_separation
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {β h q s v : ℝ},
        (β, h) ∈ K →
        q = rsQ β h →
        s ∈ Icc (0 : ℝ) 1 →
        v ∈ Icc (-q) 0 →
        c * |v - q| ≤
          |deriv (fun lam =>
            gtFunctional β h q s lam v) 0| := by
  obtain ⟨c₀, hc₀, hsep⟩ := scalarOrderParameterCorrect_global_separation data
  refine ⟨min c₀ data.gap, lt_min hc₀ data.gap_pos, ?_⟩
  intro β h q s v hp hq hs hv
  subst q
  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp
  have hqpos : 0 < rsQ β h := rsQ_pos hβ hh
  let f : ℝ → ℝ := fun u => flatnessTildeG β h (rsQ β h) s u
  have hf0 : f 0 = scalarOrderParameterCorrect β h s 0 := by
    dsimp [f]
    rw [flatnessTildeG_zero_eq_deriv_gtFunctional_zero β h (rsQ β h) s hqpos,
      flatness_deriv_gtFunctional_zero_eq_g_sub β h s 0 hβ hh hs
        ⟨le_rfl, zero_le_one⟩]
    ring
  have hzero : 0 < f 0 := by
    rw [hf0]
    simpa using
      (scalarOrderParameterCorrect_sign data hp hs).1 0 ⟨le_rfl, hqpos⟩
  have hbase : c₀ * rsQ β h ≤ f 0 := by
    have hseparation := hsep hp hs (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by
      exact ⟨le_rfl, zero_le_one⟩)
    rw [← hf0, sub_zero, abs_of_pos hzero] at hseparation
    have habs : |(0 : ℝ) - rsQ β h| = rsQ β h := by
      rw [abs_of_neg (by linarith : 0 - rsQ β h < 0)]
      ring
    rwa [habs] at hseparation
  by_cases hv0 : v = 0
  · subst v
    rw [flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg β h (rsQ β h) s 0
      ⟨hqpos, rsQ_lt_one hβ hh⟩ hs ⟨by linarith, le_rfl⟩]
    change min c₀ data.gap * |0 - rsQ β h| ≤ |f 0 - 0|
    rw [sub_zero, abs_of_pos hzero]
    have hmin : min c₀ data.gap ≤ c₀ := min_le_left _ _
    calc
      min c₀ data.gap * |0 - rsQ β h| = min c₀ data.gap * rsQ β h := by
        rw [abs_of_neg (by linarith : 0 - rsQ β h < 0)]
        ring
      _ ≤ c₀ * rsQ β h :=
        mul_le_mul_of_nonneg_right hmin hqpos.le
      _ ≤ f 0 := hbase
  · have hvneg : v < 0 := lt_of_le_of_ne hv.2 hv0
    have hcont : ContinuousOn f (Icc v 0) := by
      apply (flatnessTildeG_continuousOn_neg β h (rsQ β h) s).mono
      intro u hu
      exact ⟨le_trans hv.1 hu.1, hu.2⟩
    have hdiff : DifferentiableOn ℝ f (Ioo v 0) := by
      intro u hu
      obtain ⟨D, hD⟩ := flatnessTildeG_hasDerivAt_neg β h (rsQ β h) s u
        hβ.le hs hqpos ⟨lt_of_le_of_lt hv.1 hu.1, hu.2⟩
      exact hD.differentiableAt.differentiableWithinAt
    obtain ⟨u, hu, hslope⟩ := exists_deriv_eq_slope f hvneg hcont hdiff
    have hderiv := flatnessTildeG_deriv_lt_one_neg data hp rfl hs
      ⟨lt_of_le_of_lt hv.1 hu.1, hu.2⟩
    have hratio : (f 0 - f v) / (0 - v) ≤ 1 - data.gap := by
      rwa [← hslope]
    have hden : 0 < 0 - v := by linarith
    have hstep := (div_le_iff₀ hden).mp hratio
    have hmain : min c₀ data.gap * (rsQ β h - v) ≤ f v - v := by
      have hmin₀ : min c₀ data.gap ≤ c₀ := min_le_left _ _
      have hminGap : min c₀ data.gap ≤ data.gap := min_le_right _ _
      have hqnonneg : 0 ≤ rsQ β h := hqpos.le
      nlinarith
    rw [flatness_deriv_gtFunctional_zero_eq_tildeG_sub_neg β h (rsQ β h) s v
      ⟨hqpos, rsQ_lt_one hβ hh⟩ hs hv]
    have hmain0 : 0 ≤ f v - v := by
      apply le_trans ?_ hmain
      exact mul_nonneg (le_of_lt (lt_min hc₀ data.gap_pos))
        (by linarith : 0 ≤ rsQ β h - v)
    rw [abs_of_nonneg hmain0]
    calc
      min c₀ data.gap * |v - rsQ β h| =
          min c₀ data.gap * (rsQ β h - v) := by
        rw [abs_of_nonpos (by linarith : v - rsQ β h ≤ 0)]
        ring
      _ ≤ f v - v := hmain

private lemma flatness_smallneg_incrementScale_sq
    {β s lower upper : ℝ}
    (hs : 0 ≤ s)
    (hlu : lower ≤ upper) :
    gtIncrementScale β s lower upper ^ 2 =
      s * β ^ 2 * (upper - lower) := by
  unfold gtIncrementScale
  rw [
    mul_pow,
    mul_pow,
    Real.sq_sqrt hs,
    Real.sq_sqrt (sub_nonneg.mpr hlu)
  ]
  ring

private lemma flatness_smallneg_diagonal_zero_zero
    (F : GTTwoField) (x₁ x₂ : ℝ) :
    gtDiagonalStep 0 0 F x₁ x₂ =
      F x₁ x₂ := by
  simp [
    gtDiagonalStep,
    standardGaussianExpectation
  ]

private lemma flatness_smallneg_rankOne_half_zero
    (sign : ℝ)
    (F : GTTwoField)
    (x₁ x₂ : ℝ) :
    gtRankOneStep (1 / 2) 0 sign F x₁ x₂ =
      F x₁ x₂ := by
  simp [
    gtRankOneStep,
    standardGaussianExpectation
  ]

private lemma flatness_smallneg_diagonal_zero_split
    (a b x₁ x₂ : ℝ) :
    gtDiagonalStep 0 a
        (gtDiagonalStep 1 b (gtTerminal 0))
        x₁ x₂
      =
    standardGaussianExpectation
        (fun z =>
          Real.log (Real.cosh (x₁ + a * z)))
      +
    standardGaussianExpectation
        (fun z =>
          Real.log (Real.cosh (x₂ + a * z)))
      +
    b ^ 2 := by
  have hu :
      gtDiagonalStep 1 b (gtTerminal 0) =
        fun y₁ y₂ =>
          Real.log (Real.cosh y₁) +
            Real.log (Real.cosh y₂) +
            b ^ 2 := by
    funext y₁ y₂
    rw [
      gtDiagonalStep_one_terminal,
      gtTerminal_zero
    ]

  rw [hu]
  simp only [
    gtDiagonalStep,
    if_pos rfl
  ]
  unfold standardGaussianExpectation

  have h₁ :
      Integrable
        (fun z : ℝ =>
          Real.log (Real.cosh (x₁ + a * z)))
        (gaussianReal 0 1) :=
    flatness_smallneg_integrable_log_cosh_affine
      x₁ a 0 1

  have h₂ :
      Integrable
        (fun z : ℝ =>
          Real.log (Real.cosh (x₂ + a * z)))
        (gaussianReal 0 1) :=
    flatness_smallneg_integrable_log_cosh_affine
      x₂ a 0 1

  have hinner (z₁ : ℝ) :
      (∫ z₂,
          (Real.log
              (Real.cosh (x₁ + a * z₁)) +
            Real.log
              (Real.cosh (x₂ + a * z₂))) +
            b ^ 2
        ∂gaussianReal 0 1)
        =
      Real.log
          (Real.cosh (x₁ + a * z₁))
        +
      (∫ z₂,
          Real.log
            (Real.cosh (x₂ + a * z₂))
        ∂gaussianReal 0 1)
        +
      b ^ 2 := by
    calc
      (∫ z₂,
          (Real.log
              (Real.cosh (x₁ + a * z₁)) +
            Real.log
              (Real.cosh (x₂ + a * z₂))) +
            b ^ 2
        ∂gaussianReal 0 1)
          =
        (∫ z₂,
          Real.log
              (Real.cosh (x₁ + a * z₁)) +
            Real.log
              (Real.cosh (x₂ + a * z₂))
          ∂gaussianReal 0 1) + b ^ 2 := by
            calc
              (∫ z₂,
                  (Real.log
                      (Real.cosh (x₁ + a * z₁)) +
                    Real.log
                      (Real.cosh (x₂ + a * z₂))) + b ^ 2
                ∂gaussianReal 0 1)
                  =
                (∫ z₂,
                    Real.log
                      (Real.cosh (x₁ + a * z₁)) +
                    Real.log
                      (Real.cosh (x₂ + a * z₂))
                  ∂gaussianReal 0 1) +
                  ∫ _ : ℝ, b ^ 2 ∂gaussianReal 0 1 :=
                    integral_add
                      ((integrable_const _).add h₂)
                      (integrable_const _)
              _ =
                (∫ z₂,
                    Real.log
                      (Real.cosh (x₁ + a * z₁)) +
                    Real.log
                      (Real.cosh (x₂ + a * z₂))
                  ∂gaussianReal 0 1) + b ^ 2 := by
                    simp
      _ =
        Real.log
            (Real.cosh (x₁ + a * z₁)) +
          (∫ z₂,
            Real.log
              (Real.cosh (x₂ + a * z₂))
            ∂gaussianReal 0 1) + b ^ 2 := by
            calc
              (∫ z₂,
                  Real.log
                    (Real.cosh (x₁ + a * z₁)) +
                  Real.log
                    (Real.cosh (x₂ + a * z₂))
                ∂gaussianReal 0 1) + b ^ 2
                  =
                (∫ _ : ℝ,
                    Real.log
                      (Real.cosh (x₁ + a * z₁))
                  ∂gaussianReal 0 1) +
                  ∫ z₂,
                    Real.log
                      (Real.cosh (x₂ + a * z₂))
                    ∂gaussianReal 0 1 + b ^ 2 :=
                    congrArg (fun value : ℝ => value + b ^ 2)
                      (integral_add
                        (integrable_const _)
                        h₂)
              _ =
                Real.log
                    (Real.cosh (x₁ + a * z₁)) +
                  ∫ z₂,
                    Real.log
                      (Real.cosh (x₂ + a * z₂))
                    ∂gaussianReal 0 1 + b ^ 2 := by
                    simp

  rw [
    integral_congr_ae
      (Filter.Eventually.of_forall hinner)
  ]

  let C : ℝ :=
    (∫ z₂,
        Real.log
          (Real.cosh (x₂ + a * z₂))
      ∂gaussianReal 0 1)

  have hfun :
      (fun z₁ : ℝ =>
        Real.log
            (Real.cosh (x₁ + a * z₁)) +
          (∫ z₂,
            Real.log
              (Real.cosh (x₂ + a * z₂))
            ∂gaussianReal 0 1) +
          b ^ 2)
        =
      fun z₁ =>
        Real.log
            (Real.cosh (x₁ + a * z₁)) +
          (C + b ^ 2) := by
    funext z₁
    dsimp [C]
    ring

  rw [hfun]
  rw [
    integral_add
      h₁
      (integrable_const (C + b ^ 2))
  ]
  simp only [
    integral_const,
    probReal_univ,
    one_smul
  ]
  dsimp [C]
  ring

private lemma flatness_smallneg_zero_steps_value
    (r a b c y : ℝ)
    (hc : c ^ 2 = r ^ 2 + a ^ 2) :
    gtRankOneStep 0 r (-1)
        (gtDiagonalStep 0 a
          (gtDiagonalStep 1 b
            (gtTerminal 0)))
        y y
      =
    2 * standardGaussianExpectation
        (fun z =>
          Real.log
            (Real.cosh (y + c * z)))
      + b ^ 2 := by
  let A : ℝ → ℝ := fun z =>
    standardGaussianExpectation (fun w =>
      Real.log
        (Real.cosh
          (y + r * z + a * w)))
  let B : ℝ → ℝ := fun z =>
    standardGaussianExpectation (fun w =>
      Real.log
        (Real.cosh
          (y + (-r) * z + a * w)))

  have hAprod :=
    flatness_smallneg_integrable_log_cosh_two_affine
      y r a
  have hBprod :=
    flatness_smallneg_integrable_log_cosh_two_affine
      y (-r) a

  have hAint :
      Integrable A (gaussianReal 0 1) := by
    have h := hAprod.integral_prod_left
    simpa [A, standardGaussianExpectation] using h
  have hBint :
      Integrable B (gaussianReal 0 1) := by
    have h := hBprod.integral_prod_left
    simpa [B, standardGaussianExpectation] using h

  have hconvA :
      standardGaussianExpectation A =
        standardGaussianExpectation
          (fun z =>
            Real.log
              (Real.cosh (y + c * z))) := by
    simpa [A] using
      flatness_smallneg_gaussian_convolution_log_cosh_add_const
        y 0 r a c hc

  have hcB :
      c ^ 2 = (-r) ^ 2 + a ^ 2 := by
    nlinarith [hc]

  have hconvB :
      standardGaussianExpectation B =
        standardGaussianExpectation
          (fun z =>
            Real.log
              (Real.cosh (y + c * z))) := by
    simpa [B] using
      flatness_smallneg_gaussian_convolution_log_cosh_add_const
        y 0 (-r) a c hcB

  calc
    gtRankOneStep 0 r (-1)
        (gtDiagonalStep 0 a
          (gtDiagonalStep 1 b
            (gtTerminal 0)))
        y y
      =
      standardGaussianExpectation
        (fun z => A z + B z + b ^ 2) := by
          simp only [gtRankOneStep, if_pos rfl]
          apply congrArg standardGaussianExpectation
          funext z
          have h :=
            flatness_smallneg_diagonal_zero_split
              a b
              (y + r * z)
              (y + (-1) * r * z)
          simpa [A, B] using h
    _ =
      2 * standardGaussianExpectation
          (fun z =>
            Real.log
              (Real.cosh (y + c * z)))
        + b ^ 2 := by
          unfold standardGaussianExpectation at hconvA hconvB ⊢
          change
            (∫ z, (A z + B z) + b ^ 2
              ∂gaussianReal 0 1) =
              2 * ∫ z,
                Real.log (Real.cosh (y + c * z))
                ∂gaussianReal 0 1 + b ^ 2
          calc
            (∫ z, (A z + B z) + b ^ 2
              ∂gaussianReal 0 1)
                =
              (∫ z, A z + B z
                ∂gaussianReal 0 1) +
                ∫ _ : ℝ, b ^ 2 ∂gaussianReal 0 1 :=
                  integral_add
                    (hAint.add hBint)
                    (integrable_const _)
            _ =
              (∫ z, A z ∂gaussianReal 0 1) +
                (∫ z, B z ∂gaussianReal 0 1) + b ^ 2 := by
                  rw [integral_add hAint hBint]
                  simp
            _ =
              2 * ∫ z,
                Real.log (Real.cosh (y + c * z))
                ∂gaussianReal 0 1 + b ^ 2 := by
                  rw [hconvA, hconvB]
                  ring

private lemma flatness_smallpos_zero_steps_value
    (r a b c y : ℝ)
    (hc : c ^ 2 = r ^ 2 + a ^ 2) :
    gtRankOneStep 0 r 1
        (gtDiagonalStep 0 a
          (gtDiagonalStep 1 b
            (gtTerminal 0)))
        y y
      =
    2 * standardGaussianExpectation
        (fun z =>
          Real.log
            (Real.cosh (y + c * z)))
      + b ^ 2 := by
  let A : ℝ → ℝ := fun z =>
    standardGaussianExpectation (fun w =>
      Real.log
        (Real.cosh
          (y + r * z + a * w)))

  have hAprod :=
    flatness_smallneg_integrable_log_cosh_two_affine
      y r a

  have hAint :
      Integrable A (gaussianReal 0 1) := by
    have h := hAprod.integral_prod_left
    simpa [A, standardGaussianExpectation] using h

  have hconvA :
      standardGaussianExpectation A =
        standardGaussianExpectation
          (fun z =>
            Real.log
              (Real.cosh (y + c * z))) := by
    simpa [A] using
      flatness_smallneg_gaussian_convolution_log_cosh_add_const
        y 0 r a c hc

  calc
    gtRankOneStep 0 r 1
        (gtDiagonalStep 0 a
          (gtDiagonalStep 1 b
            (gtTerminal 0)))
        y y
      =
      standardGaussianExpectation
        (fun z => 2 * A z + b ^ 2) := by
          simp only [gtRankOneStep, if_pos rfl]
          apply congrArg standardGaussianExpectation
          funext z
          have h :=
            flatness_smallneg_diagonal_zero_split
              a b
              (y + r * z)
              (y + r * z)
          simpa [A, two_mul] using h
    _ =
      2 * standardGaussianExpectation
          (fun z =>
            Real.log
              (Real.cosh (y + c * z)))
        + b ^ 2 := by
          unfold standardGaussianExpectation at hconvA ⊢
          change
            (∫ z, 2 * A z + b ^ 2
              ∂gaussianReal 0 1) =
              2 * ∫ z,
                Real.log (Real.cosh (y + c * z))
                ∂gaussianReal 0 1 + b ^ 2
          rw [integral_add (hAint.const_mul 2) (integrable_const _)]
          rw [integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          rw [hconvA]

private lemma flatness_smallneg_scalarTrialValue_eq_rsPathValue
    (β h q s : ℝ)
    (hq : 0 < q)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    scalarTrialValue β h q s =
      rsPathValue β h q s := by
  let a : ℝ :=
    β * Real.sqrt ((1 - s) * q)
  let b : ℝ :=
    β * Real.sqrt (s * q)
  let c : ℝ :=
    β * Real.sqrt q
  let k : ℝ :=
    s * β ^ 2 / 2 * (1 - q)

  have hs0 : 0 ≤ s := hs.1
  have h1s :
      0 ≤ 1 - s :=
    sub_nonneg.mpr hs.2
  have hsq :
      c ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [a, b, c]
    rw [
      mul_pow,
      Real.sq_sqrt hq.le,
      mul_pow,
      Real.sq_sqrt
        (mul_nonneg h1s hq.le),
      mul_pow,
      Real.sq_sqrt
        (mul_nonneg hs0 hq.le)
    ]
    ring

  have hconv :=
    flatness_smallneg_gaussian_convolution_log_cosh_add_const
      h k a b c hsq
  have hinner_split (z : ℝ) :
      standardGaussianExpectation (fun w =>
        Real.log
          (Real.cosh (h + a * z + b * w)) + k)
        =
      standardGaussianExpectation (fun w =>
        Real.log
          (Real.cosh (h + a * z + b * w))) + k := by
    unfold standardGaussianExpectation
    rw [
      integral_add
        (flatness_smallneg_integrable_log_cosh_affine
          (h + a * z) b 0 1)
        (integrable_const k)
    ]
    simp
  have hlog :
      Integrable
        (fun z : ℝ =>
          Real.log
            (Real.cosh (h + c * z)))
        (gaussianReal 0 1) :=
    flatness_smallneg_integrable_log_cosh_affine
      h c 0 1
  have hsplit :
      standardGaussianExpectation (fun z =>
        Real.log
            (Real.cosh (h + c * z)) + k)
        =
      standardGaussianExpectation (fun z =>
        Real.log
          (Real.cosh (h + c * z))) + k := by
    unfold standardGaussianExpectation
    rw [
      integral_add
        hlog
        (integrable_const k)
    ]
    simp only [
      integral_const,
      probReal_univ,
      one_smul
    ]

  unfold scalarTrialValue
  unfold scalarPsi
  unfold rsPathValue
  have hqmax₁ :
      max (q - 0) 0 = q := by
    simp [hq.le]
  have hqmax₂ :
      max (0 : ℝ) q = q := by
    exact max_eq_right hq.le
  have hqmax₃ :
      max q 0 = q := by
    exact max_eq_left hq.le
  simp only [
    sub_zero,
    hqmax₁,
    hqmax₂,
    hqmax₃
  ]
  have hconv' :
      standardGaussianExpectation (fun z =>
        standardGaussianExpectation (fun w =>
          Real.log
            (Real.cosh
              (h + a * z + b * w))) + k)
        =
      standardGaussianExpectation (fun z =>
        Real.log
            (Real.cosh (h + c * z)) + k) := by
    calc
      standardGaussianExpectation (fun z =>
        standardGaussianExpectation (fun w =>
          Real.log
            (Real.cosh (h + a * z + b * w))) + k)
          =
        standardGaussianExpectation (fun z =>
          standardGaussianExpectation (fun w =>
            Real.log
              (Real.cosh (h + a * z + b * w)) + k)) := by
              apply congrArg standardGaussianExpectation
              funext z
              exact (hinner_split z).symm
      _ =
        standardGaussianExpectation (fun z =>
          Real.log
              (Real.cosh (h + c * z)) + k) := hconv
  change
    (Real.log 2 +
        standardGaussianExpectation (fun z =>
          standardGaussianExpectation (fun w =>
            Real.log
              (Real.cosh (h + a * z + b * w))) + k) -
        s * β ^ 2 / 4 * (1 - q ^ 2)) =
      (Real.log 2 +
        standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (h + c * z)))) +
        s * β ^ 2 / 4 * (1 - q) ^ 2
  rw [hconv', hsplit]
  dsimp [a, b, c, k]
  ring

private lemma flatness_smallneg_semigroup_zero_eq_two_scalarPsi
    (β q s v y : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Ico (-q) 0) :
    gtSemigroupSolution β q s 0 v 0 y y =
      2 * scalarPsi β q s 0 y := by
  have hvneg : v < 0 := hv.2
  have hsign : gtPathSign v = -1 := by
    simp [gtPathSign, not_le.mpr hvneg]
  let c : ℝ := β * Real.sqrt (s * q)
  let b : ℝ := gtIncrementScale β s q 1
  have hb2 : b ^ 2 = s * β ^ 2 * (1 - q) := by
    dsimp [b]
    exact flatness_smallneg_incrementScale_sq hs.1 hq.2.le
  have hscalar :
      2 * scalarPsi β q s 0 y =
        2 * standardGaussianExpectation
          (fun z => Real.log (Real.cosh (y + c * z))) + b ^ 2 := by
    unfold scalarPsi
    have hmax₁ : max (q - 0) 0 = q := by simp [hq.1.le]
    have hmax₂ : max (0 : ℝ) q = q := max_eq_right hq.1.le
    rw [hmax₁, hmax₂]
    dsimp [c]
    rw [hb2]
    ring
  by_cases hvleft : v = -q
  · subst v
    let r : ℝ := gtIncrementScale β s 0 q
    have hr2 : r ^ 2 = s * β ^ 2 * q := by
      dsimp [r]
      simpa using flatness_smallneg_incrementScale_sq
        (β := β) (s := s) (lower := 0) (upper := q) hs.1 hq.1.le
    have hc2 : c ^ 2 = s * β ^ 2 * q := by
      dsimp [c]
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.1 hq.1.le)]
      ring
    have hcr : c ^ 2 = r ^ 2 + 0 ^ 2 := by rw [hc2, hr2]; ring
    have hzero := flatness_smallneg_zero_steps_value r 0 b c y hcr
    have hzero' :
        gtRankOneStep 0 r (-1)
            (gtDiagonalStep 1 b (gtTerminal 0)) y y =
          2 * standardGaussianExpectation
              (fun z => Real.log (Real.cosh (y + c * z))) + b ^ 2 := by
      have hdiag :
          gtDiagonalStep 0 0 (gtDiagonalStep 1 b (gtTerminal 0)) =
            gtDiagonalStep 1 b (gtTerminal 0) := by
        funext x₁ x₂
        exact flatness_smallneg_diagonal_zero_zero _ _ _
      rw [hdiag] at hzero
      exact hzero
    have hsem :
        gtSemigroupSolution β q s 0 (-q) 0 y y =
          gtRankOneStep 0 r (-1)
            (gtDiagonalStep 1 b (gtTerminal 0)) y y := by
      have habs : |(-q : ℝ)| = q := by rw [abs_neg, abs_of_pos hq.1]
      have hqnot : ¬ q ≤ 0 := not_le.mpr hq.1
      have hnegq : gtPathSign (-q) = -1 := hsign
      simp [gtSemigroupSolution, habs, hnegq, not_le.mpr hq.1,
        r, b, gtIncrementScale]
      have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [hhalf]
      have hzero_rank (scale : ℝ) :
          gtRankOneStep (1 / 2) 0 (-1)
              (gtDiagonalStep 1 scale (gtTerminal 0)) =
            gtDiagonalStep 1 scale (gtTerminal 0) := by
        funext x₁ x₂
        exact flatness_smallneg_rankOne_half_zero _ _ _ _
      rw [hzero_rank]
    rw [hsem, hzero', ← hscalar]
  · let r : ℝ := |v|
    have hr : r = -v := by dsimp [r]; rw [abs_of_neg hvneg]
    have hrpos : 0 < r := by rw [hr]; linarith
    have hrv : r < q := by
      rw [hr]
      have hleft : -q < v := lt_of_le_of_ne hv.1 (Ne.symm hvleft)
      linarith
    let r₀ : ℝ := gtIncrementScale β s 0 r
    let a : ℝ := gtIncrementScale β s r q
    have hr₀2 : r₀ ^ 2 = s * β ^ 2 * r := by
      dsimp [r₀]
      simpa using flatness_smallneg_incrementScale_sq
        (β := β) (s := s) (lower := 0) (upper := r) hs.1 hrpos.le
    have ha2 : a ^ 2 = s * β ^ 2 * (q - r) := by
      dsimp [a]
      exact flatness_smallneg_incrementScale_sq hs.1 hrv.le
    have hc2 : c ^ 2 = s * β ^ 2 * q := by
      dsimp [c]
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.1 hq.1.le)]
      ring
    have hcra : c ^ 2 = r₀ ^ 2 + a ^ 2 := by rw [hc2, hr₀2, ha2]; ring
    have hzero := flatness_smallneg_zero_steps_value r₀ a b c y hcra
    have hsem :
        gtSemigroupSolution β q s 0 v 0 y y =
          gtRankOneStep 0 r₀ (-1)
            (gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal 0))) y y := by
      have hqr : ¬ q ≤ r := not_le.mpr hrv
      have hr0 : ¬ r ≤ (0 : ℝ) := not_le.mpr hrpos
      have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq.1
      simp [gtSemigroupSolution, r, hqr, hr0, hq0, hsign, r₀, a, b]
    rw [hsem, hzero, ← hscalar]

lemma flatness_gtFunctional_zero_eq_two_rsPathValue_small_negative
    (β h q s v : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Ico (-q) 0) :
    gtFunctional β h q s 0 v =
      2 * rsPathValue β h q s := by
  have hU (y : ℝ) :
      gtSemigroupSolution β q s 0 v 0 y y =
        2 * scalarPsi β q s 0 y :=
    flatness_smallneg_semigroup_zero_eq_two_scalarPsi β q s v y hq hs hv
  have hE :
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) =
        2 * standardGaussianExpectation (fun z =>
          scalarPsi β q s 0
            (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    calc
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) =
        standardGaussianExpectation (fun z =>
          2 * scalarPsi β q s 0
            (h + β * Real.sqrt ((1 - s) * q) * z)) := by
              apply congrArg standardGaussianExpectation
              funext z
              exact hU _
      _ = 2 * standardGaussianExpectation (fun z =>
        scalarPsi β q s 0
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
            unfold standardGaussianExpectation
            rw [integral_const_mul]
  have htrial := flatness_smallneg_scalarTrialValue_eq_rsPathValue β h q s hq.1 hs
  calc
    gtFunctional β h q s 0 v = 2 * scalarTrialValue β h q s := by
      rw [gtFunctional]
      simp only [zero_mul, sub_zero]
      rw [hE]
      unfold scalarTrialValue gtCorrection
      ring
    _ = 2 * rsPathValue β h q s := by rw [htrial]

private lemma flatness_smallpos_semigroup_zero_eq_two_scalarPsi
    (β q s v y : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
  (hv : v ∈ Icc 0 q) :
    gtSemigroupSolution β q s 0 v 0 y y =
      2 * scalarPsi β q s 0 y := by
  have hsign : gtPathSign v = 1 := by
    simp [gtPathSign, hv.1]
  let c : ℝ := β * Real.sqrt (s * q)
  let b : ℝ := gtIncrementScale β s q 1
  have hb2 : b ^ 2 = s * β ^ 2 * (1 - q) := by
    dsimp [b]
    exact flatness_smallneg_incrementScale_sq hs.1 hq.2.le
  have hscalar :
      2 * scalarPsi β q s 0 y =
        2 * standardGaussianExpectation
          (fun z => Real.log (Real.cosh (y + c * z))) + b ^ 2 := by
    unfold scalarPsi
    have hmax₁ : max (q - 0) 0 = q := by simp [hq.1.le]
    have hmax₂ : max (0 : ℝ) q = q := max_eq_right hq.1.le
    rw [hmax₁, hmax₂]
    dsimp [c]
    rw [hb2]
    ring
  by_cases hvzero : v = 0
  · subst v
    let a : ℝ := gtIncrementScale β s 0 q
    have ha2 : a ^ 2 = s * β ^ 2 * q := by
      dsimp [a]
      simpa using flatness_smallneg_incrementScale_sq
        (β := β) (s := s) (lower := 0) (upper := q) hs.1 hq.1.le
    have hc2 : c ^ 2 = s * β ^ 2 * q := by
      dsimp [c]
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.1 hq.1.le)]
      ring
    have hca : c ^ 2 = 0 ^ 2 + a ^ 2 := by rw [hc2, ha2]; ring
    have hzero := flatness_smallpos_zero_steps_value 0 a b c y hca
    have hzero' :
        gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal 0)) y y =
          2 * standardGaussianExpectation
              (fun z => Real.log (Real.cosh (y + c * z))) + b ^ 2 := by
      simpa [gtRankOneStep, standardGaussianExpectation] using hzero
    have hsem :
        gtSemigroupSolution β q s 0 0 0 y y =
          gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal 0)) y y := by
      have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq.1
      simp [gtSemigroupSolution, hq0, a, b]
    rw [hsem, hzero', ← hscalar]
  · by_cases hvright : v = q
    · subst v
      let r : ℝ := gtIncrementScale β s 0 q
      have hr2 : r ^ 2 = s * β ^ 2 * q := by
        dsimp [r]
        simpa using flatness_smallneg_incrementScale_sq
          (β := β) (s := s) (lower := 0) (upper := q) hs.1 hq.1.le
      have hc2 : c ^ 2 = s * β ^ 2 * q := by
        dsimp [c]
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.1 hq.1.le)]
        ring
      have hcr : c ^ 2 = r ^ 2 + 0 ^ 2 := by rw [hc2, hr2]; ring
      have hzero := flatness_smallpos_zero_steps_value r 0 b c y hcr
      have hzero' :
          gtRankOneStep 0 r 1
              (gtDiagonalStep 1 b (gtTerminal 0)) y y =
            2 * standardGaussianExpectation
                (fun z => Real.log (Real.cosh (y + c * z))) + b ^ 2 := by
        have hdiag :
            gtDiagonalStep 0 0 (gtDiagonalStep 1 b (gtTerminal 0)) =
              gtDiagonalStep 1 b (gtTerminal 0) := by
          funext x₁ x₂
          exact flatness_smallneg_diagonal_zero_zero _ _ _
        rw [hdiag] at hzero
        exact hzero
      have hsem :
          gtSemigroupSolution β q s 0 q 0 y y =
            gtRankOneStep 0 r 1
              (gtDiagonalStep 1 b (gtTerminal 0)) y y := by
        have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq.1
        have hsignq : gtPathSign q = 1 := by
          simp [gtPathSign, hq.1.le]
        simp [gtSemigroupSolution, abs_of_pos hq.1, hsignq, hq0,
          r, b, gtIncrementScale]
        have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [hhalf]
        have hzero_rank (scale : ℝ) :
            gtRankOneStep (1 / 2) 0 1
                (gtDiagonalStep 1 scale (gtTerminal 0)) =
              gtDiagonalStep 1 scale (gtTerminal 0) := by
          funext x₁ x₂
          exact flatness_smallneg_rankOne_half_zero _ _ _ _
        rw [hzero_rank]
      rw [hsem, hzero', ← hscalar]
    · let r : ℝ := v
      have hrpos : 0 < r := by
        dsimp [r]
        exact lt_of_le_of_ne hv.1 (Ne.symm hvzero)
      have hrv : r < q := by
        dsimp [r]
        exact lt_of_le_of_ne hv.2 hvright
      let r₀ : ℝ := gtIncrementScale β s 0 r
      let a : ℝ := gtIncrementScale β s r q
      have hr₀2 : r₀ ^ 2 = s * β ^ 2 * r := by
        dsimp [r₀]
        simpa using flatness_smallneg_incrementScale_sq
          (β := β) (s := s) (lower := 0) (upper := r) hs.1 hrpos.le
      have ha2 : a ^ 2 = s * β ^ 2 * (q - r) := by
        dsimp [a]
        exact flatness_smallneg_incrementScale_sq hs.1 hrv.le
      have hc2 : c ^ 2 = s * β ^ 2 * q := by
        dsimp [c]
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hs.1 hq.1.le)]
        ring
      have hcra : c ^ 2 = r₀ ^ 2 + a ^ 2 := by rw [hc2, hr₀2, ha2]; ring
      have hzero := flatness_smallpos_zero_steps_value r₀ a b c y hcra
      have hsem :
          gtSemigroupSolution β q s 0 v 0 y y =
            gtRankOneStep 0 r₀ 1
              (gtDiagonalStep 0 a (gtDiagonalStep 1 b (gtTerminal 0))) y y := by
        have hqr : ¬ q ≤ r := not_le.mpr hrv
        have hr0 : ¬ r ≤ (0 : ℝ) := not_le.mpr hrpos
        have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq.1
        simp [gtSemigroupSolution, r, abs_of_nonneg hv.1, hqr, hr0, hq0,
          hsign, r₀, a, b]
      rw [hsem, hzero, ← hscalar]

lemma flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
    (β h q s v : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc 0 q) :
    gtFunctional β h q s 0 v =
      2 * rsPathValue β h q s := by
  have hU (y : ℝ) :
      gtSemigroupSolution β q s 0 v 0 y y =
        2 * scalarPsi β q s 0 y :=
    flatness_smallpos_semigroup_zero_eq_two_scalarPsi β q s v y hq hs hv
  have hE :
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) =
        2 * standardGaussianExpectation (fun z =>
          scalarPsi β q s 0
            (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    calc
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) =
        standardGaussianExpectation (fun z =>
          2 * scalarPsi β q s 0
            (h + β * Real.sqrt ((1 - s) * q) * z)) := by
              apply congrArg standardGaussianExpectation
              funext z
              exact hU _
      _ = 2 * standardGaussianExpectation (fun z =>
        scalarPsi β q s 0
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
            unfold standardGaussianExpectation
            rw [integral_const_mul]
  have htrial := flatness_smallneg_scalarTrialValue_eq_rsPathValue β h q s hq.1 hs
  calc
    gtFunctional β h q s 0 v = 2 * scalarTrialValue β h q s := by
      rw [gtFunctional]
      simp only [zero_mul, sub_zero]
      rw [hE]
      unfold scalarTrialValue gtCorrection
      ring
    _ = 2 * rsPathValue β h q s := by rw [htrial]

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

lemma flatness_gtFunctional_zero_eq_two_rsPathValue_large_positive
    (β h q s v : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc q 1) :
    gtFunctional β h q s 0 v =
      2 * rsPathValue β h q s := by
  let r : ℝ := gtIncrementScale β s 0 q
  let a : ℝ := gtIncrementScale β s q v
  let b : ℝ := gtIncrementScale β s v 1
  let d : ℝ := β * Real.sqrt ((1 - s) * q)
  let c : ℝ := β * Real.sqrt q
  have hr2 : r ^ 2 = s * β ^ 2 * q := by
    dsimp [r]
    simpa using flatness_smallneg_incrementScale_sq
      (β := β) (s := s) (lower := 0) (upper := q) hs.1 hq.1.le
  have ha2 : a ^ 2 = s * β ^ 2 * (v - q) := by
    dsimp [a]
    exact flatness_smallneg_incrementScale_sq hs.1 hv.1
  have hb2 : b ^ 2 = s * β ^ 2 * (1 - v) := by
    dsimp [b]
    exact flatness_smallneg_incrementScale_sq hs.1 hv.2
  have hab : a ^ 2 + b ^ 2 = s * β ^ 2 * (1 - q) := by
    rw [ha2, hb2]
    ring
  have hdc : c ^ 2 = d ^ 2 + r ^ 2 := by
    dsimp [c, d]
    rw [mul_pow, Real.sq_sqrt hq.1.le,
      mul_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hs.2) hq.1.le), hr2]
    ring
  let A : ℝ → ℝ := fun z =>
    standardGaussianExpectation (fun w =>
      Real.log (Real.cosh (h + d * z + r * w)))
  have hAprod :=
    flatness_smallneg_integrable_log_cosh_two_affine h d r
  have hAint : Integrable A (gaussianReal 0 1) := by
    have h := hAprod.integral_prod_left
    simpa [A, standardGaussianExpectation] using h
  have hconvA :
      standardGaussianExpectation A =
        standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (h + c * z))) := by
    simpa [A] using
      flatness_smallneg_gaussian_convolution_log_cosh_add_const
        h 0 d r c hdc
  have houter :
      standardGaussianExpectation (fun z => 2 * A z + a ^ 2 + b ^ 2) =
        2 * standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (h + c * z))) + a ^ 2 + b ^ 2 := by
    have hfun :
        (fun z => 2 * A z + a ^ 2 + b ^ 2) =
          fun z => 2 * A z + (a ^ 2 + b ^ 2) := by
      funext z
      ring
    rw [hfun]
    unfold standardGaussianExpectation at hconvA ⊢
    rw [integral_add (hAint.const_mul 2) (integrable_const _)]
    rw [integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    rw [hconvA]
    ring
  have hsem (y : ℝ) :
      gtSemigroupSolution β q s 0 v 0 y y =
        2 * standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (y + r * z))) + a ^ 2 + b ^ 2 := by
    have hsign : gtPathSign v = 1 := by
      simp [gtPathSign, le_trans hq.1.le hv.1]
    have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq.1
    have hvpos : 0 < v := lt_of_lt_of_le hq.1 hv.1
    have hqv : q ≤ |v| := by
      rw [abs_of_nonneg (le_trans hq.1.le hv.1)]
      exact hv.1
    have hform :
        gtSemigroupSolution β q s 0 v 0 y y =
          gtRankOneStep 0 r 1
            (gtRankOneStep (1 / 2) a 1
              (gtDiagonalStep 1 b (gtTerminal 0))) y y := by
      simp [gtSemigroupSolution,
        abs_of_nonneg (le_trans hq.1.le hv.1), hsign, hv.1,
        not_le.mpr hvpos, hq0, r, a, b]
    rw [hform, gtRankOneStep]
    simp only [if_true, one_mul]
    calc
      standardGaussianExpectation (fun z =>
        gtRankOneStep (1 / 2) a 1
          (gtDiagonalStep 1 b (gtTerminal 0))
          (y + r * z) (y + r * z)) =
        standardGaussianExpectation (fun z =>
          a ^ 2 + b ^ 2 +
            2 * Real.log (Real.cosh (y + r * z))) := by
              apply congrArg standardGaussianExpectation
              funext z
              rw [flatness_largepos_rank_one_half_terminal_zero]
      _ =
        2 * standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (y + r * z))) + a ^ 2 + b ^ 2 := by
          have hlog :
              Integrable (fun z : ℝ =>
                Real.log (Real.cosh (y + r * z)))
                (gaussianReal 0 1) :=
            flatness_smallneg_integrable_log_cosh_affine y r 0 1
          unfold standardGaussianExpectation
          rw [integral_add (integrable_const _) (hlog.const_mul 2)]
          rw [integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          ring
  have hE :
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + d * z) (h + d * z)) =
        2 * standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (h + c * z))) + a ^ 2 + b ^ 2 := by
    calc
      standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s 0 v 0
          (h + d * z) (h + d * z)) =
        standardGaussianExpectation (fun z => 2 * A z + a ^ 2 + b ^ 2) := by
          apply congrArg standardGaussianExpectation
          funext z
          simpa [A] using hsem (h + d * z)
      _ = 2 * standardGaussianExpectation (fun z =>
          Real.log (Real.cosh (h + c * z))) + a ^ 2 + b ^ 2 := houter
  rw [gtFunctional, show
    (fun z => gtSemigroupSolution β q s 0 v 0
      (h + β * Real.sqrt ((1 - s) * q) * z)
      (h + β * Real.sqrt ((1 - s) * q) * z)) =
      fun z => gtSemigroupSolution β q s 0 v 0 (h + d * z) (h + d * z) by
        funext z
        rfl]
  rw [hE]
  unfold rsPathValue gtCorrection
  dsimp [c] at hE ⊢
  nlinarith [hab]

lemma flatness_gtFunctional_quadratic_gap_small_negative
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c > 0, ∀ {β h q s v : ℝ},
      (β, h) ∈ K → q = rsQ β h → s ∈ Icc (0 : ℝ) 1 →
      v ∈ Ico (-q) 0 → ∃ lam ∈ Icc (-1 : ℝ) 1,
        gtFunctional β h q s lam v ≤
          2 * rsPathValue β h q s - c * (v - q) ^ 2 := by
  obtain ⟨a, ha, hsep⟩ :=
    flatness_deriv_gtFunctional_zero_negative_global_separation data
  let c : ℝ := a ^ 2 / 5
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro β h q s v hp hq hs hv
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hqIoo : q ∈ Ioo (0 : ℝ) 1 := by
    rw [hq]
    exact ⟨rsQ_pos hβ hh, rsQ_lt_one hβ hh⟩
  have hvIcc : v ∈ Icc (-q) 0 := ⟨hv.1, hv.2.le⟩
  have hvOverlap : v ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2, hqIoo.2]
  have hvabs : |v| ≤ 1 := by rw [abs_le]; exact hvOverlap
  let d : ℝ := deriv (fun lam => gtFunctional β h q s lam v) 0
  have hdLower : a * |v - q| ≤ |d| := by
    dsimp [d]
    exact hsep hp hq hs hvIcc
  have hdTwo : |d| ≤ 2 := by
    dsimp [d]
    exact abs_deriv_gtFunctional_le_two β h q s 0 v hvabs
  have hdUpper : |d| ≤ (5 / 2 : ℝ) := hdTwo.trans (by norm_num)
  have hzero : gtFunctional β h q s 0 v = 2 * rsPathValue β h q s :=
    flatness_gtFunctional_zero_eq_two_rsPathValue_small_negative β h q s v hqIoo hs hv
  let H : ℝ → ℝ := fun lam =>
    gtFunctional β h q s lam v - 2 * rsPathValue β h q s
  have hHzero : H 0 ≤ 0 := by dsimp [H]; rw [hzero]; linarith
  have hTaylor : ∀ lam, |lam| ≤ 1 →
      H lam ≤ H 0 + d * lam + (5 / 2 : ℝ) / 2 * lam ^ 2 := by
    intro lam hlam
    have ht := flatness_gtFunctional_taylor_upper β h q s v lam
    dsimp [H, d]
    have hcoeff : (5 / 2 : ℝ) / 2 = 5 / 4 := by norm_num
    rw [hcoeff]
    linarith
  obtain ⟨lam, hlam, hloss⟩ :=
    gt_taylor_quadratic_loss H d (5 / 2 : ℝ) a (v - q)
      (by norm_num) ha hHzero hTaylor hdUpper hdLower
  have hlamIcc : lam ∈ Icc (-1 : ℝ) 1 := by rw [abs_le] at hlam; exact hlam
  refine ⟨lam, hlamIcc, ?_⟩
  have hcoeff : a ^ 2 / (2 * (5 / 2 : ℝ)) = c := by dsimp [c]; ring
  rw [hcoeff] at hloss
  dsimp [H] at hloss
  linarith

lemma flatness_gtFunctional_lt_two_rsPathValue_small_negative
    {K : Set (ℝ × ℝ)} (data : UniformATData K)
    {β h q s v : ℝ} (hp : (β, h) ∈ K) (hq : q = rsQ β h)
    (hs : s ∈ Icc (0 : ℝ) 1) (hv : v ∈ Ico (-q) 0) :
    ∃ lam ∈ Icc (-1 : ℝ) 1,
      gtFunctional β h q s lam v < 2 * rsPathValue β h q s := by
  obtain ⟨c, hc, hgap⟩ := flatness_gtFunctional_quadratic_gap_small_negative data
  obtain ⟨lam, hlam, hbound⟩ := hgap hp hq hs hv
  refine ⟨lam, hlam, ?_⟩
  have hβ : 0 < β := by simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by simpa using data.h_pos (β, h) hp
  have hqpos : 0 < q := by rw [hq]; exact rsQ_pos hβ hh
  have hne : v - q ≠ 0 := by linarith [hv.2, hqpos]
  have hdist : 0 < (v - q) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hne
  have hloss : 0 < c * (v - q) ^ 2 := mul_pos hc hdist
  linarith

end SpinGlass.AT
