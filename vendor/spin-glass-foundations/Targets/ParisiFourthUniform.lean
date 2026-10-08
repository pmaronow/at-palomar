module

public import Targets.ParisiThirdUniform

@[expose] public section

/-!
# Depth-independent fourth spatial derivatives of the actual Parisi recursion

The fourth exponential derivative polynomial is preserved at a fixed mass.
Its change under decreasing masses costs at most 42 times their decrement,
using the already proved uniform third-derivative bound. These decrements
telescope. All scalar formulas include zero variance and zero mass.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The fourth derivative of an exponential divided by its mass and value. -/
def parisiFourthPolynomial (p q z w m : ℝ) : ℝ :=
  w + 4 * m * p * z + 3 * m * q ^ 2 + 6 * m ^ 2 * p ^ 2 * q + m ^ 3 * p ^ 4

private theorem fourth_correction_bound {p q z m B : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hz : |z| ≤ B) (hm : m ∈ Set.Icc 0 1) :
    |4 * m * p * z + 3 * m * q ^ 2 + 6 * m ^ 2 * p ^ 2 * q + m ^ 3 * p ^ 4| ≤
      4 * B + 10 := by
  have hB : 0 ≤ B := (abs_nonneg z).trans hz
  have hm0 : 0 ≤ m := hm.1
  have hpz : |p| * |z| ≤ B := by nlinarith [mul_le_mul_of_nonneg_right hp (abs_nonneg z)]
  have hq2 : |q| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg q) hq
  have hp2 : |p| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg p) hp
  have hp2q : |p| ^ 2 * |q| ≤ 1 := mul_le_one₀ hp2 (abs_nonneg q) hq
  have hp4 : |p| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg p) hp
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm.1 hm.2
  have hm3 : m ^ 3 ≤ 1 := pow_le_one₀ hm.1 hm.2
  have H1 := abs_add_le (4 * m * p * z) (3 * m * q ^ 2)
  have H2 := abs_add_le (4 * m * p * z + 3 * m * q ^ 2) (6 * m ^ 2 * p ^ 2 * q)
  have H3 := abs_add_le (4 * m * p * z + 3 * m * q ^ 2 + 6 * m ^ 2 * p ^ 2 * q)
    (m ^ 3 * p ^ 4)
  norm_num only [abs_mul, abs_pow, abs_of_nonneg hm.1] at H1 H2 H3
  nlinarith [mul_le_mul_of_nonneg_left hpz (show 0 ≤ 4 * m by positivity),
    mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 3 * m by positivity),
    mul_le_mul_of_nonneg_left hp2q (show 0 ≤ 6 * m ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hp4 (show 0 ≤ m ^ 3 by positivity),
    mul_le_mul_of_nonneg_right hm.2 hB]

theorem abs_parisiFourthPolynomial_le {p q z w m B C : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hz : |z| ≤ B) (hw : |w| ≤ C)
    (hm : m ∈ Set.Icc 0 1) : |parisiFourthPolynomial p q z w m| ≤ C + 4 * B + 10 := by
  have H := abs_add_le w
    (4 * m * p * z + 3 * m * q ^ 2 + 6 * m ^ 2 * p ^ 2 * q + m ^ 3 * p ^ 4)
  have he : parisiFourthPolynomial p q z w m =
      w + (4 * m * p * z + 3 * m * q ^ 2 + 6 * m ^ 2 * p ^ 2 * q + m ^ 3 * p ^ 4) := by
    unfold parisiFourthPolynomial
    ring
  rw [he]
  linarith [fourth_correction_bound hp hq hz hm]

/-- Endpoint-safe candidate for the fourth spatial derivative of one step. -/
noncomputable def stepD4Uniform (A A' A'' A''' A'''' : ℝ → ℝ) (m v x : ℝ) : ℝ :=
  scalarTiltMean A (fun y => parisiFourthPolynomial (A' y) (A'' y) (A''' y) (A'''' y) m)
    m v x -
    (4 * m * stepD1 A A' m v x * stepD3Uniform A A' A'' A''' m v x +
      3 * m * (stepD2 A A' A'' m v x) ^ 2 +
      6 * m ^ 2 * (stepD1 A A' m v x) ^ 2 * stepD2 A A' A'' m v x +
      m ^ 3 * (stepD1 A A' m v x) ^ 4)

/-- The fourth Bell-polynomial identity is the genuine spatial derivative of
the endpoint-safe third derivative. No positive-variance hypothesis is needed. -/
theorem hasDerivAt_stepD3Uniform {A A' A'' A''' A'''' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'') (hA'''m : Measurable A''') (hA''''m : Measurable A'''')
    (hA'''d : ∀ x, HasDerivAt A'' (A''' x) x)
    (hA''''d : ∀ x, HasDerivAt A''' (A'''' x) x)
    (hA'''b : ∀ x, |A''' x| ≤ B) (hA''''b : ∀ x, |A'''' x| ≤ C)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    HasDerivAt (stepD3Uniform A A' A'' A''' m v)
      (stepD4Uniform A A' A'' A''' A'''' m v x) x := by
  have hAm : Measurable A := (continuous_iff_continuousAt.mpr
    fun y => (hC2.1 y).continuousAt).measurable
  have hA'm : Measurable A' := (continuous_iff_continuousAt.mpr
    fun y => (hC2.2.1 y).continuousAt).measurable
  let G := fun y => parisiThirdPolynomial (A' y) (A'' y) (A''' y) m
  let G' := fun y => A'''' y + 3 * m * (A'' y ^ 2 + A' y * A''' y) +
    3 * m ^ 2 * A' y ^ 2 * A'' y
  have hGd (y : ℝ) : HasDerivAt G (G' y) y := by
    convert! ((hA''''d y).add (((hC2.2.1 y).mul (hA'''d y)).const_mul (3 * m))).add
      (((hC2.2.1 y).pow 3).const_mul (m ^ 2)) using 1
    · funext z
      dsimp [G, parisiThirdPolynomial]
      ring
    · dsimp only [G']
      ring
  have hGb (y : ℝ) : |G y| ≤ B + 4 :=
    abs_parisiThirdPolynomial_le (hC2.abs_first_le_one y) (hC2.abs_second_le_one y)
      (hA'''b y) hm
  have hG'b (y : ℝ) : |G' y| ≤ C + 3 * B + 6 := by
    have hm0 : 0 ≤ m := hm.1
    have hB : 0 ≤ B := (abs_nonneg _).trans (hA'''b y)
    have hpp : |A' y| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hC2.abs_first_le_one y)
    have hqq : |A'' y| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hC2.abs_second_le_one y)
    have hpz : |A' y| * |A''' y| ≤ B := by
      nlinarith [mul_le_mul_of_nonneg_right (hC2.abs_first_le_one y) (abs_nonneg (A''' y)), hA'''b y]
    have hppq : |A' y| ^ 2 * |A'' y| ≤ 1 :=
      mul_le_one₀ hpp (abs_nonneg _) (hC2.abs_second_le_one y)
    have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm.1 hm.2
    have H1 := abs_add_le (A'' y ^ 2) (A' y * A''' y)
    have H2 := abs_add_le (A'''' y) (3 * m * (A'' y ^ 2 + A' y * A''' y))
    have H3 := abs_add_le (A'''' y + 3 * m * (A'' y ^ 2 + A' y * A''' y))
      (3 * m ^ 2 * A' y ^ 2 * A'' y)
    norm_num only [abs_mul, abs_pow, abs_of_nonneg hm.1] at H1 H2 H3
    dsimp only [G']
    nlinarith [hA''''b y,
      mul_le_mul_of_nonneg_left H1 (show 0 ≤ 3 * m by positivity),
      mul_le_mul_of_nonneg_left hqq (show 0 ≤ 3 * m by positivity),
      mul_le_mul_of_nonneg_left hpz (show 0 ≤ 3 * m by positivity),
      mul_le_mul_of_nonneg_left hppq (show 0 ≤ 3 * m ^ 2 by positivity),
      mul_le_mul_of_nonneg_right hm.2 hB]
  have hGm : Measurable G := by dsimp [G, parisiThirdPolynomial]; fun_prop
  have hG'm : Measurable G' := by dsimp [G']; fun_prop
  have H := hasDerivAt_scalarTiltMean_spatial hA hAm hA'm hGm hG'm
    hC2.1 hGd hC2.abs_first_le_one hGb hG'b m v x
  have he (y : ℝ) : G' y + m * G y * A' y =
      parisiFourthPolynomial (A' y) (A'' y) (A''' y) (A'''' y) m := by
    dsimp [G, G', parisiThirdPolynomial, parisiFourthPolynomial]
    ring
  simp only [he] at H
  have hp := hasDerivAt_parisiStep_spatial_second hA hAm hA'm hA''m hC2 m v x
  have hq := hasDerivAt_stepD2_uniform hA hC2 hA''m hA'''m hA'''d hA'''b m v x
  have HD := ((hp.mul hq).const_mul (3 * m)).add ((hp.pow 3).const_mul (m ^ 2))
  have hmean : scalarTiltMean A G m v x = stepD3Uniform A A' A'' A''' m v x +
      3 * m * stepD1 A A' m v x * stepD2 A A' A'' m v x +
      m ^ 2 * (stepD1 A A' m v x) ^ 3 := by
    unfold stepD3Uniform
    dsimp only [G]
    ring
  rw [hmean] at H
  convert! H.sub HD using 1
  · funext y
    dsimp [G, stepD3Uniform]
    ring
  · unfold stepD4Uniform
    ring

/-- Exact preservation of the fourth exponential polynomial at the step mass. -/
theorem parisiFourthPolynomial_stepD4Uniform (A A' A'' A''' A'''' : ℝ → ℝ) (m v x : ℝ) :
    parisiFourthPolynomial (stepD1 A A' m v x) (stepD2 A A' A'' m v x)
      (stepD3Uniform A A' A'' A''' m v x) (stepD4Uniform A A' A'' A''' A'''' m v x) m =
      scalarTiltMean A (fun y => parisiFourthPolynomial (A' y) (A'' y) (A''' y) (A'''' y) m)
        m v x := by
  unfold stepD4Uniform parisiFourthPolynomial
  ring

/-- A coarse fourth-derivative estimate for one additional step. This bound is
not iterated: the actual recursion uses the telescoping invariant below. -/
theorem abs_stepD4Uniform_le {A A' A'' A''' A'''' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hA''m : Measurable A'') (hA'''b : ∀ x, |A''' x| ≤ B)
    (hA''''b : ∀ x, |A'''' x| ≤ C) {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    |stepD4Uniform A A' A'' A''' A'''' m v x| ≤ C + 8 * B + 52 := by
  have hAm : Measurable A := (continuous_iff_continuousAt.mpr
    fun y => (hC2.1 y).continuousAt).measurable
  have hA'm : Measurable A' := (continuous_iff_continuousAt.mpr
    fun y => (hC2.2.1 y).continuousAt).measurable
  have hout := hasParisiC2_parisiStep_nonneg (v := v) hm.1 hm.2 hC2 hA hAm hA'm hA''m
  have hJ (y : ℝ) := abs_parisiFourthPolynomial_le (hC2.abs_first_le_one y)
    (hC2.abs_second_le_one y) (hA'''b y) (hA''''b y) hm
  have hMean := scalarTiltMean_abs_le hA hAm hJ m v x
  have hcorr := fourth_correction_bound (hout.abs_first_le_one x)
    (hout.abs_second_le_one x) (abs_stepD3Uniform_le hA hC2 hA''m hA'''b hm v x) hm
  unfold stepD4Uniform
  exact (abs_sub _ _).trans (by linarith)

/-- Joint continuity of the fourth derivative formula, including zero
variance. A uniform bound and continuity of the input fourth derivative suffice. -/
theorem continuous_stepD4Uniform_variance_spatial
    {A A' A'' A''' A'''' : ℝ → ℝ} {B C : ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hcA'' : Continuous A'') (hcA''' : Continuous A''') (hcA'''' : Continuous A'''')
    (hA'''b : ∀ x, |A''' x| ≤ B) (hA''''b : ∀ x, |A'''' x| ≤ C)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) :
    Continuous (fun p : ℝ × ℝ => stepD4Uniform A A' A'' A''' A'''' m p.1 p.2) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hcJ : Continuous (fun y => parisiFourthPolynomial (A' y) (A'' y) (A''' y) (A'''' y) m) := by
    unfold parisiFourthPolynomial
    fun_prop
  have hJ (y : ℝ) := abs_parisiFourthPolynomial_le (hC2.abs_first_le_one y)
    (hC2.abs_second_le_one y) (hA'''b y) (hA''''b y) hm
  have hcM := (continuous_scalarTiltMean_joint hA hcA hcJ hJ).comp
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (m, p)))
  have hc := continuous_parisiStep_variance_spatial hC2 hcA'' hm.1
  have hc3 := continuous_stepD3Uniform_variance_spatial hA hC2 hcA'' hcA''' hA'''b hm
  exact hcM.sub
    (((((hc.2.1.const_mul (4 * m)).mul hc3).add ((hc.2.2.pow 2).const_mul (3 * m))).add
      (((hc.2.1.pow 2).const_mul (6 * m ^ 2)).mul hc.2.2)).add
        ((hc.2.1.pow 4).const_mul (m ^ 3)))

/-- The fourth polynomial changes by at most 42 times the mass decrement,
using the genuine depth-independent third-derivative estimate. -/
theorem parisiFourthPolynomial_mass_change {p q z w m n : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hz : |z| ≤ 6)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1) :
    |parisiFourthPolynomial p q z w m - parisiFourthPolynomial p q z w n| ≤
      42 * (n - m) := by
  have hn0 : 0 ≤ n := hm.trans hmn
  have hm1 : m ≤ 1 := hmn.trans hn
  have hgap : 0 ≤ n - m := sub_nonneg.mpr hmn
  have hsq : m ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hm hmn 2
  have hcube : m ^ 3 ≤ n ^ 3 := pow_le_pow_left₀ hm hmn 3
  have hpz : |p * z| ≤ 6 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hp (abs_nonneg z)]
  have hq2 : |q ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg q) hq
  have hp2q : |p ^ 2 * q| ≤ 1 := by
    rw [abs_mul, abs_pow]
    exact mul_le_one₀ (pow_le_one₀ (abs_nonneg p) hp) (abs_nonneg q) hq
  have hp4 : |p ^ 4| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg p) hp
  have H1 := abs_add_le (4 * (m - n) * (p * z)) (3 * (m - n) * q ^ 2)
  have H2 := abs_add_le (4 * (m - n) * (p * z) + 3 * (m - n) * q ^ 2)
    (6 * (m ^ 2 - n ^ 2) * (p ^ 2 * q))
  have H3 := abs_add_le
    (4 * (m - n) * (p * z) + 3 * (m - n) * q ^ 2 + 6 * (m ^ 2 - n ^ 2) * (p ^ 2 * q))
    ((m ^ 3 - n ^ 3) * p ^ 4)
  have he : parisiFourthPolynomial p q z w m - parisiFourthPolynomial p q z w n =
      4 * (m - n) * (p * z) + 3 * (m - n) * q ^ 2 +
        6 * (m ^ 2 - n ^ 2) * (p ^ 2 * q) + (m ^ 3 - n ^ 3) * p ^ 4 := by
    unfold parisiFourthPolynomial
    ring
  rw [he]
  have hsqd : n ^ 2 - m ^ 2 ≤ 2 * (n - m) := by
    nlinarith [mul_nonneg hgap (show 0 ≤ 2 - n - m by linarith)]
  have hcubed : n ^ 3 - m ^ 3 ≤ 3 * (n - m) := by
    have hn2 : n ^ 2 ≤ 1 := pow_le_one₀ hn0 hn
    have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm hm1
    have hnm : n * m ≤ 1 := mul_le_one₀ hn hm hm1
    nlinarith [mul_nonneg hgap (show 0 ≤ 3 - n ^ 2 - n * m - m ^ 2 by linarith)]
  simp only [abs_mul, abs_pow] at hpz hq2 hp2q hp4
  norm_num only [abs_mul, abs_pow, abs_of_nonpos (sub_nonpos.mpr hmn),
    abs_of_nonpos (sub_nonpos.mpr hsq), abs_of_nonpos (sub_nonpos.mpr hcube)] at H1 H2 H3
  nlinarith [mul_le_mul_of_nonneg_left hpz (show 0 ≤ 4 * (n - m) by positivity),
    mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 3 * (n - m) by positivity),
    mul_le_mul_of_nonneg_left hp2q (show 0 ≤ 6 * (n ^ 2 - m ^ 2) by positivity),
    mul_le_mul_of_nonneg_left hp4 (sub_nonneg.mpr hcube)]

theorem parisiFourthPolynomial_lower_mass_bound {p q z w m n : ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hz : |z| ≤ 6)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1)
    (hpoly : |parisiFourthPolynomial p q z w n| ≤ 43 - 42 * n) :
    |parisiFourthPolynomial p q z w m| ≤ 43 - 42 * m := by
  have H := abs_sub_le (parisiFourthPolynomial p q z w m) (parisiFourthPolynomial p q z w n) 0
  simp only [sub_zero] at H
  linarith [parisiFourthPolynomial_mass_change (w := w) hp hq hz hm hmn hn]

/-- The actual fourth spatial derivative throughout the finite Parisi recursion. -/
noncomputable def parisiFFourth {k : ℕ} (s : RSBScheme k) (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => -2 * (parisiFSecond s β 0 x) ^ 2 +
      4 * (parisiFDeriv s β 0 x) ^ 2 * parisiFSecond s β 0 x
  | j + 1 => stepD4Uniform (parisiF s β j) (parisiFDeriv s β j)
      (parisiFSecond s β j) (parisiFThird s β j) (parisiFFourth s β j)
      (s.m (k + 1 - j)) (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)))

/-- Simultaneous C4 regularity and a telescoping fourth-polynomial bound.
Neither the derivative nor its bound excludes zero-variance or zero-mass steps. -/
theorem parisiFFourth_props {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    (∀ x, HasDerivAt (parisiFThird s β j) (parisiFFourth s β j x) x) ∧
      Continuous (parisiFFourth s β j) ∧
      (∀ m ∈ Set.Icc 0 (s.m (k + 1 - j)), ∀ x,
        |parisiFourthPolynomial (parisiFDeriv s β j x) (parisiFSecond s β j x)
          (parisiFThird s β j x) (parisiFFourth s β j x) m| ≤ 43 - 42 * m) := by
  induction j with
  | zero =>
    have hcP : Continuous (parisiFDeriv s β 0) := continuous_iff_continuousAt.mpr
      fun x => ((parisiF_C2_props s β 0).1.2.1 x).continuousAt
    refine ⟨?_, ((continuous_parisiFSecond s β 0).pow 2).const_mul (-2) |>.add
      (((hcP.pow 2).const_mul 4).mul (continuous_parisiFSecond s β 0)), ?_⟩
    · intro x
      convert! (((parisiF_C2_props s β 0).1.2.1 x).mul
        (hasDerivAt_parisiFSecond s β 0 x)).const_mul (-2) using 1
      · funext y
        dsimp [parisiFThird]
        ring
      · dsimp only [parisiFFourth, parisiFThird]
        ring
    · intro m hm x
      apply parisiFourthPolynomial_lower_mass_bound
        ((parisiF_C2_props s β 0).1.abs_first_le_one x)
        ((parisiF_C2_props s β 0).1.abs_second_le_one x)
        (abs_parisiFThird_le_six s β 0 x) hm.1
        (by simpa only [Nat.sub_zero, s.m_top] using hm.2) le_rfl
      have he : parisiFourthPolynomial (parisiFDeriv s β 0 x) (parisiFSecond s β 0 x)
          (parisiFThird s β 0 x) (parisiFFourth s β 0 x) 1 = 1 := by
        unfold parisiFourthPolynomial parisiFFourth parisiFThird parisiFSecond parisiFDeriv
        ring
      rw [he]
      norm_num
  | succ j ih =>
    have hA := parisiF_hasLinearGrowth s β j
    have hC2 := (parisiF_C2_props s β j).1
    have hAm := parisiF_measurable s β j
    have hA''m := (parisiF_C2_props s β j).2.2
    have hm0 := s.m_nonneg (p := k + 1 - j) (by omega)
    have hm1 := s.m_le_one (p := k + 1 - j) (by omega)
    have hB (x : ℝ) : |parisiFFourth s β j x| ≤ 43 := by
      simpa only [parisiFourthPolynomial, mul_zero, zero_mul,
        zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0),
        add_zero, sub_zero] using ih.2.2 0 ⟨le_rfl, hm0⟩ x
    have hpoly := ih.2.2 (s.m (k + 1 - j)) ⟨hm0, le_rfl⟩
    constructor
    · exact hasDerivAt_stepD3Uniform hA hC2 hA''m (continuous_parisiFThird s β j).measurable
        ih.2.1.measurable (hasDerivAt_parisiFSecond s β j) ih.1
        (abs_parisiFThird_le_six s β j) hB ⟨hm0, hm1⟩ _
    constructor
    · exact (continuous_stepD4Uniform_variance_spatial hA hC2
        (continuous_parisiFSecond s β j) (continuous_parisiFThird s β j) ih.2.1
        (abs_parisiFThird_le_six s β j) hB ⟨hm0, hm1⟩).comp
        (by fun_prop : Continuous (fun x : ℝ =>
          (β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j)), x)))
    · intro m hm x
      have hmle : m ≤ s.m (k + 1 - j) := hm.2.trans
        (s.m_mono' (k + 1 - j) (by omega) (k + 1 - (j + 1)) (by omega))
      apply parisiFourthPolynomial_lower_mass_bound
        ((parisiF_C2_props s β (j + 1)).1.abs_first_le_one x)
        ((parisiF_C2_props s β (j + 1)).1.abs_second_le_one x)
        (abs_parisiFThird_le_six s β (j + 1) x) hm.1 hmle hm1
      change |parisiFourthPolynomial (stepD1 _ _ _ _ x) (stepD2 _ _ _ _ _ x)
        (stepD3Uniform _ _ _ _ _ _ x) (stepD4Uniform _ _ _ _ _ _ _ x)
          (s.m (k + 1 - j))| ≤ _
      rw [parisiFourthPolynomial_stepD4Uniform]
      exact scalarTiltMean_abs_le hA hAm hpoly _ _ x

theorem hasDerivAt_parisiFThird {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (parisiFThird s β j) (parisiFFourth s β j x) x :=
  (parisiFFourth_props s β j).1 x

theorem continuous_parisiFFourth {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Continuous (parisiFFourth s β j) := (parisiFFourth_props s β j).2.1

/-- A fixed constant bounds the actual fourth derivative at every recursion
depth, external field, inverse temperature, mass and variance configuration. -/
theorem abs_parisiFFourth_le_43 {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    |parisiFFourth s β j x| ≤ 43 := by
  simpa only [parisiFourthPolynomial, mul_zero, zero_mul,
    zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0), add_zero, sub_zero] using
    (parisiFFourth_props s β j).2.2 0
      ⟨le_rfl, s.m_nonneg (p := k + 1 - j) (by omega)⟩ x

/-- A further physical scalar step has fourth derivative bounded by 143,
uniformly in the original scheme and smoothing variance. -/
theorem abs_stepD4Uniform_parisiF_le {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    |stepD4Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
      (parisiFThird s β j) (parisiFFourth s β j) m v x| ≤ 143 := by
  convert abs_stepD4Uniform_le (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (parisiF_C2_props s β j).2.2 (abs_parisiFThird_le_six s β j)
    (abs_parisiFFourth_le_43 s β j) hm v x using 1
  norm_num

/-- Genuine fourth spatial derivative of one additional scalar step on an
actual Parisi input, including zero smoothing variance. -/
theorem hasDerivAt_stepD3Uniform_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (v x : ℝ) :
    HasDerivAt (stepD3Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
      (parisiFThird s β j) m v)
      (stepD4Uniform (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j)
        (parisiFThird s β j) (parisiFFourth s β j) m v x) x :=
  hasDerivAt_stepD3Uniform (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (parisiF_C2_props s β j).2.2 (continuous_parisiFThird s β j).measurable
    (continuous_parisiFFourth s β j).measurable (hasDerivAt_parisiFSecond s β j)
    (hasDerivAt_parisiFThird s β j) (abs_parisiFThird_le_six s β j)
    (abs_parisiFFourth_le_43 s β j) hm v x

end SpinGlass.Targets
