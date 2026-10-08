module

public import Lemmas.GuerraTalagrand.Flatness.Cases.SmallNegative

@[expose] public section

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace SpinGlass.AT

/-! ### Small positive overlaps `0 ≤ v < q` -/

/-- Strict positivity of the endpoint multiplier derivative on the small
positive-overlap branch. -/
lemma flatness_deriv_gtFunctional_zero_pos_of_mem_Ico_zero_q
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    {β h q s v : ℝ}
    (hp : (β, h) ∈ K)
    (hq : q = rsQ β h)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Ico 0 q) :
    0 <
      deriv
        (fun lam => gtFunctional β h q s lam v) 0 := by
  subst q
  exact
    (flatness_deriv_gtFunctional_zero_sign
      data hp hs).1 v hv

/-- Uniform derivative gap on the lower positive-away region
`0 ≤ v < q - ε`. -/
lemma flatness_deriv_gtFunctional_zero_lower_away
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {β h q s v ε : ℝ},
        (β, h) ∈ K →
        q = rsQ β h →
        s ∈ Set.Icc (0 : ℝ) 1 →
        0 < ε →
        0 ≤ v →
        v < q - ε →
        c * ε ≤
          deriv (fun lam => gtFunctional β h q s lam v) 0 := by
  obtain ⟨c, hc, hsep⟩ :=
    scalarOrderParameterCorrect_global_separation data
  refine ⟨c, hc, ?_⟩
  intro β h q s v ε hp hq hs hε hv0 hvqε
  subst q
  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp
  have hq1 : rsQ β h ≤ 1 :=
    (rsQ_mem_Icc β h).2
  have hv1 : v ≤ 1 := by
    linarith
  have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hv0, hv1⟩
  have hvq : v < rsQ β h := by
    linarith
  have hmain := hsep hp hs hvIcc
  rw [flatness_deriv_gtFunctional_zero_eq_g_sub
    β h s v hβ hh hs hvIcc]
  have hsign :
      0 ≤ scalarOrderParameterCorrect β h s v - v := by
    have h :=
      (scalarOrderParameterCorrect_sign data hp hs).1 v ⟨hv0, hvq⟩
    exact h.le
  rw [abs_of_nonpos (by linarith : v - rsQ β h ≤ 0),
    abs_of_nonneg hsign] at hmain
  have hmain' :
      c * (rsQ β h - v) ≤ scalarOrderParameterCorrect β h s v - v := by
    nlinarith [hmain]
  have hdist : ε ≤ rsQ β h - v := by
    linarith
  exact
    (mul_le_mul_of_nonneg_left hdist hc.le).trans hmain'

/-- Uniform derivative gap on the upper positive-away region
`q + ε < v ≤ 1`. -/
lemma flatness_deriv_gtFunctional_zero_upper_away
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {β h q s v ε : ℝ},
        (β, h) ∈ K →
        q = rsQ β h →
        s ∈ Set.Icc (0 : ℝ) 1 →
        0 < ε →
        q + ε < v →
        v ≤ 1 →
        c * ε ≤
          -deriv (fun lam => gtFunctional β h q s lam v) 0 := by
  obtain ⟨c, hc, hsep⟩ :=
    scalarOrderParameterCorrect_global_separation data
  refine ⟨c, hc, ?_⟩
  intro β h q s v ε hp hq hs hε hqεv hv1
  subst q
  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp
  have hq0 : 0 ≤ rsQ β h :=
    (rsQ_mem_Icc β h).1
  have hv0 : 0 ≤ v := by
    linarith
  have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hv0, hv1⟩
  have hqv : rsQ β h < v := by
    linarith
  have hmain := hsep hp hs hvIcc
  have hsign :
      scalarOrderParameterCorrect β h s v - v ≤ 0 := by
    have h :=
      (scalarOrderParameterCorrect_sign data hp hs).2.2 v ⟨hqv, hv1⟩
    exact h.le
  rw [abs_of_nonneg (by linarith : 0 ≤ v - rsQ β h),
    abs_of_nonpos hsign] at hmain
  have hdist : ε ≤ v - rsQ β h := by
    linarith
  calc
    c * ε ≤ c * (v - rsQ β h) :=
      mul_le_mul_of_nonneg_left hdist hc.le
    _ ≤ -(scalarOrderParameterCorrect β h s v - v) := hmain
    _ = -deriv
        (fun lam => gtFunctional β h (rsQ β h) s lam v) 0 := by
      rw [flatness_deriv_gtFunctional_zero_eq_g_sub
        β h s v hβ hh hs hvIcc]

/-- Uniform linear separation of the multiplier derivative from zero on the
entire nonnegative-overlap branch. -/
lemma flatness_deriv_gtFunctional_zero_positive_global_separation
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {β h q s v : ℝ},
        (β, h) ∈ K →
        q = rsQ β h →
        s ∈ Set.Icc (0 : ℝ) 1 →
        v ∈ Set.Icc (0 : ℝ) 1 →
        c * |v - q| ≤
          |deriv (fun lam => gtFunctional β h q s lam v) 0| := by
  obtain ⟨c, hc, hsep⟩ :=
    scalarOrderParameterCorrect_global_separation data
  refine ⟨c, hc, ?_⟩
  intro β h q s v hp hq hs hv
  subst q
  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp
  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp
  rw [flatness_deriv_gtFunctional_zero_eq_g_sub
    β h s v hβ hh hs hv]
  exact hsep hp hs hv

/-- Uniform quadratic gap on the lower positive-away region `0 ≤ v < q - ε`. -/
lemma gtFunctional_lower_positive_away_quadratic_gap
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ c > 0, ∀ {β h q s v ε : ℝ},
      (β, h) ∈ K →
      q = rsQ β h →
      s ∈ Icc (0 : ℝ) 1 →
      0 < ε →
      0 ≤ v →
      v < q - ε →
      ∃ lam ∈ Icc (-1 : ℝ) 1,
        gtFunctional β h q s lam v ≤
          2 * rsPathValue β h q s - c * ε ^ 2 := by
  obtain ⟨a, ha, haway⟩ :=
    flatness_deriv_gtFunctional_zero_lower_away data

  refine ⟨a ^ 2 / 5, by positivity, ?_⟩
  intro β h q s v ε hp hq hs hε hv0 hvqε

  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp

  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp

  have hqpos : 0 < q := by
    rw [hq]
    exact rsQ_pos hβ hh

  have hq_lt_one : q < 1 := by
    rw [hq]
    exact rsQ_lt_one hβ hh

  have hvq : v < q := by
    linarith

  have hv1 : v ≤ 1 := by
    linarith

  have hvIcc : v ∈ Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith, hv1⟩

  have hvIcc01 : v ∈ Icc (0 : ℝ) 1 := by
    exact ⟨hv0, hv1⟩

  let F : ℝ → ℝ := fun l =>
    gtFunctional β h q s l v

  let d : ℝ := deriv F 0

  let lam : ℝ := -(2 / 5 : ℝ) * d

  have hgap : a * ε ≤ d := by
    simpa [d, F] using
      haway hp hq hs hε hv0 hvqε

  have hdpos : 0 < d := by
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
      _ ≤ d * d := hmul
      _ = d ^ 2 := by
              ring

  have hzero0 :
      gtFunctional β h q s 0 v =
        2 * rsPathValue β h q s := by
    exact flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
      β h q s v ⟨hqpos, hq_lt_one⟩ hs ⟨hv0, hvq.le⟩

  have hzero :
      F 0 = 2 * rsPathValue β h q s := by
    simpa [F] using hzero0

  refine ⟨lam, hlam, ?_⟩

  change
    F lam ≤
      2 * rsPathValue β h q s -
        (a ^ 2 / 5) * ε ^ 2

  nlinarith [ht', hsq]

/-- Uniform quadratic gap near the replica-symmetric overlap on the
nonnegative-overlap branch. -/
lemma gtFunctional_central_positive_quadratic_gap
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ ε₀ > 0, ∃ c > 0,
      ∀ {β h q s v : ℝ},
        (β, h) ∈ K →
        q = rsQ β h →
        s ∈ Icc (0 : ℝ) 1 →
        v ∈ Icc (-1 : ℝ) 1 →
        v ∈ Icc (q - ε₀) (q + ε₀) →
        ∃ lam ∈ Icc (-1 : ℝ) 1,
          gtFunctional β h q s lam v ≤
            2 * rsPathValue β h q s -
              c * (v - q) ^ 2 := by
  obtain ⟨a, ha, hsep⟩ :=
    flatness_deriv_gtFunctional_zero_positive_global_separation data

  let ε₀ : ℝ := data.qmin / 2

  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    linarith [data.qmin_pos]

  refine ⟨ε₀, hε₀, a ^ 2 / 5, by positivity, ?_⟩

  intro β h q s v hp hq hs hv hcenter

  have hβ : 0 < β := by
    simpa using data.β_pos (β, h) hp

  have hh : 0 < h := by
    simpa using data.h_pos (β, h) hp

  have hqpos : 0 < q := by
    rw [hq]
    exact rsQ_pos hβ hh

  have hq_lt_one : q < 1 := by
    rw [hq]
    exact rsQ_lt_one hβ hh

  have hqlower : data.qmin ≤ q := by
    calc
      data.qmin ≤ rsQ β h :=
        data.q_lower (β, h) hp
      _ = q := hq.symm

  have hcenter_lower : q - ε₀ ≤ v :=
    hcenter.1

  have hv0 : 0 ≤ v := by
    dsimp [ε₀] at hcenter_lower
    linarith [data.qmin_pos, hqlower, hcenter_lower]

  have hv1 : v ≤ 1 :=
    hv.2

  have hvIcc01 : v ∈ Icc (0 : ℝ) 1 :=
    ⟨hv0, hv1⟩

  have hgap :
      a * |v - q| ≤
        |deriv
          (fun lam => gtFunctional β h q s lam v) 0| :=
    hsep hp hq hs hvIcc01

  let F : ℝ → ℝ :=
    fun l => gtFunctional β h q s l v

  let d : ℝ :=
    deriv F 0

  let lam : ℝ :=
    -(2 / 5 : ℝ) * d

  have hgap' :
      a * |v - q| ≤ |d| := by
    simpa [d, F] using hgap

  have hd : |d| ≤ 2 := by
    dsimp [d, F]
    exact
      abs_deriv_gtFunctional_le_two β h q s 0 v
        (by simpa [abs_le] using hv)

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
      a ^ 2 * (v - q) ^ 2 ≤ d ^ 2 := by
    have hmul :=
      mul_self_le_mul_self
        (mul_nonneg ha.le (abs_nonneg (v - q)))
        hgap'

    calc
      a ^ 2 * (v - q) ^ 2
          =
        (a * |v - q|) * (a * |v - q|) := by
          nlinarith [sq_abs (v - q)]
      _ ≤ |d| * |d| := hmul
      _ = d ^ 2 := by
          nlinarith [sq_abs d]

  have hzero0 :
      gtFunctional β h q s 0 v =
        2 * rsPathValue β h q s := by
    rcases le_total v q with hvq | hqv
    · exact
        flatness_gtFunctional_zero_eq_two_rsPathValue_small_positive
          β h q s v ⟨hqpos, hq_lt_one⟩ hs ⟨hv0, hvq⟩
    · exact
        flatness_gtFunctional_zero_eq_two_rsPathValue_large_positive
          β h q s v ⟨hqpos, hq_lt_one⟩ hs ⟨hqv, hv1⟩

  have hzero :
      F 0 = 2 * rsPathValue β h q s := by
    simpa [F] using hzero0

  refine ⟨lam, hlam, ?_⟩

  change
    F lam ≤
      2 * rsPathValue β h q s -
        (a ^ 2 / 5) * (v - q) ^ 2

  nlinarith [ht', hsq]

end SpinGlass.AT
