module

public import Lemmas.Price.Key

@[expose] public section

/-!
# Differentiating a Gaussian integral along a path of covariance matrices

Combining the two key estimates of `Lemmas.Price.Key` with a "shift by `λ • 1`" trick, we differentiate
`s ↦ ∫ h dN(0, S s)` at a point `t` where the entries of `S` are differentiable, for a path `S`
of positive semidefinite matrices of constant trace.
-/

open Matrix MeasureTheory Filter PriceFourier
open scoped RealInnerProductSpace

namespace ProbabilityTheory

local notation "multivariateGaussian" => PriceGaussian.multivariateGaussian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary arithmetic bookkeeping -/

theorem price_budget_zero {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    c / (3 * (C + 1)) * C ≤ c / 3 := by
  have key : c / (3 * (C + 1)) * C = c * C / (3 * (C + 1)) := by ring
  rw [key, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
  nlinarith

theorem price_budget_two {c N C : ℝ} (hc : 0 < c) (hN : 0 ≤ N) (hC : 0 ≤ C) :
    2 * (c / (6 * (N + 1) * (C + 1))) * C * N ≤ c / 3 := by
  have key : 2 * (c / (6 * (N + 1) * (C + 1))) * C * N
      = c * (C * N) / (3 * (N + 1) * (C + 1)) := by
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
  nlinarith [mul_nonneg hc.le hN, mul_nonneg hc.le hC]

theorem price_budget_hess {c N M2 : ℝ} (hc : 0 < c) (hN : 0 ≤ N) (hM2 : 0 ≤ M2) :
    1 / 2 * (N * N * (2 * c / (3 * (M2 + 1) * (N * N + 1)) * M2)) ≤ c / 3 := by
  have key : 1 / 2 * (N * N * (2 * c / (3 * (M2 + 1) * (N * N + 1)) * M2))
      = c * (N * N * M2) / (3 * (M2 + 1) * (N * N + 1)) := by
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
  nlinarith [mul_nonneg hc.le hM2, mul_nonneg hc.le (mul_nonneg hN hN)]

/-- The final linear combination assembling the two second-order expansions, the zeroth-order
comparison of the Hessian traces, and the first-order comparison of the increment with its
linearization. -/
theorem price_deriv_combine {a b X SD P Gt Gs lam N eps0 eps2 M2 beta d c : ℝ}
    (hA1 : |X - b - 1 / 2 * (SD + lam * Gt)| ≤ eps2 * (lam * N))
    (hA2 : |X - a - 1 / 2 * (lam * Gs)| ≤ eps2 * (lam * N))
    (hA4 : |SD - d * P| ≤ N * N * (beta * |d| * M2))
    (hGd : |Gt - Gs| ≤ 2 * eps0)
    (hlam0 : 0 ≤ lam)
    (B1 : 2 * (eps2 * (lam * N)) ≤ c / 3 * |d|)
    (B2 : lam * eps0 ≤ c / 3 * |d|)
    (B3 : 1 / 2 * (N * N * (beta * |d| * M2)) ≤ c / 3 * |d|) :
    |a - b - d * (1 / 2 * P)| ≤ c * |d| := by
  have hG : |1 / 2 * (lam * (Gt - Gs))| ≤ lam * eps0 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hlam0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hGd hlam0]
  have h1 := abs_le.1 hA1
  have h2 := abs_le.1 hA2
  have h4 := abs_le.1 hA4
  have h5 := abs_le.1 hG
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2, h5.1, h5.2]

/-! ### A diagonally dominant shift is positive semidefinite -/

theorem posSemidef_add_smul_one {D : Matrix n n ℝ} (hsym : D.IsHermitian) {lam : ℝ}
    (hlam : ∑ i, ∑ j, |D i j| ≤ lam) :
    (D + lam • (1 : Matrix n n ℝ)).PosSemidef := by
  have habs0 : (0 : ℝ) ≤ ∑ i, ∑ j, |D i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hlam0 : 0 ≤ lam := le_trans habs0 hlam
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · have h1 : (lam • (1 : Matrix n n ℝ)).IsHermitian := by
      unfold Matrix.IsHermitian
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
    exact hsym.add h1
  · have heq : star x ⬝ᵥ ((D + lam • (1 : Matrix n n ℝ)) *ᵥ x)
        = (∑ i, ∑ j, D i j * (x i * x j)) + lam * ∑ k, x k * x k := by
      simp only [dotProduct, mulVec, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Pi.star_apply, star_trivial, smul_eq_mul, mul_ite, mul_one, mul_zero, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · simp [ite_mul, Finset.sum_ite_eq]
        ring
    rw [heq]
    set N2 : ℝ := ∑ k, x k * x k with hN2
    have hN20 : 0 ≤ N2 := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hx2 : ∀ i, x i * x i ≤ N2 := fun i =>
      Finset.single_le_sum (f := fun k => x k * x k)
        (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ i)
    have hprod : ∀ i j, |x i * x j| ≤ N2 := by
      intro i j
      rw [abs_mul]
      nlinarith [hx2 i, hx2 j, abs_nonneg (x i), abs_nonneg (x j), sq_abs (x i), sq_abs (x j),
        sq_nonneg (|x i| - |x j|)]
    have hQ : |∑ i, ∑ j, D i j * (x i * x j)| ≤ (∑ i, ∑ j, |D i j|) * N2 := by
      calc |∑ i, ∑ j, D i j * (x i * x j)|
          ≤ ∑ i, |∑ j, D i j * (x i * x j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |D i j| * N2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hprod i j) (abs_nonneg _)
        _ = (∑ i, ∑ j, |D i j|) * N2 := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    have hle : (∑ i, ∑ j, |D i j|) * N2 ≤ lam * N2 := mul_le_mul_of_nonneg_right hlam hN20
    have := abs_le.1 hQ
    linarith [this.1, this.2]

theorem trace_smul_one (lam : ℝ) :
    (lam • (1 : Matrix n n ℝ)).trace = lam * (Fintype.card n) := by
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm]

theorem sum_smul_one_mul (lam : ℝ) (Hf : n → n → ℝ) :
    ∑ i, ∑ j, (lam • (1 : Matrix n n ℝ)) i j * Hf i j = lam * ∑ i, Hf i i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.smul_apply, Matrix.one_apply, ite_mul]

theorem sum_add_smul_one_mul (D : Matrix n n ℝ) (lam : ℝ) (Hf : n → n → ℝ) :
    ∑ i, ∑ j, (D + lam • (1 : Matrix n n ℝ)) i j * Hf i j
      = (∑ i, ∑ j, D i j * Hf i j) + lam * ∑ i, Hf i i := by
  rw [← sum_smul_one_mul lam Hf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [Matrix.add_apply, add_mul]

/-! ### Auxiliary facts about `Gint` -/

variable {h : EuclideanSpace ℝ n → ℝ}

theorem abs_Gint_le {A : Matrix n n ℝ} {v : EuclideanSpace ℝ n → ℝ} (hv : Continuous v)
    {M : ℝ} (hb : ∀ z, |v z| ≤ M) : |Gint v A| ≤ M := by
  have hint : Integrable v (multivariateGaussian (0 : EuclideanSpace ℝ n) A) :=
    integrable_of_bound hv.aestronglyMeasurable hb
  calc |Gint v A| ≤ ∫ z, |v z| ∂(multivariateGaussian (0 : EuclideanSpace ℝ n) A) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _z, M ∂(multivariateGaussian (0 : EuclideanSpace ℝ n) A) :=
        integral_mono hint.abs (integrable_const M) hb
    _ = M := by simp

theorem Gint_sum_hess_diag (hC : ContDiff ℝ 2 h) {M2 : ℝ} (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    (A : Matrix n n ℝ) :
    Gint (fun z => ∑ i, (hess h z) (euclidBasis i) (euclidBasis i)) A
      = ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) A := by
  rw [Gint, integral_finset_sum _ (fun i _ => integrable_of_bound
    (continuous_hess_coord hC i i).aestronglyMeasurable (fun z => abs_hess_coord_le hb2 z i i))]
  rfl

/-! ### The derivative along a path of covariances -/

theorem hasDerivWithinAt_Gint (hC : ContDiff ℝ 2 h) {M0 M1 M2 : ℝ}
    (hb0 : ∀ z, |h z| ≤ M0) (hb1 : ∀ z, ‖fderiv ℝ h z‖ ≤ M1) (hb2 : ∀ z, ‖hess h z‖ ≤ M2)
    {U : Set ℝ} {t : ℝ} (ht : t ∈ U)
    (S : ℝ → Matrix n n ℝ) (Sdot : Matrix n n ℝ)
    (hPSD : ∀ s ∈ U, (S s).PosSemidef)
    (htr : ∀ s ∈ U, (S s).trace = (S t).trace)
    (hSd : ∀ i j, HasDerivWithinAt (fun s => S s i j) (Sdot i j) U t) :
    HasDerivWithinAt (fun s => Gint h (S s))
      (1 / 2 * ∑ i, ∑ j, Sdot i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)) U t := by
  have hM2 : 0 ≤ M2 := (norm_nonneg (hess h 0)).trans (hb2 0)
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by positivity
  set C : ℝ := ∑ i, ∑ j, (|Sdot i j| + 1) with hCdef
  have hC0 : (0 : ℝ) ≤ C :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hucont : Continuous
      fun z : EuclideanSpace ℝ n => ∑ i, (hess h z) (euclidBasis i) (euclidBasis i) :=
    continuous_finset_sum _ fun i _ => continuous_hess_coord hC i i
  have hubd : ∀ z : EuclideanSpace ℝ n,
      |∑ i, (hess h z) (euclidBasis i) (euclidBasis i)| ≤ N * M2 := by
    intro z
    calc |∑ i, (hess h z) (euclidBasis i) (euclidBasis i)|
        ≤ ∑ i, |(hess h z) (euclidBasis i) (euclidBasis i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : n, M2 := Finset.sum_le_sum fun i _ => abs_hess_coord_le hb2 z i i
      _ = N * M2 := by simp [hNdef, mul_comm]
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set eps0 : ℝ := c / (3 * (C + 1)) with heps0
  set eps2 : ℝ := c / (6 * (N + 1) * (C + 1)) with heps2
  set beta : ℝ := 2 * c / (3 * (M2 + 1) * (N * N + 1)) with hbetadef
  have heps00 : 0 < eps0 := by rw [heps0]; positivity
  have heps20 : 0 < eps2 := by rw [heps2]; positivity
  have hbeta0 : 0 < beta := by rw [hbetadef]; positivity
  obtain ⟨δ0, hδ0, Hord0⟩ := exists_delta_order0 (n := n) hucont hubd
    (K := (S t).trace) heps00
  obtain ⟨δ2, hδ2, Hord2⟩ := exists_delta_order2 hC hb0 hb1 hb2 (K := (S t).trace) heps20
  have hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ s in nhdsWithin t U, |s - t| < r := by
    intro r hr
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [Metric.ball_mem_nhds t hr] with s hs
    rwa [Metric.mem_ball, Real.dist_eq] at hs
  have hall : ∀ᶠ s in nhdsWithin t U, ∀ i j : n,
      |S s i j - S t i j - (s - t) * Sdot i j| ≤ min beta 1 * |s - t| := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have h2 := Asymptotics.isLittleO_iff.1 (hasDerivWithinAt_iff_isLittleO.1 (hSd i j))
      (show (0 : ℝ) < min beta 1 by positivity)
    filter_upwards [h2] with s hs
    simpa [Real.norm_eq_abs, smul_eq_mul] using hs
  filter_upwards [self_mem_nhdsWithin, hall,
    hsmall (min δ0 δ2 / ((C + 1) * (N + 1))) (by positivity)] with s hs hdif hsm
  -- set up the increment
  set D : Matrix n n ℝ := S s - S t with hDdef
  set lam : ℝ := ∑ i, ∑ j, |D i j| with hlamdef
  have hlam0 : 0 ≤ lam :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hst0 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
  have hdif' : ∀ i j : n, |D i j| ≤ (|Sdot i j| + 1) * |s - t| := by
    intro i j
    have h1 : |D i j - (s - t) * Sdot i j| ≤ 1 * |s - t| :=
      (hdif i j).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hst0)
    have h2 : |(s - t) * Sdot i j| = |Sdot i j| * |s - t| := by
      rw [abs_mul]; ring
    have h3 : |D i j| ≤ |D i j - (s - t) * Sdot i j| + |(s - t) * Sdot i j| := by
      simpa using abs_add_le (D i j - (s - t) * Sdot i j) ((s - t) * Sdot i j)
    rw [h2] at h3
    linarith
  have hlamC : lam ≤ C * |s - t| := by
    rw [hlamdef, hCdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hdif' i j
  have hprodle : C * N ≤ (C + 1) * (N + 1) := by nlinarith
  have hlamN : lam * N ≤ min δ0 δ2 := by
    have hpos : (0 : ℝ) < (C + 1) * (N + 1) := by positivity
    have h1 : lam * N ≤ (C * |s - t|) * N := mul_le_mul_of_nonneg_right hlamC hN0
    have h2 : |s - t| ≤ min δ0 δ2 / ((C + 1) * (N + 1)) := hsm.le
    have h3 : (C * |s - t|) * N ≤ ((C + 1) * (N + 1)) * |s - t| := by nlinarith
    have h4 : ((C + 1) * (N + 1)) * |s - t| ≤ min δ0 δ2 := by
      rw [← le_div_iff₀' hpos]
      exact h2
    linarith
  have hlamN0 : lam * N ≤ δ0 := hlamN.trans (min_le_left _ _)
  have hlamN2 : lam * N ≤ δ2 := hlamN.trans (min_le_right _ _)
  -- the shifted increments
  have hDsym : D.IsHermitian := (hPSD s hs).isHermitian.sub (hPSD t ht).isHermitian
  have hT1 : (D + lam • (1 : Matrix n n ℝ)).PosSemidef :=
    posSemidef_add_smul_one hDsym hlamdef.ge
  have hT2 : (lam • (1 : Matrix n n ℝ)).PosSemidef := by
    have h0 := posSemidef_add_smul_one (D := (0 : Matrix n n ℝ)) Matrix.isHermitian_zero
      (lam := lam) (by simpa using hlam0)
    simpa using h0
  have hsum : S t + (D + lam • (1 : Matrix n n ℝ)) = S s + lam • (1 : Matrix n n ℝ) := by
    rw [hDdef]; abel
  have hDtr : D.trace = 0 := by rw [hDdef, Matrix.trace_sub, htr s hs, sub_self]
  have htr1 : (D + lam • (1 : Matrix n n ℝ)).trace = lam * N := by
    rw [Matrix.trace_add, hDtr, zero_add, trace_smul_one, hNdef]
  have htr2 : (lam • (1 : Matrix n n ℝ)).trace = lam * N := by rw [trace_smul_one, hNdef]
  -- second-order expansion at `S t` with increment `D + lam • 1`
  have heq1 : ∑ i, ∑ j, (D + lam • (1 : Matrix n n ℝ)) i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)
      = (∑ i, ∑ j, D i j
          * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t))
        + lam * ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S t) :=
    sum_add_smul_one_mul D lam
      (fun i j => Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t))
  have heq2 : ∑ i, ∑ j, (lam • (1 : Matrix n n ℝ)) i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S s)
      = lam * ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S s) :=
    sum_smul_one_mul lam
      (fun i j => Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S s))
  have E1 : |Gint h (S s + lam • (1 : Matrix n n ℝ)) - Gint h (S t)
      - 1 / 2 * ((∑ i, ∑ j, D i j
            * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t))
          + lam * ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S t))|
      ≤ eps2 * (lam * N) := by
    have hb := Hord2 (S t) (D + lam • (1 : Matrix n n ℝ)) (hPSD t ht) hT1 le_rfl
      (by rw [htr1]; exact hlamN2)
    rwa [hsum, htr1, heq1] at hb
  have E2 : |Gint h (S s + lam • (1 : Matrix n n ℝ)) - Gint h (S s)
      - 1 / 2 * (lam * ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S s))|
      ≤ eps2 * (lam * N) := by
    have hb := Hord2 (S s) (lam • (1 : Matrix n n ℝ)) (hPSD s hs) hT2 (le_of_eq (htr s hs))
      (by rw [htr2]; exact hlamN2)
    rwa [htr2, heq2] at hb
  -- zeroth-order comparison of the traces of the Hessian integrals
  have hGd : |(∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S t))
      - ∑ i, Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis i)) (S s)| ≤ 2 * eps0 := by
    have F1 := Hord0 (S t) (D + lam • (1 : Matrix n n ℝ)) (hPSD t ht) hT1 le_rfl
      (by rw [htr1]; exact hlamN0)
    have F2 := Hord0 (S s) (lam • (1 : Matrix n n ℝ)) (hPSD s hs) hT2 (le_of_eq (htr s hs))
      (by rw [htr2]; exact hlamN0)
    rw [hsum, Gint_sum_hess_diag hC hb2, Gint_sum_hess_diag hC hb2] at F1
    rw [Gint_sum_hess_diag hC hb2, Gint_sum_hess_diag hC hb2] at F2
    have h1 := abs_le.1 F1
    have h2 := abs_le.1 F2
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- first-order comparison of the increment with its linearization
  have hsplit : (∑ i, ∑ j, D i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t))
      - (s - t) * ∑ i, ∑ j, Sdot i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)
      = ∑ i, ∑ j, (D i j - (s - t) * Sdot i j)
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hterm : ∀ i j : n, |(D i j - (s - t) * Sdot i j)
      * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)|
      ≤ beta * |s - t| * M2 := by
    intro i j
    rw [abs_mul]
    have h1 : |D i j - (s - t) * Sdot i j| ≤ beta * |s - t| :=
      (hdif i j).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hst0)
    have h2 : |Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)| ≤ M2 :=
      abs_Gint_le (continuous_hess_coord hC i j) (fun z => abs_hess_coord_le hb2 z i j)
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hbeta0.le hst0)
  have hsplitbd : |(∑ i, ∑ j, D i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t))
      - (s - t) * ∑ i, ∑ j, Sdot i j
        * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)|
      ≤ N * N * (beta * |s - t| * M2) := by
    rw [hsplit]
    calc |∑ i, ∑ j, (D i j - (s - t) * Sdot i j)
            * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)|
        ≤ ∑ i, |∑ j, (D i j - (s - t) * Sdot i j)
            * Gint (fun z => (hess h z) (euclidBasis i) (euclidBasis j)) (S t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : n, ∑ _j : n, beta * |s - t| * M2 :=
          Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
      _ = N * N * (beta * |s - t| * M2) := by
          rw [hNdef]
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- budget bookkeeping
  have hK1 : 2 * eps2 * C * N ≤ c / 3 := by
    rw [heps2]; exact price_budget_two hc hN0 hC0
  have hK2 : eps0 * C ≤ c / 3 := by
    rw [heps0]; exact price_budget_zero hc hC0
  have hK3 : 1 / 2 * (N * N * (beta * M2)) ≤ c / 3 := by
    rw [hbetadef]; exact price_budget_hess hc hN0 hM2
  have B1 : 2 * (eps2 * (lam * N)) ≤ c / 3 * |s - t| := by
    have h1 : lam * N ≤ C * |s - t| * N := mul_le_mul_of_nonneg_right hlamC hN0
    have h2 : 2 * (eps2 * (lam * N)) ≤ 2 * (eps2 * (C * |s - t| * N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 heps20.le)
        (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : 2 * (eps2 * (C * |s - t| * N)) = 2 * eps2 * C * N * |s - t| := by ring
    have h4 : 2 * eps2 * C * N * |s - t| ≤ c / 3 * |s - t| :=
      mul_le_mul_of_nonneg_right hK1 hst0
    rw [h3] at h2
    exact h2.trans h4
  have B2 : lam * eps0 ≤ c / 3 * |s - t| := by
    have h1 : lam * eps0 ≤ C * |s - t| * eps0 := mul_le_mul_of_nonneg_right hlamC heps00.le
    have h3 : C * |s - t| * eps0 = eps0 * C * |s - t| := by ring
    have h4 : eps0 * C * |s - t| ≤ c / 3 * |s - t| := mul_le_mul_of_nonneg_right hK2 hst0
    rw [h3] at h1
    exact h1.trans h4
  have B3 : 1 / 2 * (N * N * (beta * |s - t| * M2)) ≤ c / 3 * |s - t| := by
    have h3 : 1 / 2 * (N * N * (beta * |s - t| * M2))
        = 1 / 2 * (N * N * (beta * M2)) * |s - t| := by ring
    have h4 : 1 / 2 * (N * N * (beta * M2)) * |s - t| ≤ c / 3 * |s - t| :=
      mul_le_mul_of_nonneg_right hK3 hst0
    rw [h3]
    exact h4
  -- conclusion
  simp only [Real.norm_eq_abs, smul_eq_mul]
  exact price_deriv_combine E1 E2 hsplitbd hGd hlam0 B1 B2 B3

end ProbabilityTheory
