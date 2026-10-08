module

/-
# The lambda-coupled partition function in Talagrand, Section 5

The overlap constraint is bounded by a genuine, unrestricted partition sum
with interaction `lambda * sum_i sigma_i tau_i`. We prove the one-site formula
(5.14), its site factorisation, and propagate the constraint comparison through
the existing coupled cascade. This is the endpoint construction used in (5.17),
not the interpolating inequality of Theorem 3.1 or the full Theorem 2.4.
-/
public import Targets.CoupledLipschitz
public import Lemmas.GuerraTalagrand.Bound.Basic
public import Lemmas.GuerraTalagrand.Gaussian

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

theorem parisiStepPi_const_add_growth {n : ℕ} (c m v : ℝ)
    {A : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (x : Fin n → ℝ) :
    parisiStepPi n m v (fun y => c + A y) x = c + parisiStepPi n m v A x := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  by_cases hm : m = 0
  · simp only [parisiStepPi, if_pos hm]
    rw [integral_add (integrable_const c) (integrable_shift_pi hD hb hA.measurable x)]
    simp
  · simp only [parisiStepPi, if_neg hm]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_const_mul, Real.log_mul (Real.exp_ne_zero _)
      (integral_exp_shift_pi_pos (m := m) (v := v) hD hb hA.measurable x).ne', Real.log_exp]
    field_simp

theorem CoupledGrowth.const_add {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (c : ℝ) : CoupledGrowth (fun x y => c + A x y) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨hA.measurable.const_add c, |c| + C, D, hD, fun x y => ?_⟩
  nlinarith [abs_add_le c (A x y), hb x y]

theorem independentStepPi_const_add {n : ℕ} (c m v : ℝ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    independentStepPi n m v (fun x y => c + A x y) x y =
      c + independentStepPi n m v A x y := by
  by_cases hm : m = 0
  · simp only [independentStepPi, if_pos hm]
    rw [integral_add (integrable_const c) (hA.integrable_shift v x y)]
    simp
  · simp only [independentStepPi, if_neg hm]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_const_mul, Real.log_mul (Real.exp_ne_zero _)
      (hA.integral_exp_shift_pos m v x y).ne', Real.log_exp]
    field_simp

theorem sharedStepPi_const_add {n : ℕ} (c m v : ℝ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    sharedStepPi n m v (fun x y => c + A x y) x y =
      c + sharedStepPi n m v A x y :=
  parisiStepPi_const_add_growth c (m / 2) v (hA.shared_shift x y) 0

/-- Constants, including the overlap penalty, pass unchanged through every level. -/
theorem coupledCascade_const_add {n k : ℕ} (s : RSBScheme k) (β c : ℝ) (d j : ℕ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    coupledCascade n s β d (fun x y => c + A x y) j x y =
      c + coupledCascade n s β d A j x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    simp only [coupledCascade]
    have he : coupledCascade n s β d (fun x y => c + A x y) j =
        fun x y => c + coupledCascade n s β d A j x y := funext fun x => funext (ih x)
    rw [he]
    split_ifs
    · exact independentStepPi_const_add c _ _ (hA.cascade s β d j) x y
    · exact sharedStepPi_const_add c _ _ (hA.cascade s β d j) x y

/-- The positive expression inside the logarithm in (5.14). -/
noncomputable def coupledSiteZ (ℓ x y : ℝ) : ℝ :=
  Real.cosh x * Real.cosh y * Real.cosh ℓ + Real.sinh x * Real.sinh y * Real.sinh ℓ

noncomputable def coupledSite (ℓ x y : ℝ) : ℝ := Real.log (coupledSiteZ ℓ x y)

/-- Normalization bridge to RSAT's already formalized two-replica terminal. -/
theorem coupledSiteZ_eq_exp_gtTerminal (ℓ x y : ℝ) :
    coupledSiteZ ℓ x y = Real.exp (AT.gtTerminal ℓ x y) := by
  rw [AT.gtTerminal, Real.exp_log (by positivity)]
  simp only [coupledSiteZ, Real.cosh_eq, Real.sinh_eq, sub_eq_add_neg,
    Real.exp_add, Real.exp_neg]
  ring

/-- The paper's hyperbolic form and RSAT's four-exponential form are identical. -/
theorem coupledSite_eq_gtTerminal (ℓ x y : ℝ) : coupledSite ℓ x y = AT.gtTerminal ℓ x y := by
  rw [coupledSite, coupledSiteZ_eq_exp_gtTerminal, Real.log_exp]

theorem coupledSite_spin_sum (ℓ x y : ℝ) :
    (∑ a : Bool, ∑ b : Bool, Real.exp
      ((if a then (1 : ℝ) else -1) * x + (if b then (1 : ℝ) else -1) * y +
        ℓ * (if a then (1 : ℝ) else -1) * (if b then (1 : ℝ) else -1))) =
      4 * coupledSiteZ ℓ x y := by
  rw [coupledSiteZ_eq_exp_gtTerminal]
  simpa only [Fintype.sum_prod_type, mul_comm] using
    AT.sum_bool_pair_exp_eq_four_mul_exp_gtTerminal ℓ x y

theorem coupledSiteZ_pos (ℓ x y : ℝ) : 0 < coupledSiteZ ℓ x y := by
  rw [coupledSiteZ_eq_exp_gtTerminal]
  exact Real.exp_pos _

@[simp] theorem coupledSite_zero (x y : ℝ) :
    coupledSite 0 x y = Real.log (Real.cosh x) + Real.log (Real.cosh y) := by
  rw [coupledSite_eq_gtTerminal]
  exact AT.gtTerminal_zero x y

/-- The terminal lambda derivative used in the proof of Lemma 5.8. -/
theorem hasDerivAt_coupledSite_zero (x y : ℝ) :
    HasDerivAt (fun ℓ => coupledSite ℓ x y)
      ((Real.sinh x / Real.cosh x) * (Real.sinh y / Real.cosh y)) 0 := by
  simp only [coupledSite_eq_gtTerminal]
  simpa only [AT.deriv_gtTerminal_zero, Real.tanh_eq_sinh_div_cosh] using
    (AT.hasDerivAt_gtTerminal 0 x y).differentiableAt.hasDerivAt

/-- Unrestricted two-replica log partition function with an actual spin interaction. -/
noncomputable def lambdaCoupledBase (n : ℕ) (U : EnergySpace n) (h t ℓ : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  Real.log (∑ σ : Config n, ∑ τ : Config n,
    Real.exp (guerraH n U h t x σ + guerraH n U h t y τ +
      ℓ * ∑ i, spin n σ i * spin n τ i))

@[simp] theorem lambdaCoupledBase_zero (n : ℕ) (U : EnergySpace n) (h t : ℝ)
    (x y : Fin n → ℝ) : lambdaCoupledBase n U h t 0 x y = coupledBase n U h t x y := by
  simp [lambdaCoupledBase, coupledBase]

@[simp] theorem lambdaCoupledBase_zero_fun (n : ℕ) (U : EnergySpace n) (h t : ℝ) :
    lambdaCoupledBase n U h t 0 = coupledBase n U h t :=
  funext fun x => funext fun y => lambdaCoupledBase_zero n U h t x y

theorem lambdaCoupledBase_dist_le (n : ℕ) (U : EnergySpace n) (h t ℓ μ : ℝ)
    (x y : Fin n → ℝ) :
    |lambdaCoupledBase n U h t ℓ x y - lambdaCoupledBase n U h t μ x y| ≤ n * |ℓ - μ| := by
  classical
  have hb (σ τ : Config n) : |∑ i, spin n σ i * spin n τ i| ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ i, |spin n σ i * spin n τ i| := Finset.abs_sum_le_sum_abs _ _
      _ = n := by simp [abs_mul, abs_spin]
  have H := abs_log_sum_exp_sub_le_on (Finset.univ : Finset (Config n × Config n))
    Finset.univ_nonempty (f := fun p => guerraH n U h t x p.1 + guerraH n U h t y p.2 +
      ℓ * ∑ i, spin n p.1 i * spin n p.2 i)
    (g := fun p => guerraH n U h t x p.1 + guerraH n U h t y p.2 +
      μ * ∑ i, spin n p.1 i * spin n p.2 i) (ε := n * |ℓ - μ|) (by
      intro p _
      have he : guerraH n U h t x p.1 + guerraH n U h t y p.2 +
          ℓ * ∑ i, spin n p.1 i * spin n p.2 i -
          (guerraH n U h t x p.1 + guerraH n U h t y p.2 +
            μ * ∑ i, spin n p.1 i * spin n p.2 i) =
          (ℓ - μ) * ∑ i, spin n p.1 i * spin n p.2 i := by ring
      rw [he, abs_mul, mul_comm (n : ℝ)]
      exact mul_le_mul_of_nonneg_left (hb _ _) (abs_nonneg _))
  simpa only [lambdaCoupledBase, Fintype.sum_prod_type] using H

theorem measurable_lambdaCoupledBase (n : ℕ) (U : EnergySpace n) (h t ℓ : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => lambdaCoupledBase n U h t ℓ p.1 p.2) := by
  unfold lambdaCoupledBase
  apply Measurable.log
  exact Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ =>
    ((((measurable_guerraH n U h t σ).comp measurable_fst).add
      ((measurable_guerraH n U h t τ).comp measurable_snd)).add_const _).exp

theorem lambdaCoupledBase_growth (n : ℕ) (U : EnergySpace n) (h ℓ : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : CoupledGrowth (lambdaCoupledBase n U h t ℓ) := by
  obtain ⟨C, D, hD, hb⟩ := (coupledBase_growth n U h ht).bound
  refine ⟨measurable_lambdaCoupledBase n U h t ℓ, C + n * |ℓ|, D, hD, fun x y => ?_⟩
  have H := lambdaCoupledBase_dist_le n U h t ℓ 0 x y
  simp only [lambdaCoupledBase_zero, sub_zero] at H
  have ha := abs_add_le (lambdaCoupledBase n U h t ℓ x y - coupledBase n U h t x y)
    (coupledBase n U h t x y)
  rw [sub_add_cancel] at ha
  linarith [hb x y]

/-- Site factorisation for an arbitrary interaction on a pair of Ising spins. -/
theorem pairSpinSum_prod {n : ℕ} (f : Fin n → Bool → Bool → ℝ) :
    (∑ σ : Config n, ∑ τ : Config n, ∏ i, f i (σ i) (τ i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, f i a b := by
  classical
  let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => Bool)
  have H := e.sum_comp (fun p : Config n × Config n => ∏ i, f i (p.1 i) (p.2 i))
  change (∑ p : Fin n → Bool × Bool, ∏ i, f i (p i).1 (p i).2) = _ at H
  rw [Fintype.sum_prod_type] at H
  rw [← H]
  simpa only [Fintype.sum_prod_type] using
    (Fintype.prod_sum (fun i (p : Bool × Bool) => f i p.1 p.2)).symm

/-- The exact local-spin identity beneath (5.17); no Gaussian assumption is needed. -/
theorem pairSpinSum_exp {n : ℕ} (ℓ : ℝ) (x y : Fin n → ℝ) :
    (∑ σ : Config n, ∑ τ : Config n, Real.exp
      (∑ i, (spin n σ i * x i + spin n τ i * y i + ℓ * spin n σ i * spin n τ i))) =
      ∏ i, 4 * coupledSiteZ ℓ (x i) (y i) := by
  have H := AT.sum_pair_exp_sum_eq_prod_sum_exp (fun i (p : Bool × Bool) =>
    (if p.1 then (1 : ℝ) else -1) * x i + (if p.2 then (1 : ℝ) else -1) * y i +
      ℓ * (if p.1 then (1 : ℝ) else -1) * (if p.2 then (1 : ℝ) else -1))
  simp only [Fintype.sum_prod_type] at H
  rw [show (∑ σ : Config n, ∑ τ : Config n, Real.exp
      (∑ i, (spin n σ i * x i + spin n τ i * y i + ℓ * spin n σ i * spin n τ i))) = _ from H]
  simp_rw [coupledSite_spin_sum]

/-- At zero interpolation time the interacting partition function separates over sites. -/
theorem lambdaCoupledBase_time_zero (n : ℕ) (U : EnergySpace n) (h ℓ : ℝ)
    (x y : Fin n → ℝ) :
    lambdaCoupledBase n U h 0 ℓ x y =
      n * (2 * Real.log 2) + ∑ i, coupledSite ℓ (x i + h) (y i + h) := by
  have he (σ τ : Config n) : guerraH n U h 0 x σ + guerraH n U h 0 y τ +
      ℓ * ∑ i, spin n σ i * spin n τ i =
      ∑ i, (spin n σ i * (x i + h) + spin n τ i * (y i + h) +
        ℓ * spin n σ i * spin n τ i) := by
    simp only [guerraH, Real.sqrt_zero, zero_mul, sub_zero, Real.sqrt_one, one_mul,
      zero_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp only [lambdaCoupledBase, he]
  rw [pairSpinSum_exp, Real.log_prod (fun i _ =>
    (mul_pos (by norm_num : (0 : ℝ) < 4) (coupledSiteZ_pos ℓ (x i + h) (y i + h))).ne')]
  simp_rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (coupledSiteZ_pos ℓ _ _).ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  simp [h4, Finset.sum_add_distrib, coupledSite]

/-- The overlap penalty comparison preceding (5.16), valid for every real lambda. -/
theorem constrainedBase_le_lambda {n : ℕ} (hn : 0 < n) (U : EnergySpace n) (h t u ℓ : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    constrainedBase n U h t u x y ≤ -ℓ * n * u + lambdaCoupledBase n U h t ℓ x y := by
  have hp : 0 < ∑ σ : Config n, ∑ τ : Config n,
      Real.exp (guerraH n U h t x σ + guerraH n U h t y τ +
        ℓ * ∑ i, spin n σ i * spin n τ i) :=
    Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => Real.exp_pos _)
      Finset.univ_nonempty) Finset.univ_nonempty
  have H : constrainedZ n U h t u x y ≤ Real.exp (-ℓ * n * u) *
      ∑ σ : Config n, ∑ τ : Config n,
        Real.exp (guerraH n U h t x σ + guerraH n U h t y τ +
          ℓ * ∑ i, spin n σ i * spin n τ i) := by
    simp only [constrainedZ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    apply Finset.sum_le_sum
    intro τ _
    split_ifs with hστ
    · have hs : ∑ i, spin n σ i * spin n τ i = (n : ℝ) * u := by
        rw [AT.spin_sum_eq_mul_overlap hn, hστ]
      rw [← Finset.mul_sum, hs, ← Real.exp_add]
      apply le_of_eq
      congr 1
      ring
    · positivity
  have Hlog := Real.log_le_log (constrainedZ_pos U h t u hu x y) H
  rw [Real.log_mul (Real.exp_ne_zero _) hp.ne', Real.log_exp] at Hlog
  exact Hlog

/-- The deterministic endpoint bound underlying (5.17), with its exact `2 log 2` normalization. -/
theorem constrainedBase_time_zero_le {n : ℕ} (hn : 0 < n) (U : EnergySpace n)
    (h u ℓ : ℝ) (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    constrainedBase n U h 0 u x y ≤ n * (2 * Real.log 2 - ℓ * u) +
      ∑ i, coupledSite ℓ (x i + h) (y i + h) := by
  have H := constrainedBase_le_lambda hn U h 0 u ℓ hu x y
  rw [lambdaCoupledBase_time_zero] at H
  nlinarith

/-- The comparison is preserved by the actual independent/shared Gaussian cascade. -/
theorem constrainedCascade_le_lambda {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h u ℓ : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : ∃ σ τ : Config n, overlap n σ τ = u)
    (d j : ℕ) (x y : Fin n → ℝ) :
    coupledCascade n s β d (constrainedBase n U h t u) j x y ≤
      -ℓ * n * u + coupledCascade n s β d (lambdaCoupledBase n U h t ℓ) j x y := by
  have hL := lambdaCoupledBase_growth n U h ℓ ht
  have H := coupledCascade_mono s β d j (constrainedBase_growth U h u ht hu)
    (hL.const_add (-ℓ * n * u)) (constrainedBase_le_lambda hn U h t u ℓ hu) x y
  rwa [coupledCascade_const_add s β _ d j hL] at H

/-- Lambda stability is independent of the depth and split. -/
theorem lambdaCoupledCascade_dist_le {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h ℓ μ : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d j : ℕ) (x y : Fin n → ℝ) :
    |coupledCascade n s β d (lambdaCoupledBase n U h t ℓ) j x y -
      coupledCascade n s β d (lambdaCoupledBase n U h t μ) j x y| ≤ n * |ℓ - μ| :=
  coupledCascade_dist_le s β d j (lambdaCoupledBase_growth n U h ℓ ht)
    (lambdaCoupledBase_growth n U h μ ht) (lambdaCoupledBase_dist_le n U h t ℓ μ) x y

end SpinGlass.Targets
