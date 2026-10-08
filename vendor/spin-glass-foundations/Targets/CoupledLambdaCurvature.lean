module

/-
# Uniform lambda curvature for Talagrand's paired scalar recursion

RSAT supplies differentiation and continuity through each Gaussian transform.
The extra invariant E <= 1 - D^2 sharpens its depth-dependent bound: every
mass in [0,1] preserves this inequality. This gives Lemma 5.9 with constant 1
for the actual Section 5 recursion, without a factor in the number of levels.
-/
public import Targets.TalagrandSection5
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {P : Type*} [TopologicalSpace P]
variable {F D E : P → ℝ → ℝ × ℝ → ℝ}
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- A good triple with the sharper curvature invariant of a sign-valued observable. -/
structure UnitLambdaCurvature (F D E : P → ℝ → ℝ × ℝ → ℝ) : Prop where
  triple : GTFrame.GoodTriple F D E 1
  sharp : ∀ p l x, E p l x ≤ 1 - (D p l x) ^ 2

omit [TopologicalSpace P] in
theorem finiteStepD_eq_stepMD (m : ℝ) (a b : P → ℝ) (p : P) (l : ℝ) (x : ℝ × ℝ) :
    GTFrame.finiteStepD μ m a b F D p l x = GTFrame.stepMD μ m a b F D p l x := by
  by_cases hm : m = 0
  · simp [GTFrame.finiteStepD, GTFrame.stepMD, GTFrame.step0, hm]
  · simp only [GTFrame.finiteStepD, if_neg hm]

omit [TopologicalSpace P] in
theorem finiteStepDD_eq_stepMD (m : ℝ) (a b : P → ℝ) (p : P) (l : ℝ) (x : ℝ × ℝ) :
    GTFrame.finiteStepDD μ m a b F D E p l x =
      GTFrame.stepMD μ m a b F E p l x + m * GTFrame.stepMVar μ m a b F D p l x := by
  by_cases hm : m = 0
  · simp [GTFrame.finiteStepDD, GTFrame.stepMD, GTFrame.step0, hm]
  · simp only [GTFrame.finiteStepDD, if_neg hm]

/-- The sharp bound, rather than only a uniform bound on E, survives each step. -/
theorem UnitLambdaCurvature.finiteStep_sharp
    (h : UnitLambdaCurvature F D E) (hμ : GTFrame.ExpMoments μ)
    {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) (a b : P → ℝ)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    GTFrame.finiteStepDD μ m a b F D E p l x ≤
      1 - (GTFrame.finiteStepD μ m a b F D p l x) ^ 2 := by
  have hsq (p : P) (l : ℝ) (x : ℝ × ℝ) : |(D p l x) ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [h.triple.good.bddD p l x, abs_nonneg (D p l x)]
  have hiE := GTFrame.integrable_gexpShift hμ h.triple.good hm.1
    (h.triple.contE.comp (by fun_prop : Continuous fun z : ℝ =>
      ((p, l, (x.1 + a p * z, x.2 + b p * z)) : P × ℝ × (ℝ × ℝ))))
    (fun z => h.triple.absE p l _) p l (a p) (b p) x
  have hiD := GTFrame.integrable_gexpShift hμ h.triple.good hm.1
    ((h.triple.good.cont_shiftD p l (a p) (b p) x).pow 2)
    (fun z => hsq p l _) p l (a p) (b p) x
  have hAdd := integral_add hiE hiD
  simp only [Function.comp_apply, Pi.pow_apply] at hAdd
  have hsum : GTFrame.stepMD μ m a b F E p l x +
      GTFrame.stepMD μ m a b F (fun p l x => (D p l x) ^ 2) p l x ≤ 1 := by
    have H := GTFrame.stepMD_le (G := fun p l x => E p l x + (D p l x) ^ 2)
      hμ h.triple.good hm.1
      (h.triple.contE.add (h.triple.good.contD.pow 2))
      (c := 1) (fun p l x => by
        rw [abs_of_nonneg (add_nonneg (h.triple.nonnegE p l x) (sq_nonneg _))]
        linarith [h.sharp p l x]) (α := a) (β := b) p l x
    simpa only [GTFrame.stepMD, add_mul, hAdd, add_div] using H
  have hvar := GTFrame.stepMVar_nonneg hμ h.triple.good hm.1 (α := a) (β := b) p l x
  have hmul := mul_le_mul_of_nonneg_right hm.2 hvar
  rw [finiteStepDD_eq_stepMD, finiteStepD_eq_stepMD]
  dsimp only [GTFrame.stepMVar] at hmul
  dsimp only [GTFrame.stepMVar]
  linarith

/-- All analytic fields come from RSAT; only the strengthened bound is new. -/
theorem UnitLambdaCurvature.finiteStep [FirstCountableTopology P]
    (h : UnitLambdaCurvature F D E) (hμ : GTFrame.ExpMoments μ)
    {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) {a b : P → ℝ}
    (ha : Continuous a) (hb : Continuous b) :
    UnitLambdaCurvature (GTFrame.finiteStep μ m a b F)
      (GTFrame.finiteStepD μ m a b F D) (GTFrame.finiteStepDD μ m a b F D E) := by
  have H := GTFrame.goodTriple_finiteStep hμ h.triple hm.1 ha hb
  have hs := h.finiteStep_sharp hμ hm a b
  exact ⟨⟨H.good, H.contE, H.derivD, H.nonnegE,
    fun p l x => (hs p l x).trans (sub_le_self _ (sq_nonneg _))⟩, hs⟩

theorem unitLambdaCurvature_terminal :
    UnitLambdaCurvature (fun (_ : P) l x => coupledSite l x.1 x.2)
      (fun _ l x => GTFrame.fLbaseD l x) (fun _ l x => GTFrame.fLbaseDD l x) := by
  refine ⟨⟨?_, GTFrame.continuous_fLbaseDD.comp (by fun_prop),
    fun _ l x => GTFrame.hasDerivAt_fLbaseD l x,
    fun _ l x => GTFrame.fLbaseDD_nonneg l x,
    fun _ l x => GTFrame.fLbaseDD_le_one l x⟩, fun _ _ _ => le_rfl⟩
  simpa only [coupledSite_eq_gtTerminal, GTFrame.fLbase] using
    (GTFrame.goodFam_fLbase (P := P))

/-- The actual recursively differentiated second lambda derivative. -/
noncomputable def splitScalarCascadeDD (m : ℕ → ℝ) (v : ℕ → P → ℝ) (d : ℕ) :
    ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ l x => GTFrame.fLbaseDD l x
  | j + 1 => if j < d then
      GTFrame.finiteStepDD (gaussianReal 0 1) (m j) (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j))
        (GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j) (splitScalarCascadeD m v d j))
        (GTFrame.finiteStepDD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j)
          (splitScalarCascadeD m v d j) (splitScalarCascadeDD m v d j))
    else GTFrame.finiteStepDD (gaussianReal 0 1) (m j)
      (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p))
      (splitScalarCascade m v d j) (splitScalarCascadeD m v d j) (splitScalarCascadeDD m v d j)

theorem splitScalarCascade_unitCurvature [FirstCountableTopology P]
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, m j ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ j, Continuous (v j)) (d j : ℕ) :
    UnitLambdaCurvature (splitScalarCascade m v d j) (splitScalarCascadeD m v d j)
      (splitScalarCascadeDD m v d j) := by
  induction j with
  | zero => exact unitLambdaCurvature_terminal
  | succ j ih =>
    simp only [splitScalarCascade, splitScalarCascadeD, splitScalarCascadeDD]
    split_ifs
    · exact (ih.finiteStep (GTFrame.expMoments_gaussianReal 0 1)
        (hm j) continuous_const (hv j).sqrt).finiteStep
        (GTFrame.expMoments_gaussianReal 0 1) (hm j) (hv j).sqrt continuous_const
    · exact ih.finiteStep (GTFrame.expMoments_gaussianReal 0 1) (hm j) (hv j).sqrt (hv j).sqrt

theorem section5Mass_le_one {k : ℕ} (s : RSBScheme k) {m : ℝ} (hm : m ≤ 1)
    (r : ℕ) {p : ℕ} (hp : p ≤ k + 2) (hr : r ≤ k + 1) :
    section5Mass s r m p ≤ 1 := by
  unfold section5Mass
  split_ifs with hlt heq
  · have H := s.m_le_one (show p ≤ k + 1 by omega)
    linarith
  · exact hm
  · exact s.m_le_one (by omega)

/-- The actual second lambda derivative of V, with the sharp uniform invariant. -/
theorem section5V_second_derivative {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) (v l : ℝ) :
    ∃ e : ℝ, HasDerivAt (deriv (section5V s β h r m v)) e l ∧
      0 ≤ e ∧ e ≤ 1 - (deriv (section5V s β h r m v) l) ^ 2 := by
  have H := splitScalarCascade_unitCurvature
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5Variance s β r (k + 2 - j))
    (fun j => ⟨section5Mass_nonneg s hr hm.1 (by omega),
      section5Mass_le_one s hm.2 r (by omega) hr⟩)
    (fun j => section5Variance_continuous s β r (k + 2 - j)) (k + 3 - r) (k + 3)
  have hd : deriv (section5V s β h r m v) =
      fun l => splitScalarCascadeD (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5Variance s β r (k + 2 - j)) (k + 3 - r) (k + 3) v l (h, h) := by
    funext l
    exact (hasDerivAt_section5V s β h hr hm.1 v l).deriv
  rw [hd]
  exact ⟨_, H.triple.derivD v l (h, h), H.triple.nonnegE v l (h, h), H.sharp v l (h, h)⟩

/-- Talagrand Lemma 5.9 with constant 1, uniform in the level count and all parameters.
The actual second derivative is meant, not an independently postulated candidate. -/
theorem section5V_second_abs_le_one {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) (v l : ℝ) :
    |deriv (deriv (section5V s β h r m v)) l| ≤ 1 := by
  obtain ⟨e, he, h0, h1⟩ := section5V_second_derivative s β h hr hm v l
  rw [he.deriv, abs_of_nonneg h0]
  exact h1.trans (sub_le_self _ (sq_nonneg _))

/-- The precise baseline-mass specialization in Talagrand Lemma 5.9. -/
theorem talagrand_lemma_5_9 {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) (v l : ℝ) :
    |deriv (deriv (section5V s β h r (s.m (r - 1)) v)) l| ≤ 1 :=
  section5V_second_abs_le_one s β h hr
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩ v l

/-- A small tangent-quadratic adapter to Mathlib's convexity and minimum theorems. -/
theorem quadratic_upper_of_second_le_one {f d e : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (d x) x) (he : ∀ x, HasDerivAt d (e x) x)
    (hb : ∀ x, e x ≤ 1) (x : ℝ) :
    f x ≤ f 0 + d 0 * x + x ^ 2 / 2 := by
  let g : ℝ → ℝ := fun x => f 0 + d 0 * x + x ^ 2 / 2 - f x
  have hg (y : ℝ) : HasDerivAt g (d 0 + y - d y) y := by
    convert! (((hasDerivAt_const y (f 0)).add ((hasDerivAt_id y).const_mul (d 0))).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub (hd y) using 1
    simp
  have hg' : deriv g = fun y => d 0 + y - d y := funext fun y => (hg y).deriv
  have hg'' (y : ℝ) : HasDerivAt (deriv g) (1 - e y) y := by
    rw [hg']
    simpa only [zero_add, Pi.add_apply, Pi.sub_apply, id_eq] using!
      ((hasDerivAt_const y (d 0)).add (hasDerivAt_id y)).sub (he y)
  have hconv : ConvexOn ℝ Set.univ g := convexOn_univ_of_deriv2_nonneg
    (fun y => (hg y).differentiableAt) (fun y => (hg'' y).differentiableAt)
    (fun y => by simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      (hg'' y).deriv] using sub_nonneg.mpr (hb y))
  have hmin := hconv.isMinOn_of_rightDeriv_eq_zero (x := 0) (by simp)
    (by simpa using (hg 0).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
  have H := hmin (Set.mem_univ x)
  dsimp [g] at H
  nlinarith

/-- An explicit lambda gives the strict gain in (5.33), with constant 2.
Identification of the derivative at zero with U' (Lemma 5.8) is not assumed. -/
theorem section5V_lambda_gain {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr : r ≤ k + 1) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) (v u : ℝ) :
    ∃ l : ℝ, section5V s β h r m v l - l * u ≤
      section5V s β h r m v 0 - (deriv (section5V s β h r m v) 0 - u) ^ 2 / 2 := by
  let f := section5V s β h r m v
  have hfirst (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hasDerivAt_section5V s β h hr hm.1 v x).differentiableAt.hasDerivAt
  have hsecond (x : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    obtain ⟨e, he, _⟩ := section5V_second_derivative s β h hr hm v x
    exact he.differentiableAt.hasDerivAt
  have H := quadratic_upper_of_second_le_one hfirst hsecond
    (fun x => (le_abs_self _).trans (section5V_second_abs_le_one s β h hr hm v x))
    (u - deriv f 0)
  refine ⟨u - deriv f 0, ?_⟩
  change f (u - deriv f 0) - (u - deriv f 0) * u ≤ f 0 - (deriv f 0 - u) ^ 2 / 2
  nlinarith

end SpinGlass.Targets
