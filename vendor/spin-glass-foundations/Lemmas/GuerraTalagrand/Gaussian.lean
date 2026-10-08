module

public import Lemmas.AT.Definitions
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Gaussian estimates for the canonical GT recursion

This file uses the GT objects from `Lemmas.AT.Definitions`. Generic analytic transforms
are isolated in `GTFrame`; all GT-facing statements use the canonical terminal,
semigroup solution, Gaussian expectation, and functional.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-!
# Gaussian-type recursion framework and terminal function

This file develops the analytic machinery for Gaussian-type recursion steps and
instantiates it for the standard Gaussian measure and the two-replica terminal function.

The basic object is a family of functions
`F : P → ℝ → (ℝ × ℝ) → ℝ`, thought of as `F p λ x`, where `p` ranges over a parameter
space, `λ` is a distinguished real parameter that we want to differentiate in, and
`x` is a two-dimensional 'spatial' variable.

A family is *good* (`GoodFam F D`) when

* `F` and `D` are jointly continuous,
* `D` is the `λ`-derivative of `F`,
* `F p λ ·` is `1`-Lipschitz in each spatial coordinate,
* `|D| ≤ 1`.

The two 'recursion steps'

* `step0 μ α β F p λ x = ∫ z, F p λ (x.1 + α p * z, x.2 + β p * z) ∂μ`
* `stepM μ m α β F p λ x = (1/m) * log (∫ z, exp (m * F p λ (x.1 + α p * z, x.2 + β p * z)) ∂μ)`

both preserve goodness, provided `μ` is a probability measure with all exponential
moments.

Finally, the standard Gaussian measure is shown to have all exponential moments,
and the terminal function `fLbase`, together with its `lam`-derivative `fLbaseD`,
is shown to form a good family.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section

namespace GTFrame

/-! ### Measures with exponential moments -/

/-- A measure on `ℝ` such that `z ↦ exp (c * |z|)` is integrable for every `c`. -/
def ExpMoments (μ : Measure ℝ) : Prop :=
  ∀ c : ℝ, Integrable (fun z : ℝ => Real.exp (c * |z|)) μ

variable {μ : Measure ℝ}

lemma ExpMoments.integrable_abs (hμ : ExpMoments μ) :
    Integrable (fun z : ℝ => |z|) μ := by
  refine (hμ 1).mono (by fun_prop) ?_
  filter_upwards with z
  have h1 : |z| ≤ Real.exp (1 * |z|) := by
    rw [one_mul]
    linarith [Real.add_one_le_exp |z|]
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), abs_abs] using h1

lemma ExpMoments.integrable_linear (hμ : ExpMoments μ) [IsFiniteMeasure μ] (M A : ℝ) :
    Integrable (fun z : ℝ => M + A * |z|) μ :=
  (integrable_const M).add (hμ.integrable_abs.const_mul A)

lemma ExpMoments.integrable_of_bound (hμ : ExpMoments μ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g μ) {M A : ℝ} (h : ∀ z, |g z| ≤ M + A * |z|) :
    Integrable g μ := by
  refine (hμ.integrable_linear M A).mono hg ?_
  filter_upwards with z
  have h0 : (0:ℝ) ≤ M + A * |z| := le_trans (abs_nonneg _) (h z)
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h z

lemma ExpMoments.integrable_exp_linear (hμ : ExpMoments μ) (c M A : ℝ) :
    Integrable (fun z : ℝ => Real.exp (c * (M + A * |z|))) μ := by
  have := (hμ (c * A)).const_mul (Real.exp (c * M))
  refine this.congr ?_
  filter_upwards with z
  rw [← Real.exp_add]
  ring_nf

lemma ExpMoments.integrable_of_exp_bound (hμ : ExpMoments μ) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g μ) {c M A : ℝ}
    (h : ∀ z, |g z| ≤ Real.exp (c * (M + A * |z|))) :
    Integrable g μ := by
  refine (hμ.integrable_exp_linear c M A).mono hg ?_
  filter_upwards with z
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h z

/-! ### An elementary inequality for `exp` -/

lemma abs_exp_sub_exp_le (u v C : ℝ) (hu : u ≤ C) (hv : v ≤ C) :
    |Real.exp u - Real.exp v| ≤ Real.exp C * |u - v| := by
  wlog h : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u v]
    exact this v u hv hu (le_of_not_ge h)
  have hexp : Real.exp u - Real.exp v ≤ Real.exp C * (u - v) := by
    have h1 : Real.exp (v - u) ≥ 1 + (v - u) := by
      linarith [Real.add_one_le_exp (v - u)]
    have h2 : Real.exp v ≥ Real.exp u * (1 + (v - u)) := by
      have : Real.exp v = Real.exp u * Real.exp (v - u) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
    have h3 : Real.exp u - Real.exp v ≤ Real.exp u * (u - v) := by nlinarith
    have h4 : Real.exp u ≤ Real.exp C := Real.exp_le_exp.2 hu
    nlinarith [sub_nonneg.2 h]
  have h5 : 0 ≤ Real.exp u - Real.exp v := by
    simpa using Real.exp_le_exp.2 h
  rw [abs_of_nonneg h5, abs_of_nonneg (sub_nonneg.2 h)]
  exact hexp

/-! ### Good families -/

variable {P : Type*} [TopologicalSpace P]

/--
A *good family* is a pair `(F, D)` of functions of a parameter `p : P`, a distinguished
real parameter `l` (playing the role of `λ`) and a two-dimensional spatial variable `x`,
such that `F` and `D` are jointly continuous, `D` is the `l`-derivative of `F`, the map
`x ↦ F p l x` is `1`-Lipschitz in each coordinate, and `|D| ≤ 1`.
-/
structure GoodFam (F D : P → ℝ → ℝ × ℝ → ℝ) : Prop where
  contF : Continuous fun w : P × ℝ × (ℝ × ℝ) => F w.1 w.2.1 w.2.2
  contD : Continuous fun w : P × ℝ × (ℝ × ℝ) => D w.1 w.2.1 w.2.2
  hasDeriv : ∀ p l x, HasDerivAt (fun l' => F p l' x) (D p l x) l
  lipx : ∀ p l x y, |F p l x - F p l y| ≤ |x.1 - y.1| + |x.2 - y.2|
  bddD : ∀ p l x, |D p l x| ≤ 1

namespace GoodFam

variable {F D : P → ℝ → ℝ × ℝ → ℝ}

lemma contF_pt (h : GoodFam F D) (p : P) (l : ℝ) : Continuous fun x : ℝ × ℝ => F p l x := by
  have hc : Continuous fun x : ℝ × ℝ => ((p, l, x) : P × ℝ × (ℝ × ℝ)) := by fun_prop
  exact h.contF.comp hc

lemma contD_pt (h : GoodFam F D) (p : P) (l : ℝ) : Continuous fun x : ℝ × ℝ => D p l x := by
  have hc : Continuous fun x : ℝ × ℝ => ((p, l, x) : P × ℝ × (ℝ × ℝ)) := by fun_prop
  exact h.contD.comp hc

/-- `F` is `1`-Lipschitz in the distinguished parameter `l`. -/
lemma lipl (h : GoodFam F D) (p : P) (l l' : ℝ) (x : ℝ × ℝ) :
    |F p l x - F p l' x| ≤ |l - l'| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => F p t x) (f' := fun t => D p t x) (s := Set.univ) (C := 1)
    (fun t _ => (h.hasDeriv p t x).hasDerivWithinAt)
    (fun t _ => by simpa using h.bddD p t x) convex_univ (Set.mem_univ l') (Set.mem_univ l)
  simpa [Real.norm_eq_abs] using this

/-- The shifted integrand is continuous in `z`. -/
lemma cont_shift (h : GoodFam F D) (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Continuous fun z : ℝ => F p l (x.1 + a * z, x.2 + b * z) := by
  have hc : Continuous fun z : ℝ => ((p, l, (x.1 + a * z, x.2 + b * z)) : P × ℝ × (ℝ × ℝ)) := by
    fun_prop
  exact h.contF.comp hc

lemma cont_shiftD (h : GoodFam F D) (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Continuous fun z : ℝ => D p l (x.1 + a * z, x.2 + b * z) := by
  have hc : Continuous fun z : ℝ => ((p, l, (x.1 + a * z, x.2 + b * z)) : P × ℝ × (ℝ × ℝ)) := by
    fun_prop
  exact h.contD.comp hc

/-- A linear-growth bound for the shifted integrand. -/
lemma bound_shift (h : GoodFam F D) (p : P) (l a b : ℝ) (x : ℝ × ℝ) (z : ℝ) :
    |F p l (x.1 + a * z, x.2 + b * z)| ≤ |F p l x| + (|a| + |b|) * |z| := by
  have key := h.lipx p l (x.1 + a * z, x.2 + b * z) x
  have e1 : ((x.1 + a * z, x.2 + b * z) : ℝ × ℝ).1 - x.1 = a * z := by simp
  have e2 : ((x.1 + a * z, x.2 + b * z) : ℝ × ℝ).2 - x.2 = b * z := by simp
  rw [e1, e2] at key
  have h1 : |a * z| + |b * z| = (|a| + |b|) * |z| := by
    rw [abs_mul, abs_mul]; ring
  have h2 := abs_sub_abs_le_abs_sub (F p l (x.1 + a * z, x.2 + b * z)) (F p l x)
  linarith

/-- A linear-growth bound, uniform for `l` in a unit ball around `l₀`. -/
lemma bound_shift_unif (h : GoodFam F D) (p : P) (l₀ l a b : ℝ) (hl : |l - l₀| ≤ 1)
    (x : ℝ × ℝ) (z : ℝ) :
    |F p l (x.1 + a * z, x.2 + b * z)| ≤ (|F p l₀ x| + 1) + (|a| + |b|) * |z| := by
  have h1 := h.bound_shift p l a b x z
  have h2 : |F p l x| ≤ |F p l₀ x| + 1 := by
    have := h.lipl p l l₀ x
    have := abs_sub_abs_le_abs_sub (F p l x) (F p l₀ x)
    linarith
  linarith

end GoodFam

/-! ### Integrability of the shifted integrands -/

variable {F D : P → ℝ → ℝ × ℝ → ℝ}

lemma GoodFam.integrable_shift (h : GoodFam F D) (hμ : ExpMoments μ) [IsFiniteMeasure μ]
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => F p l (x.1 + a * z, x.2 + b * z)) μ :=
  hμ.integrable_of_bound (h.cont_shift p l a b x).aestronglyMeasurable (h.bound_shift p l a b x)

lemma GoodFam.integrable_shiftD (h : GoodFam F D) [IsFiniteMeasure μ]
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => D p l (x.1 + a * z, x.2 + b * z)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (h.cont_shiftD p l a b x).aestronglyMeasurable ?_
  filter_upwards with z
  simpa [Real.norm_eq_abs] using h.bddD p l _

/-! ### The `m = 0` step -/

/-- One Gaussian averaging step, corresponding to `m = 0` in the recursion. -/
def step0 (μ : Measure ℝ) (α β : P → ℝ) (G : P → ℝ → ℝ × ℝ → ℝ) : P → ℝ → ℝ × ℝ → ℝ :=
  fun p l x => ∫ z, G p l (x.1 + α p * z, x.2 + β p * z) ∂μ

omit [TopologicalSpace P] in
lemma step0_apply (μ : Measure ℝ) (α β : P → ℝ) (G : P → ℝ → ℝ × ℝ → ℝ)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    step0 μ α β G p l x = ∫ z, G p l (x.1 + α p * z, x.2 + β p * z) ∂μ := rfl

/-- A local domination hypothesis used to prove continuity of `step0`. -/
def LocDom (α β : P → ℝ) (G : P → ℝ → ℝ × ℝ → ℝ) : Prop :=
  ∀ w₀ : P × ℝ × (ℝ × ℝ), ∃ M A : ℝ, ∀ᶠ w in 𝓝 w₀, ∀ z : ℝ,
    |G w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)| ≤ M + A * |z|

lemma locDom_of_lipx {α β : P → ℝ} (hα : Continuous α) (hβ : Continuous β)
    (h : GoodFam F D) : LocDom α β F := by
  intro w₀
  refine ⟨|F w₀.1 w₀.2.1 w₀.2.2| + 1, |α w₀.1| + |β w₀.1| + 2, ?_⟩
  have hc1 : ContinuousAt (fun w : P × ℝ × (ℝ × ℝ) => |F w.1 w.2.1 w.2.2|) w₀ :=
    (continuous_abs.comp h.contF).continuousAt
  have hc2 : ContinuousAt (fun w : P × ℝ × (ℝ × ℝ) => |α w.1|) w₀ :=
    (continuous_abs.comp (hα.comp continuous_fst)).continuousAt
  have hc3 : ContinuousAt (fun w : P × ℝ × (ℝ × ℝ) => |β w.1|) w₀ :=
    (continuous_abs.comp (hβ.comp continuous_fst)).continuousAt
  have e1 : ∀ᶠ w in 𝓝 w₀, |F w.1 w.2.1 w.2.2| < |F w₀.1 w₀.2.1 w₀.2.2| + 1 :=
    Filter.eventually_iff.2 (hc1 (Iio_mem_nhds (by linarith)))
  have e2 : ∀ᶠ w in 𝓝 w₀, |α w.1| < |α w₀.1| + 1 :=
    Filter.eventually_iff.2 (hc2 (Iio_mem_nhds (by linarith)))
  have e3 : ∀ᶠ w in 𝓝 w₀, |β w.1| < |β w₀.1| + 1 :=
    Filter.eventually_iff.2 (hc3 (Iio_mem_nhds (by linarith)))
  filter_upwards [e1, e2, e3] with w hw1 hw2 hw3 z
  have hb := h.bound_shift w.1 w.2.1 (α w.1) (β w.1) w.2.2 z
  have hz : (0:ℝ) ≤ |z| := abs_nonneg z
  nlinarith [hb]

lemma locDom_of_bddD {α β : P → ℝ} (h : GoodFam F D) : LocDom α β D := by
  intro w₀
  refine ⟨1, 0, ?_⟩
  filter_upwards with w z
  simpa using h.bddD w.1 w.2.1 _

lemma continuous_step0 (hμ : ExpMoments μ) [IsProbabilityMeasure μ] [FirstCountableTopology P]
    {G : P → ℝ → ℝ × ℝ → ℝ} {α β : P → ℝ}
    (hG : Continuous fun w : P × ℝ × (ℝ × ℝ) => G w.1 w.2.1 w.2.2)
    (hα : Continuous α) (hβ : Continuous β) (hbd : LocDom α β G) :
    Continuous fun w : P × ℝ × (ℝ × ℝ) => step0 μ α β G w.1 w.2.1 w.2.2 := by
  rw [continuous_iff_continuousAt]
  intro w₀
  obtain ⟨M, A, hU⟩ := hbd w₀
  have hshift : ∀ z : ℝ, Continuous fun w : P × ℝ × (ℝ × ℝ) =>
      G w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z) := by
    intro z
    have hc : Continuous fun w : P × ℝ × (ℝ × ℝ) =>
        ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ)) := by
      fun_prop
    exact hG.comp hc
  refine continuousAt_of_dominated (bound := fun z => M + A * |z|) ?_ ?_
    (hμ.integrable_linear M A) ?_
  · filter_upwards with w
    exact ((hG.comp (by fun_prop : Continuous fun z : ℝ =>
      ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ))))).aestronglyMeasurable
  · filter_upwards [hU] with w hw
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hw z
  · filter_upwards with z
    exact (hshift z).continuousAt


lemma hasDeriv_step0 (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    {α β : P → ℝ} (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => step0 μ α β F p l' x) (step0 μ α β D p l x) l := by
  have hlip : ∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs 1)
      (fun l' => F p l' (x.1 + α p * z, x.2 + β p * z)) (Metric.ball l 1) := by
    filter_upwards with z
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u _ v _
    have := h.lipl p u v (x.1 + α p * z, x.2 + β p * z)
    simpa [Real.dist_eq] using this
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun l' z => F p l' (x.1 + α p * z, x.2 + β p * z))
    (F' := fun z => D p l (x.1 + α p * z, x.2 + β p * z))
    (x₀ := l) (bound := fun _ : ℝ => (1:ℝ)) (s := Metric.ball l 1)
    (Metric.ball_mem_nhds l one_pos)
    (Filter.Eventually.of_forall fun l' => (h.cont_shift p l' (α p) (β p) x).aestronglyMeasurable)
    (h.integrable_shift hμ p l (α p) (β p) x)
    (h.cont_shiftD p l (α p) (β p) x).aestronglyMeasurable
    hlip (integrable_const 1)
    (Filter.Eventually.of_forall fun z => h.hasDeriv p l (x.1 + α p * z, x.2 + β p * z))
  exact key.2

lemma lipx_step0 (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    {α β : P → ℝ} (p : P) (l : ℝ) (x y : ℝ × ℝ) :
    |step0 μ α β F p l x - step0 μ α β F p l y| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  have hi1 := h.integrable_shift hμ p l (α p) (β p) x
  have hi2 := h.integrable_shift hμ p l (α p) (β p) y
  have hpt : ∀ z : ℝ,
      |F p l (x.1 + α p * z, x.2 + β p * z) - F p l (y.1 + α p * z, y.2 + β p * z)|
        ≤ |x.1 - y.1| + |x.2 - y.2| := by
    intro z
    have := h.lipx p l (x.1 + α p * z, x.2 + β p * z) (y.1 + α p * z, y.2 + β p * z)
    have e1 : x.1 + α p * z - (y.1 + α p * z) = x.1 - y.1 := by ring
    have e2 : x.2 + β p * z - (y.2 + β p * z) = x.2 - y.2 := by ring
    simpa [e1, e2] using this
  simp only [step0]
  rw [← integral_sub hi1 hi2]
  calc |∫ z, (F p l (x.1 + α p * z, x.2 + β p * z) - F p l (y.1 + α p * z, y.2 + β p * z)) ∂μ|
      ≤ ∫ z, |F p l (x.1 + α p * z, x.2 + β p * z) - F p l (y.1 + α p * z, y.2 + β p * z)| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := μ) (fun z => F p l (x.1 + α p * z, x.2 + β p * z)
            - F p l (y.1 + α p * z, y.2 + β p * z))
    _ ≤ ∫ _z : ℝ, (|x.1 - y.1| + |x.2 - y.2|) ∂μ :=
        integral_mono (hi1.sub hi2).abs (integrable_const _) hpt
    _ = |x.1 - y.1| + |x.2 - y.2| := by simp

lemma bddD_step0 [IsProbabilityMeasure μ] (h : GoodFam F D)
    {α β : P → ℝ} (p : P) (l : ℝ) (x : ℝ × ℝ) :
    |step0 μ α β D p l x| ≤ 1 := by
  have hi := h.integrable_shiftD (μ := μ) p l (α p) (β p) x
  simp only [step0]
  calc |∫ z, D p l (x.1 + α p * z, x.2 + β p * z) ∂μ|
      ≤ ∫ z, |D p l (x.1 + α p * z, x.2 + β p * z)| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := μ) (fun z => D p l (x.1 + α p * z, x.2 + β p * z))
    _ ≤ ∫ _z : ℝ, (1:ℝ) ∂μ :=
        integral_mono hi.abs (integrable_const _) (fun z => h.bddD p l _)
    _ = 1 := by simp

/-- The `m = 0` step preserves goodness. -/
theorem step0_good (hμ : ExpMoments μ) [IsProbabilityMeasure μ] [FirstCountableTopology P]
    (h : GoodFam F D) {α β : P → ℝ} (hα : Continuous α) (hβ : Continuous β) :
    GoodFam (step0 μ α β F) (step0 μ α β D) where
  contF := continuous_step0 hμ h.contF hα hβ (locDom_of_lipx hα hβ h)
  contD := continuous_step0 hμ h.contD hα hβ (locDom_of_bddD h)
  hasDeriv := fun p l x => hasDeriv_step0 hμ h p l x
  lipx := fun p l x y => lipx_step0 hμ h p l x y
  bddD := fun p l x => bddD_step0 h p l x


/-! ### A general continuity criterion for parametric integrals -/

lemma continuous_integral_of_locdom {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {g : X → ℝ → ℝ} (hg : ∀ w, Continuous (g w)) (hgw : ∀ z, Continuous fun w => g w z)
    (hdom : ∀ w₀ : X, ∃ bound : ℝ → ℝ, Integrable bound μ ∧
      ∀ᶠ w in 𝓝 w₀, ∀ z, |g w z| ≤ bound z) :
    Continuous fun w => ∫ z, g w z ∂μ := by
  rw [continuous_iff_continuousAt]
  intro w₀
  obtain ⟨bound, hbi, hb⟩ := hdom w₀
  refine continuousAt_of_dominated
    (Filter.Eventually.of_forall fun w => (hg w).aestronglyMeasurable) ?_ hbi ?_
  · filter_upwards [hb] with w hw
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hw z
  · filter_upwards with z
    exact (hgw z).continuousAt

/-! ### The `m > 0` step -/

/-- One log-exp Gaussian step with parameter `m`. -/
def stepM (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ) (G : P → ℝ → ℝ × ℝ → ℝ) :
    P → ℝ → ℝ × ℝ → ℝ :=
  fun p l x => (1 / m) *
    Real.log (∫ z, Real.exp (m * G p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)

/-- The `l`-derivative of `stepM`. -/
def stepMD (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ) (G E : P → ℝ → ℝ × ℝ → ℝ) :
    P → ℝ → ℝ × ℝ → ℝ :=
  fun p l x =>
    (∫ z, E p l (x.1 + α p * z, x.2 + β p * z) *
        Real.exp (m * G p l (x.1 + α p * z, x.2 + β p * z)) ∂μ) /
    (∫ z, Real.exp (m * G p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)

omit [TopologicalSpace P] in
lemma stepM_apply (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ) (G : P → ℝ → ℝ × ℝ → ℝ)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    stepM μ m α β G p l x =
      (1 / m) * Real.log (∫ z, Real.exp (m * G p l (x.1 + α p * z, x.2 + β p * z)) ∂μ) := rfl

section StepM

variable {m : ℝ}

lemma cont_expShift (h : GoodFam F D) (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Continuous fun z : ℝ => Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) :=
  Real.continuous_exp.comp (continuous_const.mul (h.cont_shift p l a b x))

lemma integrable_expShift (hμ : ExpMoments μ) (h : GoodFam F D) (hm : 0 ≤ m)
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))) μ := by
  refine hμ.integrable_of_exp_bound (c := m) (M := |F p l x|) (A := |a| + |b|)
    (cont_expShift h p l a b x).aestronglyMeasurable ?_
  intro z
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.2 ?_
  have h1 := h.bound_shift p l a b x z
  have h2 := le_abs_self (F p l (x.1 + a * z, x.2 + b * z))
  nlinarith

lemma integrable_DexpShift (hμ : ExpMoments μ) (h : GoodFam F D) (hm : 0 ≤ m)
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => D p l (x.1 + a * z, x.2 + b * z) *
      Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))) μ := by
  refine hμ.integrable_of_exp_bound (c := m) (M := |F p l x|) (A := |a| + |b|)
    (((h.cont_shiftD p l a b x).mul (cont_expShift h p l a b x))).aestronglyMeasurable ?_
  intro z
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hD := h.bddD p l (x.1 + a * z, x.2 + b * z)
  have hle : Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))
      ≤ Real.exp (m * (|F p l x| + (|a| + |b|) * |z|)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 := h.bound_shift p l a b x z
    have h2 := le_abs_self (F p l (x.1 + a * z, x.2 + b * z))
    nlinarith
  nlinarith [Real.exp_pos (m * F p l (x.1 + a * z, x.2 + b * z)),
    Real.exp_pos (m * (|F p l x| + (|a| + |b|) * |z|)), abs_nonneg (D p l (x.1 + a*z, x.2+b*z))]

lemma integral_expShift_pos (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    (hm : 0 ≤ m) (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    0 < ∫ z, Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le)
    (integrable_expShift hμ h hm p l a b x)]
  have hsupp : (Function.support fun z => Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)))
      = Set.univ := by
    ext z; simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [hsupp]
  simp

end StepM


section StepM2

variable {m : ℝ} {α β : P → ℝ}

lemma continuous_intExp (hμ : ExpMoments μ) [FirstCountableTopology P]
    (h : GoodFam F D) (hm : 0 ≤ m) (hα : Continuous α) (hβ : Continuous β) :
    Continuous fun w : P × ℝ × (ℝ × ℝ) =>
      ∫ z, Real.exp (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) ∂μ := by
  refine continuous_integral_of_locdom
    (fun w => cont_expShift h w.1 w.2.1 (α w.1) (β w.1) w.2.2) (fun z => ?_) (fun w₀ => ?_)
  · have hc : Continuous fun w : P × ℝ × (ℝ × ℝ) =>
        ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ)) := by
      fun_prop
    exact Real.continuous_exp.comp (continuous_const.mul (h.contF.comp hc))
  · obtain ⟨M, A, hU⟩ := locDom_of_lipx hα hβ h w₀
    refine ⟨fun z => Real.exp (m * (M + A * |z|)), hμ.integrable_exp_linear m M A, ?_⟩
    filter_upwards [hU] with w hw z
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.2 ?_
    have h1 := hw z
    have h2 := le_abs_self (F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))
    nlinarith

lemma continuous_intDexp (hμ : ExpMoments μ) [FirstCountableTopology P]
    (h : GoodFam F D) (hm : 0 ≤ m) (hα : Continuous α) (hβ : Continuous β) :
    Continuous fun w : P × ℝ × (ℝ × ℝ) =>
      ∫ z, D w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z) *
        Real.exp (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) ∂μ := by
  refine continuous_integral_of_locdom
    (fun w => (h.cont_shiftD w.1 w.2.1 (α w.1) (β w.1) w.2.2).mul
      (cont_expShift h w.1 w.2.1 (α w.1) (β w.1) w.2.2)) (fun z => ?_) (fun w₀ => ?_)
  · have hc : Continuous fun w : P × ℝ × (ℝ × ℝ) =>
        ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ)) := by
      fun_prop
    exact (h.contD.comp hc).mul (Real.continuous_exp.comp (continuous_const.mul (h.contF.comp hc)))
  · obtain ⟨M, A, hU⟩ := locDom_of_lipx hα hβ h w₀
    refine ⟨fun z => Real.exp (m * (M + A * |z|)), hμ.integrable_exp_linear m M A, ?_⟩
    filter_upwards [hU] with w hw z
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hD := h.bddD w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)
    have hle : Real.exp (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))
        ≤ Real.exp (m * (M + A * |z|)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 := hw z
      have h2 := le_abs_self (F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))
      nlinarith
    nlinarith [Real.exp_pos (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)),
      Real.exp_pos (m * (M + A * |z|)),
      abs_nonneg (D w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))]

lemma hasDeriv_intExp (hμ : ExpMoments μ) (h : GoodFam F D) (hm : 0 < m)
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => ∫ z, Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z)) ∂μ)
      (m * ∫ z, D p l (x.1 + a * z, x.2 + b * z) *
        Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) ∂μ) l := by
  set M := |F p l x| + 1 with hM
  set A := |a| + |b| with hA
  have hlip : ∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs (m * Real.exp (m * (M + A * |z|))))
      (fun l' => Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z))) (Metric.ball l 1) := by
    filter_upwards with z
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    have hu1 : |u - l| ≤ 1 := by
      have := Metric.mem_ball.1 hu; rw [Real.dist_eq] at this; linarith
    have hv1 : |v - l| ≤ 1 := by
      have := Metric.mem_ball.1 hv; rw [Real.dist_eq] at this; linarith
    have hbu : m * F p u (x.1 + a * z, x.2 + b * z) ≤ m * (M + A * |z|) := by
      have h1 := h.bound_shift_unif p l u a b hu1 x z
      have h2 := le_abs_self (F p u (x.1 + a * z, x.2 + b * z))
      nlinarith
    have hbv : m * F p v (x.1 + a * z, x.2 + b * z) ≤ m * (M + A * |z|) := by
      have h1 := h.bound_shift_unif p l v a b hv1 x z
      have h2 := le_abs_self (F p v (x.1 + a * z, x.2 + b * z))
      nlinarith
    have hE := abs_exp_sub_exp_le _ _ (m * (M + A * |z|)) hbu hbv
    have hdiff : |m * F p u (x.1 + a * z, x.2 + b * z) - m * F p v (x.1 + a * z, x.2 + b * z)|
        ≤ m * |u - v| := by
      have := h.lipl p u v (x.1 + a * z, x.2 + b * z)
      rw [← mul_sub, abs_mul, abs_of_pos hm]
      exact mul_le_mul_of_nonneg_left this hm.le
    have hcoe : ((Real.nnabs (m * Real.exp (m * (M + A * |z|))) : NNReal) : ℝ)
        = m * Real.exp (m * (M + A * |z|)) := by
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
    rw [Real.dist_eq, Real.dist_eq, hcoe]
    calc |Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
            - Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))|
        ≤ Real.exp (m * (M + A * |z|)) *
            |m * F p u (x.1 + a * z, x.2 + b * z) - m * F p v (x.1 + a * z, x.2 + b * z)| := hE
      _ ≤ Real.exp (m * (M + A * |z|)) * (m * |u - v|) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)
      _ = m * Real.exp (m * (M + A * |z|)) * |u - v| := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun l' z => Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z)))
    (F' := fun z => Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) *
      (m * D p l (x.1 + a * z, x.2 + b * z)))
    (x₀ := l) (bound := fun z => m * Real.exp (m * (M + A * |z|))) (s := Metric.ball l 1)
    (Metric.ball_mem_nhds l one_pos)
    (Filter.Eventually.of_forall fun l' => (cont_expShift h p l' a b x).aestronglyMeasurable)
    (integrable_expShift hμ h hm.le p l a b x)
    (((cont_expShift h p l a b x).mul
      (continuous_const.mul (h.cont_shiftD p l a b x))).aestronglyMeasurable)
    hlip ((hμ.integrable_exp_linear m M A).const_mul m)
    (Filter.Eventually.of_forall fun z =>
      (HasDerivAt.const_mul m (h.hasDeriv p l (x.1 + a * z, x.2 + b * z))).exp)
  have hrw : (∫ z, Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) *
        (m * D p l (x.1 + a * z, x.2 + b * z)) ∂μ)
      = m * ∫ z, D p l (x.1 + a * z, x.2 + b * z) *
        Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [← hrw]
  exact key.2

lemma hasDeriv_stepM (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D) (hm : 0 < m)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => stepM μ m α β F p l' x) (stepMD μ m α β F D p l x) l := by
  have hpos := integral_expShift_pos hμ h hm.le p l (α p) (β p) x
  have hI := hasDeriv_intExp hμ h hm p l (α p) (β p) x
  have key := HasDerivAt.const_mul (1 / m) (hI.log hpos.ne')
  have e : (1 / m) * ((m * ∫ z, D p l (x.1 + α p * z, x.2 + β p * z) *
        Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ) /
      (∫ z, Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ))
      = stepMD μ m α β F D p l x := by
    have gen : ∀ N I : ℝ, I ≠ 0 → (1 / m) * ((m * N) / I) = N / I := by
      intro N I hI
      field_simp
    simp only [stepMD]
    exact gen _ _ hpos.ne'
  rw [e] at key
  exact key

lemma bddD_stepM (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D) (hm : 0 < m)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    |stepMD μ m α β F D p l x| ≤ 1 := by
  have hpos := integral_expShift_pos hμ h hm.le p l (α p) (β p) x
  have hnum : |∫ z, D p l (x.1 + α p * z, x.2 + β p * z) *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ|
      ≤ ∫ z, Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ := by
    calc |∫ z, D p l (x.1 + α p * z, x.2 + β p * z) *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ|
        ≤ ∫ z, |D p l (x.1 + α p * z, x.2 + β p * z) *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))| ∂μ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ)
            (fun z => D p l (x.1 + α p * z, x.2 + β p * z) *
              Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)))
      _ ≤ ∫ z, Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ := by
          refine integral_mono (integrable_DexpShift hμ h hm.le p l (α p) (β p) x).abs
            (integrable_expShift hμ h hm.le p l (α p) (β p) x) (fun z => ?_)
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          nlinarith [h.bddD p l (x.1 + α p * z, x.2 + β p * z),
            Real.exp_pos (m * F p l (x.1 + α p * z, x.2 + β p * z)),
            abs_nonneg (D p l (x.1 + α p * z, x.2 + β p * z))]
  simp only [stepMD, abs_div, abs_of_pos hpos]
  exact div_le_one_of_le₀ hnum hpos.le

lemma lipx_stepM (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D) (hm : 0 < m)
    (p : P) (l : ℝ) (x y : ℝ × ℝ) :
    |stepM μ m α β F p l x - stepM μ m α β F p l y| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  have main : ∀ u v : ℝ × ℝ, stepM μ m α β F p l u
      ≤ (|u.1 - v.1| + |u.2 - v.2|) + stepM μ m α β F p l v := by
    intro u v
    set d := |u.1 - v.1| + |u.2 - v.2| with hd
    have hd0 : 0 ≤ d := by positivity
    have hIu := integral_expShift_pos hμ h hm.le p l (α p) (β p) u
    have hIv := integral_expShift_pos hμ h hm.le p l (α p) (β p) v
    have hpt : ∀ z : ℝ, Real.exp (m * F p l (u.1 + α p * z, u.2 + β p * z))
        ≤ Real.exp (m * d) * Real.exp (m * F p l (v.1 + α p * z, v.2 + β p * z)) := by
      intro z
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hl := h.lipx p l (u.1 + α p * z, u.2 + β p * z) (v.1 + α p * z, v.2 + β p * z)
      have e1 : u.1 + α p * z - (v.1 + α p * z) = u.1 - v.1 := by ring
      have e2 : u.2 + β p * z - (v.2 + β p * z) = u.2 - v.2 := by ring
      simp only [e1, e2] at hl
      have h2 := le_abs_self (F p l (u.1 + α p * z, u.2 + β p * z)
        - F p l (v.1 + α p * z, v.2 + β p * z))
      nlinarith
    have hmono : (∫ z, Real.exp (m * F p l (u.1 + α p * z, u.2 + β p * z)) ∂μ)
        ≤ Real.exp (m * d) * ∫ z, Real.exp (m * F p l (v.1 + α p * z, v.2 + β p * z)) ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono (integrable_expShift hμ h hm.le p l (α p) (β p) u)
        ((integrable_expShift hμ h hm.le p l (α p) (β p) v).const_mul _) hpt
    have hlog : Real.log (∫ z, Real.exp (m * F p l (u.1 + α p * z, u.2 + β p * z)) ∂μ)
        ≤ m * d + Real.log (∫ z, Real.exp (m * F p l (v.1 + α p * z, v.2 + β p * z)) ∂μ) := by
      have := Real.log_le_log hIu hmono
      rwa [Real.log_mul (Real.exp_ne_zero _) hIv.ne', Real.log_exp] at this
    simp only [stepM]
    have hm' : 0 < 1 / m := by positivity
    have := mul_le_mul_of_nonneg_left hlog hm'.le
    calc (1/m) * Real.log (∫ z, Real.exp (m * F p l (u.1 + α p * z, u.2 + β p * z)) ∂μ)
        ≤ (1/m) * (m * d + Real.log (∫ z, Real.exp (m * F p l (v.1 + α p * z, v.2 + β p * z)) ∂μ)) := this
      _ = d + (1/m) * Real.log (∫ z, Real.exp (m * F p l (v.1 + α p * z, v.2 + β p * z)) ∂μ) := by
          have gen : ∀ L : ℝ, (1 / m) * (m * d + L) = d + (1 / m) * L := by
            intro L
            field_simp
          exact gen _
  have h1 := main x y
  have h2 := main y x
  rw [abs_sub_le_iff]
  constructor
  · linarith [h1]
  · have e1 : |y.1 - x.1| = |x.1 - y.1| := abs_sub_comm _ _
    have e2 : |y.2 - x.2| = |x.2 - y.2| := abs_sub_comm _ _
    rw [e1, e2] at h2
    linarith [h2]

/-- The `m > 0` step preserves goodness. -/
theorem stepM_good (hμ : ExpMoments μ) [IsProbabilityMeasure μ] [FirstCountableTopology P]
    (h : GoodFam F D) (hm : 0 < m) (hα : Continuous α) (hβ : Continuous β) :
    GoodFam (stepM μ m α β F) (stepMD μ m α β F D) where
  contF := by
    have hI := continuous_intExp hμ h hm.le hα hβ (m := m)
    rw [continuous_iff_continuousAt]
    intro w₀
    have hpos := integral_expShift_pos hμ h hm.le w₀.1 w₀.2.1 (α w₀.1) (β w₀.1) w₀.2.2
    exact continuousAt_const.mul (hI.continuousAt.log hpos.ne')
  contD := by
    have hI := continuous_intExp hμ h hm.le hα hβ (m := m)
    have hN := continuous_intDexp hμ h hm.le hα hβ (m := m)
    rw [continuous_iff_continuousAt]
    intro w₀
    have hpos := integral_expShift_pos hμ h hm.le w₀.1 w₀.2.1 (α w₀.1) (β w₀.1) w₀.2.2
    exact hN.continuousAt.div hI.continuousAt hpos.ne'
  hasDeriv := fun p l x => hasDeriv_stepM hμ h hm p l x
  lipx := fun p l x y => lipx_stepM hμ h hm p l x y
  bddD := fun p l x => bddD_stepM hμ h hm p l x

end StepM2

/-! ### The standard Gaussian measure -/

lemma expMoments_gaussianReal (m : ℝ) (v : NNReal) : ExpMoments (gaussianReal m v) := by
  intro c
  have hint : Integrable (fun z : ℝ => Real.exp (c * z) + Real.exp (-c * z)) (gaussianReal m v) :=
    (integrable_exp_mul_gaussianReal c).add (integrable_exp_mul_gaussianReal (-c))
  refine hint.mono (by fun_prop) ?_
  filter_upwards with z
  have hcases : c * |z| = c * z ∨ c * |z| = -c * z := by
    rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩
    · left; rw [h]
    · right; rw [h]; ring
  have hle : Real.exp (c * |z|) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
    rcases hcases with h | h <;> rw [h]
    · linarith [Real.exp_pos (-c * z)]
    · linarith [Real.exp_pos (c * z)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (c * z) + Real.exp (-c * z))]
  exact hle

/-! ### The terminal function -/

/-- The (unnormalised) sum of the four exponentials appearing in the terminal function. -/
def fS (lam : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.exp (x.1 + x.2 + lam) + Real.exp (x.1 - x.2 - lam)
    + Real.exp (-x.1 + x.2 - lam) + Real.exp (-x.1 - x.2 + lam)

/-- The two-replica terminal function. -/
abbrev fLbase (lam : ℝ) (x : ℝ × ℝ) : ℝ := SpinGlass.AT.gtTerminal lam x.1 x.2

/-- The `lam`-derivative of the terminal function. -/
def fLbaseD (lam : ℝ) (x : ℝ × ℝ) : ℝ :=
  (Real.exp (x.1 + x.2 + lam) - Real.exp (x.1 - x.2 - lam)
    - Real.exp (-x.1 + x.2 - lam) + Real.exp (-x.1 - x.2 + lam)) / fS lam x

lemma fS_pos (lam : ℝ) (x : ℝ × ℝ) : 0 < fS lam x := by
  unfold fS; positivity

lemma continuous_fS : Continuous fun w : ℝ × (ℝ × ℝ) => fS w.1 w.2 := by
  unfold fS; fun_prop

lemma continuous_fLbase : Continuous fun w : ℝ × (ℝ × ℝ) => fLbase w.1 w.2 := by
  refine Continuous.log ?_ (fun w => by have := fS_pos w.1 w.2; positivity)
  exact continuous_fS.div_const 4

lemma continuous_fLbaseD : Continuous fun w : ℝ × (ℝ × ℝ) => fLbaseD w.1 w.2 := by
  unfold fLbaseD
  refine Continuous.div (by fun_prop) continuous_fS (fun w => (fS_pos w.1 w.2).ne')

lemma hasDerivAt_fLbase (lam : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l => fLbase l x) (fLbaseD lam x) lam := by
  have hT1 : HasDerivAt (fun l : ℝ => Real.exp (x.1 + x.2 + l))
      (Real.exp (x.1 + x.2 + lam)) lam := by
    simpa using ((hasDerivAt_id lam).const_add (x.1 + x.2)).exp
  have hT2 : HasDerivAt (fun l : ℝ => Real.exp (x.1 - x.2 - l))
      (-Real.exp (x.1 - x.2 - lam)) lam := by
    have h : HasDerivAt (fun l : ℝ => x.1 - x.2 - l) (-1) lam := by
      simpa using (hasDerivAt_id lam).const_sub (x.1 - x.2)
    simpa using h.exp
  have hT3 : HasDerivAt (fun l : ℝ => Real.exp (-x.1 + x.2 - l))
      (-Real.exp (-x.1 + x.2 - lam)) lam := by
    have h : HasDerivAt (fun l : ℝ => -x.1 + x.2 - l) (-1) lam := by
      simpa using (hasDerivAt_id lam).const_sub (-x.1 + x.2)
    simpa using h.exp
  have hT4 : HasDerivAt (fun l : ℝ => Real.exp (-x.1 - x.2 + l))
      (Real.exp (-x.1 - x.2 + lam)) lam := by
    simpa using ((hasDerivAt_id lam).const_add (-x.1 - x.2)).exp
  have hS : HasDerivAt (fun l : ℝ => fS l x)
      (Real.exp (x.1 + x.2 + lam) + -Real.exp (x.1 - x.2 - lam)
        + -Real.exp (-x.1 + x.2 - lam) + Real.exp (-x.1 - x.2 + lam)) lam :=
    ((hT1.add hT2).add hT3).add hT4
  have hSdiv : HasDerivAt (fun l : ℝ => fS l x / 4)
      ((Real.exp (x.1 + x.2 + lam) + -Real.exp (x.1 - x.2 - lam)
        + -Real.exp (-x.1 + x.2 - lam) + Real.exp (-x.1 - x.2 + lam)) / 4) lam :=
    hS.div_const 4
  have hne : fS lam x / 4 ≠ 0 := by have := fS_pos lam x; positivity
  have hlog := hSdiv.log hne
  have heq : (Real.exp (x.1 + x.2 + lam) + -Real.exp (x.1 - x.2 - lam)
        + -Real.exp (-x.1 + x.2 - lam) + Real.exp (-x.1 - x.2 + lam)) / 4 / (fS lam x / 4)
      = fLbaseD lam x := by
    unfold fLbaseD
    rw [div_div_div_cancel_right₀]
    · ring_nf
    · norm_num
  rw [heq] at hlog
  exact hlog

lemma fS_le (lam : ℝ) (x y : ℝ × ℝ) :
    fS lam x ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * fS lam y := by
  have a1 := le_abs_self (x.1 - y.1)
  have a2 := le_abs_self (x.2 - y.2)
  have b1 := neg_abs_le (x.1 - y.1)
  have b2 := neg_abs_le (x.2 - y.2)
  have h1 : Real.exp (x.1 + x.2 + lam)
      ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * Real.exp (y.1 + y.2 + lam) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (x.1 - x.2 - lam)
      ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * Real.exp (y.1 - y.2 - lam) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-x.1 + x.2 - lam)
      ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * Real.exp (-y.1 + y.2 - lam) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-x.1 - x.2 + lam)
      ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * Real.exp (-y.1 - y.2 + lam) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  unfold fS
  nlinarith [h1, h2, h3, h4]

lemma fLbase_le (lam : ℝ) (x y : ℝ × ℝ) :
    fLbase lam x ≤ (|x.1 - y.1| + |x.2 - y.2|) + fLbase lam y := by
  have hx := fS_pos lam x
  have hy := fS_pos lam y
  have hmono : fS lam x / 4 ≤ Real.exp (|x.1 - y.1| + |x.2 - y.2|) * (fS lam y / 4) := by
    have := fS_le lam x y
    linarith
  have := Real.log_le_log (by positivity) hmono
  rwa [Real.log_mul (Real.exp_ne_zero _) (by positivity : fS lam y / 4 ≠ 0), Real.log_exp] at this

lemma fLbase_lipx (lam : ℝ) (x y : ℝ × ℝ) :
    |fLbase lam x - fLbase lam y| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  have h1 := fLbase_le lam x y
  have h2 := fLbase_le lam y x
  rw [abs_sub_comm (y.1) (x.1), abs_sub_comm (y.2) (x.2)] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma fLbaseD_bdd (lam : ℝ) (x : ℝ × ℝ) : |fLbaseD lam x| ≤ 1 := by
  have hS := fS_pos lam x
  have p1 := Real.exp_pos (x.1 + x.2 + lam)
  have p2 := Real.exp_pos (x.1 - x.2 - lam)
  have p3 := Real.exp_pos (-x.1 + x.2 - lam)
  have p4 := Real.exp_pos (-x.1 - x.2 + lam)
  unfold fLbaseD
  rw [abs_div, abs_of_pos hS, div_le_one hS]
  unfold fS
  rw [abs_le]
  constructor <;> [linarith; linarith]

/-- The terminal function, viewed as a family over an arbitrary parameter space,
is a good family. -/
theorem goodFam_fLbase {P : Type*} [TopologicalSpace P] :
    GoodFam (fun (_ : P) l (x : ℝ × ℝ) => fLbase l x) (fun (_ : P) l x => fLbaseD l x) where
  contF := continuous_fLbase.comp (by fun_prop)
  contD := continuous_fLbaseD.comp (by fun_prop)
  hasDeriv := fun _ l x => hasDerivAt_fLbase l x
  lipx := fun _ l x y => fLbase_lipx l x y
  bddD := fun _ l x => fLbaseD_bdd l x
end GTFrame

/-!
# The second `lam`-derivative of the terminal function

The terminal function `fLbase lam x` is the logarithm of the average of
`exp (ε₁ x₁ + ε₂ x₂ + lam ε₁ ε₂)` over the four sign patterns.  Its
`lam`-derivative `fLbaseD` is the Gibbs mean of `ε₁ ε₂`, and its second
`lam`-derivative is the corresponding variance, which because `(ε₁ ε₂) ^ 2 = 1`
equals `1 - fLbaseD ^ 2`.

This file proves that `(fLbaseD, fLbaseDD)` is again a good family, i.e. that
`fLbaseD` is `1`-Lipschitz in each spatial coordinate and that the second
derivative takes values in `[0, 1]`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section

namespace GTFrame

/-- The second `lam`-derivative of the terminal function: the variance of
`ε₁ ε₂` under the two-replica Gibbs measure. -/
def fLbaseDD (lam : ℝ) (x : ℝ × ℝ) : ℝ := 1 - (fLbaseD lam x) ^ 2

lemma continuous_fLbaseDD : Continuous fun w : ℝ × (ℝ × ℝ) => fLbaseDD w.1 w.2 :=
  continuous_const.sub (continuous_fLbaseD.pow 2)

lemma fLbaseDD_nonneg (lam : ℝ) (x : ℝ × ℝ) : 0 ≤ fLbaseDD lam x := by
  have h := fLbaseD_bdd lam x
  have h2 : (fLbaseD lam x) ^ 2 ≤ 1 := by
    have := abs_nonneg (fLbaseD lam x)
    nlinarith [sq_abs (fLbaseD lam x)]
  simpa [fLbaseDD] using h2

lemma fLbaseDD_le_one (lam : ℝ) (x : ℝ × ℝ) : fLbaseDD lam x ≤ 1 := by
  have : 0 ≤ (fLbaseD lam x) ^ 2 := sq_nonneg _
  simp only [fLbaseDD]
  linarith

lemma fLbaseDD_bdd (lam : ℝ) (x : ℝ × ℝ) : |fLbaseDD lam x| ≤ 1 :=
  abs_le.2 ⟨by linarith [fLbaseDD_nonneg lam x], fLbaseDD_le_one lam x⟩

/-! ### The `lam`-derivative of `fLbaseD` -/

lemma hasDerivAt_fLbaseD (lam : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l => fLbaseD l x) (fLbaseDD lam x) lam := by
  have hT1 : HasDerivAt (fun l : ℝ => Real.exp (x.1 + x.2 + l))
      (Real.exp (x.1 + x.2 + lam)) lam := by
    simpa using ((hasDerivAt_id lam).const_add (x.1 + x.2)).exp
  have hT2 : HasDerivAt (fun l : ℝ => Real.exp (x.1 - x.2 - l))
      (-Real.exp (x.1 - x.2 - lam)) lam := by
    have h : HasDerivAt (fun l : ℝ => x.1 - x.2 - l) (-1) lam := by
      simpa using (hasDerivAt_id lam).const_sub (x.1 - x.2)
    simpa using h.exp
  have hT3 : HasDerivAt (fun l : ℝ => Real.exp (-x.1 + x.2 - l))
      (-Real.exp (-x.1 + x.2 - lam)) lam := by
    have h : HasDerivAt (fun l : ℝ => -x.1 + x.2 - l) (-1) lam := by
      simpa using (hasDerivAt_id lam).const_sub (-x.1 + x.2)
    simpa using h.exp
  have hT4 : HasDerivAt (fun l : ℝ => Real.exp (-x.1 - x.2 + l))
      (Real.exp (-x.1 - x.2 + lam)) lam := by
    simpa using ((hasDerivAt_id lam).const_add (-x.1 - x.2)).exp
  have hN := ((hT1.sub hT2).sub hT3).add hT4
  have hS := ((hT1.add hT2).add hT3).add hT4
  have hpos := fS_pos lam x
  have hdiv := hN.div hS hpos.ne'
  refine (hdiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with l
    simp only [fLbaseD, fS, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  · simp only [fLbaseDD, fLbaseD, fS, Pi.add_apply, Pi.sub_apply]
    field_simp
    ring

/-! ### Lipschitz continuity of `fLbaseD` in the spatial variables -/

/-- A function with a derivative bounded by `C` everywhere is `C`-Lipschitz. -/
lemma lipschitz_of_hasDerivAt_bound {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ t, ∃ d, HasDerivAt f d t ∧ |d| ≤ C) (u v : ℝ) :
    |f u - f v| ≤ C * |u - v| := by
  have hd : ∀ t : ℝ, HasDerivAt f (deriv f t) t := by
    intro t
    obtain ⟨d, hdt, _⟩ := h t
    rw [hdt.deriv]
    exact hdt
  have hb : ∀ t : ℝ, ‖deriv f t‖ ≤ C := by
    intro t
    obtain ⟨d, hdt, hdb⟩ := h t
    rw [hdt.deriv]
    simpa [Real.norm_eq_abs] using hdb
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := deriv f) (s := Set.univ) (C := C)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- The partial derivative of `fLbaseD` in the first spatial coordinate exists and is
bounded by one. -/
lemma exists_hasDerivAt_fLbaseD_fst (lam x₂ t : ℝ) :
    ∃ d, HasDerivAt (fun s => fLbaseD lam (s, x₂)) d t ∧ |d| ≤ 1 := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s + x₂ + lam)) (Real.exp (t + x₂ + lam)) t := by
    simpa using (((hasDerivAt_id t).add_const x₂).add_const lam).exp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (s - x₂ - lam)) (Real.exp (t - x₂ - lam)) t := by
    simpa using (((hasDerivAt_id t).sub_const x₂).sub_const lam).exp
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s + x₂ - lam))
      (-Real.exp (-t + x₂ - lam)) t := by
    have h : HasDerivAt (fun s : ℝ => -s + x₂ - lam) (-1) t := by
      simpa using ((hasDerivAt_id t).neg.add_const x₂).sub_const lam
    simpa using h.exp
  have h4 : HasDerivAt (fun s : ℝ => Real.exp (-s - x₂ + lam))
      (-Real.exp (-t - x₂ + lam)) t := by
    have h : HasDerivAt (fun s : ℝ => -s - x₂ + lam) (-1) t := by
      simpa using ((hasDerivAt_id t).neg.sub_const x₂).add_const lam
    simpa using h.exp
  set a := Real.exp (t + x₂ + lam) with ha
  set b := Real.exp (t - x₂ - lam) with hb
  set c := Real.exp (-t + x₂ - lam) with hc
  set e := Real.exp (-t - x₂ + lam) with he
  have hap : 0 < a := Real.exp_pos _
  have hbp : 0 < b := Real.exp_pos _
  have hcp : 0 < c := Real.exp_pos _
  have hep : 0 < e := Real.exp_pos _
  have hN := ((h1.sub h2).sub h3).add h4
  have hS := ((h1.add h2).add h3).add h4
  have hSpos : 0 < fS lam (t, x₂) := fS_pos lam (t, x₂)
  have hdiv := hN.div hS hSpos.ne'
  refine ⟨_, hdiv.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards with s
    simp only [fLbaseD, fS, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  have hfS : fS lam (t, x₂) = a + b + c + e := rfl
  have hA : Real.exp (t + x₂ + lam) = a := rfl
  have hB : Real.exp (t - x₂ - lam) = b := rfl
  have hC : Real.exp (-t + x₂ - lam) = c := rfl
  have hE : Real.exp (-t - x₂ + lam) = e := rfl
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hA, hB, hC, hE, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < (a + b + c + e) ^ 2),
    div_le_one (by positivity : (0:ℝ) < (a + b + c + e) ^ 2), abs_le]
  constructor
  · nlinarith [sq_nonneg (a - c), sq_nonneg (b - e), mul_pos hap hcp, mul_pos hbp hep,
      mul_pos (add_pos hap hcp) (add_pos hbp hep)]
  · nlinarith [sq_nonneg (a - c), sq_nonneg (b - e), mul_pos hap hcp, mul_pos hbp hep,
      mul_pos (add_pos hap hcp) (add_pos hbp hep)]

/-- The partial derivative of `fLbaseD` in the second spatial coordinate exists and is
bounded by one. -/
lemma exists_hasDerivAt_fLbaseD_snd (lam x₁ t : ℝ) :
    ∃ d, HasDerivAt (fun s => fLbaseD lam (x₁, s)) d t ∧ |d| ≤ 1 := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (x₁ + s + lam)) (Real.exp (x₁ + t + lam)) t := by
    have h : HasDerivAt (fun s : ℝ => x₁ + s + lam) 1 t := by
      simpa using ((hasDerivAt_id t).const_add x₁).add_const lam
    simpa using h.exp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (x₁ - s - lam)) (-Real.exp (x₁ - t - lam)) t := by
    have h : HasDerivAt (fun s : ℝ => x₁ - s - lam) (-1) t := by
      simpa using ((hasDerivAt_id t).const_sub x₁).sub_const lam
    simpa using h.exp
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-x₁ + s - lam)) (Real.exp (-x₁ + t - lam)) t := by
    have h : HasDerivAt (fun s : ℝ => -x₁ + s - lam) 1 t := by
      simpa using ((hasDerivAt_id t).const_add (-x₁)).sub_const lam
    simpa using h.exp
  have h4 : HasDerivAt (fun s : ℝ => Real.exp (-x₁ - s + lam)) (-Real.exp (-x₁ - t + lam)) t := by
    have h : HasDerivAt (fun s : ℝ => -x₁ - s + lam) (-1) t := by
      simpa using ((hasDerivAt_id t).const_sub (-x₁)).add_const lam
    simpa using h.exp
  set a := Real.exp (x₁ + t + lam) with ha
  set b := Real.exp (x₁ - t - lam) with hb
  set c := Real.exp (-x₁ + t - lam) with hc
  set e := Real.exp (-x₁ - t + lam) with he
  have hap : 0 < a := Real.exp_pos _
  have hbp : 0 < b := Real.exp_pos _
  have hcp : 0 < c := Real.exp_pos _
  have hep : 0 < e := Real.exp_pos _
  have hN := ((h1.sub h2).sub h3).add h4
  have hS := ((h1.add h2).add h3).add h4
  have hSpos : 0 < fS lam (x₁, t) := fS_pos lam (x₁, t)
  have hdiv := hN.div hS hSpos.ne'
  refine ⟨_, hdiv.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards with s
    simp only [fLbaseD, fS, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  have hfS : fS lam (x₁, t) = a + b + c + e := rfl
  have hA : Real.exp (x₁ + t + lam) = a := rfl
  have hB : Real.exp (x₁ - t - lam) = b := rfl
  have hC : Real.exp (-x₁ + t - lam) = c := rfl
  have hE : Real.exp (-x₁ - t + lam) = e := rfl
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hA, hB, hC, hE, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < (a + b + c + e) ^ 2),
    div_le_one (by positivity : (0:ℝ) < (a + b + c + e) ^ 2), abs_le]
  constructor
  · nlinarith [sq_nonneg (a - b), sq_nonneg (c - e), mul_pos hap hbp, mul_pos hcp hep,
      mul_pos (add_pos hap hbp) (add_pos hcp hep)]
  · nlinarith [sq_nonneg (a - b), sq_nonneg (c - e), mul_pos hap hbp, mul_pos hcp hep,
      mul_pos (add_pos hap hbp) (add_pos hcp hep)]

lemma fLbaseD_lipx (lam : ℝ) (x y : ℝ × ℝ) :
    |fLbaseD lam x - fLbaseD lam y| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  have h1 : |fLbaseD lam (x.1, x.2) - fLbaseD lam (y.1, x.2)| ≤ |x.1 - y.1| := by
    have := lipschitz_of_hasDerivAt_bound
      (f := fun s => fLbaseD lam (s, x.2)) (C := 1)
      (fun t => exists_hasDerivAt_fLbaseD_fst lam x.2 t) x.1 y.1
    simpa using this
  have h2 : |fLbaseD lam (y.1, x.2) - fLbaseD lam (y.1, y.2)| ≤ |x.2 - y.2| := by
    have := lipschitz_of_hasDerivAt_bound
      (f := fun s => fLbaseD lam (y.1, s)) (C := 1)
      (fun t => exists_hasDerivAt_fLbaseD_snd lam y.1 t) x.2 y.2
    simpa using this
  have hx : x = (x.1, x.2) := rfl
  have hy : y = (y.1, y.2) := rfl
  calc |fLbaseD lam x - fLbaseD lam y|
      = |(fLbaseD lam (x.1, x.2) - fLbaseD lam (y.1, x.2))
          + (fLbaseD lam (y.1, x.2) - fLbaseD lam (y.1, y.2))| := by
        rw [← hx, ← hy]; ring_nf
    _ ≤ |fLbaseD lam (x.1, x.2) - fLbaseD lam (y.1, x.2)|
          + |fLbaseD lam (y.1, x.2) - fLbaseD lam (y.1, y.2)| := abs_add_le _ _
    _ ≤ |x.1 - y.1| + |x.2 - y.2| := add_le_add h1 h2

/-- The `lam`-derivative of the terminal function, together with its own
`lam`-derivative, is a good family. -/
theorem goodFam_fLbaseD {P : Type*} [TopologicalSpace P] :
    GoodFam (fun (_ : P) l (x : ℝ × ℝ) => fLbaseD l x) (fun (_ : P) l x => fLbaseDD l x) where
  contF := continuous_fLbaseD.comp (by fun_prop)
  contD := continuous_fLbaseDD.comp (by fun_prop)
  hasDeriv := fun _ l x => hasDerivAt_fLbaseD l x
  lipx := fun _ l x y => fLbaseD_lipx l x y
  bddD := fun _ l x => fLbaseDD_bdd l x

end GTFrame


/-!
# Derivatives of the finite GT recursion and uniform bounds

This section continues the Gaussian recursion developed earlier in this module. It computes the
first and second `lam`-derivatives of one finite recursion step and uses them to
derive uniform bounds on the first two `lam`-derivatives of the finite
Guerra–Talagrand solution and of the GT functional.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable section

namespace GTFrame

variable {P : Type*} [TopologicalSpace P] {μ : Measure ℝ}
variable {F D E : P → ℝ → ℝ × ℝ → ℝ} {m : ℝ} {α β : P → ℝ}

/-! ### First and second derivatives of the finite recursion -/

/-- The variance under the exponential tilt used in a positive-mass recursion step. -/
def stepMVar (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ)
    (F D : P → ℝ → ℝ × ℝ → ℝ) : P → ℝ → ℝ × ℝ → ℝ :=
  fun p l x =>
    stepMD μ m α β F (fun p' l' x' => (D p' l' x') ^ 2) p l x
      - (stepMD μ m α β F D p l x) ^ 2

/-- A recursion step that includes both the zero-mass and positive-mass cases. -/
def finiteStep (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ)
    (F : P → ℝ → ℝ × ℝ → ℝ) : P → ℝ → ℝ × ℝ → ℝ :=
  if m = 0 then step0 μ α β F else stepM μ m α β F

/-- The candidate first `l`-derivative of `finiteStep`. -/
def finiteStepD (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ)
    (F D : P → ℝ → ℝ × ℝ → ℝ) : P → ℝ → ℝ × ℝ → ℝ :=
  if m = 0 then step0 μ α β D else stepMD μ m α β F D

/-- The candidate second `l`-derivative of `finiteStep`. -/
def finiteStepDD (μ : Measure ℝ) (m : ℝ) (α β : P → ℝ)
    (F D E : P → ℝ → ℝ × ℝ → ℝ) : P → ℝ → ℝ × ℝ → ℝ :=
  if m = 0 then step0 μ α β E
  else fun p l x =>
    stepMD μ m α β F E p l x + m * stepMVar μ m α β F D p l x

/-! ### Auxiliary lemmas for the second derivative of a positive-mass step -/

omit [TopologicalSpace P] in
/-- The algebraic identity behind the quotient rule for `stepMD`. -/
lemma tilted_quotient_identity (NE N2 N I mm : ℝ) (hI : I ≠ 0) :
    NE / I + mm * (N2 / I - (N / I) ^ 2)
      = ((NE + mm * N2) * I - N * (mm * N)) / I ^ 2 := by
  field_simp
  ring

omit [TopologicalSpace P] in
/-- If `H` is the `l`-derivative of `G` and `|H| ≤ c`, then `G` is `c`-Lipschitz in `l`. -/
lemma lipl_of_bddDeriv {G H : P → ℝ → ℝ × ℝ → ℝ} {c : ℝ}
    (hd : ∀ p l x, HasDerivAt (fun l' => G p l' x) (H p l x) l)
    (hb : ∀ p l x, |H p l x| ≤ c) (p : P) (l l' : ℝ) (x : ℝ × ℝ) :
    |G p l x - G p l' x| ≤ c * |l - l'| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => G p t x) (f' := fun t => H p t x) (s := Set.univ) (C := c)
    (fun t _ => (hd p t x).hasDerivWithinAt)
    (fun t _ => by simpa [Real.norm_eq_abs] using hb p t x) convex_univ (Set.mem_univ l')
    (Set.mem_univ l)
  simpa [Real.norm_eq_abs] using this

/-- Integrability of `g * exp (m * F)` along a shifted line, for a bounded continuous `g`. -/
lemma integrable_gexpShift (hμ : ExpMoments μ) (h : GoodFam F D) (hm : 0 ≤ m)
    {g : ℝ → ℝ} {c : ℝ} (hg : Continuous g) (hgb : ∀ z, |g z| ≤ c)
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => g z * Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))) μ := by
  refine Integrable.mono' ((hμ.integrable_exp_linear m (|F p l x|) (|a| + |b|)).const_mul c)
    ((hg.mul (cont_expShift h p l a b x)).aestronglyMeasurable) ?_
  filter_upwards with z
  have hle : Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))
      ≤ Real.exp (m * (|F p l x| + (|a| + |b|) * |z|)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 := h.bound_shift p l a b x z
    have h2 := le_abs_self (F p l (x.1 + a * z, x.2 + b * z))
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hg0 := abs_nonneg (g z)
  nlinarith [Real.exp_pos (m * F p l (x.1 + a * z, x.2 + b * z)),
    Real.exp_pos (m * (|F p l x| + (|a| + |b|) * |z|)), hgb z]

/-- Differentiating `∫ D * exp (m * F)` in the distinguished parameter. -/
lemma hasDeriv_intDexp (hμ : ExpMoments μ) (hF : GoodFam F D) (hm : 0 < m) {c : ℝ}
    (hEcont : Continuous fun w : P × ℝ × (ℝ × ℝ) => E w.1 w.2.1 w.2.2)
    (hEderiv : ∀ p l x, HasDerivAt (fun l' => D p l' x) (E p l x) l)
    (hEbdd : ∀ p l x, |E p l x| ≤ c)
    (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => ∫ z, D p l' (x.1 + a * z, x.2 + b * z) *
          Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z)) ∂μ)
      (∫ z, (E p l (x.1 + a * z, x.2 + b * z)
          + m * (D p l (x.1 + a * z, x.2 + b * z)) ^ 2) *
          Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)) ∂μ) l := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hEbdd p l x)
  set M := |F p l x| + 1 with hM
  set A := |a| + |b| with hA
  have hcontE : ∀ l' : ℝ, Continuous fun z : ℝ => E p l' (x.1 + a * z, x.2 + b * z) := by
    intro l'
    exact hEcont.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l', (x.1 + a * z, x.2 + b * z)) : P × ℝ × (ℝ × ℝ)))
  have hlip : ∀ᵐ z ∂μ, LipschitzOnWith
      (Real.nnabs ((c + m) * Real.exp (m * (M + A * |z|))))
      (fun l' => D p l' (x.1 + a * z, x.2 + b * z) *
        Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z))) (Metric.ball l 1) := by
    filter_upwards with z
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    have hu1 : |u - l| ≤ 1 := by
      have := Metric.mem_ball.1 hu; rw [Real.dist_eq] at this; linarith
    have hv1 : |v - l| ≤ 1 := by
      have := Metric.mem_ball.1 hv; rw [Real.dist_eq] at this; linarith
    have hbu : m * F p u (x.1 + a * z, x.2 + b * z) ≤ m * (M + A * |z|) := by
      have h1 := hF.bound_shift_unif p l u a b hu1 x z
      have h2 := le_abs_self (F p u (x.1 + a * z, x.2 + b * z))
      nlinarith
    have hbv : m * F p v (x.1 + a * z, x.2 + b * z) ≤ m * (M + A * |z|) := by
      have h1 := hF.bound_shift_unif p l v a b hv1 x z
      have h2 := le_abs_self (F p v (x.1 + a * z, x.2 + b * z))
      nlinarith
    have hexp := abs_exp_sub_exp_le _ _ (m * (M + A * |z|)) hbu hbv
    have hdiffF : |m * F p u (x.1 + a * z, x.2 + b * z)
        - m * F p v (x.1 + a * z, x.2 + b * z)| ≤ m * |u - v| := by
      have := hF.lipl p u v (x.1 + a * z, x.2 + b * z)
      rw [← mul_sub, abs_mul, abs_of_pos hm]
      exact mul_le_mul_of_nonneg_left this hm.le
    have hdiffD : |D p u (x.1 + a * z, x.2 + b * z) - D p v (x.1 + a * z, x.2 + b * z)|
        ≤ c * |u - v| := lipl_of_bddDeriv hEderiv hEbdd p u v _
    have hDv : |D p v (x.1 + a * z, x.2 + b * z)| ≤ 1 := hF.bddD p v _
    have hexpu : Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
        ≤ Real.exp (m * (M + A * |z|)) := Real.exp_le_exp.2 hbu
    have hcoe : ((Real.nnabs ((c + m) * Real.exp (m * (M + A * |z|))) : NNReal) : ℝ)
        = (c + m) * Real.exp (m * (M + A * |z|)) := by
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
    rw [Real.dist_eq, Real.dist_eq, hcoe]
    have hsplit : D p u (x.1 + a * z, x.2 + b * z) *
          Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
        - D p v (x.1 + a * z, x.2 + b * z) *
          Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))
        = (D p u (x.1 + a * z, x.2 + b * z) - D p v (x.1 + a * z, x.2 + b * z)) *
            Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
          + D p v (x.1 + a * z, x.2 + b * z) *
            (Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
              - Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))) := by ring
    rw [hsplit]
    have hstep1 := abs_add_le (((D p u (x.1 + a * z, x.2 + b * z)
        - D p v (x.1 + a * z, x.2 + b * z))) *
          Real.exp (m * F p u (x.1 + a * z, x.2 + b * z)))
      (D p v (x.1 + a * z, x.2 + b * z) *
        (Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
          - Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))))
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)] at hstep1
    have hb1 : |D p u (x.1 + a * z, x.2 + b * z) - D p v (x.1 + a * z, x.2 + b * z)| *
        Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
        ≤ (c * |u - v|) * Real.exp (m * (M + A * |z|)) :=
      mul_le_mul hdiffD hexpu (Real.exp_nonneg _) (by positivity)
    have hb2 : |D p v (x.1 + a * z, x.2 + b * z)| *
        |Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
          - Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))|
        ≤ 1 * (Real.exp (m * (M + A * |z|)) * (m * |u - v|)) := by
      refine mul_le_mul hDv ?_ (abs_nonneg _) zero_le_one
      calc |Real.exp (m * F p u (x.1 + a * z, x.2 + b * z))
              - Real.exp (m * F p v (x.1 + a * z, x.2 + b * z))|
          ≤ Real.exp (m * (M + A * |z|)) *
              |m * F p u (x.1 + a * z, x.2 + b * z)
                - m * F p v (x.1 + a * z, x.2 + b * z)| := hexp
        _ ≤ Real.exp (m * (M + A * |z|)) * (m * |u - v|) :=
            mul_le_mul_of_nonneg_left hdiffF (Real.exp_nonneg _)
    nlinarith [hstep1, hb1, hb2]
  have hptderiv : ∀ z : ℝ, HasDerivAt
      (fun l' => D p l' (x.1 + a * z, x.2 + b * z) *
        Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z)))
      ((E p l (x.1 + a * z, x.2 + b * z)
          + m * (D p l (x.1 + a * z, x.2 + b * z)) ^ 2) *
        Real.exp (m * F p l (x.1 + a * z, x.2 + b * z))) l := by
    intro z
    have h1 := hEderiv p l (x.1 + a * z, x.2 + b * z)
    have h2 := (HasDerivAt.const_mul m (hF.hasDeriv p l (x.1 + a * z, x.2 + b * z))).exp
    have := h1.mul h2
    convert this using 1 <;> first | rfl | ring
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun l' z => D p l' (x.1 + a * z, x.2 + b * z) *
      Real.exp (m * F p l' (x.1 + a * z, x.2 + b * z)))
    (F' := fun z => (E p l (x.1 + a * z, x.2 + b * z)
        + m * (D p l (x.1 + a * z, x.2 + b * z)) ^ 2) *
      Real.exp (m * F p l (x.1 + a * z, x.2 + b * z)))
    (x₀ := l) (bound := fun z => (c + m) * Real.exp (m * (M + A * |z|)))
    (s := Metric.ball l 1) (Metric.ball_mem_nhds l one_pos)
    (Filter.Eventually.of_forall fun l' =>
      ((hF.cont_shiftD p l' a b x).mul (cont_expShift hF p l' a b x)).aestronglyMeasurable)
    (integrable_DexpShift hμ hF hm.le p l a b x)
    ((((hcontE l).add (continuous_const.mul ((hF.cont_shiftD p l a b x).pow 2))).mul
      (cont_expShift hF p l a b x)).aestronglyMeasurable)
    hlip ((hμ.integrable_exp_linear m M A).const_mul (c + m))
    (Filter.Eventually.of_forall hptderiv)
  exact key.2

/-- The `l`-derivative of the tilted mean `stepMD`: the tilted mean of the next
derivative plus `m` times the tilted variance. -/
lemma hasDeriv_stepMD (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (hF : GoodFam F D)
    (hm : 0 < m) {c : ℝ}
    (hEcont : Continuous fun w : P × ℝ × (ℝ × ℝ) => E w.1 w.2.1 w.2.2)
    (hEderiv : ∀ p l x, HasDerivAt (fun l' => D p l' x) (E p l x) l)
    (hEbdd : ∀ p l x, |E p l x| ≤ c)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => stepMD μ m α β F D p l' x)
      (stepMD μ m α β F E p l x + m * stepMVar μ m α β F D p l x) l := by
  have hpos := integral_expShift_pos hμ hF hm.le p l (α p) (β p) x
  have hI := hasDeriv_intExp hμ hF hm p l (α p) (β p) x
  have hN := hasDeriv_intDexp hμ hF hm hEcont hEderiv hEbdd p l (α p) (β p) x
  have hcontE : Continuous fun z : ℝ => E p l (x.1 + α p * z, x.2 + β p * z) :=
    hEcont.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l, (x.1 + α p * z, x.2 + β p * z)) : P × ℝ × (ℝ × ℝ)))
  have hIE : Integrable (fun z => E p l (x.1 + α p * z, x.2 + β p * z) *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))) μ :=
    integrable_gexpShift hμ hF hm.le hcontE (fun z => hEbdd p l _) p l (α p) (β p) x
  have hI2 : Integrable (fun z => (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))) μ := by
    refine integrable_gexpShift (c := 1) hμ hF hm.le ((hF.cont_shiftD p l (α p) (β p) x).pow 2)
      (fun z => ?_) p l (α p) (β p) x
    have := hF.bddD p l (x.1 + α p * z, x.2 + β p * z)
    change |D p l (x.1 + α p * z, x.2 + β p * z) ^ 2| ≤ 1
    rw [abs_pow]
    nlinarith [abs_nonneg (D p l (x.1 + α p * z, x.2 + β p * z))]
  have hsplit : (∫ z, (E p l (x.1 + α p * z, x.2 + β p * z)
        + m * (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2) *
        Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)
      = (∫ z, E p l (x.1 + α p * z, x.2 + β p * z) *
          Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)
        + m * ∫ z, (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
          Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ := by
    have hfun : (fun z => (E p l (x.1 + α p * z, x.2 + β p * z)
          + m * (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2) *
          Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)))
        = fun z => E p l (x.1 + α p * z, x.2 + β p * z) *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))
          + m * ((D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))) := by
      funext z; ring
    rw [hfun, integral_add hIE (hI2.const_mul m), integral_const_mul]
  rw [hsplit] at hN
  have hdiv := hN.div hI hpos.ne'
  refine (hdiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with l'
    rfl
  · simp only [stepMD, stepMVar]
    exact (tilted_quotient_identity _ _ _ _ _ hpos.ne').symm

/-- At one finite recursion step, the first derivative is the tilted mean of the
next derivative, while the second derivative is the tilted mean of the next
second derivative plus `m` times the tilted variance of the first derivative.
For `m = 0`, both tilted means reduce to ordinary expectations and the variance
term vanishes. -/
lemma finiteStep_derivatives (hμ : ExpMoments μ) [IsProbabilityMeasure μ]
    (hF : GoodFam F D) (hD : GoodFam D E) (hm : 0 ≤ m)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => finiteStep μ m α β F p l' x)
        (finiteStepD μ m α β F D p l x) l ∧
      HasDerivAt (fun l' => finiteStepD μ m α β F D p l' x)
        (finiteStepDD μ m α β F D E p l x) l := by
  /-
  Proof plan:
  * Split into `m = 0` and `0 < m`.
  * In the zero-mass case, unfold the three finite-step definitions and apply
    `hasDeriv_step0` first to `hF` and then to `hD`.
  * In the positive-mass case, the first assertion is `hasDeriv_stepM`.
  * For the second assertion, differentiate the numerator and denominator in
    `stepMD` under the integral. The numerator derivative is the integral of
    `(E + m * D ^ 2) * exp (m * F)`, and the denominator derivative is the
    integral of `m * D * exp (m * F)`.
  * Apply the quotient rule, use positivity of the denominator, and rearrange
    the result as the tilted mean of `E` plus `m * stepMVar`.
  -/
  rcases eq_or_lt_of_le hm with h0 | hpos
  · have hm0 : m = 0 := h0.symm
    subst hm0
    simp only [finiteStep, finiteStepD, finiteStepDD]
    exact ⟨hasDeriv_step0 hμ hF p l x, hasDeriv_step0 hμ hD p l x⟩
  · have hne : m ≠ 0 := ne_of_gt hpos
    simp only [finiteStep, finiteStepD, finiteStepDD, if_neg hne]
    exact ⟨hasDeriv_stepM hμ hF hpos p l x,
      hasDeriv_stepMD hμ hF hpos hD.contD hD.hasDeriv hD.bddD p l x⟩

/-! ### Propagating bounds on the two derivatives along the recursion -/

section Propagate

variable {c : ℝ}

/-- Integrability of a bounded continuous family along a shifted line. -/
lemma integrable_shiftG [IsFiniteMeasure μ] {G : P → ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun w : P × ℝ × (ℝ × ℝ) => G w.1 w.2.1 w.2.2)
    (hGb : ∀ p l x, |G p l x| ≤ c) (p : P) (l a b : ℝ) (x : ℝ × ℝ) :
    Integrable (fun z => G p l (x.1 + a * z, x.2 + b * z)) μ := by
  have hcont : Continuous fun z : ℝ => G p l (x.1 + a * z, x.2 + b * z) :=
    hG.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l, (x.1 + a * z, x.2 + b * z)) : P × ℝ × (ℝ × ℝ)))
  refine Integrable.mono' (integrable_const c) hcont.aestronglyMeasurable ?_
  filter_upwards with z
  simpa [Real.norm_eq_abs] using hGb p l _

/-- A version of `hasDeriv_step0` that only needs boundedness of the derivative family. -/
lemma hasDeriv_step0_gen [IsProbabilityMeasure μ]
    (hDcont : Continuous fun w : P × ℝ × (ℝ × ℝ) => D w.1 w.2.1 w.2.2)
    (hDbdd : ∀ p l x, |D p l x| ≤ 1)
    (hEcont : Continuous fun w : P × ℝ × (ℝ × ℝ) => E w.1 w.2.1 w.2.2)
    (hEderiv : ∀ p l x, HasDerivAt (fun l' => D p l' x) (E p l x) l)
    (hEbdd : ∀ p l x, |E p l x| ≤ c)
    (p : P) (l : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun l' => step0 μ α β D p l' x) (step0 μ α β E p l x) l := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hEbdd p l x)
  have hcontD : ∀ l' : ℝ, Continuous fun z : ℝ => D p l' (x.1 + α p * z, x.2 + β p * z) :=
    fun l' => hDcont.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l', (x.1 + α p * z, x.2 + β p * z)) : P × ℝ × (ℝ × ℝ)))
  have hcontE : ∀ l' : ℝ, Continuous fun z : ℝ => E p l' (x.1 + α p * z, x.2 + β p * z) :=
    fun l' => hEcont.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l', (x.1 + α p * z, x.2 + β p * z)) : P × ℝ × (ℝ × ℝ)))
  have hlip : ∀ᵐ z ∂μ, LipschitzOnWith (Real.nnabs c)
      (fun l' => D p l' (x.1 + α p * z, x.2 + β p * z)) (Metric.ball l 1) := by
    filter_upwards with z
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u _ v _
    have hlv := lipl_of_bddDeriv hEderiv hEbdd p u v (x.1 + α p * z, x.2 + β p * z)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hc0]
    exact hlv
  have hint : Integrable (fun z => D p l (x.1 + α p * z, x.2 + β p * z)) μ :=
    integrable_shiftG hDcont hDbdd p l (α p) (β p) x
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun l' z => D p l' (x.1 + α p * z, x.2 + β p * z))
    (F' := fun z => E p l (x.1 + α p * z, x.2 + β p * z))
    (x₀ := l) (bound := fun _ : ℝ => c) (s := Metric.ball l 1)
    (Metric.ball_mem_nhds l one_pos)
    (Filter.Eventually.of_forall fun l' => (hcontD l').aestronglyMeasurable)
    hint (hcontE l).aestronglyMeasurable hlip (integrable_const c)
    (Filter.Eventually.of_forall fun z => hEderiv p l _)
  exact key.2

/-- Continuity of the tilted integral with a general bounded numerator. -/
lemma continuous_intGexp (hμ : ExpMoments μ) [FirstCountableTopology P]
    (h : GoodFam F D) (hm : 0 ≤ m) (hα : Continuous α) (hβ : Continuous β)
    {G : P → ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun w : P × ℝ × (ℝ × ℝ) => G w.1 w.2.1 w.2.2)
    (hGb : ∀ p l x, |G p l x| ≤ c) :
    Continuous fun w : P × ℝ × (ℝ × ℝ) =>
      ∫ z, G w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z) *
        Real.exp (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) ∂μ := by
  refine continuous_integral_of_locdom (fun w => ?_) (fun z => ?_) (fun w₀ => ?_)
  · exact (hG.comp (by fun_prop : Continuous fun z : ℝ =>
      ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ)))).mul
        (cont_expShift h w.1 w.2.1 (α w.1) (β w.1) w.2.2)
  · have hc : Continuous fun w : P × ℝ × (ℝ × ℝ) =>
        ((w.1, w.2.1, (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)) : P × ℝ × (ℝ × ℝ)) := by
      fun_prop
    exact (hG.comp hc).mul (Real.continuous_exp.comp (continuous_const.mul (h.contF.comp hc)))
  · have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hGb w₀.1 w₀.2.1 w₀.2.2)
    obtain ⟨M, A, hU⟩ := locDom_of_lipx hα hβ h w₀
    refine ⟨fun z => c * Real.exp (m * (M + A * |z|)),
      (hμ.integrable_exp_linear m M A).const_mul c, ?_⟩
    filter_upwards [hU] with w hw z
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hle : Real.exp (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))
        ≤ Real.exp (m * (M + A * |z|)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 := hw z
      have h2 := le_abs_self (F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))
      nlinarith
    have hGz := hGb w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)
    nlinarith [Real.exp_pos (m * F w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z)),
      Real.exp_pos (m * (M + A * |z|)),
      abs_nonneg (G w.1 w.2.1 (w.2.2.1 + α w.1 * z, w.2.2.2 + β w.1 * z))]

/-- Continuity of a tilted mean with a general bounded numerator. -/
lemma continuous_stepMD_gen (hμ : ExpMoments μ) [IsProbabilityMeasure μ]
    [FirstCountableTopology P] (h : GoodFam F D) (hm : 0 ≤ m)
    (hα : Continuous α) (hβ : Continuous β) {G : P → ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun w : P × ℝ × (ℝ × ℝ) => G w.1 w.2.1 w.2.2)
    (hGb : ∀ p l x, |G p l x| ≤ c) :
    Continuous fun w : P × ℝ × (ℝ × ℝ) => stepMD μ m α β F G w.1 w.2.1 w.2.2 := by
  have hI := continuous_intExp hμ h hm hα hβ (m := m)
  have hN := continuous_intGexp hμ h hm hα hβ hG hGb
  rw [continuous_iff_continuousAt]
  intro w₀
  have hpos := integral_expShift_pos hμ h hm w₀.1 w₀.2.1 (α w₀.1) (β w₀.1) w₀.2.2
  exact hN.continuousAt.div hI.continuousAt hpos.ne'

/-- A tilted mean of a nonnegative function is nonnegative. -/
lemma stepMD_nonneg (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    (hm : 0 ≤ m) {G : P → ℝ → ℝ × ℝ → ℝ} (hGnn : ∀ p l x, 0 ≤ G p l x)
    (p : P) (l : ℝ) (x : ℝ × ℝ) : 0 ≤ stepMD μ m α β F G p l x := by
  have hpos := integral_expShift_pos hμ h hm p l (α p) (β p) x
  have hnum : 0 ≤ ∫ z, G p l (x.1 + α p * z, x.2 + β p * z) *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ :=
    integral_nonneg fun z => mul_nonneg (hGnn _ _ _) (Real.exp_nonneg _)
  simp only [stepMD]
  positivity

/-- A tilted mean is bounded by a pointwise bound on the numerator. -/
lemma stepMD_le (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    (hm : 0 ≤ m) {G : P → ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun w : P × ℝ × (ℝ × ℝ) => G w.1 w.2.1 w.2.2)
    (hGb : ∀ p l x, |G p l x| ≤ c) (p : P) (l : ℝ) (x : ℝ × ℝ) :
    stepMD μ m α β F G p l x ≤ c := by
  have hpos := integral_expShift_pos hμ h hm p l (α p) (β p) x
  have hcontG : Continuous fun z : ℝ => G p l (x.1 + α p * z, x.2 + β p * z) :=
    hG.comp (by fun_prop :
      Continuous fun z : ℝ => ((p, l, (x.1 + α p * z, x.2 + β p * z)) : P × ℝ × (ℝ × ℝ)))
  have hIG := integrable_gexpShift hμ h hm hcontG (fun z => hGb p l _) p l (α p) (β p) x
  have hIe := integrable_expShift hμ h hm p l (α p) (β p) x
  have hmono : (∫ z, G p l (x.1 + α p * z, x.2 + β p * z) *
        Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)
      ≤ c * ∫ z, Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hIG (hIe.const_mul c) (fun z => ?_)
    have hGz := (abs_le.1 (hGb p l (x.1 + α p * z, x.2 + β p * z))).2
    have := Real.exp_pos (m * F p l (x.1 + α p * z, x.2 + β p * z))
    nlinarith
  simp only [stepMD]
  rw [div_le_iff₀ hpos]
  linarith

/-- The tilted variance is nonnegative. -/
lemma stepMVar_nonneg (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    (hm : 0 ≤ m) (p : P) (l : ℝ) (x : ℝ × ℝ) : 0 ≤ stepMVar μ m α β F D p l x := by
  have hpos := integral_expShift_pos hμ h hm p l (α p) (β p) x
  set I := ∫ z, Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ with hI
  set N := ∫ z, D p l (x.1 + α p * z, x.2 + β p * z) *
    Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ with hN
  set N2 := ∫ z, (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
    Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ with hN2
  have hIe := integrable_expShift hμ h hm p l (α p) (β p) x
  have hID := integrable_DexpShift hμ h hm p l (α p) (β p) x
  have hID2 : Integrable (fun z => (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))) μ := by
    refine integrable_gexpShift (c := 1) hμ h hm ((h.cont_shiftD p l (α p) (β p) x).pow 2)
      (fun z => ?_) p l (α p) (β p) x
    have := h.bddD p l (x.1 + α p * z, x.2 + β p * z)
    change |D p l (x.1 + α p * z, x.2 + β p * z) ^ 2| ≤ 1
    rw [abs_pow]
    nlinarith [abs_nonneg (D p l (x.1 + α p * z, x.2 + β p * z))]
  set t := N / I with ht
  have hnn : 0 ≤ ∫ z, (D p l (x.1 + α p * z, x.2 + β p * z) - t) ^ 2 *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hexpand : (∫ z, (D p l (x.1 + α p * z, x.2 + β p * z) - t) ^ 2 *
      Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) ∂μ)
      = N2 - 2 * t * N + t ^ 2 * I := by
    have hfun : (fun z => (D p l (x.1 + α p * z, x.2 + β p * z) - t) ^ 2 *
        Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)))
        = fun z => ((D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))
          + (-(2 * t)) * (D p l (x.1 + α p * z, x.2 + β p * z) *
            Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))))
          + t ^ 2 * Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)) := by
      funext z; ring
    have hsum : Integrable (fun z => (D p l (x.1 + α p * z, x.2 + β p * z)) ^ 2 *
        Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z))
        + (-(2 * t)) * (D p l (x.1 + α p * z, x.2 + β p * z) *
          Real.exp (m * F p l (x.1 + α p * z, x.2 + β p * z)))) μ :=
      hID2.add (hID.const_mul (-(2 * t)))
    rw [hfun, integral_add hsum (hIe.const_mul (t ^ 2)),
      integral_add hID2 (hID.const_mul (-(2 * t))), integral_const_mul, integral_const_mul]
    simp only [← hN, ← hN2, ← hI]
    ring
  rw [hexpand] at hnn
  have hIne : I ≠ 0 := hpos.ne'
  have ht' : t * I = N := by
    rw [ht]
    field_simp
  have hmul : 0 ≤ (N2 - 2 * t * N + t ^ 2 * I) * I := mul_nonneg hnn hpos.le
  have hid : (N2 - 2 * t * N + t ^ 2 * I) * I = N2 * I - N ^ 2 := by
    linear_combination (t * I - N) * ht'
  have hkey : N ^ 2 ≤ N2 * I := by rw [hid] at hmul; linarith
  simp only [stepMVar, stepMD, ← hI, ← hN, ← hN2]
  rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) hpos]
  nlinarith [hkey, hpos]

/-- The tilted variance of a family bounded by one is at most one. -/
lemma stepMVar_le_one (hμ : ExpMoments μ) [IsProbabilityMeasure μ] (h : GoodFam F D)
    (hm : 0 ≤ m) (p : P) (l : ℝ) (x : ℝ × ℝ) : stepMVar μ m α β F D p l x ≤ 1 := by
  have hpos := integral_expShift_pos hμ h hm p l (α p) (β p) x
  have hsq : stepMD μ m α β F (fun p' l' x' => (D p' l' x') ^ 2) p l x ≤ 1 := by
    refine stepMD_le (c := 1) hμ h hm ?_ (fun p' l' x' => ?_) p l x
    · exact (h.contD.pow 2)
    · have := h.bddD p' l' x'
      rw [abs_pow]
      nlinarith [abs_nonneg (D p' l' x')]
  have hnn : 0 ≤ (stepMD μ m α β F D p l x) ^ 2 := sq_nonneg _
  simp only [stepMVar]
  linarith

/-- A triple `(F, D, E)` in which `(F, D)` is a good family, `E` is the `l`-derivative
of `D`, and `E` takes values in `[0, c]`. -/
structure GoodTriple (F D E : P → ℝ → ℝ × ℝ → ℝ) (c : ℝ) : Prop where
  good : GoodFam F D
  contE : Continuous fun w : P × ℝ × (ℝ × ℝ) => E w.1 w.2.1 w.2.2
  derivD : ∀ p l x, HasDerivAt (fun l' => D p l' x) (E p l x) l
  nonnegE : ∀ p l x, 0 ≤ E p l x
  bddE : ∀ p l x, E p l x ≤ c

lemma GoodTriple.absE {c : ℝ} (h : GoodTriple F D E c) (p : P) (l : ℝ) (x : ℝ × ℝ) :
    |E p l x| ≤ c := by
  have h1 := h.nonnegE p l x
  have h2 := h.bddE p l x
  rw [abs_le]
  constructor <;> linarith

/-- One finite recursion step turns a good triple with bound `c` into a good triple
with bound `c + m`. -/
theorem goodTriple_finiteStep (hμ : ExpMoments μ) [IsProbabilityMeasure μ]
    [FirstCountableTopology P] {c : ℝ} (h : GoodTriple F D E c) (hm : 0 ≤ m)
    (hα : Continuous α) (hβ : Continuous β) :
    GoodTriple (finiteStep μ m α β F) (finiteStepD μ m α β F D)
      (finiteStepDD μ m α β F D E) (c + m) := by
  rcases eq_or_lt_of_le hm with h0 | hpos
  · have hm0 : m = 0 := h0.symm
    subst hm0
    simp only [finiteStep, finiteStepD, finiteStepDD, add_zero]
    refine
      { good := step0_good hμ h.good hα hβ
        contE := ?_
        derivD := fun p l x =>
          hasDeriv_step0_gen h.good.contD h.good.bddD h.contE h.derivD h.absE p l x
        nonnegE := fun p l x => ?_
        bddE := fun p l x => ?_ }
    · refine continuous_step0 hμ h.contE hα hβ ?_
      intro w₀
      refine ⟨c, 0, ?_⟩
      filter_upwards with w z
      simpa using h.absE w.1 w.2.1 _
    · show (0:ℝ) ≤ ∫ z, E p l (x.1 + α p * z, x.2 + β p * z) ∂μ
      exact integral_nonneg fun z => h.nonnegE _ _ _
    · show (∫ z, E p l (x.1 + α p * z, x.2 + β p * z) ∂μ) ≤ c
      have hint := integrable_shiftG (μ := μ) h.contE h.absE p l (α p) (β p) x
      calc (∫ z, E p l (x.1 + α p * z, x.2 + β p * z) ∂μ)
          ≤ ∫ _z : ℝ, c ∂μ :=
            integral_mono hint (integrable_const c) (fun z => h.bddE _ _ _)
        _ = c := by simp
  · have hne : m ≠ 0 := ne_of_gt hpos
    simp only [finiteStep, finiteStepD, finiteStepDD, if_neg hne]
    refine
      { good := stepM_good hμ h.good hpos hα hβ
        contE := ?_
        derivD := fun p l x =>
          hasDeriv_stepMD hμ h.good hpos h.contE h.derivD h.absE p l x
        nonnegE := fun p l x => ?_
        bddE := fun p l x => ?_ }
    · have h1 : Continuous fun w : P × ℝ × (ℝ × ℝ) => stepMD μ m α β F E w.1 w.2.1 w.2.2 :=
        continuous_stepMD_gen hμ h.good hpos.le hα hβ h.contE h.absE
      have h2 : Continuous fun w : P × ℝ × (ℝ × ℝ) =>
          stepMD μ m α β F (fun p' l' x' => (D p' l' x') ^ 2) w.1 w.2.1 w.2.2 := by
        refine continuous_stepMD_gen (c := 1) hμ h.good hpos.le hα hβ (h.good.contD.pow 2)
          (fun p' l' x' => ?_)
        have := h.good.bddD p' l' x'
        rw [abs_pow]
        nlinarith [abs_nonneg (D p' l' x')]
      have h3 : Continuous fun w : P × ℝ × (ℝ × ℝ) => stepMD μ m α β F D w.1 w.2.1 w.2.2 :=
        continuous_stepMD_gen (c := 1) hμ h.good hpos.le hα hβ h.good.contD h.good.bddD
      simp only [stepMVar]
      exact h1.add (continuous_const.mul (h2.sub (h3.pow 2)))
    · have hE := stepMD_nonneg (α := α) (β := β) hμ h.good hpos.le h.nonnegE p l x
      have hV := stepMVar_nonneg (α := α) (β := β) hμ h.good hpos.le p l x
      have : 0 ≤ m * stepMVar μ m α β F D p l x := mul_nonneg hpos.le hV
      linarith
    · have hE := stepMD_le (α := α) (β := β) hμ h.good hpos.le h.contE h.absE p l x
      have hV := stepMVar_le_one (α := α) (β := β) hμ h.good hpos.le p l x
      nlinarith

end Propagate

end GTFrame

namespace SpinGlass.AT

/-! ## The terminal function -/

/-- The numerator in the logarithmic derivative of `gtTerminal`. -/
def gtTerminalNumerator (lam x₁ x₂ : ℝ) : ℝ :=
  Real.exp (x₁ + x₂ + lam) - Real.exp (x₁ - x₂ - lam) -
    Real.exp (-x₁ + x₂ - lam) + Real.exp (-x₁ - x₂ + lam)

/-- The positive partition sum occurring in `gtTerminal`. -/
def gtTerminalSum (lam x₁ x₂ : ℝ) : ℝ :=
  Real.exp (x₁ + x₂ + lam) + Real.exp (x₁ - x₂ - lam) +
    Real.exp (-x₁ + x₂ - lam) + Real.exp (-x₁ - x₂ + lam)

private lemma gtTerminalSum_pos (lam x₁ x₂ : ℝ) :
    0 < gtTerminalSum lam x₁ x₂ := by
  unfold gtTerminalSum
  positivity

/-- Exact first derivative of the canonical terminal condition in `lam`. -/
lemma hasDerivAt_gtTerminal (lam x₁ x₂ : ℝ) :
    HasDerivAt (fun l => gtTerminal l x₁ x₂)
      (gtTerminalNumerator lam x₁ x₂ / gtTerminalSum lam x₁ x₂) lam := by
  let A : ℝ → ℝ := fun l => Real.exp (x₁ + x₂ + l)
  let B : ℝ → ℝ := fun l => Real.exp (x₁ - x₂ - l)
  let C : ℝ → ℝ := fun l => Real.exp (-x₁ + x₂ - l)
  let D : ℝ → ℝ := fun l => Real.exp (-x₁ - x₂ + l)
  have hA : HasDerivAt A (A lam) lam := by
    dsimp [A]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id lam).const_add (x₁ + x₂)).exp
  have hB : HasDerivAt B (-B lam) lam := by
    dsimp [B]
    simpa only [id_eq, mul_neg_one] using
      ((hasDerivAt_id lam).const_sub (x₁ - x₂)).exp
  have hC : HasDerivAt C (-C lam) lam := by
    dsimp [C]
    simpa only [id_eq, mul_neg_one] using
      ((hasDerivAt_id lam).const_sub (-x₁ + x₂)).exp
  have hD : HasDerivAt D (D lam) lam := by
    dsimp [D]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id lam).const_add (-x₁ - x₂)).exp
  have hsum := (((hA.add hB).add hC).add hD)
  have hquot := hsum.div_const 4
  have hpos : 0 < ((A + B + C + D) lam) / 4 := by
    dsimp [A, B, C, D]
    positivity
  have hlog := hquot.log hpos.ne'
  convert hlog using 1
  · funext l
    simp only [gtTerminal, A, B, C, D, Pi.add_apply]
  · simp only [gtTerminalNumerator, gtTerminalSum, A, B, C, D, Pi.add_apply]
    field_simp
    ring

/-- The first `lam`-derivative of `gtTerminal` has absolute value at most one. -/
lemma abs_deriv_gtTerminal_le_one (lam x₁ x₂ : ℝ) :
    |deriv (fun l => gtTerminal l x₁ x₂) lam| ≤ 1 := by
  rw [(hasDerivAt_gtTerminal lam x₁ x₂).deriv]
  have hpos := gtTerminalSum_pos lam x₁ x₂
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hpos]
    unfold gtTerminalNumerator gtTerminalSum
    nlinarith [Real.exp_pos (x₁ + x₂ + lam), Real.exp_pos (x₁ - x₂ - lam),
      Real.exp_pos (-x₁ + x₂ - lam), Real.exp_pos (-x₁ - x₂ + lam)]
  · rw [div_le_iff₀ hpos]
    unfold gtTerminalNumerator gtTerminalSum
    nlinarith [Real.exp_pos (x₁ + x₂ + lam), Real.exp_pos (x₁ - x₂ - lam),
      Real.exp_pos (-x₁ + x₂ - lam), Real.exp_pos (-x₁ - x₂ + lam)]

/-! ## Canonical finite recursion -/

/--
Uniform multiplier-derivative bounds for the recursion defined in
`Lemmas.AT.Definitions`. The statement refers directly to `gtSemigroupSolution` and
`gtFunctional`, whose branches are built from `gtDiagonalStep` and
`gtRankOneStep`.
-/
private abbrev gauss : Measure ℝ := gaussianReal 0 1

private lemma integral_exp_add_mul (a t : ℝ) :
    (∫ z, Real.exp (a + t * z) ∂gauss) = Real.exp (a + t ^ 2 / 2) := by
  have hmgf := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id_eq, zero_mul, NNReal.coe_one, one_mul, zero_add] at hmgf
  rw [show (fun z : ℝ => Real.exp (a + t * z)) =
      fun z => Real.exp a * Real.exp (t * z) by
        funext z
        rw [Real.exp_add]]
  rw [integral_const_mul, hmgf, ← Real.exp_add]

private lemma integrable_exp_add_mul (a t : ℝ) :
    Integrable (fun z => Real.exp (a + t * z)) gauss := by
  rw [show (fun z : ℝ => Real.exp (a + t * z)) =
      fun z => Real.exp a * Real.exp (t * z) by
        funext z
        rw [Real.exp_add]]
  exact (integrable_exp_mul_gaussianReal t).const_mul _

private lemma rankOne_one_zero_terminal (scale l x₁ x₂ : ℝ) :
    gtRankOneStep 1 scale 0 (gtTerminal l) x₁ x₂ =
      gtTerminal l x₁ x₂ + scale ^ 2 / 2 := by
  simp only [gtRankOneStep, one_ne_zero, if_false, one_div, one_mul,
    standardGaussianExpectation]
  have hpoint : (fun z => Real.exp (gtTerminal l (x₁ + scale * z) (x₂ + 0 * scale * z))) =
      fun z => (Real.exp (x₁ + scale * z + x₂ + l) +
        Real.exp (x₁ + scale * z - x₂ - l) +
        Real.exp (-(x₁ + scale * z) + x₂ - l) +
        Real.exp (-(x₁ + scale * z) - x₂ + l)) / 4 := by
    funext z
    simp only [zero_mul, add_zero]
    rw [gtTerminal, Real.exp_log]
    positivity
  rw [hpoint]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]
  have hi1 : Integrable (fun z => Real.exp (x₁ + scale * z + x₂ + l)) gauss := by
    convert integrable_exp_add_mul (x₁ + x₂ + l) scale using 1 <;> ring
  have hi2 : Integrable (fun z => Real.exp (x₁ + scale * z - x₂ - l)) gauss := by
    convert integrable_exp_add_mul (x₁ - x₂ - l) scale using 1 <;> ring
  have hi3 : Integrable (fun z => Real.exp (-(x₁ + scale * z) + x₂ - l)) gauss := by
    convert integrable_exp_add_mul (-x₁ + x₂ - l) (-scale) using 1 <;> ring
  have hi4 : Integrable (fun z => Real.exp (-(x₁ + scale * z) - x₂ + l)) gauss := by
    convert integrable_exp_add_mul (-x₁ - x₂ + l) (-scale) using 1 <;> ring
  have h12 :
      (∫ z, Real.exp (x₁ + scale * z + x₂ + l) +
          Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) =
        (∫ z, Real.exp (x₁ + scale * z + x₂ + l) ∂gauss) +
        (∫ z, Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) := by
    simpa only [Pi.add_apply] using integral_add hi1 hi2
  have h123 :
      (∫ z, Real.exp (x₁ + scale * z + x₂ + l) +
          Real.exp (x₁ + scale * z - x₂ - l) +
          Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) =
        (∫ z, Real.exp (x₁ + scale * z + x₂ + l) ∂gauss) +
        (∫ z, Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) +
        (∫ z, Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) := by
    calc
      _ = (∫ z, Real.exp (x₁ + scale * z + x₂ + l) +
              Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) +
            (∫ z, Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) := by
          simpa only [Pi.add_apply] using integral_add (hi1.add hi2) hi3
      _ = _ := by rw [h12]
  have hsplit :
      (∫ z, Real.exp (x₁ + scale * z + x₂ + l) +
          Real.exp (x₁ + scale * z - x₂ - l) +
          Real.exp (-(x₁ + scale * z) + x₂ - l) +
          Real.exp (-(x₁ + scale * z) - x₂ + l) ∂gauss) =
        (∫ z, Real.exp (x₁ + scale * z + x₂ + l) ∂gauss) +
        (∫ z, Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) +
        (∫ z, Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) +
        (∫ z, Real.exp (-(x₁ + scale * z) - x₂ + l) ∂gauss) := by
    calc
      _ = (∫ z, Real.exp (x₁ + scale * z + x₂ + l) +
              Real.exp (x₁ + scale * z - x₂ - l) +
              Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) +
            (∫ z, Real.exp (-(x₁ + scale * z) - x₂ + l) ∂gauss) := by
          simpa only [Pi.add_apply] using integral_add ((hi1.add hi2).add hi3) hi4
      _ = _ := by rw [h123]
  rw [hsplit]
  have hv1 : (∫ z, Real.exp (x₁ + scale * z + x₂ + l) ∂gauss) =
      Real.exp (x₁ + x₂ + l + scale ^ 2 / 2) := by
    convert integral_exp_add_mul (x₁ + x₂ + l) scale using 1 <;> ring
  have hv2 : (∫ z, Real.exp (x₁ + scale * z - x₂ - l) ∂gauss) =
      Real.exp (x₁ - x₂ - l + scale ^ 2 / 2) := by
    convert integral_exp_add_mul (x₁ - x₂ - l) scale using 1 <;> ring
  have hv3 : (∫ z, Real.exp (-(x₁ + scale * z) + x₂ - l) ∂gauss) =
      Real.exp (-x₁ + x₂ - l + (-scale) ^ 2 / 2) := by
    convert integral_exp_add_mul (-x₁ + x₂ - l) (-scale) using 1 <;> ring
  have hv4 : (∫ z, Real.exp (-(x₁ + scale * z) - x₂ + l) ∂gauss) =
      Real.exp (-x₁ - x₂ + l + (-scale) ^ 2 / 2) := by
    convert integral_exp_add_mul (-x₁ - x₂ + l) (-scale) using 1 <;> ring
  rw [hv1, hv2, hv3, hv4, gtTerminal]
  have hsum : 0 < (Real.exp (x₁ + x₂ + l) + Real.exp (x₁ - x₂ - l) +
      Real.exp (-x₁ + x₂ - l) + Real.exp (-x₁ - x₂ + l)) / 4 := by positivity
  have hfactor :
      (Real.exp (x₁ + x₂ + l + scale ^ 2 / 2) +
          Real.exp (x₁ - x₂ - l + scale ^ 2 / 2) +
          Real.exp (-x₁ + x₂ - l + (-scale) ^ 2 / 2) +
          Real.exp (-x₁ - x₂ + l + (-scale) ^ 2 / 2)) * 4⁻¹ =
        Real.exp (scale ^ 2 / 2) *
          ((Real.exp (x₁ + x₂ + l) + Real.exp (x₁ - x₂ - l) +
            Real.exp (-x₁ + x₂ - l) + Real.exp (-x₁ - x₂ + l)) / 4) := by
    rw [show (-scale) ^ 2 = scale ^ 2 by ring]
    simp_rw [Real.exp_add]
    ring
  rw [hfactor, Real.log_mul (Real.exp_ne_zero _) hsum.ne', Real.log_exp]
  ring

private lemma gtTerminal_swap (l x₁ x₂ : ℝ) :
    gtTerminal l x₂ x₁ = gtTerminal l x₁ x₂ := by
  unfold gtTerminal
  congr 2
  ring_nf

private lemma rankOne_one_zero_terminal_snd (scale l x₁ x₂ : ℝ) :
    Real.log (standardGaussianExpectation (fun z =>
      Real.exp (gtTerminal l x₁ (x₂ + scale * z)))) =
      gtTerminal l x₁ x₂ + scale ^ 2 / 2 := by
  have h := rankOne_one_zero_terminal scale l x₂ x₁
  simp only [gtRankOneStep, one_ne_zero, if_false, one_div, one_mul, zero_mul,
    add_zero] at h
  rw [← gtTerminal_swap l x₂ x₁] at h
  calc
    _ = Real.log (standardGaussianExpectation (fun z =>
          Real.exp (gtTerminal l (x₂ + scale * z) x₁))) := by
        congr 3
        funext z
        rw [gtTerminal_swap]
    _ = _ := by norm_num at h ⊢; exact h

private lemma rankOne_one_zero_terminal_add (scale l k x₁ x₂ : ℝ) :
    gtRankOneStep 1 scale 0 (fun y₁ y₂ => gtTerminal l y₁ y₂ + k) x₁ x₂ =
      gtTerminal l x₁ x₂ + scale ^ 2 / 2 + k := by
  have hbase := rankOne_one_zero_terminal scale l x₁ x₂
  simp only [gtRankOneStep, one_ne_zero, if_false, one_div, one_mul, zero_mul,
    add_zero] at hbase ⊢
  have hpos : 0 < standardGaussianExpectation (fun z =>
      Real.exp (gtTerminal l (x₁ + scale * z) x₂)) := by
    unfold standardGaussianExpectation
    simpa using GTFrame.integral_expShift_pos (GTFrame.expMoments_gaussianReal 0 1)
      (GTFrame.goodFam_fLbase (P := Unit)) (m := (1 : ℝ)) (by norm_num)
      () l scale 0 (x₁, x₂)
  have hfun : (fun z => Real.exp (gtTerminal l (x₁ + scale * z) x₂ + k)) =
      fun z => Real.exp k * Real.exp (gtTerminal l (x₁ + scale * z) x₂) := by
    funext z
    rw [add_comm, Real.exp_add]
  rw [hfun]
  unfold standardGaussianExpectation at hbase hpos ⊢
  rw [integral_const_mul, Real.log_mul (Real.exp_ne_zero k) hpos.ne', Real.log_exp,
    ]
  norm_num at hbase ⊢
  linarith

private lemma diagonal_one_terminal (scale l x₁ x₂ : ℝ) :
    gtDiagonalStep 1 scale (gtTerminal l) x₁ x₂ =
      gtTerminal l x₁ x₂ + scale ^ 2 := by
  simp only [gtDiagonalStep, one_ne_zero, if_false, one_div, one_mul]
  have hsnd : ∀ y₁ y₂,
      Real.log (standardGaussianExpectation (fun z =>
        Real.exp (gtTerminal l y₁ (y₂ + scale * z)))) =
        gtTerminal l y₁ y₂ + scale ^ 2 / 2 :=
    rankOne_one_zero_terminal_snd scale l
  have hpos : ∀ y₁ y₂, 0 < standardGaussianExpectation (fun z =>
      Real.exp (gtTerminal l y₁ (y₂ + scale * z))) := by
    intro y₁ y₂
    unfold standardGaussianExpectation
    simpa using GTFrame.integral_expShift_pos (GTFrame.expMoments_gaussianReal 0 1)
      (GTFrame.goodFam_fLbase (P := Unit)) (m := (1 : ℝ)) (by norm_num)
      () l 0 scale (y₁, y₂)
  have hinner : ∀ y₁ y₂,
      standardGaussianExpectation (fun z => Real.exp (gtTerminal l y₁ (y₂ + scale * z))) =
        Real.exp (gtTerminal l y₁ y₂ + scale ^ 2 / 2) := by
    intro y₁ y₂
    rw [← hsnd y₁ y₂, Real.exp_log (hpos y₁ y₂)]
  simp_rw [hinner]
  have h := rankOne_one_zero_terminal_add scale l (scale ^ 2 / 2) x₁ x₂
  simp only [gtRankOneStep, one_ne_zero, if_false, one_div, one_mul, zero_mul,
    add_zero] at h
  norm_num at h ⊢
  nlinarith

/-- A level-one independent Gaussian step adds only its covariance constant
to the two-replica terminal condition.  This public form is useful when
computing multiplier derivatives at the endpoint. -/
lemma gtDiagonalStep_one_terminal (scale l x₁ x₂ : ℝ) :
    gtDiagonalStep 1 scale (gtTerminal l) x₁ x₂ =
      gtTerminal l x₁ x₂ + scale ^ 2 :=
  diagonal_one_terminal scale l x₁ x₂

private def rankStep (m scale sign : ℝ)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) : Unit → ℝ → ℝ × ℝ → ℝ :=
  GTFrame.finiteStep gauss m (fun _ => scale) (fun _ => sign * scale) F

private def diagonalStep (m scale : ℝ)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) : Unit → ℝ → ℝ × ℝ → ℝ :=
  GTFrame.finiteStep gauss m (fun _ => scale) (fun _ => 0)
    (GTFrame.finiteStep gauss m (fun _ => 0) (fun _ => scale) F)

private lemma rankStep_apply (m scale sign : ℝ)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) (l x₁ x₂ : ℝ) :
    rankStep m scale sign F () l (x₁, x₂) =
      gtRankOneStep m scale sign (fun y₁ y₂ => F () l (y₁, y₂)) x₁ x₂ := by
  by_cases hm : m = 0
  · simp [rankStep, GTFrame.finiteStep, GTFrame.step0, gtRankOneStep,
      standardGaussianExpectation, gauss, hm]
  · simp [rankStep, GTFrame.finiteStep, GTFrame.stepM, gtRankOneStep,
      standardGaussianExpectation, gauss, hm, mul_assoc]

private lemma diagonalStep_zero_apply
    (scale : ℝ) (F : Unit → ℝ → ℝ × ℝ → ℝ) (l x₁ x₂ : ℝ) :
    diagonalStep 0 scale F () l (x₁, x₂) =
      gtDiagonalStep 0 scale (fun y₁ y₂ => F () l (y₁, y₂)) x₁ x₂ := by
  simp [diagonalStep, GTFrame.finiteStep, GTFrame.step0, gtDiagonalStep,
    standardGaussianExpectation, gauss]

private def terminalD : Unit → ℝ → ℝ × ℝ → ℝ :=
  fun _ l x => GTFrame.fLbaseD l x

private def terminalE : Unit → ℝ → ℝ × ℝ → ℝ :=
  fun _ l x => GTFrame.fLbaseDD l x

private def upperF (scale : ℝ) : Unit → ℝ → ℝ × ℝ → ℝ :=
  fun _ l x => GTFrame.fLbase l x + scale ^ 2

private lemma upper_goodTriple (scale : ℝ) :
    GTFrame.GoodTriple (upperF scale) terminalD terminalE 1 := by
  refine
    { good := ?_
      contE := GTFrame.continuous_fLbaseDD.comp (by fun_prop)
      derivD := fun _ l x => GTFrame.hasDerivAt_fLbaseD l x
      nonnegE := fun _ l x => GTFrame.fLbaseDD_nonneg l x
      bddE := fun _ l x => GTFrame.fLbaseDD_le_one l x }
  exact
    { contF := (GTFrame.continuous_fLbase.comp (by fun_prop)).add continuous_const
      contD := GTFrame.continuous_fLbaseD.comp (by fun_prop)
      hasDeriv := fun _ l x => (GTFrame.hasDerivAt_fLbase l x).add_const _
      lipx := by
        intro _ l x y
        simpa [upperF] using GTFrame.fLbase_lipx l x y
      bddD := fun _ l x => GTFrame.fLbaseD_bdd l x }

private lemma upperF_apply (scale l x₁ x₂ : ℝ) :
    upperF scale () l (x₁, x₂) =
      gtDiagonalStep 1 scale (gtTerminal l) x₁ x₂ := by
  rw [diagonal_one_terminal]
  rfl

private lemma rankStep_good {F D E : Unit → ℝ → ℝ × ℝ → ℝ} {c m : ℝ}
    (h : GTFrame.GoodTriple F D E c) (hm : 0 ≤ m) (scale sign : ℝ) :
    GTFrame.GoodTriple (rankStep m scale sign F)
      (GTFrame.finiteStepD gauss m (fun _ => scale) (fun _ => sign * scale) F D)
      (GTFrame.finiteStepDD gauss m (fun _ => scale) (fun _ => sign * scale) F D E)
      (c + m) := by
  exact GTFrame.goodTriple_finiteStep (GTFrame.expMoments_gaussianReal 0 1)
    h hm continuous_const continuous_const

private lemma diagonalStep_zero_good {F D E : Unit → ℝ → ℝ × ℝ → ℝ} {c : ℝ}
    (h : GTFrame.GoodTriple F D E c) (scale : ℝ) :
    ∃ D' E', GTFrame.GoodTriple (diagonalStep 0 scale F) D' E' c := by
  let D₁ := GTFrame.finiteStepD gauss 0 (fun _ : Unit => 0) (fun _ => scale) F D
  let E₁ := GTFrame.finiteStepDD gauss 0 (fun _ : Unit => 0) (fun _ => scale) F D E
  have h₁ : GTFrame.GoodTriple
      (GTFrame.finiteStep gauss 0 (fun _ : Unit => 0) (fun _ => scale) F) D₁ E₁ c := by
    simpa [D₁, E₁] using GTFrame.goodTriple_finiteStep
      (GTFrame.expMoments_gaussianReal 0 1) h (by norm_num : (0 : ℝ) ≤ 0)
      continuous_const continuous_const
  let D₂ := GTFrame.finiteStepD gauss 0 (fun _ : Unit => scale) (fun _ => 0)
    (GTFrame.finiteStep gauss 0 (fun _ : Unit => 0) (fun _ => scale) F) D₁
  let E₂ := GTFrame.finiteStepDD gauss 0 (fun _ : Unit => scale) (fun _ => 0)
    (GTFrame.finiteStep gauss 0 (fun _ : Unit => 0) (fun _ => scale) F) D₁ E₁
  refine ⟨D₂, E₂, ?_⟩
  simpa [diagonalStep, D₂, E₂] using GTFrame.goodTriple_finiteStep
    (GTFrame.expMoments_gaussianReal 0 1) h₁ (by norm_num : (0 : ℝ) ≤ 0)
    continuous_const continuous_const

private lemma bounds_of_goodTriple {F D E : Unit → ℝ → ℝ × ℝ → ℝ} {c : ℝ}
    (h : GTFrame.GoodTriple F D E c) (hc : c ≤ 5 / 2) (lam x₁ x₂ : ℝ) :
    |deriv (fun l => F () l (x₁, x₂)) lam| ≤ 1 ∧
      0 ≤ deriv (deriv (fun l => F () l (x₁, x₂))) lam ∧
      deriv (deriv (fun l => F () l (x₁, x₂))) lam ≤ 5 / 2 := by
  have hfirst : ∀ l, deriv (fun t => F () t (x₁, x₂)) l = D () l (x₁, x₂) :=
    fun l => (h.good.hasDeriv () l (x₁, x₂)).deriv
  have hderiv : deriv (fun t => F () t (x₁, x₂)) = fun l => D () l (x₁, x₂) :=
    funext hfirst
  rw [hfirst lam, hderiv, (h.derivD () lam (x₁, x₂)).deriv]
  exact ⟨h.good.bddD () lam (x₁, x₂), h.nonnegE () lam (x₁, x₂),
    (h.bddE () lam (x₁, x₂)).trans hc⟩

private lemma semigroup_package (β q s v u : ℝ) :
    ∃ F D E c, GTFrame.GoodTriple F D E c ∧ c ≤ 5 / 2 ∧
      ∀ l x₁ x₂, F () l (x₁, x₂) = gtSemigroupSolution β q s l v u x₁ x₂ := by
  let r : ℝ := |v|
  let sign : ℝ := gtPathSign v
  by_cases hqr : q ≤ r
  · by_cases hru : r ≤ u
    · let scaleU := gtIncrementScale β s u 1
      refine ⟨upperF scaleU, terminalD, terminalE, 1,
        upper_goodTriple scaleU, by norm_num, ?_⟩
      intro l x₁ x₂
      rw [upperF_apply]
      simp [gtSemigroupSolution, r, sign, hqr, hru, scaleU]
    · have hur : u < r := lt_of_not_ge hru
      by_cases hqu : q ≤ u
      · let scaleR := gtIncrementScale β s r 1
        let scaleUR := gtIncrementScale β s u r
        let F := rankStep (1 / 2) scaleUR sign (upperF scaleR)
        have hF := rankStep_good (upper_goodTriple scaleR)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) scaleUR sign
        refine ⟨F, _, _, 1 + 1 / 2, hF, by norm_num, ?_⟩
        intro l x₁ x₂
        dsimp [F]
        rw [rankStep_apply]
        simp_rw [upperF_apply]
        simp [gtSemigroupSolution, r, sign, hqr, hru, hqu, scaleR, scaleUR]
      · have huq : u < q := lt_of_not_ge hqu
        let scaleR := gtIncrementScale β s r 1
        let scaleQR := gtIncrementScale β s q r
        let atQ := rankStep (1 / 2) scaleQR sign (upperF scaleR)
        have hatQ := rankStep_good (upper_goodTriple scaleR)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) scaleQR sign
        let scaleUQ := gtIncrementScale β s u q
        let F := rankStep 0 scaleUQ sign atQ
        have hF := rankStep_good hatQ (by norm_num : (0 : ℝ) ≤ 0) scaleUQ sign
        refine ⟨F, _, _, (1 + 1 / 2) + 0, hF, by norm_num, ?_⟩
        intro l x₁ x₂
        dsimp [F, atQ]
        rw [rankStep_apply]
        simp_rw [rankStep_apply, upperF_apply]
        simp [gtSemigroupSolution, r, sign, hqr, hru, hqu, scaleR, scaleQR, scaleUQ]
  · have hrq : r < q := lt_of_not_ge hqr
    by_cases hqu : q ≤ u
    · let scaleU := gtIncrementScale β s u 1
      refine ⟨upperF scaleU, terminalD, terminalE, 1,
        upper_goodTriple scaleU, by norm_num, ?_⟩
      intro l x₁ x₂
      rw [upperF_apply]
      simp [gtSemigroupSolution, r, sign, hqr, hqu, scaleU]
    · have huq : u < q := lt_of_not_ge hqu
      by_cases hru : r ≤ u
      · let scaleQ := gtIncrementScale β s q 1
        let scaleUQ := gtIncrementScale β s u q
        obtain ⟨D, E, hF⟩ := diagonalStep_zero_good (upper_goodTriple scaleQ) scaleUQ
        refine ⟨diagonalStep 0 scaleUQ (upperF scaleQ), D, E, 1, hF,
          by norm_num, ?_⟩
        intro l x₁ x₂
        rw [diagonalStep_zero_apply]
        simp_rw [upperF_apply]
        simp [gtSemigroupSolution, r, sign, hqr, hqu, hru, scaleQ, scaleUQ]
      · have hur : u < r := lt_of_not_ge hru
        let scaleQ := gtIncrementScale β s q 1
        let scaleRQ := gtIncrementScale β s r q
        let atR := diagonalStep 0 scaleRQ (upperF scaleQ)
        obtain ⟨DR, ER, hatR⟩ := diagonalStep_zero_good (upper_goodTriple scaleQ) scaleRQ
        let scaleUR := gtIncrementScale β s u r
        let F := rankStep 0 scaleUR sign atR
        have hF := rankStep_good hatR (by norm_num : (0 : ℝ) ≤ 0) scaleUR sign
        refine ⟨F, _, _, 1 + 0, hF, by norm_num, ?_⟩
        intro l x₁ x₂
        dsimp [F, atR]
        rw [rankStep_apply]
        simp_rw [diagonalStep_zero_apply, upperF_apply]
        simp [gtSemigroupSolution, r, sign, hqr, hqu, hru, scaleQ, scaleRQ, scaleUR]

theorem gt_lambda_derivative_bounds
    (β h q s lam v u x₁ x₂ : ℝ) :
    (|deriv (fun l => gtSemigroupSolution β q s l v u x₁ x₂) lam| ≤ 1 ∧
      0 ≤ deriv (deriv (fun l =>
        gtSemigroupSolution β q s l v u x₁ x₂)) lam ∧
      deriv (deriv (fun l =>
        gtSemigroupSolution β q s l v u x₁ x₂)) lam ≤ 5 / 2) ∧
    (0 ≤ deriv (deriv (fun l => gtFunctional β h q s l v)) lam ∧
      deriv (deriv (fun l => gtFunctional β h q s l v)) lam ≤ 5 / 2) := by
  /-
  The terminal second derivative is the variance of a sign and lies in
  `[0, 1]`. A finite-mass GT step adds its mass times a tilted variance.
  The canonical branches have masses `1` and, when present, `1 / 2`; mass-zero
  Gaussian steps preserve the bound. Differentiation of the outer Gaussian
  expectation gives the functional estimate because its remaining `lam` term
  is affine.
  -/
  obtain ⟨F, D, E, c, hF, hc, heq⟩ := semigroup_package β q s v u
  have hsemigroup := bounds_of_goodTriple hF hc lam x₁ x₂
  have hfun : (fun l => gtSemigroupSolution β q s l v u x₁ x₂) =
      fun l => F () l (x₁, x₂) := by
    funext l
    exact (heq l x₁ x₂).symm
  rw [hfun]
  refine ⟨hsemigroup, ?_⟩
  obtain ⟨F₀, D₀, E₀, c₀, hF₀, hc₀, heq₀⟩ := semigroup_package β q s v 0
  let scale := β * Real.sqrt ((1 - s) * q)
  let Fout := rankStep 0 scale 1 F₀
  have hout := rankStep_good hF₀ (by norm_num : (0 : ℝ) ≤ 0) scale 1
  have hcOut : c₀ + 0 ≤ 5 / 2 := by linarith
  have houtEq : ∀ l,
      Fout () l (h, h) = standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s l v 0
          (h + scale * z) (h + scale * z)) := by
    intro l
    dsimp [Fout]
    rw [rankStep_apply]
    simp only [gtRankOneStep, if_pos rfl, standardGaussianExpectation, zero_mul,
      one_mul, if_true]
    congr 1
    funext z
    rw [heq₀]
  have hfunctional : (fun l => gtFunctional β h q s l v) = fun l =>
      2 * Real.log 2 + Fout () l (h, h) - l * v - gtCorrection β q s := by
    funext l
    rw [gtFunctional, houtEq]
  rw [hfunctional]
  have hfirstOut : deriv (fun l =>
      2 * Real.log 2 + Fout () l (h, h) - l * v - gtCorrection β q s) =
      fun l =>
        (GTFrame.finiteStepD gauss 0 (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () l (h, h) - v := by
    funext t
    have hd := (((hout.good.hasDeriv () t (h, h)).const_add (2 * Real.log 2)).sub
      ((hasDerivAt_id t).mul_const v)).sub_const (gtCorrection β q s)
    simpa [Fout] using hd.deriv
  rw [hfirstOut]
  have hsecond := (hout.derivD () lam (h, h)).sub_const v
  rw [hsecond.deriv]
  exact ⟨hout.nonnegE () lam (h, h), (hout.bddE () lam (h, h)).trans hcOut⟩

/-- The first multiplier derivative of the GT functional has absolute value
at most two when the prescribed overlap lies in `[-1, 1]`. -/
theorem abs_deriv_gtFunctional_le_two
    (β h q s lam v : ℝ)
    (hv : |v| ≤ 1) :
    |deriv (fun l => gtFunctional β h q s l v) lam| ≤ 2 := by
  obtain ⟨F₀, D₀, E₀, c₀, hF₀, _hc₀, heq₀⟩ :=
    semigroup_package β q s v 0
  let scale := β * Real.sqrt ((1 - s) * q)
  let Fout := rankStep 0 scale 1 F₀
  have hout :=
    rankStep_good hF₀ (by norm_num : (0 : ℝ) ≤ 0) scale 1
  have houtEq : ∀ l,
      Fout () l (h, h) = standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s l v 0
          (h + scale * z) (h + scale * z)) := by
    intro l
    dsimp [Fout]
    rw [rankStep_apply]
    simp only [gtRankOneStep, if_pos rfl, standardGaussianExpectation,
      zero_mul, one_mul, if_true]
    congr 1
    funext z
    rw [heq₀]
  have hfunctional :
      (fun l => gtFunctional β h q s l v) = fun l =>
        2 * Real.log 2 + Fout () l (h, h) - l * v -
          gtCorrection β q s := by
    funext l
    rw [gtFunctional, houtEq]
  have hderiv :
      deriv (fun l => gtFunctional β h q s l v) lam =
        (GTFrame.finiteStepD gauss 0
          (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () lam (h, h) - v := by
    rw [hfunctional]
    have hd :=
      (((hout.good.hasDeriv () lam (h, h)).const_add
        (2 * Real.log 2)).sub
        ((hasDerivAt_id lam).mul_const v)).sub_const
        (gtCorrection β q s)
    simpa [Fout] using hd.deriv
  rw [hderiv]
  calc
    |(GTFrame.finiteStepD gauss 0
          (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () lam (h, h) - v| ≤
        |(GTFrame.finiteStepD gauss 0
          (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () lam (h, h)| + |v| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (hout.good.bddD () lam (h, h)) hv
    _ = 2 := by norm_num

/-- The first multiplier derivative of the GT functional is differentiable.
This is the regularity companion to `gt_lambda_derivative_bounds`. -/
lemma differentiable_deriv_gtFunctional (β h q s v : ℝ) :
    Differentiable ℝ (deriv (fun l => gtFunctional β h q s l v)) := by
  obtain ⟨F₀, D₀, E₀, c₀, hF₀, _hc₀, heq₀⟩ := semigroup_package β q s v 0
  let scale := β * Real.sqrt ((1 - s) * q)
  let Fout := rankStep 0 scale 1 F₀
  have hout := rankStep_good hF₀ (by norm_num : (0 : ℝ) ≤ 0) scale 1
  have houtEq : ∀ l,
      Fout () l (h, h) = standardGaussianExpectation (fun z =>
        gtSemigroupSolution β q s l v 0
          (h + scale * z) (h + scale * z)) := by
    intro l
    dsimp [Fout]
    rw [rankStep_apply]
    simp only [gtRankOneStep, standardGaussianExpectation, zero_mul,
      one_mul, if_true]
    congr 1
    funext z
    rw [heq₀]
  have hfunctional : (fun l => gtFunctional β h q s l v) = fun l =>
      2 * Real.log 2 + Fout () l (h, h) - l * v - gtCorrection β q s := by
    funext l
    rw [gtFunctional, houtEq]
  have hfirst : deriv (fun l =>
      2 * Real.log 2 + Fout () l (h, h) - l * v - gtCorrection β q s) =
      fun l =>
        (GTFrame.finiteStepD gauss 0 (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () l (h, h) - v := by
    funext l
    have hd := (((hout.good.hasDeriv () l (h, h)).const_add (2 * Real.log 2)).sub
      ((hasDerivAt_id l).mul_const v)).sub_const (gtCorrection β q s)
    simpa [Fout] using hd.deriv
  rw [hfunctional, hfirst]
  intro l
  exact ((hout.derivD () l (h, h)).sub_const v).differentiableAt

/-! ## The deterministic coercivity step -/

/-- Convert a Taylor upper bound and a linear derivative gap into a quadratic loss. -/
lemma gt_taylor_quadratic_loss (H : ℝ → ℝ) (d M c delta : ℝ)
    (hM : 0 < M) (hc : 0 < c) (hzero : H 0 ≤ 0)
    (htaylor : ∀ lam, |lam| ≤ 1 →
      H lam ≤ H 0 + d * lam + M / 2 * lam ^ 2)
    (hd_upper : |d| ≤ M) (hd_lower : c * |delta| ≤ |d|) :
    ∃ lam, |lam| ≤ 1 ∧
      H lam ≤ -(c ^ 2 / (2 * M)) * delta ^ 2 := by
  let lam := -d / M
  have hlam : |lam| ≤ 1 := by
    dsimp [lam]
    rw [abs_div, abs_neg, abs_of_pos hM]
    exact (div_le_iff₀ hM).2 (by simpa using hd_upper)
  have ht := htaylor lam hlam
  have hlocal : H lam ≤ -(d ^ 2) / (2 * M) := by
    calc
      H lam ≤ H 0 + d * lam + M / 2 * lam ^ 2 := ht
      _ ≤ 0 + d * lam + M / 2 * lam ^ 2 := by gcongr
      _ = -(d ^ 2) / (2 * M) := by
        dsimp [lam]
        field_simp [ne_of_gt hM]
        ring
  have hsq : c ^ 2 * delta ^ 2 ≤ d ^ 2 := by
    have hmul := mul_self_le_mul_self
      (mul_nonneg hc.le (abs_nonneg delta)) hd_lower
    calc
      c ^ 2 * delta ^ 2 = (c * |delta|) * (c * |delta|) := by
        nlinarith [sq_abs delta]
      _ ≤ |d| * |d| := hmul
      _ = d ^ 2 := by nlinarith [sq_abs d]
  refine ⟨lam, hlam, hlocal.trans ?_⟩
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  calc
    -(d ^ 2) / (2 * M) ≤ -(c ^ 2 * delta ^ 2) / (2 * M) := by
      exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
    _ = -(c ^ 2 / (2 * M)) * delta ^ 2 := by ring



/-! ## Explicit first-derivative formulas -/

/-- Differentiate the outer Gaussian expectation in `gtFunctional`. -/
lemma hasDerivAt_gtFunctional
    (β h q s lam v : ℝ) :
    HasDerivAt (fun l => gtFunctional β h q s l v)
      (standardGaussianExpectation (fun z =>
        deriv (fun l =>
          gtSemigroupSolution β q s l v 0
            (h + β * Real.sqrt ((1 - s) * q) * z)
            (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v) lam := by
  obtain ⟨F₀, D₀, E₀, c₀, hF₀, hc₀, heq₀⟩ :=
    semigroup_package β q s v 0

  let scale : ℝ := β * Real.sqrt ((1 - s) * q)
  let Fout := rankStep 0 scale 1 F₀

  have hout :=
    rankStep_good hF₀ (by norm_num : (0 : ℝ) ≤ 0) scale 1

  have houtEq : ∀ l,
      Fout () l (h, h) =
        standardGaussianExpectation (fun z =>
          gtSemigroupSolution β q s l v 0
            (h + scale * z) (h + scale * z)) := by
    intro l
    dsimp [Fout]
    rw [rankStep_apply]
    simp only [gtRankOneStep, if_pos rfl, standardGaussianExpectation,
      zero_mul, one_mul, if_true]
    congr 1
    funext z
    rw [heq₀]

  have houterD :
      (GTFrame.finiteStepD gauss 0
        (fun _ : Unit => scale) (fun _ => 1 * scale)
        F₀ D₀) () lam (h, h)
        =
      standardGaussianExpectation (fun z =>
        deriv (fun l =>
          gtSemigroupSolution β q s l v 0
            (h + scale * z) (h + scale * z)) lam) := by
    simp only [GTFrame.finiteStepD, if_pos rfl, GTFrame.step0, one_mul]
    unfold standardGaussianExpectation
    apply integral_congr_ae
    filter_upwards with z
    have hfun :
        (fun l => F₀ () l
          (h + scale * z, h + scale * z))
          =
        (fun l =>
          gtSemigroupSolution β q s l v 0
            (h + scale * z) (h + scale * z)) := by
      funext l
      exact heq₀ l _ _
    have hd :=
      (hF₀.good.hasDeriv () lam
        (h + scale * z, h + scale * z)).deriv
    rw [hfun] at hd
    exact hd.symm

  have hfunctional :
      (fun l => gtFunctional β h q s l v)
        =
      (fun l =>
        2 * Real.log 2 + Fout () l (h, h)
          - l * v - gtCorrection β q s) := by
    funext l
    rw [gtFunctional, houtEq]

  have hbase :
      HasDerivAt
        (fun l =>
          2 * Real.log 2 + Fout () l (h, h)
            - l * v - gtCorrection β q s)
        ((GTFrame.finiteStepD gauss 0
          (fun _ : Unit => scale) (fun _ => 1 * scale)
          F₀ D₀) () lam (h, h) - v) lam := by
    have hd :=
      (((hout.good.hasDeriv () lam (h, h)).const_add
        (2 * Real.log 2)).sub
        ((hasDerivAt_id lam).mul_const v)).sub_const
        (gtCorrection β q s)
    simpa [Fout] using hd

  rw [houterD] at hbase
  rw [hfunctional]
  simpa [scale] using hbase


lemma deriv_gtFunctional_eq
    (β h q s lam v : ℝ) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtSemigroupSolution β q s l v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  exact (hasDerivAt_gtFunctional β h q s lam v).deriv


/-! ### Case `|v| = 0` -/

lemma gtFunctional_formula_abs_v_eq_zero
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hv : |v| = 0) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal lam))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - gtCorrection β q s := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  simp [gtFunctional, gtSemigroupSolution, hq0]


lemma deriv_gtFunctional_formula_abs_v_eq_zero
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hv : |v| = 0) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal l))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  rw [deriv_gtFunctional_eq]
  simp only [sub_zero]
  apply congrArg standardGaussianExpectation
  funext z
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hfun :
      (fun l =>
        gtSemigroupSolution β q s l 0 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
        =
      (fun l =>
        gtDiagonalStep 0 (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1 (gtIncrementScale β s q 1)
            (gtTerminal l))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    funext l
    simp [gtSemigroupSolution, hq0]
  rw [hfun]


/-! ### Case `0 < |v| < q` -/

lemma gtFunctional_formula_abs_v_lt_q
    (β h q s lam v : ℝ)
    (hv0 : 0 < |v|) (hvq : |v| < q) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hqr : ¬ q ≤ |v| := not_le.mpr hvq
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hv0
  have hqpos : 0 < q := lt_trans hv0 hvq
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hqpos
  simp [gtFunctional, gtSemigroupSolution, hqr, hr0, hq0]


lemma deriv_gtFunctional_formula_abs_v_lt_q
    (β h q s lam v : ℝ)
    (hv0 : 0 < |v|) (hvq : |v| < q) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun x : ℝ => x - v)
  apply congrArg standardGaussianExpectation
  funext z

  have hqr : ¬ q ≤ |v| := not_le.mpr hvq
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hv0
  have hqpos : 0 < q := lt_trans hv0 hvq
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hqpos

  have hfun :
      (fun l =>
        gtSemigroupSolution β q s l v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
        =
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|) (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    funext l
    simp [gtSemigroupSolution, hqr, hr0, hq0]

  rw [hfun]


/-! ### Case `q ≤ |v| < 1` -/

lemma gtFunctional_formula_q_le_abs_v_lt_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hqv : q ≤ |v|) (_hv1 : |v| < 1) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hrpos : 0 < |v| := lt_of_lt_of_le hq hqv
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  simp [gtFunctional, gtSemigroupSolution, hqv, hr0, hq0]


lemma deriv_gtFunctional_formula_q_le_abs_v_lt_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hqv : q ≤ |v|) (_hv1 : |v| < 1) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun x : ℝ => x - v)
  apply congrArg standardGaussianExpectation
  funext z

  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hrpos : 0 < |v| := lt_of_lt_of_le hq hqv
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos

  have hfun :
      (fun l =>
        gtSemigroupSolution β q s l v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
        =
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    funext l
    simp [gtSemigroupSolution, hqv, hr0, hq0]

  rw [hfun]


/-! ### Case `|v| = 1` -/

lemma gtFunctional_formula_abs_v_eq_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    gtFunctional β h q s lam v
      =
    2 * Real.log 2
      + standardGaussianExpectation (fun z =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal lam)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
      - lam * v - gtCorrection β q s := by
  have hqv : q ≤ |v| := by
    simpa [hv] using hq1
  have hrpos : 0 < |v| := by
    rw [hv]
    norm_num
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num
  simp [gtFunctional, gtSemigroupSolution, hv, hq1, hqv, hr0, hq0, h10]


lemma deriv_gtFunctional_formula_abs_v_eq_one
    (β h q s lam v : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    deriv (fun l => gtFunctional β h q s l v) lam
      =
    standardGaussianExpectation (fun z =>
      deriv (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) lam) - v := by
  rw [deriv_gtFunctional_eq]
  apply congrArg (fun x : ℝ => x - v)
  apply congrArg standardGaussianExpectation
  funext z

  have hqv : q ≤ |v| := by
    simpa [hv] using hq1
  have hrpos : 0 < |v| := by
    rw [hv]
    norm_num
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq

  have hfun :
      (fun l =>
        gtSemigroupSolution β q s l v 0
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z))
        =
      (fun l =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q) (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1) (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal l)))
          (h + β * Real.sqrt ((1 - s) * q) * z)
          (h + β * Real.sqrt ((1 - s) * q) * z)) := by
    funext l
    simp [gtSemigroupSolution, hv, hq1, hqv, hr0, hq0]

  rw [hfun]


/-! ### Explicit formulas for ∂_λ U_s^{λ,v}|_{λ=0} -/

/-! Case `|v| = 0`. -/

lemma deriv_gtSemigroupSolution_zero_abs_v_eq_zero
    (β q s v x₁ x₂ : ℝ)
    (hq : 0 < q) (hv : |v| = 0) :
    deriv (fun lam =>
      gtSemigroupSolution β q s lam v 0 x₁ x₂) 0
      =
    deriv (fun lam =>
      gtDiagonalStep 0
        (gtIncrementScale β s 0 q)
        (gtDiagonalStep 1
          (gtIncrementScale β s q 1)
          (gtTerminal lam))
        x₁ x₂) 0 := by
  have hv0 : v = 0 := abs_eq_zero.mp hv
  subst v
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hfun :
      (fun lam =>
        gtSemigroupSolution β q s lam 0 0 x₁ x₂)
        =
      (fun lam =>
        gtDiagonalStep 0
          (gtIncrementScale β s 0 q)
          (gtDiagonalStep 1
            (gtIncrementScale β s q 1)
            (gtTerminal lam))
          x₁ x₂) := by
    funext lam
    simp [gtSemigroupSolution, hq0]
  rw [hfun]


/-! Case `0 < |v| < q`. -/

lemma deriv_gtSemigroupSolution_zero_abs_v_lt_q
    (β q s v x₁ x₂ : ℝ)
    (hv0 : 0 < |v|) (hvq : |v| < q) :
    deriv (fun lam =>
      gtSemigroupSolution β q s lam v 0 x₁ x₂) 0
      =
    deriv (fun lam =>
      gtRankOneStep 0
        (gtIncrementScale β s 0 |v|)
        (gtPathSign v)
        (gtDiagonalStep 0
          (gtIncrementScale β s |v| q)
          (gtDiagonalStep 1
            (gtIncrementScale β s q 1)
            (gtTerminal lam)))
        x₁ x₂) 0 := by
  have hqr : ¬ q ≤ |v| := not_le.mpr hvq
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hv0
  have hqpos : 0 < q := lt_trans hv0 hvq
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hqpos

  have hfun :
      (fun lam =>
        gtSemigroupSolution β q s lam v 0 x₁ x₂)
        =
      (fun lam =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 |v|)
          (gtPathSign v)
          (gtDiagonalStep 0
            (gtIncrementScale β s |v| q)
            (gtDiagonalStep 1
              (gtIncrementScale β s q 1)
              (gtTerminal lam)))
          x₁ x₂) := by
    funext lam
    simp [gtSemigroupSolution, hqr, hr0, hq0]

  rw [hfun]


/-! Case `q ≤ |v| < 1`. -/

lemma deriv_gtSemigroupSolution_zero_q_le_abs_v_lt_one
    (β q s v x₁ x₂ : ℝ)
    (hq : 0 < q) (hqv : q ≤ |v|) (hv1 : |v| < 1) :
    deriv (fun lam =>
      gtSemigroupSolution β q s lam v 0 x₁ x₂) 0
      =
    deriv (fun lam =>
      gtRankOneStep 0
        (gtIncrementScale β s 0 q)
        (gtPathSign v)
        (gtRankOneStep (1 / 2)
          (gtIncrementScale β s q |v|)
          (gtPathSign v)
          (gtDiagonalStep 1
            (gtIncrementScale β s |v| 1)
            (gtTerminal lam)))
        x₁ x₂) 0 := by
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have hrpos : 0 < |v| := lt_of_lt_of_le hq hqv
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos

  have hfun :
      (fun lam =>
        gtSemigroupSolution β q s lam v 0 x₁ x₂)
        =
      (fun lam =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q)
          (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q |v|)
            (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s |v| 1)
              (gtTerminal lam)))
          x₁ x₂) := by
    funext lam
    simp [gtSemigroupSolution, hqv, hr0, hq0]

  rw [hfun]


/-! Case `|v| = 1`. -/

lemma deriv_gtSemigroupSolution_zero_abs_v_eq_one
    (β q s v x₁ x₂ : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hv : |v| = 1) :
    deriv (fun lam =>
      gtSemigroupSolution β q s lam v 0 x₁ x₂) 0
      =
    deriv (fun lam =>
      gtRankOneStep 0
        (gtIncrementScale β s 0 q)
        (gtPathSign v)
        (gtRankOneStep (1 / 2)
          (gtIncrementScale β s q 1)
          (gtPathSign v)
          (gtDiagonalStep 1
            (gtIncrementScale β s 1 1)
            (gtTerminal lam)))
        x₁ x₂) 0 := by
  have hqv : q ≤ |v| := by
    simpa [hv] using hq1
  have hrpos : 0 < |v| := by
    rw [hv]
    norm_num
  have hr0 : ¬ |v| ≤ (0 : ℝ) := not_le.mpr hrpos
  have hq0 : ¬ q ≤ (0 : ℝ) := not_le.mpr hq
  have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num

  have hfun :
      (fun lam =>
        gtSemigroupSolution β q s lam v 0 x₁ x₂)
        =
      (fun lam =>
        gtRankOneStep 0
          (gtIncrementScale β s 0 q)
          (gtPathSign v)
          (gtRankOneStep (1 / 2)
            (gtIncrementScale β s q 1)
            (gtPathSign v)
            (gtDiagonalStep 1
              (gtIncrementScale β s 1 1)
              (gtTerminal lam)))
          x₁ x₂) := by
    funext lam
    simp [gtSemigroupSolution, hv, hq1, hqv, hr0, hq0, h10]

  rw [hfun]


/-- At `lam = 0`, the two-replica terminal function splits into
the sum of the two one-replica terminal functions. -/
lemma gtTerminal_zero (x₁ x₂ : ℝ) :
    gtTerminal 0 x₁ x₂ =
      Real.log (Real.cosh x₁) + Real.log (Real.cosh x₂) := by
  rw [gtTerminal]
  simp only [add_zero, sub_zero]

  have h :
      (Real.exp (x₁ + x₂) +
          Real.exp (x₁ - x₂) +
          Real.exp (-x₁ + x₂) +
          Real.exp (-x₁ - x₂)) / 4
        =
      Real.cosh x₁ * Real.cosh x₂ := by
    rw [Real.cosh_eq, Real.cosh_eq]
    simp [Real.exp_add, sub_eq_add_neg]
    ring

  rw [h]
  rw [Real.log_mul
    (ne_of_gt (Real.cosh_pos x₁))
    (ne_of_gt (Real.cosh_pos x₂))]


/-- Explicit first derivative of the terminal function in `lam`. -/
lemma deriv_gtTerminal_explicit (lam x₁ x₂ : ℝ) :
    deriv (fun l => gtTerminal l x₁ x₂) lam
      =
    (Real.exp (x₁ + x₂ + lam)
        - Real.exp (x₁ - x₂ - lam)
        - Real.exp (-x₁ + x₂ - lam)
        + Real.exp (-x₁ - x₂ + lam))
      /
    (Real.exp (x₁ + x₂ + lam)
        + Real.exp (x₁ - x₂ - lam)
        + Real.exp (-x₁ + x₂ - lam)
        + Real.exp (-x₁ - x₂ + lam)) := by
  simpa [gtTerminalNumerator, gtTerminalSum] using
    (hasDerivAt_gtTerminal lam x₁ x₂).deriv


/-- At `lam = 0`, the `lam`-derivative factorizes as
`tanh x₁ * tanh x₂`. -/
lemma deriv_gtTerminal_zero (x₁ x₂ : ℝ) :
    deriv (fun lam => gtTerminal lam x₁ x₂) 0
      =
    Real.tanh x₁ * Real.tanh x₂ := by
  rw [deriv_gtTerminal_explicit]
  simp only [add_zero, sub_zero]

  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]

  have h₁ : Real.cosh x₁ ≠ 0 :=
    ne_of_gt (Real.cosh_pos x₁)
  have h₂ : Real.cosh x₂ ≠ 0 :=
    ne_of_gt (Real.cosh_pos x₂)

  have hnum :
      Real.exp (x₁ + x₂) - Real.exp (x₁ - x₂)
          - Real.exp (-x₁ + x₂) + Real.exp (-x₁ - x₂)
        = 4 * Real.sinh x₁ * Real.sinh x₂ := by
    rw [Real.sinh_eq, Real.sinh_eq]
    simp [Real.exp_add, sub_eq_add_neg]
    ring

  have hden :
      Real.exp (x₁ + x₂) + Real.exp (x₁ - x₂)
          + Real.exp (-x₁ + x₂) + Real.exp (-x₁ - x₂)
        = 4 * Real.cosh x₁ * Real.cosh x₂ := by
    rw [Real.cosh_eq, Real.cosh_eq]
    simp [Real.exp_add, sub_eq_add_neg]
    ring

  rw [hnum, hden]

  field_simp [h₁, h₂]









end SpinGlass.AT
