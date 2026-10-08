module

/- Compatibility adaptation: current probability-map instance, measurable-pi constructor and Gaussian-law elaboration annotations. -/
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# Finite-dimensional Gaussian concentration

This file contains the complete development: foundational Gaussian-measure lemmas,
the smooth covariance estimate, mollification, the Herbst argument, and the final
one-sided and two-sided concentration inequalities.
-/

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory
open ProbabilityTheory
open intervalIntegral

namespace SYK

/-!
## Gaussian measure and analytic auxiliary lemmas
-/

/-- The Euclidean space of real SYK couplings. -/
abbrev CouplingSpace (N q : ℕ) :=
  EuclideanSpace ℝ ({s : Finset (Fin N) // s.card = q})

@[simp]
theorem couplingSpace_card (N q : ℕ) :
    Fintype.card ({s : Finset (Fin N) // s.card = q}) = Nat.choose N q := by
  simp

/-- The product standard Gaussian measure transported to coupling space. -/
noncomputable def standardGaussianMeasure (N q : ℕ) :
    Measure (CouplingSpace N q) :=
  (Measure.pi fun _ : ({s : Finset (Fin N) // s.card = q}) => gaussianReal 0 1).map
    (WithLp.toLp 2)

/-- One standard Gaussian measure for every finite Euclidean coordinate type.
This is the product of standard one-dimensional Gaussians pushed forward to the
Euclidean (`L²`) structure on the coordinate space. -/
noncomputable def standardGaussianMeasureOnEuclidean
    (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)

/-- The SYK coupling-space measure is the standard Euclidean Gaussian on the
interaction-index type. -/
@[simp]
theorem standardGaussianMeasure_eq_onEuclidean (N q : ℕ) :
    standardGaussianMeasure N q =
      standardGaussianMeasureOnEuclidean ({s : Finset (Fin N) // s.card = q}) := rfl

/-- The standard Euclidean Gaussian is a probability measure. -/
instance standardGaussianMeasureOnEuclidean_isProbability
    {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean
  infer_instance

/-- The finite product of standard real Gaussians is a Gaussian measure. -/
instance isGaussian_pi_gaussianReal {ι : Type*} [Fintype ι] :
    IsGaussian (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  have hindep : iIndepFun (fun (i : ι) (ω : ι → ℝ) => ω i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    have := iIndepFun_pi (X := fun (_ : ι) (x : ℝ) => x)
      (μ := fun _ : ι => gaussianReal 0 1) (fun _ => measurable_id.aemeasurable)
    simpa using this
  have hlaw : ∀ i : ι, HasGaussianLaw (fun ω : ι → ℝ => ω i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    intro i
    have h0 : (Measure.pi fun _ : ι => gaussianReal 0 1).map (Function.eval i)
        = gaussianReal 0 1 := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq
    have : IsGaussian ((Measure.pi fun _ : ι => gaussianReal 0 1).map (fun ω => ω i)) := by
      rw [show (fun ω : ι → ℝ => ω i) = Function.eval i from rfl, h0]; infer_instance
    exact IsGaussian.hasGaussianLaw (P := Measure.pi fun _ : ι => gaussianReal 0 1) (X := fun ω : ι → ℝ => ω i) (measurable_pi_apply i).aemeasurable
  have h2 : IsGaussian ((Measure.pi fun _ : ι => gaussianReal 0 1).map (fun ω i => ω i)) :=
    (hindep.hasGaussianLaw hlaw).isGaussian_map
  simpa using h2

/-- The standard Euclidean Gaussian measure is a Gaussian measure. -/
instance standardGaussianMeasureOnEuclidean_isGaussian {ι : Type*} [Fintype ι] :
    IsGaussian (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean
  rw [show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm from rfl]
  infer_instance

/-
Analytic proof outline for the Gaussian concentration estimate.

The standard Gaussian log-Sobolev inequality says that, for locally Lipschitz
$g : \mathbb R^n \to \mathbb R$ with $e^g \in L^1(\gamma_n)$,
$\operatorname{Ent}_{\gamma_n}(e^g) \le
  \frac12 \int |\nabla g|^2 e^g \, d\gamma_n$, where
$\operatorname{Ent}_{\gamma_n}(H) =
  \int H \log H \, d\gamma_n -
  (\int H \, d\gamma_n)\log(\int H \, d\gamma_n)$.
Here $\nabla g$ is the a.e. gradient.

If $F$ is $L$-Lipschitz, Rademacher's theorem gives
$|\nabla F(x)| \le L$ for a.e. $x$. Also
$|F(x)| \le |F(0)| + L|x|$, so $e^{\lambda F} \in L^1(\gamma_n)$
for every $\lambda \in \mathbb R$. Set
$\Phi(\lambda) = \log \mathbb E e^{\lambda F(X)}$.

For $\lambda > 0$, applying log-Sobolev to $g = \lambda F$ gives
$\operatorname{Ent}_{\gamma_n}(e^{\lambda F})
  \le \frac{\lambda^2 L^2}{2}\mathbb E e^{\lambda F(X)}$.
Since
$\Phi'(\lambda) =
  \mathbb E[F(X)e^{\lambda F(X)}] / \mathbb E e^{\lambda F(X)}$,
the entropy identity is
$\operatorname{Ent}_{\gamma_n}(e^{\lambda F}) =
  \mathbb E e^{\lambda F(X)}(\lambda\Phi'(\lambda)-\Phi(\lambda))$.
Thus
$\lambda\Phi'(\lambda)-\Phi(\lambda) \le \lambda^2L^2/2$, hence
$(\Phi(\lambda)/\lambda)' \le L^2/2$.

Integrating from $0$ to $\lambda$ and using
$\lim_{s \downarrow 0}\Phi(s)/s = \mathbb E F(X)$ yields
$\Phi(\lambda) \le \lambda\mathbb E F(X) + \lambda^2L^2/2$, equivalently
$\mathbb E e^{\lambda(F(X)-\mathbb E F(X))} \le e^{\lambda^2L^2/2}$.
Chernoff's bound then gives
$\mathbb P(F(X)-\mathbb E F(X) > t)
  \le \exp(-\lambda t + \lambda^2L^2/2)$, optimized at
$\lambda = t/L^2$, so
$\mathbb P(F(X)-\mathbb E F(X) > t)
  \le \exp(-t^2/(2L^2))$.
Applying the same argument to $-F$ and using the union bound gives
$\mathbb P(|F(X)-\mathbb E F(X)| > t)
  \le 2\exp(-t^2/(2L^2))$.

Exponential-of-norm functions are integrable against the standard Euclidean Gaussian.
This follows from the fact that a standard Gaussian has finite exponential moments of its
Euclidean norm.
-/
theorem integrable_exp_mul_norm {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (c * ‖x‖))
      (standardGaussianMeasureOnEuclidean ι) := by
  unfold standardGaussianMeasureOnEuclidean;
  rw [ MeasureTheory.integrable_map_measure ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => ∏ i, Real.exp ( |c| * |x i| );
    · have h_integrable : ∀ i : ι, MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|)) (gaussianReal 0 1) := by
        intro i
        have h_integrable : MeasureTheory.Integrable (fun x : ℝ => Real.exp (|c| * |x|)) (gaussianReal 0 1) := by
          have h_mgf : ∀ s : ℝ, MeasureTheory.Integrable (fun x : ℝ => Real.exp (s * x)) (gaussianReal 0 1) := by
            intro s
            have h_integrable : ∫ x, Real.exp (s * x) ∂(gaussianReal 0 1) = Real.exp (s^2 / 2) := by
              have := @ProbabilityTheory.mgf_gaussianReal;
              convert @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) _ s using 1 <;>
                norm_num [mgf, mul_comm]
            exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity )
          refine' MeasureTheory.Integrable.mono' ( h_mgf |c| |> fun h => h.add ( h_mgf ( -|c| ) ) ) _ _;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by norm_num; cases abs_cases x <;> simp +decide [ * ] <;> positivity;
        exact h_integrable;
      have h_prod_integrable : ∀ {f : ι → ℝ → ℝ}, (∀ i, MeasureTheory.Integrable (fun x => f i x) (gaussianReal 0 1)) → MeasureTheory.Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) (Measure.pi fun _ => gaussianReal 0 1) := by
        exact fun {f} a => Integrable.fintype_prod a;
      exact h_prod_integrable h_integrable;
    · fun_prop (disch := norm_num);
    · simp +decide [ ← Real.exp_sum, EuclideanSpace.norm_eq ];
      refine' Filter.Eventually.of_forall fun x => _;
      -- Apply the triangle inequality to the sum.
      have h_triangle : Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
        exact Real.sqrt_le_iff.mpr ⟨ by exact Finset.sum_nonneg fun _ _ => abs_nonneg _, by simpa [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => abs_nonneg ( x i ) ) hi ) ( abs_nonneg ( x i ) ) ⟩;
      rw [ ← Finset.mul_sum _ _ _ ];
      cases abs_cases c <;> nlinarith [ Real.sqrt_nonneg ( ∑ i, x i ^ 2 ) ];
  · fun_prop;
  · fun_prop

/-
Real-analysis Grönwall-type core of the Herbst argument.  If `Φ` is differentiable,
vanishes at `0`, and its derivative stays within `c * |s|` of `m` for every `s`, then `Φ`
is dominated by the quadratic `m * t + c * t ^ 2 / 2`.  (The two-sided derivative bound
forces `Φ' - m` to have the sign of `s` at the endpoints, which is exactly what is needed
for both `t ≥ 0` and `t ≤ 0`.)
-/
lemma quadratic_bound_of_deriv_sub_le {Φ : ℝ → ℝ} {m c : ℝ}
    (hdiff : Differentiable ℝ Φ) (h0 : Φ 0 = 0)
    (hderiv : ∀ s, |deriv Φ s - m| ≤ c * |s|) (t : ℝ) :
    Φ t ≤ m * t + c * t ^ 2 / 2 := by
  let psi : ℝ → ℝ := fun s ↦ Φ s - (m * s + c * s ^ 2 / 2)
  have hpsi_deriv (s : ℝ) : deriv psi s = deriv Φ s - (m + c * s) := by
    have hquad := ((hasDerivAt_id s).const_mul m).add
      (((hasDerivAt_id s).pow 2).const_mul c |>.div_const 2)
    have hsub := (hdiff.differentiableAt.hasDerivAt.sub hquad).deriv
    change deriv (Φ - fun x : ℝ ↦ m * x + c * x ^ 2 / 2) s = _
    have hfun :
        (Φ - fun x : ℝ ↦ m * x + c * x ^ 2 / 2) =
          Φ - ((fun y : ℝ ↦ m * id y) + fun x ↦ c * (id ^ 2) x / 2) := by
      funext x
      change Φ x - (m * x + c * x ^ 2 / 2) =
        Φ x - (m * x + c * x ^ 2 / 2)
      rfl
    rw [hfun, hsub]
    simp only [id_eq, Nat.cast_ofNat, mul_one]
    ring
  by_cases ht : 0 ≤ t
  · have h_antitone : AntitoneOn psi (Set.Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      · exact hdiff.continuous.continuousOn.sub (by fun_prop)
      · exact hdiff.differentiableOn.sub (by fun_prop)
      · intro x hx
        rw [hpsi_deriv]
        have hb := (abs_le.mp (hderiv x)).2
        have hxIcc : x ∈ Set.Icc 0 t := interior_subset hx
        rw [abs_of_nonneg hxIcc.1] at hb
        linarith
    have hmono := h_antitone (show 0 ∈ Set.Icc 0 t by exact ⟨le_rfl, ht⟩)
      (show t ∈ Set.Icc 0 t by exact ⟨ht, le_rfl⟩) ht
    simp [psi, h0] at hmono
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht
    have h_mvt := exists_deriv_eq_slope psi htneg
      (hdiff.continuous.continuousOn.sub (by fun_prop))
      (hdiff.differentiableOn.sub (by fun_prop))
    obtain ⟨ξ, hξ, hξeq⟩ := h_mvt
    have hb := (abs_le.mp (hderiv ξ)).1
    rw [abs_of_neg hξ.2] at hb
    have hnonneg : 0 ≤ deriv psi ξ := by
      rw [hpsi_deriv]
      linarith
    rw [hξeq, le_div_iff₀ (by linarith : 0 < 0 - t)] at hnonneg
    simp [psi, h0] at hnonneg
    linarith

/-
For a Lipschitz function `F`, the function `exp (s • F)` is integrable against the
standard Gaussian measure, for every real `s`.  This uses the linear growth
`|F x| ≤ |F 0| + L * ‖x‖` together with `integrable_exp_mul_norm`.
-/
lemma integrable_exp_smul_lipschitz {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    Integrable (fun x => Real.exp (s * F x)) (standardGaussianMeasureOnEuclidean ι) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖x‖ );
  · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( |s| * L ) ) _;
  · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul ( hLip.continuous ) ) );
  · -- Apply the Lipschitz condition to bound |F x|.
    have h_bound : ∀ x, |F x - F 0| ≤ L * ‖x‖ := by
      intro x
      have hx := hLip.dist_le_mul x 0
      rw [show (L.toNNReal : ℝ) = L by exact Real.coe_toNNReal L hL.le] at hx
      simpa only [Real.dist_eq, dist_zero_right] using hx
    simp +decide [ ← Real.exp_add ];
    filter_upwards [ ] with x using by cases abs_cases s <;> cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_bound x ) ] ;

/-- The set of exponents `s` for which `exp (s • F)` is integrable is all of `ℝ`. -/
lemma integrableExpSet_lipschitz_eq_univ {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) :
    integrableExpSet F (standardGaussianMeasureOnEuclidean ι) = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact integrable_exp_smul_lipschitz F L hL hLip s

/-
**Herbst's argument, assembly step.**  Given the sharp Gaussian covariance bound
`|∫ F e^{sF} - (∫ F)(∫ e^{sF})| ≤ L² |s| ∫ e^{sF}` for every `s`, the centered function
`F - ∫ F` has a sub-Gaussian moment-generating function with parameter `L²`.

The cumulant generating function `Φ = cgf F μ` is analytic (hence differentiable) on all of
`ℝ` since every exponential moment is finite; it satisfies `Φ 0 = 0` and
`Φ'(s) = (∫ F e^{sF}) / ∫ e^{sF}`.  The covariance bound gives `|Φ'(s) - ∫ F| ≤ L² |s|`, and
`quadratic_bound_of_deriv_sub_le` yields `Φ t ≤ (∫ F) t + L² t² / 2`, which is exactly the
claimed bound after unfolding `mgf (F - ∫ F) μ t = exp (Φ t - t ∫ F)`.
-/
lemma herbst_of_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F)
    (hcov : ∀ s : ℝ,
      |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
          - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
            * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
        ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι))
    (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
        (standardGaussianMeasureOnEuclidean ι) t ≤
      Real.exp (L ^ 2 * t ^ 2 / 2) := by
  -- Let $\Phi(s) = \log \mathbb{E}[e^{sF}]$.
  set Φ : ℝ → ℝ := fun s => Real.log (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι);
  -- We need to show that $\Phi(t) \leq mt + L^2 t^2 / 2$.
  have hΦ : Φ t ≤ (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι) * t + L^2 * t^2 / 2 := by
    apply quadratic_bound_of_deriv_sub_le;
    · have h_analytic : ∀ s : ℝ, AnalyticAt ℝ Φ s := by
        intro s;
        apply_rules [ ProbabilityTheory.analyticAt_cgf ];
        rw [ integrableExpSet_lipschitz_eq_univ F L hL hLip ] ; norm_num;
      exact fun s => ( h_analytic s |> AnalyticAt.differentiableAt );
    · simp +zetaDelta at *;
    · intro s
      have h_deriv : deriv Φ s = (∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) / (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
        apply_rules [ ProbabilityTheory.deriv_cgf ];
        rw [ integrableExpSet_lipschitz_eq_univ F L hL hLip ] ; norm_num;
      rw [ h_deriv, div_sub' ];
      · rw [ abs_div, abs_of_nonneg ( show 0 ≤ ∫ x, Real.exp ( s * F x ) ∂standardGaussianMeasureOnEuclidean ι from MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) ];
        exact div_le_of_le_mul₀ ( MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) ( by positivity ) ( by simpa only [ mul_comm ] using hcov s );
      · refine' ne_of_gt ( _ );
        rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
        · simp +decide [ Function.support, Real.exp_ne_zero ];
        · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _;
        · exact integrable_exp_smul_lipschitz F L hL hLip s;
  convert Real.exp_le_exp.mpr ( show Φ t - ( ∫ x, F x ∂standardGaussianMeasureOnEuclidean ι ) * t ≤ L ^ 2 * t ^ 2 / 2 from by linarith ) using 1;
  rw [ Real.exp_sub, Real.exp_log ];
  · simp +decide [ mgf, mul_sub, Real.exp_sub ];
    rw [ MeasureTheory.integral_div, mul_comm ];
  · apply_rules [ ProbabilityTheory.mgf_pos ];
    exact integrable_exp_smul_lipschitz F L hL hLip t

/-
**One-dimensional Gaussian integration by parts (Stein's identity).**  For a `C¹`
function `g` on `ℝ` whose value and derivative grow no faster than `C e^{c|x|}`, integration
against the standard Gaussian satisfies `∫ x * g x dγ = ∫ g' x dγ`.  This follows from the
boundary-free integration-by-parts on `ℝ` together with the identity `φ' = -x φ` for the
Gaussian density `φ`.
-/
set_option maxHeartbeats 4000000 in
lemma gaussianReal_stein (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'cont : Continuous g')
    (C c : ℝ) (hgbound : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hg'bound : ∀ x, |g' x| ≤ C * Real.exp (c * |x|)) :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  -- Let's simplify the integral using the fact that multiplication by a constant out of the integral sign can be taken outside.
  suffices h_simp : ∫ x, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) = ∫ x, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) by
    convert h_simp using 1 <;> norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, gaussianReal ];
    · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part, MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul, MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ gaussianPDF ];
        · congr! 2;
          · congr! 1;
            ext; rw [ ← ENNReal.ofReal_mul ( by exact ( by rw [ gaussianPDFReal ] ; positivity ) ) ] ; rw [ gaussianPDFReal ] ; ring_nf; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ] ;
            ring_nf;
          · refine' MeasureTheory.lintegral_congr fun x => _;
            rw [ ← ENNReal.ofReal_mul ( by exact mul_nonneg ( by positivity ) ( by positivity ) ) ] ; norm_num [ gaussianPDFReal ] ; ring_nf;
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( Measurable.neg ( measurable_id.mul ( show Measurable g from by exact Continuous.measurable ( by exact continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) );
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( measurable_id.mul ( show Measurable g from by exact Continuous.measurable ( by exact continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) );
      · have h_integrable : MeasureTheory.Integrable (fun x => x * g x * (Real.exp (-x^2 / 2))) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => x * (C * Real.exp (c * |x|)) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
                have := @integrable_rpow_mul_exp_neg_mul_sq;
                convert @this ( 1 / 4 ) ( by norm_num ) 1 ( by norm_num ) using 3 ; norm_num ; ring_nf;
              have h_integrable : ∀ x : ℝ, |x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)| ≤ |x * Real.exp (-x^2 / 4)| * Real.exp (c^2) := by
                intro x; rw [ abs_mul, abs_mul, abs_mul ] ; norm_num [ ← Real.exp_add ] ; ring_nf; norm_num;
                norm_num [ mul_assoc, ← Real.exp_add ];
                exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases x <;> nlinarith [ sq_nonneg ( |x| - 2 * c ) ] ) ( abs_nonneg x );
              refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun x => |x * Real.exp ( -x ^ 2 / 4 )| * Real.exp ( c ^ 2 );
              · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.abs ‹_› ) _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · exact Filter.Eventually.of_forall h_integrable;
            convert h_integrable.const_mul C using 2 ; ring;
          refine' h_integrable.norm.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) ( Continuous.aestronglyMeasurable ( show Continuous fun x => Real.exp ( -x ^ 2 / 2 ) from Real.continuous_exp.comp <| by continuity ) );
          · simp_all +decide [ mul_assoc ];
            filter_upwards [ ] with x using mul_le_mul_of_nonneg_left ( by rw [ ← mul_assoc ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( hgbound x ) ( mul_le_mul_of_nonneg_right ( le_abs_self _ ) ( Real.exp_nonneg _ ) ) ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ );
        convert h_integrable.div_const ( Real.sqrt 2 * Real.sqrt Real.pi ) using 2 ; ring;
      · have h_integrable : MeasureTheory.Integrable (fun x => x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => x * g x * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => x * (C * Real.exp (c * |x|)) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
                have h_integrable : MeasureTheory.Integrable (fun x => x * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
                  have := @integrable_rpow_mul_exp_neg_mul_sq;
                  convert @this ( 1 / 4 ) ( by norm_num ) 1 ( by norm_num ) using 3 ; norm_num ; ring_nf;
                have h_integrable : ∀ x : ℝ, |x * Real.exp (c * |x|) * Real.exp (-x^2 / 2)| ≤ |x * Real.exp (-x^2 / 4)| * Real.exp (c^2) := by
                  intro x; rw [ abs_mul, abs_mul, abs_mul ] ; norm_num [ ← Real.exp_add ] ; ring_nf; norm_num;
                  norm_num [ mul_assoc, ← Real.exp_add ];
                  exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases x <;> nlinarith [ sq_nonneg ( |x| - 2 * c ) ] ) ( abs_nonneg x );
                refine' MeasureTheory.Integrable.mono' _ _ _;
                refine' fun x => |x * Real.exp ( -x ^ 2 / 4 )| * Real.exp ( c ^ 2 );
                · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.abs ‹_› ) _;
                · exact Continuous.aestronglyMeasurable ( by continuity );
                · exact Filter.Eventually.of_forall h_integrable;
              convert h_integrable.const_mul C using 2 ; ring;
            refine' h_integrable.norm.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ) ( Continuous.aestronglyMeasurable ( show Continuous fun x => Real.exp ( -x ^ 2 / 2 ) from Real.continuous_exp.comp <| by continuity ) );
            · simp_all +decide [ mul_assoc ];
              filter_upwards [ ] with x using mul_le_mul_of_nonneg_left ( by rw [ ← mul_assoc ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( hgbound x ) ( mul_le_mul_of_nonneg_right ( le_abs_self _ ) ( Real.exp_nonneg _ ) ) ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ );
          convert h_integrable.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 2 ; ring;
        rw [ MeasureTheory.integrable_withDensity_iff ];
        · convert h_integrable using 1 <;>
            first
            | rfl
            | (funext x
               rw [toReal_gaussianPDF]
               norm_num [gaussianPDFReal]
               ring_nf
               exact Or.inl trivial)
        · fun_prop;
        · simp [gaussianPDF];
    · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part, MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
      · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul, MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ gaussianPDF ];
        · congr! 2;
          · congr! 1;
            ext; rw [ gaussianPDFReal ] ; ring_nf;
            rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; norm_num ; ring_nf;
          · congr! 1;
            ext; rw [ ← ENNReal.ofReal_mul ( by exact mul_nonneg ( by positivity ) ( Real.exp_nonneg _ ) ) ] ; norm_num [ gaussianPDFReal ] ; ring_nf;
        · fun_prop;
        · exact Measurable.ennreal_ofReal ( hg'cont.measurable.neg );
        · fun_prop;
        · exact Measurable.ennreal_ofReal hg'cont.measurable;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => C * Real.exp ( c * |x| ) * ( Real.exp ( -x ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) );
        · have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x|) * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
                simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
              refine' h_integrable.const_mul ( Real.exp ( 2 * c ^ 2 ) ) |> fun h => h.mono' _ _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
            convert h_integrable using 2 ; rw [ ← Real.exp_add ] ; ring_nf;
          convert h_integrable.const_mul ( C / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) using 2 ; ring;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
        · filter_upwards [ ] with x using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ Real.exp ( -x ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ] ; exact mul_le_mul_of_nonneg_right ( hg'bound x ) ( by positivity ) ;
      · have h_integrable : MeasureTheory.Integrable (fun x => g' x * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => C * Real.exp (c * |x|) * Real.exp (-x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
              have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
                simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
              refine' h_integrable.const_mul ( Real.exp ( 2 * c ^ 2 ) ) |> fun h => h.mono' _ _;
              · exact Continuous.aestronglyMeasurable ( by continuity );
              · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
            convert h_integrable.const_mul C using 2 ; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf;
          refine' h_integrable.mono' _ _;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
          · filter_upwards [ ] using fun x => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( hg'bound x ) ( Real.exp_nonneg _ ) ;
        rw [ MeasureTheory.integrable_withDensity_iff ];
        · convert h_integrable.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 1 <;>
            first
            | rfl
            | (funext x
               rw [toReal_gaussianPDF]
               norm_num [gaussianPDFReal]
               ring)
        · fun_prop;
        · simp [gaussianPDF];
  -- By integration by parts, we have $\int_{-\infty}^{\infty} x g(x) \phi(x) \, dx = \left[ -g(x) \phi(x) \right]_{-\infty}^{\infty} + \int_{-\infty}^{\infty} g'(x) \phi(x) \, dx$.
  have h_parts : ∀ a b : ℝ, ∫ x in a..b, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) = -g b * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi)) + g a * (Real.exp (-a^2 / 2) / Real.sqrt (2 * Real.pi)) + ∫ x in a..b, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) := by
    intro a b;
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => -g x * ( Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) ) + ∫ x in a..x, g' x * ( Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) );
    · simpa using by ring;
    · intro x hx
      have hden : HasDerivAt
          (fun y : ℝ ↦ Real.exp (-y ^ 2 / 2) / Real.sqrt (2 * Real.pi))
          (-x * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) x := by
        convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp.div_const
          (Real.sqrt (2 * Real.pi))) using 1 <;>
          first | rfl | (simp only [Pi.neg_apply]; ring_nf)
      have hint : HasDerivAt
          (fun y : ℝ ↦ ∫ u in a..y,
            g' u * (Real.exp (-u ^ 2 / 2) / Real.sqrt (2 * Real.pi)))
          (g' x * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi))) x := by
        exact intervalIntegral.integral_hasDerivAt_right
          (Continuous.intervalIntegrable (hg'cont.mul (by fun_prop)) _ _)
          ((hg'cont.mul (by fun_prop)).stronglyMeasurable.stronglyMeasurableAtFilter)
          (hg'cont.continuousAt.mul (by fun_prop))
      have htotal := ((hg x).neg.mul hden).add hint
      convert htotal using 1 <;>
        first | rfl | (simp only [Pi.neg_apply]; ring_nf)
    · exact Continuous.intervalIntegrable ( by exact Continuous.mul ( Continuous.mul continuous_id ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ( by continuity ) ) _ _;
  -- Let's choose any two points $a$ and $b$ such that $a < b$.
  have h_lim : Filter.Tendsto (fun b => ∫ x in (-b)..b, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds (∫ x, x * g x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)))) := by
    apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
    · -- We'll use the fact that $|x g(x)| \leq C |x| e^{c|x|}$ and $|x| e^{c|x|}$ is integrable.
      have h_integrable : MeasureTheory.Integrable (fun x => |x| * Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
        have h_integrable : MeasureTheory.Integrable (fun x => |x| * Real.exp (-x^2 / 4)) MeasureTheory.volume := by
          have := @integrable_rpow_mul_exp_neg_mul_sq;
          specialize @this ( 1 / 4 ) ( by norm_num ) ( 1 : ℝ ) ; norm_num at this;
          convert this.norm using 2 ; norm_num [ div_eq_inv_mul ];
        have h_integrable : ∀ x : ℝ, |x| * Real.exp (c * |x|) * Real.exp (-x^2 / 2) ≤ |x| * Real.exp (-x^2 / 4) * Real.exp (2 * c^2) := by
          intro x; rw [ mul_assoc, mul_assoc ] ; rw [ ← Real.exp_add, ← Real.exp_add ] ; ring_nf; norm_num;
          exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ( abs_nonneg x );
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => |x| * Real.exp ( -x ^ 2 / 4 ) * Real.exp ( 2 * c ^ 2 );
        · exact MeasureTheory.Integrable.mul_const ‹_› _;
        · exact Continuous.aestronglyMeasurable ( by continuity );
        · filter_upwards [ ] using fun x => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_integrable x;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => |x| * C * Real.exp ( c * |x| ) * Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi );
      · convert h_integrable.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 1 <;>
          first | rfl | (funext x; ring_nf)
      · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( Continuous.mul continuous_id ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hg x ) ) ) ( by continuity ) );
      · simp_all +decide [ mul_assoc, mul_div_assoc ];
        filter_upwards [ ] with x using by rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; exact mul_le_mul_of_nonneg_left ( by simpa only [ mul_assoc, mul_div_assoc ] using mul_le_mul_of_nonneg_right ( hgbound x ) ( by positivity ) ) ( by positivity ) ;
    · exact Filter.tendsto_neg_atTop_atBot;
    · exact Filter.tendsto_id;
  -- By the properties of the Gaussian measure, we know that $\lim_{b \to \infty} g(b) \phi(b) = 0$ and $\lim_{b \to \infty} g(-b) \phi(-b) = 0$.
  have h_lim_zero : Filter.Tendsto (fun b => g b * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun b => g (-b) * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) := by
    have h_lim_zero : Filter.Tendsto (fun b => C * Real.exp (c * |b|) * (Real.exp (-b^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds 0) := by
      -- We can factor out the constant $C / \sqrt{2\pi}$ and use the fact that $\exp(-b^2 / 2 + c|b|)$ tends to $0$ as $b$ tends to infinity.
      have h_exp : Filter.Tendsto (fun b => Real.exp (-b^2 / 2 + c * |b|)) Filter.atTop (nhds 0) := by
        norm_num [ Filter.tendsto_atTop_atBot ];
        exact fun b => ⟨ |b| * 2 + |c| * 2 + 1, fun x hx => by cases abs_cases b <;> cases abs_cases c <;> cases abs_cases x <;> nlinarith ⟩;
      convert h_exp.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 2 <;> ring_nf;
      rw [ Real.exp_add ] ; ring;
    refine' ⟨ squeeze_zero_norm _ h_lim_zero, squeeze_zero_norm _ h_lim_zero ⟩;
    · exact fun x => by simpa [ abs_mul, abs_div, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] using mul_le_mul_of_nonneg_right ( hgbound x ) ( by positivity ) ;
    · simp +zetaDelta at *;
      exact fun x => by rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ), abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; exact mul_le_mul_of_nonneg_right ( by simpa using hgbound ( -x ) ) ( by positivity ) ;
  have h_lim_zero : Filter.Tendsto (fun b => ∫ x in (-b)..b, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) Filter.atTop (nhds (∫ x, g' x * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)))) := by
    apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
    · -- The function $g'$ is bounded by $C e^{c|x|}$, and the Gaussian density is integrable.
      have h_integrable : MeasureTheory.Integrable (fun x => C * Real.exp (c * |x|) * (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi))) MeasureTheory.volume := by
        have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x|) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
          have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (c * |x| - x ^ 2 / 2)) MeasureTheory.volume := by
            have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-x ^ 2 / 4)) MeasureTheory.volume := by
              simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
            refine' h_integrable.const_mul ( Real.exp ( c ^ 2 ) ) |> fun h => h.mono' _ _;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by nlinarith [ sq_nonneg ( |x| - 2 * c ), abs_mul_abs_self x ] ) ;
          convert h_integrable using 1 ; ext x ; rw [ ← Real.exp_add ] ; ring_nf;
        convert h_integrable.const_mul ( C / Real.sqrt ( 2 * Real.pi ) ) using 2 ; ring;
      refine' h_integrable.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( hg'cont.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
      · filter_upwards [ ] with x using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( by positivity : 0 ≤ Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) ) ] ; exact mul_le_mul_of_nonneg_right ( hg'bound x ) ( by positivity ) ;
    · exact Filter.tendsto_neg_atTop_atBot;
    · exact Filter.tendsto_id;
  simp_all +decide;
  exact tendsto_nhds_unique h_lim ( by simpa using Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.neg ( ‹Filter.Tendsto ( fun b => g b * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun b => g ( -b ) * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ›.1 ) ) ( ‹Filter.Tendsto ( fun b => g b * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun b => g ( -b ) * ( Real.exp ( -b ^ 2 / 2 ) / ( Real.sqrt 2 * Real.sqrt Real.pi ) ) ) Filter.atTop ( nhds 0 ) ›.2 ) ) h_lim_zero )

/-
The standard Euclidean Gaussian measure is centered: its mean is `0`.
-/
lemma standardGaussianMeasureOnEuclidean_integral_id {ι : Type*} [Fintype ι] :
    (standardGaussianMeasureOnEuclidean ι)[id] = (0 : EuclideanSpace ℝ ι) := by
  by_contra h_nonzero;
  -- The measure `standardGaussianMeasureOnEuclidean ι` is symmetric around `0`, meaning it is equal to its pushforward by the negation map.
  have h_symm : standardGaussianMeasureOnEuclidean ι = MeasureTheory.Measure.map (fun x => -x) (standardGaussianMeasureOnEuclidean ι) := by
    unfold standardGaussianMeasureOnEuclidean;
    rw [ MeasureTheory.Measure.map_map ];
    · have h_gauss_symm : ∀ (μ : MeasureTheory.Measure ℝ), μ = gaussianReal 0 1 → MeasureTheory.Measure.map (fun x => -x) μ = μ := by
        grind +suggestions;
      have h_gauss_symm : MeasureTheory.Measure.map (fun x : ι → ℝ => fun i => -x i) (Measure.pi fun _ : ι => gaussianReal 0 1) = Measure.pi fun _ : ι => gaussianReal 0 1 := by
        refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
        intro s hs; rw [ MeasureTheory.Measure.map_apply ];
        · simp +decide [ Set.preimage ];
          convert MeasureTheory.Measure.pi_pi _ _ using 1;
          · rw [ show { x : ι → ℝ | ∀ i, -x i ∈ s i } = ( Set.pi Set.univ fun i => ( fun x => -x ) ⁻¹' s i ) by ext; simp +decide ];
            rw [ MeasureTheory.Measure.pi_pi, MeasureTheory.Measure.pi_pi ];
            exact Finset.prod_congr rfl fun i _ => by rw [ ← MeasureTheory.Measure.map_apply ( measurable_neg ) ( hs i ), h_gauss_symm _ rfl ] ;
          · exact fun i => by infer_instance;
        · exact Measurable.of_eval fun _ => measurable_neg.comp ( measurable_pi_apply _ );
        · exact MeasurableSet.univ_pi hs;
      convert congr_arg ( MeasureTheory.Measure.map ( WithLp.toLp 2 ) ) h_gauss_symm.symm using 1;
      rw [ MeasureTheory.Measure.map_map ];
      · congr! 1;
      · exact WithLp.measurable_toLp 2 _;
      · exact Measurable.of_eval fun _ => measurable_neg.comp ( measurable_pi_apply _ );
    · exact measurable_id.neg;
    · fun_prop;
  apply_fun ( fun μ => ∫ x, x ∂μ ) at h_symm;
  rw [ MeasureTheory.integral_map ] at h_symm;
  · rw [ MeasureTheory.integral_neg ] at h_symm;
    exact h_nonzero ( by ext; have := congr_arg ( fun x => x ‹_› ) h_symm; norm_num at *; linarith );
  · exact measurable_id.neg.aemeasurable;
  · exact measurable_id.aestronglyMeasurable

/-
`exp (c |y|)` is integrable against the one-dimensional standard Gaussian.
-/
lemma integrable_exp_abs_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * |y|)) (gaussianReal 0 1) := by
  have h_integrable : MeasureTheory.Integrable (fun y => Real.exp (c * y)) (gaussianReal 0 1) ∧ MeasureTheory.Integrable (fun y => Real.exp (-c * y)) (gaussianReal 0 1) := by
    constructor;
    · have h_integrable : ∫ y, Real.exp (c * y) ∂(gaussianReal 0 1) = Real.exp (c^2 / 2) := by
        have := @ProbabilityTheory.mgf_gaussianReal;
        convert @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) _ c using 1 <;> norm_num [ mgf ];
      exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
    · have := @ProbabilityTheory.mgf_gaussianReal;
      specialize @this ℝ _ ( gaussianReal 0 1 ) 0 1 ( fun x => x ) ; norm_num at this;
      contrapose! this;
      use -c; simp_all +decide [ mgf ];
      rw [ MeasureTheory.integral_undef this ] ; positivity;
  refine' MeasureTheory.Integrable.mono' ( h_integrable.1.add h_integrable.2 ) _ _;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; cases abs_cases x <;> simp +decide [ * ] <;> positivity;

/-
`|y| exp (c |y|)` is integrable against the one-dimensional standard Gaussian.
-/
lemma integrable_abs_mul_exp_abs_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => |y| * Real.exp (c * |y|)) (gaussianReal 0 1) := by
  -- We'll use the fact that |y| * exp(c * |y|) ≤ exp((|c| + 1) * |y|).
  have h_bound : ∀ y : ℝ, |y| * Real.exp (c * |y|) ≤ Real.exp ((|c| + 1) * |y|) := by
    intro y;
    exact le_trans ( mul_le_mul_of_nonneg_right ( show |y| ≤ Real.exp |y| by linarith [ Real.add_one_le_exp |y| ] ) ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases c <;> cases abs_cases y <;> nlinarith ) );
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => Real.exp ( ( |c| + 1 ) * |y| );
  · convert integrable_exp_abs_gaussianReal ( |c| + 1 ) using 1;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · filter_upwards [ ] using fun x => by simpa using h_bound x;

/-- `exp (c ∑ⱼ |yⱼ|)` is integrable against the product standard Gaussian. -/
lemma integrable_exp_c_sum_abs_pi {ι : Type*} [Fintype ι] (c : ℝ) :
    Integrable (fun y : ι → ℝ => Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have : (fun y : ι → ℝ => Real.exp (c * ∑ j, |y j|))
      = (fun y : ι → ℝ => ∏ j, Real.exp (c * |y j|)) := by
    funext y; rw [← Real.exp_sum, Finset.mul_sum]
  rw [this]
  exact Integrable.fintype_prod (fun j => integrable_exp_abs_gaussianReal c)

/-
`|yᵢ| exp (c ∑ⱼ |yⱼ|)` is integrable against the product standard Gaussian.
-/
lemma integrable_abs_coord_mul_exp_c_sum_abs_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (i : ι) :
    Integrable (fun y : ι → ℝ => |y i| * Real.exp (c * ∑ j, |y j|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => Real.exp ( ( |c| + 1 ) * ∑ j, |y j| );
  · convert integrable_exp_c_sum_abs_pi ( |c| + 1 ) using 1;
  · fun_prop;
  · filter_upwards [ ] with y using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_trans ( mul_le_mul_of_nonneg_right ( show |y i| ≤ Real.exp |y i| by linarith [ Real.add_one_le_exp |y i| ] ) ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases c <;> cases abs_cases ( y i ) <;> nlinarith [ Real.exp_pos |y i|, Finset.single_le_sum ( fun a _ => abs_nonneg ( y a ) ) ( Finset.mem_univ i ) ] ) ) ;

/-
**Tensorized Stein identity on the product Gaussian measure.**  For a `C¹` function `h`
on `ι → ℝ` whose value and coordinate partial derivatives grow no faster than
`C e^{c ∑ⱼ |yⱼ|}`, integration against the product of standard Gaussians satisfies
`∫ yᵢ h y = ∫ ∂ᵢ h y`.  This is Fubini over the `i`-th coordinate combined with the
one-dimensional Stein identity `gaussianReal_stein`.
-/
lemma pi_gaussian_stein_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (ι → ℝ) → ℝ) (i : ι)
    (hh : ContDiff ℝ 1 h) (C c : ℝ) (_hc : 0 ≤ c) (_hC : 0 ≤ C)
    (hhb : ∀ y, |h y| ≤ C * Real.exp (c * ∑ j, |y j|))
    (hdb : ∀ y j, |fderiv ℝ h y (Pi.single j 1)| ≤ C * Real.exp (c * ∑ k, |y k|)) :
    ∫ y, y i * h y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = ∫ y, fderiv ℝ h y (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h_integrable : MeasureTheory.Integrable (fun y : ι → ℝ => y i * h y) (Measure.pi fun _ : ι => gaussianReal 0 1) ∧ MeasureTheory.Integrable (fun y : ι → ℝ => (fderiv ℝ h y) (Pi.single i 1)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    constructor;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => C * |y i| * Real.exp ( c * ∑ j, |y j| );
      · convert integrable_abs_coord_mul_exp_c_sum_abs_pi c i |> fun h => h.const_mul C using 2 ; ring;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply i |> Measurable.aestronglyMeasurable ) ( hh.continuous.aestronglyMeasurable );
      · filter_upwards [ ] with y using by rw [ Real.norm_eq_abs, abs_mul ] ; nlinarith [ hhb y, abs_nonneg ( y i ) ] ;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => C * Real.exp ( c * ∑ j, |y j| );
      · exact MeasureTheory.Integrable.const_mul ( integrable_exp_c_sum_abs_pi c ) _;
      · fun_prop;
      · exact Filter.Eventually.of_forall fun y => hdb y i;
  have h_split : ∀ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, x * h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x) ∂(gaussianReal 0 1) = ∫ x : ℝ, (fderiv ℝ h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x)) (Pi.single i 1) ∂(gaussianReal 0 1) := by
    intro y
    set Yb : ι → ℝ := fun j => if h : j = i then 0 else y ⟨j,h⟩
    have h_Yb : ∀ x, Function.update Yb i x = fun j => if h : j = i then x else y ⟨j,h⟩ := by
      grind;
    have h_G : ∀ x, HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)) x := by
      intro x
      have h_chain : HasDerivAt (fun t => h (Function.update Yb i t)) ((fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)) x := by
        have h_update : HasDerivAt (fun t => Function.update Yb i t) (Pi.single i 1) x :=
          hasDerivAt_update Yb i x
        convert HasFDerivAt.comp_hasDerivAt x
          (hh.contDiffAt.differentiableAt (by norm_num) |> DifferentiableAt.hasFDerivAt)
          h_update using 1 <;> rfl
      exact h_chain;
    have h_G_bound : ∀ x, |h (Function.update Yb i x)| ≤ C * Real.exp (c * (|x| + ∑ j, |y j|)) ∧ |(fderiv ℝ h (Function.update Yb i x)) (Pi.single i 1)| ≤ C * Real.exp (c * (|x| + ∑ j, |y j|)) := by
      intro x
      have h_sum : ∑ j, |(Function.update Yb i x) j| = |x| + ∑ j, |y j| := by
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)];
        refine' congr_arg₂ ( · + · ) _ _;
        · simp +decide;
        · refine' Finset.sum_bij ( fun j _ => ⟨ j, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ Function.update_apply ];
          aesop;
      exact ⟨ by simpa only [ h_sum ] using hhb ( Function.update Yb i x ), by simpa only [ h_sum ] using hdb ( Function.update Yb i x ) i ⟩;
    have := @gaussianReal_stein;
    convert this ( fun x => h ( Function.update Yb i x ) ) ( fun x => ( fderiv ℝ h ( Function.update Yb i x ) ) ( Pi.single i 1 ) ) h_G _ ( C * Real.exp ( c * ∑ j, |y j| ) ) c _ _ using 1;
    · fun_prop;
    · intro x; convert h_G_bound x |>.1 using 1; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf;
    · intro x; specialize h_G_bound x; rw [ mul_assoc, ← Real.exp_add ] ; ring_nf at *; aesop;
  have h_split : ∫ y : ι → ℝ, y i * h y ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = ∫ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, x * h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x) ∂(gaussianReal 0 1) ∂(Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
    have h_split : Measure.pi (fun _ : ι => gaussianReal 0 1) = Measure.map (fun p : ℝ × ({j // j ≠ i} → ℝ) => Function.update (fun j => if h : j = i then 0 else p.2 ⟨j,h⟩) i p.1) (gaussianReal 0 1 |> Measure.prod <| Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
      refine' MeasureTheory.Measure.pi_eq _;
      intro s hs; rw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun p : ℝ × ( { j // j ≠ i } → ℝ ) => Function.update ( fun j => if h : j = i then 0 else p.2 ⟨ j, h ⟩ ) i p.1 ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
        · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          simp +decide [MeasureTheory.Measure.prod_prod]
          refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
        · grind;
      · refine' Measurable.of_eval _;
        intro j; by_cases hj : j = i <;> simp +decide [ hj ] ;
        · exact measurable_fst;
        · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_split, MeasureTheory.integral_map ];
    · erw [ MeasureTheory.integral_prod_symm ];
      · simp +decide;
      · convert h_integrable.1 using 1;
        rw [ h_split ];
        rw [ MeasureTheory.integrable_map_measure ];
        · rfl;
        · exact h_split ▸ h_integrable.1.aestronglyMeasurable;
        · refine' Measurable.aemeasurable _;
          refine' Measurable.of_eval _;
          intro j; by_cases hj : j = i <;> simp +decide [ hj ] ;
          · exact measurable_fst;
          · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · refine' Measurable.aemeasurable _;
      refine' Measurable.of_eval _;
      intro j; by_cases hj : j = i <;> simp +decide [ hj ] ;
      · exact measurable_fst;
      · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · exact h_split ▸ h_integrable.1.aestronglyMeasurable;
  have h_split : ∫ y : ι → ℝ, (fderiv ℝ h y) (Pi.single i 1) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = ∫ y : {j // j ≠ i} → ℝ, ∫ x : ℝ, (fderiv ℝ h (Function.update (fun j => if h : j = i then 0 else y ⟨j,h⟩) i x)) (Pi.single i 1) ∂(gaussianReal 0 1) ∂(Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
    have h_split : Measure.pi (fun _ : ι => gaussianReal 0 1) = Measure.map (fun p : ℝ × ({j // j ≠ i} → ℝ) => Function.update (fun j => if h : j = i then 0 else p.2 ⟨j,h⟩) i p.1) (gaussianReal 0 1 |> Measure.prod <| Measure.pi fun _ : {j // j ≠ i} => gaussianReal 0 1) := by
      rw [ MeasureTheory.Measure.pi_eq ];
      intro s hs;
      rw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun p : ℝ × ( { j // j ≠ i } → ℝ ) => Function.update ( fun j => if h : j = i then 0 else p.2 ⟨ j, h ⟩ ) i p.1 ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
        · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          simp +decide [MeasureTheory.Measure.prod_prod]
          refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
        · grind;
      · refine' Measurable.of_eval _;
        intro j; by_cases hj : j = i <;> simp +decide [ hj ] ;
        · exact measurable_fst;
        · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_split, MeasureTheory.integral_map ];
    · rw [ MeasureTheory.integral_prod_symm ];
      rw [ h_split ] at h_integrable;
      have hmap : Measurable
          (fun p : ℝ × ({j // j ≠ i} → ℝ) ↦
            Function.update (fun j ↦ if h : j = i then 0 else p.2 ⟨j, h⟩) i p.1) := by
        refine Measurable.of_eval fun j ↦ ?_
        by_cases hj : j = i
        · simpa [hj] using measurable_fst
        · have hm : Measurable
              (fun p : ℝ × ({j // j ≠ i} → ℝ) ↦ p.2 ⟨j, hj⟩) :=
            (@measurable_pi_apply {j // j ≠ i} (fun _ ↦ ℝ) _ ⟨j, hj⟩).comp
              measurable_snd
          simpa [hj] using hm
      convert h_integrable.2.comp_measurable hmap using 1
      rfl
    · refine' Measurable.aemeasurable _;
      refine' Measurable.of_eval _;
      intro j; by_cases hj : j = i <;> simp +decide [ hj ] ;
      · exact measurable_fst;
      · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd;
    · convert h_integrable.2.aestronglyMeasurable using 1;
      exact h_split.symm;
  aesop

/-
The `i`-th coordinate of the gradient equals the partial derivative in direction `i`.
-/
lemma gradient_coord_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    (gradient g w) i = fderiv ℝ g w (EuclideanSpace.single i 1) := by
  simp +decide [ gradient ];
  rw [ ← InnerProductSpace.toDual_symm_apply ];
  rw [ EuclideanSpace.inner_single_right ] ; norm_num

/-
Transferring the `i`-th gradient coordinate through the `toLp` identification: it becomes
the `i`-th partial derivative of the composed function on `ι → ℝ`.
-/
lemma gradient_toLp_coord_eq_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : EuclideanSpace ℝ ι → ℝ) (hg : Differentiable ℝ g) (y : ι → ℝ) (i : ι) :
    (gradient g (WithLp.toLp 2 y)) i
      = fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single i 1) := by
  rw [ gradient ];
  rw [ show ( fun z => g ( WithLp.toLp 2 z ) ) = g ∘ ( WithLp.toLp 2 ) from rfl, fderiv_comp ] <;> norm_num [ hg.differentiableAt, WithLp.ofLp ];
  · rw [ fderiv ];
    rw [ fderiv ];
    rw [ fderivWithin_univ, fderivWithin_univ, show ( WithLp.toLp 2 : ( ι → ℝ ) → EuclideanSpace ℝ ι ) = ( PiLp.continuousLinearEquiv 2 ℝ ( fun _ : ι => ℝ ) ).symm from rfl, ContinuousLinearEquiv.fderiv ] ; norm_num;
    rw [ ← InnerProductSpace.toDual_symm_apply ];
    rw [ EuclideanSpace.inner_single_right ] ; norm_num;
  · refine' ⟨ _, hasFDerivAt_iff_tendsto.mpr _ ⟩;
    exact ( ContinuousLinearEquiv.toContinuousLinearMap ( ContinuousLinearEquiv.symm ( EuclideanSpace.equiv ι ℝ ) ) );
    simp +decide

/-
The value and gradient of `g` are integrable against the standard Gaussian when they have
exponential growth.
-/
lemma gaussian_ibp_integrable {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ)
    (i : ι) (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    Integrable (fun w => w i * g w) (standardGaussianMeasureOnEuclidean ι)
      ∧ Integrable (fun w => (gradient g w) i) (standardGaussianMeasureOnEuclidean ι) := by
  constructor;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun w => |C| * Real.exp ( ( c + 1 ) * ‖w‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm ( c + 1 ) ) _;
    · refine' MeasureTheory.AEStronglyMeasurable.mul _ ( hg.continuous.aestronglyMeasurable );
      fun_prop;
    · refine' Filter.Eventually.of_forall fun w => _;
      refine' le_trans ( norm_mul_le _ _ ) _;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( show ‖w.ofLp i‖ ≤ ‖w‖ from _ ) ( norm_nonneg _ ) ) _;
      · simp +decide [ EuclideanSpace.norm_eq ];
        exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( w.ofLp i ) ) ( Finset.mem_univ i ) );
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( hgb w ) ( norm_nonneg _ ) ) _;
        rw [ add_mul, one_mul, Real.exp_add ];
        cases abs_cases C <;> nlinarith [ show 0 ≤ Real.exp ( c * ‖w‖ ) * Real.exp ‖w‖ by positivity, show ‖w‖ ≤ Real.exp ‖w‖ by exact le_trans ( by norm_num ) ( Real.add_one_le_exp _ ), show 0 ≤ C * Real.exp ( c * ‖w‖ ) by exact le_trans ( abs_nonneg _ ) ( hgb w ) ];
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun w => C * Real.exp ( c * ‖w‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm c ) _;
    · have h_grad_cont : Continuous (gradient g) := by
        have := hg.continuous_fderiv;
        exact Continuous.comp ( LinearIsometryEquiv.continuous _ ) ( this one_ne_zero );
      fun_prop;
    · refine' Filter.Eventually.of_forall fun w => le_trans _ ( hgradb w );
      simp +decide [ EuclideanSpace.norm_eq ];
      exact Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( ( gradient g w ).ofLp i ) ) ( Finset.mem_univ i ) )

/-!
# Smooth-case Gaussian covariance bound: supporting lemmas

This file develops the covariance interpolation identity used to prove the sharp
Gaussian covariance bound `SYK.gaussian_cov_bound_smooth`.

Let `μ = standardGaussianMeasureOnEuclidean ι` and, for a `C¹` function `F` with
`‖∇F‖ ≤ L`, write `G x = exp (s * F x)`.  The covariance
`Cov = ∫ F·G - (∫ F)(∫ G)` is represented as
`Cov = ∫₀^{π/2} sin θ · (∫∫ ⟪∇G x, ∇F (cos θ • x - sin θ • y)⟫ dμ dμ) dθ`
via rotation invariance of `μ.prod μ` and the Gaussian integration-by-parts lemma
`gaussian_ibp`.  The bound then follows from Cauchy–Schwarz and `∫₀^{π/2} sin = 1`.
-/

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-! ## Infrastructure moved from gaussian_concentration.lean -/

/-- Per-coordinate Gaussian integration by parts: the tensorized one-dimensional Stein
identity along coordinate `i`. -/
lemma gaussian_ibp_coord {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ) (i : ι)
    (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∫ w, w i * g w ∂(standardGaussianMeasureOnEuclidean ι)
      = ∫ w, (gradient g w) i ∂(standardGaussianMeasureOnEuclidean ι) := by
  classical
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  obtain ⟨hI1, hI2⟩ := gaussian_ibp_integrable g i hg C c hgb hgradb
  have hmeas : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    WithLp.measurable_toLp 2 _
  have hC : 0 ≤ C := le_trans (abs_nonneg (g 0)) (by simpa using hgb 0)
  have hcd : ContDiff ℝ 1 (fun z : ι → ℝ => g (WithLp.toLp 2 z)) :=
    hg.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.contDiff
  have hnorm : ∀ y : ι → ℝ, ‖WithLp.toLp 2 y‖ ≤ ∑ j, |y j| := by
    intro y
    rw [EuclideanSpace.norm_eq]
    have hsum_nonneg : (0:ℝ) ≤ ∑ j, |y j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : ∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2 = ∑ j, |y j| ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs]
    have hle : ∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2 ≤ (∑ j, |y j|) ^ 2 := by
      rw [h1]; exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _
    calc Real.sqrt (∑ j, ‖(WithLp.toLp 2 y) j‖ ^ 2)
        ≤ Real.sqrt ((∑ j, |y j|) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ∑ j, |y j| := Real.sqrt_sq hsum_nonneg
  have hexpmono : ∀ y : ι → ℝ, c * ‖WithLp.toLp 2 y‖ ≤ |c| * ∑ j, |y j| := fun y =>
    (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hnorm y) (abs_nonneg c))
  have hcoord : ∀ (x : EuclideanSpace ℝ ι) (j : ι), |x j| ≤ ‖x‖ := by
    intro x j
    rw [EuclideanSpace.norm_eq,
        show |x j| = Real.sqrt (|x j|^2) from (Real.sqrt_sq (abs_nonneg _)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [show |x j|^2 = ‖x j‖^2 by rw [Real.norm_eq_abs]]
    exact Finset.single_le_sum (f := fun k => ‖x k‖^2) (fun k _ => by positivity) (Finset.mem_univ j)
  have hhb' : ∀ y : ι → ℝ, |g (WithLp.toLp 2 y)| ≤ C * Real.exp (|c| * ∑ j, |y j|) := fun y =>
    (hgb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpmono y)) hC)
  have hdb' : ∀ (y : ι → ℝ) (j : ι),
      |fderiv ℝ (fun z => g (WithLp.toLp 2 z)) y (Pi.single j 1)|
        ≤ C * Real.exp (|c| * ∑ k, |y k|) := by
    intro y j
    rw [← gradient_toLp_coord_eq_fderiv g hgd y j]
    exact (hcoord _ j).trans ((hgradb _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpmono y)) hC))
  have eq3 := pi_gaussian_stein_coord (fun z => g (WithLp.toLp 2 z)) i hcd C |c|
    (abs_nonneg c) hC hhb' hdb'
  have hμ : standardGaussianMeasureOnEuclidean ι
      = (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2) := rfl
  rw [hμ, integral_map hmeas.aemeasurable (by rw [← hμ]; exact hI1.aestronglyMeasurable),
      integral_map hmeas.aemeasurable (by rw [← hμ]; exact hI2.aestronglyMeasurable)]
  simp only [gradient_toLp_coord_eq_fderiv g hgd]
  exact eq3


/-
**`n`-dimensional Gaussian integration by parts.**  For a `C¹` function `g` on
`EuclideanSpace ℝ ι` whose value and gradient grow no faster than `C e^{c‖w‖}`, and any fixed
vector `v`, integration against the standard Gaussian satisfies
`∫ ⟪v, w⟫ g w = ∫ ⟪v, ∇g w⟫`.  This is the tensorization of the one-dimensional Stein
identity `gaussianReal_stein` over the coordinates (Fubini for the product measure).
-/
lemma gaussian_ibp {ι : Type*} [Fintype ι] (g : EuclideanSpace ℝ ι → ℝ)
    (v : EuclideanSpace ℝ ι) (hg : ContDiff ℝ 1 g)
    (C c : ℝ) (hgb : ∀ w, |g w| ≤ C * Real.exp (c * ‖w‖))
    (hgradb : ∀ w, ‖gradient g w‖ ≤ C * Real.exp (c * ‖w‖)) :
    ∫ w, (inner ℝ v w) * g w ∂(standardGaussianMeasureOnEuclidean ι)
      = ∫ w, (inner ℝ v (gradient g w)) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have hcoord := fun i => gaussian_ibp_coord g i hg C c hgb hgradb
  have hint := fun i => gaussian_ibp_integrable g i hg C c hgb hgradb
  -- `⟪v, w⟫ = ∑ i, v i * w i` and `⟪v, ∇g w⟫ = ∑ i, v i * (∇g w) i`; use linearity of the
  -- integral and the per-coordinate identity.
  simp +decide only [inner];
  simp +decide only [Finset.sum_mul];
  rw [ MeasureTheory.integral_finsetSum, MeasureTheory.integral_finsetSum ];
  · simp_all +decide [ mul_assoc ];
    exact Finset.sum_congr rfl fun i _ => by rw [ show ( fun w => w.ofLp i * ( v.ofLp i * g w ) ) = fun w => v.ofLp i * ( w.ofLp i * g w ) by ext; ring, show ( fun w => ( gradient g w ).ofLp i * v.ofLp i ) = fun w => v.ofLp i * ( gradient g w ).ofLp i by ext; ring, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hcoord i ] ;
  · simp_all +decide;
    exact fun i => ( ‹∀ i, Integrable ( fun w => w.ofLp i * g w ) ( standardGaussianMeasureOnEuclidean ι ) ∧ Integrable ( fun w => ( gradient g w ).ofLp i ) ( standardGaussianMeasureOnEuclidean ι ) › i ).2.mul_const _;
  · simp +decide [ mul_assoc ];
    exact fun i => by simpa only [ mul_left_comm, mul_assoc ] using ( ‹∀ i, Integrable ( fun w => w.ofLp i * g w ) ( standardGaussianMeasureOnEuclidean ι ) ∧ Integrable ( fun w => ( gradient g w ).ofLp i ) ( standardGaussianMeasureOnEuclidean ι ) › i |>.1 ).const_mul ( v.ofLp i ) ;

/-- A `C¹` function with gradient bounded by `L` grows at most linearly. -/
lemma contDiff_abs_le_of_gradient_le {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (x : EuclideanSpace ℝ ι) :
    |F x| ≤ |F 0| + L * ‖x‖ := by
  have hfd : ∀ y, ‖fderiv ℝ F y‖ ≤ L := by
    intro y
    have hh : ‖gradient F y‖ = ‖fderiv ℝ F y‖ := by
      rw [gradient]; exact LinearIsometryEquiv.norm_map _ _
    rw [← hh]; exact hgrad y
  have hlip : LipschitzWith L.toNNReal F := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num))
    intro y
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal L hL]
    exact hfd y
  have hb := hlip.dist_le_mul x 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero, Real.coe_toNNReal L hL, Real.norm_eq_abs] at hb
  have h2 := abs_le.mp hb
  cases abs_cases (F x) <;> cases abs_cases (F 0) <;> nlinarith [norm_nonneg x]

/-- The gradient of `x ↦ exp (s * F x)`. -/
lemma gradient_exp_smul {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : ContDiff ℝ 1 F) (s : ℝ) (x : EuclideanSpace ℝ ι) :
    gradient (fun y => Real.exp (s * F y)) x = (s * Real.exp (s * F x)) • gradient F x := by
  have hd : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hexp : HasFDerivAt (fun y => Real.exp (s * F y))
      ((s * Real.exp (s * F x)) • fderiv ℝ F x) x := by
    have h1 : HasFDerivAt (fun y => s * F y) (s • fderiv ℝ F x) x := hd.const_mul s
    simpa only [smul_smul, mul_comm] using h1.exp
  rw [gradient, gradient, hexp.fderiv, map_smul]

/-- Projecting the rotation-invariant product Gaussian onto its first coordinate returns the
standard Gaussian: `(μ.prod μ).map ((rotation θ ·).1) = μ`.  In particular the affine
combination `cos θ • a + sin θ • b` has law `μ`. -/
lemma map_rotation_fst {ι : Type*} [Fintype ι] (θ : ℝ) :
    (((standardGaussianMeasureOnEuclidean ι).prod
        (standardGaussianMeasureOnEuclidean ι)).map
          (fun p => (ContinuousLinearMap.rotation θ p).1))
      = standardGaussianMeasureOnEuclidean ι := by
  have hmean : (standardGaussianMeasureOnEuclidean ι)[id] = 0 :=
    standardGaussianMeasureOnEuclidean_integral_id
  have hrot := IsGaussian.map_rotation_eq_self hmean θ
  have hfstcomp :
      (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (ContinuousLinearMap.rotation θ p).1)
        = Prod.fst ∘ (ContinuousLinearMap.rotation θ) := rfl
  rw [hfstcomp, ← Measure.map_map measurable_fst
      (ContinuousLinearMap.rotation θ).continuous.measurable, hrot]
  have h := Measure.fst_prod (μ := standardGaussianMeasureOnEuclidean ι)
    (ν := standardGaussianMeasureOnEuclidean ι)
  exact h


/-
The rotation `(a,b) ↦ (cos θ • a + sin θ • b, -(sin θ • a) + cos θ • b)` preserves the
product standard Gaussian measure.
-/
lemma rotation_measurePreserving (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation θ)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  refine' ⟨ _, _ ⟩;
  · fun_prop;
  · convert IsGaussian.map_rotation_eq_self _ _;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · convert standardGaussianMeasureOnEuclidean_integral_id using 1

/-
Gradient of `F` composed with the affine map `z ↦ c • x - d • z`.
-/
lemma gradient_affine_comp (F : EuclideanSpace ℝ ι → ℝ) (hF : Differentiable ℝ F)
    (c d : ℝ) (x y : EuclideanSpace ℝ ι) :
    gradient (fun z => F (c • x - d • z)) y = (-d) • gradient F (c • x - d • y) := by
  have haff : HasFDerivAt (fun z : EuclideanSpace ℝ ι => c • x - d • z)
      (0 - d • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) y :=
    (hasFDerivAt_const (c • x) y).sub ((hasFDerivAt_id y).const_smul d)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp y haff
  have hmap :
      fderiv ℝ F (c • x - d • y) ∘L
          (0 - d • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) =
        (-d) • fderiv ℝ F (c • x - d • y) := by
    ext v
    simp
  have hcomp' : HasFDerivAt (fun z => F (c • x - d • z))
      ((-d) • fderiv ℝ F (c • x - d • y)) y := by
    simpa only [Function.comp_def, hmap] using hcomp
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt, map_smul, toDual_gradient]
  exact hcomp'

/-
The covariance rewritten as a double integral over the product measure.
-/
lemma gaussian_cov_eq_double (f g : EuclideanSpace ℝ ι → ℝ)
    (hf : Integrable f (standardGaussianMeasureOnEuclidean ι))
    (hg : Integrable g (standardGaussianMeasureOnEuclidean ι))
    (hfg : Integrable (fun x => f x * g x) (standardGaussianMeasureOnEuclidean ι)) :
    (∫ x, f x * g x ∂(standardGaussianMeasureOnEuclidean ι))
        - (∫ x, f x ∂(standardGaussianMeasureOnEuclidean ι))
          * (∫ x, g x ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ a, ∫ b, f a * (g a - g b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  norm_num [ mul_sub ];
  convert ( MeasureTheory.integral_sub ( hfg ) _ ) using 1;
  rw [ MeasureTheory.integral_sub hfg ];
  any_goals exact fun x => f x * ∫ y, g y ∂standardGaussianMeasureOnEuclidean ι;
  · rw [ MeasureTheory.integral_mul_const ];
  · exact hf.mul_const _;
  · convert MeasureTheory.integral_sub _ _ using 3;
    · rw [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul ] <;> norm_num;
      · rw [ MeasureTheory.integral_const_mul ];
      · exact MeasureTheory.integrable_const _;
      · exact hg.const_mul _;
    · exact hfg;
    · exact hf.mul_const _;
  · exact hf.mul_const _

/-
Fundamental theorem of calculus along the rotation path `θ ↦ cos θ • a + sin θ • b`.
-/
lemma gaussian_path_ftc (g : EuclideanSpace ℝ ι → ℝ) (hg : ContDiff ℝ 1 g)
    (a b : EuclideanSpace ℝ ι) :
    g a - g b = - ∫ θ in (0:ℝ)..(Real.pi/2),
      inner ℝ (gradient g (Real.cos θ • a + Real.sin θ • b))
        (-Real.sin θ • a + Real.cos θ • b) := by
  -- By the fundamental theorem of calculus, the integral of the derivative of $h$ over $[0, \pi/2]$ is $h(\pi/2) - h(0)$.
  have h_ftc : ∫ θ in (0 : ℝ)..Real.pi / 2, deriv (fun θ => g (Real.cos θ • a + Real.sin θ • b)) θ = g b - g a := by
    rw [ intervalIntegral.integral_deriv_eq_sub ];
    · simp +decide;
    · exact fun x hx => DifferentiableAt.comp x ( hg.contDiffAt.differentiableAt ( by norm_num ) ) ( DifferentiableAt.add ( DifferentiableAt.smul ( Real.differentiableAt_cos ) ( differentiableAt_const _ ) ) ( DifferentiableAt.smul ( Real.differentiableAt_sin ) ( differentiableAt_const _ ) ) );
    · apply Continuous.intervalIntegrable
      have hcurve : ContDiff ℝ 1
          (fun θ : ℝ => g (Real.cos θ • a + Real.sin θ • b)) := by
        apply hg.comp
        exact (Real.contDiff_cos.smul contDiff_const).add
          (Real.contDiff_sin.smul contDiff_const)
      exact hcurve.continuous_deriv (by norm_num)
  -- By definition of the gradient, we know that the derivative of $g$ along the path is given by the inner product of the gradient and the direction vector.
  have h_grad : ∀ θ, deriv (fun θ => g (Real.cos θ • a + Real.sin θ • b)) θ = ⟪gradient g (Real.cos θ • a + Real.sin θ • b), (-Real.sin θ) • a + (Real.cos θ) • b⟫_ℝ := by
    intro θ
    have hpath : HasDerivAt (fun t : ℝ => Real.cos t • a + Real.sin t • b)
        ((-Real.sin θ) • a + Real.cos θ • b) θ :=
      (Real.hasDerivAt_cos θ).smul_const a |>.add
        ((Real.hasDerivAt_sin θ).smul_const b)
    have hcomp := hg.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt.comp θ
      hpath.hasFDerivAt
    have hcomp' : HasFDerivAt
        (fun t => g (Real.cos t • a + Real.sin t • b))
        (fderiv ℝ g (Real.cos θ • a + Real.sin θ • b) ∘L
          ContinuousLinearMap.toSpanSingleton ℝ
            ((-Real.sin θ) • a + Real.cos θ • b)) θ := by
      simpa only [Function.comp_def] using hcomp
    have hderiv := hcomp'.hasDerivAt.deriv
    rw [← toDual_gradient] at hderiv
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      InnerProductSpace.toDual_apply_apply] using hderiv
  aesop

/-
Integrability of the change-of-variables covariance integrand
`ψ (x,y) = F(cos θ•x - sin θ•y) · ⟪∇G x, y⟫` on the product Gaussian measure.
-/
lemma integrable_cov_psi (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        F (Real.cos θ • p.1 - Real.sin θ • p.2) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) p.1) p.2)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun p => ( |F 0| + L * ‖p.1‖ + L * ‖p.2‖ ) * ( |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ );
  · -- The product of integrable functions is integrable.
    have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (|F 0| + L * ‖p.1‖ + L) * (Real.exp (|s| * L * ‖p.1‖)) * (‖p.2‖ + ‖p.2‖^2)) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
      have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => (|F 0| + L * ‖p‖ + L) * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) ∧ Integrable (fun p : EuclideanSpace ℝ ι => ‖p‖ + ‖p‖^2) (standardGaussianMeasureOnEuclidean ι) := by
        constructor;
        · have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => ‖p‖ * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
            have h_integrable : ∀ c : ℝ, Integrable (fun p : EuclideanSpace ℝ ι => Real.exp (c * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
              intro c
              apply SYK.integrable_exp_mul_norm;
            have := h_integrable ( |s| * L + 1 );
            refine' this.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_norm.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_const.mul measurable_norm |> Measurable.aestronglyMeasurable ) );
            · filter_upwards [ ] with p using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ add_mul, one_mul, Real.exp_add ] ; nlinarith [ Real.exp_pos ( |s| * L * ‖p‖ ), Real.exp_pos ‖p‖, Real.add_one_le_exp ‖p‖, mul_nonneg ( abs_nonneg s ) hL ] ;
          have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι => Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
            convert integrable_exp_mul_norm ( |s| * L ) using 1;
          simp_all +decide [ add_mul, mul_assoc ];
          exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add ( h_integrable.const_mul _ ) ( MeasureTheory.Integrable.const_mul ‹_› _ ) ) ( h_integrable.const_mul _ );
        · refine' MeasureTheory.Integrable.add _ _;
          · have := @integrable_exp_mul_norm ι;
            refine' MeasureTheory.Integrable.mono' ( this 1 ) _ _;
            · exact Continuous.aestronglyMeasurable ( continuous_norm );
            · filter_upwards [ ] with x using by simpa using le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) ;
          · convert integrable_exp_mul_norm 2 |> fun h => h.mono' _ _ using 1;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( sq_nonneg _ ) ] ; rw [ two_mul, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp ( ‖x‖ ), Real.add_one_le_exp ( ‖x‖ ), norm_nonneg x ] ;
      exact MeasureTheory.Integrable.mul_prod h_integrable.1 h_integrable.2;
    refine' h_integrable.const_mul ( |s| * L * Real.exp ( |s| * |F 0| ) ) |> fun h => h.mono' _ _;
    · fun_prop;
    · filter_upwards [ ] with p;
      rw [ Real.norm_of_nonneg ( by positivity ) ];
      nlinarith [ show 0 ≤ |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ by positivity, show 0 ≤ |s| * L * Real.exp ( |s| * |F 0| ) * Real.exp ( |s| * L * ‖p.1‖ ) * ‖p.2‖ ^ 2 by positivity, show 0 ≤ |F 0| * ‖p.2‖ by positivity, show 0 ≤ L * ‖p.1‖ * ‖p.2‖ by positivity, show 0 ≤ L * ‖p.2‖ ^ 2 by positivity ];
  · refine' Measurable.aestronglyMeasurable _;
    refine' Measurable.mul _ _;
    · exact hF.continuous.measurable.comp (by fun_prop)
    · -- The gradient of a continuously differentiable function is continuous, hence measurable.
      have h_grad_cont : Continuous (fun x => gradient (fun z => Real.exp (s * F z)) x) := by
        refine' Continuous.comp ( LinearIsometryEquiv.continuous _ ) _;
        fun_prop;
      fun_prop;
  · refine' Filter.Eventually.of_forall _;
    intro p
    have h_abs : |F (Real.cos θ • p.1 - Real.sin θ • p.2)| ≤ |F 0| + L * ‖p.1‖ + L * ‖p.2‖ := by
      have h_triangle : ‖Real.cos θ • p.1 - Real.sin θ • p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
        exact le_trans ( norm_sub_le _ _ ) ( add_le_add ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) );
      have := contDiff_abs_le_of_gradient_le F L hL hF hgrad ( Real.cos θ • p.1 - Real.sin θ • p.2 ) ; simp_all +decide [ add_assoc ] ; nlinarith;
    have h_grad : ‖gradient (fun z => Real.exp (s * F z)) p.1‖ ≤ |s| * L * Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖p.1‖) := by
      have h_grad : ‖gradient (fun z => Real.exp (s * F z)) p.1‖ = |s| * Real.exp (s * F p.1) * ‖gradient F p.1‖ := by
        rw [ gradient_exp_smul F hF s p.1 ] ; norm_num [ norm_smul, abs_mul ];
      have h_exp : Real.exp (s * F p.1) ≤ Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖p.1‖) := by
        rw [ ← Real.exp_add ];
        have h_exp : |F p.1| ≤ |F 0| + L * ‖p.1‖ := by
          apply contDiff_abs_le_of_gradient_le F L hL hF hgrad p.1;
        exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> cases abs_cases ( F p.1 ) <;> nlinarith [ abs_le.mp h_exp ] );
      nlinarith [ show 0 ≤ |s| * Real.exp ( s * F p.1 ) by positivity, show 0 ≤ |s| * L by positivity, hgrad p.1 ]
    generalize_proofs at *;
    simp_all +decide;
    exact mul_le_mul h_abs ( by simpa [ abs_mul ] using abs_real_inner_le_norm ( gradient ( fun z => Real.exp ( s * F z ) ) p.1 ) p.2 |> le_trans <| mul_le_mul_of_nonneg_right h_grad <| norm_nonneg _ ) ( by positivity ) ( by positivity )

/-
Integrability of the original covariance integrand
`Φ (a,b) = F a · ⟪∇G(cos θ•a+sin θ•b), -sin θ•a+cos θ•b⟫` on the product Gaussian measure.
-/
lemma integrable_cov_Phi (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        F p.1 *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • p.1 + Real.sin θ • p.2))
            (-Real.sin θ • p.1 + Real.cos θ • p.2))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
  have h_integrable : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      F (Real.cos θ • p.1 - Real.sin θ • p.2) *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) p.1) p.2)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
        apply_rules [ integrable_cov_psi ];
  have h_rotation : MeasurePreserving (ContinuousLinearMap.rotation θ)
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))
      ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) :=
    rotation_measurePreserving θ
  have h_integrable_map : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪gradient (fun z => Real.exp (s * F z)) p.1, p.2⟫_ℝ) ((Measure.prod (standardGaussianMeasureOnEuclidean ι) (standardGaussianMeasureOnEuclidean ι)).map (ContinuousLinearMap.rotation θ)) := by
    rw [h_rotation.map_eq]
    exact h_integrable
  convert h_integrable_map.comp_measurable
      (ContinuousLinearMap.rotation θ).continuous.measurable using 1;
  · ext ⟨x, y⟩
    simp only [Function.comp_apply, ContinuousLinearMap.rotation_apply]
    congr 1
    apply congr_arg F
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      x.ofLp i = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * x.ofLp i := by
        rw [Real.sin_sq_add_cos_sq]
        ring
      _ = Real.cos θ * (Real.cos θ * x.ofLp i + Real.sin θ * y.ofLp i) -
          Real.sin θ * (-Real.sin θ * x.ofLp i + Real.cos θ * y.ofLp i) := by ring

/-
Change of variables by the rotation on the product Gaussian measure: rewriting the
covariance integrand `F a · ⟪∇G(cos θ•a+sin θ•b), -sin θ•a+cos θ•b⟫` as
`F(cos θ•x - sin θ•y) · ⟪∇G x, y⟫`.  Here `G z = exp (s * F z)`.
-/
lemma gaussian_cov_change_of_var (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ a, ∫ b, F a *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x) y
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have h_psi_integrable : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
    convert integrable_cov_psi F L hL hF hgrad s θ using 1;
  have h_psi_integrable : ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F p.1 * ⟪(gradient (fun z => Real.exp (s * F z)) (Real.cos θ • p.1 + Real.sin θ • p.2)), -Real.sin θ • p.1 + Real.cos θ • p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) := by
    have h_psi_integrable : ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (Real.cos θ • p.1 - Real.sin θ • p.2) * ⟪(gradient (fun z => Real.exp (s * F z)) p.1), p.2⟫_ℝ ∂(Measure.map (ContinuousLinearMap.rotation θ) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι))) := by
      rw [ rotation_measurePreserving θ |>.map_eq ];
    rw [ h_psi_integrable, MeasureTheory.integral_map ];
    · simp +decide [ ContinuousLinearMap.rotation ];
      congr with p ; ring_nf;
      rw [ show Real.cos θ • Real.cos θ • p.1 + Real.cos θ • Real.sin θ • p.2 - ( - ( Real.sin θ • Real.sin θ • p.1 ) + Real.sin θ • Real.cos θ • p.2 ) = p.1 by ext i; simpa using by ring_nf; rw [ Real.sin_sq, Real.cos_sq ] ; ring ] ; ring;
    · exact Continuous.aemeasurable ( by continuity );
    · refine' MeasureTheory.Integrable.aestronglyMeasurable _;
      rw [ rotation_measurePreserving θ |>.map_eq ] ; assumption;
  convert h_psi_integrable.symm using 1;
  · erw [ MeasureTheory.integral_prod ];
    convert integrable_cov_Phi F L hL hF hgrad s θ using 1;
  · rw [ MeasureTheory.integral_prod ];
    assumption

/-
Gaussian integration by parts in the `y`-variable, applied to the change-of-variables
form.  Here `G z = exp (s * F z)`.
-/
lemma gaussian_cov_ibp_step (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x) y
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = - Real.sin θ * ∫ x, ∫ y,
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  have hpointwise : ∀ x, ∫ y, F (Real.cos θ • x - Real.sin θ • y) * ⟪gradient (fun z => Real.exp (s * F z)) x, y⟫_ℝ ∂standardGaussianMeasureOnEuclidean ι = -Real.sin θ * ∫ y, ⟪gradient (fun z => Real.exp (s * F z)) x, gradient F (Real.cos θ • x - Real.sin θ • y)⟫_ℝ ∂standardGaussianMeasureOnEuclidean ι := by
    intro x;
    convert gaussian_ibp ( fun y => F ( Real.cos θ • x - Real.sin θ • y ) ) ( gradient ( fun z => Real.exp ( s * F z ) ) x ) ( show ContDiff ℝ 1 ( fun y => F ( Real.cos θ • x - Real.sin θ • y ) ) from ?_ ) ( |F 0| + L * ‖x‖ + L ) 1 ?_ ?_ using 1;
    · ac_rfl;
    · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; rw [ gradient_affine_comp ] ; ring_nf;
      · simp +decide [ inner_smul_right ];
      · exact ContDiff.differentiable_one hF;
    · fun_prop;
    · intro w
      have h_bound : |F (Real.cos θ • x - Real.sin θ • w)| ≤ |F 0| + L * ‖Real.cos θ • x - Real.sin θ • w‖ := by
        apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
      have h_bound : ‖Real.cos θ • x - Real.sin θ • w‖ ≤ ‖x‖ + ‖w‖ := by
        exact le_trans ( norm_sub_le _ _ ) ( add_le_add ( by simpa [ norm_smul ] using mul_le_of_le_one_left ( norm_nonneg x ) ( Real.abs_cos_le_one θ ) ) ( by simpa [ norm_smul ] using mul_le_of_le_one_left ( norm_nonneg w ) ( Real.abs_sin_le_one θ ) ) );
      nlinarith [ abs_nonneg ( F 0 ), Real.add_one_le_exp ( 1 * ‖w‖ ), Real.one_le_exp ( show 0 ≤ 1 * ‖w‖ by positivity ), mul_nonneg hL ( norm_nonneg x ), mul_nonneg hL ( norm_nonneg w ) ];
    · -- By definition of $G$, we know that its gradient is $(-\sin \theta) \cdot \nabla F(\cos \theta \cdot x - \sin \theta \cdot y)$.
      have h_grad_G : ∀ w, gradient (fun y => F (Real.cos θ • x - Real.sin θ • y)) w = (-Real.sin θ) • gradient F (Real.cos θ • x - Real.sin θ • w) := by
        apply_rules [ gradient_affine_comp ];
        fun_prop;
      intro w
      rw [h_grad_G w]
      simp [norm_smul];
      refine' le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) _;
      refine' le_trans ( hgrad _ ) _;
      exact le_trans ( by nlinarith [ abs_nonneg ( F 0 ), norm_nonneg x ] ) ( le_mul_of_one_le_right ( by positivity ) ( Real.one_le_exp ( norm_nonneg w ) ) );
  rw [ ← MeasureTheory.integral_const_mul, funext hpointwise ]

/-- Per-angle covariance identity: change of variables (rotation) followed by Gaussian
integration by parts in the second variable.  Here `G z = exp (s * F z)`. -/
lemma gaussian_cov_per_theta (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    (∫ a, ∫ b, F a *
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b)
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = - Real.sin θ * ∫ x, ∫ y,
          inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  rw [gaussian_cov_change_of_var F L hL hF hgrad s θ,
      gaussian_cov_ibp_step F L hL hF hgrad s θ]

/-
Joint integrability of the covariance integrand over `((a,b), θ)` where `θ` ranges over
the finite interval `Ioc 0 (π/2)`.  Used for the Fubini swap.
-/
set_option maxHeartbeats 1000000 in
lemma integrable_cov_joint (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    Integrable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ =>
        F q.1.1 *
          inner ℝ (gradient (fun z => Real.exp (s * F z))
              (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2))
            (-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2))
      (((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)).prod
        (volume.restrict (Set.Ioc (0:ℝ) (Real.pi/2)))) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun q => ( |s| * L * Real.exp ( |s| * |F 0| ) ) * ( ( |F 0| + L * ‖q.1.1‖ ) * Real.exp ( |s| * L * ‖q.1.1‖ ) * ( 1 + ‖q.1.1‖ ) ) * ( ( 1 + ‖q.1.2‖ ) * Real.exp ( |s| * L * ‖q.1.2‖ ) );
  · have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) => ((|F 0| + L * ‖p.1‖) * Real.exp (|s| * L * ‖p.1‖) * (1 + ‖p.1‖)) * ((1 + ‖p.2‖) * Real.exp (|s| * L * ‖p.2‖))) ((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)) := by
      have h_integrable : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) ^ a * Real.exp (b * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        intro a b ha hb
        have h_integrable : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ ι => Real.exp ((a + b) * ‖p‖) * 2 ^ a) (standardGaussianMeasureOnEuclidean ι) := by
          exact MeasureTheory.Integrable.mul_const ( integrable_exp_mul_norm _ ) _;
        refine' h_integrable.mono' _ _;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.pow_const ( by exact measurable_const.add ( measurable_norm ) ) _ ) ( by exact Real.continuous_exp.measurable.comp ( by exact measurable_const.mul ( measurable_norm ) ) ) );
        · filter_upwards [ ] with p
          have h_bound : (1 + ‖p‖) ^ a ≤ 2 ^ a * Real.exp (a * ‖p‖) := by
            have h_bound : (1 + ‖p‖) ≤ 2 * Real.exp (‖p‖) := by
              linarith [ Real.add_one_le_exp ‖p‖, norm_nonneg p ];
            exact le_trans ( Real.rpow_le_rpow ( by positivity ) h_bound ( by positivity ) ) ( by rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.exp_mul ] ; ring_nf; norm_num );
          rw [ Real.norm_of_nonneg ( by positivity ) ];
          calc
            (1 + ‖p‖) ^ a * Real.exp (b * ‖p‖)
                ≤ (2 ^ a * Real.exp (a * ‖p‖)) * Real.exp (b * ‖p‖) :=
              mul_le_mul_of_nonneg_right h_bound (Real.exp_nonneg _)
            _ = Real.exp ((a + b) * ‖p‖) * 2 ^ a := by
              rw [add_mul, Real.exp_add]
              ring
      have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (|F 0| + L * ‖p‖) * Real.exp (|s| * L * ‖p‖) * (1 + ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) ^ 2 * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
          exact_mod_cast h_integrable 2 ( |s| * L ) ( by norm_num ) ( by positivity );
        refine' h_integrable.const_mul ( |F 0| + L ) |> fun h => h.mono' _ _;
        · fun_prop;
        · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_of_sub_nonneg ( by ring_nf; positivity ) ;
      have h_integrable : MeasureTheory.Integrable (fun (p : EuclideanSpace ℝ ι) => (1 + ‖p‖) * Real.exp (|s| * L * ‖p‖)) (standardGaussianMeasureOnEuclidean ι) := by
        convert ‹∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Integrable ( fun p : EuclideanSpace ℝ ι => ( 1 + ‖p‖ ) ^ a * Real.exp ( b * ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › 1 ( |s| * L ) zero_le_one ( mul_nonneg ( abs_nonneg s ) hL ) using 1 ; norm_num;
      convert MeasureTheory.Integrable.mul_prod ‹Integrable ( fun p : EuclideanSpace ℝ ι => ( |F 0| + L * ‖p‖ ) * Real.exp ( |s| * L * ‖p‖ ) * ( 1 + ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › ‹Integrable ( fun p : EuclideanSpace ℝ ι => ( 1 + ‖p‖ ) * Real.exp ( |s| * L * ‖p‖ ) ) ( standardGaussianMeasureOnEuclidean ι ) › using 1;
    convert h_integrable.const_mul ( |s| * L * Real.exp ( |s| * |F 0| ) ) |> MeasureTheory.Integrable.comp_fst <| MeasureTheory.Measure.restrict ( MeasureTheory.MeasureSpace.volume ) ( Set.Ioc 0 ( Real.pi / 2 ) ) using 1 ; ext ; ring_nf;
  · have h_measurable : Continuous (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ => F q.1.1 * ⟪gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2), -Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2⟫_ℝ) := by
      refine' Continuous.mul ( hF.continuous.comp continuous_fst.fst ) _;
      have h_cont : Continuous (fun q : EuclideanSpace ℝ ι => gradient (fun z => Real.exp (s * F z)) q) := by
        refine' Continuous.comp ( LinearIsometryEquiv.continuous _ ) _;
        fun_prop;
      fun_prop;
    exact h_measurable.aestronglyMeasurable
  · refine' Filter.Eventually.of_forall _;
    intro q
    have h_bound : ‖gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ ≤ |s| * L * Real.exp (|s| * |F 0|) * Real.exp (|s| * L * ‖q.1.1‖) * Real.exp (|s| * L * ‖q.1.2‖) := by
      have h_bound : ‖gradient (fun z => Real.exp (s * F z)) (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ ≤ |s| * L * Real.exp (|s| * |F 0| + |s| * L * ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖) := by
        rw [ gradient_exp_smul ];
        · rw [ norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ];
          rw [ mul_right_comm ];
          gcongr;
          · exact hgrad _;
          · have h_bound : |F (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)| ≤ |F 0| + L * ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖ := by
              apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
            cases abs_cases s <;> cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp h_bound ];
        · exact hF;
      have h_bound : ‖Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2‖ ≤ ‖q.1.1‖ + ‖q.1.2‖ := by
        exact le_trans ( norm_add_le _ _ ) ( add_le_add ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_cos_le_one _ ) ) ( by rw [ norm_smul, Real.norm_eq_abs ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.abs_sin_le_one _ ) ) );
      simp_all +decide [ mul_assoc, ← Real.exp_add ];
      exact le_trans ‹_› ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ abs_nonneg s, mul_nonneg ( abs_nonneg s ) hL ] ) <| by positivity ) <| by positivity );
    have h_bound : |F q.1.1| ≤ |F 0| + L * ‖q.1.1‖ := by
      apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
    have h_bound : ‖-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2‖ ≤ (1 + ‖q.1.1‖) * (1 + ‖q.1.2‖) := by
      refine' le_trans ( norm_add_le _ _ ) _;
      norm_num [ norm_smul ];
      nlinarith [ abs_nonneg ( Real.sin q.2 ), abs_nonneg ( Real.cos q.2 ), Real.abs_sin_le_one q.2, Real.abs_cos_le_one q.2, norm_nonneg q.1.1, norm_nonneg q.1.2 ];
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |F q.1.1| * |⟪gradient (fun z => Real.exp (s * F z))
          (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2),
          -Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2⟫_ℝ|
          ≤ |F q.1.1| *
              (‖gradient (fun z => Real.exp (s * F z))
                  (Real.cos q.2 • q.1.1 + Real.sin q.2 • q.1.2)‖ *
                ‖-Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ ≤ (|F 0| + L * ‖q.1.1‖) *
            ((|s| * L * Real.exp (|s| * |F 0|) *
                Real.exp (|s| * L * ‖q.1.1‖) *
                Real.exp (|s| * L * ‖q.1.2‖)) *
              ((1 + ‖q.1.1‖) * (1 + ‖q.1.2‖))) := by
            gcongr
      _ = (|s| * L * Real.exp (|s| * |F 0|)) *
            ((|F 0| + L * ‖q.1.1‖) * Real.exp (|s| * L * ‖q.1.1‖) *
              (1 + ‖q.1.1‖)) *
            ((1 + ‖q.1.2‖) * Real.exp (|s| * L * ‖q.1.2‖)) := by ring

lemma gaussian_cov_fubini_swap (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    (∫ a, ∫ b, F a * (∫ θ in (0:ℝ)..(Real.pi/2),
        inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
          (-Real.sin θ • a + Real.cos θ • b))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ θ in (0:ℝ)..(Real.pi/2), ∫ a, ∫ b, F a *
          inner ℝ (gradient (fun z => Real.exp (s * F z)) (Real.cos θ • a + Real.sin θ • b))
            (-Real.sin θ • a + Real.cos θ • b)
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  -- Apply Fubini's theorem to interchange the order of integration.
  have h_fubini : ∀ {f : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × ℝ → ℝ}, MeasureTheory.Integrable f (((standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι)).prod (volume.restrict (Set.Ioc 0 (Real.pi / 2)))) → ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, ∫ θ in Set.Ioc 0 (Real.pi / 2), f (p, θ) ∂volume ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) = ∫ θ in Set.Ioc 0 (Real.pi / 2), ∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, f (p, θ) ∂(standardGaussianMeasureOnEuclidean ι).prod (standardGaussianMeasureOnEuclidean ι) ∂volume := by
    intro f hf;
    apply_rules [ MeasureTheory.integral_integral_swap ];
  convert h_fubini ( integrable_cov_joint F L hL hF hgrad s ) using 1;
  · rw [ MeasureTheory.integral_prod ];
    · simp +decide only [intervalIntegral.integral_of_le Real.pi_div_two_pos.le, MeasureTheory.integral_const_mul];
    · convert ( integrable_cov_joint F L hL hF hgrad s ).integral_prod_left using 1;
  · rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun θ hθ => _;
    erw [ MeasureTheory.integral_prod ];
    convert integrable_cov_Phi F L hL hF hgrad s θ using 1

/-
The covariance interpolation representation: `Cov = ∫₀^{π/2} sin θ · H θ dθ` where
`H θ = ∫∫ ⟪∇G x, ∇F (cos θ • x - sin θ • y)⟫`.
-/
lemma gaussian_cov_repr (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    (∫ x, F x * Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))
        - (∫ x, F x ∂(standardGaussianMeasureOnEuclidean ι))
          * (∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))
      = ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ *
          ∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
            (gradient F (Real.cos θ • x - Real.sin θ • y))
            ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι) := by
  rw [ gaussian_cov_eq_double ];
  · convert congr_arg Neg.neg ( gaussian_cov_fubini_swap F L hL hF hgrad s ) using 1;
    · rw [ ← MeasureTheory.integral_neg ];
      congr! 2;
      rw [ ← MeasureTheory.integral_neg ] ; congr ; ext ;
      rename_i a b;
      rw [ gaussian_path_ftc ( fun z => Real.exp ( s * F z ) ) ( by fun_prop ) a b ] ; ring;
    · rw [ ← intervalIntegral.integral_neg ] ; congr ; ext θ ; rw [ gaussian_cov_per_theta F L hL hF hgrad s θ ] ; ring;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => |F 0| + L * Real.exp ( ‖x‖ );
    · refine' MeasureTheory.Integrable.add _ _;
      · simp +decide;
      · refine' MeasureTheory.Integrable.const_mul _ _;
        convert integrable_exp_mul_norm 1 using 1;
        norm_num;
    · exact hF.continuous.aestronglyMeasurable;
    · filter_upwards [ ] with x using le_trans ( contDiff_abs_le_of_gradient_le F L hL hF hgrad x ) ( by nlinarith [ Real.add_one_le_exp ‖x‖, norm_nonneg x ] );
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => Real.exp ( |s| * ( |F 0| + L * ‖x‖ ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * |F 0| ) ) using 1 ; ext ; ring_nf;
      rw [ ← Real.exp_add ];
    · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) );
    · have h_bound : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
        apply contDiff_abs_le_of_gradient_le F L hL hF hgrad;
      filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( h_bound x ) ] ) ;
  · have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x * Real.exp (s * F x)| ≤ C * Real.exp (c * ‖x‖) := by
      have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x| ≤ C * Real.exp (c * ‖x‖) := by
        use |F 0| + L, 1;
        have := contDiff_abs_le_of_gradient_le F L hL hF hgrad;
        exact ⟨ by positivity, by positivity, fun x => le_trans ( this x ) ( by nlinarith [ abs_nonneg ( F 0 ), Real.add_one_le_exp ( 1 * ‖x‖ ), norm_nonneg x ] ) ⟩;
      have h_integrable : ∃ C c, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |Real.exp (s * F x)| ≤ C * Real.exp (c * ‖x‖) := by
        use Real.exp (|s| * |F 0|), |s| * L;
        simp +decide [ ← Real.exp_add ];
        exact ⟨ Real.exp_nonneg _, mul_nonneg ( abs_nonneg _ ) hL, fun x => by cases abs_cases s <;> cases abs_cases ( F 0 ) <;> cases abs_cases ( F x ) <;> nlinarith [ contDiff_abs_le_of_gradient_le F L hL hF hgrad x ] ⟩;
      obtain ⟨ C₁, c₁, hC₁, hc₁, h₁ ⟩ := ‹∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ x, |F x| ≤ C * Real.exp ( c * ‖x‖ ) ›
      obtain ⟨ C₂, c₂, hC₂, hc₂, h₂ ⟩ := h_integrable
      use C₁ * C₂, c₁ + c₂;
      simp_all +decide [ abs_mul, add_mul, Real.exp_add ];
      exact ⟨ mul_nonneg hC₁ hC₂, add_nonneg hc₁ hc₂, fun x => by nlinarith [ h₁ x, h₂ x, abs_nonneg ( F x ), Real.exp_pos ( s * F x ), mul_le_mul_of_nonneg_left ( h₂ x ) ( abs_nonneg ( F x ) ) ] ⟩;
    obtain ⟨ C, c, hC, hc, h ⟩ := h_integrable;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => C * Real.exp ( c * ‖x‖ );
    · exact MeasureTheory.Integrable.const_mul ( integrable_exp_mul_norm c ) _;
    · exact Continuous.aestronglyMeasurable ( by exact Continuous.mul ( hF.continuous ) ( Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) ) );
    · exact Filter.Eventually.of_forall h

/-
Pointwise bound on the inner double integral `H θ`.
-/
lemma gaussian_cov_H_bound (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s θ : ℝ) :
    |∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
          (gradient F (Real.cos θ • x - Real.sin θ • y))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι)|
      ≤ |s| * L ^ 2 * ∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι) := by
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : EuclideanSpace ℝ ι → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun x => |s| * L ^ 2 * Real.exp ( s * F x );
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    have h_integrable : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
      intro x;
      have h_abs_le : ∀ x, |F x| ≤ |F 0| + L * ‖x‖ := by
        intro x
        have h_abs_le_aux : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (fun t => F (t • x)) t| ≤ L * ‖x‖ := by
          intro t ht
          have h_deriv : deriv (fun t => F (t • x)) t = (fderiv ℝ F (t • x)) x := by
            rw [ deriv ];
            erw [ fderiv_comp ] <;> norm_num [ hF.contDiffAt.differentiableAt ];
            exact congr_arg _ ( HasDerivAt.deriv ( by simpa using HasDerivAt.smul_const ( hasDerivAt_id t ) x ) );
          have := hgrad ( t • x ) ; simp_all +decide [ gradient ] ;
          exact le_trans ( by simpa using ( fderiv ℝ F ( t • x ) |> ContinuousLinearMap.le_opNorm ) x ) ( mul_le_mul_of_nonneg_right ( hgrad _ ) ( norm_nonneg _ ) )
        have := exists_deriv_eq_slope ( f := fun t => F ( t • x ) ) zero_lt_one;
        simp +zetaDelta at *;
        exact this ( Continuous.continuousOn <| by exact hF.continuous.comp ( continuous_id.smul continuous_const ) ) ( fun t ht => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.comp t ( hF.contDiffAt.differentiableAt ( by norm_num ) ) <| differentiableAt_id.smul_const _ ) |> fun ⟨ c, hc₁, hc₂ ⟩ => abs_le.mpr ⟨ by cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_abs_le_aux c hc₁.1.le hc₁.2.le ) ], by cases abs_cases ( F 0 ) <;> nlinarith [ abs_le.mp ( h_abs_le_aux c hc₁.1.le hc₁.2.le ) ] ⟩;
      exact h_abs_le x;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun x => Real.exp ( |s| * ( |F 0| + L * ‖x‖ ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * |F 0| ) ) using 2 ; ring_nf;
      rw [ ← Real.exp_add ];
    · exact Continuous.aestronglyMeasurable ( by exact Real.continuous_exp.comp ( continuous_const.mul hF.continuous ) );
    · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> cases abs_cases ( F x ) <;> nlinarith [ h_integrable x ] ) ;
  · refine' Filter.Eventually.of_forall fun x => _;
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun y => ‖gradient ( fun z => Real.exp ( s * F z ) ) x‖ * L;
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
    · exact MeasureTheory.integrable_const _;
    · filter_upwards [ ] with y using by simpa using abs_real_inner_le_norm ( gradient ( fun z => Real.exp ( s * F z ) ) x ) ( gradient F ( Real.cos θ • x - Real.sin θ • y ) ) |> le_trans <| mul_le_mul_of_nonneg_left ( hgrad _ ) <| norm_nonneg _;
    · have h_grad_exp : gradient (fun z => Real.exp (s * F z)) x = (s * Real.exp (s * F x)) • gradient F x := by
        unfold gradient;
        rw [ fderiv_exp ] <;> norm_num [ hF.contDiffAt.differentiableAt ];
        rw [ fderiv_const_mul ] <;> norm_num [ hF.contDiffAt.differentiableAt ] ; ring_nf;
        rw [ smul_smul, mul_comm ];
      simp_all +decide [ norm_smul ];
      nlinarith [ show 0 ≤ |s| * Real.exp ( s * F x ) * L by positivity, show 0 ≤ |s| * Real.exp ( s * F x ) * ‖gradient F x‖ by positivity, hgrad x, mul_le_mul_of_nonneg_left ( hgrad x ) ( show 0 ≤ |s| * Real.exp ( s * F x ) by positivity ) ];
  · rw [ MeasureTheory.integral_const_mul ]

/-
Interval-integrability of the covariance representation integrand `θ ↦ sin θ · H θ`.
-/
lemma gaussian_cov_sinH_intervalIntegrable (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    IntervalIntegrable (fun θ => Real.sin θ *
        ∫ x, ∫ y, inner ℝ (gradient (fun z => Real.exp (s * F z)) x)
          (gradient F (Real.cos θ • x - Real.sin θ • y))
          ∂(standardGaussianMeasureOnEuclidean ι) ∂(standardGaussianMeasureOnEuclidean ι))
      volume 0 (Real.pi/2) := by
  rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_div_two_pos.le ] at *;
  refine' MeasureTheory.Integrable.congr _ _;
  refine' fun θ => ∫ p : ( EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ), - ( F p.1 * inner ℝ ( gradient ( fun z => Real.exp ( s * F z ) ) ( Real.cos θ • p.1 + Real.sin θ • p.2 ) ) ( -Real.sin θ • p.1 + Real.cos θ • p.2 ) ) ∂ ( standardGaussianMeasureOnEuclidean ι |> Measure.prod <| standardGaussianMeasureOnEuclidean ι );
  · exact (integrable_cov_joint F L hL hF hgrad s).neg.integral_prod_right
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with θ hθ;
    have := gaussian_cov_per_theta F L hL hF hgrad s θ;
    rw [ MeasureTheory.integral_neg, MeasureTheory.integral_prod ];
    · linarith;
    · convert integrable_cov_Phi F L hL hF hgrad s θ using 1

/-!
# Mollification of Lipschitz functions

To pass from the smooth Gaussian covariance bound to the general Lipschitz case we approximate
an `L`-Lipschitz function `F` by a sequence of `C¹` functions with the same Lipschitz constant,
obtained by convolving `F` with a normalized `ContDiffBump`.  The key output is
`SYK.exists_smooth_lipschitz_approx`.
-/

open MeasureTheory

/-
Approximation of an `L`-Lipschitz function on a finite-dimensional Euclidean space by a
sequence of `C¹` functions with gradient bounded by `L`, uniform linear growth, and pointwise
convergence.  Obtained by convolution with a normalized `ContDiffBump` of shrinking radius.
-/
lemma exists_smooth_lipschitz_approx {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : LipschitzWith L.toNNReal F) :
    ∃ Fn : ℕ → EuclideanSpace ℝ ι → ℝ,
      (∀ n, ContDiff ℝ 1 (Fn n)) ∧
      (∀ n x, ‖gradient (Fn n) x‖ ≤ L) ∧
      (∀ n x, |Fn n x| ≤ (|F 0| + L) + L * ‖x‖) ∧
      (∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) := by
  obtain ⟨Fn, hFn⟩ : ∃ (Fn : ℕ → (EuclideanSpace ℝ ι → ℝ)),
      (∀ n, ContDiff ℝ 1 (Fn n)) ∧
      (∀ n, LipschitzWith L.toNNReal (Fn n)) ∧
      (∀ n x, |Fn n x| ≤ |F 0| + L + L * ‖x‖) ∧
      (∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) := by
        have : ∀ n : ℕ, ∃ ψ : ContDiffBump (0 : EuclideanSpace ℝ ι), ψ.rIn = 1 / (n + 2) ∧ ψ.rOut = 2 / (n + 2) := by
          intro n
          use ⟨1 / (n + 2), 2 / (n + 2), by positivity, by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩;
        choose ψ hψ using this;
        refine' ⟨ fun n => convolution ( ( ψ n ).normed volume ) F ( ContinuousLinearMap.lsmul ℝ ℝ ) volume, _, _, _, _ ⟩;
        · intro n;
          apply_rules [ HasCompactSupport.contDiff_convolution_left ];
          · exact ( ψ n ).hasCompactSupport_normed;
          · exact ContDiffBump.contDiff_normed _;
          · exact hLip.continuous.locallyIntegrable;
        · intro n;
          refine' LipschitzWith.of_dist_le_mul _;
          intro x y;
          simp +decide [ convolution_def ];
          rw [ dist_eq_norm, ← MeasureTheory.integral_sub ];
          · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
            refine' fun a => ( ψ n ).normed volume a * ( L.toNNReal * dist x y );
            · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with a;
              rw [ ← mul_sub, norm_mul, Real.norm_of_nonneg ( by exact ( ψ n ).nonneg_normed _ ) ];
              exact mul_le_mul_of_nonneg_left ( hLip.dist_le_mul _ _ ) ( by exact ( ψ n ).nonneg_normed _ ) |> le_trans <| by simp +decide [ dist_eq_norm ] ;
            · rw [ MeasureTheory.integral_mul_const, ( ψ n ).integral_normed ] ; aesop;
          · refine' Continuous.integrable_of_hasCompactSupport _ _;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun t ht => by aesop;
          · refine' Continuous.integrable_of_hasCompactSupport _ _;
            · exact Continuous.mul ( ContDiffBump.continuous_normed _ ) ( hLip.continuous.comp ( continuous_const.sub continuous_id' ) );
            · have h_compact_support : HasCompactSupport (fun t => (ψ n).normed volume t) := by
                convert ( ψ n ).hasCompactSupport_normed; all_goals infer_instance;
              exact h_compact_support.mono fun x hx => by aesop;
        · intro n x
          have h_bound : ∀ t ∈ Metric.ball (0 : EuclideanSpace ℝ ι) ((ψ n).rOut), |F (x - t)| ≤ |F 0| + L + L * ‖x‖ := by
            intro t ht
            have h_bound : |F (x - t)| ≤ |F 0| + L * ‖x - t‖ := by
              have := hLip.dist_le_mul ( x - t ) 0;
              simp_all +decide [ dist_eq_norm ];
              exact abs_le.mpr ⟨ by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ], by cases abs_cases ( F 0 ) <;> linarith [ abs_le.mp this ] ⟩;
            have h_bound : ‖x - t‖ ≤ ‖x‖ + ‖t‖ := by
              exact norm_sub_le x t;
            have h_bound : ‖t‖ ≤ 1 := by
              simp_all +decide [ Metric.mem_ball ];
              exact ht.le.trans ( by rw [ div_le_iff₀ ] <;> linarith );
            nlinarith [ abs_nonneg ( F 0 ), abs_nonneg ( F ( x - t ) ) ];
          have h_integral_bound : ∫ t, |(ψ n).normed volume t * F (x - t)| ∂volume ≤ ∫ t, (ψ n).normed volume t * (|F 0| + L + L * ‖x‖) ∂volume := by
            refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
            · exact Filter.Eventually.of_forall fun t => abs_nonneg _;
            · exact MeasureTheory.Integrable.mul_const ( ContDiffBump.integrable_normed _ ) _;
            · filter_upwards [ ] with t;
              by_cases ht : t ∈ Metric.ball 0 (ψ n).rOut;
              · rw [ abs_mul, abs_of_nonneg ( show 0 ≤ ( ψ n ).normed volume t from _ ) ];
                · exact mul_le_mul_of_nonneg_left ( h_bound t ht ) ( by exact ( ψ n ).nonneg_normed t );
                · exact ( ψ n ).nonneg_normed t;
              · rw [ show ( ψ n ).normed volume t = 0 from _ ] ; norm_num;
                exact not_not.mp fun h => ht <| by simpa using ( ψ n ).support_normed_eq.subset <| by simpa using h;
          refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : EuclideanSpace ℝ ι → ℝ ) ) ( h_integral_bound.trans _ );
          rw [ MeasureTheory.integral_mul_const, ContDiffBump.integral_normed ] ; norm_num;
        · apply ContDiffBump.convolution_tendsto_right_of_continuous;
          · simpa only [ hψ ] using tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
          · exact hLip.continuous;
  refine' ⟨ Fn, hFn.1, _, hFn.2.2.1, hFn.2.2.2 ⟩;
  intro n x
  have h_grad : ‖fderiv ℝ (Fn n) x‖ ≤ L := by
    convert norm_fderiv_le_of_lipschitz ℝ ( hFn.2.1 n ) using 1;
    rw [ Real.coe_toNNReal _ hL ]
  simp [gradient, h_grad]

/-
Dominated-convergence transfer of the three relevant integrals along a uniformly
linearly-bounded, pointwise-convergent approximating sequence.
-/
lemma tendsto_integrals_of_approx {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (Fn : ℕ → EuclideanSpace ℝ ι → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcont : ∀ n, Continuous (Fn n))
    (hbound : ∀ n x, |Fn n x| ≤ C + L * ‖x‖)
    (htend : ∀ x, Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (F x))) (s : ℝ) :
    Filter.Tendsto (fun n => ∫ x, Fn n x ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, F x ∂(standardGaussianMeasureOnEuclidean ι)))
      ∧ Filter.Tendsto (fun n => ∫ x, Real.exp (s * Fn n x) ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι)))
      ∧ Filter.Tendsto (fun n => ∫ x, Fn n x * Real.exp (s * Fn n x) ∂(standardGaussianMeasureOnEuclidean ι))
        Filter.atTop (nhds (∫ x, F x * Real.exp (s * F x) ∂(standardGaussianMeasureOnEuclidean ι))) := by
  refine' ⟨ _, _, _ ⟩;
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => C + L * ‖x‖;
    · exact fun n => ( hcont n |> Continuous.aestronglyMeasurable );
    · refine' MeasureTheory.Integrable.add _ _;
      · exact MeasureTheory.integrable_const _;
      · have h_integrable : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm 1 |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( continuous_norm );
          · filter_upwards [ ] with x using by simpa using le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) ;
        exact h_integrable.const_mul L;
    · exact fun n => Filter.Eventually.of_forall ( hbound n );
    · exact Filter.Eventually.of_forall htend;
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => Real.exp ( |s| * ( C + L * ‖x‖ ) );
    · exact fun n => Continuous.aestronglyMeasurable ( Real.continuous_exp.comp ( continuous_const.mul ( hcont n ) ) );
    · convert integrable_exp_mul_norm ( |s| * L ) |> fun h => h.const_mul ( Real.exp ( |s| * C ) ) using 1 ; ext ; ring_nf;
      rw [ ← Real.exp_add ];
    · intro n; filter_upwards [ ] with x; rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n x ) ] ) ;
    · exact Filter.Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp ( Filter.Tendsto.mul tendsto_const_nhds ( htend x ) );
  · refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => ( C + L * ‖x‖ ) * Real.exp ( |s| * ( C + L * ‖x‖ ) );
    · exact fun n => Continuous.aestronglyMeasurable ( by exact Continuous.mul ( hcont n ) ( Real.continuous_exp.comp ( continuous_const.mul ( hcont n ) ) ) );
    · have h_integrable : Integrable (fun x => (C + L * ‖x‖) * Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
        have h_integrable : Integrable (fun x => ‖x‖ * Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
          convert integrable_exp_mul_norm ( |s| * L + 1 ) |> fun h => h.mono' _ _ using 1;
          · exact Continuous.aestronglyMeasurable ( by continuity );
          · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ add_mul, one_mul, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp ( |s| * L * ‖x‖ ), Real.add_one_le_exp ‖x‖, norm_nonneg x, show 0 ≤ |s| * L * ‖x‖ by positivity ] ;
        simp_all +decide [ add_mul, mul_assoc ];
        refine' MeasureTheory.Integrable.add _ _;
        · have h_integrable : Integrable (fun x => Real.exp (|s| * L * ‖x‖)) (standardGaussianMeasureOnEuclidean ι) := by
            convert integrable_exp_mul_norm ( |s| * L ) using 1;
          simpa only [ mul_assoc ] using h_integrable.const_mul C;
        · exact h_integrable.const_mul L;
      convert h_integrable.const_mul ( Real.exp ( |s| * C ) ) using 2 ; ring_nf;
      simp only [mul_assoc, ← Real.exp_add];
    · intro n
      simp;
      filter_upwards [ ] with x using mul_le_mul ( hbound n x ) ( Real.exp_le_exp.mpr ( by cases abs_cases s <;> nlinarith [ abs_le.mp ( hbound n x ) ] ) ) ( by positivity ) ( by positivity );
    · exact Filter.Eventually.of_forall fun x => Filter.Tendsto.mul ( htend x ) ( Real.continuous_exp.continuousAt.tendsto.comp ( tendsto_const_nhds.mul ( htend x ) ) )

/-!
## Gaussian concentration inequalities
-/

/-
The sharp Gaussian covariance bound for a `C¹` function with globally bounded gradient
(the smooth case, proved via rotation invariance of `μ.prod μ` and Gaussian integration by
parts).  The general Lipschitz case follows by mollification.
-/
lemma gaussian_cov_bound_smooth {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hF : ContDiff ℝ 1 F) (hgrad : ∀ x, ‖gradient F x‖ ≤ L) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  rw [ gaussian_cov_repr F L hL hF hgrad s ];
  rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun θ => |Real.sin θ| * ( |s| * L ^ 2 * ∫ x, Real.exp ( s * F x ) ∂standardGaussianMeasureOnEuclidean ι );
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · exact Continuous.integrableOn_Ioc ( by continuity );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with θ hθ;
    simpa only [ norm_mul, Real.norm_eq_abs ] using mul_le_mul_of_nonneg_left ( gaussian_cov_H_bound F L hL hF hgrad s θ ) ( abs_nonneg _ );
  · rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le ( by linarith [ Real.pi_pos, hx.2 ] ) ) ], ← intervalIntegral.integral_of_le Real.pi_div_two_pos.le ] ; norm_num ; ring_nf ; norm_num

/-
**The sharp Gaussian covariance bound** for an `L`-Lipschitz `F`:
`|Cov(F, e^{sF})| ≤ L² |s| ∫ e^{sF}` against the standard Gaussian.  This is the last
remaining analytic input to `product_standardGaussian_mgf_le`.  It reduces to the smooth
case `gaussian_cov_bound_smooth` (proved via rotation invariance of `μ.prod μ` and the
Gaussian integration-by-parts lemma `gaussian_ibp`) by mollifying `F` into a sequence of
`C¹` functions with the same Lipschitz constant and passing to the limit by dominated
convergence.  The supporting infrastructure (`gaussian_ibp`, `map_rotation_fst`,
`gradient_exp_smul`, `contDiff_abs_le_of_gradient_le`, the mean-zero and integrability
lemmas) is fully proved; the smooth-case assembly and the mollification limit remain.
-/
lemma gaussian_cov_bound {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (s : ℝ) :
    |(∫ x, F x * Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)
        - (∫ x, F x ∂standardGaussianMeasureOnEuclidean ι)
          * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι)|
      ≤ L ^ 2 * |s| * (∫ x, Real.exp (s * F x) ∂standardGaussianMeasureOnEuclidean ι) := by
  obtain ⟨Fn, hCD, hgr, hbd, htd⟩ := SYK.exists_smooth_lipschitz_approx F L hL.le hLip;
  obtain ⟨t1, t2, t3⟩ := SYK.tendsto_integrals_of_approx F Fn (|F 0| + L) L (by positivity) hL.le (fun n => (hCD n).continuous) hbd htd s;
  convert le_of_tendsto_of_tendsto' ( Filter.Tendsto.abs ( t3.sub ( t1.mul t2 ) ) ) ( t2.const_mul ( L ^ 2 * |s| ) ) _ using 1;
  exact fun n => gaussian_cov_bound_smooth _ _ hL.le ( hCD n ) ( hgr n ) s

/-- The centered Lipschitz function of a standard Gaussian vector has a sub-Gaussian
moment-generating function with parameter `L ^ 2`.  This is Herbst's conclusion from the
Gaussian logarithmic Sobolev inequality: for every `t`,
`𝔼[exp (t (F - 𝔼 F))] ≤ exp (L² t² / 2)`.

This is the analytic heart of Gaussian concentration and is not currently available in
Mathlib; a full proof requires the Gaussian log-Sobolev inequality (or the equivalent
Ornstein–Uhlenbeck semigroup interpolation) together with Rademacher's theorem
(`LipschitzWith.ae_differentiableAt`) giving `‖∇F‖ ≤ L` almost everywhere. -/
theorem product_standardGaussian_mgf_le
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) (t : ℝ) :
    mgf (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
        (standardGaussianMeasureOnEuclidean ι) t ≤
      Real.exp (L ^ 2 * t ^ 2 / 2) :=
  herbst_of_cov_bound F L hL hLip (gaussian_cov_bound F L hL hLip) t

/-- The centered Lipschitz function of a standard Gaussian vector has a sub-Gaussian
moment-generating function with parameter `L ^ 2`. -/
theorem product_standardGaussian_hasSubgaussianMGF
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) :
    HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι)
      (Real.toNNReal (L ^ 2)) (standardGaussianMeasureOnEuclidean ι) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- Integrability of `exp (t · (F - ∫ F))`.
    have hbound : ∀ x : EuclideanSpace ℝ ι, |F x| ≤ |F 0| + L * ‖x‖ := by
      intro x
      have h := hLip.dist_le_mul x 0
      simp only [dist_eq_norm, sub_zero, Real.coe_toNNReal L hL.le] at h
      cases abs_cases (F x) <;> cases abs_cases (F 0) <;>
        [skip; skip; skip; skip] <;> nlinarith [abs_le.mp h, norm_nonneg x]
    set μ := standardGaussianMeasureOnEuclidean ι
    have hdom := (integrable_exp_mul_norm (ι := ι) (|t| * L)).const_mul
      (Real.exp (|t| * |F 0| + |t| * |∫ y, F y ∂μ|))
    refine hdom.mono' ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul
        ((hLip.continuous).sub continuous_const))).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hFx : F x - ∫ y, F y ∂μ ≤ |F 0| + L * ‖x‖ + |∫ y, F y ∂μ| := by
        have := abs_le.mp (hbound x)
        have h2 := neg_abs_le (∫ y, F y ∂μ)
        nlinarith [this.1, this.2]
      have hneg : -(|F 0| + L * ‖x‖ + |∫ y, F y ∂μ|) ≤ F x - ∫ y, F y ∂μ := by
        have := abs_le.mp (hbound x)
        have h2 := le_abs_self (∫ y, F y ∂μ)
        nlinarith [this.1, this.2]
      have hnn : (0:ℝ) ≤ L * ‖x‖ := mul_nonneg hL.le (norm_nonneg x)
      rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> nlinarith [hFx, hneg, hnn]
  · -- The moment-generating-function bound, from the deep Herbst inequality.
    have hmgf := product_standardGaussian_mgf_le F L hL hLip t
    have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
      Real.coe_toNNReal _ (sq_nonneg L)
    rw [hcoe]
    exact hmgf

/-- Upper-tail concentration for Lipschitz functions of a standard Gaussian vector. -/
theorem product_standardGaussian_upper_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  set μ := standardGaussianMeasureOnEuclidean ι with hμ
  have hsg := product_standardGaussian_hasSubgaussianMGF F L hL hLip
  have hchern := hsg.measure_ge_le (ε := t) ht.le
  have hcoe : ((Real.toNNReal (L ^ 2) : ℝ≥0) : ℝ) = L ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg L)
  rw [hcoe] at hchern
  -- `hchern : μ.real {ω | t ≤ F ω - ∫ F} ≤ exp (-t ^ 2 / (2 * L ^ 2))`
  have hsubset :
      {x | F x - ∫ y, F y ∂μ > t} ⊆
        {x | t ≤ F x - ∫ y, F y ∂μ} := by
    intro x hx
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hx ⊢
    exact le_of_lt hx
  calc
    μ {x | F x - ∫ y, F y ∂μ > t}
        ≤ μ {x | t ≤ F x - ∫ y, F y ∂μ} := measure_mono hsubset
    _ = ENNReal.ofReal (μ.real {x | t ≤ F x - ∫ y, F y ∂μ}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
          ENNReal.ofReal_le_ofReal hchern

/-- Lower-tail concentration for Lipschitz functions of a standard Gaussian vector. -/
theorem product_standardGaussian_lower_tail
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  convert product_standardGaussian_upper_tail ( fun x => -F x ) L t hL ht ( hLip.neg ) using 2 ; simp +decide [ sub_eq_neg_add ];
  rw [ MeasureTheory.integral_neg ] ; ext ; simp +decide [ add_comm ]

theorem abs_gt_iff_pos_or_neg {a t : ℝ} : |a| > t ↔ a > t ∨ -a > t := by
  rw [ abs_eq_max_neg, gt_iff_lt, gt_iff_lt, gt_iff_lt, lt_max_iff, lt_neg ]

/-- Two-sided Gaussian concentration on a finite-dimensional Euclidean space. -/
theorem euclidean_lipschitz_gaussian_concentration
    {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasureOnEuclidean ι
        {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  have hexp : (0 : ℝ) ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := Real.exp_nonneg _
  have hsubset :
      {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t} ⊆
        {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ∪
          {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} := by
    intro x hx
    rcases abs_gt_iff_pos_or_neg.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [neg_sub] using h)
  calc
    standardGaussianMeasureOnEuclidean ι
          {x | |F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι| > t}
        ≤ standardGaussianMeasureOnEuclidean ι
            ({x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} ∪
              {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t}) :=
          measure_mono hsubset
    _ ≤ standardGaussianMeasureOnEuclidean ι
            {x | F x - ∫ y, F y ∂standardGaussianMeasureOnEuclidean ι > t} +
          standardGaussianMeasureOnEuclidean ι
            {x | (∫ y, F y ∂standardGaussianMeasureOnEuclidean ι) - F x > t} :=
          measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) +
          ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
          add_le_add (product_standardGaussian_upper_tail F L t hL ht hLip)
            (product_standardGaussian_lower_tail F L t hL ht hLip)
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
          rw [← ENNReal.ofReal_add hexp hexp]; congr 1; ring

/-- Gaussian concentration for the product standard Gaussian on the SYK coupling space. -/
theorem gaussian_lipschitz_concentration
    (N q : ℕ) (F : CouplingSpace N q → ℝ) (L t : ℝ)
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal F) :
    standardGaussianMeasure N q
        {x | |F x - ∫ y, F y ∂standardGaussianMeasure N q| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  simpa using
    euclidean_lipschitz_gaussian_concentration
      (ι := ({s : Finset (Fin N) // s.card = q})) F L t hL ht hLip

end SYK

