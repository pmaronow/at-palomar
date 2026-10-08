module

/-
# One-dimensional Gaussian concentration

New work for the ParisiFormula project (not vendored).

RSAT proves the Herbst sub-Gaussian bound for Lipschitz functions of a Gaussian vector,
`SYK.product_standardGaussian_mgf_le` (note: RSAT's concentration file is in the `SYK`
namespace, not `SpinGlass`), but states it on

  `standardGaussianMeasureOnEuclidean ι = (Measure.pi fun _ : ι => gaussianReal 0 1).map (WithLp.toLp 2)`.

`Targets.parisiStep` smooths against `gaussianReal 0 1` on `ℝ`, so we need the same bound
there.  This file transports it along the singleton index `Unit`.

## Why the sharp form is needed

Target 2b must control a change of the *variance* `v` in `T_{m,v}`.  Via the semigroup law
(`SpinGlass.Parisi.T_add`) that reduces to bounding `|T_{m,w} A - A|` for small `w`, i.e.

  `(1/m) log 𝔼[exp (m g)]`,  `g = A (x + √w Z) - A x`,  `|g| ≤ L √w |Z|`.

The naive bound `𝔼[exp (a|Z|)] ≤ 2 exp (a²/2)` contributes `(log 2)/m`, which **blows up as
`m → 0`** — fatal, since an RSB scheme may have arbitrarily small `m_p`.  The sub-Gaussian
form `𝔼[exp (a (|Z| - 𝔼|Z|))] ≤ exp (a²/2)` has `(1/m) log (…) = O(1)` instead, which is
what keeps the eventual Lipschitz constant uniform in `k`.
-/
public import ParisiFormula.GaussianCosh
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

open MeasureTheory ProbabilityTheory Real

-- RSAT's concentration results live in the `SYK` namespace, not `SpinGlass`.
open SYK

open scoped BigOperators NNReal

namespace SpinGlass

/-! ## 1. Transporting integrals along the singleton index -/

/-- The measure-preserving identification `(Unit → ℝ) ≃ᵐ ℝ` for the Gaussian. -/
theorem measurePreserving_funUnique_gaussian :
    MeasurePreserving (MeasurableEquiv.funUnique Unit ℝ)
      (Measure.pi fun _ : Unit => gaussianReal 0 1) (gaussianReal 0 1) :=
  measurePreserving_funUnique (gaussianReal 0 1) Unit

/-- `WithLp.toLp 2` is measurable: it is the inverse of a continuous linear equivalence.
(RSAT uses the same identification, e.g. in `gaussian_concentration.lean`.) -/
theorem measurable_toLp_unit :
    Measurable (WithLp.toLp 2 : (Unit → ℝ) → EuclideanSpace ℝ Unit) := by
  rw [show (WithLp.toLp 2 : (Unit → ℝ) → EuclideanSpace ℝ Unit)
        = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Unit => ℝ)).symm from rfl]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Unit => ℝ)).symm.continuous.measurable

/--
Integrals against the one-dimensional Euclidean Gaussian are integrals against
`gaussianReal 0 1`.
-/
theorem integral_standardGaussianOnEuclidean_unit (G : EuclideanSpace ℝ Unit → ℝ)
    (hG : Measurable G) :
    (∫ x, G x ∂(standardGaussianMeasureOnEuclidean Unit))
      = ∫ z : ℝ, G (WithLp.toLp 2 (fun _ : Unit => z)) ∂(gaussianReal 0 1) := by
  classical
  rw [standardGaussianMeasureOnEuclidean, integral_map]
  · -- now an integral over `Measure.pi fun _ : Unit => gaussianReal 0 1`
    have hfun : ∀ y : Unit → ℝ,
        G (WithLp.toLp 2 y)
          = (fun z : ℝ => G (WithLp.toLp 2 (fun _ : Unit => z)))
              (MeasurableEquiv.funUnique Unit ℝ y) := by
      intro y
      have : (fun _ : Unit => y default) = y := by
        funext u
        simp [Unique.eq_default u]
      simp [MeasurableEquiv.funUnique, this]
    calc (∫ y, G (WithLp.toLp 2 y) ∂(Measure.pi fun _ : Unit => gaussianReal 0 1))
        = ∫ y, (fun z : ℝ => G (WithLp.toLp 2 (fun _ : Unit => z)))
            (MeasurableEquiv.funUnique Unit ℝ y)
            ∂(Measure.pi fun _ : Unit => gaussianReal 0 1) := by
          exact integral_congr_ae (Filter.Eventually.of_forall hfun)
      _ = ∫ z : ℝ, G (WithLp.toLp 2 (fun _ : Unit => z)) ∂(gaussianReal 0 1) :=
          measurePreserving_funUnique_gaussian.integral_comp'
            (fun z : ℝ => G (WithLp.toLp 2 (fun _ : Unit => z)))
  · exact measurable_toLp_unit.aemeasurable
  · exact hG.aestronglyMeasurable

/-! ## 2. Lipschitz functions on the one-dimensional Euclidean space -/

/-- `dist` on `EuclideanSpace ℝ Unit` is the absolute difference of the single coordinate. -/
theorem dist_euclidean_unit (x y : EuclideanSpace ℝ Unit) :
    dist x y = |x default - y default| := by
  rw [EuclideanSpace.dist_eq]
  rw [Finset.sum_unique_nonempty] <;> simp [Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- A Lipschitz `f : ℝ → ℝ` lifts to a Lipschitz function on `EuclideanSpace ℝ Unit`. -/
theorem lipschitzWith_euclidean_unit {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x : EuclideanSpace ℝ Unit => f (x default)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_euclidean_unit x y, Real.dist_eq]
  simpa [Real.dist_eq] using hf.dist_le_mul (x default) (y default)

/-! ## 3. The one-dimensional Herbst bound -/

/--
**Sub-Gaussian moment generating function for a Lipschitz function of a standard Gaussian**,
in one dimension:

  `𝔼[exp (t (f Z - 𝔼 f Z))] ≤ exp (L² t² / 2)`.

Transported from RSAT's `product_standardGaussian_mgf_le` along the singleton index.
-/
theorem gaussianReal_mgf_le_of_lipschitz (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal f) (hmeas : Measurable f) (t : ℝ) :
    mgf (fun z : ℝ => f z - ∫ y : ℝ, f y ∂(gaussianReal 0 1)) (gaussianReal 0 1) t
      ≤ Real.exp (L ^ 2 * t ^ 2 / 2) := by
  classical
  set F : EuclideanSpace ℝ Unit → ℝ := fun x => f (x default) with hFdef
  have hFmeas : Measurable F := hmeas.comp (by fun_prop)
  have hFlip : LipschitzWith L.toNNReal F := lipschitzWith_euclidean_unit hLip
  -- the two means agree
  have hmean : (∫ x, F x ∂(standardGaussianMeasureOnEuclidean Unit))
      = ∫ y : ℝ, f y ∂(gaussianReal 0 1) := by
    rw [integral_standardGaussianOnEuclidean_unit F hFmeas]
  -- and so do the two mgfs
  have hmgf : mgf (fun x => F x - ∫ y, F y ∂(standardGaussianMeasureOnEuclidean Unit))
      (standardGaussianMeasureOnEuclidean Unit) t
      = mgf (fun z : ℝ => f z - ∫ y : ℝ, f y ∂(gaussianReal 0 1)) (gaussianReal 0 1) t := by
    simp only [mgf]
    have hmeasG : Measurable
        (fun x : EuclideanSpace ℝ Unit =>
          Real.exp (t * (F x - ∫ y, F y ∂(standardGaussianMeasureOnEuclidean Unit)))) :=
      Real.continuous_exp.measurable.comp ((hFmeas.sub measurable_const).const_mul t)
    rw [integral_standardGaussianOnEuclidean_unit _ hmeasG, hmean]
  rw [← hmgf]
  exact product_standardGaussian_mgf_le F L hL hFlip t

/-! ## 4. The `m → 0` sandwich

Talagrand's admissible sequences (1.6) allow `m_0 = 0`, and `Targets.parisiStep` is defined
by a *separate* `m = 0` branch (`∫ A dγ`).  Any statement about the behaviour of the Parisi
functional in its parameters must therefore control the gap between the two branches.

The gap is one-sided and **linear in `m`**: for `f` `L`-Lipschitz and `m > 0`,

  `𝔼[f] ≤ (1/m) log 𝔼[exp (m f)] ≤ 𝔼[f] + m L² / 2`.

The lower bound is Jensen (`integral_log_le_log_integral`); the upper bound is the Herbst
sub-Gaussian estimate (`gaussianReal_mgf_le_of_lipschitz`).  Note that the constant involves
only the Lipschitz constant `L` — *not* `sup |f|`, which is infinite here — and is therefore
uniform over all translates of `f`.  That uniformity is what makes the estimate usable inside
the Parisi recursion, where it must hold at every `x` simultaneously.
-/

/-- **Jensen half.**  `𝔼[f] ≤ (1/m) log 𝔼[exp (m f)]` for `m > 0`. -/
theorem integral_le_inv_mul_log_integral_exp {f : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (hint : Integrable f (gaussianReal 0 1))
    (hexp : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1)) :
    (∫ z, f z ∂(gaussianReal 0 1))
      ≤ (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1)) := by
  have hlogint : Integrable (fun z => Real.log (Real.exp (m * f z))) (gaussianReal 0 1) := by
    refine (hint.const_mul m).congr ?_
    filter_upwards with z
    rw [Real.log_exp]
  have hJ := integral_log_le_log_integral (μ := gaussianReal 0 1)
      (W := fun z => Real.exp (m * f z)) (fun z => Real.exp_pos _) hexp hlogint
  have hLHS : (∫ z, Real.log (Real.exp (m * f z)) ∂(gaussianReal 0 1))
      = m * ∫ z, f z ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show Real.log (Real.exp (m * f z)) = m * f z
    rw [Real.log_exp]
  rw [hLHS] at hJ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
  exact hJ

/-- **Herbst half.**  `(1/m) log 𝔼[exp (m f)] ≤ 𝔼[f] + m L² / 2` for `f` `L`-Lipschitz. -/
theorem inv_mul_log_integral_exp_le {f : ℝ → ℝ} {L m : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal f) (hmeas : Measurable f)
    (hexp : Integrable (fun z => Real.exp (m * f z)) (gaussianReal 0 1)) :
    (1 / m) * Real.log (∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1))
      ≤ (∫ z, f z ∂(gaussianReal 0 1)) + m * L ^ 2 / 2 := by
  set M : ℝ := ∫ z, f z ∂(gaussianReal 0 1) with hM
  set I : ℝ := ∫ z, Real.exp (m * f z) ∂(gaussianReal 0 1) with hI
  have hIpos : 0 < I := by rw [hI]; exact integral_exp_pos hexp
  have hherbst := gaussianReal_mgf_le_of_lipschitz f L hL hLip hmeas m
  rw [← hM] at hherbst
  have hmgf : mgf (fun z : ℝ => f z - M) (gaussianReal 0 1) m = I * Real.exp (-(m * M)) := by
    have hcongr : (∫ z, Real.exp (m * (f z - M)) ∂(gaussianReal 0 1))
        = ∫ z, Real.exp (m * f z) * Real.exp (-(m * M)) ∂(gaussianReal 0 1) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by
        show Real.exp (m * (f z - M)) = Real.exp (m * f z) * Real.exp (-(m * M))
        rw [← Real.exp_add]; ring_nf)
    calc mgf (fun z : ℝ => f z - M) (gaussianReal 0 1) m
        = ∫ z, Real.exp (m * (f z - M)) ∂(gaussianReal 0 1) := rfl
      _ = ∫ z, Real.exp (m * f z) * Real.exp (-(m * M)) ∂(gaussianReal 0 1) := hcongr
      _ = I * Real.exp (-(m * M)) := by rw [integral_mul_const, ← hI]
  rw [hmgf] at hherbst
  -- `I ≤ exp (L² m² / 2 + m M)`
  have h1 : I ≤ Real.exp (L ^ 2 * m ^ 2 / 2 + m * M) := by
    have hmul := mul_le_mul_of_nonneg_right hherbst (Real.exp_pos (m * M)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
      ← Real.exp_add] at hmul
    exact hmul
  have hlogI : Real.log I ≤ L ^ 2 * m ^ 2 / 2 + m * M :=
    (Real.log_le_iff_le_exp hIpos).2 h1
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hm]
  calc Real.log I ≤ L ^ 2 * m ^ 2 / 2 + m * M := hlogI
    _ = (M + m * L ^ 2 / 2) * m := by ring

end SpinGlass
