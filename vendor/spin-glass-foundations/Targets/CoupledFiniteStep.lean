module

/-
# Finite paired-field recursions, reusing the RSAT Gaussian framework

The masses and the two Gaussian coefficients are specified independently at
each step. This permits inserted levels and signed shared fields in Talagrand
Sections 3--5. All analytic propagation is imported from `GTFrame`, and all
site tensorization from `AT.gtVectorStep_sum`; no new Gaussian calculus is used.
The positive-overlap left-interval instance and its endpoints are supplied in
`TalagrandSecondInterpolation`; Theorem 3.1's derivative bound remains open.
-/
public import Targets.CoupledLambda
public import Lemmas.GuerraTalagrand.Bound.FiniteStep

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The existing shared step is precisely RSAT's general vector step at half mass. -/
theorem sharedStepPi_eq_gtVectorStep (n : ℕ) (m v : ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    sharedStepPi n m v A x y =
      AT.gtVectorStep n (m / 2) (Real.sqrt v) (Real.sqrt v) A x y := by
  simp only [sharedStepPi, parisiStepPi, AT.gtVectorStep,
    GeneralizedLatala.gaussianProduct, Pi.add_def, Pi.zero_apply, zero_add]

/-- Two independent fields are two RSAT vector steps of the same mass.
Fubini is reused from the existing interacting-cascade lemma. -/
theorem independentStepPi_eq_gtVectorSteps {n : ℕ} (m v : ℝ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (x y : Fin n → ℝ) :
    independentStepPi n m v A x y =
      AT.gtVectorStep n m (Real.sqrt v) 0
        (AT.gtVectorStep n m 0 (Real.sqrt v) A) x y := by
  rw [independentStepPi_eq_nested m v hA]
  simp only [parisiStepPi, AT.gtVectorStep, GeneralizedLatala.gaussianProduct, zero_mul, add_zero]

variable {P : Type*}

/-- The single-site recursion, using RSAT's zero/positive-mass transform verbatim. -/
noncomputable def pairedScalarCascade (m : ℕ → ℝ) (a b : ℕ → P → ℝ) :
    ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ ℓ x => coupledSite ℓ x.1 x.2
  | j + 1 => GTFrame.finiteStep (gaussianReal 0 1) (m j) (a j) (b j)
      (pairedScalarCascade m a b j)

/-- Its lambda derivative is the existing recursively tilted derivative. -/
noncomputable def pairedScalarCascadeD (m : ℕ → ℝ) (a b : ℕ → P → ℝ) :
    ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ ℓ x => GTFrame.fLbaseD ℓ x
  | j + 1 => GTFrame.finiteStepD (gaussianReal 0 1) (m j) (a j) (b j)
      (pairedScalarCascade m a b j) (pairedScalarCascadeD m a b j)

/-- The N-site recursion, using RSAT's vector step without changing its measure. -/
noncomputable def pairedVectorCascade (n : ℕ) (m : ℕ → ℝ) (a b : ℕ → P → ℝ) :
    ℕ → P → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => fun _ ℓ x y => ∑ i, coupledSite ℓ (x i) (y i)
  | j + 1 => fun p ℓ => AT.gtVectorStep n (m j) (a j p) (b j p)
      (pairedVectorCascade n m a b j p ℓ)

theorem pairedScalarCascade_succ (m : ℕ → ℝ) (a b : ℕ → P → ℝ)
    (j : ℕ) (p : P) (ℓ x y : ℝ) :
    pairedScalarCascade m a b (j + 1) p ℓ (x, y) =
      AT.gtScalarStep (m j) (a j p) (b j p)
        (fun x y => pairedScalarCascade m a b j p ℓ (x, y)) x y := by
  simp only [pairedScalarCascade, GTFrame.finiteStep, AT.gtScalarStep]
  split_ifs <;> rfl

variable [TopologicalSpace P] [FirstCountableTopology P]

/-- Reuse RSAT's regularity theorem at every finite level, including mass zero.
This packages joint continuity, the actual lambda derivative, unit spatial
Lipschitz bounds, and a unit lambda-derivative bound. No strictness is needed. -/
theorem pairedScalarCascade_good (m : ℕ → ℝ) (a b : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (ha : ∀ j, Continuous (a j)) (hb : ∀ j, Continuous (b j)) (j : ℕ) :
    GTFrame.GoodFam (pairedScalarCascade m a b j) (pairedScalarCascadeD m a b j) := by
  induction j with
  | zero =>
    simpa only [pairedScalarCascade, pairedScalarCascadeD, coupledSite_eq_gtTerminal,
      GTFrame.fLbase] using (GTFrame.goodFam_fLbase (P := P))
  | succ j ih =>
    simp only [pairedScalarCascade, pairedScalarCascadeD, GTFrame.finiteStep, GTFrame.finiteStepD]
    by_cases hj : m j = 0
    · simp only [if_pos hj]
      exact GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) ih (ha j) (hb j)
    · simp only [if_neg hj]
      exact GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) ih
        (lt_of_le_of_ne (hm j) (Ne.symm hj)) (ha j) (hb j)

/-- Site tensorization for any finite sequence of signed paired increments.
All integrability and positivity hypotheses of the imported theorem are proved. -/
theorem pairedVectorCascade_eq_sum (n : ℕ) (m : ℕ → ℝ) (a b : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (ha : ∀ j, Continuous (a j)) (hb : ∀ j, Continuous (b j))
    (j : ℕ) (p : P) (ℓ : ℝ) (x y : Fin n → ℝ) :
    pairedVectorCascade n m a b j p ℓ x y =
      ∑ i, pairedScalarCascade m a b j p ℓ (x i, y i) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have hgood := pairedScalarCascade_good m a b hm ha hb j
    have he : pairedVectorCascade n m a b j p ℓ =
        fun x y => ∑ i, pairedScalarCascade m a b j p ℓ (x i, y i) :=
      funext fun x => funext (ih x)
    simp only [pairedVectorCascade]
    rw [he]
    have H := AT.gtVectorStep_sum (m j) (a j p) (b j p)
      (fun _ x y => pairedScalarCascade m a b j p ℓ (x, y)) x y
      (fun i => hgood.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
        p ℓ (a j p) (b j p) (x i, y i))
      (fun _ i => GTFrame.integral_expShift_pos (GTFrame.expMoments_gaussianReal 0 1)
        hgood (hm j) p ℓ (a j p) (b j p) (x i, y i))
    simpa only [pairedScalarCascade_succ] using H

/-- At identical fields, the N-site endpoint is N times one scalar recursion. -/
theorem pairedVectorCascade_const (n : ℕ) (m : ℕ → ℝ) (a b : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (ha : ∀ j, Continuous (a j)) (hb : ∀ j, Continuous (b j))
    (j : ℕ) (p : P) (ℓ x y : ℝ) :
    pairedVectorCascade n m a b j p ℓ (fun _ => x) (fun _ => y) =
      n * pairedScalarCascade m a b j p ℓ (x, y) := by
  rw [pairedVectorCascade_eq_sum n m a b hm ha hb]
  simp

/-- Differentiation in lambda through the whole finite one-site recursion. -/
theorem hasDerivAt_pairedScalarCascade (m : ℕ → ℝ) (a b : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (ha : ∀ j, Continuous (a j)) (hb : ∀ j, Continuous (b j))
    (j : ℕ) (p : P) (ℓ : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun z => pairedScalarCascade m a b j p z x)
      (pairedScalarCascadeD m a b j p ℓ x) ℓ :=
  (pairedScalarCascade_good m a b hm ha hb j).hasDeriv p ℓ x

end SpinGlass.Targets
