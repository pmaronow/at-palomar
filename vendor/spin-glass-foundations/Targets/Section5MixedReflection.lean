module

public import Targets.Section5MixedCascade
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-!
# Exact replica reflection and the dual mixed strictness mechanism

Reflection of the second replica interchanges ordinary and opposite shared
Gaussian fields. Independent fields are invariant under the genuine Gaussian
change of variables. This transports the proved opposite-before-shared
strictness theorem to the dual order, without a new analytic strictness proof.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

def Section5GaussianMode.reflectSecond : Section5GaussianMode → Section5GaussianMode
  | .independent => .independent
  | .shared => .opposite
  | .opposite => .shared

@[simp] theorem Section5GaussianMode.reflectSecond_scalarMass (mode : Section5GaussianMode)
    (m : ℝ) : mode.reflectSecond.scalarMass m = mode.scalarMass m := by cases mode <;> rfl

private theorem scalarStep_reflectSecond (m a b : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    AT.gtScalarStep m a b (fun x y => F x (-y)) x y =
      AT.gtScalarStep m a (-b) F x (-y) := by
  simp only [AT.gtScalarStep, neg_add, neg_mul]

private theorem scalarStep_neg_coefficients (m a b : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) :
    AT.gtScalarStep m (-a) (-b) F x y = AT.gtScalarStep m a b F x y := by
  have hp : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have H (g : ℝ → ℝ) :
      (∫ z, g (F (x + -a * z) (y + -b * z)) ∂gaussianReal 0 1) =
        ∫ z, g (F (x + a * z) (y + b * z)) ∂gaussianReal 0 1 := by
    simpa only [Function.comp_apply, mul_neg, neg_mul] using
      hp.integral_comp measurableEmbedding_neg
        (fun z => g (F (x + a * z) (y + b * z)))
  by_cases hm : m = 0
  · simpa only [AT.gtScalarStep, AT.standardGaussianExpectation, if_pos hm, id_eq] using H id
  · simp only [AT.gtScalarStep, AT.standardGaussianExpectation, if_neg hm]
    rw [H (fun z => Real.exp (m * z))]

/-- Exact second-replica reflection of the mixed zero-lambda recursion.
There are no integrability, mass-positivity or variance-positivity assumptions:
the independent sign change is a measure-preserving measurable equivalence. -/
theorem mixedScalarCascade_reflectSecond_zero {P : Type*}
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (j : ℕ) (p : P) (x y : ℝ) :
    mixedScalarCascade mode m v j p 0 (x, y) =
      mixedScalarCascade (fun i => (mode i).reflectSecond) m v j p 0 (x, -y) := by
  induction j generalizing x y with
  | zero => simp only [mixedScalarCascade, coupledSite_zero, Real.cosh_neg]
  | succ j ih =>
    let F := fun x y => mixedScalarCascade (fun i => (mode i).reflectSecond) m v j p 0 (x, y)
    have he : (fun x y => mixedScalarCascade mode m v j p 0 (x, y)) =
        (fun x y => F x (-y)) := funext fun x => funext fun y => ih x y
    cases hmj : mode j with
    | shared =>
      simp only [mixedScalarCascade, hmj, Section5GaussianMode.reflectSecond]
      simp only [finiteStep_eq_gtScalarStep]
      change AT.gtScalarStep (m j) (Real.sqrt (v j p)) (Real.sqrt (v j p))
        (fun x y => mixedScalarCascade mode m v j p 0 (x, y)) x y =
        AT.gtScalarStep (m j) (Real.sqrt (v j p)) (-Real.sqrt (v j p)) F x (-y)
      rw [he]
      exact scalarStep_reflectSecond _ _ _ _ _ _
    | opposite =>
      simp only [mixedScalarCascade, hmj, Section5GaussianMode.reflectSecond]
      simp only [finiteStep_eq_gtScalarStep]
      change AT.gtScalarStep (m j) (Real.sqrt (v j p)) (-Real.sqrt (v j p))
        (fun x y => mixedScalarCascade mode m v j p 0 (x, y)) x y =
        AT.gtScalarStep (m j) (Real.sqrt (v j p)) (Real.sqrt (v j p)) F x (-y)
      rw [he]
      simpa only [neg_neg] using scalarStep_reflectSecond (m j) (Real.sqrt (v j p))
        (-Real.sqrt (v j p)) F x y
    | independent =>
      simp only [mixedScalarCascade, hmj, Section5GaussianMode.reflectSecond]
      simp only [finiteStep_eq_gtScalarStep]
      change AT.gtScalarStep (m j) (Real.sqrt (v j p)) 0
        (fun x y => AT.gtScalarStep (m j) 0 (Real.sqrt (v j p))
          (fun x y => mixedScalarCascade mode m v j p 0 (x, y)) x y) x y =
        AT.gtScalarStep (m j) (Real.sqrt (v j p)) 0
          (fun x y => AT.gtScalarStep (m j) 0 (Real.sqrt (v j p)) F x y) x (-y)
      rw [he]
      have hi : (fun x y => AT.gtScalarStep (m j) 0 (Real.sqrt (v j p))
          (fun x y => F x (-y)) x y) =
          (fun x y => AT.gtScalarStep (m j) 0 (Real.sqrt (v j p)) F x (-y)) := by
        funext x y
        rw [scalarStep_reflectSecond]
        simpa only [neg_zero] using scalarStep_neg_coefficients (m j) 0
          (Real.sqrt (v j p)) F x (-y)
      rw [hi]
      simpa only [neg_zero] using scalarStep_reflectSecond (m j) (Real.sqrt (v j p)) 0
        (fun x y => AT.gtScalarStep (m j) 0 (Real.sqrt (v j p)) F x y) x y

@[simp] theorem mixedScalarReference_reflectSecond {P : Type*}
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (j : ℕ) (p : P) :
    mixedScalarReference (fun i => (mode i).reflectSecond) m v j p =
      mixedScalarReference mode m v j p := by
  simp only [mixedScalarReference, Section5GaussianMode.reflectSecond_scalarMass]

/-- A positive ordinary shared step, followed outwards by a positive opposite
variance, produces strictness everywhere. The outer opposite mass may be zero. -/
theorem mixedScalarCascade_lt_of_shared_before_opposite
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, Continuous (v j))
    (hscalar : ∀ j, (mode j).scalarMass (m j) ∈ Set.Icc 0 1)
    {c b j : ℕ} (hcb : c < b) (hbj : b < j) (p : P)
    (hc : mode c = .shared) (hmc : 0 < m c) (hvc : 0 < v c p)
    (hb : mode b = .opposite) (hvb : 0 < v b p) (x y : ℝ) :
    mixedScalarCascade mode m v j p 0 (x, y) <
      mixedScalarReference mode m v j p x + mixedScalarReference mode m v j p y := by
  have H := mixedScalarCascade_lt_of_opposite_before_shared
    (fun i => (mode i).reflectSecond) m v hm hv
    (by simpa only [Section5GaussianMode.reflectSecond_scalarMass] using hscalar)
    hcb hbj p (by simp [hc, Section5GaussianMode.reflectSecond]) hmc hvc
    (by simp [hb, Section5GaussianMode.reflectSecond]) hvb x (-y)
  rw [← mixedScalarCascade_reflectSecond_zero] at H
  simpa only [mixedScalarReference_reflectSecond, mixedScalarReference,
    scalarFieldCascade_even _ _ _ y] using H

end SpinGlass.Targets
