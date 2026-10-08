module

public import Targets.Section4ZeroOverlap
public import Targets.ParisiStrictConvexity
public import Targets.Section5SignedCascadeFlip
public import Targets.CoupledSharedInsertion

@[expose] public section

/-!
# Actual overlap reflection at zero first overlap

An arbitrary external field cannot be reflected away. Here original
fixed-level minimality first forces the field to be zero: the initial scalar
slope vanishes, while that slope is strictly increasing and the scalar
potential is even. Only then do we reflect the second physical replica.
The sole shared outer variance is zero and is deleted exactly.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Evenness of the actual scalar potential forces its genuine slope to
vanish at the origin. No spatial or Gaussian variance is assumed positive. -/
theorem parisiFDeriv_zero_field {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    parisiFDeriv s β j 0 = 0 := by
  have H := (parisiF_C2_props s β j).1.1 0
  have H0 : HasDerivAt (parisiF s β j) (parisiFDeriv s β j 0) (-(0 : ℝ)) := by
    simpa only [neg_zero] using H
  have Hneg := H0.comp 0 (hasDerivAt_id (0 : ℝ)).neg
  have he : (fun x => parisiF s β j (-x)) = parisiF s β j :=
    funext (parisiF_even s β j)
  simp only [Function.comp_def, he, mul_neg, mul_one] at Hneg
  have hh := H.unique Hneg
  linarith

/-- Original minimality at zero first overlap forces zero external field.
This uses actual stationarity, not an additional symmetry assumption. -/
theorem field_eq_zero_of_initial_overlap_zero_min {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1)
    (hgap : s.q 1 < s.q 2)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    h = 0 := by
  apply (strictMono_parisiFDeriv s β (k + 1)).injective
  rw [parisiFDeriv_initial_zero_of_min s β h hβ hq hm (Or.inl hgap) hmin,
    parisiFDeriv_zero_field]

/-- At zero external field the actual constrained terminal reflects to the
opposite overlap, with the second Gaussian field also reflected. -/
theorem constrainedBase_flip_zero_field {n : ℕ} (U : EnergySpace n)
    (hU : ∀ σ, U (configFlip n σ) = U σ) (t u : ℝ) (x y : Fin n → ℝ) :
    constrainedBase n U 0 t u x y = constrainedBase n U 0 t (-u) x (-y) := by
  have hs : ∀ σ, (Real.sqrt t • U) (configFlip n σ) = (Real.sqrt t • U) σ := by
    intro σ
    simp only [PiLp.smul_apply, smul_eq_mul, hU]
  rw [constrainedBase_eq_pairFieldBase, constrainedPairFieldBase_flip _ hs,
    constrainedBase_eq_pairFieldBase]
  simp only [add_zero, Pi.neg_apply, mul_neg]
  rfl

/-- The initial outer shared level is exactly the identity when `q₁=0`. -/
theorem coupledCascade_initial_zero_drop {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (hq : s.q 1 = 0) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledCascade n s β (k + 1) F (k + 2) =
      coupledCascade n s β (k + 1) F (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, coupledCascade]
  simp only [lt_self_iff_false, if_false, Nat.sub_self,
    show k + 2 - (k + 1) = 1 by omega, hq, s.q_zero, sub_self, mul_zero,
    sharedStepPi_variance_zero]

/-- Exact physical cascade reflection after deleting the zero shared level.
No sign, attainability or system-size restriction is needed for this identity. -/
theorem constrainedCascade_initial_zero_reflection {n k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hq : s.q 1 = 0) (U : EnergySpace n)
    (hU : ∀ σ, U (configFlip n σ) = U σ) (t u : ℝ) :
    coupledCascade n s β (k + 1) (constrainedBase n U 0 t u) (k + 2) 0 0 =
      coupledCascade n s β (k + 1) (constrainedBase n U 0 t (-u)) (k + 2) 0 0 := by
  rw [coupledCascade_initial_zero_drop s β hq, coupledCascade_initial_zero_drop s β hq,
    coupledCascade_eq_fieldCascade, coupledCascade_eq_fieldCascade]
  have H := coupledFieldCascade_independent_flip_second
    (fun j => if j < k + 1 then s.m (k + 1 - j) else s.m (k + 1 - j) / 2)
    (fun j => β ^ 2 * (s.q (k + 2 - j) - s.q (k + 1 - j))) (d := k + 1)
    (j := k + 1) le_rfl (constrainedBase_flip_zero_field U hU t u) 0 0
  simpa only [neg_zero] using H

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- At zero first overlap and zero field the original constrained free
energy, not an auxiliary endpoint, is even in its overlap. -/
theorem constrainedPhi_initial_zero_reflection {n k : ℕ} (s : RSBScheme k)
    (β : ℝ) (sk : SKDisorder (Ω := Ω) n β 0) (hq : s.q 1 = 0) (t u : ℝ) :
    constrainedPhi n s β 0 sk.U (k + 1) t u =
      constrainedPhi n s β 0 sk.U (k + 1) t (-u) := by
  unfold constrainedPhi
  congr 1
  apply integral_congr_ae
  filter_upwards [skDisorder_even_ae β 0 sk] with ω hω
  exact constrainedCascade_initial_zero_reflection s β hq (sk.U ω) hω t u

/-- The physical reflection follows from original fixed-level minimality;
zero external field is a proved consequence, not a new target hypothesis. -/
theorem constrainedPhi_initial_zero_reflection_of_min {n k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h)
    (hβ : β ≠ 0) (hq : s.q 1 = 0) (hm : s.m 0 < s.m 1)
    (hgap : s.q 1 < s.q 2)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h)
    (t u : ℝ) :
    constrainedPhi n s β h sk.U (k + 1) t u =
      constrainedPhi n s β h sk.U (k + 1) t (-u) := by
  obtain rfl := field_eq_zero_of_initial_overlap_zero_min s β h hβ hq hm hgap hmin
  exact constrainedPhi_initial_zero_reflection s β sk hq t u

end Disorder

end SpinGlass.Targets
