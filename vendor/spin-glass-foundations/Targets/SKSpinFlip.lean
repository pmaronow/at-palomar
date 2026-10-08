module

public import Targets.TalagrandSecondInterpolation

@[expose] public section

/-!
# Global spin reflection for exact-covariance SK disorder

Flipping every spin reverses overlap and the associated physical field.
The SK Hamiltonian is even almost surely, as follows from its exact covariance,
not from an extra symmetry hypothesis. The second replica may therefore be
reflected while its external field is reflected explicitly as well.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- The global spin reflection, as an involutive finite equivalence. -/
def configFlip (n : ℕ) : Config n ≃ Config n where
  toFun σ i := !(σ i)
  invFun σ i := !(σ i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

@[simp] theorem configFlip_configFlip (n : ℕ) (σ : Config n) :
    configFlip n (configFlip n σ) = σ := by
  funext i
  simp [configFlip]

@[simp] theorem spin_configFlip (n : ℕ) (σ : Config n) (i : Fin n) :
    spin n (configFlip n σ) i = -spin n σ i := by
  cases hσ : σ i <;> simp [spin, configFlip, hσ]

@[simp] theorem overlap_configFlip_right (n : ℕ) (σ τ : Config n) :
    overlap n σ (configFlip n τ) = -overlap n σ τ := by
  simp [overlap, spin_configFlip, Finset.sum_neg_distrib]

@[simp] theorem overlap_configFlip_left (n : ℕ) (σ τ : Config n) :
    overlap n (configFlip n σ) τ = -overlap n σ τ := by
  simp [overlap, spin_configFlip, Finset.sum_neg_distrib]

/-- An even Hamiltonian permits a second-replica reflection only with the
second physical field reflected too. This includes unattainable overlaps. -/
theorem constrainedPairFieldBase_flip {n : ℕ} (U : EnergySpace n)
    (hU : ∀ σ, U (configFlip n σ) = U σ) (u : ℝ) (x y : Fin n → ℝ) :
    constrainedPairFieldBase n U u x y =
      constrainedPairFieldBase n U (-u) x (-y) := by
  unfold constrainedPairFieldBase
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [← (configFlip n).sum_comp]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [overlap_configFlip_right, hU, spin_configFlip, Pi.neg_apply, neg_mul,
    mul_neg, neg_eq_iff_eq_neg]

/-- Attainability is preserved by reflecting the second replica. -/
theorem attainableOverlap_neg {n : ℕ} {u : ℝ}
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    ∃ σ τ : Config n, overlap n σ τ = -u := by
  obtain ⟨σ, τ, hστ⟩ := hu
  exact ⟨σ, configFlip n τ, by simp only [overlap_configFlip_right, hστ]⟩

/-- The constrained finite state space is nonempty at the reflected overlap. -/
theorem constrainedPair_nonempty_neg {n : ℕ} (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] : Nonempty (AT.ConstrainedPair n (-u)) := by
  obtain ⟨p⟩ := ‹Nonempty (AT.ConstrainedPair n u)›
  exact ⟨⟨(p.1.1, configFlip n p.1.2), by simp only [overlap_configFlip_right, p.2]⟩⟩

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Every positive-variance spectral direction of exact SK disorder is even. -/
theorem skDisorder_basis_even_of_variance_ne_zero {n : ℕ} (β h : ℝ)
    (sk : SKDisorder (Ω := Ω) n β h) (i : sk.hU.ι) (hi : sk.hU.τ i ≠ 0)
    (σ : Config n) : sk.hU.w i (configFlip n σ) = sk.hU.w i σ := by
  have Hff := sk_covariance_spectral_sum β h sk (configFlip n σ) (configFlip n σ)
  have Hfs := sk_covariance_spectral_sum β h sk (configFlip n σ) σ
  have Hss := sk_covariance_spectral_sum β h sk σ σ
  simp only [sk_cov_kernel, overlap_configFlip_left, overlap_configFlip_right,
    neg_neg, neg_sq] at Hff Hfs Hss
  have Hsum : (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
      (sk.hU.w j (configFlip n σ) - sk.hU.w j σ) ^ 2) = 0 := by
    calc
      _ = (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
          (sk.hU.w j (configFlip n σ) * sk.hU.w j (configFlip n σ))) -
        2 * (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) *
          (sk.hU.w j (configFlip n σ) * sk.hU.w j σ)) +
        (∑ j : sk.hU.ι, (sk.hU.τ j : ℝ) * (sk.hU.w j σ * sk.hU.w j σ)) := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = 0 := by rw [Hff, Hfs, Hss]; ring
  have Hterm : (sk.hU.τ i : ℝ) * (sk.hU.w i (configFlip n σ) - sk.hU.w i σ) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (sk.hU.τ j).coe_nonneg (sq_nonneg _))).mp Hsum i (Finset.mem_univ i)
  have ht : (sk.hU.τ i : ℝ) ≠ 0 := by exact_mod_cast hi
  have Hz := (mul_eq_zero.mp Hterm).resolve_left ht
  nlinarith [sq_nonneg (sk.hU.w i (configFlip n σ) - sk.hU.w i σ)]

/-- Exact-covariance SK Hamiltonians are even on one common full-measure set. -/
theorem skDisorder_even_ae {n : ℕ} (β h : ℝ) (sk : SKDisorder (Ω := Ω) n β h) :
    ∀ᵐ ω, ∀ σ, sk.U ω (configFlip n σ) = sk.U ω σ := by
  have hc (i : sk.hU.ι) : ∀ᵐ ω, ∀ σ,
      sk.hU.c i ω * sk.hU.w i (configFlip n σ) = sk.hU.c i ω * sk.hU.w i σ := by
    by_cases hi : sk.hU.τ i = 0
    · have hm := sk.hU.c_gauss i
      change Measure.map (sk.hU.c i) ℙ = gaussianReal 0 (sk.hU.τ i) at hm
      have hz : ∀ᵐ z ∂Measure.map (sk.hU.c i) ℙ, z = 0 := by
        rw [hm, hi, gaussianReal_zero_var]
        simp
      have hz' : ∀ᵐ ω, sk.hU.c i ω = 0 := ae_of_ae_map (sk.hU.c_meas i).aemeasurable hz
      filter_upwards [hz'] with ω hω
      simp [hω]
    · exact Filter.Eventually.of_forall fun ω σ =>
        congrArg (fun x => sk.hU.c i ω * x)
          (skDisorder_basis_even_of_variance_ne_zero β h sk i hi σ)
  filter_upwards [Filter.eventually_all.mpr hc] with ω hω
  intro σ
  have Hrepr := congrFun sk.hU.repr ω
  rw [Hrepr]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => hω i σ

end SpinGlass.Targets
