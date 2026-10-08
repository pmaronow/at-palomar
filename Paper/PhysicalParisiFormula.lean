module

public import Paper.PhysicalSKDisorder
public import Targets.TalagrandFinal

@[expose] public section

/-! # Talagrand's finite-step formula for the paper's actual SK model

The sign of the Gaussian energy and the sign of the external field are
bridged explicitly.  The independent common Gaussian correction was already
proved to leave the paper's expected log partition function unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Paper

noncomputable def physicalTalagrandDisorder (n : ℕ) (β h : ℝ) :
    SpinGlass.SKDisorder (Ω := PhysicalSKGaussianSpace) n β h := by
  let sk := physicalGaussianSKDisorder n (-β) h
  refine ⟨sk.U, sk.hU, ?_⟩
  intro σ τ
  rw [sk.cov_eq]
  simp only [SpinGlass.sk_cov_kernel, neg_sq]

theorem physicalSKCoefficient_neg (n : ℕ) (β : ℝ) (σ : SKConfiguration n)
    (k : Option (SKEdge n)) :
    physicalSKCoefficient n (-β) σ k = -physicalSKCoefficient n β σ k := by
  cases k with
  | none =>
      unfold physicalSKCoefficient skCommonNoiseCoefficient
      split_ifs <;> ring
  | some e =>
      unfold physicalSKCoefficient
      ring

theorem physicalTalagrandDisorder_U (n : ℕ) (β h : ℝ)
    (ω : PhysicalSKGaussianSpace) (σ : SKConfiguration n) :
    (physicalTalagrandDisorder n β h).U ω σ =
      -(physicalGaussianSKDisorder n β (-h)).U ω σ := by
  change (∑ k, physicalSKCoefficient n (-β) σ k * physicalSKCoordinates n ω k) =
    -(∑ k, physicalSKCoefficient n β σ k * physicalSKCoordinates n ω k)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [physicalSKCoefficient_neg]
  ring

theorem physicalTalagrandDisorder_energy_eq (n : ℕ) (β h : ℝ)
    (ω : PhysicalSKGaussianSpace) :
    SpinGlass.skEnergy (N := n) (β := β) (h := h)
      ((physicalTalagrandDisorder n β h).U ω) =
        SpinGlass.AT.fullPathHamiltonian
          (physicalGaussianPath n β (-h) 0 (by norm_num)) 1 ω := by
  ext σ
  unfold SpinGlass.skEnergy SpinGlass.AT.fullPathHamiltonian
  simp only [Real.sqrt_one, sub_self, Real.sqrt_zero, one_smul, zero_smul, add_zero]
  simp only [neg_one_zsmul, WithLp.ofLp_add, WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply]
  rw [physicalTalagrandDisorder_U]
  simp only [neg_neg]
  rfl

/-- Exact expected free-energy agreement, including the size-zero convention. -/
theorem physicalTalagrandDisorder_freeEntropy_eq (n : ℕ) (β h : ℝ) :
    SpinGlass.free_entropy (Ω := PhysicalSKGaussianSpace) (N := n) (β := β) (h := h)
      (physicalTalagrandDisorder n β h).U = finiteSKFreeEnergy β h n := by
  unfold SpinGlass.free_entropy
  simp_rw [physicalTalagrandDisorder_energy_eq]
  change SpinGlass.AT.skFreeEnergy (physicalGaussianPath n β (-h) 0 (by norm_num)) = _
  rw [physicalGaussianPath_freeEnergy_eq]
  unfold finiteSKFreeEnergy
  simp_rw [skPartitionFunction_neg_field]

/-- The paper's finite SK free energy converges to the genuine finite-step
Parisi value, for every positive temperature and every real field. -/
theorem physicalParisiFormula_finiteStep (β h : ℝ) (hβ : 0 < β) :
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (SpinGlass.Targets.parisiValue β h)) := by
  have h := SpinGlass.Targets.parisi_formula β h hβ
    (fun n => physicalTalagrandDisorder n β h)
  simpa only [physicalTalagrandDisorder_freeEntropy_eq] using h

end Paper
