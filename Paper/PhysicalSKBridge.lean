module

public import Paper.FiniteSK
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Physical SK normalization bridge

The paper uses independent couplings for increasing unordered pairs.  Their
covariance differs from the exact SK overlap kernel by a configuration-independent
constant.  One independent centered common Gaussian restores that covariance and
leaves the expected log partition unchanged.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper

@[simp] theorem spinSign_sq (s : Bool) : spinSign s ^ 2 = 1 := by
  cases s <;> norm_num [spinSign]

/-- Square expansion separating increasing pairs and the diagonal. -/
theorem unordered_pair_sum_square {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ^ 2 = 1) :
    (∑ i, x i) ^ 2 = (n : ℝ) + 2 * ∑ e : SKEdge n, x e.val.1 * x e.val.2 := by
  classical
  have hsplit (i j : Fin n) : x i * x j =
      (if i < j then x i * x j else 0) +
      (if j < i then x i * x j else 0) +
      (if i = j then x i * x j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr hij.le, ne_of_lt hij]
    · subst j
      simp
    · simp [hij, not_lt.mpr hij.le, ne_of_gt hij]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then x i * x j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    split_ifs <;> ring
  have hdiag : (∑ i : Fin n, ∑ j : Fin n, if i = j then x i * x j else 0) =
      (n : ℝ) := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← pow_two, hx]
    simp
  have hedge : (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) =
      ∑ e : SKEdge n, x e.val.1 * x e.val.2 := by
    rw [← Finset.sum_product', Finset.univ_product_univ]
    symm
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2))
      (by simp) (fun ij => x ij.1 * x ij.2)).symm
  rw [pow_two, Finset.sum_mul_sum]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [hsplit]
  simp only [Finset.sum_add_distrib]
  rw [hswap, hdiag, hedge]
  ring

/-- An independent common Gaussian restores the missing diagonal covariance.
Its coefficient is zero for the harmless size-zero model. -/
noncomputable def skCommonNoiseCoefficient (n : ℕ) (β : ℝ) : ℝ :=
  if n = 0 then 0 else β / Real.sqrt 2

/-- Coefficients of the centered external energy, with its `exp (-H)` convention. -/
noncomputable def physicalSKCoefficient (n : ℕ) (β : ℝ)
    (σ : SKConfiguration n) : Option (SKEdge n) → ℝ
  | none => skCommonNoiseCoefficient n β
  | some e => -(β / Real.sqrt (n : ℝ)) * spinSign (σ e.val.1) * spinSign (σ e.val.2)

/-- The coefficient inner product is exactly the SK overlap covariance kernel. -/
theorem physicalSKCoefficient_covariance (n : ℕ) (β : ℝ)
    (σ τ : SKConfiguration n) :
    (∑ k, physicalSKCoefficient n β σ k * physicalSKCoefficient n β τ k) =
      ((n : ℝ) * β ^ 2 / 2) *
        ((1 / (n : ℝ)) * ∑ i, spinSign (σ i) * spinSign (τ i)) ^ 2 := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [Fintype.sum_option]
    simp [physicalSKCoefficient, skCommonNoiseCoefficient]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsqn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  let x : Fin n → ℝ := fun i => spinSign (σ i) * spinSign (τ i)
  have hx (i : Fin n) : x i ^ 2 = 1 := by
    simp [x, mul_pow]
  have hpair := unordered_pair_sum_square x hx
  have hterm (e : SKEdge n) :
      physicalSKCoefficient n β σ (some e) * physicalSKCoefficient n β τ (some e) =
        (β / Real.sqrt (n : ℝ)) ^ 2 * (x e.val.1 * x e.val.2) := by
    simp only [physicalSKCoefficient, x]
    ring
  rw [Fintype.sum_option]
  simp_rw [hterm]
  simp only [physicalSKCoefficient, skCommonNoiseCoefficient, hn, ite_false, ← pow_two]
  rw [← Finset.mul_sum]
  change (β / Real.sqrt 2) ^ 2 + (β / Real.sqrt (n : ℝ)) ^ 2 *
      ∑ e : SKEdge n, x e.val.1 * x e.val.2 = _
  rw [div_pow, div_pow, hsq2, hsqn]
  change β ^ 2 / 2 + β ^ 2 / (n : ℝ) *
      ∑ e : SKEdge n, x e.val.1 * x e.val.2 =
        ((n : ℝ) * β ^ 2 / 2) * ((1 / (n : ℝ)) * ∑ i, x i) ^ 2
  rw [mul_pow, hpair]
  field_simp [hnr]

/-- Global spin reversal is a permutation of the finite configuration space. -/
def skSpinFlip (n : ℕ) : SKConfiguration n ≃ SKConfiguration n where
  toFun σ i := !(σ i)
  invFun σ i := !(σ i)
  left_inv σ := by funext i; exact Bool.not_not _
  right_inv σ := by funext i; exact Bool.not_not _

@[simp] theorem spinSign_not (s : Bool) : spinSign (!s) = -spinSign s := by
  cases s <;> norm_num [spinSign]

theorem skHamiltonian_spinFlip {n : ℕ} (β h : ℝ) (g : SKCouplings n)
    (σ : SKConfiguration n) :
    skHamiltonian β h g (skSpinFlip n σ) = skHamiltonian β (-h) g σ := by
  unfold skHamiltonian skSpinFlip
  simp only [Equiv.coe_fn_mk, spinSign_not]
  simp only [mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib]

/-- Field sign reversal leaves the actual partition function unchanged. -/
theorem skPartitionFunction_neg_field {n : ℕ} (β h : ℝ) (g : SKCouplings n) :
    skPartitionFunction β (-h) g = skPartitionFunction β h g := by
  unfold skPartitionFunction
  rw [← Equiv.sum_comp (skSpinFlip n) (fun σ => Real.exp (skHamiltonian β h g σ))]
  simp_rw [skHamiltonian_spinFlip]

/-- The corrected energy uses the external `exp (-H)` sign convention. -/
noncomputable def physicalCorrectedEnergy {n : ℕ} (β h : ℝ)
    (g : SKCouplings n) (ξ : ℝ) (σ : SKConfiguration n) : ℝ :=
  -skHamiltonian β (-h) g σ + skCommonNoiseCoefficient n β * ξ

/-- The independent common Gaussian adds only a configuration-independent log term. -/
theorem physicalCorrectedPartition_eq {n : ℕ} (β h : ℝ)
    (g : SKCouplings n) (ξ : ℝ) :
    (∑ σ, Real.exp (-physicalCorrectedEnergy β h g ξ σ)) =
      Real.exp (-skCommonNoiseCoefficient n β * ξ) * skPartitionFunction β h g := by
  unfold physicalCorrectedEnergy
  have hterm (σ : SKConfiguration n) :
      Real.exp (-(-skHamiltonian β (-h) g σ + skCommonNoiseCoefficient n β * ξ)) =
      Real.exp (-skCommonNoiseCoefficient n β * ξ) * Real.exp (skHamiltonian β (-h) g σ) := by
    rw [show -(-skHamiltonian β (-h) g σ + skCommonNoiseCoefficient n β * ξ) =
      -skCommonNoiseCoefficient n β * ξ + skHamiltonian β (-h) g σ by ring, Real.exp_add]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [← skPartitionFunction, skPartitionFunction_neg_field]

theorem physicalCorrectedLogPartition_eq {n : ℕ} (β h : ℝ)
    (g : SKCouplings n) (ξ : ℝ) :
    Real.log (∑ σ, Real.exp (-physicalCorrectedEnergy β h g ξ σ)) =
      -skCommonNoiseCoefficient n β * ξ + Real.log (skPartitionFunction β h g) := by
  rw [physicalCorrectedPartition_eq,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (skPartitionFunction_pos β h g)), Real.log_exp]

/-- The corrected finite-volume expected free energy is the paper's actual one.
The common Gaussian has mean zero, and all terms are integrable. -/
theorem physicalCorrectedFreeEnergy_eq {n : ℕ} (β h : ℝ) :
    (1 / (n : ℝ)) *
      (∫ p : SKCouplings n × ℝ,
        Real.log (∑ σ, Real.exp (-physicalCorrectedEnergy β h p.1 p.2 σ))
        ∂(skCouplingLaw n).prod (gaussianReal 0 1)) = finiteSKFreeEnergy β h n := by
  have hg := (integrable_log_skPartitionFunction (n := n) β h).comp_fst (gaussianReal 0 1)
  have hξ := ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).comp_snd
    (skCouplingLaw n)
  have hci := hξ.const_mul (-skCommonNoiseCoefficient n β)
  have hfull : Integrable (fun p : SKCouplings n × ℝ =>
      -skCommonNoiseCoefficient n β * p.2 + Real.log (skPartitionFunction β h p.1))
      ((skCouplingLaw n).prod (gaussianReal 0 1)) := hci.add hg
  simp_rw [physicalCorrectedLogPartition_eq]
  rw [integral_prod _ hfull]
  have hinner (g : SKCouplings n) :
      (∫ ξ : ℝ, -skCommonNoiseCoefficient n β * ξ + Real.log (skPartitionFunction β h g)
        ∂gaussianReal 0 1) = Real.log (skPartitionFunction β h g) := by
    have hlin : Integrable (fun ξ : ℝ => -skCommonNoiseCoefficient n β * ξ)
        (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).const_mul _
    rw [integral_add hlin (integrable_const _), integral_const_mul]
    simp
  simp_rw [hinner]
  rfl

/-- Mean of any measurable standard Gaussian coordinate. -/
theorem standardGaussianCoordinate_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hXm : Measurable X)
    (hX : P.map X = gaussianReal 0 1) : (∫ ω, X ω ∂P) = 0 := by
  have hm := integral_map (μ := P) hXm.aemeasurable measurable_id.aestronglyMeasurable
  rw [hX] at hm
  simpa using hm.symm

/-- A coordinate with an actual standard Gaussian pushforward has Gaussian law. -/
theorem standardGaussianCoordinate_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hXm : Measurable X)
    (hX : P.map X = gaussianReal 0 1) : HasGaussianLaw X P :=
  HasLaw.hasGaussianLaw ⟨hXm.aemeasurable, hX⟩

/-- Pairwise coordinate second moments from genuine independence and Gaussian laws. -/
theorem independent_standardGaussian_secondMoment {Ω I : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [DecidableEq I] (X : I → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, P.map (X i) = gaussianReal 0 1) (hI : iIndepFun X P) (i j : I) :
    (∫ ω, X i ω * X j ω ∂P) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    simp only [← pow_two]
    have hm := integral_map (hXm i).aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2) (P.map (X i)) by fun_prop)
    rw [hX i] at hm
    have hs : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
      have hv := variance_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_eq_integral measurable_id.aemeasurable] at hv
      simpa using hv
    simpa using hm.symm.trans hs
  · simp only [hij, ite_false]
    have hm := (hI.indepFun hij).integral_mul_eq_mul_integral
      (hXm i).aestronglyMeasurable (hXm j).aestronglyMeasurable
    simpa [standardGaussianCoordinate_mean P _ (hXm i) (hX i),
      standardGaussianCoordinate_mean P _ (hXm j) (hX j)] using hm

/-- The actual covariance of two finite linear combinations of independent Gaussians. -/
theorem independent_standardGaussian_linear_covariance {Ω I : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype I] [DecidableEq I] (X : I → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, P.map (X i) = gaussianReal 0 1) (hI : iIndepFun X P) (a b : I → ℝ) :
    (∫ ω, (∑ i, a i * X i ω) * (∑ j, b j * X j ω) ∂P) = ∑ i, a i * b i := by
  have hterm (i j : I) : Integrable (fun ω => a i * b j * (X i ω * X j ω)) P := by
    exact ((standardGaussianCoordinate_gaussian P _ (hXm i) (hX i)).memLp_two.integrable_mul
      (standardGaussianCoordinate_gaussian P _ (hXm j) (hX j)).memLp_two).const_mul _
  have hprod (ω : Ω) : (∑ i, a i * X i ω) * (∑ j, b j * X j ω) =
      ∑ j, ∑ i, a i * b j * (X i ω * X j ω) := by
    rw [Finset.sum_mul, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hprod]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ (fun i hi => hterm i j))]
  simp_rw [integral_finsetSum _ (fun i hi => hterm i _), integral_const_mul,
    independent_standardGaussian_secondMoment X hXm hX hI]
  simp

end Paper
