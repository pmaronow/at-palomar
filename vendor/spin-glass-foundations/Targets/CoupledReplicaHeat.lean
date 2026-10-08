module

public import Targets.CoupledReplicaHessian

@[expose] public section

/-!
# Outer transport of the actual spatial heat covariance

The Hessian at an inner level is transported through the unchanged outer
levels. Its replica law is the product at that original inner split followed
by all remaining transports, not the product of the final averaged means.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

set_option autoImplicit false

namespace SpinGlass.Targets

variable {n : ℕ}

/-- Composition of original-level normalized transports. This is an identity
of the actual recursive definitions, without analytic hypotheses. -/
theorem coupledOuterMean_comp (m v : ℕ → ℝ) (d l r s : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledOuterMean m v d A (l + r) s (coupledOuterMean m v d A l r G) =
      coupledOuterMean m v d A l (r + s) G := by
  induction s with
  | zero => simp only [coupledOuterMean_zero, Nat.add_zero]
  | succ s ih =>
    rw [coupledOuterMean_succ, ih]
    rw [show r + (s + 1) = (r + s) + 1 by omega, coupledOuterMean_succ]
    simp only [Nat.add_assoc]

theorem coupledOuterMean_add {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d A l r (fun x y => G x y + H x y) x y =
      coupledOuterMean m v d A l r G x y + coupledOuterMean m v d A l r H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul] using
      coupledOuterMean_sum hA h (fun _ => 1) m v hm hv d l r x y

theorem coupledOuterMean_const_mul {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (c : ℝ)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d A l r (fun x y => c * G x y) x y =
      c * coupledOuterMean m v d A l r G x y := by
  simpa using coupledOuterMean_sum (I := Unit) hA (fun _ => hG) (fun _ => c)
    m v hm hv d l r x y

theorem constrainedReplicaBilinear_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (f g : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (constrainedReplicaBilinear m v d l r U u f g) := by
  apply CoupledBounded.sum
  intro p
  apply CoupledBounded.sum
  intro q
  have H := constrainedCascadeReplica_measurable_bound U u m v hm hv d l r p q
  exact ((show CoupledBounded (fun x y => constrainedCascadeReplica m v d l r U u x y p q)
    from ⟨H.1, 1, H.2⟩).mul (CoupledBounded.const (f p))).mul (CoupledBounded.const (g q))

theorem constrainedCascadeGibbs_diagonal_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (f g : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (fun x y => ∑ p, constrainedCascadeGibbs m v d j U u x y p * f p * g p) := by
  apply CoupledBounded.sum
  intro p
  have H := constrainedCascadeGibbs_measurable_bound U u m v hm hv d j p
  exact ((show CoupledBounded (fun x y => constrainedCascadeGibbs m v d j U u x y p)
    from ⟨H.1, 1, H.2⟩).mul (CoupledBounded.const (f p))).mul (CoupledBounded.const (g p))

theorem constrainedReplicaHessianExpression_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (f g : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (constrainedReplicaHessianExpression m v d j U u f g) := by
  exact ((constrainedCascadeGibbs_diagonal_bounded U u m v hm hv d j f g).sub
    (constrainedReplicaBilinear_bounded U u m v hm hv d 0 j f g)).add
      (CoupledBounded.sum fun l : Fin j =>
        ((constrainedReplicaBilinear_bounded U u m v hm hv d l (j - l) f g).sub
          (constrainedReplicaBilinear_bounded U u m v hm hv d (l + 1) (j - (l + 1)) f g)).const_mul (m l))

/-- Transport extends the outer length of the same actual split law. -/
theorem coupledOuterMean_replicaBilinear
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r s : ℕ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d (constrainedPairFieldBase n U u) (l + r) s
      (constrainedReplicaBilinear m v d l r U u f g) x y =
        constrainedReplicaBilinear m v d l (r + s) U u f g x y := by
  have he (t : ℕ) : constrainedReplicaBilinear m v d l t U u f g =
      coupledOuterMean m v d (constrainedPairFieldBase n U u) l t
        (fun x y => (∑ p, constrainedCascadeGibbs m v d l U u x y p * f p) *
          (∑ p, constrainedCascadeGibbs m v d l U u x y p * g p)) := by
    funext x y
    exact (constrainedCascadeReplica_product_moment U u m v hm hv d l t f g x y).symm
  rw [he r, he (r + s), coupledOuterMean_comp]

theorem coupledOuterMean_gibbs_diagonal
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d (constrainedPairFieldBase n U u) j r
      (fun x y => ∑ p, constrainedCascadeGibbs m v d j U u x y p * f p * g p) x y =
      ∑ p, constrainedCascadeGibbs m v d (j + r) U u x y p * f p * g p := by
  have he (t : ℕ) : (fun x y => ∑ p, constrainedCascadeGibbs m v d t U u x y p * f p * g p) =
      coupledFieldCascadeD m v d (constrainedPairFieldBase n U u)
        (fun x y => ∑ p, constrainedPairGibbs n U u x y p * (f p * g p)) t := by
    funext x y
    simpa only [mul_assoc] using (constrainedCascadeGibbs_moment U u m v hm hv d t
      (fun p => f p * g p) x y).symm
  change _ = (fun x y => ∑ p, constrainedCascadeGibbs m v d (j + r) U u x y p * f p * g p) x y
  rw [he j, he (j + r), coupledOuterMean_cascadeD]

/-- Inner covariance terms retain their original level, while every term is
transported through all `r` additional outer levels. -/
noncomputable def constrainedReplicaTransportedHessian
    (m v : ℕ → ℝ) (d j r : ℕ) (U : EnergySpace n) (u : ℝ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (∑ p, constrainedCascadeGibbs m v d (j + r) U u x y p * f p * g p) -
    constrainedReplicaBilinear m v d 0 (j + r) U u f g x y +
    ∑ l : Fin j, m l *
      (constrainedReplicaBilinear m v d l (j + r - l) U u f g x y -
        constrainedReplicaBilinear m v d (l + 1) (j + r - (l + 1)) U u f g x y)

theorem coupledOuterMean_replicaHessian
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d (constrainedPairFieldBase n U u) j r
      (constrainedReplicaHessianExpression m v d j U u f g) x y =
      constrainedReplicaTransportedHessian m v d j r U u f g x y := by
  have hA : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv d 0
  have hb := fun l t => constrainedReplicaBilinear_bounded U u m v hm hv d l t f g
  have hd := constrainedCascadeGibbs_diagonal_bounded U u m v hm hv d j f g
  have hs := fun l : Fin j => (hb l (j - l)).sub (hb (l + 1) (j - (l + 1)))
  have ht (l : ℕ) (hl : l ≤ j) :
      coupledOuterMean m v d (constrainedPairFieldBase n U u) j r
        (constrainedReplicaBilinear m v d l (j - l) U u f g) x y =
      constrainedReplicaBilinear m v d l (j + r - l) U u f g x y := by
    convert coupledOuterMean_replicaBilinear U u m v hm hv d l (j - l) r f g x y using 1 <;>
      congr 2 <;> omega
  unfold constrainedReplicaHessianExpression
  rw [coupledOuterMean_add hA (hd.sub (hb 0 j))
    (CoupledBounded.sum fun l : Fin j => (hs l).const_mul (m l)) m v hm hv d j r x y,
    coupledOuterMean_sub hA hd (hb 0 j) m v hm hv d j r x y,
    coupledOuterMean_gibbs_diagonal U u m v hm hv d j r f g x y,
    coupledOuterMean_sum hA hs (fun l : Fin j => m l) m v hm hv d j r x y]
  have hz := ht 0 (Nat.zero_le j)
  simp only [Nat.sub_zero] at hz
  rw [hz]
  unfold constrainedReplicaTransportedHessian
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [coupledOuterMean_sub hA (hb l (j - l)) (hb (l + 1) (j - (l + 1)))
    m v hm hv d j r x y, ht l (by omega), ht (l + 1) (by omega)]

/-- The actual spatial heat input, after any number of unchanged outer levels,
has its explicit finite replica expansion. Zero masses and variances remain
allowed throughout. -/
theorem coupledOuterMean_constrainedSpatialHeat_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (mass : ℝ) (A B x y : Fin n → ℝ) :
    coupledOuterMean m v d (constrainedPairFieldBase n U u) j r
      (constrainedSpatialHeat U u m v d j mass A B) x y =
      constrainedReplicaTransportedHessian m v d j r U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y +
      mass * constrainedReplicaBilinear m v d j r U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y := by
  let f := pairFieldPotential n u A B
  have he : constrainedSpatialHeat U u m v d j mass A B =
      fun x y => constrainedReplicaHessianExpression m v d j U u f f x y +
        mass * constrainedReplicaBilinear m v d j 0 U u f f x y := by
    funext x y
    exact constrainedSpatialHeat_eq_replica U u m v hm hv d j mass A B x y
  have hA : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv d 0
  rw [he, coupledOuterMean_add hA
    (constrainedReplicaHessianExpression_bounded U u m v hm hv d j f f)
    ((constrainedReplicaBilinear_bounded U u m v hm hv d j 0 f f).const_mul mass)
    m v hm hv d j r x y,
    coupledOuterMean_replicaHessian U u m v hm hv d j r f f x y,
    coupledOuterMean_const_mul hA
      (constrainedReplicaBilinear_bounded U u m v hm hv d j 0 f f) mass m v hm hv d j r x y]
  have H := coupledOuterMean_replicaBilinear U u m v hm hv d j 0 r f f x y
  simpa only [Nat.add_zero, Nat.zero_add] using congrArg
    (fun z => constrainedReplicaTransportedHessian m v d j r U u f f x y + mass * z) H

/-- Bounded measurable perturbations give genuine two-sided local parameter
derivatives. This is used only to compare two representations of a tilt. -/
theorem CoupledBounded.perturbation {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hF : CoupledGrowth F) :
    ∃ B : ℝ, CoupledParamDeriv (fun a x y => F x y + a * G x y)
      (fun _ => G) (Set.Ioo (-1) 1) B := by
  obtain ⟨B, hb⟩ := hG.bound
  obtain ⟨C, D, hD, hf⟩ := hF.bound
  refine ⟨B, ?_, fun a _ => hF.measurable.add (hG.measurable.const_mul a),
    fun _ _ => hG.measurable, ⟨C + B, D, hD, ?_⟩, fun _ _ => hb⟩
  · intro a _ x y
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id a).mul_const (G x y)).const_add (F x y)
  · intro a ha x y
    have ha' : |a| ≤ 1 := abs_le.mpr ⟨le_of_lt ha.1, le_of_lt ha.2⟩
    have hg : |a * G x y| ≤ B := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul ha' (hb x y) (abs_nonneg _)
        (show (0 : ℝ) ≤ 1 by norm_num)
    have H := abs_add_le (F x y) (a * G x y)
    linarith [hf x y]

/-- The existing Gaussian parameter theorem applied to a fixed linear field
shift. It introduces no joint-regularity assumption. -/
theorem CoupledParamDeriv.hasDerivAt_linearStep {p : ℕ}
    {F G : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K : ℝ}
    (h : CoupledParamDeriv F G s K) {a : ℝ} (hs : s ∈ 𝓝 a)
    (mass variance : ℝ) (A B : Fin p → Fin n → ℝ) (x y : Fin n → ℝ) :
    HasDerivAt (fun z => coupledLinearStep mass variance A B (F z) x y)
      (coupledLinearMean mass variance A B (F a) (G a) x y) a := by
  obtain ⟨C, D, hD, hb⟩ := h.growth
  let S := ∑ i, (l1 (A i) + l1 (B i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => add_nonneg (l1_nonneg _) (l1_nonneg _)
  exact hasDerivAt_parisiStepPi_param (C := C + D * (l1 x + l1 y)) (D := D * S)
    (C' := K) (D' := 0) 0 hs (mul_nonneg hD hS) le_rfl
    (fun z hz w => h.deriv z hz _ _)
    (fun z hz => ((h.growth_at hz).linear_input A B x y).measurable)
    (fun z hz => (h.measurable_deriv z hz).comp
      ((measurable_const.add (measurable_pairedFieldLinear A)).prodMk
        (measurable_const.add (measurable_pairedFieldLinear B))))
    (fun z hz w => coupled_linear_growth_bound hD (hb z hz) A B x y w)
    (fun z hz w => by simpa only [zero_mul, add_zero] using h.bound z hz _ _)

/-- The packed independent Gaussian tilt and its two successive equal-mass
representations agree on every bounded measurable observable. The proof uses
uniqueness of two proved derivatives of the same bounded perturbation. -/
theorem coupledLinearMean_independent {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledBounded G) {mass variance : ℝ}
    (hm : 0 ≤ mass) (hv : 0 ≤ variance) (x y : Fin n → ℝ) :
    coupledLinearMean mass variance (independentLeftDirection n) (independentRightDirection n) F G x y =
      pairedIndependentMean mass variance F G x y := by
  obtain ⟨K, H⟩ := hG.perturbation hF
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by constructor <;> norm_num
  have hL := H.hasDerivAt_linearStep (isOpen_Ioo.mem_nhds h0) mass variance
    (independentLeftDirection n) (independentRightDirection n) x y
  have hR := (H.independentStep isOpen_Ioo hm hv).deriv 0 h0 x y
  simp only [coupledLinearStep_independent, zero_mul, add_zero] at hL
  simpa only [zero_mul, add_zero] using hL.unique hR

theorem coupledLinearMean_shared {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledBounded G) {mass variance : ℝ}
    (hm : 0 ≤ mass) (hv : 0 ≤ variance) (x y : Fin n → ℝ) :
    coupledLinearMean mass variance (fun i : Fin n => Pi.single i 1)
      (fun i : Fin n => Pi.single i 1) F G x y =
      pairedSharedMean mass variance F G x y := by
  obtain ⟨K, H⟩ := hG.perturbation hF
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by constructor <;> norm_num
  have hL := H.hasDerivAt_linearStep (isOpen_Ioo.mem_nhds h0) mass variance
    (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) x y
  have hR := (H.sharedStep isOpen_Ioo hm hv).deriv 0 h0 x y
  simp only [coupledLinearStep_shared, zero_mul, add_zero] at hL
  simpa only [zero_mul, add_zero] using hL.unique hR

theorem constrainedSpatialHeat_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (mass : ℝ) (A B : Fin n → ℝ) :
    CoupledBounded (constrainedSpatialHeat U u m v d j mass A B) :=
  ⟨measurable_constrainedSpatialHeat U u m v hm hv d j mass A B,
    _, constrainedSpatialHeat_abs_le U u m v hm hv d j mass A B⟩

/-- At the current variance, the original variance derivative propagates its
genuine heat seed with exactly the original outer normalized transports. -/
theorem constrainedLevelVarianceD_eq_outerMean
    (U : EnergySpace n) (u : ℝ) (m v : ℕ → ℝ) (d l r : ℕ) :
    constrainedLevelVarianceD U u m v d l r (v l) =
      coupledOuterMean m v d (constrainedPairFieldBase n U u) (l + 1) r
        (constrainedLevelHeat U u m v d l (v l)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [constrainedLevelVarianceD, Function.update_eq_self, ih,
      coupledOuterMean_succ, coupledLevelMean]

/-- Finite coordinate heat sums commute with all unchanged outer levels. -/
theorem coupledOuterMean_level_sum {I : Type*} [Fintype I]
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : ∀ i, CoupledBounded (G i))
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d F (l + 1) r
      (fun x y => (∑ i, coupledLevelMean m v d l (coupledFieldCascade n m v d F l) (G i) x y) / 2) x y =
      (∑ i, coupledOuterMean m v d F l (r + 1) (G i) x y) / 2 := by
  have H := coupledOuterMean_sum hF
    (fun i => (hG i).levelMean (hF.fieldCascade m v hm hv d l) m v hm hv d l)
    (fun _ => (1 : ℝ) / 2) m v hm hv d (l + 1) r x y
  have he (i : I) : coupledLevelMean m v d l (coupledFieldCascade n m v d F l) (G i) =
      coupledOuterMean m v d F l 1 (G i) := by
    simpa only [Nat.add_zero, coupledOuterMean_zero] using
      (coupledOuterMean_succ m v d l 0 F (G i)).symm
  simp_rw [he, coupledOuterMean_comp, Nat.add_comm 1 r] at H
  simpa only [one_div, ← Finset.mul_sum, div_eq_inv_mul, mul_one, he] using H

theorem constrainedLevelHeat_independent_eq_mean
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l : ℕ) (hl : l < d) :
    constrainedLevelHeat U u m v d l (v l) = fun x y =>
      (∑ i : Fin (n + n), coupledLevelMean m v d l
        (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
        (constrainedSpatialHeat U u m v d l (m l)
          (independentLeftDirection n i) (independentRightDirection n i)) x y) / 2 := by
  funext x y
  simp only [constrainedLevelHeat, if_pos hl, constrainedLinearHeat, coupledLevelMean]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coupledLinearMean_independent (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (constrainedSpatialHeat_bounded U u m v hm hv d l (m l) _ _) (hm l) (hv l) x y

theorem constrainedLevelHeat_shared_eq_mean
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l : ℕ) (hl : ¬ l < d) :
    constrainedLevelHeat U u m v d l (v l) = fun x y =>
      (∑ i : Fin n, coupledLevelMean m v d l
        (coupledFieldCascade n m v d (constrainedPairFieldBase n U u) l)
        (constrainedSpatialHeat U u m v d l (m l) (Pi.single i 1) (Pi.single i 1)) x y) / 2 := by
  funext x y
  simp only [constrainedLevelHeat, if_neg hl, constrainedLinearHeat, coupledLevelMean]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coupledLinearMean_shared (constrainedPairFieldCascade_growth U u m v hm hv d l)
    (constrainedSpatialHeat_bounded U u m v hm hv d l (m l) _ _) (hm l) (hv l) x y

/-- The existing genuine original-level variance derivative, in the independent
branch, equals the explicit finite split-replica heat expansion. This identity
allows variance zero; its analytic derivative interpretation at that coordinate
is supplied separately on positive variance by `hasDerivAt_constrainedFieldCascade_variance`. -/
theorem constrainedLevelVarianceD_independent_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : l < d) (x y : Fin n → ℝ) :
    constrainedLevelVarianceD U u m v d l r (v l) x y =
      (∑ i : Fin (n + n),
        (constrainedReplicaTransportedHessian m v d l (r + 1) U u
          (pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i))
          (pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i)) x y +
        m l * constrainedReplicaBilinear m v d l (r + 1) U u
          (pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i))
          (pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i)) x y)) / 2 := by
  have hF : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv d 0
  rw [constrainedLevelVarianceD_eq_outerMean,
    constrainedLevelHeat_independent_eq_mean U u m v hm hv d l hl,
    coupledOuterMean_level_sum hF
      (fun i => constrainedSpatialHeat_bounded U u m v hm hv d l (m l)
        (independentLeftDirection n i) (independentRightDirection n i)) m v hm hv d l r x y]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coupledOuterMean_constrainedSpatialHeat_eq_replica U u m v hm hv d l (r + 1)
    (m l) _ _ x y

/-- The corresponding shared-level variance derivative uses the actual mass
`m l` (the legacy shared-step parameter is `2 * m l`). -/
theorem constrainedLevelVarianceD_shared_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : ¬ l < d) (x y : Fin n → ℝ) :
    constrainedLevelVarianceD U u m v d l r (v l) x y =
      (∑ i : Fin n,
        (constrainedReplicaTransportedHessian m v d l (r + 1) U u
          (pairFieldPotential n u (Pi.single i 1) (Pi.single i 1))
          (pairFieldPotential n u (Pi.single i 1) (Pi.single i 1)) x y +
        m l * constrainedReplicaBilinear m v d l (r + 1) U u
          (pairFieldPotential n u (Pi.single i 1) (Pi.single i 1))
          (pairFieldPotential n u (Pi.single i 1) (Pi.single i 1)) x y)) / 2 := by
  have hF : CoupledGrowth (constrainedPairFieldBase n U u) :=
    constrainedPairFieldCascade_growth U u m v hm hv d 0
  rw [constrainedLevelVarianceD_eq_outerMean,
    constrainedLevelHeat_shared_eq_mean U u m v hm hv d l hl,
    coupledOuterMean_level_sum hF
      (fun i => constrainedSpatialHeat_bounded U u m v hm hv d l (m l)
        (Pi.single i 1) (Pi.single i 1)) m v hm hv d l r x y]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coupledOuterMean_constrainedSpatialHeat_eq_replica U u m v hm hv d l (r + 1)
    (m l) _ _ x y

end SpinGlass.Targets
