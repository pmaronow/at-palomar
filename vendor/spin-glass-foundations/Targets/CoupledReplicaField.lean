module

public import Targets.CoupledReplicaHeat
public import Targets.CoupledReplicaTrace

@[expose] public section

/-!
# Field contractions of the actual split-replica heat terms

Contract the coordinate heat identities with the independent/shared spin
directions. The kernels are the linear overlap covariances already used in
the square-completion argument. The level and final split coefficients are
retained explicitly, including zero masses and zero variances.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

@[simp] theorem pairFieldPotential_single_left (u : ℝ)
    (p : AT.ConstrainedPair n u) (i : Fin n) :
    pairFieldPotential n u (Pi.single i 1) 0 p = spin n p.1.1 i := by
  simp [pairFieldPotential, Pi.single_apply]

@[simp] theorem pairFieldPotential_single_right (u : ℝ)
    (p : AT.ConstrainedPair n u) (i : Fin n) :
    pairFieldPotential n u 0 (Pi.single i 1) p = spin n p.1.2 i := by
  simp [pairFieldPotential, Pi.single_apply]

@[simp] theorem pairFieldPotential_single_shared (u : ℝ)
    (p : AT.ConstrainedPair n u) (i : Fin n) :
    pairFieldPotential n u (Pi.single i 1) (Pi.single i 1) p =
      spin n p.1.1 i + spin n p.1.2 i := by
  simp [pairFieldPotential, Pi.single_apply]

theorem pairFieldPotential_independent_contraction (hn : 0 < n) (u : ℝ)
    (p q : AT.ConstrainedPair n u) :
    (∑ i : Fin (n + n),
      pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i) p *
      pairFieldPotential n u (independentLeftDirection n i) (independentRightDirection n i) q) =
      n * pairFieldCovariance 1 1 0 p.1 q.1 := by
  rw [Fin.sum_univ_add]
  simp only [independentLeftDirection_castAdd, independentRightDirection_castAdd,
    independentLeftDirection_natAdd, independentRightDirection_natAdd,
    pairFieldPotential_single_left, pairFieldPotential_single_right]
  rw [← Finset.sum_add_distrib, independent_pair_spin_contraction hn]
  simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]

theorem pairFieldPotential_shared_contraction (hn : 0 < n) (u : ℝ)
    (p q : AT.ConstrainedPair n u) :
    (∑ i : Fin n,
      pairFieldPotential n u (Pi.single i 1) (Pi.single i 1) p *
      pairFieldPotential n u (Pi.single i 1) (Pi.single i 1) q) =
      n * pairFieldCovariance 1 1 1 p.1 q.1 := by
  simp only [pairFieldPotential_single_shared]
  have H := shared_pair_spin_contraction hn (e := 1) (by norm_num) p.1 q.1
  simp only [one_mul] at H
  rw [H]
  simp only [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, one_mul]
  ring

theorem pairFieldCovariance_diagonal (hn : 0 < n) (β a c u : ℝ)
    (p : AT.ConstrainedPair n u) :
    pairFieldCovariance β a c p.1 p.1 = 2 * β ^ 2 * (a + c * u) := by
  simp [pairFieldCovariance, pairTrialMatrix, AT.pairOverlapMatrix_self hn, Fin.sum_univ_two]
  ring

/-- The normalized original-level heat expression, after all outer levels.
The terminal product at split `j` has coefficient `m j`. -/
noncomputable def constrainedReplicaHeatExpression
    (m v : ℕ → ℝ) (d j r : ℕ) (U : EnergySpace n) (u D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  D - constrainedReplicaMoment m v d 0 (j + r) U u K x y +
    ∑ l : Fin j, m l *
      (constrainedReplicaMoment m v d l (j + r - l) U u K x y -
        constrainedReplicaMoment m v d (l + 1) (j + r - (l + 1)) U u K x y) +
    m j * constrainedReplicaMoment m v d j r U u K x y

/-- Contraction of the full transported heat identity, with a constant
constrained diagonal. All replica moments retain the same original split. -/
theorem constrainedReplicaHeat_contraction {I : Type*} [Fintype I]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (f : I → AT.ConstrainedPair n u → ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (D : ℝ)
    (hK : ∀ p q, (∑ i, f i p * f i q) = n * K p q)
    (hD : ∀ p, K p p = D) (x y : Fin n → ℝ) :
    (∑ i, (constrainedReplicaTransportedHessian m v d j r U u (f i) (f i) x y +
      m j * constrainedReplicaBilinear m v d j r U u (f i) (f i) x y)) =
      n * constrainedReplicaHeatExpression m v d j r U u D K x y := by
  have hb (l s : ℕ) :
      (∑ i, constrainedReplicaBilinear m v d l s U u (f i) (f i) x y) =
        n * constrainedReplicaMoment m v d l s U u K x y := by
    have H := constrainedReplicaBilinear_contraction m v d l s U u (fun _ : I => 1) f x y
    simpa only [one_mul, hK, constrainedReplicaMoment_const_mul] using H
  have hd : (∑ i, ∑ p, constrainedCascadeGibbs m v d (j + r) U u x y p * f i p * f i p) =
      n * D := by
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hK, hD]
    rw [← Finset.sum_mul, sum_constrainedCascadeGibbs U u m v hm hv d (j + r) x y, one_mul]
  unfold constrainedReplicaTransportedHessian
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hd, hb]
  have hs : (∑ i, ∑ l : Fin j, m l *
      (constrainedReplicaBilinear m v d l (j + r - l) U u (f i) (f i) x y -
        constrainedReplicaBilinear m v d (l + 1) (j + r - (l + 1)) U u (f i) (f i) x y)) =
      n * ∑ l : Fin j, m l *
        (constrainedReplicaMoment m v d l (j + r - l) U u K x y -
          constrainedReplicaMoment m v d (l + 1) (j + r - (l + 1)) U u K x y) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, hb, ← mul_sub, mul_left_comm (m _) (n : ℝ)]
    rw [← Finset.mul_sum]
  rw [hs, ← Finset.mul_sum, hb]
  unfold constrainedReplicaHeatExpression
  ring

/-- Independent fields give the two diagonal cross-overlaps, with factor N/2. -/
theorem constrainedLevelVarianceD_independent_overlap
    (hn : 0 < n) (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : l < d) (x y : Fin n → ℝ) :
    constrainedLevelVarianceD U u m v d l r (v l) x y =
      (n : ℝ) / 2 * constrainedReplicaHeatExpression m v d l (r + 1) U u 2
        (fun p q => pairFieldCovariance 1 1 0 p.1 q.1) x y := by
  rw [constrainedLevelVarianceD_independent_eq_replica U u m v hm hv d l r hl x y,
    constrainedReplicaHeat_contraction U u m v hm hv d l (r + 1) _ _ 2
      (pairFieldPotential_independent_contraction hn u)
      (fun p => by simpa using pairFieldCovariance_diagonal hn 1 1 0 u p) x y]
  ring

/-- Shared fields give all four cross-overlaps, with factor N/2.
The overlap constraint makes the diagonal 2(1+u). -/
theorem constrainedLevelVarianceD_shared_overlap
    (hn : 0 < n) (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : ¬l < d) (x y : Fin n → ℝ) :
    constrainedLevelVarianceD U u m v d l r (v l) x y =
      (n : ℝ) / 2 * constrainedReplicaHeatExpression m v d l (r + 1) U u (2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1 1 p.1 q.1) x y := by
  rw [constrainedLevelVarianceD_shared_eq_replica U u m v hm hv d l r hl x y,
    constrainedReplicaHeat_contraction U u m v hm hv d l (r + 1) _ _ (2 * (1 + u))
      (pairFieldPotential_shared_contraction hn u)
      (fun p => by simpa using pairFieldCovariance_diagonal hn 1 1 1 u p) x y]
  ring

section Disorder

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The same original-level expression under the disorder-averaged split law. -/
noncomputable def averagedConstrainedReplicaHeatExpression (Z : Ω → EnergySpace n)
    (m v : ℕ → ℝ) (d j r : ℕ) (u D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  D - averagedConstrainedReplicaMoment Z m v d 0 (j + r) u K x y +
    ∑ l : Fin j, m l *
      (averagedConstrainedReplicaMoment Z m v d l (j + r - l) u K x y -
        averagedConstrainedReplicaMoment Z m v d (l + 1) (j + r - (l + 1)) u K x y) +
    m j * averagedConstrainedReplicaMoment Z m v d j r u K x y

theorem integrable_constrainedReplicaHeatExpression {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (D : ℝ) (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) :
    Integrable (fun ω => constrainedReplicaHeatExpression m v d j r (Z ω) u D K x y) := by
  have hi := fun l s => integrable_constrainedReplicaMoment hZ u m v hm hv d l s K x y
  exact (((integrable_const D).sub (hi 0 (j + r))).add
    (integrable_finsetSum (Finset.univ : Finset (Fin j)) fun l _ => ((hi l (j + r - l)).sub
      (hi (l + 1) (j + r - (l + 1)))).const_mul (m l))).add ((hi j r).const_mul (m j))

/-- All outer expectations are justified by integrability of the actual
normalized weights, not by a formal interchange of infinite integrals. -/
theorem integral_constrainedReplicaHeatExpression {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j r : ℕ) (D : ℝ) (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (x y : Fin n → ℝ) :
    (∫ ω, constrainedReplicaHeatExpression m v d j r (Z ω) u D K x y) =
      averagedConstrainedReplicaHeatExpression Z m v d j r u D K x y := by
  have hi := fun l s => integrable_constrainedReplicaMoment hZ u m v hm hv d l s K x y
  have hs : Integrable (fun ω => ∑ l : Fin j, m l *
      (constrainedReplicaMoment m v d l (j + r - l) (Z ω) u K x y -
        constrainedReplicaMoment m v d (l + 1) (j + r - (l + 1)) (Z ω) u K x y)) :=
    integrable_finsetSum _ fun l _ => ((hi l (j + r - l)).sub
      (hi (l + 1) (j + r - (l + 1)))).const_mul (m l)
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin j)) (fun l _ =>
    ((hi l (j + r - l)).sub (hi (l + 1) (j + r - (l + 1)))).const_mul (m l))
  have hlast := integral_add (((integrable_const D).sub (hi 0 (j + r))).add hs)
    ((hi j r).const_mul (m j))
  have hfirst := integral_add ((integrable_const D).sub (hi 0 (j + r))) hs
  have hsub := integral_sub (integrable_const D) (hi 0 (j + r))
  simp only [Pi.sub_apply, Pi.add_apply] at hsum hlast hfirst hsub
  unfold constrainedReplicaHeatExpression averagedConstrainedReplicaHeatExpression
  rw [hlast, hfirst, hsub,
    integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, integral_constrainedReplicaMoment hZ u m v hm hv,
    integral_constrainedReplicaMoment hZ u m v hm hv]
  congr 2
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_sub (hi l (j + r - l)) (hi (l + 1) (j + r - (l + 1))),
    integral_constrainedReplicaMoment hZ u m v hm hv,
    integral_constrainedReplicaMoment hZ u m v hm hv]

theorem integral_constrainedLevelVarianceD_independent_overlap
    (hn : 0 < n) {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : l < d) (x y : Fin n → ℝ) :
    (∫ ω, constrainedLevelVarianceD (Z ω) u m v d l r (v l) x y) =
      (n : ℝ) / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (r + 1) u 2
        (fun p q => pairFieldCovariance 1 1 0 p.1 q.1) x y := by
  simp_rw [constrainedLevelVarianceD_independent_overlap hn _ u m v hm hv d l r hl x y]
  rw [integral_const_mul, integral_constrainedReplicaHeatExpression hZ u m v hm hv]

theorem integral_constrainedLevelVarianceD_shared_overlap
    (hn : 0 < n) {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d l r : ℕ) (hl : ¬l < d) (x y : Fin n → ℝ) :
    (∫ ω, constrainedLevelVarianceD (Z ω) u m v d l r (v l) x y) =
      (n : ℝ) / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (r + 1) u (2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1 1 p.1 q.1) x y := by
  simp_rw [constrainedLevelVarianceD_shared_overlap hn _ u m v hm hv d l r hl x y]
  rw [integral_const_mul, integral_constrainedReplicaHeatExpression hZ u m v hm hv]

end Disorder

end SpinGlass.Targets
