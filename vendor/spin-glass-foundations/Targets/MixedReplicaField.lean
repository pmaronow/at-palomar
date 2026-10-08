module

public import Targets.MixedNestedVariance
public import Targets.MixedReplicaHeat
public import Targets.MixedReplicaTrace
public import Targets.MixedReplicaAverage
public import Targets.MixedReplicaMoments
public import Targets.CoupledReplicaField
public import Targets.Section5InterleavedCovariance

@[expose] public section

/-!
# Actual mixed field-variance derivatives as replica overlap moments

The packed Gaussian mean is identified with the actual mixed derivative
transport by uniqueness of genuine perturbation derivatives. Coordinate
contraction then gives the overlap kernel with correlation zero, one or
minus one, and the same original split law survives disorder averaging.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

/-- Gaussian dimension of one actual mixed level. -/
def mixedModeDimension (n : ℕ) : Section5GaussianMode → ℕ
  | .independent => n + n
  | .shared => n
  | .opposite => n

noncomputable def mixedModeLeftDirection (n : ℕ) :
    (mode : Section5GaussianMode) → Fin (mixedModeDimension n mode) → Fin n → ℝ
  | .independent => independentLeftDirection n
  | .shared => fun i => Pi.single i 1
  | .opposite => fun i => Pi.single i 1

noncomputable def mixedModeRightDirection (n : ℕ) :
    (mode : Section5GaussianMode) → Fin (mixedModeDimension n mode) → Fin n → ℝ
  | .independent => independentRightDirection n
  | .shared => fun i => Pi.single i 1
  | .opposite => fun i => -Pi.single i 1

theorem coupledLinearStep_mixedMode {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (mode : Section5GaussianMode) (mass variance : ℝ) :
    coupledLinearStep mass variance (mixedModeLeftDirection n mode)
      (mixedModeRightDirection n mode) F = mixedVectorStep n mode mass variance F := by
  cases mode with
  | independent =>
    exact (coupledLinearStep_independent mass variance F).trans
      (mixedVectorStep_independent_eq mass variance hF).symm
  | shared =>
    exact (coupledLinearStep_shared mass variance F).trans
      (mixedVectorStep_shared_eq n mass variance F).symm
  | opposite => exact coupledLinearStep_opposite mass variance F

/-- Uniqueness of two checked derivatives identifies the full packed and
mixed normalized means; no Gaussian mean equality is assumed. -/
theorem coupledLinearMean_mixedMode {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledBounded G) (mode : Section5GaussianMode)
    {mass variance : ℝ} (hm : 0 ≤ mass) (hv : 0 ≤ variance) (x y : Fin n → ℝ) :
    coupledLinearMean mass variance (mixedModeLeftDirection n mode)
      (mixedModeRightDirection n mode) F G x y = mixedVectorMean n mode mass variance F G x y := by
  obtain ⟨K, H⟩ := hG.perturbation hF
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by constructor <;> norm_num
  have hL := H.hasDerivAt_linearStep (isOpen_Ioo.mem_nhds h0) mass variance
    (mixedModeLeftDirection n mode) (mixedModeRightDirection n mode) x y
  have hR := (H.mixedStep isOpen_Ioo mode hm hv).deriv 0 h0 x y
  have he : (fun a => coupledLinearStep mass variance (mixedModeLeftDirection n mode)
      (mixedModeRightDirection n mode) (fun x y => F x y + a * G x y) x y) =ᶠ[nhds 0]
      (fun a => mixedVectorStep n mode mass variance (fun x y => F x y + a * G x y) x y) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with a ha
    exact congrFun (congrFun (coupledLinearStep_mixedMode (H.growth_at ha) mode mass variance) x) y
  simpa only [zero_mul, add_zero] using (hL.congr_of_eventuallyEq he.symm).unique hR

theorem mixedSpatialHeat_bounded
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (mass : ℝ) (A B : Fin n → ℝ) :
    CoupledBounded (mixedSpatialHeat U u mode m v j mass A B) :=
  ⟨measurable_mixedSpatialHeat U u mode m v hm hv j mass A B,
    _, mixedSpatialHeat_abs_le U u mode m v hm hv j mass A B⟩

theorem mixedLevelHeat_eq_linear (U : EnergySpace n) (u : ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l : ℕ) (w : ℝ) :
    mixedLevelHeat U u mode m v l w =
      mixedLinearHeat U u mode m v l (m l) w
        (mixedModeLeftDirection n (mode l)) (mixedModeRightDirection n (mode l)) := by
  cases he : mode l <;> simp only [mixedLevelHeat, he, mixedModeLeftDirection, mixedModeRightDirection] <;> rfl

theorem mixedLevelHeat_eq_mean
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l : ℕ) :
    mixedLevelHeat U u mode m v l (v l) = fun x y =>
      (∑ i : Fin (mixedModeDimension n (mode l)),
        mixedVectorMean n (mode l) (m l) (v l)
          (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) l)
          (mixedSpatialHeat U u mode m v l (m l)
            (mixedModeLeftDirection n (mode l) i) (mixedModeRightDirection n (mode l) i)) x y) / 2 := by
  rw [mixedLevelHeat_eq_linear]
  funext x y
  unfold mixedLinearHeat
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact coupledLinearMean_mixedMode (mixedConstrainedCascade_growth U u mode m v hm hv l)
    (mixedSpatialHeat_bounded U u mode m v hm hv l (m l) _ _) (mode l) (hm l) (hv l) x y

/-- Evaluating the actual individual-variance derivative at the original
variance transports its heat seed through exactly the original outer levels. -/
theorem mixedLevelVarianceD_eq_outerMean
    (U : EnergySpace n) (u : ℝ) (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (l r : ℕ) :
    mixedLevelVarianceD U u mode m v l r (v l) =
      mixedOuterMean mode m v (constrainedPairFieldBase n U u) (l + 1) r
        (mixedLevelHeat U u mode m v l (v l)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [mixedLevelVarianceD, Function.update_eq_self, ih, mixedOuterMean_succ]

theorem mixedOuterMean_level_sum {I : Type*} [Fintype I]
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : ∀ i, CoupledBounded (G i))
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedOuterMean mode m v F (l + 1) r
      (fun x y => (∑ i, mixedVectorMean n (mode l) (m l) (v l)
        (mixedVectorCascade n mode m v F l) (G i) x y) / 2) x y =
      (∑ i, mixedOuterMean mode m v F l (r + 1) (G i) x y) / 2 := by
  have H := mixedOuterMean_sum hF
    (fun i => (hG i).mixedMean (hF.mixedCascade mode m v hm hv l) (mode l) (hm l) (hv l))
    (fun _ => (1 : ℝ) / 2) mode m v hm hv (l + 1) r x y
  have he (i : I) : mixedVectorMean n (mode l) (m l) (v l)
      (mixedVectorCascade n mode m v F l) (G i) = mixedOuterMean mode m v F l 1 (G i) := by
    simpa only [Nat.add_zero, mixedOuterMean_zero] using (mixedOuterMean_succ mode m v l 0 F (G i)).symm
  simp_rw [he, mixedOuterMean_comp, Nat.add_comm 1 r] at H
  simpa only [one_div, ← Finset.mul_sum, div_eq_inv_mul, mul_one, he] using H

/-- The actual coordinate heat terms, before contraction to overlaps.
Variance zero is included as an algebraic heat identity; its analytic
individual-variance derivative interpretation requires positive variance. -/
theorem mixedLevelVarianceD_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedLevelVarianceD U u mode m v l r (v l) x y =
      (∑ i : Fin (mixedModeDimension n (mode l)),
        let f := pairFieldPotential n u (mixedModeLeftDirection n (mode l) i)
          (mixedModeRightDirection n (mode l) i)
        mixedReplicaTransportedHessian mode m v l (r + 1) U u f f x y +
          m l * mixedReplicaBilinear mode m v l (r + 1) U u f f x y) / 2 := by
  have hF : CoupledGrowth (constrainedPairFieldBase n U u) :=
    mixedConstrainedCascade_growth U u mode m v hm hv 0
  rw [mixedLevelVarianceD_eq_outerMean, mixedLevelHeat_eq_mean U u mode m v hm hv,
    mixedOuterMean_level_sum hF
      (fun i => mixedSpatialHeat_bounded U u mode m v hm hv l (m l)
        (mixedModeLeftDirection n (mode l) i) (mixedModeRightDirection n (mode l) i))
      mode m v hm hv l r x y]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mixedOuterMean_spatialHeat_eq_replica U u mode m v hm hv l (r + 1) (m l) _ _ x y

/-- Common original-split heat expression; its last term has raw mass `m j`. -/
noncomputable def mixedReplicaHeatExpression
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j r : ℕ) (U : EnergySpace n) (u D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  D - mixedReplicaMoment mode m v 0 (j + r) U u K x y +
    ∑ l : Fin j, m l * (mixedReplicaMoment mode m v l (j + r - l) U u K x y -
      mixedReplicaMoment mode m v (l + 1) (j + r - (l + 1)) U u K x y) +
    m j * mixedReplicaMoment mode m v j r U u K x y

theorem mixedReplicaHeat_contraction {I : Type*} [Fintype I]
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ)
    (f : I → AT.ConstrainedPair n u → ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (D : ℝ)
    (hK : ∀ p q, (∑ i, f i p * f i q) = n * K p q) (hD : ∀ p, K p p = D)
    (x y : Fin n → ℝ) :
    (∑ i : I, (mixedReplicaTransportedHessian mode m v j r U u (f i) (f i) x y +
      m j * mixedReplicaBilinear mode m v j r U u (f i) (f i) x y)) =
      n * mixedReplicaHeatExpression mode m v j r U u D K x y := by
  have hb (l s : ℕ) : (∑ i, mixedReplicaBilinear mode m v l s U u (f i) (f i) x y) =
      n * mixedReplicaMoment mode m v l s U u K x y := by
    simpa only [one_mul, hK, mixedReplicaMoment_const_mul] using
      mixedReplicaBilinear_contraction mode m v l s U u (fun _ : I => 1) f x y
  have hd : (∑ i, ∑ p, mixedConstrainedGibbs mode m v (j + r) U u x y p * f i p * f i p) = n * D := by
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hK, hD]
    rw [← Finset.sum_mul, sum_mixedConstrainedGibbs U u mode m v hm hv (j + r) x y, one_mul]
  unfold mixedReplicaTransportedHessian
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hd, hb]
  have hs : (∑ i, ∑ l : Fin j, m l *
      (mixedReplicaBilinear mode m v l (j + r - l) U u (f i) (f i) x y -
        mixedReplicaBilinear mode m v (l + 1) (j + r - (l + 1)) U u (f i) (f i) x y)) =
      n * ∑ l : Fin j, m l * (mixedReplicaMoment mode m v l (j + r - l) U u K x y -
        mixedReplicaMoment mode m v (l + 1) (j + r - (l + 1)) U u K x y) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, hb, ← mul_sub, mul_left_comm (m _) (n : ℝ)]
    rw [← Finset.mul_sum]
  rw [hs, ← Finset.mul_sum, hb]
  unfold mixedReplicaHeatExpression
  ring

/-- Contracting the actual mode directions gives its signed overlap kernel. -/
theorem pairFieldPotential_mixedMode_contraction (hn : 0 < n) (u : ℝ)
    (mode : Section5GaussianMode) (p q : AT.ConstrainedPair n u) :
    (∑ i : Fin (mixedModeDimension n mode),
      pairFieldPotential n u (mixedModeLeftDirection n mode i) (mixedModeRightDirection n mode i) p *
      pairFieldPotential n u (mixedModeLeftDirection n mode i) (mixedModeRightDirection n mode i) q) =
      n * pairFieldCovariance 1 1 mode.correlation p.1 q.1 := by
  cases mode with
  | independent => exact pairFieldPotential_independent_contraction hn u p q
  | shared => exact pairFieldPotential_shared_contraction hn u p q
  | opposite =>
    change (∑ i : Fin n, pairFieldPotential n u (Pi.single i 1) (-Pi.single i 1) p *
      pairFieldPotential n u (Pi.single i 1) (-Pi.single i 1) q) =
      n * pairFieldCovariance 1 1 (-1) p.1 q.1
    simp only [show ∀ i : Fin n, -Pi.single i (1 : ℝ) = (-1 : ℝ) • Pi.single i 1 by
      intro i; simp, pairFieldPotential_shared_single]
    rw [shared_pair_spin_contraction hn (e := -1) (by norm_num)]
    simp only [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_pow, one_mul]
    ring

/-- Exact overlap formula for the actual mixed level variance derivative.
All original split indices are retained, including the current level's mean. -/
theorem mixedLevelVarianceD_overlap (hn : 0 < n) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    mixedLevelVarianceD U u mode m v l r (v l) x y =
      (n : ℝ) / 2 * mixedReplicaHeatExpression mode m v l (r + 1) U u
        (2 * (1 + (mode l).correlation * u))
        (fun p q => pairFieldCovariance 1 1 (mode l).correlation p.1 q.1) x y := by
  rw [mixedLevelVarianceD_eq_replica U u mode m v hm hv]
  rw [mixedReplicaHeat_contraction U u mode m v hm hv l (r + 1)
    (fun i => pairFieldPotential n u (mixedModeLeftDirection n (mode l) i)
      (mixedModeRightDirection n (mode l) i)) _ (2 * (1 + (mode l).correlation * u))
    (pairFieldPotential_mixedMode_contraction hn u (mode l))
    (fun p => by simpa only [one_pow, one_mul, mul_one] using
      pairFieldCovariance_diagonal hn 1 1 (mode l).correlation u p)]
  ring

section DisorderAverage

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The same finite heat expression under the genuine disorder-averaged law. -/
noncomputable def averagedMixedReplicaHeatExpression (Z : Ω → EnergySpace n)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ) (j r : ℕ) (u D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  D - averagedMixedReplicaMoment Z mode m v 0 (j + r) u K x y +
    ∑ l : Fin j, m l * (averagedMixedReplicaMoment Z mode m v l (j + r - l) u K x y -
      averagedMixedReplicaMoment Z mode m v (l + 1) (j + r - (l + 1)) u K x y) +
    m j * averagedMixedReplicaMoment Z mode m v j r u K x y

theorem integrable_mixedReplicaHeatExpression {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ) (D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    Integrable (fun ω => mixedReplicaHeatExpression mode m v j r (Z ω) u D K x y) := by
  have hi := fun l s => integrable_mixedReplicaMoment hZ u mode m v hm hv l s K x y
  exact (((integrable_const D).sub (hi 0 (j + r))).add
    (integrable_finsetSum (Finset.univ : Finset (Fin j)) fun l _ =>
      ((hi l (j + r - l)).sub (hi (l + 1) (j + r - (l + 1)))).const_mul (m l))).add
      ((hi j r).const_mul (m j))

theorem integral_mixedReplicaHeatExpression {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j r : ℕ) (D : ℝ)
    (K : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    (∫ ω, mixedReplicaHeatExpression mode m v j r (Z ω) u D K x y) =
      averagedMixedReplicaHeatExpression Z mode m v j r u D K x y := by
  have hi := fun l s => integrable_mixedReplicaMoment hZ u mode m v hm hv l s K x y
  have hs := integrable_finsetSum (Finset.univ : Finset (Fin j)) fun l _ =>
    ((hi l (j + r - l)).sub (hi (l + 1) (j + r - (l + 1)))).const_mul (m l)
  have hlin := integral_add (((integrable_const D).sub (hi 0 (j + r))).add hs)
    ((hi j r).const_mul (m j))
  have hlin' := integral_add ((integrable_const D).sub (hi 0 (j + r))) hs
  simp only [Pi.sub_apply, Pi.add_apply] at hlin hlin'
  unfold mixedReplicaHeatExpression averagedMixedReplicaHeatExpression
  rw [hlin, hlin',
    integral_sub (integrable_const D) (hi 0 (j + r)), integral_const,
    probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, integral_mixedReplicaMoment hZ u mode m v hm hv,
    integral_mixedReplicaMoment hZ u mode m v hm hv]
  congr 2
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin j)) (fun l _ =>
    ((hi l (j + r - l)).sub (hi (l + 1) (j + r - (l + 1)))).const_mul (m l))
  simp only [Pi.sub_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, integral_sub (hi l (j + r - l)) (hi (l + 1) (j + r - (l + 1))),
    integral_mixedReplicaMoment hZ u mode m v hm hv,
    integral_mixedReplicaMoment hZ u mode m v hm hv]

theorem integrable_mixedLevelVarianceD_all_variances (hn : 0 < n)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    Integrable (fun ω => mixedLevelVarianceD (Z ω) u mode m v l r (v l) x y) := by
  simp_rw [mixedLevelVarianceD_overlap hn _ u mode m v hm hv l r x y]
  exact (integrable_mixedReplicaHeatExpression hZ u mode m v hm hv l (r + 1)
    (2 * (1 + (mode l).correlation * u)) _ x y).const_mul _

/-- Actual mixed variance heat after disorder averaging, with its signed
overlap kernel and the exact system-size normalization. -/
theorem integral_mixedLevelVarianceD_overlap (hn : 0 < n)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    (∫ ω, mixedLevelVarianceD (Z ω) u mode m v l r (v l) x y) =
      (n : ℝ) / 2 * averagedMixedReplicaHeatExpression Z mode m v l (r + 1) u
        (2 * (1 + (mode l).correlation * u))
        (fun p q => pairFieldCovariance 1 1 (mode l).correlation p.1 q.1) x y := by
  simp_rw [mixedLevelVarianceD_overlap hn _ u mode m v hm hv l r x y]
  rw [integral_const_mul, integral_mixedReplicaHeatExpression hZ u mode m v hm hv]

end DisorderAverage

end SpinGlass.Targets
