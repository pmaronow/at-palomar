module

public import Targets.MixedCascadeDeriv
public import Targets.CoupledReplicaHessian

@[expose] public section

/-!
# Actual Gibbs and split-replica weights for mixed Gaussian cascades

Every weight is transported through the actual normalized mean of its mixed
level. Opposite sharing reflects only the second field; the raw tilt mass is
unchanged. Positivity, normalization and finite moments are proved from the
existing Gaussian kernels, including zero masses and zero variances.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

variable {n : ℕ}

theorem CoupledGrowth.mixedCascade
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) :
    CoupledGrowth (mixedVectorCascade n mode m v F j) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact ih.mixedStep (mode j) (hm j) (hv j)

theorem CoupledBounded.flip_second
    {G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hG : CoupledBounded G) :
    CoupledBounded (fun x y => G x (-y)) := by
  obtain ⟨B, hb⟩ := hG.bound
  exact ⟨hG.measurable.comp (measurable_fst.prodMk measurable_snd.neg), B,
    fun x y => hb x (-y)⟩

theorem mixedVectorMean_measurable_bound
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B m v : ℝ}
    (hA : CoupledGrowth A)
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (hb : ∀ x y, |G x y| ≤ B) (mode : Section5GaussianMode)
    (hm : 0 ≤ m) (hv : 0 ≤ v) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedVectorMean n mode m v A G p.1 p.2) ∧
      ∀ x y, |mixedVectorMean n mode m v A G x y| ≤ B := by
  cases mode with
  | independent => exact pairedIndependentMean_measurable_bound hA hG hb hm hv
  | shared => exact pairedSharedMean_measurable_bound hA hG hb m v
  | opposite =>
    have H := pairedSharedMean_measurable_bound (G := fun x y => G x (-y)) hA.flip_second
      (hG.comp (measurable_fst.prodMk measurable_snd.neg))
      (fun x y => hb x (-y)) m v
    exact ⟨H.1.comp (measurable_fst.prodMk measurable_snd.neg), fun x y => H.2 x (-y)⟩

theorem mixedVectorMean_nonneg
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (hG : ∀ x y, 0 ≤ G x y) (mode : Section5GaussianMode)
    {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) (x y : Fin n → ℝ) :
    0 ≤ mixedVectorMean n mode m v A G x y := by
  cases mode with
  | independent =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, Nat.zero_lt_succ, if_true] using
      coupledFieldCascadeD_nonneg hA hG (fun _ => m) (fun _ => v)
        (fun _ => hm) (fun _ => hv) 1 1 x y
  | shared =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, lt_self_iff_false, if_false] using
      coupledFieldCascadeD_nonneg hA hG (fun _ => m) (fun _ => v)
        (fun _ => hm) (fun _ => hv) 0 1 x y
  | opposite =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, lt_self_iff_false, if_false] using
      coupledFieldCascadeD_nonneg hA.flip_second (fun x y => hG x (-y))
        (fun _ => m) (fun _ => v) (fun _ => hm) (fun _ => hv) 0 1 x (-y)

theorem mixedVectorMean_const
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (c : ℝ) (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun _ _ => c) x y = c := by
  cases mode with
  | independent =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, Nat.zero_lt_succ, if_true] using
      coupledFieldCascadeD_const hA (fun _ => m) (fun _ => v)
        (fun _ => hm) (fun _ => hv) 1 1 c x y
  | shared =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, lt_self_iff_false, if_false] using
      coupledFieldCascadeD_const hA (fun _ => m) (fun _ => v)
        (fun _ => hm) (fun _ => hv) 0 1 c x y
  | opposite =>
    simpa only [mixedVectorMean, coupledFieldCascadeD, coupledFieldCascade, lt_self_iff_false, if_false] using
      coupledFieldCascadeD_const hA.flip_second (fun _ => m) (fun _ => v)
        (fun _ => hm) (fun _ => hv) 0 1 c x (-y)

theorem mixedVectorMean_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : I → ℝ}
    (hA : CoupledGrowth A)
    (hG : ∀ i, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G i p.1 p.2))
    (hb : ∀ i x y, |G i x y| ≤ B i) (c : I → ℝ)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    (x y : Fin n → ℝ) :
    mixedVectorMean n mode m v A (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * mixedVectorMean n mode m v A (G i) x y := by
  cases mode with
  | independent => exact pairedIndependentMean_sum hA hG hb c hm hv x y
  | shared => exact pairedSharedMean_sum hA hG hb c m v x y
  | opposite =>
    exact pairedSharedMean_sum (G := fun i x y => G i x (-y)) hA.flip_second
      (fun i => (hG i).comp (measurable_fst.prodMk measurable_snd.neg))
      (fun i x y => hb i x (-y)) c m v x (-y)

theorem mixedVectorCascadeD_measurable_bound
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : ℝ}
    (hA : CoupledGrowth A)
    (hG : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2))
    (hb : ∀ x y, |G x y| ≤ B) (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedVectorCascadeD n mode m v A G j p.1 p.2) ∧
      ∀ x y, |mixedVectorCascadeD n mode m v A G j x y| ≤ B := by
  induction j with
  | zero => exact ⟨hG, hb⟩
  | succ j ih =>
    exact mixedVectorMean_measurable_bound
      (hA.mixedCascade mode m v hm hv j) ih.1 ih.2 (mode j) (hm j) (hv j)

theorem CoupledBounded.mixedMean
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hG : CoupledBounded G)
    (hA : CoupledGrowth A) (mode : Section5GaussianMode) {m v : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ v) : CoupledBounded (mixedVectorMean n mode m v A G) := by
  obtain ⟨B, hb⟩ := hG.bound
  have H := mixedVectorMean_measurable_bound hA hG.measurable hb mode hm hv
  exact ⟨H.1, B, H.2⟩

theorem CoupledBounded.mixedCascadeD
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hG : CoupledBounded G)
    (hA : CoupledGrowth A) (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) :
    CoupledBounded (mixedVectorCascadeD n mode m v A G j) := by
  obtain ⟨B, hb⟩ := hG.bound
  have H := mixedVectorCascadeD_measurable_bound hA hG.measurable hb mode m v hm hv j
  exact ⟨H.1, B, H.2⟩

theorem mixedVectorCascadeD_nonneg
    {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (hG : ∀ x y, 0 ≤ G x y) (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    0 ≤ mixedVectorCascadeD n mode m v A G j x y := by
  induction j generalizing x y with
  | zero => exact hG x y
  | succ j ih =>
    exact mixedVectorMean_nonneg (hA.mixedCascade mode m v hm hv j)
      ih (mode j) (hm j) (hv j) x y

theorem mixedVectorCascadeD_const
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (c : ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n mode m v A (fun _ _ => c) j x y = c := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he := funext fun x => funext fun y => ih x y
    simp only [mixedVectorCascadeD, he]
    exact mixedVectorMean_const (hA.mixedCascade mode m v hm hv j) (mode j) (hm j) (hv j) c x y

theorem mixedVectorCascadeD_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {B : I → ℝ}
    (hA : CoupledGrowth A)
    (hG : ∀ i, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G i p.1 p.2))
    (hb : ∀ i x y, |G i x y| ≤ B i) (c : I → ℝ)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n mode m v A (fun x y => ∑ i, c i * G i x y) j x y =
      ∑ i, c i * mixedVectorCascadeD n mode m v A (G i) j x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he := funext fun x => funext fun y => ih x y
    have hp (i : I) := mixedVectorCascadeD_measurable_bound hA (hG i) (hb i) mode m v hm hv j
    simp only [mixedVectorCascadeD, he]
    exact mixedVectorMean_sum (hA.mixedCascade mode m v hm hv j)
      (fun i => (hp i).1) (fun i => (hp i).2) c (mode j) (hm j) (hv j) x y

/-- The genuine finite-state Gibbs coordinates under the mixed transport. -/
noncomputable def mixedConstrainedGibbs (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (j : ℕ) (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ)
    (p : AT.ConstrainedPair n u) : ℝ :=
  mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
    (fun x y => constrainedPairGibbs n U u x y p) j x y

private theorem gibbs_abs_le_one (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (p : AT.ConstrainedPair n u) (x y : Fin n → ℝ) :
    |constrainedPairGibbs n U u x y p| ≤ 1 := by
  rw [abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
  exact AT.gtStateGibbs_le_one _ _ _

private theorem terminal_growth (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] : CoupledGrowth (constrainedPairFieldBase n U u) :=
  constrainedPairFieldCascade_growth U u (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) 0 0

theorem mixedConstrainedGibbs_measurable_bound
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (p : AT.ConstrainedPair n u) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => mixedConstrainedGibbs mode m v j U u z.1 z.2 p) ∧
      ∀ x y, |mixedConstrainedGibbs mode m v j U u x y p| ≤ 1 :=
  mixedVectorCascadeD_measurable_bound (terminal_growth U u)
    (measurable_constrainedPairGibbs_fields U u p) (gibbs_abs_le_one U u p) mode m v hm hv j

theorem mixedConstrainedGibbs_nonneg
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (x y : Fin n → ℝ) (p : AT.ConstrainedPair n u) :
    0 ≤ mixedConstrainedGibbs mode m v j U u x y p :=
  mixedVectorCascadeD_nonneg (terminal_growth U u)
    (fun x y => constrainedPairGibbs_nonneg n U u x y p) mode m v hm hv j x y

theorem mixedConstrainedGibbs_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ)
    (f : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p) j x y =
      ∑ p, mixedConstrainedGibbs mode m v j U u x y p * f p := by
  simpa only [mul_comm, mixedConstrainedGibbs] using
    mixedVectorCascadeD_sum (terminal_growth U u) (measurable_constrainedPairGibbs_fields U u)
      (gibbs_abs_le_one U u) f mode m v hm hv j x y

theorem sum_mixedConstrainedGibbs
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    ∑ p, mixedConstrainedGibbs mode m v j U u x y p = 1 := by
  have H := mixedConstrainedGibbs_moment U u mode m v hm hv j (fun _ => 1) x y
  simp only [mul_one, sum_constrainedPairGibbs] at H
  exact H.symm.trans (mixedVectorCascadeD_const (terminal_growth U u) mode m v hm hv j 1 x y)

/-- The actual disorder derivative is a moment under these same Gibbs weights. -/
theorem mixedConstrainedCascadeD_disorder_eq_replica
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairDirection U V u) j x y =
      ∑ p, mixedConstrainedGibbs mode m v j U u x y p * (V p.1.1 + V p.1.2) :=
  mixedConstrainedGibbs_moment U u mode m v hm hv j _ x y

/-- Independent and signed field directions have the same actual Gibbs law. -/
theorem mixedConstrainedCascadeD_field_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B x y : Fin n → ℝ) :
    mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairFieldDirection U u A B) j x y =
      ∑ p, mixedConstrainedGibbs mode m v j U u x y p * pairFieldPotential n u A B p :=
  mixedConstrainedGibbs_moment U u mode m v hm hv j _ x y

theorem hasDerivAt_mixedConstrainedCascade_eq_replica
    (U V : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (U + b • V) u) j x y)
      (∑ p, mixedConstrainedGibbs mode m v j (U + a • V) u x y p * (V p.1.1 + V p.1.2)) a := by
  simpa only [mixedConstrainedCascadeD_disorder_eq_replica _ V u mode m v hm hv] using
    hasDerivAt_mixedConstrainedCascade U V u mode m v hm hv j x y a

theorem hasDerivAt_mixedConstrainedCascade_field_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (A B x y : Fin n → ℝ) :
    HasDerivAt (fun a : ℝ => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j
      (x + a • A) (y + a • B))
      (∑ p, mixedConstrainedGibbs mode m v j U u x y p * pairFieldPotential n u A B p) 0 := by
  simpa only [mixedConstrainedCascadeD_field_eq_replica U u mode m v hm hv] using
    hasDerivAt_mixedConstrainedCascade_field U u mode m v hm hv j A B x y

/-- Restarting the actual mixed recursion shifts all three level arrays. -/
theorem mixedVectorCascade_add_levels (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (l r : ℕ) (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorCascade n (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
      (mixedVectorCascade n mode m v A l) r = mixedVectorCascade n mode m v A (l + r) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [mixedVectorCascade, ih]; rfl

/-- Replicas split after `l` inner levels; their product is formed before
transport through the remaining `r` actual mixed levels. -/
noncomputable def mixedConstrainedReplica (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (l r : ℕ) (U : EnergySpace n) (u : ℝ) (x y : Fin n → ℝ)
    (p q : AT.ConstrainedPair n u) : ℝ :=
  mixedVectorCascadeD n (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
    (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) l)
    (fun x y => mixedConstrainedGibbs mode m v l U u x y p *
      mixedConstrainedGibbs mode m v l U u x y q) r x y

private theorem replica_product_props
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l : ℕ)
    (p : AT.ConstrainedPair n u × AT.ConstrainedPair n u) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedConstrainedGibbs mode m v l U u z.1 z.2 p.1 *
        mixedConstrainedGibbs mode m v l U u z.1 z.2 p.2) ∧
      ∀ x y, |mixedConstrainedGibbs mode m v l U u x y p.1 *
        mixedConstrainedGibbs mode m v l U u x y p.2| ≤ 1 := by
  have h1 := mixedConstrainedGibbs_measurable_bound U u mode m v hm hv l p.1
  have h2 := mixedConstrainedGibbs_measurable_bound U u mode m v hm hv l p.2
  refine ⟨h1.1.mul h2.1, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_one₀ (h1.2 x y) (abs_nonneg _) (h2.2 x y)

theorem mixedConstrainedReplica_measurable_bound
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (p q : AT.ConstrainedPair n u) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      mixedConstrainedReplica mode m v l r U u z.1 z.2 p q) ∧
      ∀ x y, |mixedConstrainedReplica mode m v l r U u x y p q| ≤ 1 :=
  mixedVectorCascadeD_measurable_bound ((terminal_growth U u).mixedCascade mode m v hm hv l)
    (replica_product_props U u mode m v hm hv l (p, q)).1
    (replica_product_props U u mode m v hm hv l (p, q)).2
    _ _ _ (fun i => hm (l + i)) (fun i => hv (l + i)) r

theorem mixedConstrainedReplica_nonneg
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (x y : Fin n → ℝ) (p q : AT.ConstrainedPair n u) :
    0 ≤ mixedConstrainedReplica mode m v l r U u x y p q :=
  mixedVectorCascadeD_nonneg ((terminal_growth U u).mixedCascade mode m v hm hv l)
    (fun x y => mul_nonneg (mixedConstrainedGibbs_nonneg U u mode m v hm hv l x y p)
      (mixedConstrainedGibbs_nonneg U u mode m v hm hv l x y q))
    _ _ _ (fun i => hm (l + i)) (fun i => hv (l + i)) r x y

theorem mixedConstrainedReplica_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (f : AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
      (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) l)
      (fun x y => ∑ p, ∑ q, mixedConstrainedGibbs mode m v l U u x y p *
        mixedConstrainedGibbs mode m v l U u x y q * f p q) r x y =
      ∑ p, ∑ q, mixedConstrainedReplica mode m v l r U u x y p q * f p q := by
  have H := mixedVectorCascadeD_sum ((terminal_growth U u).mixedCascade mode m v hm hv l)
    (fun p => (replica_product_props U u mode m v hm hv l p).1)
    (fun p => (replica_product_props U u mode m v hm hv l p).2)
    (fun p => f p.1 p.2) (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
    (fun i => hm (l + i)) (fun i => hv (l + i)) r x y
  simpa only [Fintype.sum_prod_type, mul_comm, mixedConstrainedReplica] using H

theorem sum_mixedConstrainedReplica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ) (x y : Fin n → ℝ) :
    ∑ p, ∑ q, mixedConstrainedReplica mode m v l r U u x y p q = 1 := by
  have H := mixedConstrainedReplica_moment U u mode m v hm hv l r (fun _ _ => 1) x y
  simp only [mul_one, ← Finset.mul_sum, sum_mixedConstrainedGibbs U u mode m v hm hv,
    mul_one] at H
  exact H.symm.trans (mixedVectorCascadeD_const
    ((terminal_growth U u).mixedCascade mode m v hm hv l)
      (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
      (fun i => hm (l + i)) (fun i => hv (l + i)) r 1 x y)

theorem mixedConstrainedReplica_product_moment
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (l r : ℕ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    mixedVectorCascadeD n (fun i => mode (l + i)) (fun i => m (l + i)) (fun i => v (l + i))
      (mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) l)
      (fun x y => (∑ p, mixedConstrainedGibbs mode m v l U u x y p * f p) *
        (∑ q, mixedConstrainedGibbs mode m v l U u x y q * g q)) r x y =
      ∑ p, ∑ q, mixedConstrainedReplica mode m v l r U u x y p q * f p * g q := by
  have he (x y : Fin n → ℝ) :
      (∑ p, mixedConstrainedGibbs mode m v l U u x y p * f p) *
        (∑ q, mixedConstrainedGibbs mode m v l U u x y q * g q) =
      ∑ p, ∑ q, mixedConstrainedGibbs mode m v l U u x y p *
        mixedConstrainedGibbs mode m v l U u x y q * (f p * g q) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [he]
  simpa only [mul_assoc] using mixedConstrainedReplica_moment U u mode m v hm hv l r
    (fun p q => f p * g q) x y

end SpinGlass.Targets
