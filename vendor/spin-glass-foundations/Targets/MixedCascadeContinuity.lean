module

public import Targets.MixedCascadeGrowth
public import Targets.ConstrainedPathContinuity
public import Targets.CoupledDisorderInterpolation

@[expose] public section

/-!
# Continuity of the actual mixed interpolation

The existing arbitrary-direction Gaussian continuity theorem applies to every
mixed level. Second-field reflection handles opposite sharing without changing
the frozen physical fields. Uniform contraction in the terminal potential gives
an integrable bound for the outer disorder average, including both endpoints.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {n : ℕ}

theorem mixedVectorStep_dist_le (mode : Section5GaussianMode) {m v ε : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ v)
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledGrowth G)
    (hb : ∀ x y, |F x y - G x y| ≤ ε) (x y : Fin n → ℝ) :
    |mixedVectorStep n mode m v F x y - mixedVectorStep n mode m v G x y| ≤ ε := by
  cases mode with
  | independent =>
    rw [mixedVectorStep_independent_eq m v hF, mixedVectorStep_independent_eq m v hG]
    exact independentStepPi_dist_le hm hv hF hG hb x y
  | shared =>
    rw [mixedVectorStep_shared_eq, mixedVectorStep_shared_eq]
    exact sharedStepPi_dist_le hF hG hb x y
  | opposite =>
    rw [mixedVectorStep_opposite_eq, mixedVectorStep_opposite_eq]
    exact sharedStepPi_dist_le hF.flip_second hG.flip_second (fun a b => hb a (-b)) x (-y)

theorem mixedVectorListCascade_dist_le {α : Type*}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a) {ε : ℝ}
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledGrowth G)
    (hb : ∀ x y, |F x y - G x y| ≤ ε) (x y : Fin n → ℝ) :
    |mixedVectorListCascade n mode m v l F x y -
      mixedVectorListCascade n mode m v l G x y| ≤ ε := by
  induction l generalizing x y with
  | nil => exact hb x y
  | cons a l ih =>
    have hm' : ∀ b ∈ l, 0 ≤ m b := fun b hb => hm b (List.mem_cons_of_mem a hb)
    have hv' : ∀ b ∈ l, 0 ≤ v b := fun b hb => hv b (List.mem_cons_of_mem a hb)
    exact mixedVectorStep_dist_le (mode a) (hm a List.mem_cons_self) (hv a List.mem_cons_self)
      (hF.mixedList mode m v l hm' hv') (hG.mixedList mode m v l hm' hv') (ih hm' hv') x y

section Parameter

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]

omit [FirstCountableTopology P] in
theorem CoupledContinuousOn.flip_second
    {F : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) :
    CoupledContinuousOn (fun z x y => F z x (-y)) S := by
  obtain ⟨C, D, hD, hb⟩ := hF.growth
  refine ⟨fun z hz => (hF.growth_at hz).flip_second.measurable, ⟨C, D, hD, ?_⟩, ?_⟩
  · intro z hz x y
    simpa only [l1, Pi.neg_apply, abs_neg] using hb z hz x (-y)
  · intro x y hx hy
    exact hF.continuous x (fun z => -y z) hx hy.neg

/-- Compact-parameter continuity for every actual mixed Gaussian mode. -/
theorem CoupledContinuousOn.mixedStep
    {F : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) (hS : IsCompact S) (mode : Section5GaussianMode)
    {mass : ℝ} (hm : 0 ≤ mass) {v : P → ℝ}
    (hvc : ContinuousOn v S) (hv : ∀ z ∈ S, 0 ≤ v z) :
    CoupledContinuousOn (fun z => mixedVectorStep n mode mass (v z) (F z)) S := by
  cases mode with
  | independent =>
    have H := hF.linearStep hS (independentLeftDirection n) (independentRightDirection n) hm hvc hv
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simpa only [mixedVectorStep_independent_eq mass (v z) (hF.growth_at hz),
        coupledLinearStep_independent] using H.measurable z hz
    · obtain ⟨C, D, hD, hb⟩ := H.growth
      refine ⟨C, D, hD, fun z hz x y => ?_⟩
      simpa only [mixedVectorStep_independent_eq mass (v z) (hF.growth_at hz),
        coupledLinearStep_independent] using hb z hz x y
    · intro x y hx hy
      apply (H.continuous x y hx hy).congr
      intro z hz
      dsimp only
      rw [mixedVectorStep_independent_eq mass (v z) (hF.growth_at hz),
        coupledLinearStep_independent]
  | shared =>
    simpa only [mixedVectorStep_shared_eq, coupledLinearStep_shared] using
      hF.linearStep hS (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) hm hvc hv
  | opposite =>
    have he : (fun z => mixedVectorStep n .opposite mass (v z) (F z)) =
        (fun z x y => sharedStepPi n (2 * mass) (v z) (fun x y => F z x (-y)) x (-y)) :=
      funext fun z => funext fun x => funext fun y => mixedVectorStep_opposite_eq n mass (v z) (F z) x y
    rw [he]
    simpa only [coupledLinearStep_shared] using
      (hF.flip_second.linearStep hS
        (fun i : Fin n => Pi.single i 1) (fun i : Fin n => Pi.single i 1) hm hvc hv).flip_second

/-- All mixed variances and the terminal may vary simultaneously, including
zero variances. Only visited tags need to satisfy the hypotheses. -/
theorem CoupledContinuousOn.mixedList {α : Type*}
    {F : P → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {S : Set P}
    (hF : CoupledContinuousOn F S) (hS : IsCompact S)
    (mode : α → Section5GaussianMode) (m : α → ℝ) (v : α → P → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hvc : ∀ a ∈ l, ContinuousOn (v a) S)
    (hv : ∀ a ∈ l, ∀ z ∈ S, 0 ≤ v a z) :
    CoupledContinuousOn (fun z => mixedVectorListCascade n mode m (fun a => v a z) l (F z)) S := by
  induction l with
  | nil => exact hF
  | cons a l ih =>
    exact (ih (fun b hb => hm b (List.mem_cons_of_mem a hb))
      (fun b hb => hvc b (List.mem_cons_of_mem a hb))
      (fun b hb => hv b (List.mem_cons_of_mem a hb))).mixedStep hS (mode a)
        (hm a List.mem_cons_self) (hvc a List.mem_cons_self) (hv a List.mem_cons_self)

end Parameter

/-- Disorder contraction is uniform in the number and ordering of mixed levels. -/
theorem mixedConstrainedList_disorder_dist_le {α : Type*}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a)
    (U U' : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    |mixedVectorListCascade n mode m v l (constrainedPairFieldBase n U u) x y -
      mixedVectorListCascade n mode m v l (constrainedPairFieldBase n U' u) x y| ≤
      2 * uAbs n (U - U') := by
  have hg (W : EnergySpace n) : CoupledGrowth (constrainedPairFieldBase n W u) :=
    constrainedPairFieldCascade_growth W u (fun _ => 0) (fun _ => 0)
      (fun _ => le_rfl) (fun _ => le_rfl) 0 0
  exact mixedVectorListCascade_dist_le mode m v l hm hv (hg U) (hg U')
    (fun x y => constrainedPairFieldCascade_disorder_dist_le U U' u
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) 0 0 x y) x y

theorem continuous_mixedConstrainedList_disorder {α : Type*}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    Continuous (fun U => mixedVectorListCascade n mode m v l (constrainedPairFieldBase n U u) x y) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨2 * Fintype.card (Config n), by positivity⟩) ?_).continuous
  intro U U'
  change |_ - _| ≤ (2 * Fintype.card (Config n)) * ‖U - U'‖
  exact (mixedConstrainedList_disorder_dist_le mode m v l hm hv U U' u x y).trans
    (by nlinarith [uAbs_le_card_mul_norm n (U - U')])

end SpinGlass.Targets
