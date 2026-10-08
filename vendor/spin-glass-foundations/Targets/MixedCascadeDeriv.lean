module

public import Targets.MixedCascadeGrowth
public import Targets.CoupledCascadeField

@[expose] public section

/-!
# Actual first derivatives of arbitrary mixed Gaussian cascades

The independent and shared rules are the checked normalized Gaussian chain
rules. Opposite fields are the shared rule conjugated by second-field
reflection. Masses below are always the raw logarithmic-Laplace masses.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators

namespace SpinGlass.Targets

/-- The normalized mean corresponding to one actual mixed Gaussian step. -/
noncomputable def mixedVectorMean (n : ℕ) (mode : Section5GaussianMode) (m v : ℝ)
    (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  match mode with
  | .independent => pairedIndependentMean m v F G
  | .shared => pairedSharedMean m v F G
  | .opposite => fun x y => pairedSharedMean m v
      (fun x y => F x (-y)) (fun x y => G x (-y)) x (-y)

/-- The actual first-derivative recursion, with no restriction on mode order. -/
noncomputable def mixedVectorCascadeD (n : ℕ) (mode : ℕ → Section5GaussianMode)
    (m v : ℕ → ℝ) (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => G
  | j + 1 => mixedVectorMean n (mode j) (m j) (v j)
      (mixedVectorCascade n mode m v F j) (mixedVectorCascadeD n mode m v F G j)

variable {n : ℕ}

/-- Local equality of actual families preserves the full parameter package. -/
theorem CoupledParamDeriv.congr_eq_on
    {F G F' G' : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K : ℝ}
    (h : CoupledParamDeriv F G s K) (hs : IsOpen s)
    (hF : ∀ a ∈ s, F' a = F a) (hG : ∀ a ∈ s, G' a = G a) :
    CoupledParamDeriv F' G' s K := by
  obtain ⟨C, D, hD, hb⟩ := h.growth
  refine ⟨?_, fun a ha => by rw [hF a ha]; exact h.measurable a ha,
    fun a ha => by rw [hG a ha]; exact h.measurable_deriv a ha,
    ⟨C, D, hD, fun a ha x y => by rw [hF a ha]; exact hb a ha x y⟩,
    fun a ha x y => by rw [hG a ha]; exact h.bound a ha x y⟩
  intro a ha x y
  rw [hG a ha]
  apply (h.deriv a ha x y).congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds ha] with b hb
  rw [hF b hb]

/-- Reflection is a fixed field substitution, not a symmetry assumption on
the external field or the constrained terminal. -/
theorem CoupledParamDeriv.flip_second
    {F G : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K : ℝ}
    (h : CoupledParamDeriv F G s K) :
    CoupledParamDeriv (fun a x y => F a x (-y)) (fun a x y => G a x (-y)) s K := by
  apply h.comp_fields (fun p => p.1) (fun p => -p.2) measurable_fst measurable_snd.neg
    (K := 1) zero_le_one
  intro p
  simp only [l1, Pi.neg_apply, abs_neg, one_mul, le_refl]

/-- Every mixed mode preserves actual parameter differentiation and the
field-independent derivative bound, including zero masses and variances. -/
theorem CoupledParamDeriv.mixedStep
    {F G : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K m v : ℝ}
    (h : CoupledParamDeriv F G s K) (hs : IsOpen s)
    (mode : Section5GaussianMode) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledParamDeriv (fun a => mixedVectorStep n mode m v (F a))
      (fun a => mixedVectorMean n mode m v (F a) (G a)) s K := by
  cases mode with
  | independent =>
    exact (h.independentStep hs hm hv).congr_eq_on hs
      (fun a ha => mixedVectorStep_independent_eq m v (h.growth_at ha)) (fun _ _ => rfl)
  | shared =>
    simpa only [mixedVectorStep_shared_eq, mixedVectorMean] using h.sharedStep hs hm hv
  | opposite =>
    exact (h.flip_second.sharedStep hs hm hv).flip_second.congr_eq_on hs
      (fun a _ => funext fun x => funext fun y => mixedVectorStep_opposite_eq n m v (F a) x y)
      (fun _ _ => rfl)

/-- Full first-derivative induction through the genuine mixed recursion. -/
theorem CoupledParamDeriv.mixedCascade
    {F G : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {s : Set ℝ} {K : ℝ}
    (h : CoupledParamDeriv F G s K) (hs : IsOpen s)
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) :
    CoupledParamDeriv (fun a => mixedVectorCascade n mode m v (F a) j)
      (fun a => mixedVectorCascadeD n mode m v (F a) (G a) j) s K := by
  induction j with
  | zero => exact h
  | succ j ih => exact ih.mixedStep hs (mode j) (hm j) (hv j)

/-- Fixed translations commute with the genuine finite Gaussian operator. -/
theorem gtVectorStep_translate (n : ℕ) (m a b : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (X Y : Fin n → ℝ) :
    AT.gtVectorStep n m a b (fun x y => F (x + X) (y + Y)) =
      fun x y => AT.gtVectorStep n m a b F (x + X) (y + Y) := by
  funext x y
  simp only [AT.gtVectorStep, Pi.add_def, add_right_comm]

theorem mixedVectorStep_translate (mode : Section5GaussianMode) (m v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (X Y : Fin n → ℝ) :
    mixedVectorStep n mode m v (fun x y => F (x + X) (y + Y)) =
      fun x y => mixedVectorStep n mode m v F (x + X) (y + Y) := by
  cases mode <;> simp only [mixedVectorStep, gtVectorStep_translate]

/-- Arbitrary mixed modes commute with separate translations of the fields. -/
theorem mixedVectorCascade_translate (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (j : ℕ) (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (X Y x y : Fin n → ℝ) :
    mixedVectorCascade n mode m v (fun x y => F (x + X) (y + Y)) j x y =
      mixedVectorCascade n mode m v F j (x + X) (y + Y) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he := funext fun x => funext fun y => ih x y
    change mixedVectorStep n (mode j) (m j) (v j)
      (mixedVectorCascade n mode m v (fun x y => F (x + X) (y + Y)) j) x y = _
    rw [he, mixedVectorStep_translate]
    rfl

/-- The actual constrained disorder derivative for every mixed mode order. -/
theorem hasDerivAt_mixedConstrainedCascade (U V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b => mixedVectorCascade n mode m v
      (constrainedPairFieldBase n (U + b • V) u) j x y)
      (mixedVectorCascadeD n mode m v (constrainedPairFieldBase n (U + a • V) u)
        (constrainedPairDirection (U + a • V) V u) j x y) a :=
  ((constrainedPairFieldBase_paramDeriv U V u a).mixedCascade
    isOpen_Ioo mode m v hm hv j).deriv a ⟨by linarith, by linarith⟩ x y

theorem mixedConstrainedCascadeD_disorder_abs_le (U V : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (x y : Fin n → ℝ) :
    |mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairDirection U V u) j x y| ≤ 2 * uAbs n V := by
  have H := ((constrainedPairFieldBase_paramDeriv U V u 0).mixedCascade
    isOpen_Ioo mode m v hm hv j).bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [zero_smul, add_zero] using H

/-- The spatial first derivative is the actual normalized transport of the
two-replica spin direction, without assuming a replica interpretation. -/
theorem hasDerivAt_mixedConstrainedCascade_field (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (A B x y : Fin n → ℝ) :
    HasDerivAt (fun a : ℝ => mixedVectorCascade n mode m v (constrainedPairFieldBase n U u) j
      (x + a • A) (y + a • B))
      (mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
        (constrainedPairFieldDirection U u A B) j x y) 0 := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).mixedCascade
    isOpen_Ioo mode m v hm hv j).deriv 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [mixedVectorCascade_translate, zero_smul, add_zero] using H

theorem mixedConstrainedCascadeD_field_abs_le (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (j : ℕ) (A B x y : Fin n → ℝ) :
    |mixedVectorCascadeD n mode m v (constrainedPairFieldBase n U u)
      (constrainedPairFieldDirection U u A B) j x y| ≤ l1 A + l1 B := by
  have H := ((constrainedPairFieldBase_fieldParamDeriv U u 0 A B).mixedCascade
    isOpen_Ioo mode m v hm hv j).bound 0
      ⟨by norm_num [guerraLineNbhd], by norm_num [guerraLineNbhd]⟩ x y
  simpa only [zero_smul, add_zero] using H

end SpinGlass.Targets
