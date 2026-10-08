module

public import Targets.MixedCascadeGrowth
public import Targets.Section5InterleavedScalarCore

@[expose] public section

/-!
# The genuine zero-time interleaved endpoint

The constrained terminal comparison passes through the actual finite tagged
Gaussian operators. Finite-site tensorization then identifies the scalar
endpoint. No interpolation derivative inequality is assumed.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- An arbitrary finite tagged forward list is exactly the bottom-up mixed
recursion with reversed positions. The natural subtraction remains in range
even at unused indices, so no arbitrary padding tag is needed. -/
theorem mixedVectorListCascade_ofFn {α : Type*} (n : ℕ) {N : ℕ} (hN : 0 < N)
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (f : Fin N → α)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorListCascade n mode m v (List.ofFn f) F =
      mixedVectorCascade n
        (fun i => mode (f ⟨N - 1 - i, by omega⟩))
        (fun i => m (f ⟨N - 1 - i, by omega⟩))
        (fun i => v (f ⟨N - 1 - i, by omega⟩)) F N := by
  let g : ℕ → α := fun i => f ⟨min i (N - 1), by omega⟩
  have hg (i : Fin N) : g i = f i := by
    dsimp [g]
    congr 1
    apply Fin.ext
    exact min_eq_left (by omega)
  have hlist : List.ofFn f = (List.ofFn (fun p : Fin N => p.val)).map g := by
    rw [List.map_ofFn]
    congr 1
    funext p
    exact (hg p).symm
  rw [hlist, mixedVectorListCascade_map, mixedVectorListCascade_forward]
  apply mixedVectorCascade_congr
  all_goals
    intro i _
    dsimp only [Function.comp_apply, g]
    congr 2
    apply Fin.ext
    exact min_eq_left (Nat.sub_le _ _)

/-- Actual field-only endpoint comparison through arbitrary tagged Gaussian
modes, including negative shared directions. The lambda relaxation, growth,
order, and finite-site tensorization are all proved before normalization. -/
theorem mixedVectorListCascade_constrained_zero_le {α : Type*} {n N : ℕ}
    (hn : 0 < n) (hN : 0 < N) (mode : α → Section5GaussianMode)
    (m v : α → ℝ) (hm : ∀ a, 0 ≤ m a) (hv : ∀ a, 0 ≤ v a)
    (f : Fin N → α) (u ℓ h : ℝ) (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    mixedVectorListCascade n mode m v (List.ofFn f)
      (constrainedPairFieldBase n (0 : EnergySpace n) u) (fun _ => h) (fun _ => h) ≤
    n * (2 * Real.log 2 + mixedScalarCascade
      (fun i => mode (f ⟨N - 1 - i, by omega⟩))
      (fun i => m (f ⟨N - 1 - i, by omega⟩))
      (fun i (_ : Unit) => v (f ⟨N - 1 - i, by omega⟩)) N () ℓ (h, h) - ℓ * u) := by
  let F := constrainedPairFieldBase n (0 : EnergySpace n) u
  let G := fun x y : Fin n → ℝ => ∑ i, coupledSite ℓ (x i) (y i)
  let c := (n : ℝ) * (2 * Real.log 2 - ℓ * u)
  have hFbase : F = constrainedBase n (0 : EnergySpace n) 0 0 u := by
    funext x y
    simpa only [Real.sqrt_zero, Real.sqrt_one, zero_smul, zero_mul, one_mul,
      add_zero, sub_zero] using (constrainedBase_eq_pairFieldBase n (0 : EnergySpace n) 0 0 u x y).symm
  have hF : CoupledGrowth F := by
    rw [hFbase]
    exact constrainedBase_growth (0 : EnergySpace n) 0 u ⟨le_rfl, zero_le_one⟩ hu
  have hG : CoupledGrowth G := coupledSite_sum_growth n ℓ
  have H := mixedVectorListCascade_mono mode m v (List.ofFn f)
    (fun a _ => hm a) (fun a _ => hv a) hF (hG.const_add c)
    (fun x y => by
      rw [hFbase]
      simpa only [add_zero] using constrainedBase_time_zero_le hn (0 : EnergySpace n) 0 u ℓ hu x y)
    (fun _ => h) (fun _ => h)
  rw [mixedVectorListCascade_const_add mode m v (List.ofFn f)
    (fun a _ => hm a) (fun a _ => hv a) c hG,
    mixedVectorListCascade_ofFn n hN mode m v f G] at H
  have Hsum := mixedVectorCascade_eq_sum n
    (fun i => mode (f ⟨N - 1 - i, by omega⟩))
    (fun i => m (f ⟨N - 1 - i, by omega⟩))
    (fun i (_ : Unit) => v (f ⟨N - 1 - i, by omega⟩))
    (fun i => hm _) (fun _ => continuous_const) N () ℓ (fun _ => h) (fun _ => h)
  rw [Hsum] at H
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
  convert H using 1
  dsimp [c]
  ring

/-- At zero second time the disorder has actually disappeared from the
definition, leaving the deterministic tagged Gaussian cascade. -/
theorem section5InterleavedInterpolation_zero_eq {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r j : ℕ) (t u : ℝ) :
    section5InterleavedInterpolation n s β h U r j t u 0 =
      (1 / (n : ℝ)) * mixedVectorListCascade n (section5TaggedMode r j (decide (u < 0)))
        (section5TaggedMass s r j) (section5TaggedVariance s β t |u| j)
        (List.ofFn (section5Interleaving s r j))
        (constrainedPairFieldBase n (0 : EnergySpace n) u) (fun _ => h) (fun _ => h) := by
  simp only [section5InterleavedInterpolation, zero_mul, Real.sqrt_zero, zero_smul,
    section5TaggedPathVariance_zero, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- The actual zero-time interpolation endpoint is bounded by the genuine
mixed scalar lambda family. Both signs retain the original external fields,
and the normalization is precisely `2 log 2`; no derivative inequality enters. -/
theorem section5InterleavedInterpolation_zero_le_lambda {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) (ℓ : ℝ) :
    section5InterleavedInterpolation n s β h U r j t u 0 ≤
      2 * Real.log 2 + section5InterleavedScalarV s β h r j t u ℓ - ℓ * u := by
  have H := mixedVectorListCascade_constrained_zero_le hn
    (show 0 < (k + 2) + (k + 3) by omega)
    (section5TaggedMode r j (decide (u < 0)))
    (section5TaggedMass s r j) (section5TaggedVariance s β t |u| j)
    (fun tag => (section5TaggedMass_mem_Icc s r hj tag).1)
    (section5TaggedVariance_nonneg s β ht hj hu)
    (section5Interleaving s r j) u ℓ h hatt
  change mixedVectorListCascade n (section5TaggedMode r j (decide (u < 0)))
      (section5TaggedMass s r j) (section5TaggedVariance s β t |u| j)
      (List.ofFn (section5Interleaving s r j)) (constrainedPairFieldBase n (0 : EnergySpace n) u)
      (fun _ => h) (fun _ => h) ≤
    n * (2 * Real.log 2 + section5InterleavedScalarV s β h r j t u ℓ - ℓ * u) at H
  rw [section5InterleavedInterpolation_zero_eq]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have H' := mul_le_mul_of_nonneg_left H (one_div_nonneg.mpr hnR.le)
  simpa only [one_div, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul] using H'

/-- The zero-lambda endpoint needed for the strict interleaved comparison. -/
theorem section5InterleavedInterpolation_zero_le {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ} (hn : 0 < n) (s : RSBScheme k)
    (β h : ℝ) (U : Ω → EnergySpace n) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolation n s β h U r j t u 0 ≤
      2 * Real.log 2 + section5InterleavedScalarV s β h r j t u 0 := by
  simpa only [zero_mul, sub_zero] using
    section5InterleavedInterpolation_zero_le_lambda hn s β h U r hj ht hu hatt 0

end SpinGlass.Targets
