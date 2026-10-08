module

public import Targets.MixedCascadeContinuity

@[expose] public section

/-!
# Closed-interval continuity of Proposition 5.7's mixed free energy

The bound for the disorder average comes from the actual mixed cascade's
contraction, not an assumed continuity of the pressure. Frozen and moving
variances, both overlap signs, and all zero faces are retained.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open PhysLean.Probability.GaussianIBP

namespace SpinGlass.Targets

variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem integrable_mixedConstrainedList_amplitude {α : Type*}
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) (a u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ b ∈ l, 0 ≤ m b) (hv : ∀ b ∈ l, 0 ≤ v b) (x y : Fin n → ℝ) :
    Integrable (fun ω => mixedVectorListCascade n mode m v l
      (constrainedPairFieldBase n (a • Z ω) u) x y) ℙ := by
  let F := fun U => mixedVectorListCascade n mode m v l (constrainedPairFieldBase n U u) x y
  apply integrable_comp_of_affine_norm_bound hZ
    ((continuous_mixedConstrainedList_disorder mode m v l hm hv u x y).measurable.comp
      (show Measurable (fun U : EnergySpace n => a • U) by fun_prop))
    (C := |F 0|) (D := 2 * Fintype.card (Config n) * |a|) (abs_nonneg _) (by positivity)
  intro U
  have H := mixedConstrainedList_disorder_dist_le mode m v l hm hv (a • U) 0 u x y
  have Hb := uAbs_le_card_mul_norm n (a • U)
  simp only [sub_zero] at H
  simp only [norm_smul, Real.norm_eq_abs] at Hb
  have Ht := abs_add_le (F (a • U) - F 0) (F 0)
  rw [sub_add_cancel] at Ht
  change |F (a • U) - F 0| ≤ _ at H
  change |F (a • U)| ≤ _
  nlinarith

/-- Simultaneous continuous variation of every visited mixed variance,
disorder amplitude and physical field survives the actual Gaussian average. -/
theorem continuousOn_mixedConstrainedGaussian_path
    {P α : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] {S : Set P} (hS : IsCompact S)
    (a : P → ℝ) (ha : ContinuousOn a S)
    (mode : α → Section5GaussianMode) (m : α → ℝ) (v : α → P → ℝ) (l : List α)
    (hm : ∀ b ∈ l, 0 ≤ m b) (hvc : ∀ b ∈ l, ContinuousOn (v b) S)
    (hv : ∀ b ∈ l, ∀ z ∈ S, 0 ≤ v b z)
    (x y : P → Fin n → ℝ) (hx : ContinuousOn x S) (hy : ContinuousOn y S) :
    ContinuousOn (fun z => ∫ ω, mixedVectorListCascade n mode m (fun b => v b z) l
      (constrainedPairFieldBase n (a z • Z ω) u) (x z) (y z) ∂ℙ) S := by
  let F := fun (U : EnergySpace n) z => mixedVectorListCascade n mode m (fun b => v b z) l
    (constrainedPairFieldBase n (a z • U) u) (x z) (y z)
  have hF (U : EnergySpace n) : ContinuousOn (F U) S := by
    exact ((coupledContinuousOn_constrainedPairFieldBase u hS
      (ha.smul continuousOn_const)).mixedList hS mode m v l hm hvc hv).continuous x y hx hy
  obtain ⟨C, hC⟩ := hS.bddAbove_image (hF 0).abs
  obtain ⟨A, hA⟩ := hS.bddAbove_image ha.abs
  apply continuousOn_of_dominated
    (bound := fun ω => C + (2 * |A| * Fintype.card (Config n)) * ‖Z ω‖)
  · intro z hz
    exact ((continuous_mixedConstrainedList_disorder mode m (fun b => v b z) l hm
      (fun b hb => hv b hb z hz) u (x z) (y z)).measurable.comp
        (hZ.repr_measurable.const_smul (a z))).aestronglyMeasurable
  · intro z hz
    filter_upwards with ω
    have H := mixedConstrainedList_disorder_dist_le mode m (fun b => v b z) l hm
      (fun b hb => hv b hb z hz) (a z • Z ω) 0 u (x z) (y z)
    simp only [sub_zero] at H
    have HN := uAbs_le_card_mul_norm n (a z • Z ω)
    rw [norm_smul, Real.norm_eq_abs] at HN
    have HA : |a z| ≤ |A| := (hA (Set.mem_image_of_mem _ hz)).trans (le_abs_self _)
    have H0 : |F 0 z| ≤ C := hC (Set.mem_image_of_mem _ hz)
    have HT := abs_sub_le (F (Z ω) z) (F 0 z) 0
    simp only [sub_zero] at HT
    have HD : |F (Z ω) z - F 0 z| ≤ 2 * uAbs n (a z • Z ω) := by
      simpa only [F, smul_zero] using H
    rw [Real.norm_eq_abs]
    change |F (Z ω) z| ≤ _
    nlinarith [mul_le_mul_of_nonneg_right HA (norm_nonneg (Z ω)),
      mul_nonneg (show 0 ≤ (Fintype.card (Config n) : ℝ) by positivity)
        (show 0 ≤ (|A| - |a z|) * ‖Z ω‖ from mul_nonneg (sub_nonneg.mpr HA) (norm_nonneg _))]
  · exact (integrable_const C).add ((integrable_norm_of_gaussian hZ).const_mul _)
  · exact Eventually.of_forall fun ω => hF (Z ω)

/-- The actual mixed second interpolation is continuous on the whole closed
interval, for either overlap sign and without strictly positive variances. -/
theorem continuousOn_section5InterleavedInterpolation {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    {t u : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (section5InterleavedInterpolation n s β h Z r j t u) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_mixedConstrainedGaussian_path (S := Set.Icc (0 : ℝ) 1) hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (section5TaggedMode r j (decide (u < 0))) (section5TaggedMass s r j)
    (fun tag w => section5TaggedPathVariance s β t |u| j w tag)
    (List.ofFn (section5Interleaving s r j))
    (fun tag _ => (section5TaggedMass_mem_Icc s r hj tag).1)
    (fun tag _ => by cases tag <;> dsimp [section5TaggedPathVariance] <;> fun_prop)
    (fun tag _ w hw => section5TaggedPathVariance_nonneg s β ht hj hu hw.2 tag)
    (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

end SpinGlass.Targets
