module

public import Paper.ReplicaSymmetry
public import Paper.ParisiJT
public import Paper.ATSmoothGraph
public import Paper.ParisiPDEWellPosed
public import Paper.ParisiPDEFormula
public import Paper.ParisiDiracIdentification
public import Paper.ParisiSelectedMoment
public import Paper.DiracMagnetization

@[expose] public section

/-!
# The fifteen numbered statements of arXiv:2604.11921v2

Each `Statement_*` is a proposition about the actual model, constructed weak
PDE solution, or constructed Brownian state. Each `result_*` below is a closed
proof of that proposition: no Parisi formula, PDE regularity, stochastic law,
or variational identity is supplied as an additional mathematical premise.

The statements inherit the paper's positive-temperature convention. The
time derivatives in Proposition 2.1 are distributional derivatives; arbitrary
atomic CDFs do not give a globally classical time derivative. Proposition 5.4
uses the conditional expectation in the Brownian filtration, together with
the explicit measurable probability transition kernel, so it does not condition on an
event of probability zero.

All fifteen targets are paired with closed proofs. The general-measure first
variation and mixing convexity used in 2.3 and 6.2 concern the actual selected
PDE and state and have themselves been proved.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped Topology NNReal

namespace Paper.Numbered

/-- Theorem 1.1: the actual finite SK free energy converges to the RS value. -/
def Statement_1_1 : Prop := MainReplicaSymmetryTarget

theorem result_1_1 : Statement_1_1 := replicaSymmetry_via_parisiPDE

/-- Proposition 1.2: the exact AT boundary is the stated smooth increasing graph. -/
def Statement_1_2 : Prop := SmoothATBoundaryTarget

theorem result_1_2 : Statement_1_2 := smoothATBoundary

/-- Proposition 2.1: original weak-class uniqueness and all stated regularity. -/
def Statement_2_1 : Prop :=
  ∀ β : ℝ, 0 < β → ∀ μ : ParisiMeasure, ParisiPDEWellPosedTarget β μ

theorem result_2_1 : Statement_2_1 :=
  fun β hβ μ => parisiPDE_wellPosed β hβ.ne' μ

/-- Theorem 2.2: the limit equals the infimum over all actual probability laws. -/
def Statement_2_2 : Prop :=
  ∀ β h : ℝ, 0 < β →
    Tendsto (finiteSKFreeEnergy β h) atTop (𝓝 (parisiPDEValue β h))

theorem result_2_2 : Statement_2_2 := physicalParisiFormula

/-- Proposition 2.3: minimizers of the actual PDE functional are characterized
by the topological support and actual state-based first-variation observable. -/
def Statement_2_3 : Prop :=
  ∀ β h : ℝ, ∀ hβ : 0 < β, ∀ μ : ParisiMeasure,
    (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) ↔
      (μ : Measure Overlap).support ⊆
        overlapArgmin (fun q => selectedParisiG β h hβ.ne' μ q)

theorem result_2_3 : Statement_2_3 :=
  fun β h hβ μ => parisiJT_support_criterion β h hβ.ne' μ

/-- Proposition 3.1: actual Dirac PDE and strong state, including both interface
values and the exact Gaussian law. No fixed-point or AT hypothesis is needed. -/
def Statement_3_1 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, ∀ hq : q ∈ Icc (0 : ℝ) 1,
    (∀ t ∈ Icc q (1 : ℝ), ∀ x,
      parisiPotential β (diracOverlap q hq) (t, x) = rsHardPotential β t x ∧
      parisiGradient β (diracOverlap q hq) (t, x) = Real.tanh x ∧
      parisiHessian β (diracOverlap q hq) (t, x) = sech x ^ 2) ∧
    (∀ t ∈ Icc (0 : ℝ) q, ∀ x,
      parisiPotential β (diracOverlap q hq) (t, x) = rsSoftPotential β q t x) ∧
    (∀ ω t, t ∈ Icc (0 : ℝ) q →
      selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t =
        h + β * canonicalBrownian t.toNNReal ω) ∧
    (∀ ω t, t ∈ Icc q (1 : ℝ) →
      selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω t =
        h + β * canonicalBrownian t.toNNReal ω +
          ∫ s in q..t, β ^ 2 * Real.tanh
            (selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω s)) ∧
    HasLaw (fun ω => selectedParisiStateReal β h hβ.ne' (diracOverlap q hq) ω q)
      (gaussianReal h (β ^ 2 * q).toNNReal) canonicalBrownianMeasure

theorem result_3_1 : Statement_3_1 := by
  intro β h q hβ hq
  refine ⟨?_, ?_, ?_, ?_, hasLaw_selectedParisiState_dirac_interface β h q hβ hq⟩
  · intro t ht x
    exact ⟨parisiPotential_dirac_hard β q hβ hq t x ht,
      parisiGradient_dirac_hard β q hβ hq t x ht,
      parisiHessian_dirac_hard β q hβ hq t x ht⟩
  · exact fun t ht x => parisiPotential_dirac_soft β q hβ hq t x ht
  · exact fun ω t ht => selectedParisiState_dirac_before β h q hβ hq ω ht
  · exact fun ω t ht => selectedParisiState_dirac_after β h q hβ hq ω ht

/-- Proposition 4.1: the precise quantitative lower bound for the actual
general-PDE Dirac observable, including the equality AT boundary. -/
def Statement_4_1 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → atParameter β h q ≤ 1 →
    ∀ t ∈ Icc (0 : ℝ) q,
      0 ≤ (1 - atParameter β h q) * (q - t) ∧
        (1 - atParameter β h q) * (q - t) ≤
          selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t - t

theorem result_4_1 : Statement_4_1 := by
  intro β h q hβ hq hfixed hAT t ht
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨ht.1, ht.2.trans hq.2⟩,
    physicalRSSecondMoment_eq β h q hq hβ.le ⟨ht.1, ht.2.trans hq.2⟩,
    rsSecondMoment_eq_soft ht.2]
  exact softSecondMoment_left_quantitative hβ.le ht hfixed hAT

/-- The actual selected general process is the constructed Dirac process on
the physical strip. This prevents the stochastic wrappers from using a
separate, unidentified process. -/
theorem selectedIto_dirac_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) (ω : BrownianSample) :
    selectedParisiItoState β h hβ.ne' (diracOverlap q hq) t ω =
      canonicalDiracItoState β h q hq t ω := by
  rw [selectedParisiItoState_eq β h hβ.ne' (diracOverlap q hq) ht ω,
    selectedParisiState_dirac_eq β h q hβ hq ω ⟨t.coe_nonneg, ht⟩,
    canonicalDiracItoState_eq β h q hq ht ω]

/-- Genuine left sums with the paper's coefficient `β(1-m²)` and the actual
selected state, rather than an abstract supplied stochastic integral. -/
def selectedMagnetizationLeftSum (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0) (n : ℕ) (ω : BrownianSample) : ℝ :=
  ∑ i ∈ Finset.range n,
    β * (1 - Real.tanh (selectedParisiItoState β h hβ.ne' (diracOverlap q hq)
      (a + uniformPartitionTime T n i) ω) ^ 2) *
    (canonicalBrownian (a + uniformPartitionTime T n (i + 1)) ω -
      canonicalBrownian (a + uniformPartitionTime T n i) ω)

def selectedMagnetizationIncrement (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0) (ω : BrownianSample) : ℝ :=
  Real.tanh (selectedParisiItoState β h hβ.ne' (diracOverlap q hq) (a + T) ω) -
    Real.tanh (selectedParisiItoState β h hβ.ne' (diracOverlap q hq) a ω)

def selectedDiracFourthMoment (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) : ℝ :=
  ∫ ω, (1 - Real.tanh (selectedParisiStateReal β h hβ.ne'
    (diracOverlap q hq) ω t) ^ 2) ^ 2 ∂canonicalBrownianMeasure

theorem selectedDiracFourthMoment_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    selectedDiracFourthMoment β h q hβ hq t = hardFourthMoment β h q t := by
  rw [← physicalHardFourthMoment_eq β h q hq ht]
  unfold selectedDiracFourthMoment physicalHardFourthMoment
  apply integral_congr_ae
  exact .of_forall fun ω => by
    dsimp only
    rw [selectedParisiState_dirac_eq β h q hβ hq ω ⟨hq.1.trans ht.1, ht.2⟩]
    have he : 1 - Real.tanh (canonicalDiracStateReal β h q hq ω t) ^ 2 =
        sech (canonicalDiracStateReal β h q hq ω t) ^ 2 := by
      linarith [tanh_sq_add_sech_sq (canonicalDiracStateReal β h q hq ω t)]
    rw [he]
    ring

theorem selectedMagnetizationLeftSum_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0) (haT : (a : ℝ) + T ≤ 1)
    {n : ℕ} (hn : 0 < n) (ω : BrownianSample) :
    selectedMagnetizationLeftSum β h q hβ hq a T n ω =
      canonicalMagnetizationItoApprox β h q hq a T n ω := by
  unfold selectedMagnetizationLeftSum canonicalMagnetizationItoApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hpart := (uniformPartitionTime_mem_Icc_of_le T hn
    (Nat.le_of_lt (Finset.mem_range.mp hi))).2
  have htime : ((a + uniformPartitionTime T n i : ℝ≥0) : ℝ) ≤ 1 := by
    rw [NNReal.coe_add]
    exact (add_le_add le_rfl (NNReal.coe_le_coe.mpr hpart)).trans haT
  rw [selectedIto_dirac_eq β h q hβ hq htime ω]
  have he : 1 - Real.tanh (canonicalDiracItoState β h q hq
      (a + uniformPartitionTime T n i) ω) ^ 2 =
      sech (canonicalDiracItoState β h q hq (a + uniformPartitionTime T n i) ω) ^ 2 := by
    linarith [tanh_sq_add_sech_sq (canonicalDiracItoState β h q hq
      (a + uniformPartitionTime T n i) ω)]
  rw [he]

theorem selectedMagnetizationIncrement_eq (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) (a T : ℝ≥0) (haT : (a : ℝ) + T ≤ 1) :
    selectedMagnetizationIncrement β h q hβ hq a T =
      canonicalMagnetizationItoIntegral β h q hq a T := by
  funext ω
  unfold selectedMagnetizationIncrement canonicalMagnetizationItoIntegral
  rw [selectedIto_dirac_eq β h q hβ hq (by simpa only [NNReal.coe_add] using haT) ω,
    selectedIto_dirac_eq β h q hβ hq ((le_add_of_nonneg_right T.coe_nonneg).trans haT) ω]

theorem selectedDiracMoment_eq_hard (β h q : ℝ) (hβ : 0 < β)
    (hq : q ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t =
      hardSecondMoment β h q t := by
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩,
    physicalRSSecondMoment_eq β h q hq hβ.le ⟨hq.1.trans ht.1, ht.2⟩,
    rsSecondMoment_eq_hard_of_le hq.1 ht.1]

/-- Proposition 5.1: genuine Brownian left-sum stochastic equation, literal
second-moment derivative on the closed interval, initial fixed-point value,
and the two endpoint derivatives in their correct one-sided senses. -/
def Statement_5_1 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q →
    (∀ a T : ℝ≥0, q ≤ (a : ℝ) → (a : ℝ) + T ≤ 1 →
      TendstoInMeasure canonicalBrownianMeasure
        (fun n => selectedMagnetizationLeftSum β h q hβ hq a T (n + 1)) atTop
        (selectedMagnetizationIncrement β h q hβ hq a T)) ∧
    (∀ t ∈ Icc q (1 : ℝ),
      HasDerivWithinAt (selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq))
        (β ^ 2 * selectedDiracFourthMoment β h q hβ hq t) (Icc q (1 : ℝ)) t) ∧
    selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) q = q ∧
    HasDerivWithinAt (selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq))
      (atParameter β h q) (Ici q) q ∧
    HasDerivWithinAt (selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq))
      (β ^ 2 * selectedDiracFourthMoment β h q hβ hq 1) (Iic 1) 1

theorem result_5_1 : Statement_5_1 := by
  intro β h q hβ hq hfixed
  have he : EqOn (selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq))
      (hardSecondMoment β h q) (Icc q (1 : ℝ)) :=
    fun t ht => selectedDiracMoment_eq_hard β h q hβ hq ht
  have hqone : q < 1 := fixedPoint_lt_one hfixed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a T hqa haT
    rw [selectedMagnetizationIncrement_eq β h q hβ hq a T haT]
    have hl := canonicalMagnetizationItoApprox_tendstoInMeasure β h q hq a T hqa haT
    apply hl.congr
    · intro n
      exact .of_forall fun ω => (selectedMagnetizationLeftSum_eq β h q hβ hq a T haT
        (Nat.succ_pos n) ω).symm
    · exact .of_forall fun _ => rfl
  · intro t ht
    rw [selectedDiracFourthMoment_eq β h q hβ hq ht]
    exact ((hasDerivWithinAt_hardSecondMoment_closed β h q ht.1).mono
      (fun _ hs => hs.1)).congr_of_mem (fun s hs => he hs) ht
  · rw [he ⟨le_rfl, hq.2⟩]
    exact hardSecondMoment_initial_fixed hq.1 hfixed
  · simpa only [hardFourthMoment_initial hq.1] using
      hasDerivWithinAt_physicalMoment_interface hqone he
  · rw [selectedDiracFourthMoment_eq β h q hβ hq ⟨hq.2, le_rfl⟩]
    exact hasDerivWithinAt_physicalMoment_terminal hqone he

/-- Proposition 5.2: the small-complement regime, with no AT premise. -/
def Statement_5_2 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → β ^ 2 * (1 - q) ≤ 1 →
    ∀ t ∈ Icc q (1 : ℝ),
      selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t ≤ t

theorem result_5_2 : Statement_5_2 := by
  intro β h q hβ hq hfixed hsmall t ht
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩]
  exact physicalRSSecondMoment_right_of_small_variance hβ hq hfixed hsmall ht

/-- Proposition 5.3: the structural field inequality, without an AT premise. -/
def Statement_5_3 : Prop :=
  ∀ β h q : ℝ, 0 < h → q ∈ Icc (0 : ℝ) 1 →
    q = overlapMap β h q → 1 < β ^ 2 * (1 - q) → h < β ^ 2 * q

theorem result_5_3 : Statement_5_3 :=
  fun _ _ _ hh hq hfixed hlarge => fixedPoint_structural_field_lt hh hq.1 hfixed hlarge

theorem doobOperator_eq_heatSemigroup (lam : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ) (x : ℝ) :
    doobOperator lam ψ x = Real.exp (-(lam : ℝ) / 2) / Real.cosh x *
      heatSemigroup lam (fun y => Real.cosh y * ψ y) x := by
  rw [heatSemigroup_eq_gaussian_integral (lam : ℝ) lam.coe_nonneg
    (fun y => Real.cosh y * ψ y) (Real.continuous_cosh.measurable.mul hψ),
    Real.toNNReal_coe]
  rfl

/-- Proposition 5.4: the actual selected state has the normalized cosh-Gaussian
conditional transition operator. The formula includes elapsed time zero. -/
def Statement_5_4 : Prop :=
  (∀ lam : ℝ≥0, IsMarkovKernel (coshStateKernel lam) ∧
    ∀ ψ : ℝ → ℝ, Measurable ψ → ∀ x : ℝ,
      (∫ y, ψ y ∂coshStateKernel lam x) =
        Real.exp (-(lam : ℝ) / 2) / Real.cosh x *
          heatSemigroup lam (fun y => Real.cosh y * ψ y) x) ∧
  ∀ β h q : ℝ, ∀ hβ : 0 < β, ∀ hq : q ∈ Icc (0 : ℝ) 1,
    ∀ a T : ℝ≥0, q ≤ (a : ℝ) → (a : ℝ) + T ≤ 1 →
    ∀ ψ : ℝ → ℝ, Measurable ψ → ∀ M : ℝ, (∀ x, ‖ψ x‖ ≤ M) →
      canonicalBrownianMeasure[(fun ω => ψ (selectedParisiItoState β h hβ.ne'
        (diracOverlap q hq) (a + T) ω)) | canonicalBrownianFiltration a] =ᵐ[canonicalBrownianMeasure]
        fun ω => Real.exp (-(β ^ 2 * (T : ℝ)) / 2) /
          Real.cosh (selectedParisiItoState β h hβ.ne' (diracOverlap q hq) a ω) *
          heatSemigroup (β ^ 2 * (T : ℝ)) (fun y => Real.cosh y * ψ y)
            (selectedParisiItoState β h hβ.ne' (diracOverlap q hq) a ω)

theorem result_5_4 : Statement_5_4 := by
  refine ⟨?_, ?_⟩
  · intro lam
    refine ⟨inferInstance, ?_⟩
    intro ψ hψ x
    rw [integral_coshStateKernel, doobOperator_eq_heatSemigroup lam ψ hψ]
  intro β h q hβ hq a T hqa haT ψ hψ M hM
  have ht : ((a + T : ℝ≥0) : ℝ) ≤ 1 := by simpa only [NNReal.coe_add] using haT
  have ha : (a : ℝ) ≤ 1 := (le_add_of_nonneg_right T.coe_nonneg).trans haT
  have he0 : selectedParisiItoState β h hβ.ne' (diracOverlap q hq) a =
      canonicalDiracItoState β h q hq a := funext (selectedIto_dirac_eq β h q hβ hq ha)
  have he1 : selectedParisiItoState β h hβ.ne' (diracOverlap q hq) (a + T) =
      canonicalDiracItoState β h q hq (a + T) := funext (selectedIto_dirac_eq β h q hβ hq ht)
  rw [he0, he1]
  have hl := condExp_canonicalDiracItoState_after β h q hq a T hqa haT ψ hψ M hM
  have hlam : 0 ≤ β ^ 2 * (T : ℝ) := mul_nonneg (sq_nonneg β) T.coe_nonneg
  simpa only [doobOperator_eq_heatSemigroup _ ψ hψ, Real.coe_toNNReal _ hlam] using hl

/-- Proposition 5.5: actual small-field right bound and its strictness after q. -/
def Statement_5_5 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, 0 < h → ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → atParameter β h q ≤ 1 → h ≤ β ^ 2 * q →
    (∀ t ∈ Icc q (1 : ℝ),
      selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t ≤ t) ∧
    (∀ t ∈ Ioc q (1 : ℝ),
      selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t < t)

theorem result_5_5 : Statement_5_5 := by
  intro β h q hβ hh hq hfixed hAT hfield
  constructor
  · intro t ht
    rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩]
    exact physicalRSSecondMoment_right_sign hβ hh hq hfixed hAT ht
  · intro t ht
    rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1.le, ht.2⟩]
    exact physicalRSSecondMoment_right_strict_of_small_field hβ hh hq hfixed hAT hfield ht

/-- Proposition 5.6: the complete actual Dirac moment bound after q. -/
def Statement_5_6 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, 0 < h → ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → atParameter β h q ≤ 1 →
    ∀ t ∈ Icc q (1 : ℝ),
      selectedParisiSecondMoment β h hβ.ne' (diracOverlap q hq) t ≤ t

theorem result_5_6 : Statement_5_6 := by
  intro β h q hβ hh hq hfixed hAT t ht
  rw [selectedParisiSecondMoment_dirac_eq β h q hβ hq ⟨hq.1.trans ht.1, ht.2⟩]
  exact physicalRSSecondMoment_right_sign hβ hh hq hfixed hAT ht

/-- Proposition 6.1: the actual general-measure G at δq is minimized at q. -/
def Statement_6_1 : Prop :=
  ∀ β h q : ℝ, ∀ hβ : 0 < β, 0 < h → ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → atParameter β h q ≤ 1 →
    ∀ t ∈ Icc (0 : ℝ) 1,
      selectedParisiG β h hβ.ne' (diracOverlap q hq) q ≤
        selectedParisiG β h hβ.ne' (diracOverlap q hq) t

theorem result_6_1 : Statement_6_1 :=
  fun _ _ _ hβ hh hq hfixed hAT => selectedParisiG_dirac_minimum hβ hh hq hfixed hAT

/-- Remark 6.2: δq is a minimizer, and every actual PDE-functional minimizer
equals it. This asserts existence and uniqueness, not merely a conditional
deduction from a supplied uniqueness theorem. -/
def Statement_6_2 : Prop :=
  ∀ β h q : ℝ, 0 < β → 0 < h → ∀ hq : q ∈ Icc (0 : ℝ) 1,
    q = overlapMap β h q → atParameter β h q ≤ 1 →
    (∀ ν : ParisiMeasure,
      parisiPDEFunctional β h (diracOverlap q hq) ≤ parisiPDEFunctional β h ν) ∧
    ∀ μ : ParisiMeasure,
      (∀ ν : ParisiMeasure, parisiPDEFunctional β h μ ≤ parisiPDEFunctional β h ν) →
        μ = diracOverlap q hq

theorem result_6_2 : Statement_6_2 :=
  fun _ _ _ hβ hh hq hfixed hAT => parisiUniqueDirac hβ hh hq hfixed hAT

end Paper.Numbered
