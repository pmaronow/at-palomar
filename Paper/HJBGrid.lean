module

public import Paper.HJBGridCells
public import Paper.ControlCostIntegrability
public import Paper.ParisiFiniteApproximation
public import Paper.ItoStateIntegrability

@[expose] public section

/-! # Verified control bounds on the whole finite Parisi grid

Every Cole--Hopf cell is verified on the same actual controlled state.
Finite telescoping preserves the genuine running cost and CDF approximation
error. No convergence of state processes is required.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal
namespace Paper

/-- Global finite-grid bounds, with all cost and endpoint integrability
proved from the actual characteristics and bounded measurable control. -/
theorem hjbGrid_control_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (μ ν : ParisiMeasure) (n : ℕ)
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A))
    (hA : ∀ r ω, ‖A r ω‖ ≤ 1)
    (hd : ∀ ω, ∀ r ∈ Icc (0 : ℝ) 1, d r.toNNReal ω = β ^ 2 * parisiCDF μ r * A r ω)
    (hi0 : Integrable (X 0) P) {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ ω, ∀ r ∈ Icc (0 : ℝ) 1,
      ‖A r ω - parisiFiniteGradient (parisiGridRSBScheme ν n) β (r, X r.toNNReal ω)‖ ≤ eps) :
    let initial := ∫ ω, parisiFinitePotential (parisiGridRSBScheme ν n) β (0, X 0 ω) ∂P
    let payoff := (∫ ω, Real.log (Real.cosh (X 1 ω)) ∂P) -
      (∫ ω, parisiControlCost β μ A ω ∂P)
    let error := (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n)
    payoff ≤ initial + error ∧ initial - error - β ^ 2 / 2 * eps ^ 2 ≤ payoff := by
  let C := parisiInstantControlCost β μ A
  let E := hjbGridCoefficientError β μ ν n
  let T := hjbGridTime n
  let F := fun j => ∫ ω, parisiFinitePotential (parisiGridRSBScheme ν n) β
    (T j, X (T j).toNNReal ω) ∂P
  have ht : ∀ ω i, i < n + 1 → IntervalIntegrable (fun t => C t ω) volume (T i) (T (i + 1)) :=
    fun ω i _ => intervalIntegrable_parisiInstantControlCost β μ A hAm hA _ _ ω
  have hi : ∀ i, i < n + 1 → Integrable (fun ω => ∫ t in T i..T (i + 1), C t ω) P :=
    fun i _ => integrable_parisiInstantControlCost_integral P β μ A hAm hA _ _
      (hjbGridTime_step_lt n i).le
  have hE : ∀ i, i < n + 1 → IntervalIntegrable E volume (T i) (T (i + 1)) :=
    fun i _ => hjbGridCoefficientError_intervalIntegrable β μ ν n _ _
  have hcell (i : ℕ) (hiN : i < n + 1) :=
    hjbGrid_cell_control_error_bounds hc hβ μ ν n i hiN A hA hd
      (by simpa only [C, parisiInstantControlCost] using fun ω => ht ω i hiN)
      (by simpa only [C, parisiInstantControlCost] using hi i hiN)
      (hc.integrable_state hi0 _) (hc.integrable_state hi0 _) heps hclose
  have hupper := hjb_expected_cells_telescope_upper P C E T (n + 1) F ht hi hE
    (fun i hiN => (hcell i hiN).1)
  have hlower := hjb_expected_cells_telescope_lower P C E T (n + 1) F (β ^ 2 / 2 * eps ^ 2)
    ht hi hE (fun i hiN => (hcell i hiN).2)
  have hT0 : T 0 = 0 := by simp [T, hjbGridTime]
  have hTN : T (n + 1) = 1 := by
    dsimp [T, hjbGridTime]
    exact div_self (by positivity)
  have hcost : hjbExpectedCost P C 0 1 = ∫ ω, parisiControlCost β μ A ω ∂P := by
    unfold hjbExpectedCost
    apply integral_congr_ae
    exact .of_forall fun ω => parisiInstantControlCost_integral_eq_cost β μ A ω
  have herr : (∫ t in (0 : ℝ)..1, E t) =
      (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n) := by
    unfold E hjbGridCoefficientError parisiCDFDistance
    rw [intervalIntegral.integral_const_mul]
    simp only [Real.norm_eq_abs]
  have hF0 : F 0 = ∫ ω, parisiFinitePotential (parisiGridRSBScheme ν n) β (0, X 0 ω) ∂P := by
    dsimp only [F]
    simp only [hT0, Real.toNNReal_zero]
  have hFN : F (n + 1) = ∫ ω, Real.log (Real.cosh (X 1 ω)) ∂P := by
    dsimp only [F]
    simp only [hTN, Real.toNNReal_one, parisiFinitePotential_terminal]
  rw [hT0, hTN, hF0, hFN, hcost, herr] at hupper hlower
  dsimp only
  constructor
  · exact hupper
  · simpa only [sub_zero, mul_one] using hlower

/-- Arbitrary bounded controls satisfy the grid upper bound; the proximity
premise of the two-sided theorem is discharged by the sharp unit bounds. -/
theorem hjbGrid_control_upper {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (μ ν : ParisiMeasure) (n : ℕ)
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A))
    (hA : ∀ r ω, ‖A r ω‖ ≤ 1)
    (hd : ∀ ω, ∀ r ∈ Icc (0 : ℝ) 1, d r.toNNReal ω = β ^ 2 * parisiCDF μ r * A r ω)
    (hi0 : Integrable (X 0) P) :
    (∫ ω, Real.log (Real.cosh (X 1 ω)) ∂P) - (∫ ω, parisiControlCost β μ A ω ∂P) ≤
      (∫ ω, parisiFinitePotential (parisiGridRSBScheme ν n) β (0, X 0 ω) ∂P) +
        (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n) := by
  exact (hjbGrid_control_error_bounds hc hβ μ ν n A hAm hA hd hi0
    (by norm_num : (0 : ℝ) ≤ 2) (fun ω r _ =>
      (norm_sub_le _ _).trans (by
        have hh := norm_parisiFiniteGradient_le_one (parisiGridRSBScheme ν n) β (r, X r.toNNReal ω)
        have ha := hA r ω
        linarith))).1

end Paper
