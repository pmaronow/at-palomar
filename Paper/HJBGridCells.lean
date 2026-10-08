module

public import Paper.HJBOptimal
public import Paper.HJBGridTelescope
public import Paper.ParisiFiniteCells

@[expose] public section

/-! Actual uniform-grid HJB cell bounds. The rounded CDF and glued finite
potential are identified with their genuine Cole--Hopf cell on both closed
endpoints. The deterministic coefficient error is the actual CDF difference,
including laws with atoms and duplicated end levels. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real StochasticCalculus
open scoped NNReal

namespace Paper
open SpinGlass SpinGlass.Targets

def hjbGridTime (n i : ℕ) : ℝ := (i : ℝ) / (n + 1 : ℕ)

theorem hjbGridTime_nonneg (n i : ℕ) : 0 ≤ hjbGridTime n i := by
  unfold hjbGridTime
  positivity

theorem hjbGridTime_step_lt (n i : ℕ) : hjbGridTime n i < hjbGridTime n (i + 1) := by
  unfold hjbGridTime
  apply div_lt_div_of_pos_right _ (by positivity)
  exact_mod_cast Nat.lt_succ_self i

theorem hjbGridTime_le_one (n i : ℕ) (hi : i ≤ n + 1) : hjbGridTime n i ≤ 1 := by
  unfold hjbGridTime
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast hi

@[simp] theorem coe_hjbGridTime_toNNReal (n i : ℕ) :
    ((hjbGridTime n i).toNNReal : ℝ) = hjbGridTime n i :=
  Real.coe_toNNReal _ (hjbGridTime_nonneg n i)

theorem hjbGrid_cell_q (ν : ParisiMeasure) (n i : ℕ) (hi : i < n + 1) :
    (parisiGridRSBScheme ν n).q (i + 1) = hjbGridTime n i ∧
      (parisiGridRSBScheme ν n).q (i + 2) = hjbGridTime n (i + 1) := by
  constructor <;> simp [parisiGridRSBScheme, parisiGridSchemeOverlap,
    hjbGridTime, Nat.min_eq_left (by omega : i ≤ n + 1),
    Nat.min_eq_left (by omega : i + 1 ≤ n + 1)]

theorem hjbGrid_cell_potential (ν : ParisiMeasure) (n : ℕ) (β : ℝ)
    (i : ℕ) (hi : i < n + 1) (t x : ℝ)
    (ht : t ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1))) :
    parisiFinitePotential (parisiGridRSBScheme ν n) β (t, x) =
      parisiSlabPotential (parisiGridRSBScheme ν n) β (n + 1 - i)
        ((parisiGridRSBScheme ν n).m (i + 1)) (hjbGridTime n (i + 1)) t x := by
  obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q ν n i hi
  have he : (n + 1) + 1 - (i + 1) = n + 1 - i := by omega
  have hp : i + 1 ≤ (n + 1) + 1 := by omega
  have hq : (parisiGridRSBScheme ν n).q (i + 1) < (parisiGridRSBScheme ν n).q (i + 2) := by
    rw [hq0, hq1]
    exact hjbGridTime_step_lt n i
  have hcell : t ∈ Icc ((parisiGridRSBScheme ν n).q (i + 1))
      ((parisiGridRSBScheme ν n).q ((i + 1) + 1)) := by simpa [hq0, hq1] using ht
  simpa only [he, show i + 1 + 1 = i + 2 by omega, hq1] using
    parisiFinitePotential_eq_slab (parisiGridRSBScheme ν n) β hp hq hcell x

theorem hjbGrid_cell_gradient (ν : ParisiMeasure) (n : ℕ) (β : ℝ)
    (i : ℕ) (hi : i < n + 1) (t x : ℝ)
    (ht : t ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1))) :
    parisiFiniteGradient (parisiGridRSBScheme ν n) β (t, x) =
      parisiSlabGradient (parisiGridRSBScheme ν n) β (n + 1 - i)
        ((parisiGridRSBScheme ν n).m (i + 1)) (hjbGridTime n (i + 1)) t x := by
  obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q ν n i hi
  have he : (n + 1) + 1 - (i + 1) = n + 1 - i := by omega
  have hp : i + 1 ≤ (n + 1) + 1 := by omega
  have hq : (parisiGridRSBScheme ν n).q (i + 1) < (parisiGridRSBScheme ν n).q (i + 2) := by
    rw [hq0, hq1]
    exact hjbGridTime_step_lt n i
  have hcell : t ∈ Icc ((parisiGridRSBScheme ν n).q (i + 1))
      ((parisiGridRSBScheme ν n).q ((i + 1) + 1)) := by simpa [hq0, hq1] using ht
  simpa only [he, show i + 1 + 1 = i + 2 by omega, hq1] using
    parisiFiniteGradient_eq_slab (parisiGridRSBScheme ν n) β hp hq hcell x

def hjbGridCoefficientError (β : ℝ) (μ ν : ParisiMeasure) (n : ℕ) (t : ℝ) : ℝ :=
  (3 / 2 : ℝ) * β ^ 2 * ‖parisiCDF μ t - parisiCDF (parisiGridMeasure ν n) t‖

theorem hjbGridCoefficientError_intervalIntegrable (β : ℝ) (μ ν : ParisiMeasure)
    (n : ℕ) (a b : ℝ) : IntervalIntegrable (hjbGridCoefficientError β μ ν n) volume a b :=
  (((parisiCDF_monotone μ).intervalIntegrable (a := a) (b := b)).sub
    ((parisiCDF_monotone (parisiGridMeasure ν n)).intervalIntegrable (a := a) (b := b))).norm.const_mul _

theorem hjbGrid_cell_error_integral (β : ℝ) (μ ν : ParisiMeasure) (n i : ℕ)
    (hi : i < n + 1) :
    (∫ t in hjbGridTime n i..hjbGridTime n (i + 1),
      (3 / 2 : ℝ) * β ^ 2 * |parisiCDF μ t - (parisiGridRSBScheme ν n).m (i + 1)|) =
      ∫ t in hjbGridTime n i..hjbGridTime n (i + 1), hjbGridCoefficientError β μ ν n t := by
  apply intervalIntegral.integral_congr_uIoo
  rw [uIoo_of_le (hjbGridTime_step_lt n i).le]
  intro t ht
  have hcell : t ∈ Ico ((parisiGridRSBScheme ν n).q (i + 1))
      ((parisiGridRSBScheme ν n).q ((i + 1) + 1)) := by
    obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q ν n i hi
    simpa [hq0, hq1] using (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i + 1)) from ⟨ht.1.le, ht.2⟩)
  rw [hjbGridCoefficientError, Real.norm_eq_abs,
    parisiCDF_grid_eq_scheme_mass ν n (i + 1) (by omega) (by omega) hcell]

/-- Actual single-grid-cell control bounds in exactly the expected form
consumed by the finite telescope. State, drift, control and costs are genuine;
the finite potential and deterministic coefficient error are identified here. -/
theorem hjbGrid_cell_control_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (μ ν : ParisiMeasure) (n i : ℕ) (hi : i < n + 1)
    (A : ℝ → Ω → ℝ) (hA : ∀ r ω, ‖A r ω‖ ≤ 1)
    (hd : ∀ ω, ∀ r ∈ Icc (0 : ℝ) 1, d r.toNNReal ω = β ^ 2 * parisiCDF μ r * A r ω)
    (hcost : ∀ ω, IntervalIntegrable (fun r => β ^ 2 / 2 * parisiCDF μ r * A r ω ^ 2)
      volume (hjbGridTime n i) (hjbGridTime n (i + 1)))
    (hicost : Integrable (fun ω => ∫ r in hjbGridTime n i..hjbGridTime n (i + 1),
      β ^ 2 / 2 * parisiCDF μ r * A r ω ^ 2) P)
    (hXa : Integrable (X (hjbGridTime n i).toNNReal) P)
    (hXb : Integrable (X (hjbGridTime n (i + 1)).toNNReal) P)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ ω, ∀ r ∈ Icc (0 : ℝ) 1,
      ‖A r ω - parisiFiniteGradient (parisiGridRSBScheme ν n) β (r, X r.toNNReal ω)‖ ≤ eps) :
    let F := fun j => ∫ ω, parisiFinitePotential (parisiGridRSBScheme ν n) β
      (hjbGridTime n j, X (hjbGridTime n j).toNNReal ω) ∂P
    let C := hjbExpectedCost P (fun r ω => β ^ 2 / 2 * parisiCDF μ r * A r ω ^ 2)
      (hjbGridTime n i) (hjbGridTime n (i + 1))
    let E := ∫ r in hjbGridTime n i..hjbGridTime n (i + 1), hjbGridCoefficientError β μ ν n r
    F (i + 1) - C ≤ F i + E ∧
      F i - E - β ^ 2 / 2 * eps ^ 2 * (hjbGridTime n (i + 1) - hjbGridTime n i) ≤ F (i + 1) - C := by
  let s := parisiGridRSBScheme ν n
  let a := (hjbGridTime n i).toNNReal
  let b := (hjbGridTime n (i + 1)).toNNReal
  have hab : a < b := NNReal.coe_lt_coe.mp (by
    simpa only [a, b, coe_hjbGridTime_toNNReal] using hjbGridTime_step_lt n i)
  have hm : s.m (i + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hsub : Icc (hjbGridTime n i) (hjbGridTime n (i + 1)) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hjbGridTime_nonneg n i) (hjbGridTime_le_one n (i + 1) (by omega))
  have herr : IntervalIntegrable (fun r => (3 / 2 : ℝ) * β ^ 2 * |parisiCDF μ r - s.m (i + 1)|)
      volume a b := by
    exact (((parisiCDF_monotone μ).intervalIntegrable (a := a) (b := b)).sub intervalIntegrable_const).norm.const_mul _
  have hd' : ∀ ω, ∀ r ∈ Icc (a : ℝ) (b : ℝ), d r.toNNReal ω = β ^ 2 * parisiCDF μ r * A r ω := by
    intro ω r hr
    apply hd ω
    exact hsub (by simpa only [a, b, coe_hjbGridTime_toNNReal] using hr)
  have hclose' : ∀ ω, ∀ r ∈ Icc (a : ℝ) (b : ℝ),
      ‖A r ω - parisiSlabGradient s β (n + 1 - i) (s.m (i + 1)) b r (X r.toNNReal ω)‖ ≤ eps := by
    intro ω r hr
    have hr' : r ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1)) := by
      simpa only [a, b, coe_hjbGridTime_toNNReal] using hr
    simpa only [s, b, coe_hjbGridTime_toNNReal,
      ← hjbGrid_cell_gradient ν n β i hi r (X r.toNNReal ω) hr'] using hclose ω r (hsub hr')
  have hh := parisiSlab_control_error_bounds hc s hβ (n + 1 - i) hm a b hab
    (parisiCDF μ) A hA hd'
    (by simpa only [a, b, coe_hjbGridTime_toNNReal] using hcost)
    (by simpa only [a, b, coe_hjbGridTime_toNNReal] using hicost)
    herr hXa hXb heps hclose'
  dsimp only at hh ⊢
  rw [integral_sub (integrable_parisiSlabPotential s β (n + 1 - i) hm b b hXb)
    (by simpa only [a, b, coe_hjbGridTime_toNNReal] using hicost)] at hh
  have hpa : (fun ω => parisiSlabPotential s β (n + 1 - i) (s.m (i + 1)) b a (X a ω)) =
      fun ω => parisiFinitePotential s β (hjbGridTime n i, X a ω) := by
    funext ω
    simpa only [s, a, b, coe_hjbGridTime_toNNReal] using
      (hjbGrid_cell_potential ν n β i hi (hjbGridTime n i) (X a ω)
      ⟨le_rfl, (hjbGridTime_step_lt n i).le⟩).symm
  have hpb : (fun ω => parisiSlabPotential s β (n + 1 - i) (s.m (i + 1)) b b (X b ω)) =
      fun ω => parisiFinitePotential s β (hjbGridTime n (i + 1), X b ω) := by
    funext ω
    simpa only [s, a, b, coe_hjbGridTime_toNNReal] using
      (hjbGrid_cell_potential ν n β i hi (hjbGridTime n (i + 1)) (X b ω)
      ⟨(hjbGridTime_step_lt n i).le, le_rfl⟩).symm
  rw [hpa, hpb] at hh
  simpa only [s, a, b, coe_hjbGridTime_toNNReal, hjbExpectedCost,
    hjbGrid_cell_error_integral β μ ν n i hi] using hh

end Paper
