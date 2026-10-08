module

public import Paper.ParisiGradientMesh
public import Paper.HJBGrid

@[expose] public section

/-! Actual grid HJB verification in elapsed time after a fresh restart. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open scoped NNReal
namespace Paper
open SpinGlass SpinGlass.Targets

def hjbRestartMeshTime (n : ℕ) (a : ℝ) (i : ℕ) : ℝ :=
  parisiGradientMeshTime n a i - a

lemma hjbRestartMeshTime_nonneg (n : ℕ) (a : ℝ) (i : ℕ) :
    0 ≤ hjbRestartMeshTime n a i := sub_nonneg.mpr (le_max_left _ _)

lemma hjbRestartMeshTime_mono (n : ℕ) (a : ℝ) : Monotone (hjbRestartMeshTime n a) := by
  intro i j hij
  exact sub_le_sub_right (parisiGradientMeshTime_mono n a hij) a

@[simp] theorem hjbRestartMeshTime_zero (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    hjbRestartMeshTime n a 0 = 0 := by simp only [hjbRestartMeshTime, parisiGradientMeshTime_zero n ha, sub_self]

@[simp] theorem hjbRestartMeshTime_terminal (n : ℕ) {a : ℝ} (ha : a ≤ 1) :
    hjbRestartMeshTime n a (n + 1) = 1 - a := by simp only [hjbRestartMeshTime, parisiGradientMeshTime_terminal n ha]

lemma hjbRestartMeshTime_mem (n : ℕ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    {i : ℕ} (hi : i ≤ n + 1) : hjbRestartMeshTime n a i ∈ Icc (0 : ℝ) (1 - a) :=
  ⟨hjbRestartMeshTime_nonneg n a i, sub_le_sub_right (parisiGradientMeshTime_mem n ha hi).2 a⟩

lemma parisiSlabPotential_shift {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (m b a r x : ℝ) :
    parisiSlabPotential s β j m b (a + r) x = parisiSlabPotential s β j m (b - a) r x := by
  unfold parisiSlabPotential
  congr 1
  ring

lemma parisiSlabGradient_shift {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (m b a r x : ℝ) :
    parisiSlabGradient s β j m b (a + r) x = parisiSlabGradient s β j m (b - a) r x := by
  unfold parisiSlabGradient
  congr 1
  ring

set_option maxHeartbeats 1000000 in
theorem hjbTimeGrid_cell_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (rho μ ν : ParisiMeasure) (n : ℕ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hshift : ∀ r ∈ Icc (0 : ℝ) (1 - a), parisiCDF rho r = parisiCDF μ (a + r))
    (i : ℕ) (hi : i < n + 1)
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A)) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), d r.toNNReal sample = β ^ 2 * parisiCDF rho r * A r sample)
    (hi0 : Integrable (X 0) P) {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a),
      ‖A r sample - parisiFiniteGradient (parisiGridRSBScheme ν n) β (a + r, X r.toNNReal sample)‖ ≤ eps) :
    let S := hjbRestartMeshTime n a
    let F := fun j => ∫ sample, parisiFinitePotential (parisiGridRSBScheme ν n) β
      (a + S j, X (S j).toNNReal sample) ∂P
    let C := hjbExpectedCost P (parisiInstantControlCost β rho A) (S i) (S (i + 1))
    let E := ∫ r in S i..S (i + 1), hjbGridCoefficientError β μ ν n (a + r)
    F (i + 1) - C ≤ F i + E ∧
      F i - E - β ^ 2 / 2 * eps ^ 2 * (S (i + 1) - S i) ≤ F (i + 1) - C := by
  let T := parisiGradientMeshTime n a
  let S := hjbRestartMeshTime n a
  rcases parisiGradientMeshTime_step_cases n a i with hEq | hlt
  · have he : S i = S (i + 1) := by dsimp only [S, hjbRestartMeshTime]; rw [hEq]
    dsimp only [S] at he
    dsimp only
    simp only [he, hjbExpectedCost, intervalIntegral.integral_same, integral_zero,
      sub_zero, add_zero, sub_self, mul_zero, le_refl, and_self]
  · let s := parisiGridRSBScheme ν n
    let ta := (S i).toNNReal
    let tb := (S (i + 1)).toNNReal
    have hta := hjbRestartMeshTime_mem n ha (i := i) (by omega)
    have htb := hjbRestartMeshTime_mem n ha (i := i + 1) (by omega)
    have htae : (ta : ℝ) = S i := Real.coe_toNNReal _ hta.1
    have htbe : (tb : ℝ) = S (i + 1) := Real.coe_toNNReal _ htb.1
    have hltS : S i < S (i + 1) := sub_lt_sub_right hlt a
    have hab : ta < tb := NNReal.coe_lt_coe.mp (by simpa only [htae, htbe] using hltS)
    have hup : T (i + 1) = hjbGridTime n (i + 1) := parisiGradientMeshTime_step_lt_terminal n a i hlt
    dsimp only [T] at hup
    have hsub := parisiGradientMeshTime_cell_subset n a i hlt
    have hphys : Icc (S i) (S (i + 1)) ⊆ Icc (0 : ℝ) (1 - a) := Icc_subset_Icc hta.1 htb.2
    have hcell (r : ℝ) (hr : r ∈ Icc (S i) (S (i + 1))) : a + r ∈ Icc (T i) (T (i + 1)) := by
      dsimp only [S, hjbRestartMeshTime] at hr
      constructor <;> linarith [hr.1, hr.2]
    have hm : s.m (i + 1) ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
    have heU (r x : ℝ) (hr : r ∈ Icc (S i) (S (i + 1))) :
        parisiFinitePotential s β (a + r, x) = parisiSlabPotential s β (n + 1 - i) (s.m (i + 1)) tb r x := by
      have hh := hjbGrid_cell_potential ν n β i hi (a + r) x (hsub (hcell r hr))
      rw [parisiSlabPotential_shift] at hh
      simpa only [s, htbe, S, hjbRestartMeshTime, hup] using hh
    have heG (r x : ℝ) (hr : r ∈ Icc (S i) (S (i + 1))) :
        parisiFiniteGradient s β (a + r, x) = parisiSlabGradient s β (n + 1 - i) (s.m (i + 1)) tb r x := by
      have hh := hjbGrid_cell_gradient ν n β i hi (a + r) x (hsub (hcell r hr))
      rw [parisiSlabGradient_shift] at hh
      simpa only [s, htbe, S, hjbRestartMeshTime, hup] using hh
    have herr : IntervalIntegrable (fun r => (3 / 2 : ℝ) * β ^ 2 * |parisiCDF rho r - s.m (i + 1)|) volume ta tb :=
      (((parisiCDF_monotone rho).intervalIntegrable (a := (ta : ℝ)) (b := (tb : ℝ))).sub intervalIntegrable_const).norm.const_mul _
    have heInt : (∫ r in (ta : ℝ)..(tb : ℝ), (3 / 2 : ℝ) * β ^ 2 * |parisiCDF rho r - s.m (i + 1)|) =
        ∫ r in S i..S (i + 1), hjbGridCoefficientError β μ ν n (a + r) := by
      rw [htae, htbe]
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le hltS.le]
      intro r hr
      have hr' : r ∈ Icc (S i) (S (i + 1)) := ⟨hr.1.le, hr.2.le⟩
      have hcell' : a + r ∈ Ico ((parisiGridRSBScheme ν n).q (i + 1)) ((parisiGridRSBScheme ν n).q ((i + 1) + 1)) := by
        obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q ν n i hi
        rw [hq0, hq1]
        refine ⟨(le_max_right _ _).trans (hcell r hr').1, ?_⟩
        dsimp only [S, hjbRestartMeshTime] at hr
        rw [← hup]
        linarith [hr.2]
      dsimp only [hjbGridCoefficientError]
      rw [Real.norm_eq_abs,
        parisiCDF_grid_eq_scheme_mass ν n (i + 1) (by omega) (by omega) hcell', hshift r (hphys hr')]
    have hicost : Integrable (fun sample => ∫ r in (ta : ℝ)..(tb : ℝ), β ^ 2 / 2 * parisiCDF rho r * A r sample ^ 2) P :=
      integrable_parisiInstantControlCost_integral P β rho A hAm hA ta tb (NNReal.coe_le_coe.mpr hab.le)
    have hXa := hc.integrable_state hi0 ta
    have hXb := hc.integrable_state hi0 tb
    have hh := parisiSlab_control_error_bounds hc s hβ (n + 1 - i) hm ta tb hab (parisiCDF rho) A hA
      (fun sample r hr => hd sample r (hphys (by simpa only [htae, htbe] using hr)))
      (fun sample => intervalIntegrable_parisiInstantControlCost β rho A hAm hA ta tb sample)
      hicost herr hXa hXb heps (fun sample r hr => by
        have hr' : r ∈ Icc (S i) (S (i + 1)) := by simpa only [htae, htbe] using hr
        rw [← heG r _ hr']
        exact hclose sample r (hphys hr'))
    rw [integral_sub (integrable_parisiSlabPotential s β (n + 1 - i) hm tb tb hXb) hicost] at hh
    have hpa : (fun sample => parisiSlabPotential s β (n + 1 - i) (s.m (i + 1)) tb ta (X ta sample)) =
        fun sample => parisiFinitePotential s β (a + S i, X (S i).toNNReal sample) := by
      funext sample
      simpa only [htae] using (heU (S i) (X ta sample) ⟨le_rfl, hltS.le⟩).symm
    have hpb : (fun sample => parisiSlabPotential s β (n + 1 - i) (s.m (i + 1)) tb tb (X tb sample)) =
        fun sample => parisiFinitePotential s β (a + S (i + 1), X (S (i + 1)).toNNReal sample) := by
      funext sample
      simpa only [htbe] using (heU (S (i + 1)) (X tb sample) ⟨hltS.le, le_rfl⟩).symm
    rw [hpa, hpb, heInt] at hh
    try dsimp only at hh ⊢
    simpa only [htae, htbe, S, s, hjbExpectedCost, parisiInstantControlCost] using hh

lemma hjbTimeGridCoefficientError_intervalIntegrable (β : ℝ) (μ ν : ParisiMeasure)
    (n : ℕ) (a c d : ℝ) :
    IntervalIntegrable (fun r => hjbGridCoefficientError β μ ν n (a + r)) volume c d := by
  have hm : Monotone (fun r => parisiCDF μ (a + r)) :=
    (parisiCDF_monotone μ).comp (monotone_const.add monotone_id)
  have hn : Monotone (fun r => parisiCDF (parisiGridMeasure ν n) (a + r)) :=
    (parisiCDF_monotone _).comp (monotone_const.add monotone_id)
  exact (hm.intervalIntegrable.sub hn.intervalIntegrable).norm.const_mul _

lemma hjbTimeGridCoefficientError_integral_le (β : ℝ) (μ ν : ParisiMeasure)
    (n : ℕ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ r in (0 : ℝ)..(1 - a), hjbGridCoefficientError β μ ν n (a + r)) ≤
      (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n) := by
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero, add_sub_cancel]
  have hh := parisiGradientMesh_integral_le_full ha
    (hjbGridCoefficientError_intervalIntegrable β μ ν n 0 1)
    (fun r => by dsimp only [hjbGridCoefficientError]; positivity)
  unfold hjbGridCoefficientError at hh
  unfold parisiCDFDistance hjbGridCoefficientError
  simpa only [intervalIntegral.integral_const_mul, Real.norm_eq_abs] using hh

set_option maxHeartbeats 1000000 in
/-- Full restarted-grid bounds on the same genuinely controlled process. -/
theorem hjbTimeGrid_control_error_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (rho μ ν : ParisiMeasure) (n : ℕ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hshift : ∀ r ∈ Icc (0 : ℝ) (1 - a), parisiCDF rho r = parisiCDF μ (a + r))
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A)) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), d r.toNNReal sample = β ^ 2 * parisiCDF rho r * A r sample)
    (hi0 : Integrable (X 0) P) {eps : ℝ} (heps : 0 ≤ eps)
    (hclose : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a),
      ‖A r sample - parisiFiniteGradient (parisiGridRSBScheme ν n) β (a + r, X r.toNNReal sample)‖ ≤ eps) :
    let initial := ∫ sample, parisiFinitePotential (parisiGridRSBScheme ν n) β (a, X 0 sample) ∂P
    let payoff := (∫ sample, Real.log (Real.cosh (X (1 - a).toNNReal sample)) ∂P) -
      hjbExpectedCost P (parisiInstantControlCost β rho A) 0 (1 - a)
    let error := (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n)
    payoff ≤ initial + error ∧ initial - error - β ^ 2 / 2 * eps ^ 2 * (1 - a) ≤ payoff := by
  let C := parisiInstantControlCost β rho A
  let E := fun r => hjbGridCoefficientError β μ ν n (a + r)
  let S := hjbRestartMeshTime n a
  let F := fun j => ∫ sample, parisiFinitePotential (parisiGridRSBScheme ν n) β
    (a + S j, X (S j).toNNReal sample) ∂P
  have ht : ∀ sample i, i < n + 1 → IntervalIntegrable (fun r => C r sample) volume (S i) (S (i + 1)) :=
    fun sample i _ => intervalIntegrable_parisiInstantControlCost β rho A hAm hA _ _ sample
  have hi : ∀ i, i < n + 1 → Integrable (fun sample => ∫ r in S i..S (i + 1), C r sample) P :=
    fun i _ => integrable_parisiInstantControlCost_integral P β rho A hAm hA _ _
      (hjbRestartMeshTime_mono n a (Nat.le_succ i))
  have hE : ∀ i, i < n + 1 → IntervalIntegrable E volume (S i) (S (i + 1)) :=
    fun i _ => hjbTimeGridCoefficientError_intervalIntegrable β μ ν n a _ _
  have hcell (i : ℕ) (hiN : i < n + 1) :=
    hjbTimeGrid_cell_error_bounds hc hβ rho μ ν n a ha hshift i hiN A hAm hA hd hi0 heps hclose
  have hu := hjb_expected_cells_telescope_upper P C E S (n + 1) F ht hi hE
    (fun i hiN => (hcell i hiN).1)
  have hl := hjb_expected_cells_telescope_lower P C E S (n + 1) F (β ^ 2 / 2 * eps ^ 2)
    ht hi hE (fun i hiN => (hcell i hiN).2)
  have hS0 : S 0 = 0 := hjbRestartMeshTime_zero n ha.1
  have hSN : S (n + 1) = 1 - a := hjbRestartMeshTime_terminal n ha.2
  have hF0 : F 0 = ∫ sample, parisiFinitePotential (parisiGridRSBScheme ν n) β (a, X 0 sample) ∂P := by
    dsimp only [F]
    simp only [hS0, add_zero, Real.toNNReal_zero]
  have hFN : F (n + 1) = ∫ sample, Real.log (Real.cosh (X (1 - a).toNNReal sample)) ∂P := by
    dsimp only [F]
    simp only [hSN, add_sub_cancel, parisiFinitePotential_terminal]
  rw [hS0, hSN, hF0, hFN] at hu hl
  have herr := hjbTimeGridCoefficientError_integral_le β μ ν n ha
  dsimp only
  constructor
  · exact hu.trans (add_le_add le_rfl herr)
  · dsimp only [E] at hl
    simp only [sub_zero] at hl
    linarith

theorem hjbTimeGrid_control_upper {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β)
    (hβ : β ≠ 0) (rho μ ν : ParisiMeasure) (n : ℕ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hshift : ∀ r ∈ Icc (0 : ℝ) (1 - a), parisiCDF rho r = parisiCDF μ (a + r))
    (A : ℝ → Ω → ℝ) (hAm : Measurable (Function.uncurry A)) (hA : ∀ r sample, ‖A r sample‖ ≤ 1)
    (hd : ∀ sample, ∀ r ∈ Icc (0 : ℝ) (1 - a), d r.toNNReal sample = β ^ 2 * parisiCDF rho r * A r sample)
    (hi0 : Integrable (X 0) P) :
    (∫ sample, Real.log (Real.cosh (X (1 - a).toNNReal sample)) ∂P) -
      hjbExpectedCost P (parisiInstantControlCost β rho A) 0 (1 - a) ≤
        (∫ sample, parisiFinitePotential (parisiGridRSBScheme ν n) β (a, X 0 sample) ∂P) +
          (3 / 2 : ℝ) * β ^ 2 * parisiCDFDistance μ (parisiGridMeasure ν n) := by
  exact (hjbTimeGrid_control_error_bounds hc hβ rho μ ν n a ha hshift A hAm hA hd hi0
    (by norm_num : (0 : ℝ) ≤ 2) (fun sample r _ => (norm_sub_le _ _).trans (by
      have hb := norm_parisiFiniteGradient_le_one (parisiGridRSBScheme ν n) β (a + r, X r.toNNReal sample)
      have ha := hA r sample
      linarith))).1

end Paper
