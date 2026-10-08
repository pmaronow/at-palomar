module

public import Paper.ParisiGradientCells
public import Paper.ParisiHJBBase

@[expose] public section

/-! Weighted finite-grid gradient estimates on the actual selected Parisi state. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace Paper
open SpinGlass SpinGlass.Targets

def parisiGradientGridError (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) : ℝ :=
  β ^ 2 * (|parisiCDF μ t - parisiCDF (parisiGridMeasure μ n) t| + parisiHJBGradientError β μ n)

lemma parisiGradientGridError_nonneg (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) :
    0 ≤ parisiGradientGridError β μ n t :=
  mul_nonneg (sq_nonneg _) (add_nonneg (abs_nonneg _) (parisiHJBGradientError_nonneg _ _ _))

lemma parisiGradientGridError_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (n : ℕ) (a b : ℝ) : IntervalIntegrable (parisiGradientGridError β μ n) volume a b :=
  (((((parisiCDF_monotone μ).intervalIntegrable (a := a) (b := b)).sub
    ((parisiCDF_monotone (parisiGridMeasure μ n)).intervalIntegrable)).norm).add
      intervalIntegrable_const).const_mul _

set_option maxHeartbeats 1000000 in
/-- Every nonempty truncated grid cell has exactly the weighted expectation
error of its genuine CDF and gradient approximations. -/
theorem selectedParisiState_gradient_grid_cell_bound
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n i : ℕ) (hi : i < n + 1)
    (r a b : ℝ≥0) (hra : r ≤ a) (hab : a < b)
    (ha : (a : ℝ) ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1)))
    (hb : (b : ℝ) = hjbGridTime n (i + 1))
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration r] Z)
    (hZb : ∀ ω, ‖Z ω‖ ≤ 1) :
    ‖(∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (b, selectedParisiItoState β h hβ μ b ω) ∂canonicalBrownianMeasure) -
      ∫ ω, Z ω * parisiFiniteGradient (parisiGridRSBScheme μ n) β
        (a, selectedParisiItoState β h hβ μ a ω) ∂canonicalBrownianMeasure‖ ≤
      ∫ t in (a : ℝ)..(b : ℝ), parisiGradientGridError β μ n t := by
  let s := parisiGridRSBScheme μ n
  let X := selectedParisiItoState β h hβ μ
  let v := fun t x => parisiGradient β μ (t, x)
  let m := s.m (i + 1)
  have hm : m ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
  have hb1 : (b : ℝ) ≤ 1 := hb ▸ hjbGridTime_le_one n (i + 1) (by omega)
  have hcell (t : ℝ) (ht : t ∈ Icc (a : ℝ) (b : ℝ)) :
      t ∈ Icc (hjbGridTime n i) (hjbGridTime n (i + 1)) :=
    ⟨ha.1.trans ht.1, ht.2.trans_eq hb⟩
  have hclose : ∀ ω, ∀ t ∈ Icc (a : ℝ) (b : ℝ),
      ‖v t (X t.toNNReal ω) - parisiSlabGradient s β (n + 1 - i) m b t (X t.toNNReal ω)‖ ≤
        parisiHJBGradientError β μ n := by
    intro ω t ht
    have hh := parisiHJBGradientError_bound β μ n t (X t.toNNReal ω)
    rw [hjbGrid_cell_gradient μ n β i hi t _ (hcell t ht)] at hh
    simpa only [v, s, m, hb] using hh
  have hh := canonicalParisiState_gradient_cell_bound β h hβ μ v
    (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t, x))
    (lipschitzWith_parisiGradient β hβ μ) r a b hra hab hb1 s (n + 1 - i) hm Z hZ hZb
    (parisiHJBGradientError_nonneg β μ n) hclose
  have hia : (fun ω => parisiSlabGradient s β (n + 1 - i) m b a (X a ω)) =
      fun ω => parisiFiniteGradient s β (a, X a ω) := by
    funext ω
    simpa only [s, m, hb] using (hjbGrid_cell_gradient μ n β i hi a (X a ω) ha).symm
  have hib : (fun ω => parisiSlabGradient s β (n + 1 - i) m b b (X b ω)) =
      fun ω => parisiFiniteGradient s β (b, X b ω) := by
    funext ω
    simpa only [s, m, hb] using (hjbGrid_cell_gradient μ n β i hi b (X b ω)
      ⟨(hjbGridTime_step_lt n i).le.trans_eq hb.symm, hb.le⟩).symm
  change ‖(∫ ω, Z ω * parisiSlabGradient s β (n + 1 - i) m b b (X b ω) ∂canonicalBrownianMeasure) -
    ∫ ω, Z ω * parisiSlabGradient s β (n + 1 - i) m b a (X a ω) ∂canonicalBrownianMeasure‖ ≤ _ at hh
  simp_rw [congrFun hib, congrFun hia] at hh
  have hmass : (∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - m|) =
      ∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - parisiCDF (parisiGridMeasure μ n) t| := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (NNReal.coe_lt_coe.mpr hab).le]
    intro t ht
    have htc : t ∈ Ico ((parisiGridRSBScheme μ n).q (i + 1))
        ((parisiGridRSBScheme μ n).q (i + 1 + 1)) := by
      obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q μ n i hi
      simpa only [hq0, show i + 1 + 1 = i + 2 by omega, hq1] using
        (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i + 1)) from
          ⟨ha.1.trans ht.1.le, ht.2.trans_eq hb⟩)
    dsimp only
    rw [parisiCDF_grid_eq_scheme_mass μ n (i + 1) (by omega) (by omega) htc]
  rw [hmass] at hh
  have he : (∫ t in (a : ℝ)..(b : ℝ), parisiGradientGridError β μ n t) =
      β ^ 2 * (∫ t in (a : ℝ)..(b : ℝ), |parisiCDF μ t - parisiCDF (parisiGridMeasure μ n) t|) +
        β ^ 2 * parisiHJBGradientError β μ n * ((b : ℝ) - a) := by
    dsimp only [parisiGradientGridError]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · exact (((parisiCDF_monotone μ).intervalIntegrable).sub
        ((parisiCDF_monotone (parisiGridMeasure μ n)).intervalIntegrable)).norm
    · exact intervalIntegrable_const
  simpa only [X, s, ← he] using hh

end Paper
