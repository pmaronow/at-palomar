module

public import StochasticCalculus.WeightedBracketRiemann

@[expose] public section

/-! Signed integrable drift coefficients in weighted uniform-partition limits. -/

noncomputable section
open MeasureTheory Filter Set StochasticCalculus
open scoped NNReal Topology
namespace Paper

/-- Continuous bounded weights have the expected partition limit against a
signed integrable coefficient. Positive and negative parts reduce the claim
to the library's proved nonnegative-density Riemann theorem. -/
theorem uniformPartition_weighted_integral_tendsto_signed
    {μ : Measure ℝ≥0} (d w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hd : IntegrableOn d (Ioc 0 t) μ) (hw : Continuous w) :
    Tendsto
      (fun n => ∑ i ∈ Finset.range (n + 1),
        w (uniformPartitionTime t (n + 1) i) *
          ((∫ s in Ioc 0 (uniformPartitionTime t (n + 1) (i + 1)), d s ∂μ) -
            ∫ s in Ioc 0 (uniformPartitionTime t (n + 1) i), d s ∂μ))
      atTop (𝓝 (∫ s in Ioc 0 t, w s * d s ∂μ)) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuousOn : ContinuousOn w (Icc 0 t))
  have hb : ∀ᵐ s ∂μ.restrict (Ioc 0 t), ‖w s‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hK s ⟨hs.1.le, hs.2⟩
  let p : ℝ≥0 → ℝ := fun s => (1 / 2 : ℝ) * (|d s| + d s)
  let m : ℝ≥0 → ℝ := fun s => (1 / 2 : ℝ) * (|d s| - d s)
  have ha : IntegrableOn (fun s => |d s|) (Ioc 0 t) μ := by
    change Integrable (fun s => |d s|) (μ.restrict (Ioc 0 t))
    simpa only [Real.norm_eq_abs] using hd.norm
  have hp : IntegrableOn p (Ioc 0 t) μ := (ha.add hd).const_mul (1 / 2)
  have hm : IntegrableOn m (Ioc 0 t) μ := (ha.sub hd).const_mul (1 / 2)
  have hwp : IntegrableOn (fun s => w s * p s) (Ioc 0 t) μ :=
    hp.bdd_mul hw.aestronglyMeasurable hb
  have hwm : IntegrableOn (fun s => w s * m s) (Ioc 0 t) μ :=
    hm.bdd_mul hw.aestronglyMeasurable hb
  have hpnonneg (s : ℝ≥0) : 0 ≤ p s := by
    dsimp [p]
    have := neg_abs_le (d s)
    linarith
  have hmnonneg (s : ℝ≥0) : 0 ≤ m s := by
    dsimp [m]
    have := le_abs_self (d s)
    linarith
  have hdecomp (s : ℝ≥0) : d s = p s - m s := by dsimp [p, m]; ring
  have hint (r : ℝ≥0) (hr : r ≤ t) :
      (∫ s in Ioc 0 r, d s ∂μ) = (∫ s in Ioc 0 r, p s ∂μ) -
        ∫ s in Ioc 0 r, m s ∂μ := by
    rw [← integral_sub (hp.mono_set (Ioc_subset_Ioc_right hr))
      (hm.mono_set (Ioc_subset_Ioc_right hr))]
    exact integral_congr_ae (Eventually.of_forall hdecomp)
  have htarget : (∫ s in Ioc 0 t, w s * d s ∂μ) =
      (∫ s in Ioc 0 t, w s * p s ∂μ) - ∫ s in Ioc 0 t, w s * m s ∂μ := by
    rw [← integral_sub hwp hwm]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [hdecomp s]
    ring
  have hlp := uniformPartition_weighted_integral_tendsto p w t hp hwp hpnonneg hw.continuousOn
  have hlm := uniformPartition_weighted_integral_tendsto m w t hm hwm hmnonneg hw.continuousOn
  rw [htarget]
  convert hlp.sub hlm using 1
  funext n
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  rw [hint _ (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos n)
      (Nat.succ_le_iff.mpr hi')).2,
    hint _ (uniformPartitionTime_mem_Icc_of_le t (Nat.succ_pos n) (Nat.le_of_lt hi')).2]
  ring

end Paper
