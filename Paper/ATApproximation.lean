module

public import Paper.GaussianHeat
public import Paper.ATCoordinates

@[expose] public section

/-!
# Strict-AT approximation of every closed-AT physical point

Keep the physical variance `s=β²q` fixed, increase the field by `ε`, and
reconstruct the overlap and beta coordinate. The resulting actual Gaussian
fixed point satisfies the strict AT inequality and converges to the original
physical point. No Gaussian regularity or fixed-point selector is assumed.
-/

open Filter
open scoped Topology

namespace Paper

noncomputable def atStrictApproxOverlap (β h q ε : ℝ) : ℝ :=
  1 - gaussianA (h + ε) (β ^ 2 * q)

noncomputable def atStrictApproxBeta (β h q ε : ℝ) : ℝ :=
  Real.sqrt ((β ^ 2 * q) / atStrictApproxOverlap β h q ε)

theorem gaussian_fixedPoint_time_relation (β h q : ℝ) (hβ : 0 ≤ β)
    (hfixed : q = overlapMap β h q) : q = 1 - gaussianA h (β ^ 2 * q) := by
  have he := overlapMap_add_sech_sq β h q
  rw [gaussian_sech_time_coordinate β h q 2 hβ, ← hfixed] at he
  change q + gaussianA h (β ^ 2 * q) = 1 at he
  linarith

/-- The zero function equals `q(α−1)` at an actual fixed point. -/
theorem atZeroFunction_fixedPoint_identity (β h q : ℝ) (hβ : 0 ≤ β)
    (hfixed : q = overlapMap β h q) :
    atZeroFunction h (β ^ 2 * q) = q * (atParameter β h q - 1) := by
  have hrel := gaussian_fixedPoint_time_relation β h q hβ hfixed
  have hA : gaussianA h (β ^ 2 * q) = 1 - q := by linarith
  have hα : atParameter β h q = β ^ 2 * gaussianC h (β ^ 2 * q) := by
    unfold atParameter
    rw [gaussian_sech_time_coordinate β h q 4 hβ]
    rfl
  rw [hα]
  unfold atZeroFunction
  rw [hA]
  ring

theorem atZeroFunction_nonpos_of_at_le_one (β h q : ℝ) (hβ : 0 ≤ β)
    (hq : 0 ≤ q) (hfixed : q = overlapMap β h q) (hα : atParameter β h q ≤ 1) :
    atZeroFunction h (β ^ 2 * q) ≤ 0 := by
  rw [atZeroFunction_fixedPoint_identity β h q hβ hfixed]
  exact mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hα)

theorem atStrictApproxOverlap_bounds (β h q ε : ℝ) (hfield : 0 < h + ε) :
    atStrictApproxOverlap β h q ε ∈ Set.Ioo (0 : ℝ) 1 := by
  have hApos := gaussianA_pos (h + ε) (β ^ 2 * q)
  have hAlt := gaussianA_lt_one_of_field_pos (h + ε) (β ^ 2 * q) hfield
  unfold atStrictApproxOverlap
  constructor <;> linarith

theorem atStrictApprox_argument (β h q ε : ℝ) (hs : 0 < β ^ 2 * q)
    (hfield : 0 < h + ε) :
    atStrictApproxBeta β h q ε * Real.sqrt (atStrictApproxOverlap β h q ε) =
      Real.sqrt (β ^ 2 * q) := by
  have hq := (atStrictApproxOverlap_bounds β h q ε hfield).1
  unfold atStrictApproxBeta
  rw [← Real.sqrt_mul (div_nonneg hs.le hq.le)]
  congr 1
  exact div_mul_cancel₀ _ (ne_of_gt hq)

/-- Reconstruction is an actual Gaussian fixed point even away from the
AT zero set. -/
theorem atStrictApprox_fixedPoint (β h q ε : ℝ) (hs : 0 < β ^ 2 * q)
    (hfield : 0 < h + ε) :
    atStrictApproxOverlap β h q ε = overlapMap (atStrictApproxBeta β h q ε)
      (h + ε) (atStrictApproxOverlap β h q ε) := by
  have harg := atStrictApprox_argument β h q ε hs hfield
  have he := overlapMap_add_sech_sq (atStrictApproxBeta β h q ε) (h + ε)
    (atStrictApproxOverlap β h q ε)
  have hmoment : gaussianExpectation
      (fun z => sech (gaussianField (atStrictApproxBeta β h q ε) (h + ε)
        (atStrictApproxOverlap β h q ε) z) ^ 2) = gaussianA (h + ε) (β ^ 2 * q) := by
    unfold gaussianA
    congr 1
    ext z
    unfold gaussianField
    rw [harg, add_comm]
  rw [hmoment] at he
  have hqdef : atStrictApproxOverlap β h q ε + gaussianA (h + ε) (β ^ 2 * q) = 1 := by
    unfold atStrictApproxOverlap
    ring
  linarith

/-- Every positive-field closed-AT point admits the explicit strict-AT
perturbation. All fixed-point and strict parameter facts are proved for the
concrete Gaussian integrals. -/
theorem atStrictApprox_properties (β h q ε : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q)
    (hα : atParameter β h q ≤ 1) (hε : 0 < ε) :
    0 < atStrictApproxBeta β h q ε ∧ 0 < h + ε ∧
      atStrictApproxOverlap β h q ε ∈ Set.Ioo (0 : ℝ) 1 ∧
      atStrictApproxOverlap β h q ε = overlapMap (atStrictApproxBeta β h q ε)
        (h + ε) (atStrictApproxOverlap β h q ε) ∧
      atParameter (atStrictApproxBeta β h q ε) (h + ε)
        (atStrictApproxOverlap β h q ε) < 1 := by
  have hqpos := fixedPoint_pos hh hq.1 hfixed
  have hs : 0 < β ^ 2 * q := mul_pos (sq_pos_of_pos hβ) hqpos
  have hfield : 0 < h + ε := by linarith
  have hqeps := atStrictApproxOverlap_bounds β h q ε hfield
  have hβeps : 0 < atStrictApproxBeta β h q ε := Real.sqrt_pos.mpr (div_pos hs hqeps.1)
  refine ⟨hβeps, hfield, hqeps, atStrictApprox_fixedPoint β h q ε hs hfield, ?_⟩
  have hFle := atZeroFunction_nonpos_of_at_le_one β h q hβ.le hq.1 hfixed hα
  have hFlt := atZeroFunction_strictAntiOn_field hs hh.le hfield.le
    (show h < h + ε by linarith)
  dsimp only at hFlt
  have hFnegative : atZeroFunction (h + ε) (β ^ 2 * q) < 0 := lt_of_lt_of_le hFlt hFle
  have hmoment : gaussianExpectation
      (fun z => sech (gaussianField (atStrictApproxBeta β h q ε) (h + ε)
        (atStrictApproxOverlap β h q ε) z) ^ 4) = gaussianC (h + ε) (β ^ 2 * q) := by
    conv_rhs => unfold gaussianC
    congr 1
    ext z
    unfold gaussianField
    rw [atStrictApprox_argument β h q ε hs hfield, add_comm]
  have hgap : (β ^ 2 * q) * gaussianC (h + ε) (β ^ 2 * q) <
      atStrictApproxOverlap β h q ε := by
    unfold atZeroFunction at hFnegative
    unfold atStrictApproxOverlap
    linarith
  unfold atParameter
  rw [hmoment]
  rw [atStrictApproxBeta, Real.sq_sqrt (div_nonneg hs.le hqeps.1.le)]
  calc
    (β ^ 2 * q / atStrictApproxOverlap β h q ε) * gaussianC (h + ε) (β ^ 2 * q) =
        ((β ^ 2 * q) * gaussianC (h + ε) (β ^ 2 * q)) / atStrictApproxOverlap β h q ε := by ring
    _ < 1 := (div_lt_one hqeps.1).mpr hgap

theorem atStrictApproxOverlap_zero (β h q : ℝ) (hβ : 0 ≤ β)
    (hfixed : q = overlapMap β h q) : atStrictApproxOverlap β h q 0 = q := by
  simpa only [atStrictApproxOverlap, add_zero] using
    (gaussian_fixedPoint_time_relation β h q hβ hfixed).symm

theorem continuous_atStrictApproxOverlap (β h q : ℝ) :
    Continuous (atStrictApproxOverlap β h q) := by
  have hpair : Continuous (fun ε : ℝ => (h + ε, β ^ 2 * q)) :=
    (continuous_const.add continuous_id).prodMk continuous_const
  exact continuous_const.sub (continuous_gaussianA_joint.comp
    (f := fun ε : ℝ => (h + ε, β ^ 2 * q)) hpair)

theorem atStrictApproxBeta_zero (β h q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (hfixed : q = overlapMap β h q) : atStrictApproxBeta β h q 0 = β := by
  rw [atStrictApproxBeta, atStrictApproxOverlap_zero β h q hβ.le hfixed,
    mul_div_cancel_right₀ _ (ne_of_gt hq), Real.sqrt_sq hβ.le]

theorem continuousAt_atStrictApproxBeta_zero (β h q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (hfixed : q = overlapMap β h q) : ContinuousAt (atStrictApproxBeta β h q) 0 := by
  have hden : atStrictApproxOverlap β h q 0 ≠ 0 := by
    rw [atStrictApproxOverlap_zero β h q hβ.le hfixed]
    exact ne_of_gt hq
  exact (continuousAt_const.div (continuous_atStrictApproxOverlap β h q).continuousAt hden).sqrt

theorem tendsto_atStrictApproxOverlap_zero_right (β h q : ℝ) (hβ : 0 ≤ β)
    (hfixed : q = overlapMap β h q) :
    Tendsto (atStrictApproxOverlap β h q) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 q) := by
  have hc := ((continuous_atStrictApproxOverlap β h q).continuousAt (x := 0)).continuousWithinAt
    (s := Set.Ioi (0 : ℝ))
  change Tendsto (atStrictApproxOverlap β h q) (𝓝[Set.Ioi (0 : ℝ)] 0)
    (𝓝 (atStrictApproxOverlap β h q 0)) at hc
  simpa only [atStrictApproxOverlap_zero β h q hβ hfixed] using hc

theorem tendsto_atStrictApproxBeta_zero_right (β h q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (hfixed : q = overlapMap β h q) :
    Tendsto (atStrictApproxBeta β h q) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 β) := by
  have hc := (continuousAt_atStrictApproxBeta_zero β h q hβ hq hfixed).continuousWithinAt
    (s := Set.Ioi (0 : ℝ))
  change Tendsto (atStrictApproxBeta β h q) (𝓝[Set.Ioi (0 : ℝ)] 0)
    (𝓝 (atStrictApproxBeta β h q 0)) at hc
  simpa only [atStrictApproxBeta_zero β h q hβ hq hfixed] using hc

theorem tendsto_atStrictApprox_point_zero_right (β h q : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hfixed : q = overlapMap β h q) :
    Tendsto (fun ε : ℝ => (atStrictApproxBeta β h q ε, h + ε, atStrictApproxOverlap β h q ε))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (β, h, q)) := by
  have hqpos := fixedPoint_pos hh hq.1 hfixed
  have hb := tendsto_atStrictApproxBeta_zero_right β h q hβ hqpos hfixed
  have hf : Tendsto (fun ε : ℝ => h + ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 h) := by
    simpa only [add_zero, id_eq] using tendsto_const_nhds.add
      ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (a := (0 : ℝ))))
  exact hb.prodMk_nhds (hf.prodMk_nhds (tendsto_atStrictApproxOverlap_zero_right β h q hβ.le hfixed))

end Paper
