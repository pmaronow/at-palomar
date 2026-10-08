module

public import Targets.Section4Variance
public import Targets.CascadeDerivPi

@[expose] public section

/-!
# The split-variance derivative in Talagrand Section 4

The outer-transform calculation reuses the local-neighborhood cascade chain
rule, specialized to a single Gaussian coordinate. Scalar Gaussian Stein then
cancels the second-spatial-derivative term and yields (4.11). The actual recursive
`parisiF` inputs satisfy every analytic hypothesis, including at zero mass. The
split variance is interior: `0 < v < a`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- A scalar local-neighborhood version of the existing N-site chain rule. -/
theorem hasDerivAt_parisiStep_param_local {F F' : ℝ → ℝ → ℝ} {C D C' D' t m : ℝ}
    {s : Set ℝ} (hs : s ∈ 𝓝 t) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hd : ∀ u ∈ s, ∀ z, HasDerivAt (fun v => F v z) (F' u z) u)
    (hmF : ∀ u ∈ s, Measurable (F u)) (hmF' : ∀ u ∈ s, Measurable (F' u))
    (hb : ∀ u ∈ s, ∀ z, |F u z| ≤ C + D * |z|)
    (hb' : ∀ u ∈ s, ∀ z, |F' u z| ≤ C' + D' * |z|) :
    HasDerivAt (fun u => parisiStep m 1 (F u) 0)
      (∫ z, F' t z * tiltWeight m 1 (F t) 0 z ∂(gaussianReal 0 1)) t := by
  have ht := mem_of_mem_nhds hs
  have hg (u : ℝ) (hu : u ∈ s) : HasLinearGrowth (F u) :=
    ⟨|C|, D, abs_nonneg C, hD, fun z => (hb u hu z).trans (by linarith [le_abs_self C])⟩
  have H := hasDerivAt_parisiStepPi_param (n := 1) (m := m) (v := 1)
    (A := fun u z => F u (z 0)) (A' := fun u z => F' u (z 0))
    (C := C) (D := D) (C' := C') (D' := D') 0 hs hD hD'
    (fun u hu z => hd u hu (z 0))
    (fun u hu => (hmF u hu).comp (measurable_pi_apply 0))
    (fun u hu => (hmF' u hu).comp (measurable_pi_apply 0))
    (fun u hu z => by simpa [l1] using hb u hu (z 0))
    (fun u hu z => by simpa [l1] using hb' u hu (z 0))
  have heq : (fun u => parisiStep m 1 (F u) 0) =ᶠ[𝓝 t]
      fun u => parisiStepPi 1 m 1 (fun z => F u (z 0)) 0 := by
    filter_upwards [hs] with u hu
    simpa using (parisiStepPi_sum (n := 1) m 1 (hg u hu) (hmF u hu) 0).symm
  apply (H.congr_of_eventuallyEq heq).congr_deriv
  have hw (z : Fin 1 → ℝ) : tiltWeightPi 1 m 1 (fun y => F t (y 0)) 0 z =
      tiltWeight m 1 (F t) 0 (z 0) := by
    simp only [tiltWeightPi, tiltWeight, Pi.zero_apply, Real.sqrt_one, one_mul, zero_add]
    by_cases hm : m = 0
    · simp [hm]
    · rw [if_neg hm, if_neg hm,
        integral_piGauss_eval (0 : Fin 1) (fun z => Real.exp (m * F t z))
          ((hmF t ht).const_mul m).exp.aestronglyMeasurable]
  simp only [Pi.zero_apply, Real.sqrt_one, one_mul, zero_add, hw]
  apply integral_piGauss_eval (0 : Fin 1) (fun z => F' t z * tiltWeight m 1 (F t) 0 z)
  apply ((hmF' t ht).mul ?_).aestronglyMeasurable
  unfold tiltWeight
  split
  · exact measurable_const
  · exact ((hmF t ht).comp (by fun_prop)).const_mul m |>.exp |>.div measurable_const

private theorem parisiC2_dist_le {A A' A'' : ℝ → ℝ} (hC2 : HasParisiC2 A A' A'') (x y : ℝ) :
    |A x - A y| ≤ |x - y| := by
  simpa only [Real.norm_eq_abs, one_mul] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := A') (s := Set.univ) (C := 1)
    (fun t _ => (hC2.1 t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hC2.abs_first_le_one t)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- The actual derivative of the inner smoothing at the moving outer field. -/
noncomputable def splitVarianceVelocity (A A' A'' : ℝ → ℝ) (m a x v z : ℝ) : ℝ :=
  (stepD2 A A' A'' m v (x + Real.sqrt (a - v) * z) +
      m * (stepD1 A A' m v (x + Real.sqrt (a - v) * z)) ^ 2) / 2 -
    z / (2 * Real.sqrt (a - v)) * stepD1 A A' m v (x + Real.sqrt (a - v) * z)

/-- Differentiation through the genuine outer transform; no differentiability of
the outer integral is assumed. The subsequent Stein cancellation gives (4.11). -/
theorem hasDerivAt_split_parisiStep_before_ibp {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (m' a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => parisiStep m' (a - w) (parisiStep m w A) x)
      (∫ z, splitVarianceVelocity A A' A'' m a x v z *
        tiltWeight m' (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)) v := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  have hB2 (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w) hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hj := continuous_parisiStep_variance_spatial hC2 hc'' hm.1
  let lo := v / 2
  let hi := (a + v) / 2
  let K := Set.Icc lo hi
  have hvlo : lo < v := by dsimp [lo]; linarith [hv.1]
  have hvhi : v < hi := by dsimp [hi]; linarith [hv.2]
  have hK (w : ℝ) (hw : w ∈ K) : w ∈ Set.Ioo 0 a := by
    rcases hw with ⟨hw0, hw1⟩
    dsimp [lo, hi] at hw0 hw1
    constructor <;> linarith [hv.1, hv.2]
  have hvK : v ∈ K := ⟨hvlo.le, hvhi.le⟩
  have hcont : ContinuousOn (fun w => 1 / (2 * Real.sqrt (a - w))) K := by
    apply continuousOn_const.div (continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id))).continuousOn
    intro w hw
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (sub_pos.mpr (hK w hw).2)).ne'
  obtain ⟨L, hL⟩ := (show IsCompact K from isCompact_Icc).exists_bound_of_continuousOn hcont
  obtain ⟨C, hC⟩ := (show IsCompact K from isCompact_Icc).exists_bound_of_continuousOn
    (hj.1.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hbound (w : ℝ) (hw : w ∈ K) (z : ℝ) :
      |parisiStep m w A (x + Real.sqrt (a - w) * z)| ≤ (C + |x|) + Real.sqrt a * |z| := by
    have hb0 : |parisiStep m w A 0| ≤ C := by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using! hC w hw
    have hl := parisiC2_dist_le (hB2 w) (x + Real.sqrt (a - w) * z) 0
    have hsqrt : Real.sqrt (a - w) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith [(hK w hw).1])
    have htri := abs_add_le x (Real.sqrt (a - w) * z)
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at htri
    have htri2 := abs_sub_le (parisiStep m w A (x + Real.sqrt (a - w) * z))
      (parisiStep m w A 0) 0
    simp only [sub_zero] at htri2
    simp only [sub_zero] at hl
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (abs_nonneg z)]
  have hbound' (w : ℝ) (hw : w ∈ K) (z : ℝ) :
      |splitVarianceVelocity A A' A'' m a x w z| ≤ 1 / 2 + |L| * |z| := by
    let y := x + Real.sqrt (a - w) * z
    have hb1 := (hB2 w).abs_first_le_one y
    have hb2 : (stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2 ∈ Set.Icc 0 (1 / 2) := by
      have H := deriv_parisiStep_variance_mem_Icc hA hC2 hc.measurable hc'.measurable hc''.measurable
        hm y (hK w hw).1
      rwa [(hasDerivAt_parisiStep_variance hA hC2 hc.measurable hc'.measurable hc''.measurable
        m y (hK w hw).1).deriv] at H
    have hcoef : |1 / (2 * Real.sqrt (a - w))| ≤ |L| := by
      have hh : |1 / (2 * Real.sqrt (a - w))| ≤ L := by
        simpa only [Real.norm_eq_abs] using hL w hw
      exact hh.trans (le_abs_self L)
    change |(stepD2 A A' A'' m w y + m * (stepD1 A A' m w y) ^ 2) / 2 -
      z / (2 * Real.sqrt (a - w)) * stepD1 A A' m w y| ≤ _
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hb2.1, show z / (2 * Real.sqrt (a - w)) =
      z * (1 / (2 * Real.sqrt (a - w))) by ring, abs_mul, abs_mul]
    have h2 := mul_le_mul hcoef hb1 (abs_nonneg _) (abs_nonneg L)
    nlinarith [hb2.2, mul_le_mul_of_nonneg_left h2 (abs_nonneg z)]
  have hmeas (w : ℝ) : Measurable (fun z => parisiStep m w A (x + Real.sqrt (a - w) * z)) :=
    (measurable_parisiStep hc.measurable m w).comp (by fun_prop)
  have hmeas' (w : ℝ) : Measurable (splitVarianceVelocity A A' A'' m a x w) := by
    unfold splitVarianceVelocity
    have h1 := (measurable_stepD1 hc.measurable hc'.measurable m w).comp
      (show Measurable (fun z => x + Real.sqrt (a - w) * z) by fun_prop)
    have h2 := (measurable_stepD2 hc.measurable hc'.measurable hc''.measurable m w).comp
      (show Measurable (fun z => x + Real.sqrt (a - w) * z) by fun_prop)
    exact (h2.add ((h1.pow_const 2).const_mul m)).div_const 2 |>.sub
      ((measurable_id.div_const _).mul h1)
  have H := hasDerivAt_parisiStep_param_local (m := m')
    (F := fun w z => parisiStep m w A (x + Real.sqrt (a - w) * z))
    (F' := splitVarianceVelocity A A' A'' m a x)
    (C := C + |x|) (D := Real.sqrt a) (C' := 1 / 2) (D' := |L|)
    (Icc_mem_nhds hvlo hvhi) (Real.sqrt_nonneg a) (abs_nonneg L)
    (fun w hw z => hasDerivAt_parisiStep_split_field hA hC2 hc'' hm.1 a x z (hK w hw))
    (fun w _ => hmeas w) (fun w _ => hmeas' w) hbound hbound'
  simpa only [parisiStep, tiltWeight, Real.sqrt_one, one_mul, zero_add] using! H

/-- Scalar Gaussian Stein for the actual normalized Parisi tilt, including mass zero. -/
theorem integral_mul_first_tiltWeight {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'')
    (hmeas : Measurable A) (hmeas' : Measurable A') (hmeas'' : Measurable A'') (m v x : ℝ) :
    (∫ z, z * (A' (x + Real.sqrt v * z) * tiltWeight m v A x z) ∂(gaussianReal 0 1)) =
      Real.sqrt v * ∫ z, (A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) *
        tiltWeight m v A x z ∂(gaussianReal 0 1) := by
  have hLip : ∀ y z, |A y - A z| ≤ 1 * |y - z| := fun y z => by
    simpa only [one_mul] using parisiC2_dist_le hC2 y z
  have h1m : Measurable (fun z => A' (x + Real.sqrt v * z)) := hmeas'.comp (by fun_prop)
  have h2m : Measurable (fun z => A'' (x + Real.sqrt v * z)) := hmeas''.comp (by fun_prop)
  have hbound (y : ℝ) : |A'' y + m * (A' y) ^ 2| ≤ 1 + |m| := by
    have hsq : (A' y) ^ 2 ≤ 1 := by
      nlinarith [hC2.abs_first_le_one y, sq_abs (A' y), abs_nonneg (A' y)]
    calc
      |A'' y + m * (A' y) ^ 2| ≤ |A'' y| + |m * (A' y) ^ 2| := abs_add_le _ _
      _ = |A'' y| + |m| * (A' y) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (A' y))]
      _ ≤ 1 + |m| := by nlinarith [hC2.abs_second_le_one y,
        mul_le_mul_of_nonneg_left hsq (abs_nonneg m)]
  have hgi := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one hLip hA hmeas x
    h1m (b := 0) (le_refl 0) (a := 1)
    (fun z => by simpa using hC2.abs_first_le_one (x + Real.sqrt v * z))
  have hxgi : Integrable (fun z => z * (A' (x + Real.sqrt v * z) * tiltWeight m v A x z))
      (gaussianReal 0 1) := by
    have H := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one hLip hA hmeas x
      (f := fun z => z * A' (x + Real.sqrt v * z))
      (measurable_id.mul h1m) (b := 1) zero_le_one (a := 0) (fun z => ?_)
    · simpa only [mul_assoc] using H
    · rw [abs_mul, zero_add, one_mul]
      nlinarith [hC2.abs_first_le_one (x + Real.sqrt v * z), abs_nonneg z]
  have hg'i := integrable_mul_tiltWeight_of_bound (m := m) (v := v) zero_le_one hLip hA hmeas x
    (h2m.add ((h1m.pow_const 2).const_mul m)) (b := 0) (le_refl 0) (a := 1 + |m|)
    (fun z => by simpa using hbound (x + Real.sqrt v * z))
  have hdA (z : ℝ) : HasDerivAt (fun u => A (x + Real.sqrt v * u))
      (Real.sqrt v * A' (x + Real.sqrt v * z)) z := by
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using!
      (hC2.1 _).comp z (((hasDerivAt_id z).const_mul (Real.sqrt v)).const_add x)
  have hdA' (z : ℝ) : HasDerivAt (fun u => A' (x + Real.sqrt v * u))
      (Real.sqrt v * A'' (x + Real.sqrt v * z)) z := by
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using!
      (hC2.2.1 _).comp z (((hasDerivAt_id z).const_mul (Real.sqrt v)).const_add x)
  have hdW (z : ℝ) : HasDerivAt (fun u => tiltWeight m v A x u)
      (Real.sqrt v * m * A' (x + Real.sqrt v * z) * tiltWeight m v A x z) z := by
    by_cases hm : m = 0
    · simpa [tiltWeight, hm] using hasDerivAt_const z (1 : ℝ)
    · simp only [tiltWeight, if_neg hm]
      apply (((hdA z).const_mul m).exp.div_const _).congr_deriv
      ring
  have H := gaussianReal_stein_of_hasDerivAt
    (fun z => A' (x + Real.sqrt v * z) * tiltWeight m v A x z)
    (fun z => Real.sqrt v * ((A'' (x + Real.sqrt v * z) + m * (A' (x + Real.sqrt v * z)) ^ 2) *
      tiltWeight m v A x z)) (fun z => ?_) hgi hxgi (hg'i.const_mul (Real.sqrt v))
  · simpa only [integral_const_mul] using H
  · apply ((hdA' z).mul (hdW z)).congr_deriv
    ring

/-- Talagrand's split-variance identity (4.11), on the genuine two-step recursion. -/
theorem hasDerivAt_split_parisiStep {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (m' a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => parisiStep m' (a - w) (parisiStep m w A) x)
      ((m - m') / 2 * ∫ z, (stepD1 A A' m v (x + Real.sqrt (a - v) * z)) ^ 2 *
        tiltWeight m' (a - v) (parisiStep m v A) x z ∂(gaussianReal 0 1)) v := by
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt
  have hc' : Continuous A' := continuous_iff_continuousAt.mpr fun y => (hC2.2.1 y).continuousAt
  let B := parisiStep m v A
  let B' := stepD1 A A' m v
  let B'' := stepD2 A A' A'' m v
  have hB : HasLinearGrowth B := hasLinearGrowth_parisiStep hA hc.measurable m v
  have hBm : Measurable B := measurable_parisiStep hc.measurable m v
  have hB'm : Measurable B' := measurable_stepD1 hc.measurable hc'.measurable m v
  have hB''m : Measurable B'' := measurable_stepD2 hc.measurable hc'.measurable hc''.measurable m v
  have hB2 : HasParisiC2 B B' B'' := hasParisiC2_parisiStep_nonneg hm.1 hm.2 hC2 hA
    hc.measurable hc'.measurable hc''.measurable
  have hLip : ∀ y z, |B y - B z| ≤ 1 * |y - z| := fun y z => by
    simpa only [one_mul] using parisiC2_dist_le hB2 y z
  let W := tiltWeight m' (a - v) B x
  let Q := fun z => B'' (x + Real.sqrt (a - v) * z) * W z
  let R := fun z => (B' (x + Real.sqrt (a - v) * z)) ^ 2 * W z
  let P := fun z => z * (B' (x + Real.sqrt (a - v) * z) * W z)
  have hQ : Integrable Q (gaussianReal 0 1) :=
    integrable_mul_tiltWeight_of_bound (m := m') (v := a - v) zero_le_one hLip hB hBm x
      (hB''m.comp (by fun_prop)) (b := 0) (le_refl 0) (a := 1)
      (fun z => by simpa using hB2.abs_second_le_one (x + Real.sqrt (a - v) * z))
  have hR : Integrable R (gaussianReal 0 1) := by
    apply integrable_mul_tiltWeight_of_bound (m := m') (v := a - v) zero_le_one hLip hB hBm x
      (f := fun z => (B' (x + Real.sqrt (a - v) * z)) ^ 2)
      ((hB'm.comp (by fun_prop)).pow_const 2) (b := 0) (le_refl 0) (a := 1)
    intro z
    rw [zero_mul, add_zero, abs_of_nonneg (sq_nonneg (B' (x + Real.sqrt (a - v) * z)))]
    nlinarith [hB2.abs_first_le_one (x + Real.sqrt (a - v) * z),
      sq_abs (B' (x + Real.sqrt (a - v) * z)), abs_nonneg (B' (x + Real.sqrt (a - v) * z))]
  have hP : Integrable P (gaussianReal 0 1) := by
    have H := integrable_mul_tiltWeight_of_bound (m := m') (v := a - v) zero_le_one hLip hB hBm x
      (f := fun z => z * B' (x + Real.sqrt (a - v) * z))
      (measurable_id.mul (hB'm.comp (by fun_prop))) (b := 1) zero_le_one (a := 0) (fun z => ?_)
    · simpa only [P, mul_assoc] using H
    · rw [abs_mul, zero_add, one_mul]
      nlinarith [hB2.abs_first_le_one (x + Real.sqrt (a - v) * z), abs_nonneg z]
  have hstein := integral_mul_first_tiltWeight hB hB2 hBm hB'm hB''m m' (a - v) x
  have hsplit : (∫ z, (B'' (x + Real.sqrt (a - v) * z) +
        m' * (B' (x + Real.sqrt (a - v) * z)) ^ 2) * W z ∂(gaussianReal 0 1)) =
      (∫ z, Q z ∂(gaussianReal 0 1)) + m' * ∫ z, R z ∂(gaussianReal 0 1) := by
    simp only [add_mul, mul_assoc]
    exact (integral_add hQ (hR.const_mul m')).trans (by rw [integral_const_mul])
  change (∫ z, P z ∂(gaussianReal 0 1)) = Real.sqrt (a - v) *
    (∫ z, (B'' (x + Real.sqrt (a - v) * z) + m' * (B' (x + Real.sqrt (a - v) * z)) ^ 2) *
      W z ∂(gaussianReal 0 1)) at hstein
  rw [hsplit] at hstein
  apply (hasDerivAt_split_parisiStep_before_ibp hA hC2 hc'' hm m' a x hv).congr_deriv
  have hvel : (fun z => splitVarianceVelocity A A' A'' m a x v z * W z) =
      fun z => (1 / 2) * Q z + (m / 2) * R z - (1 / (2 * Real.sqrt (a - v))) * P z := by
    funext z
    dsimp [splitVarianceVelocity, Q, R, P, B', B'']
    ring
  change (∫ z, splitVarianceVelocity A A' A'' m a x v z * W z ∂(gaussianReal 0 1)) =
    (m - m') / 2 * ∫ z, R z ∂(gaussianReal 0 1)
  rw [hvel]
  have hsum : Integrable (fun z => (1 / 2) * Q z + (m / 2) * R z) (gaussianReal 0 1) :=
    (hQ.const_mul (1 / 2)).add (hR.const_mul (m / 2))
  rw [integral_sub hsum (hP.const_mul _),
    integral_add (hQ.const_mul (1 / 2)) (hR.const_mul (m / 2)), integral_const_mul,
    integral_const_mul, integral_const_mul, hstein]
  have hs : Real.sqrt (a - v) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hv.2)).ne'
  field_simp
  ring

/-- Equation (4.11) for every actual scalar Parisi recursion input; no additional
regularity or integrability hypothesis is required. -/
theorem hasDerivAt_split_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) (m' a x : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (fun w => parisiStep m' (a - w) (parisiStep m w (parisiF s β j)) x)
      ((m - m') / 2 * ∫ z,
        (stepD1 (parisiF s β j) (parisiFDeriv s β j) m v (x + Real.sqrt (a - v) * z)) ^ 2 *
          tiltWeight m' (a - v) (parisiStep m v (parisiF s β j)) x z ∂(gaussianReal 0 1)) v :=
  hasDerivAt_split_parisiStep (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) hm m' a x hv

/-- The split-variance derivative is nonnegative when the inner mass is at
least the outer mass. This is the immediate sign consequence of (4.11). -/
theorem deriv_split_parisiStep_nonneg {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hc'' : Continuous A'')
    {m m' : ℝ} (hm : m ∈ Set.Icc 0 1) (hmm' : m' ≤ m) (a x : ℝ)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    0 ≤ deriv (fun w => parisiStep m' (a - w) (parisiStep m w A) x) v := by
  rw [(hasDerivAt_split_parisiStep hA hC2 hc'' hm m' a x hv).deriv]
  refine mul_nonneg (div_nonneg (sub_nonneg.mpr hmm') (by norm_num)) (integral_nonneg fun z => ?_)
  have hmeas : Measurable A :=
    (continuous_iff_continuousAt.mpr fun y => (hC2.1 y).continuousAt).measurable
  exact mul_nonneg (sq_nonneg _) (tiltWeight_nonneg
    (hasLinearGrowth_parisiStep hA hmeas m v) (measurable_parisiStep hmeas m v) x z)

end SpinGlass.Targets
