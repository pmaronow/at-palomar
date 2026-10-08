module

public import Targets.Section4SquaredSlopeDerivative
public import Targets.ParisiJointMassContinuity

@[expose] public section

/-!
# The signed initial Gaussian factor

The shared outer Gaussian enters the two replicas with opposite signs.
Its covariance is negative, whereas the two inner Gaussian means are
independent. The input in the initial interval is `parisiF s β (k+1)`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- The actual signed squared-slope factor, with independent inner means. -/
noncomputable def signedSplitSlope (A A' : ℝ → ℝ) (a h v : ℝ) : ℝ :=
  ∫ z, stepD1 A A' 0 v (h + Real.sqrt (a - v) * z) *
    stepD1 A A' 0 v (h - Real.sqrt (a - v) * z) ∂(gaussianReal 0 1)

/-- The signed product of the two actual smoothed Hessians. -/
noncomputable def signedSplitHessian (A A' A'' : ℝ → ℝ) (a h v : ℝ) : ℝ :=
  ∫ z, stepD2 A A' A'' 0 v (h + Real.sqrt (a - v) * z) *
    stepD2 A A' A'' 0 v (h - Real.sqrt (a - v) * z) ∂(gaussianReal 0 1)

/-- At the independent endpoint the actual signed factor is a square. -/
theorem signedSplitSlope_top (A A' : ℝ → ℝ) (a h : ℝ) :
    signedSplitSlope A A' a h a = (stepD1 A A' 0 a h) ^ 2 := by
  simp [signedSplitSlope, pow_two]

/-- The independent endpoint is nonnegative, with no stationarity hypothesis. -/
theorem signedSplitSlope_top_nonneg (A A' : ℝ → ℝ) (a h : ℝ) :
    0 ≤ signedSplitSlope A A' a h a := by
  rw [signedSplitSlope_top]
  exact sq_nonneg _

/-- Closed endpoint continuity follows from actual joint smoothing continuity
and the unit bound on the smoothed slopes. -/
theorem continuous_signedSplitSlope {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    (a h : ℝ) : Continuous (signedSplitSlope A A' a h) := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun x => (hC2.1 x).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun x => (hC2.2.1 x).continuousAt
  have hc := (continuous_parisiStep_variance_spatial hC2 hcA'' (m := 0) le_rfl).2.1
  have hB (v : ℝ) := hasParisiC2_parisiStep_nonneg (v := v)
    (m := 0) le_rfl zero_le_one hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro v
    exact (((measurable_stepD1 hcA.measurable hcA'.measurable 0 v).comp (by fun_prop)).mul
      ((measurable_stepD1 hcA.measurable hcA'.measurable 0 v).comp (by fun_prop))).aestronglyMeasurable
  · intro v
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul ((hB v).abs_first_le_one _) ((hB v).abs_first_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · exact integrable_const 1
  · filter_upwards with z
    exact (hc.comp (by fun_prop : Continuous (fun v : ℝ => (v, h + Real.sqrt (a - v) * z)))).mul
      (hc.comp (by fun_prop : Continuous (fun v : ℝ => (v, h - Real.sqrt (a - v) * z))))

/-- The actual signed factor velocity before Gaussian integration by parts. -/
noncomputable def signedSplitVelocity (A A' A'' : ℝ → ℝ) (a h v z : ℝ) : ℝ :=
  let yp := h + Real.sqrt (a - v) * z
  let ym := h - Real.sqrt (a - v) * z
  let c := z / (2 * Real.sqrt (a - v))
  (stepD1Variance A A' A'' 0 v yp - c * stepD2 A A' A'' 0 v yp) *
      stepD1 A A' 0 v ym +
    stepD1 A A' 0 v yp *
      (stepD1Variance A A' A'' 0 v ym + c * stepD2 A A' A'' 0 v ym)

/-- Genuine differentiation of the signed factor under its Gaussian integral.
The local dominating function is affine in the outer Gaussian absolute value. -/
theorem hasDerivAt_signedSplitSlope_before_ibp {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    (a h : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (signedSplitSlope A A' a h)
      (∫ z, signedSplitVelocity A A' A'' a h v z ∂(gaussianReal 0 1)) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun x => (hC2.1 x).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun x => (hC2.2.1 x).continuousAt
  have hB (w : ℝ) := hasParisiC2_parisiStep_nonneg (v := w)
    (m := 0) le_rfl zero_le_one hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  let lo := v / 2
  let hi := (a + v) / 2
  let K := 3 * (Real.exp (Real.sqrt hi * gAbsMoment) * gAbsExpMoment (Real.sqrt hi)) /
    (2 * Real.sqrt lo)
  let L := 1 / (2 * Real.sqrt (a - hi))
  have hlo : 0 < lo := div_pos hv.1 (by norm_num)
  have hhi : hi < a := by dsimp [hi]; linarith [hv.2]
  have hJ : Set.Icc lo hi ∈ 𝓝 v :=
    Icc_mem_nhds (by dsimp [lo]; linarith [hv.1]) (by dsimp [hi]; linarith [hv.2])
  have hJ' (w : ℝ) (hw : w ∈ Set.Icc lo hi) : w ∈ Set.Ioo 0 a :=
    ⟨hlo.trans_le hw.1, hw.2.trans_lt hhi⟩
  let F := fun w z => stepD1 A A' 0 w (h + Real.sqrt (a - w) * z) *
    stepD1 A A' 0 w (h - Real.sqrt (a - w) * z)
  have hSm (w : ℝ) := measurable_stepD1 hcA.measurable hcA'.measurable 0 w
  have hTm (w : ℝ) := measurable_stepD2 hcA.measurable hcA'.measurable hcA''.measurable 0 w
  have hFm (w : ℝ) : Measurable (F w) := (hSm w |>.comp (by fun_prop)).mul
    (hSm w |>.comp (by fun_prop))
  have hDm : Measurable (signedSplitVelocity A A' A'' a h v) := by
    have hVm : Measurable (stepD1Variance A A' A'' 0 v) :=
      ((continuousOn_stepD1Variance hA hC2 hcA'' 0).comp_continuous
        (by fun_prop : Continuous (fun y : ℝ => (v, y)))
        (fun _ => ⟨hv.1, Set.mem_univ _⟩)).measurable
    exact ((hVm.comp (by fun_prop)).sub ((measurable_id.div_const _).mul
      ((hTm v).comp (by fun_prop))) |>.mul ((hSm v).comp (by fun_prop))).add
      (((hSm v).comp (by fun_prop)).mul ((hVm.comp (by fun_prop)).add
        ((measurable_id.div_const _).mul ((hTm v).comp (by fun_prop)))))
  have hd (w : ℝ) (hw : w ∈ Set.Ioo 0 a) (z : ℝ) :
      HasDerivAt (fun w => F w z) (signedSplitVelocity A A' A'' a h w z) w := by
    have hX := ((Real.hasDerivAt_sqrt (sub_pos.mpr hw.2).ne').comp w
      ((hasDerivAt_id w).const_sub a)).mul_const z
    have hp := hasDerivAt_stepD1_variance_curve hA hC2 hcA'' (m := 0) le_rfl
      (hasDerivAt_id w) (hX.const_add h) hw.1
    have hm := hasDerivAt_stepD1_variance_curve hA hC2 hcA'' (m := 0) le_rfl
      (hasDerivAt_id w) (hX.const_sub h) hw.1
    convert! hp.mul hm using 1
    dsimp only [signedSplitVelocity, id_eq, Function.comp_def]
    ring
  have hbound (w : ℝ) (hw : w ∈ Set.Icc lo hi) (z : ℝ) :
      ‖signedSplitVelocity A A' A'' a h w z‖ ≤ 2 * K + 2 * L * |z| := by
    let c := z / (2 * Real.sqrt (a - w))
    have hb (y : ℝ) : |stepD1Variance A A' A'' 0 w y| ≤ K :=
      abs_stepD1Variance_le_on_Icc hA hC2 hcA''.measurable ⟨le_rfl, zero_le_one⟩ hlo hw y
    have hKn : 0 ≤ K := (abs_nonneg _).trans (hb 0)
    have hLn : 0 ≤ L := by dsimp [L]; positivity
    have hc : |c| ≤ L * |z| := by
      dsimp [c]
      rw [abs_div, abs_of_pos (mul_pos (by norm_num)
        (Real.sqrt_pos.mpr (sub_pos.mpr (hJ' w hw).2)))]
      have HH : 1 / (2 * Real.sqrt (a - w)) ≤ L :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hw.2])) (by norm_num))
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_left HH (abs_nonneg z)
    have hcp (y : ℝ) : |c * stepD2 A A' A'' 0 w y| ≤ L * |z| := by
      rw [abs_mul]
      exact (mul_le_mul hc ((hB w).abs_second_le_one y) (abs_nonneg _)
        (mul_nonneg hLn (abs_nonneg z))).trans_eq (mul_one _)
    have hbminus (y : ℝ) : |stepD1Variance A A' A'' 0 w y -
        c * stepD2 A A' A'' 0 w y| ≤ K + L * |z| :=
      (abs_sub _ _).trans (add_le_add (hb y) (hcp y))
    have hbplus (y : ℝ) : |stepD1Variance A A' A'' 0 w y +
        c * stepD2 A A' A'' 0 w y| ≤ K + L * |z| :=
      (abs_add_le _ _).trans (add_le_add (hb y) (hcp y))
    have hbn : 0 ≤ K + L * |z| := add_nonneg hKn (mul_nonneg hLn (abs_nonneg z))
    have hp := mul_le_mul (hbminus (h + Real.sqrt (a - w) * z))
      ((hB w).abs_first_le_one (h - Real.sqrt (a - w) * z)) (abs_nonneg _) hbn
    have hm := mul_le_mul ((hB w).abs_first_le_one (h + Real.sqrt (a - w) * z))
      (hbplus (h - Real.sqrt (a - w) * z)) (abs_nonneg _) zero_le_one
    have HH := abs_add_le
      ((stepD1Variance A A' A'' 0 w (h + Real.sqrt (a - w) * z) -
          c * stepD2 A A' A'' 0 w (h + Real.sqrt (a - w) * z)) *
        stepD1 A A' 0 w (h - Real.sqrt (a - w) * z))
      (stepD1 A A' 0 w (h + Real.sqrt (a - w) * z) *
        (stepD1Variance A A' A'' 0 w (h - Real.sqrt (a - w) * z) +
          c * stepD2 A A' A'' 0 w (h - Real.sqrt (a - w) * z)))
    simp only [abs_mul, mul_one, one_mul] at HH hp hm
    change |signedSplitVelocity A A' A'' a h w z| ≤ _
    exact HH.trans (by nlinarith only [hp, hm])
  have hFi : Integrable (F v) (gaussianReal 0 1) := by
    apply Integrable.of_bound (hFm v).aestronglyMeasurable (C := 1)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul ((hB v).abs_first_le_one _) ((hB v).abs_first_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ
    (Eventually.of_forall fun w => (hFm w).aestronglyMeasurable) hFi hDm.aestronglyMeasurable
    (Eventually.of_forall fun z w hw => hbound w hw z)
    ((integrable_const (2 * K)).add ((GTFrame.expMoments_gaussianReal 0 1).integrable_abs.const_mul (2 * L)))
    (Eventually.of_forall fun z w hw => hd w (hJ' w hw) z)).2

/-- Gaussian Stein cancels the two heat terms and leaves the product of
the actual smoothed Hessians. This is the signed analogue of (4.16). -/
theorem hasDerivAt_signedSplitSlope {A A' A'' : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hC2 : HasParisiC2 A A' A'') (hcA'' : Continuous A'')
    (a h : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (signedSplitSlope A A' a h) (signedSplitHessian A A' A'' a h v) v := by
  have hcA : Continuous A := continuous_iff_continuousAt.mpr fun x => (hC2.1 x).continuousAt
  have hcA' : Continuous A' := continuous_iff_continuousAt.mpr fun x => (hC2.2.1 x).continuousAt
  have hB := hasParisiC2_parisiStep_nonneg (v := v)
    (m := 0) le_rfl zero_le_one hC2 hA hcA.measurable hcA'.measurable hcA''.measurable
  let S := stepD1 A A' 0 v
  let T := stepD2 A A' A'' 0 v
  let E := stepD3 A A' A'' 0 v
  let p := fun z => h + Real.sqrt (a - v) * z
  let n := fun z => h - Real.sqrt (a - v) * z
  let G := fun z => T (p z) * S (n z) - S (p z) * T (n z)
  let J := fun z => E (p z) * S (n z) - 2 * T (p z) * T (n z) + S (p z) * E (n z)
  let H := fun z => T (p z) * T (n z)
  have hE (x : ℝ) : HasDerivAt T (E x) x :=
    hasDerivAt_stepD2_spatial hA hC2 hcA'' ⟨le_rfl, zero_le_one⟩ hv.1 x
  obtain ⟨K, hEb⟩ : ∃ K : ℝ, ∀ x, |E x| ≤ K :=
    ⟨_, fun x => abs_stepD3_le hA hC2 hcA'' ⟨le_rfl, zero_le_one⟩ hv.1 x⟩
  have hKn : 0 ≤ K := (abs_nonneg _).trans (hEb 0)
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun x => (hB.2.1 x).continuousAt
  have hTc : Continuous T := continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt
  have hEc : Continuous E := continuous_stepD3_spatial hA hC2 hcA'' le_rfl hv.1
  have hpc : Continuous p := by dsimp [p]; fun_prop
  have hnc : Continuous n := by dsimp [n]; fun_prop
  have hGc : Continuous G := ((hTc.comp hpc).mul (hSc.comp hnc)).sub
    ((hSc.comp hpc).mul (hTc.comp hnc))
  have hJc : Continuous J := ((hEc.comp hpc).mul (hSc.comp hnc) |>.sub
    (((hTc.comp hpc).const_mul 2).mul (hTc.comp hnc))).add
      ((hSc.comp hpc).mul (hEc.comp hnc))
  have hHc : Continuous H := (hTc.comp hpc).mul (hTc.comp hnc)
  have hGb (z : ℝ) : |G z| ≤ 2 := by
    have hp := mul_le_mul (hB.abs_second_le_one (p z)) (hB.abs_first_le_one (n z))
      (abs_nonneg _) zero_le_one
    have hn := mul_le_mul (hB.abs_first_le_one (p z)) (hB.abs_second_le_one (n z))
      (abs_nonneg _) zero_le_one
    have HH := abs_sub (T (p z) * S (n z)) (S (p z) * T (n z))
    simp only [abs_mul, one_mul] at HH hp hn
    exact HH.trans (by nlinarith only [hp, hn])
  have hHb (z : ℝ) : |H z| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hB.abs_second_le_one (p z)) (hB.abs_second_le_one (n z))
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hJb (z : ℝ) : |J z| ≤ 2 * K + 2 := by
    have hp := mul_le_mul (hEb (p z)) (hB.abs_first_le_one (n z)) (abs_nonneg _) hKn
    have hn := mul_le_mul (hB.abs_first_le_one (p z)) (hEb (n z)) (abs_nonneg _) zero_le_one
    have HH := abs_add_le (E (p z) * S (n z) - 2 * T (p z) * T (n z)) (S (p z) * E (n z))
    have HH' := abs_sub (E (p z) * S (n z)) (2 * T (p z) * T (n z))
    have hb := hHb z
    simp only [H, abs_mul, one_mul, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at HH HH' hp hn hb
    exact HH.trans (by nlinarith only [HH', hp, hn, hb])
  have hGi : Integrable G (gaussianReal 0 1) :=
    Integrable.of_bound hGc.aestronglyMeasurable 2 (Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hGb z)
  have hJi : Integrable J (gaussianReal 0 1) :=
    Integrable.of_bound hJc.aestronglyMeasurable (2 * K + 2) (Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hJb z)
  have hHi : Integrable H (gaussianReal 0 1) :=
    Integrable.of_bound hHc.aestronglyMeasurable 1 (Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hHb z)
  have hxi : Integrable (fun z => z * G z) (gaussianReal 0 1) := by
    refine ((GTFrame.expMoments_gaussianReal 0 1).integrable_abs.const_mul 2).mono'
      ((continuous_id.mul hGc).aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hGb z) (abs_nonneg z)
  have hGd (z : ℝ) : HasDerivAt G (Real.sqrt (a - v) * J z) z := by
    have hp := ((hasDerivAt_id z).const_mul (Real.sqrt (a - v))).const_add h
    have hn := ((hasDerivAt_id z).const_mul (Real.sqrt (a - v))).const_sub h
    have HS := (((hE _).comp z hp).mul ((hB.2.1 _).comp z hn)).sub
      (((hB.2.1 _).comp z hp).mul ((hE _).comp z hn))
    convert! HS using 1
    dsimp only [J, p, n, id_eq, Function.comp_def, S, T]
    ring
  have hstein := gaussianReal_stein_of_hasDerivAt G
    (fun z => Real.sqrt (a - v) * J z) hGd hGi hxi (hJi.const_mul _)
  rw [integral_const_mul] at hstein
  apply (hasDerivAt_signedSplitSlope_before_ibp hA hC2 hcA'' a h hv).congr_deriv
  calc
    (∫ z, signedSplitVelocity A A' A'' a h v z ∂(gaussianReal 0 1)) =
        ∫ z, (J z / 2 + H z) - (1 / (2 * Real.sqrt (a - v))) * (z * G z)
          ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [signedSplitVelocity, J, G, H, S, T, E, p, n, stepD3]
      ring
    _ = (∫ z, J z ∂(gaussianReal 0 1)) / 2 +
        (∫ z, H z ∂(gaussianReal 0 1)) -
        (1 / (2 * Real.sqrt (a - v))) * (∫ z, z * G z ∂(gaussianReal 0 1)) := by
      have hsum : Integrable (fun z => J z / 2 + H z) (gaussianReal 0 1) := by
        simpa only [Pi.add_apply] using! (hJi.div_const 2).add hHi
      rw [integral_sub hsum (hxi.const_mul _),
        integral_add (hJi.div_const 2) hHi, integral_div, integral_const_mul]
    _ = signedSplitHessian A A' A'' a h v := by
      rw [hstein]
      change _ = ∫ z, H z ∂(gaussianReal 0 1)
      field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hv.2)).ne']
      ring

/-- The signed Gaussian derivative on every actual Parisi-recursion input. -/
theorem hasDerivAt_signedSplitSlope_parisiF {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (a h : ℝ) {v : ℝ} (hv : v ∈ Set.Ioo 0 a) :
    HasDerivAt (signedSplitSlope (parisiF s β j) (parisiFDeriv s β j) a h)
      (signedSplitHessian (parisiF s β j) (parisiFDeriv s β j) (parisiFSecond s β j) a h v) v :=
  hasDerivAt_signedSplitSlope (parisiF_hasLinearGrowth s β j) (parisiF_C2_props s β j).1
    (continuous_parisiFSecond s β j) a h hv

end SpinGlass.Targets
