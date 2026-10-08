module

/- Compatibility adaptation: current Set.domRestrict continuity interface. -/
public import Lemmas.GuerraTalagrand.Gaussian
public import Lemmas.AT.FixedPoint

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

set_option maxHeartbeats 800000

namespace SpinGlass.AT

abbrev P := (ℝ × ℝ) × (ℝ × (ℝ × ℝ))

private def signedIncrement (p : P) : ℝ :=
  if 0 ≤ p.2.2.2 then
    gtIncrementScale p.1.1 p.2.2.1 0 p.2.2.2
  else
    -gtIncrementScale p.1.1 p.2.2.1 0 (-p.2.2.2)

private lemma continuous_signedIncrement : Continuous signedIncrement := by
  unfold signedIncrement
  apply Continuous.if_le (by unfold gtIncrementScale; fun_prop)
    (by unfold gtIncrementScale; fun_prop) continuous_const (by fun_prop)
  intro p hp
  have hv : p.2.2.2 = 0 := hp.symm
  rw [hv]
  simp [gtIncrementScale]

private def lowerBranch (p : P) (lam : ℝ) : ℝ :=
  2 * Real.log 2 + standardGaussianExpectation (fun z =>
    gtRankOneStep 0
      (gtIncrementScale p.1.1 p.2.2.1 0 |p.2.2.2|) (gtPathSign p.2.2.2)
      (gtDiagonalStep 0
        (gtIncrementScale p.1.1 p.2.2.1 |p.2.2.2| p.2.1)
        (gtDiagonalStep 1
          (gtIncrementScale p.1.1 p.2.2.1 p.2.1 1)
          (gtTerminal lam)))
      (p.1.2 + p.1.1 * Real.sqrt ((1 - p.2.2.1) * p.2.1) * z)
      (p.1.2 + p.1.1 * Real.sqrt ((1 - p.2.2.1) * p.2.1) * z))
    - lam * p.2.2.2 - gtCorrection p.1.1 p.2.1 p.2.2.1

private lemma continuous_lowerBranch :
    Continuous fun w : P × ℝ => lowerBranch w.1 w.2 := by
  let F0 : P → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbase l x
  let D0 : P → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbaseD l x
  have h0 : GTFrame.GoodFam F0 D0 := GTFrame.goodFam_fLbase
  let aU : P → ℝ := fun p => gtIncrementScale p.1.1 p.2.2.1 p.2.1 1
  let F1 := GTFrame.stepM (gaussianReal 0 1) 1 (fun _ : P => 0) aU F0
  let D1 := GTFrame.stepMD (gaussianReal 0 1) 1 (fun _ : P => 0) aU F0 D0
  have h1 : GTFrame.GoodFam F1 D1 := by
    apply GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h0 one_pos
    · fun_prop
    · dsimp [aU]
      unfold gtIncrementScale
      fun_prop
  let F2 := GTFrame.stepM (gaussianReal 0 1) 1 aU (fun _ : P => 0) F1
  let D2 := GTFrame.stepMD (gaussianReal 0 1) 1 aU (fun _ : P => 0) F1 D1
  have h2 : GTFrame.GoodFam F2 D2 := by
    apply GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h1 one_pos
    · dsimp [aU]
      unfold gtIncrementScale
      fun_prop
    · fun_prop
  have hF2 : ∀ p l x, F2 p l x =
      gtDiagonalStep 1 (aU p) (gtTerminal l) x.1 x.2 := by
    intro p l x
    dsimp [F2, F1, F0]
    simp only [GTFrame.stepM, gtDiagonalStep, one_ne_zero, if_false,
      one_div, inv_one, one_mul, zero_mul, add_zero, standardGaussianExpectation]
    apply congrArg Real.log
    apply integral_congr_ae
    filter_upwards with z
    rw [Real.exp_log]
    simpa [F0] using (GTFrame.integral_expShift_pos
      (GTFrame.expMoments_gaussianReal 0 1) h0 (by norm_num : (0 : ℝ) ≤ 1)
      p l 0 (aU p) (x.1 + aU p * z, x.2))
  let aD : P → ℝ := fun p => gtIncrementScale p.1.1 p.2.2.1 |p.2.2.2| p.2.1
  let F3 := GTFrame.step0 (gaussianReal 0 1) (fun _ : P => 0) aD F2
  let D3 := GTFrame.step0 (gaussianReal 0 1) (fun _ : P => 0) aD D2
  have h3 : GTFrame.GoodFam F3 D3 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h2
    · fun_prop
    · dsimp [aD]
      unfold gtIncrementScale
      fun_prop
  let F4 := GTFrame.step0 (gaussianReal 0 1) aD (fun _ : P => 0) F3
  let D4 := GTFrame.step0 (gaussianReal 0 1) aD (fun _ : P => 0) D3
  have h4 : GTFrame.GoodFam F4 D4 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h3
    · dsimp [aD]
      unfold gtIncrementScale
      fun_prop
    · fun_prop
  let aR : P → ℝ := fun p => gtIncrementScale p.1.1 p.2.2.1 0 |p.2.2.2|
  let F5 := GTFrame.step0 (gaussianReal 0 1) aR signedIncrement F4
  let D5 := GTFrame.step0 (gaussianReal 0 1) aR signedIncrement D4
  have h5 : GTFrame.GoodFam F5 D5 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h4
    · dsimp [aR]
      unfold gtIncrementScale
      fun_prop
    · exact continuous_signedIncrement
  let aO : P → ℝ := fun p => p.1.1 * Real.sqrt ((1 - p.2.2.1) * p.2.1)
  let F6 := GTFrame.step0 (gaussianReal 0 1) aO aO F5
  let D6 := GTFrame.step0 (gaussianReal 0 1) aO aO D5
  have h6 : GTFrame.GoodFam F6 D6 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h5 <;>
      dsimp [aO] <;> fun_prop
  let eval : P × ℝ → P × ℝ × (ℝ × ℝ) :=
    fun w => (w.1, w.2, (w.1.1.2, w.1.1.2))
  have hevalMap : Continuous eval := by fun_prop
  have heval := h6.contF.comp hevalMap
  have heval' : Continuous fun w : P × ℝ =>
      F6 w.1 w.2 (w.1.1.2, w.1.1.2) := by
    simpa [eval, Function.comp_def] using heval
  have hsigned : ∀ p : P,
      signedIncrement p = gtPathSign p.2.2.2 *
        gtIncrementScale p.1.1 p.2.2.1 0 |p.2.2.2| := by
    intro p
    unfold signedIncrement gtPathSign
    split_ifs with hv
    · simp [abs_of_nonneg hv]
    · rw [abs_of_neg (lt_of_not_ge hv)]
      ring
  have hF4 : ∀ p l x, F4 p l x =
      gtDiagonalStep 0 (aD p)
        (gtDiagonalStep 1 (aU p) (gtTerminal l)) x.1 x.2 := by
    intro p l x
    simp [F4, F3, GTFrame.step0, gtDiagonalStep,
      standardGaussianExpectation, hF2]
  have hF5 : ∀ p l x, F5 p l x =
      gtRankOneStep 0 (aR p) (gtPathSign p.2.2.2)
        (gtDiagonalStep 0 (aD p)
          (gtDiagonalStep 1 (aU p) (gtTerminal l))) x.1 x.2 := by
    intro p l x
    simp [F5, GTFrame.step0, gtRankOneStep, standardGaussianExpectation,
      hF4, hsigned, aR]
  have hF6 : ∀ p l, F6 p l (p.1.2, p.1.2) =
      standardGaussianExpectation (fun z =>
        gtRankOneStep 0 (aR p) (gtPathSign p.2.2.2)
          (gtDiagonalStep 0 (aD p)
            (gtDiagonalStep 1 (aU p) (gtTerminal l)))
          (p.1.2 + aO p * z) (p.1.2 + aO p * z)) := by
    intro p l
    simp [F6, GTFrame.step0, standardGaussianExpectation, hF5]
  have hlamv : Continuous fun w : P × ℝ => w.2 * w.1.2.2.2 := by fun_prop
  have hcorr : Continuous fun w : P × ℝ =>
      gtCorrection w.1.1.1 w.1.2.1 w.1.2.2.1 := by
    unfold gtCorrection
    fun_prop
  have hconst : Continuous fun _ : P × ℝ => 2 * Real.log 2 := continuous_const
  have hbase : Continuous fun w : P × ℝ =>
      2 * Real.log 2 + F6 w.1 w.2 (w.1.1.2, w.1.1.2) -
        w.2 * w.1.2.2.2 - gtCorrection w.1.1.1 w.1.2.1 w.1.2.2.1 :=
    ((hconst.add heval').sub hlamv).sub hcorr
  have heq : (fun w : P × ℝ => lowerBranch w.1 w.2) =
      fun w => 2 * Real.log 2 + F6 w.1 w.2 (w.1.1.2, w.1.1.2) -
        w.2 * w.1.2.2.2 - gtCorrection w.1.1.1 w.1.2.1 w.1.2.2.1 := by
    funext w
    unfold lowerBranch
    rw [hF6]
  rw [heq]
  exact hbase

private def regularSign (p : P) : ℝ :=
  p.2.2.2 / max |p.2.2.2| p.2.1

private def upperBranch (p : P) (lam : ℝ) : ℝ :=
  2 * Real.log 2 + standardGaussianExpectation (fun z =>
    gtRankOneStep 0
      (gtIncrementScale p.1.1 p.2.2.1 0 p.2.1) (regularSign p)
      (gtRankOneStep (1 / 2)
        (gtIncrementScale p.1.1 p.2.2.1 p.2.1 |p.2.2.2|) (regularSign p)
        (gtDiagonalStep 1
          (gtIncrementScale p.1.1 p.2.2.1 |p.2.2.2| 1)
          (gtTerminal lam)))
      (p.1.2 + p.1.1 * Real.sqrt ((1 - p.2.2.1) * p.2.1) * z)
      (p.1.2 + p.1.1 * Real.sqrt ((1 - p.2.2.1) * p.2.1) * z))
    - lam * p.2.2.2 - gtCorrection p.1.1 p.2.1 p.2.2.1

private lemma regularSign_eq_pathSign {p : P} (hq : 0 < p.2.1)
    (hqv : p.2.1 ≤ |p.2.2.2|) : regularSign p = gtPathSign p.2.2.2 := by
  have hv : p.2.2.2 ≠ 0 := by
    intro hv
    rw [hv] at hqv
    simp only [abs_zero] at hqv
    linarith
  rw [regularSign, max_eq_left hqv]
  unfold gtPathSign
  split_ifs with hv0
  · rw [abs_of_nonneg hv0]
    exact div_self hv
  · rw [abs_of_neg (lt_of_not_ge hv0)]
    field_simp

private lemma branches_agree {p : P} {lam : ℝ}
    (hq : 0 < p.2.1) (hv1 : |p.2.2.2| ≤ 1)
    (heq : p.2.1 = |p.2.2.2|) : upperBranch p lam = lowerBranch p lam := by
  have hsign := regularSign_eq_pathSign hq heq.le
  unfold upperBranch lowerBranch
  rw [hsign, heq]
  simp [gtIncrementScale, gtRankOneStep, gtDiagonalStep,
    standardGaussianExpectation]

private abbrev PPos := {p : P // 0 < p.2.1}

private lemma continuous_regularSign_pos :
    Continuous fun p : PPos => regularSign p.1 := by
  unfold regularSign
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  have : 0 < max |p.1.2.2.2| p.1.2.1 :=
    lt_of_lt_of_le p.2 (le_max_right _ _)
  exact this.ne'

private lemma continuousOn_upperBranch :
    ContinuousOn (fun w : P × ℝ => upperBranch w.1 w.2)
      {w | 0 < w.1.2.1} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let Q := {w : P × ℝ // 0 < w.1.2.1}
  let toPPos : Q → PPos := fun w => ⟨w.1.1, w.2⟩
  have htoPPos : Continuous toPPos := by fun_prop
  let F0 : PPos → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbase l x
  let D0 : PPos → ℝ → ℝ × ℝ → ℝ := fun _ l x => GTFrame.fLbaseD l x
  have h0 : GTFrame.GoodFam F0 D0 := GTFrame.goodFam_fLbase
  let aU : PPos → ℝ := fun p =>
    gtIncrementScale p.1.1.1 p.1.2.2.1 |p.1.2.2.2| 1
  let F1 := GTFrame.stepM (gaussianReal 0 1) 1 (fun _ : PPos => 0) aU F0
  let D1 := GTFrame.stepMD (gaussianReal 0 1) 1 (fun _ : PPos => 0) aU F0 D0
  have h1 : GTFrame.GoodFam F1 D1 := by
    apply GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h0 one_pos
    · fun_prop
    · dsimp [aU]
      unfold gtIncrementScale
      fun_prop
  let F2 := GTFrame.stepM (gaussianReal 0 1) 1 aU (fun _ : PPos => 0) F1
  let D2 := GTFrame.stepMD (gaussianReal 0 1) 1 aU (fun _ : PPos => 0) F1 D1
  have h2 : GTFrame.GoodFam F2 D2 := by
    apply GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h1 one_pos
    · dsimp [aU]
      unfold gtIncrementScale
      fun_prop
    · fun_prop
  have hF2 : ∀ p l x, F2 p l x =
      gtDiagonalStep 1 (aU p) (gtTerminal l) x.1 x.2 := by
    intro p l x
    dsimp [F2, F1, F0]
    simp only [GTFrame.stepM, gtDiagonalStep, one_ne_zero, if_false,
      one_div, inv_one, one_mul, zero_mul, add_zero, standardGaussianExpectation]
    apply congrArg Real.log
    apply integral_congr_ae
    filter_upwards with z
    rw [Real.exp_log]
    simpa [F0] using (GTFrame.integral_expShift_pos
      (GTFrame.expMoments_gaussianReal 0 1) h0 (by norm_num : (0 : ℝ) ≤ 1)
      p l 0 (aU p) (x.1 + aU p * z, x.2))
  let aH : PPos → ℝ := fun p =>
    gtIncrementScale p.1.1.1 p.1.2.2.1 p.1.2.1 |p.1.2.2.2|
  let bH : PPos → ℝ := fun p => regularSign p.1 * aH p
  let F3 := GTFrame.stepM (gaussianReal 0 1) (1 / 2) aH bH F2
  let D3 := GTFrame.stepMD (gaussianReal 0 1) (1 / 2) aH bH F2 D2
  have h3 : GTFrame.GoodFam F3 D3 := by
    apply GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h2 (by norm_num)
    · dsimp [aH]
      unfold gtIncrementScale
      fun_prop
    · dsimp [bH]
      exact continuous_regularSign_pos.mul (by
        dsimp [aH]
        unfold gtIncrementScale
        fun_prop)
  have hF3 : ∀ p l x, F3 p l x =
      gtRankOneStep (1 / 2) (aH p) (regularSign p.1)
        (gtDiagonalStep 1 (aU p) (gtTerminal l)) x.1 x.2 := by
    intro p l x
    simp [F3, GTFrame.stepM, gtRankOneStep, standardGaussianExpectation,
      hF2, bH]
  let aR : PPos → ℝ := fun p =>
    gtIncrementScale p.1.1.1 p.1.2.2.1 0 p.1.2.1
  let bR : PPos → ℝ := fun p => regularSign p.1 * aR p
  let F4 := GTFrame.step0 (gaussianReal 0 1) aR bR F3
  let D4 := GTFrame.step0 (gaussianReal 0 1) aR bR D3
  have h4 : GTFrame.GoodFam F4 D4 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h3
    · dsimp [aR]
      unfold gtIncrementScale
      fun_prop
    · dsimp [bR]
      exact continuous_regularSign_pos.mul (by
        dsimp [aR]
        unfold gtIncrementScale
        fun_prop)
  have hF4 : ∀ p l x, F4 p l x =
      gtRankOneStep 0 (aR p) (regularSign p.1)
        (gtRankOneStep (1 / 2) (aH p) (regularSign p.1)
          (gtDiagonalStep 1 (aU p) (gtTerminal l))) x.1 x.2 := by
    intro p l x
    simp [F4, GTFrame.step0, gtRankOneStep, standardGaussianExpectation,
      hF3, bR]
  let aO : PPos → ℝ := fun p =>
    p.1.1.1 * Real.sqrt ((1 - p.1.2.2.1) * p.1.2.1)
  let F5 := GTFrame.step0 (gaussianReal 0 1) aO aO F4
  let D5 := GTFrame.step0 (gaussianReal 0 1) aO aO D4
  have h5 : GTFrame.GoodFam F5 D5 := by
    apply GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h4 <;>
      dsimp [aO] <;> fun_prop
  let eval : Q → PPos × ℝ × (ℝ × ℝ) := fun w =>
    (toPPos w, w.1.2, (w.1.1.1.2, w.1.1.1.2))
  have hevalMap : Continuous eval := by fun_prop
  have heval := h5.contF.comp hevalMap
  have heval' : Continuous fun w : Q =>
      F5 (toPPos w) w.1.2 (w.1.1.1.2, w.1.1.1.2) := by
    simpa [eval, Function.comp_def] using heval
  have hF5 : ∀ p l, F5 p l (p.1.1.2, p.1.1.2) =
      standardGaussianExpectation (fun z =>
        gtRankOneStep 0 (aR p) (regularSign p.1)
          (gtRankOneStep (1 / 2) (aH p) (regularSign p.1)
            (gtDiagonalStep 1 (aU p) (gtTerminal l)))
          (p.1.1.2 + aO p * z) (p.1.1.2 + aO p * z)) := by
    intro p l
    simp [F5, GTFrame.step0, standardGaussianExpectation, hF4]
  have hconst : Continuous fun _ : Q => 2 * Real.log 2 := continuous_const
  have hlamv : Continuous fun w : Q => w.1.2 * w.1.1.2.2.2 := by fun_prop
  have hcorr : Continuous fun w : Q =>
      gtCorrection w.1.1.1.1 w.1.1.2.1 w.1.1.2.2.1 := by
    unfold gtCorrection
    fun_prop
  have hbase : Continuous fun w : Q =>
      2 * Real.log 2 + F5 (toPPos w) w.1.2
        (w.1.1.1.2, w.1.1.1.2) - w.1.2 * w.1.1.2.2.2 -
          gtCorrection w.1.1.1.1 w.1.1.2.1 w.1.1.2.2.1 :=
    ((hconst.add heval').sub hlamv).sub hcorr
  have heq : ({w : P × ℝ | 0 < w.1.2.1}.domRestrict
      (fun w => upperBranch w.1 w.2)) =
      fun w : Q => 2 * Real.log 2 + F5 (toPPos w) w.1.2
        (w.1.1.1.2, w.1.1.1.2) - w.1.2 * w.1.1.2.2.2 -
          gtCorrection w.1.1.1.1 w.1.1.2.1 w.1.1.2.2.1 := by
    funext w
    unfold Set.domRestrict upperBranch
    rw [hF5]
  rw [heq]
  exact hbase

def admissible : Set (P × ℝ) :=
  {w | 0 < w.1.2.1 ∧ |w.1.2.2.2| ≤ 1}

private lemma gtFunctional_eq_piecewise {w : P × ℝ}
    (hw : w ∈ admissible) :
    gtFunctional w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2 =
      if w.1.2.1 ≤ |w.1.2.2.2| then upperBranch w.1 w.2
      else lowerBranch w.1 w.2 := by
  rcases hw with ⟨hq, hv1⟩
  split_ifs with hqv
  · unfold upperBranch
    rw [regularSign_eq_pathSign hq hqv]
    rcases hv1.eq_or_lt with hv | hv
    · simpa [hv] using (gtFunctional_formula_abs_v_eq_one
        w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2
        hq (hqv.trans hv1) hv)
    · exact gtFunctional_formula_q_le_abs_v_lt_one
        w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2
        hq hqv hv
  · have hvq : |w.1.2.2.2| < w.1.2.1 := lt_of_not_ge hqv
    unfold lowerBranch
    rcases (abs_nonneg w.1.2.2.2).eq_or_lt with hv | hv
    · have hvzero : w.1.2.2.2 = 0 := abs_eq_zero.mp hv.symm
      simpa [hvzero, gtIncrementScale, gtRankOneStep,
        standardGaussianExpectation] using (gtFunctional_formula_abs_v_eq_zero
        w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2 hq hv.symm
      )
    · exact gtFunctional_formula_abs_v_lt_q
        w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2 hv hvq

lemma continuousOn_gtFunctional_params :
    ContinuousOn (fun w : P × ℝ =>
      gtFunctional w.1.1.1 w.1.1.2 w.1.2.1 w.1.2.2.1 w.2 w.1.2.2.2)
      admissible := by
  have huOn : ContinuousOn (fun w : P × ℝ => upperBranch w.1 w.2)
      admissible := continuousOn_upperBranch.mono (by
    intro w hw
    exact hw.1)
  rw [continuousOn_iff_continuous_domRestrict] at huOn ⊢
  have hl : Continuous (fun w : admissible => lowerBranch w.1.1 w.1.2) :=
    continuous_lowerBranch.comp continuous_subtype_val
  have hq : Continuous (fun w : admissible => w.1.1.2.1) := by fun_prop
  have hv : Continuous (fun w : admissible => |w.1.1.2.2.2|) := by fun_prop
  have hpiece : Continuous fun w : admissible =>
      if w.1.1.2.1 ≤ |w.1.1.2.2.2| then upperBranch w.1.1 w.1.2
      else lowerBranch w.1.1 w.1.2 := by
    apply Continuous.if_le huOn hl hq hv
    intro w heq
    exact branches_agree w.2.1 w.2.2 heq
  apply hpiece.congr
  intro w
  exact (gtFunctional_eq_piecewise w.2).symm

/-- `gtFunctional` (with `q = rsQ β h`) is continuous on
`K × [0,1] × [-1,1] × [-1,1]`
when `K` lies in the strict AT region. -/
lemma continuousOn_gtFunctional (K : Set (ℝ × ℝ))
    (hK : K ⊆ strictATRegion) :
    ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) =>
      gtFunctional w.1.1 w.1.2 (rsQ w.1.1 w.1.2)
        w.2.1 w.2.2.2 w.2.2.1)
      (K ×ˢ (Icc (0 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))) := by
  let S : Set ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) :=
    K ×ˢ (Icc (0 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
  let Φ : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) → P × ℝ := fun w =>
    (((w.1.1, w.1.2), (rsQ w.1.1 w.1.2, (w.2.1, w.2.2.1))), w.2.2.2)
  have hqK : ContinuousOn (fun p : ℝ × ℝ => rsQ p.1 p.2) K :=
    continuousOn_rsQ_of_pos_field (fun p hp => (hK hp).2.1)
  have hqS : ContinuousOn
      (fun w : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) => rsQ w.1.1 w.1.2) S :=
    hqK.comp continuousOn_fst (by
      intro w hw
      exact hw.1)
  have hΦ : ContinuousOn Φ S := by
    dsimp [Φ]
    fun_prop
  have hΦmem : MapsTo Φ S admissible := by
    intro w hw
    have hpar := hK hw.1
    refine ⟨rsQ_pos hpar.1 hpar.2.1, ?_⟩
    exact abs_le.mpr hw.2.2.1
  have hcomp := continuousOn_gtFunctional_params.comp hΦ hΦmem
  simpa [S, Φ, Function.comp_def] using hcomp


end SpinGlass.AT
