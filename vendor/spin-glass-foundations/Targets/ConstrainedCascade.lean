module

/-
# The overlap-constrained cascade and the induction in Lemma 2.6

Definitions (2.26)--(2.28) use the actual overlap-restricted partition sum.
Its positivity, and every logarithm identity below, require attainable overlap.
The final comparison is the deterministic part of Lemma 2.6; the Gaussian
concentration estimate completing that lemma is not supplied here.
-/
public import Targets.CascadeEventBound

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- Indicator of the overlap event. -/
noncomputable def overlapEvent (n : ℕ) (u : ℝ) (σ τ : Config n) : ℝ :=
  if overlap n σ τ = u then 1 else 0

/-- The sum in (2.26), before taking its logarithm. -/
noncomputable def constrainedZ (n : ℕ) (U : EnergySpace n) (h t u : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ σ : Config n, ∑ τ : Config n,
    if overlap n σ τ = u then Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) else 0

noncomputable def constrainedBase (n : ℕ) (U : EnergySpace n) (h t u : ℝ)
    (x y : Fin n → ℝ) : ℝ := Real.log (constrainedZ n U h t u x y)

theorem constrainedZ_nonneg (n : ℕ) (U : EnergySpace n) (h t u : ℝ) (x y : Fin n → ℝ) :
    0 ≤ constrainedZ n U h t u x y := by
  apply Finset.sum_nonneg
  intro σ _
  apply Finset.sum_nonneg
  intro τ _
  split_ifs <;> positivity

theorem exp_pair_le_constrainedZ {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    {σ τ : Config n} (hu : overlap n σ τ = u) (x y : Fin n → ℝ) :
    Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) ≤ constrainedZ n U h t u x y := by
  have hn : ∀ ρ υ : Config n,
      0 ≤ (if overlap n ρ υ = u then Real.exp (guerraH n U h t x ρ + guerraH n U h t y υ) else 0) :=
    fun _ _ => by split_ifs <;> positivity
  calc
    _ = (if overlap n σ τ = u then Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) else 0) :=
      (if_pos hu).symm
    _ ≤ ∑ υ : Config n,
        if overlap n σ υ = u then Real.exp (guerraH n U h t x σ + guerraH n U h t y υ) else 0 :=
      Finset.single_le_sum (fun υ _ => hn σ υ) (Finset.mem_univ τ)
    _ ≤ constrainedZ n U h t u x y :=
      Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg (fun υ _ => hn ρ υ)) (Finset.mem_univ σ)

theorem constrainedZ_pos {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    0 < constrainedZ n U h t u x y := by
  obtain ⟨σ, τ, hu⟩ := hu
  exact (Real.exp_pos _).trans_le (exp_pair_le_constrainedZ U h t u hu x y)

theorem constrainedZ_le (n : ℕ) (U : EnergySpace n) (h t u : ℝ) (x y : Fin n → ℝ) :
    constrainedZ n U h t u x y ≤
      ∑ σ : Config n, ∑ τ : Config n, Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) := by
  apply Finset.sum_le_sum
  intro σ _
  apply Finset.sum_le_sum
  intro τ _
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem constrainedBase_le {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    constrainedBase n U h t u x y ≤ coupledBase n U h t x y :=
  Real.log_le_log (constrainedZ_pos U h t u hu x y) (constrainedZ_le n U h t u x y)

theorem pair_le_constrainedBase {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    {σ τ : Config n} (hu : overlap n σ τ = u) (x y : Fin n → ℝ) :
    guerraH n U h t x σ + guerraH n U h t y τ ≤ constrainedBase n U h t u x y := by
  have hh := Real.log_le_log (Real.exp_pos _) (exp_pair_le_constrainedZ U h t u hu x y)
  simpa only [Real.log_exp, constrainedBase] using hh

theorem measurable_constrainedBase (n : ℕ) (U : EnergySpace n) (h t u : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => constrainedBase n U h t u p.1 p.2) := by
  unfold constrainedBase constrainedZ
  apply Measurable.log
  apply Finset.measurable_sum
  intro σ _
  apply Finset.measurable_sum
  intro τ _
  by_cases hu : overlap n σ τ = u
  · simp only [if_pos hu]
    exact (((measurable_guerraH n U h t σ).comp measurable_fst).add
      ((measurable_guerraH n U h t τ).comp measurable_snd)).exp
  · simp only [if_neg hu]
    exact measurable_const

theorem constrainedBase_growth {n : ℕ} (U : EnergySpace n) (h u : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    CoupledGrowth (constrainedBase n U h t u) := by
  obtain ⟨C, D, hD, hb⟩ := (coupledBase_growth n U h ht).bound
  refine ⟨measurable_constrainedBase n U h t u,
    |C| + 2 * uAbs n U + 2 * (n * |h|), D + 1, by positivity, fun x y => ?_⟩
  obtain ⟨σ, τ, hστ⟩ := hu
  have hlo := pair_le_constrainedBase U h t u hστ x y
  have hhi := constrainedBase_le U h t u ⟨σ, τ, hστ⟩ x y
  have hH : |guerraH n U h t x σ + guerraH n U h t y τ| ≤
      2 * uAbs n U + 2 * (n * |h|) + l1 x + l1 y := by
    have hx := abs_guerraH_le n U h ht.1 ht.2 x σ
    have hy := abs_guerraH_le n U h ht.1 ht.2 y τ
    nlinarith [abs_add_le (guerraH n U h t x σ) (guerraH n U h t y τ),
      abs_le_uAbs n U σ, abs_le_uAbs n U τ]
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (guerraH n U h t x σ + guerraH n U h t y τ),
      mul_nonneg hD (add_nonneg (l1_nonneg x) (l1_nonneg y)), abs_nonneg C]
  · nlinarith [hb x y, le_abs_self (coupledBase n U h t x y), le_abs_self C,
      uAbs_nonneg n U, mul_nonneg (Nat.cast_nonneg n) (abs_nonneg h), l1_nonneg x, l1_nonneg y]

/-- The Gibbs overlap-event probability is the ratio of the two partition sums. -/
theorem coupledGibbsAvg_overlapEvent (n : ℕ) (U : EnergySpace n) (h t u : ℝ)
    (x y : Fin n → ℝ) :
    coupledGibbsAvg n U h t (overlapEvent n u) x y = constrainedZ n U h t u x y /
      ∑ σ : Config n, ∑ τ : Config n, Real.exp (guerraH n U h t x σ + guerraH n U h t y τ) := by
  unfold coupledGibbsAvg constrainedZ
  have he : ∀ (a b : ℝ) (P : Prop) (_ : Decidable P),
      a / b * (if P then 1 else 0) = (if P then a else 0) / b := by
    intros
    split_ifs <;> simp
  simp_rw [overlapEvent, he, ← Finset.sum_div]

/-- Equation (2.34), with attainable overlap ensuring all logarithms are genuine. -/
theorem constrainedBase_eq_add_log_event {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    constrainedBase n U h t u x y = coupledBase n U h t x y +
      Real.log (coupledGibbsAvg n U h t (overlapEvent n u) x y) := by
  rw [coupledGibbsAvg_overlapEvent, Real.log_div (constrainedZ_pos U h t u hu x y).ne'
    (Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => Real.exp_pos _)
      Finset.univ_nonempty) Finset.univ_nonempty).ne']
  unfold constrainedBase coupledBase
  ring

theorem coupledGibbsAvg_event_eq_exp {n : ℕ} (U : EnergySpace n) (h t u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y : Fin n → ℝ) :
    coupledGibbsAvg n U h t (overlapEvent n u) x y =
      Real.exp (constrainedBase n U h t u x y - coupledBase n U h t x y) := by
  rw [coupledGibbsAvg_overlapEvent]
  unfold constrainedBase coupledBase
  rw [Real.exp_sub, Real.exp_log (constrainedZ_pos U h t u hu x y),
    Real.exp_log (Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => Real.exp_pos _)
      Finset.univ_nonempty) Finset.univ_nonempty)]

variable {Ω : Type*} [MeasureSpace Ω]

/-- The constrained pressure `Ψ(t,u)` from (2.28). -/
noncomputable def constrainedPhi {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) (d : ℕ) (t u : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω,
    coupledCascade n s β d (constrainedBase n (U ω) h t u) (k + 2) 0 0 ∂ℙ

/-- Restricting to an attainable overlap decreases each actual cascade level. -/
theorem constrainedCascade_le {n k : ℕ} (s : RSBScheme k) (β : ℝ) (U : EnergySpace n)
    (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledCascade n s β d (constrainedBase n U h t u) j x y ≤
      coupledCascade n s β d (coupledBase n U h t) j x y :=
  coupledCascade_mono s β d j (constrainedBase_growth U h u ht hu)
    (coupledBase_growth n U h ht) (constrainedBase_le U h t u hu) x y

theorem measurable_coupledObservable {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ) (K : Config n → Config n → ℝ) (j : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      coupledObservable n s β U h t d K j p.1 p.2) := by
  induction j with
  | zero =>
    unfold coupledObservable coupledGibbsAvg guerraH
    fun_prop
  | succ j ih =>
    simp only [coupledObservable]
    split_ifs
    · exact measurable_independentTiltAvg _ _
        ((coupledBase_growth n U h ht).cascade s β d j).measurable ih
    · exact measurable_sharedTiltAvg _ _
        ((coupledBase_growth n U h ht).cascade s β d j).measurable ih

theorem coupledObservable_nonneg {n k : ℕ} (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (d : ℕ) {K : Config n → Config n → ℝ}
    (hK : ∀ σ τ, 0 ≤ K σ τ) (j : ℕ) (x y : Fin n → ℝ) :
    0 ≤ coupledObservable n s β U h t d K j x y := by
  induction j generalizing x y with
  | zero =>
    apply Finset.sum_nonneg
    intro σ _
    apply Finset.sum_nonneg
    intro τ _
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)))) (hK σ τ)
  | succ j ih =>
    simp only [coupledObservable]
    split_ifs
    · exact independentTiltAvg_nonneg _ _ _ ih x y
    · exact sharedTiltAvg_nonneg _ _ _ ih x y

/-- Coupled masses indexed from the Gibbs base, before the final zero-mass average. -/
noncomputable def coupledMass {k : ℕ} (s : RSBScheme k) (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => if j < d then s.m (k + 1 - j) else s.m (k + 1 - j) / 2

theorem coupledMass_succ_le {k : ℕ} (s : RSBScheme k) (d j : ℕ) :
    coupledMass s d (j + 1) ≤ coupledMass s d j := by
  cases j with
  | zero =>
    simp only [coupledMass, Nat.sub_zero, s.m_top]
    split_ifs <;> norm_num
  | succ j =>
    have hmono := s.m_mono' (k + 1 - j) (by omega) (k + 1 - (j + 1)) (by omega)
    have hnonneg := s.m_nonneg (p := k + 1 - (j + 1)) (by omega)
    simp only [coupledMass]
    split_ifs <;> first | omega | linarith

theorem coupledMass_pos {k : ℕ} (s : RSBScheme k) (hs : 0 < s.m 1)
    (d j : ℕ) (hj : j ≤ k + 1) : 0 < coupledMass s d j := by
  cases j with
  | zero => exact zero_lt_one
  | succ j =>
    have hmono := s.m_mono' (k + 1 - j) (by omega) 1 (by omega)
    have hp : 0 < s.m (k + 1 - j) := hs.trans_le hmono
    simp only [coupledMass]
    split_ifs
    · exact hp
    · exact div_pos hp (by norm_num)

/-- The deterministic induction (2.34)--(2.36), in exponential form.
At `j = k + 1` this is the comparison immediately before concentration in Lemma 2.6.
The zero-mass outer average is deliberately excluded: its mass cannot appear in a denominator. -/
theorem coupledEvent_le_exp_gap {n k : ℕ} (s : RSBScheme k) (hs : 0 < s.m 1)
    (β : ℝ) (U : EnergySpace n) (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) (hj : j ≤ k + 1)
    (x y : Fin n → ℝ) :
    coupledObservable n s β U h t d (overlapEvent n u) j x y ≤
      Real.exp (coupledMass s d j *
        (coupledCascade n s β d (constrainedBase n U h t u) j x y -
          coupledCascade n s β d (coupledBase n U h t) j x y)) := by
  have hK : ∀ σ τ : Config n, 0 ≤ overlapEvent n u σ τ := by
    intros
    unfold overlapEvent
    split_ifs <;> norm_num
  induction j generalizing x y with
  | zero =>
    simp only [coupledObservable, coupledCascade, coupledMass, one_mul,
      coupledGibbsAvg_event_eq_exp U h t u hu]
    exact le_rfl
  | succ j ih =>
    have hA := (coupledBase_growth n U h ht).cascade s β d j
    have hB := (constrainedBase_growth U h u ht hu).cascade s β d j
    have hF := measurable_coupledObservable s β U h ht d (overlapEvent n u) j
    have hBA := constrainedCascade_le s β U h u ht hu d j
    have hF0 := coupledObservable_nonneg s β U h t d hK j
    have hp := coupledMass_pos s hs d (j + 1) hj
    have hmp := coupledMass_succ_le s d j
    have hbound := fun x y => ih (by omega) x y
    by_cases hjd : j < d
    · simp only [coupledObservable, coupledCascade, coupledMass, if_pos hjd]
      simp only [coupledMass, if_pos hjd] at hp hmp
      exact independentTiltAvg_le_exp_gap hp hmp hA hB hF hBA hF0 hbound x y
    · simp only [coupledObservable, coupledCascade, coupledMass, if_neg hjd]
      simp only [coupledMass, if_neg hjd] at hp hmp
      exact sharedTiltAvg_le_exp_gap hp hmp hA hB hF hBA hF0 hbound x y

/-- In particular the event probability stays at most one at every positive-mass level. -/
theorem coupledEvent_le_one {n k : ℕ} (s : RSBScheme k) (hs : 0 < s.m 1)
    (β : ℝ) (U : EnergySpace n) (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) (hj : j ≤ k + 1)
    (x y : Fin n → ℝ) :
    coupledObservable n s β U h t d (overlapEvent n u) j x y ≤ 1 := by
  refine (coupledEvent_le_exp_gap s hs β U h u ht hu d j hj x y).trans ?_
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos (coupledMass_pos s hs d j hj).le
    (sub_nonpos.mpr (constrainedCascade_le s β U h u ht hu d j x y))

/-- An attainable overlap has strictly positive tilted probability.
This includes the final zero-mass averaging step, although the pressure-gap induction does not. -/
theorem coupledEvent_pos {n k : ℕ} (s : RSBScheme k) (hs : 0 < s.m 1)
    (β : ℝ) (U : EnergySpace n) (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) (hj : j ≤ k + 2)
    (x y : Fin n → ℝ) :
    0 < coupledObservable n s β U h t d (overlapEvent n u) j x y := by
  induction j generalizing x y with
  | zero =>
    change 0 < coupledGibbsAvg n U h t (overlapEvent n u) x y
    rw [coupledGibbsAvg_event_eq_exp U h t u hu]
    exact Real.exp_pos _
  | succ j ih =>
    have hA := (coupledBase_growth n U h ht).cascade s β d j
    have hF := measurable_coupledObservable s β U h ht d (overlapEvent n u) j
    have hF0 := fun x y => ih (by omega) x y
    have hF1 := coupledEvent_le_one s hs β U h u ht hu d j (by omega)
    simp only [coupledObservable]
    split_ifs
    · exact independentTiltAvg_pos _ _ hA hF hF0 hF1 x y
    · exact sharedTiltAvg_pos _ _ hA hF hF0 hF1 x y

/-- The logarithmic comparison just before the concentration step in Lemma 2.6.
The event is proved positive; `Real.log 0` is never used to justify this inequality. -/
theorem log_coupledEvent_le_gap {n k : ℕ} (s : RSBScheme k) (hs : 0 < s.m 1)
    (β : ℝ) (U : EnergySpace n) (h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) (hj : j ≤ k + 1)
    (x y : Fin n → ℝ) :
    Real.log (coupledObservable n s β U h t d (overlapEvent n u) j x y) ≤
      coupledMass s d j *
        (coupledCascade n s β d (constrainedBase n U h t u) j x y -
          coupledCascade n s β d (coupledBase n U h t) j x y) := by
  have hh := Real.log_le_log (coupledEvent_pos s hs β U h u ht hu d j (by omega) x y)
    (coupledEvent_le_exp_gap s hs β U h u ht hu d j hj x y)
  simpa only [Real.log_exp] using hh

end SpinGlass.Targets
