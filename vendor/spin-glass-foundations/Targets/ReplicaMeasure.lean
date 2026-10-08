module

/-
# From the coupled replica measures to the Guerra remainder

This file connects Lemma 2.7's individual `μ_r` to the mass-weighted replica
expectation used in `TalagrandConvergence`. In particular, per-level overlap
concentration gives exactly the concentration input needed there. It does not
assume, or claim to prove, Proposition 2.3 itself.
-/
public import Targets.CoupledCascade
public import Targets.TalagrandConvergence

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

theorem measurable_guerraOuterAvg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t : ℝ) (d : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (l : ℕ) : Measurable (guerraOuterAvg n s β U h t d F l) := by
  induction l with
  | zero => exact hF
  | succ l ih =>
    exact (measurable_guerraStepAvg_joint s β h t (d + l)
      (f := fun _ => guerraOuterAvg n s β U h t d F l)
      (ih.comp measurable_snd)).comp (measurable_const.prodMk measurable_id)

theorem measurable_guerraOuterAvg_joint {n k : ℕ} (s : RSBScheme k) (β h t : ℝ)
    (d : ℕ) {F : EnergySpace n → (Fin n → ℝ) → ℝ}
    (hF : Measurable (fun p : EnergySpace n × (Fin n → ℝ) => F p.1 p.2)) (l : ℕ) :
    Measurable (fun p : EnergySpace n × (Fin n → ℝ) =>
      guerraOuterAvg n s β p.1 h t d (F p.1) l p.2) := by
  induction l with
  | zero => exact hF
  | succ l ih =>
    exact measurable_guerraStepAvg_joint s β h t (d + l)
      (f := fun U => guerraOuterAvg n s β U h t d (F U) l) ih

theorem guerraOuterAvg_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d l : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    guerraOuterAvg n s β U h t d (fun _ => c) l x = c := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    simp only [guerraOuterAvg, show guerraOuterAvg n s β U h t d (fun _ => c) l =
      (fun _ => c) from funext ih]
    exact guerraStepAvg_const n s β U h ht (d + l) c x

theorem guerraOuterAvg_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (d l : ℕ) {F : (Fin n → ℝ) → ℝ} (hF : ∀ x, 0 ≤ F x) (x : Fin n → ℝ) :
    0 ≤ guerraOuterAvg n s β U h t d F l x := by
  induction l generalizing x with
  | zero => exact hF x
  | succ l ih => exact guerraStepAvg_nonneg n s β U h ht (d + l) ih x

theorem guerraOuterAvg_abs_le {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d l : ℕ) {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) {C : ℝ}
    (hb : ∀ x, |F x| ≤ C) (x : Fin n → ℝ) :
    |guerraOuterAvg n s β U h t d F l x| ≤ C := by
  induction l generalizing x with
  | zero => exact hb x
  | succ l ih =>
    exact guerraStepAvg_abs_le n s β U h ht (d + l)
      (measurable_guerraOuterAvg n s β U h t d hF l) ih x

theorem guerraStepAvg_finset_sum {ι : Type*} {k : ℕ} (n : ℕ) (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (j : ℕ) (I : Finset ι) (f : ι → (Fin n → ℝ) → ℝ) (hf : ∀ i ∈ I, GuerraGrowth (f i))
    (x : Fin n → ℝ) :
    guerraStepAvg n s β U h t j (fun y => ∑ i ∈ I, f i y) x =
      ∑ i ∈ I, guerraStepAvg n s β U h t j (f i) x := by
  unfold guerraStepAvg
  simp_rw [Finset.sum_mul]
  apply integral_finsetSum
  intro i hi
  obtain ⟨a, b, hb, hfb⟩ := (hf i hi).bound
  exact integrable_guerraStepAvg_integrand n s β U h ht j (hf i hi).measurable hb hfb x

/-- Each summand is an actual propagated replica observable, not a newly assumed measure. -/
theorem guerraReplicaAccum_eq_sum_outer {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} {C : ℝ} (hK : ∀ d σ τ, |K d σ τ| ≤ C)
    (j : ℕ) (x : Fin n → ℝ) :
    guerraReplicaAccum n s β U h t K j x = ∑ d ∈ Finset.range j,
      (guerraMass s d - guerraMass s (d + 1)) *
        guerraOuterAvg n s β U h t d (guerraReplicaAvg n s β U h t d (K d)) (j - d) x := by
  have hm : ∀ d, Measurable (guerraReplicaAvg n s β U h t d (K d)) := fun d =>
    (measurable_guerraReplicaAvg_joint s β h t d (K d)).comp
      (f := fun y : Fin n → ℝ => (U, y)) (measurable_const.prodMk measurable_id)
  have hg : ∀ d l, GuerraGrowth (guerraOuterAvg n s β U h t d
      (guerraReplicaAvg n s β U h t d (K d)) l) := fun d l =>
    GuerraGrowth.of_bound (measurable_guerraOuterAvg n s β U h t d (hm d) l)
      (guerraOuterAvg_abs_le n s β U h ht d l (hm d)
        (guerraReplicaAvg_abs_le n s β U h ht d (hK d)))
  induction j generalizing x with
  | zero => simp [guerraReplicaAccum]
  | succ j ih =>
    rw [guerraReplicaAccum, guerraStepAvg_add_growth n s β U h ht j
      (guerraReplicaAccum_growth n s β U h ht hK j)
      ((guerraReplicaAvg_growth n s β U h ht (hK j) j).const_mul _),
      guerraStepAvg_const_mul]
    rw [show guerraReplicaAccum n s β U h t K j =
      (fun y => ∑ d ∈ Finset.range j, (guerraMass s d - guerraMass s (d + 1)) *
        guerraOuterAvg n s β U h t d (guerraReplicaAvg n s β U h t d (K d)) (j - d) y)
      from funext ih]
    rw [guerraStepAvg_finset_sum n s β U h ht j _ _
      (fun d _ => (hg d (j - d)).const_mul _), Finset.sum_range_succ]
    simp only [guerraStepAvg_const_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro d hd
      have hdj : d ≤ j := (Finset.mem_range.mp hd).le
      rw [show j + 1 - d = (j - d) + 1 by omega, guerraOuterAvg, Nat.add_sub_of_le hdj]
    · simp [guerraOuterAvg]

variable {Ω : Type*} [MeasureSpace Ω]

theorem guerraReplicaMeasure_nonneg {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) {K : Config n → Config n → ℝ} (hK : ∀ σ τ, 0 ≤ K σ τ) :
    0 ≤ guerraReplicaMeasure n s β h U t d K := by
  apply integral_nonneg
  intro ω
  exact guerraOuterAvg_nonneg n s β (U ω) h ⟨ht.1.le, ht.2.le⟩ d (k + 2 - d)
    (guerraReplicaAvg_nonneg n s β (U ω) h ht d hK) 0

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

theorem guerraReplicaMeasure_const {k : ℕ} (n : ℕ) (s : RSBScheme k) (β h : ℝ)
    (U : Ω → EnergySpace n) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (d : ℕ) (c : ℝ) :
    guerraReplicaMeasure n s β h U t d (fun _ _ => c) = c := by
  unfold guerraReplicaMeasure
  simp_rw [show ∀ ω, guerraReplicaAvg n s β (U ω) h t d (fun _ _ => c) =
    (fun _ => c) from fun ω => funext (guerraReplicaAvg_const n s β (U ω) h ht d c)]
  simp_rw [guerraOuterAvg_const n s β _ h ⟨ht.1.le, ht.2.le⟩]
  simp

theorem integrable_guerraOuterReplica {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {U : Ω → EnergySpace n} (hU : Measurable U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d l : ℕ) {K : Config n → Config n → ℝ} {C : ℝ} (hK : ∀ σ τ, |K σ τ| ≤ C)
    (x : Fin n → ℝ) :
    Integrable (fun ω => guerraOuterAvg n s β (U ω) h t d
      (guerraReplicaAvg n s β (U ω) h t d K) l x) ℙ := by
  refine Integrable.mono (integrable_const C)
    (((measurable_guerraOuterAvg_joint s β h t d
      (F := fun U => guerraReplicaAvg n s β U h t d K)
      (measurable_guerraReplicaAvg_joint s β h t d K) l).comp
      (hU.prodMk measurable_const)).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (guerraOuterAvg_abs_le n s β (U ω) h ht d l
    ((measurable_guerraReplicaAvg_joint s β h t d K).comp
      (measurable_const.prodMk measurable_id))
    (guerraReplicaAvg_abs_le n s β (U ω) h ht d hK) x).trans (le_abs_self C)

/-- Bounded observables stay bounded under the genuine replica probability. -/
theorem guerraReplicaMeasure_abs_le {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {U : Ω → EnergySpace n} (hU : Measurable U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) {K : Config n → Config n → ℝ} {C : ℝ} (hK : ∀ σ τ, |K σ τ| ≤ C) :
    |guerraReplicaMeasure n s β h U t d K| ≤ C := by
  unfold guerraReplicaMeasure
  refine abs_integral_le_integral_abs.trans ?_
  calc
    _ ≤ ∫ _ω : Ω, C ∂ℙ := integral_mono
      (integrable_guerraOuterReplica s β h hU ht d (k + 2 - d) hK 0).abs
      (integrable_const C) (fun ω => guerraOuterAvg_abs_le n s β (U ω) h ht d (k + 2 - d)
        ((measurable_guerraReplicaAvg_joint s β h t d K).comp
          (measurable_const.prodMk measurable_id))
        (guerraReplicaAvg_abs_le n s β (U ω) h ht d hK) 0)
    _ = C := by simp

/-- The actual remainder's replica expectation is the convex combination of the `μ_r`. -/
theorem guerraReplicaExpectation_eq_sum_measures {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {U : Ω → EnergySpace n} (hU : Measurable U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K : ℕ → Config n → Config n → ℝ} {C : ℝ} (hK : ∀ d σ τ, |K d σ τ| ≤ C) :
    guerraReplicaExpectation n s β h U t K = ∑ d ∈ Finset.range (k + 2),
      (guerraMass s d - guerraMass s (d + 1)) * guerraReplicaMeasure n s β h U t d (K d) := by
  unfold guerraReplicaExpectation guerraReplicaMeasure
  simp_rw [guerraReplicaAccum_eq_sum_outer n s β _ h ht hK]
  rw [integral_finsetSum _ (fun d _ =>
    (integrable_guerraOuterReplica s β h hU ht d (k + 2 - d) (hK d) 0).const_mul _)]
  simp_rw [integral_const_mul]

theorem guerraMass_sum_drops {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    (∑ d ∈ Finset.range j, (guerraMass s d - guerraMass s (d + 1))) = 1 - guerraMass s j := by
  induction j with
  | zero => simp [guerraMass]
  | succ j ih => rw [Finset.sum_range_succ, ih]; ring

/-- Uniform bounds on the genuine per-level replica tails give the mass-weighted tail bound.
Depth zero has zero mass and does not require an assumption; `1 ≤ d ≤ k + 1`
corresponds exactly to the paper's `1 ≤ r ≤ k + 1`. -/
theorem guerraOverlapTail_le_of_replicaMeasure {n k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {U : Ω → EnergySpace n} (hU : Measurable U) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {a δ : ℝ}
    (hbound : ∀ d, 1 ≤ d → d ≤ k + 1 →
      guerraReplicaMeasure n s β h U t d
        (fun σ τ => if a ≤ (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0) ≤ δ) :
    guerraOverlapTail n s β h U t a ≤ δ := by
  classical
  let K : ℕ → Config n → Config n → ℝ := fun d σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0
  have hK : ∀ d σ τ, |K d σ τ| ≤ 1 := by intros; dsimp [K]; split_ifs <;> norm_num
  change guerraReplicaExpectation n s β h U t K ≤ δ
  rw [guerraReplicaExpectation_eq_sum_measures s β h hU ht hK]
  calc
    _ ≤ ∑ d ∈ Finset.range (k + 2), (guerraMass s d - guerraMass s (d + 1)) * δ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0, guerraMass, s.m_top]
      · exact mul_le_mul_of_nonneg_left (hbound d (by omega) (by
          have := Finset.mem_range.mp hd; omega)) (guerraMass_drop_nonneg s d)
    _ = δ := by rw [← Finset.sum_mul, guerraMass_sum_drops, guerraMass_top]; ring

end SpinGlass.Targets
