module

/- Compatibility adaptation: allow finite normalization to finish before optional residual simplification. -/
/- Adapted for the paper formalization: replaced 18 native decision tactics with kernel decide. Original source and pinned revision are recorded in PROVENANCE.json. -/
public import Lemmas.Cavity.Interpolation
public import Lemmas.SmartPath.Interpolation
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal
set_option autoImplicit false
namespace SpinGlass.AT

/-!
# Quantitative last-spin cavity estimates

This file contains the analytic part of the cavity argument: last-site
factorization, interpolation derivative identities, the uniform cubic-moment
estimate, endpoint replacement, and the final three-coordinate remainder
bound.  The deliberately local helper names are kept inside
`CavityEstimates`; only the final norm estimate is used by
`Talagrand_Cavity`.
-/

namespace CavityEstimates

lemma prod_mul_prod_eq_prod_symmDiff_test {α : Type*} [DecidableEq α]
    (x : α → ℝ) (hx : ∀ a, x a ^ 2 = 1) (S T : Finset α) :
    (∏ a ∈ S, x a) * (∏ a ∈ T, x a) = ∏ a ∈ symmDiff S T, x a := by
  induction S using Finset.induction_on generalizing T with
  | empty => simp [symmDiff_def]
  | @insert a S ha ih =>
      by_cases hat : a ∈ T
      · let T' := T.erase a
        have hT : T = insert a T' := (Finset.insert_erase hat).symm
        have haT' : a ∉ T' := by simp [T']
        rw [hT, Finset.prod_insert ha, Finset.prod_insert haT']
        rw [show symmDiff (insert a S) (insert a T') = symmDiff S T' by
          ext b
          by_cases hba : b = a
          · subst b; simp [Finset.mem_symmDiff, ha, haT']
          · simp [Finset.mem_symmDiff, hba]]
        rw [← ih T']
        have hxa : x a * x a = 1 := by simpa [pow_two] using hx a
        rw [show (x a * ∏ x_1 ∈ S, x x_1) *
            (x a * ∏ x_1 ∈ T', x x_1) =
            (x a * x a) * ((∏ x_1 ∈ S, x x_1) * ∏ x_1 ∈ T', x x_1) by ring,
          hxa, one_mul]
      · rw [Finset.prod_insert ha]
        rw [show symmDiff (insert a S) T = insert a (symmDiff S T) by
          ext b
          by_cases hba : b = a
          · subst b; simp [Finset.mem_symmDiff, ha, hat]
          · simp [Finset.mem_symmDiff, hba]]
        rw [Finset.prod_insert]
        · rw [← ih T]
          ring
        · simp [Finset.mem_symmDiff, ha, hat]

lemma normalizedScore_four_explicit_test {N : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N 6) :
    normalizedCavityScoreObservable (n := 4) q i σs =
      cavityInteractionAt q i (σs 0) (σs 1) +
      cavityInteractionAt q i (σs 0) (σs 2) +
      cavityInteractionAt q i (σs 0) (σs 3) +
      cavityInteractionAt q i (σs 1) (σs 2) +
      cavityInteractionAt q i (σs 1) (σs 3) +
      cavityInteractionAt q i (σs 2) (σs 3) -
      4 * (cavityInteractionAt q i (σs 0) (σs 4) +
        cavityInteractionAt q i (σs 1) (σs 4) +
        cavityInteractionAt q i (σs 2) (σs 4) +
        cavityInteractionAt q i (σs 3) (σs 4)) +
      10 * cavityInteractionAt q i (σs 4) (σs 5) := by
  unfold normalizedCavityScoreObservable initialReplicas firstFreshReplica secondFreshReplica
  let T : Fin 4 × Fin 4 → ℝ := fun p =>
    cavityInteractionAt q i (σs (Fin.castAdd 2 p.1)) (σs (Fin.castAdd 2 p.2))
  let E : Finset (Fin 4 × Fin 4) := Finset.univ.filter (fun p => p.1 < p.2)
  have hsum := Finset.sum_subtype
    (p := fun p : Fin 4 × Fin 4 => p.1 < p.2)
    (F := inferInstanceAs (Fintype (ReplicaEdge 4))) E (by simp [E]) T
  rw [← hsum]
  norm_num [E, T, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  try simp (disch := decide)
  ring

def ee01 : ReplicaEdge 6 := ⟨(0,1), by decide⟩
def ee02 : ReplicaEdge 6 := ⟨(0,2), by decide⟩
def ee03 : ReplicaEdge 6 := ⟨(0,3), by decide⟩
def ee12 : ReplicaEdge 6 := ⟨(1,2), by decide⟩
def ee13 : ReplicaEdge 6 := ⟨(1,3), by decide⟩
def ee23 : ReplicaEdge 6 := ⟨(2,3), by decide⟩
def ee04 : ReplicaEdge 6 := ⟨(0,4), by decide⟩
def ee14 : ReplicaEdge 6 := ⟨(1,4), by decide⟩
def ee24 : ReplicaEdge 6 := ⟨(2,4), by decide⟩
def ee34 : ReplicaEdge 6 := ⟨(3,4), by decide⟩
def ee45 : ReplicaEdge 6 := ⟨(4,5), by decide⟩

def edgeFinset6 (e : ReplicaEdge 6) : Finset (Fin 6) := {e.1.1, e.1.2}

lemma edgeSymmDiff_card_test (e f : ReplicaEdge 6) :
    (symmDiff (edgeFinset6 e) (edgeFinset6 f)).card =
      match edgeRelation e f with
      | .equal => 0 | .sharesOne => 2 | .disjoint => 4 := by
  decide +revert

noncomputable def edgeSpin6 {N : ℕ} (i : Fin N) (e : ReplicaEdge 6)
    (σs : Replicas N 6) : ℝ :=
  SpinGlass.spin N (σs e.1.1) i * SpinGlass.spin N (σs e.1.2) i

lemma edgeSpin6_eq_prod {N : ℕ} (i : Fin N) (e : ReplicaEdge 6)
    (σs : Replicas N 6) :
    edgeSpin6 i e σs = ∏ a ∈ edgeFinset6 e, SpinGlass.spin N (σs a) i := by
  rw [edgeSpin6, edgeFinset6]
  simp [ne_of_lt e.2]

lemma edgeSpin6_mul {N : ℕ} (i : Fin N) (e f : ReplicaEdge 6)
    (σs : Replicas N 6) :
    edgeSpin6 i e σs * edgeSpin6 i f σs =
      ∏ a ∈ symmDiff (edgeFinset6 e) (edgeFinset6 f),
        SpinGlass.spin N (σs a) i := by
  rw [edgeSpin6_eq_prod, edgeSpin6_eq_prod]
  apply prod_mul_prod_eq_prod_symmDiff_test
  intro a
  cases h : σs a i <;> simp [SpinGlass.spin, h]

lemma lastSiteQuenchedAverage_sub_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F G : ReplicaFun N n) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs => F σs - G σs) =
      lastSiteQuenchedAverage (s := s) path i u F -
        lastSiteQuenchedAverage (s := s) path i u G := by
  unfold lastSiteQuenchedAverage quenchedReplicaAverage
  have hmeas := measurable_lastSiteHamiltonian (s := s) path i u
  have hF := integrable_replicaGibbsAverage_comp
    (lastSiteHamiltonian (s := s) path i u) hmeas F
  have hG := integrable_replicaGibbsAverage_comp
    (lastSiteHamiltonian (s := s) path i u) hmeas G
  rw [show (fun ω => replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω)
      (fun σs => F σs - G σs)) =
      fun ω => replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω) F -
        replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω) G by
    funext ω
    unfold replicaGibbsAverage
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σs _
    ring]
  exact integral_sub hF hG

lemma lastSiteQuenchedAverage_const_mul_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u c : ℝ) (F : ReplicaFun N n) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs => c * F σs) =
      c * lastSiteQuenchedAverage (s := s) path i u F := by
  exact quenchedReplicaAverage_const_mul (lastSiteHamiltonian (s := s) path i u) c F

noncomputable def lastSiteAverageLinearMap_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) : ReplicaFun N n →ₗ[ℝ] ℝ where
  toFun F := lastSiteQuenchedAverage (s := s) path i u F
  map_add' F G := by
    unfold lastSiteQuenchedAverage quenchedReplicaAverage
    have hmeas := measurable_lastSiteHamiltonian (s := s) path i u
    have hF := integrable_replicaGibbsAverage_comp
      (lastSiteHamiltonian (s := s) path i u) hmeas F
    have hG := integrable_replicaGibbsAverage_comp
      (lastSiteHamiltonian (s := s) path i u) hmeas G
    rw [show (fun ω => replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω)
        (F + G)) = fun ω =>
        replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω) F +
          replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω) G by
      funext ω
      unfold replicaGibbsAverage
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σs _
      simp only [Pi.add_apply]
      ring]
    exact integral_add hF hG
  map_smul' c F := by
    rw [show c • F = fun σs => c * F σs by rfl]
    simpa [smul_eq_mul] using
      lastSiteQuenchedAverage_const_mul_test (s := s) path i u c F

@[simp] lemma lastSiteAverageLinearMap_apply_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) :
    lastSiteAverageLinearMap_test (s := s) path i u F =
      lastSiteQuenchedAverage (s := s) path i u F := rfl

lemma endpoint_scalar_two_test {β h q : ℝ} (hh : 0 < h) (hq : q = rsQ β h) :
    standardGaussianExpectation (fun z =>
      (-Real.tanh (h + β * Real.sqrt q * z)) ^ 2) = q := by
  rw [hq]
  rw [show (fun z => (-Real.tanh (h + β * Real.sqrt (rsQ β h) * z)) ^ 2) =
      fun z => Real.tanh (h + β * Real.sqrt (rsQ β h) * z) ^ 2 by
    funext z; ring]
  exact (rsQ_eq_gaussian_tanh_sq hh).symm

lemma endpoint_scalar_four_test (β h q : ℝ) (hq : q = rsQ β h) :
    standardGaussianExpectation (fun z =>
      (-Real.tanh (h + β * Real.sqrt q * z)) ^ 4) = rsR β h := by
  rw [hq]
  rw [rsR_eq_gaussian_tanh_fourth]
  congr 1
  funext z
  ring

lemma lastSite_zero_bulk_spin_two_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (F : (Fin 6 → SiteBaseConfig N i) → ℝ) (S : Finset (Fin 6))
    (hS : S.card = 2) :
    lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => F (replicasSplitSiteEquiv i σs).1 *
          ∏ a ∈ S, SpinGlass.spin N (σs a) i) =
      q * lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => F (replicasSplitSiteEquiv i σs).1) := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rsQ_mem_Icc β h).1
  have hfac := lastSiteQuenchedAverage_zero_factor (s := s) path hN hq0 i F S
  have hfac0 := lastSiteQuenchedAverage_zero_factor (s := s) path hN hq0 i F ∅
  rw [hS, endpoint_scalar_two_test hh hq] at hfac
  simp [standardGaussianExpectation] at hfac0
  rw [hfac, hfac0]
  ring

lemma lastSite_zero_bulk_spin_four_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hq : q = rsQ β h) (i : Fin N)
    (F : (Fin 6 → SiteBaseConfig N i) → ℝ) (S : Finset (Fin 6))
    (hS : S.card = 4) :
    lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => F (replicasSplitSiteEquiv i σs).1 *
          ∏ a ∈ S, SpinGlass.spin N (σs a) i) =
      rsR β h * lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => F (replicasSplitSiteEquiv i σs).1) := by
  have hq0 : 0 ≤ q := by rw [hq]; exact (rsQ_mem_Icc β h).1
  have hfac := lastSiteQuenchedAverage_zero_factor (s := s) path hN hq0 i F S
  have hfac0 := lastSiteQuenchedAverage_zero_factor (s := s) path hN hq0 i F ∅
  rw [hS, endpoint_scalar_four_test β h q hq] at hfac
  simp [standardGaussianExpectation] at hfac0
  rw [hfac, hfac0]
  ring

lemma edgeFinset6_card (e : ReplicaEdge 6) : (edgeFinset6 e).card = 2 := by
  simp [edgeFinset6, ne_of_lt e.2]

lemma lastSite_zero_centered_edge_factor_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (F : (Fin 6 → SiteBaseConfig N i) → ℝ) (e f : ReplicaEdge 6) :
    lastSiteQuenchedAverage (s := s) path i 0 (fun σs =>
        F (replicasSplitSiteEquiv i σs).1 *
          ((edgeSpin6 i e σs - q) * edgeSpin6 i f σs)) =
      decoupledSpinCoefficient q (rsR β h) (edgeRelation e f) *
        lastSiteQuenchedAverage (s := s) path i 0
          (fun σs => F (replicasSplitSiteEquiv i σs).1) := by
  let S := symmDiff (edgeFinset6 e) (edgeFinset6 f)
  let base : ReplicaFun N 6 := fun σs => F (replicasSplitSiteEquiv i σs).1
  have hobs : (fun σs : Replicas N 6 =>
      F (replicasSplitSiteEquiv i σs).1 *
        ((edgeSpin6 i e σs - q) * edgeSpin6 i f σs)) =
      fun σs =>
        (base σs * ∏ a ∈ S, SpinGlass.spin N (σs a) i) -
          q * (base σs * ∏ a ∈ edgeFinset6 f, SpinGlass.spin N (σs a) i) := by
    funext σs
    rw [← edgeSpin6_eq_prod i f σs, ← edgeSpin6_mul i e f σs]
    dsimp [base, S]
    ring
  rw [hobs, lastSiteQuenchedAverage_sub_test,
    lastSiteQuenchedAverage_const_mul_test]
  have hsecond := lastSite_zero_bulk_spin_two_test (s := s) path hN hh hq i F
    (edgeFinset6 f) (edgeFinset6_card f)
  change lastSiteQuenchedAverage (s := s) path i 0
      (fun σs => base σs * ∏ a ∈ S, SpinGlass.spin N (σs a) i) -
      q * lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => base σs * ∏ a ∈ edgeFinset6 f, SpinGlass.spin N (σs a) i) = _
  change _ = _ at hsecond
  rw [hsecond]
  have hcard : S.card = match edgeRelation e f with
      | .equal => 0 | .sharesOne => 2 | .disjoint => 4 := by
    exact edgeSymmDiff_card_test e f
  cases hr : edgeRelation e f with
  | equal =>
      rw [hr] at hcard
      have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      rw [hS]
      simp [base, decoupledSpinCoefficient, hr]
      ring
  | sharesOne =>
      rw [hr] at hcard
      have hfirst := lastSite_zero_bulk_spin_two_test (s := s) path hN hh hq i F S hcard
      change _ = _ at hfirst
      rw [hfirst]
      simp [decoupledSpinCoefficient, hr]
      ring
  | disjoint =>
      rw [hr] at hcard
      have hfirst := lastSite_zero_bulk_spin_four_test (s := s) path hN hq i F S hcard
      change _ = _ at hfirst
      rw [hfirst]
      simp [decoupledSpinCoefficient, hr]
      ring

lemma configCavityOverlapAt_update_false_test {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    configCavityOverlapAt i (Function.update σ i false) (Function.update τ i false) =
      configCavityOverlapAt i σ τ := by
  have hu (ξ : SpinGlass.Config N) :
      Function.update ξ i false = if ξ i then flipSite i ξ else ξ := by
    funext j
    by_cases hji : j = i
    · subst j
      cases h : ξ i <;> simp [h, flipSite]
    · by_cases hξ : ξ i <;> simp [hξ, hji, flipSite]
  rw [hu σ, hu τ]
  split <;> split
  · rw [configCavityOverlapAt_flip_left, configCavityOverlapAt_flip_right]
  · rw [configCavityOverlapAt_flip_left]
  · rw [configCavityOverlapAt_flip_right]
  · rfl

noncomputable def bulkCavityOverlap6 {N : ℕ} (q : ℝ) (i : Fin N)
    (ρs : Fin 6 → SiteBaseConfig N i) (a b : Fin 6) : ℝ :=
  cavityOverlapAt q i (fun c => (ρs c).1) a b

lemma bulkCavityOverlap6_split_test {N : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N 6) (a b : Fin 6) :
    bulkCavityOverlap6 q i (replicasSplitSiteEquiv i σs).1 a b =
      cavityOverlapAt q i σs a b := by
  rw [bulkCavityOverlap6, cavityOverlapAt_eq_configCavityOverlapAt_sub,
    cavityOverlapAt_eq_configCavityOverlapAt_sub]
  exact congrArg (fun x => x - q)
    (configCavityOverlapAt_update_false_test i (σs a) (σs b))

noncomputable def bulkEdgeCavity6 {N : ℕ} (q : ℝ) (i : Fin N)
    (e : ReplicaEdge 6) (ρs : Fin 6 → SiteBaseConfig N i) : ℝ :=
  bulkCavityOverlap6 q i ρs e.1.1 e.1.2

lemma bulkEdgeCavity6_split_test {N : ℕ} (q : ℝ) (i : Fin N)
    (e : ReplicaEdge 6) (σs : Replicas N 6) :
    bulkEdgeCavity6 q i e (replicasSplitSiteEquiv i σs).1 =
      cavityOverlapAt q i σs e.1.1 e.1.2 :=
  bulkCavityOverlap6_split_test q i σs _ _

abbrev SamePair6 (a b c d : Fin 6) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def canonicalEdge6 : EdgeRelation → ReplicaEdge 6
  | .equal => ee01 | .sharesOne => ee02 | .disjoint => ee23

def momentCoeff (A B C : ℝ) : EdgeRelation → ℝ
  | .equal => A | .sharesOne => B | .disjoint => C

def abstractTerm (q r A B C : ℝ) (target deriv : ReplicaEdge 6) : ℝ :=
  decoupledSpinCoefficient q r (edgeRelation target deriv) *
    momentCoeff A B C (edgeRelation ee01 deriv)

def abstractRow (q r A B C : ℝ) (target : ReplicaEdge 6) : ℝ :=
  abstractTerm q r A B C target ee01 + abstractTerm q r A B C target ee02 +
  abstractTerm q r A B C target ee03 + abstractTerm q r A B C target ee12 +
  abstractTerm q r A B C target ee13 + abstractTerm q r A B C target ee23 -
  4 * (abstractTerm q r A B C target ee04 + abstractTerm q r A B C target ee14 +
    abstractTerm q r A B C target ee24 + abstractTerm q r A B C target ee34) +
  10 * abstractTerm q r A B C target ee45

lemma exists_edgeMoment_perm6_test (e : ReplicaEdge 6) :
    ∃ p : Equiv.Perm (Fin 6),
      SamePair6 (p 0) (p 1) 0 1 ∧
        SamePair6 (p (canonicalEdge6 (edgeRelation ee01 e)).1.1)
          (p (canonicalEdge6 (edgeRelation ee01 e)).1.2) e.1.1 e.1.2 := by
  fin_cases e
  all_goals first
    | exact ⟨Equiv.refl _, by decide⟩
    | exact ⟨Equiv.swap 2 3, by decide⟩
    | exact ⟨Equiv.swap 2 4, by decide⟩
    | exact ⟨Equiv.swap 2 5, by decide⟩
    | exact ⟨Equiv.swap 0 1, by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 2 3), by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 2 4), by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 2 5), by decide⟩
    | exact ⟨Equiv.swap 3 4, by decide⟩
    | exact ⟨Equiv.swap 3 5, by decide⟩
    | exact ⟨(Equiv.swap 3 4).trans (Equiv.swap 2 3), by decide⟩
    | exact ⟨(Equiv.swap 3 5).trans (Equiv.swap 2 3), by decide⟩
    | exact ⟨(Equiv.swap 2 4).trans (Equiv.swap 3 5), by decide⟩

lemma cavityOverlapAt_comm_test {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) :
    cavityOverlapAt q i σs a b = cavityOverlapAt q i σs b a := by
  rw [cavityOverlapAt_eq_configCavityOverlapAt_sub,
    cavityOverlapAt_eq_configCavityOverlapAt_sub]
  congr 1
  unfold configCavityOverlapAt SpinGlass.overlap
  have hsum : (∑ j, SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j) =
      ∑ j, SpinGlass.spin N (σs b) j * SpinGlass.spin N (σs a) j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

lemma cavityOverlapAt_samePair6_test {N : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N 6) {a b c d : Fin 6} (hp : SamePair6 a b c d) :
    cavityOverlapAt q i σs a b = cavityOverlapAt q i σs c d := by
  rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rfl
  · exact cavityOverlapAt_comm_test q i σs _ _

lemma cavityOverlapAt_relabel6_test {N : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N 6) (p : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    cavityOverlapAt q i (replicaRelabelEquiv p σs) a b =
      cavityOverlapAt q i σs (p a) (p b) := by
  rfl

noncomputable def cavityMoment6
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f : ReplicaEdge 6) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u (fun σs =>
    cavityOverlapAt q i σs e.1.1 e.1.2 *
      cavityOverlapAt q i σs f.1.1 f.1.2)

lemma cavityMoment6_by_relation_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e : ReplicaEdge 6) :
    cavityMoment6 (s := s) path i u ee01 e =
      momentCoeff
        (cavityMoment6 (s := s) path i u ee01 ee01)
        (cavityMoment6 (s := s) path i u ee01 ee02)
        (cavityMoment6 (s := s) path i u ee01 ee23)
        (edgeRelation ee01 e) := by
  obtain ⟨p, hpbase, hpedge⟩ := exists_edgeMoment_perm6_test e
  let ce := canonicalEdge6 (edgeRelation ee01 e)
  let F : ReplicaFun N 6 := fun σs =>
    cavityOverlapAt q i σs 0 1 *
      cavityOverlapAt q i σs ce.1.1 ce.1.2
  have hrel := quenchedReplicaAverage_relabel
    (lastSiteHamiltonian (s := s) path i u) F p
  have hpoint : (fun σs => F (replicaRelabelEquiv p σs)) = fun σs =>
      cavityOverlapAt q i σs 0 1 * cavityOverlapAt q i σs e.1.1 e.1.2 := by
    funext σs
    dsimp [F, replicaRelabelEquiv, ce]
    change cavityOverlapAt q i σs (p 0) (p 1) *
      cavityOverlapAt q i σs
        (p (canonicalEdge6 (edgeRelation ee01 e)).1.1)
        (p (canonicalEdge6 (edgeRelation ee01 e)).1.2) = _
    rw [cavityOverlapAt_samePair6_test q i σs hpbase,
      cavityOverlapAt_samePair6_test q i σs hpedge]
  rw [hpoint] at hrel
  cases hr : edgeRelation ee01 e <;>
    simp [momentCoeff, cavityMoment6, F, ce, canonicalEdge6, hr] at hrel ⊢ <;>
    exact hrel

lemma cavityInteractionAt_edge6_test {N : ℕ} (q : ℝ) (i : Fin N)
    (e : ReplicaEdge 6) (σs : Replicas N 6) :
    cavityInteractionAt q i (σs e.1.1) (σs e.1.2) =
      edgeSpin6 i e σs * cavityOverlapAt q i σs e.1.1 e.1.2 := by
  rw [cavityInteractionAt, cavityOverlapAt_eq_configCavityOverlapAt_sub]
  rfl

lemma endpoint_score_term_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (target deriv : ReplicaEdge 6) :
    lastSiteQuenchedAverage (s := s) path i 0 (fun σs =>
      cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
        cavityInteractionAt q i (σs deriv.1.1) (σs deriv.1.2)) =
      abstractTerm q (rsR β h)
        (cavityMoment6 (s := s) path i 0 ee01 ee01)
        (cavityMoment6 (s := s) path i 0 ee01 ee02)
        (cavityMoment6 (s := s) path i 0 ee01 ee23) target deriv := by
  let F : (Fin 6 → SiteBaseConfig N i) → ℝ := fun ρs =>
    bulkEdgeCavity6 q i ee01 ρs * bulkEdgeCavity6 q i deriv ρs
  have hobs : (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
        cavityInteractionAt q i (σs deriv.1.1) (σs deriv.1.2)) =
      fun σs => F (replicasSplitSiteEquiv i σs).1 *
        ((edgeSpin6 i target σs - q) * edgeSpin6 i deriv σs) := by
    funext σs
    rw [cavityInteractionAt_edge6_test]
    simp only [F, bulkEdgeCavity6_split_test]
    simp [ee01]
    ring
  rw [hobs, lastSite_zero_centered_edge_factor_test path hN hh hq i F target deriv]
  rw [show lastSiteQuenchedAverage (s := s) path i 0
      (fun σs => F (replicasSplitSiteEquiv i σs).1) =
      cavityMoment6 (s := s) path i 0 ee01 deriv by
    unfold cavityMoment6
    congr 1
    funext σs
    simp only [F, bulkEdgeCavity6_split_test]]
  rw [cavityMoment6_by_relation_test]
  rfl

noncomputable def scoreTermObs6 {N : ℕ} (q : ℝ) (i : Fin N)
    (target deriv : ReplicaEdge 6) : ReplicaFun N 6 := fun σs =>
  cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
    cavityInteractionAt q i (σs deriv.1.1) (σs deriv.1.2)

lemma endpoint_fullScore_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (target : ReplicaEdge 6) :
    lastSiteQuenchedAverage (s := s) path i 0 (fun σs =>
      cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
        normalizedCavityScoreObservable (n := 4) q i σs) =
      abstractRow q (rsR β h)
        (cavityMoment6 (s := s) path i 0 ee01 ee01)
        (cavityMoment6 (s := s) path i 0 ee01 ee02)
        (cavityMoment6 (s := s) path i 0 ee01 ee23) target := by
  let L := lastSiteAverageLinearMap_test (n := 6) (s := s) path i 0
  have hobs : (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
        normalizedCavityScoreObservable (n := 4) q i σs) =
      scoreTermObs6 q i target ee01 + scoreTermObs6 q i target ee02 +
      scoreTermObs6 q i target ee03 + scoreTermObs6 q i target ee12 +
      scoreTermObs6 q i target ee13 + scoreTermObs6 q i target ee23 -
      (4 : ℝ) • (scoreTermObs6 q i target ee04 + scoreTermObs6 q i target ee14 +
        scoreTermObs6 q i target ee24 + scoreTermObs6 q i target ee34) +
      (10 : ℝ) • scoreTermObs6 q i target ee45 := by
    funext σs
    rw [normalizedScore_four_explicit_test]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      scoreTermObs6]
    simp [ee01, ee02, ee03, ee12, ee13, ee23, ee04, ee14, ee24, ee34, ee45,
      edgeSpin6]
    ring
  change L _ = _
  rw [hobs]
  simp only [map_add, map_sub, map_smul]
  simp only [L, lastSiteAverageLinearMap_apply_test, smul_eq_mul]
  have ht (deriv : ReplicaEdge 6) :
      lastSiteQuenchedAverage (s := s) path i 0 (scoreTermObs6 q i target deriv) =
        abstractTerm q (rsR β h)
          (cavityMoment6 (s := s) path i 0 ee01 ee01)
          (cavityMoment6 (s := s) path i 0 ee01 ee02)
          (cavityMoment6 (s := s) path i 0 ee01 ee23) target deriv := by
    change lastSiteQuenchedAverage (s := s) path i 0 (fun σs =>
      cavityOverlapAt q i σs 0 1 * (edgeSpin6 i target σs - q) *
        cavityInteractionAt q i (σs deriv.1.1) (σs deriv.1.2)) = _
    exact endpoint_score_term_test path hN hh hq i target deriv
  rw [ht ee01, ht ee02, ht ee03, ht ee12, ht ee13, ht ee23,
    ht ee04, ht ee14, ht ee24, ht ee34, ht ee45]
  rfl

lemma abs_lastSiteAverage_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F G : ReplicaFun N n)
    (hFG : ∀ σs, |F σs| ≤ G σs) :
    |lastSiteQuenchedAverage (s := s) path i u F| ≤
      lastSiteQuenchedAverage (s := s) path i u G := by
  have hmeas := measurable_lastSiteHamiltonian (s := s) path i u
  exact (abs_quenchedReplicaAverage_le_abs_average
    (lastSiteHamiltonian (s := s) path i u) hmeas F).trans
      (quenchedReplicaAverage_mono (lastSiteHamiltonian (s := s) path i u)
        hmeas (fun σs => |F σs|) G hFG)

lemma lastSiteAverage_initialReplicas_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) :
    lastSiteQuenchedAverage (s := s) path i u
      (fun σs : Replicas N (n + 2) => F (initialReplicas σs)) =
    lastSiteQuenchedAverage (s := s) path i u F :=
  quenchedReplicaAverage_initialReplicas _ F

noncomputable def cavityCube4
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u
    (fun σs : Replicas N 4 => |cavityOverlapAt q i σs 0 1| ^ 3)

lemma cavityCube4_nonneg
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) : 0 ≤ cavityCube4 (s := s) path i u := by
  unfold cavityCube4 lastSiteQuenchedAverage quenchedReplicaAverage
  apply integral_nonneg
  intro ω
  apply replicaGibbsAverage_nonneg
  intro σs
  positivity

lemma cavityCube4_deriv_bound
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (i : Fin N) :
    ∃ d, HasDerivAt (fun v => cavityCube4 (s := s) path i v) d u ∧
      |d| ≤ 64 * β ^ 2 * cavityCube4 (s := s) path i u := by
  let F : ReplicaFun N 4 := fun σs => |cavityOverlapAt q i σs 0 1| ^ 3
  let d : ℝ := s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u
    (fun σs : Replicas N 6 =>
      F (initialReplicas σs) * normalizedCavityScoreObservable q i σs)
  refine ⟨d, ?_, ?_⟩
  · exact hasDerivAt_lastSiteQuenchedAverage_fixedScore path i hs hu F
  · have havg :
        |lastSiteQuenchedAverage (s := s) path i u
          (fun σs : Replicas N 6 =>
            F (initialReplicas σs) * normalizedCavityScoreObservable q i σs)| ≤
          64 * cavityCube4 (s := s) path i u := by
      calc
        _ ≤ lastSiteQuenchedAverage (s := s) path i u
            (fun σs : Replicas N 6 => 64 * F (initialReplicas σs)) := by
          apply abs_lastSiteAverage_le_test
          intro σs
          rw [abs_mul]
          have hsco := abs_normalizedCavityScoreObservable_four_le hN hqI i σs
          have hF0 : 0 ≤ F (initialReplicas σs) := by dsimp [F]; positivity
          rw [abs_of_nonneg hF0]
          nlinarith
        _ = 64 * cavityCube4 (s := s) path i u := by
          rw [show (fun σs : Replicas N 6 => 64 * F (initialReplicas σs)) =
              fun σs => (64 : ℝ) * F (initialReplicas σs) by rfl,
            lastSiteQuenchedAverage_const_mul_test,
            lastSiteAverage_initialReplicas_test]
          simp only [cavityCube4, F]
    dsimp [d]
    rw [abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg (sq_nonneg β)]
    calc
      s * β ^ 2 *
          |lastSiteQuenchedAverage (s := s) path i u
            (fun σs : Replicas N 6 =>
              F (initialReplicas σs) * normalizedCavityScoreObservable q i σs)| ≤
          1 * β ^ 2 * (64 * cavityCube4 (s := s) path i u) := by
        gcongr
        exact hs.2
      _ = 64 * β ^ 2 * cavityCube4 (s := s) path i u := by ring

lemma abs_sub_cube_le (x y : ℝ) : |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have h := abs_sub x y
  have hpow := pow_le_pow_left₀ (abs_nonneg (x - y)) h 3
  calc
    |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := hpow
    _ ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
      nlinarith [sq_nonneg (|x| - |y|), abs_nonneg x, abs_nonneg y]

noncomputable def pairPerm_test {n : ℕ} (e : ReplicaEdge (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  let p₀ := Equiv.swap (0 : Fin (n + 2)) e.1.1
  p₀.trans (Equiv.swap (p₀ 1) e.1.2)

lemma pairPerm_zero_test {n : ℕ} (e : ReplicaEdge (n + 2)) :
    pairPerm_test e 0 = e.1.1 := by
  let p₀ := Equiv.swap (0 : Fin (n + 2)) e.1.1
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
  have hcne : p₀ 1 ≠ e.1.1 := by
    rw [← Equiv.swap_apply_left (0 : Fin (n + 2)) e.1.1]
    exact fun h => h01 (p₀.injective h.symm)
  have hab : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  change (Equiv.swap (p₀ 1) e.1.2) (p₀ 0) = e.1.1
  rw [show p₀ 0 = e.1.1 by exact Equiv.swap_apply_left _ _]
  rw [Equiv.swap_apply_def]
  simp [hcne.symm, hab]

lemma pairPerm_one_test {n : ℕ} (e : ReplicaEdge (n + 2)) :
    pairPerm_test e 1 = e.1.2 := by
  change (Equiv.swap ((Equiv.swap (0 : Fin (n + 2)) e.1.1) 1) e.1.2)
      ((Equiv.swap (0 : Fin (n + 2)) e.1.1) 1) = e.1.2
  exact Equiv.swap_apply_left _ _

lemma lastSite_cube_edge_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e : ReplicaEdge (n + 2)) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N (n + 2) =>
      |cavityOverlapAt q i σs e.1.1 e.1.2| ^ 3) =
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N (n + 2) =>
      |cavityOverlapAt q i σs 0 1| ^ 3) := by
  let F : ReplicaFun N (n + 2) := fun σs => |cavityOverlapAt q i σs 0 1| ^ 3
  have hr := quenchedReplicaAverage_relabel
    (lastSiteHamiltonian (s := s) path i u) F (pairPerm_test e)
  have hp : (fun σs => F (replicaRelabelEquiv (pairPerm_test e) σs)) =
      fun σs => |cavityOverlapAt q i σs e.1.1 e.1.2| ^ 3 := by
    funext σs
    dsimp only [F]
    change |cavityOverlapAt q i σs (pairPerm_test e 0) (pairPerm_test e 1)| ^ 3 = _
    rw [pairPerm_zero_test, pairPerm_one_test]
  rw [hp] at hr
  exact hr

lemma young_three_abs_test (x y z : ℝ) :
    |x * y * z| ≤ (|x| ^ 3 + |y| ^ 3 + |z| ^ 3) / 3 := by
  rw [abs_mul, abs_mul]
  let a := |x|
  let b := |y|
  let c := |z|
  have ha : 0 ≤ a := abs_nonneg x
  have hb : 0 ≤ b := abs_nonneg y
  have hc : 0 ≤ c := abs_nonneg z
  have h1 : 3 * a ^ 2 * c ≤ 2 * a ^ 3 + c ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - c)) (by positivity : 0 ≤ 2 * a + c)]
  have h2 : 3 * b ^ 2 * c ≤ 2 * b ^ 3 + c ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (b - c)) (by positivity : 0 ≤ 2 * b + c)]
  have hab : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have habc : 6 * a * b * c ≤ 3 * (a ^ 2 + b ^ 2) * c := by nlinarith
  dsimp [a, b, c] at *
  nlinarith

lemma abs_lastSite_triple_edges_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f g : ReplicaEdge (n + 2))
    (W : ReplicaFun N (n + 2)) (hW : ∀ σs, |W σs| ≤ 1) :
    |lastSiteQuenchedAverage (s := s) path i u (fun σs => W σs *
      cavityOverlapAt q i σs e.1.1 e.1.2 *
      cavityOverlapAt q i σs f.1.1 f.1.2 *
      cavityOverlapAt q i σs g.1.1 g.1.2)| ≤
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N (n + 2) =>
      |cavityOverlapAt q i σs 0 1| ^ 3) := by
  let Q : ReplicaEdge (n + 2) → ReplicaFun N (n + 2) := fun a σs =>
    cavityOverlapAt q i σs a.1.1 a.1.2
  calc
    _ ≤ lastSiteQuenchedAverage (s := s) path i u (fun σs =>
        (|Q e σs| ^ 3 + |Q f σs| ^ 3 + |Q g σs| ^ 3) / 3) := by
      apply abs_lastSiteAverage_le_test
      intro σs
      have ht := young_three_abs_test (Q e σs) (Q f σs) (Q g σs)
      have hnon : 0 ≤ (|Q e σs| ^ 3 + |Q f σs| ^ 3 + |Q g σs| ^ 3) / 3 := by positivity
      calc
        |W σs * Q e σs * Q f σs * Q g σs| =
            |W σs| * |Q e σs * Q f σs * Q g σs| := by
          simp only [abs_mul]
          ring
        _ ≤ 1 * |Q e σs * Q f σs * Q g σs| := by
          gcongr
          exact hW σs
        _ ≤ 1 * ((|Q e σs| ^ 3 + |Q f σs| ^ 3 + |Q g σs| ^ 3) / 3) := by
          gcongr
        _ = _ := one_mul _
    _ = _ := by
      rw [show (fun σs =>
          (|Q e σs| ^ 3 + |Q f σs| ^ 3 + |Q g σs| ^ 3) / 3) =
          (3 : ℝ)⁻¹ • ((fun σs => |Q e σs| ^ 3) +
            (fun σs => |Q f σs| ^ 3) + (fun σs => |Q g σs| ^ 3)) by
        funext σs; simp [smul_eq_mul]; ring]
      change lastSiteAverageLinearMap_test (s := s) path i u _ = _
      simp only [map_smul, map_add, lastSiteAverageLinearMap_apply_test, smul_eq_mul]
      rw [lastSite_cube_edge_eq_test path i u e,
        lastSite_cube_edge_eq_test path i u f,
        lastSite_cube_edge_eq_test path i u g]
      ring

lemma lastSiteQuenchedAverage_one_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    lastSiteQuenchedAverage (n := n) (s := s) path i u (fun _ => 1) = 1 := by
  unfold lastSiteQuenchedAverage quenchedReplicaAverage replicaGibbsAverage
  simp only [mul_one]
  rw [show (fun ω => ∑ σs : Replicas N n,
      ∏ a, SpinGlass.gibbs_pmf N (lastSiteHamiltonian (s := s) path i u ω) (σs a)) =
      fun _ => 1 by
    funext ω
    rw [← Fintype.prod_sum]
    simp [SpinGlass.sum_gibbs_pmf]]
  simp

lemma cavityCube4_one_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (i : Fin N) :
    cavityCube4 (s := s) path i 1 ≤
      4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3) := by
  let X : ReplicaFun N 4 := fun σs => |centeredOverlap q σs 0 1| ^ 3
  let c : ℝ := (1 / (N : ℝ)) ^ 3
  calc
    cavityCube4 (s := s) path i 1 ≤
        lastSiteQuenchedAverage (s := s) path i 1 (fun σs : Replicas N 4 =>
          4 * (X σs + c)) := by
      unfold cavityCube4
      apply quenchedReplicaAverage_mono
      · exact measurable_lastSiteHamiltonian path i 1
      · intro σs
        dsimp [X, c]
        have hs0 : |(1 / (N : ℝ)) * SpinGlass.spin N (σs 0) i *
              SpinGlass.spin N (σs 1) i| = 1 / (N : ℝ) := by
          have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
          cases h0 : σs 0 i <;> cases h1 : σs 1 i <;>
            simp [SpinGlass.spin, h0, h1]
        have hcub := abs_sub_cube_le (centeredOverlap q σs 0 1)
          ((1 / (N : ℝ)) * SpinGlass.spin N (σs 0) i *
            SpinGlass.spin N (σs 1) i)
        rw [hs0] at hcub
        change |centeredOverlap q σs 0 1 -
            (1 / (N : ℝ)) * SpinGlass.spin N (σs 0) i *
              SpinGlass.spin N (σs 1) i| ^ 3 ≤ _
        exact hcub
    _ = 4 * (thirdMoment path s + c) := by
      rw [show (fun σs : Replicas N 4 => 4 * (X σs + c)) =
          (4 : ℝ) • (X + fun _ => c) by
        funext σs; simp [smul_eq_mul]]
      change lastSiteAverageLinearMap_test (s := s) path i 1 _ = _
      simp only [map_smul, map_add, lastSiteAverageLinearMap_apply_test, smul_eq_mul]
      rw [show lastSiteQuenchedAverage (s := s) path i 1 X = thirdMoment path s by
        unfold lastSiteQuenchedAverage thirdMoment
        congr 1
        funext ω
        rw [lastSiteHamiltonian_one]]
      rw [show (fun _ : Replicas N 4 => c) = fun σs => c * (1 : ℝ) by
          funext σs; ring,
        lastSiteQuenchedAverage_const_mul_test, lastSiteQuenchedAverage_one_test]
      ring
    _ = _ := rfl

lemma cavityCube4_uniform_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) :
    cavityCube4 (s := s) path i u ≤
      Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)) := by
  let M : ℝ → ℝ := fun v => cavityCube4 (s := s) path i v
  let φ : ℝ → ℝ := fun x => (1 : ℝ) + -x
  let g : ℝ → ℝ := M ∘ φ
  let T : ℝ := 1 - u
  have hT : 0 ≤ T := by dsimp [T]; linarith [hu.2]
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) T) := by
    exact ((continuous_lastSiteQuenchedAverage path i
      (fun σs : Replicas N 4 => |cavityOverlapAt q i σs 0 1| ^ 3)).comp
        (continuous_const.sub continuous_id)).continuousOn
  have hgderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : ℝ,
      HasDerivAt g d t ∧ d ≤ (64 * β ^ 2) * g t := by
    intro t ht
    rcases ht with ⟨ht0, htT⟩
    have hv : φ t ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [T] at htT
      dsimp [φ]
      constructor <;> linarith [hu.1]
    obtain ⟨d, hd, hdb⟩ := cavityCube4_deriv_bound path hN hqI hs hv i
    refine ⟨-d, ?_, ?_⟩
    · have hi : HasDerivAt φ (-1 : ℝ) t := (hasDerivAt_neg t).const_add 1
      simpa only [g, mul_neg, mul_one] using hd.comp t hi
    · change -d ≤ (64 * β ^ 2) * M (φ t)
      exact (neg_le_abs d).trans hdb
  have hgr := SpinGlass.GeneralizedLatala.gronwall_le_endpoint hT hgcont hgderiv
  have hM1 := cavityCube4_one_le_test (s := s) path hN i
  have hnon : 0 ≤ M 1 := cavityCube4_nonneg path i 1
  have hexp : Real.exp ((64 * β ^ 2) * T) ≤ Real.exp (64 * β ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hk : 0 ≤ 64 * β ^ 2 := by positivity
    nlinarith [hu.1]
  calc
    M u = g T := by simp [g, φ, T]
    _ ≤ Real.exp ((64 * β ^ 2) * T) * g 0 := hgr
    _ ≤ Real.exp (64 * β ^ 2) * M 1 := by
      simp only [g, φ, Function.comp_apply, neg_zero, add_zero]
      gcongr
    _ ≤ Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)) := by
      gcongr
    _ = _ := rfl

def scoreInternalEdge_test {n : ℕ} (e : ReplicaEdge n) : ReplicaEdge (n + 2) :=
  ⟨(Fin.castAdd 2 e.1.1, Fin.castAdd 2 e.1.2), by
    rw [Fin.mk_lt_mk]
    exact e.2⟩

def scoreFreshEdge_test {n : ℕ} (a : Fin n) : ReplicaEdge (n + 2) :=
  ⟨(Fin.castAdd 2 a, Fin.natAdd n (0 : Fin 2)), by
    rw [Fin.mk_lt_mk]
    simpa only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, add_zero] using a.isLt⟩

def scoreLastEdge_test (n : ℕ) : ReplicaEdge (n + 2) :=
  ⟨(Fin.natAdd n (0 : Fin 2), Fin.natAdd n (1 : Fin 2)), by simp⟩

lemma normalizedScore_average_bound_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u M : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (P : ReplicaFun N (n + 2)) (hM : 0 ≤ M)
    (hterm : ∀ e : ReplicaEdge (n + 2),
      |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
        P σs * cavityInteractionAt q i (σs e.1.1) (σs e.1.2))| ≤ M) :
    |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
      P σs * normalizedCavityScoreObservable (n := n) q i σs)| ≤
      ((Fintype.card (ReplicaEdge n) : ℝ) + (n : ℝ) * n +
        (n : ℝ) * ((n : ℝ) + 1) / 2) * M := by
  let L := lastSiteAverageLinearMap_test (n := n + 2) (s := s) path i u
  let A : ReplicaEdge n → ReplicaFun N (n + 2) := fun e σs =>
    P σs * cavityInteractionAt q i
      (σs (scoreInternalEdge_test e).1.1) (σs (scoreInternalEdge_test e).1.2)
  let B : Fin n → ReplicaFun N (n + 2) := fun a σs =>
    P σs * cavityInteractionAt q i
      (σs (scoreFreshEdge_test a).1.1) (σs (scoreFreshEdge_test a).1.2)
  let D : ReplicaFun N (n + 2) := fun σs =>
    P σs * cavityInteractionAt q i
      (σs (scoreLastEdge_test n).1.1) (σs (scoreLastEdge_test n).1.2)
  have hobs : (fun σs : Replicas N (n + 2) =>
      P σs * normalizedCavityScoreObservable (n := n) q i σs) =
      (∑ e, A e) - (n : ℝ) • (∑ a, B a) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) • D := by
    funext σs
    unfold normalizedCavityScoreObservable
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, A, B, D, scoreInternalEdge_test, scoreFreshEdge_test,
      scoreLastEdge_test, initialReplicas, firstFreshReplica, secondFreshReplica]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  change |L _| ≤ _
  rw [hobs]
  simp only [map_add, map_sub, map_smul, map_sum, smul_eq_mul]
  have hA : |∑ e, L (A e)| ≤ (Fintype.card (ReplicaEdge n) : ℝ) * M := by
    calc
      _ ≤ ∑ e, |L (A e)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : ReplicaEdge n, M := by
        gcongr with e
        simpa [L, A, lastSiteAverageLinearMap_apply_test] using
          hterm (scoreInternalEdge_test e)
      _ = _ := by simp [nsmul_eq_mul]
  have hB : |∑ a, L (B a)| ≤ (n : ℝ) * M := by
    calc
      _ ≤ ∑ a, |L (B a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, M := by
        gcongr with a
        simpa [L, B, lastSiteAverageLinearMap_apply_test] using
          hterm (scoreFreshEdge_test a)
      _ = _ := by simp [nsmul_eq_mul]
  have hD : |L D| ≤ M := by
    simpa [L, D, lastSiteAverageLinearMap_apply_test] using hterm (scoreLastEdge_test n)
  calc
    |∑ e, L (A e) - (n : ℝ) * ∑ a, L (B a) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * L D| ≤
      |∑ e, L (A e)| + |(n : ℝ) * ∑ a, L (B a)| +
        |((n : ℝ) * ((n : ℝ) + 1) / 2) * L D| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (Fintype.card (ReplicaEdge n) : ℝ) * M +
        (n : ℝ) * ((n : ℝ) * M) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * M := by
      rw [abs_mul, abs_mul]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [abs_of_nonneg hn]
      have hc : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by positivity
      rw [abs_of_nonneg hc]
      gcongr
    _ ≤ _ := by
      have ht : 0 ≤ thirdMoment path s := by
        unfold thirdMoment quenchedReplicaAverage
        apply integral_nonneg
        intro ω
        apply replicaGibbsAverage_nonneg
        intro σs
        positivity
      ring_nf
      nlinarith

lemma abs_cavityInteractionAt_eq_test {N : ℕ} (q : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    |cavityInteractionAt q i σ τ| =
      |configCavityOverlapAt i σ τ - q| := by
  unfold cavityInteractionAt
  rw [abs_mul, abs_mul]
  have hσ : |SpinGlass.spin N σ i| = 1 := by
    cases h : σ i <;> simp [SpinGlass.spin, h]
  have hτ : |SpinGlass.spin N τ i| = 1 := by
    cases h : τ i <;> simp [SpinGlass.spin, h]
  rw [hσ, hτ, one_mul, one_mul]

lemma abs_cavityInteractionAt_replicas_eq_test {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) :
    |cavityInteractionAt q i (σs a) (σs b)| = |cavityOverlapAt q i σs a b| := by
  rw [abs_cavityInteractionAt_eq_test, cavityOverlapAt_eq_configCavityOverlapAt_sub]

lemma cavityInteractionAt_eq_spin_mul_overlap_test {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) :
    cavityInteractionAt q i (σs a) (σs b) =
      SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i *
        cavityOverlapAt q i σs a b := by
  rw [cavityInteractionAt, cavityOverlapAt_eq_configCavityOverlapAt_sub]

lemma canonicalCube6_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
      |cavityOverlapAt q i σs 0 1| ^ 3) = cavityCube4 (s := s) path i u := by
  let F : ReplicaFun N 4 := fun σs => |cavityOverlapAt q i σs 0 1| ^ 3
  have hp : (fun σs : Replicas N 6 => |cavityOverlapAt q i σs 0 1| ^ 3) =
      fun σs => F (initialReplicas σs) := by rfl
  rw [hp, lastSiteAverage_initialReplicas_test]
  rfl

lemma canonicalCube8_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 8 =>
      |cavityOverlapAt q i σs 0 1| ^ 3) = cavityCube4 (s := s) path i u := by
  calc
    _ = lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
        |cavityOverlapAt q i σs 0 1| ^ 3) := by
      let F : ReplicaFun N 6 := fun σs => |cavityOverlapAt q i σs 0 1| ^ 3
      have hp : (fun σs : Replicas N 8 => |cavityOverlapAt q i σs 0 1| ^ 3) =
          fun σs => F (initialReplicas σs) := by rfl
      rw [hp, lastSiteAverage_initialReplicas_test]
    _ = _ := canonicalCube6_eq_test path i u

lemma abs_lastSite_QQ_score_four_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f : ReplicaEdge 6) :
    |lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs e.1.1 e.1.2 *
      cavityOverlapAt q i σs f.1.1 f.1.2 *
      normalizedCavityScoreObservable (n := 4) q i σs)| ≤
      32 * cavityCube4 (s := s) path i u := by
  let P : ReplicaFun N 6 := fun σs =>
    cavityOverlapAt q i σs e.1.1 e.1.2 *
      cavityOverlapAt q i σs f.1.1 f.1.2
  have hterm (d : ReplicaEdge 6) :
      |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
        P σs * cavityInteractionAt q i (σs d.1.1) (σs d.1.2))| ≤
        cavityCube4 (s := s) path i u := by
    let W : ReplicaFun N 6 := fun σs =>
      SpinGlass.spin N (σs d.1.1) i * SpinGlass.spin N (σs d.1.2) i
    have hW : ∀ σs, |W σs| ≤ 1 := by
      intro σs
      cases h1 : σs d.1.1 i <;> cases h2 : σs d.1.2 i <;>
        simp [W, SpinGlass.spin, h1, h2]
    calc
      _ = |lastSiteQuenchedAverage (s := s) path i u (fun σs => W σs *
          cavityOverlapAt q i σs e.1.1 e.1.2 *
          cavityOverlapAt q i σs f.1.1 f.1.2 *
          cavityOverlapAt q i σs d.1.1 d.1.2)| := by
        congr 2
        funext σs
        rw [cavityInteractionAt_eq_spin_mul_overlap_test]
        dsimp [P, W]
        ring
      _ ≤ lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
          |cavityOverlapAt q i σs 0 1| ^ 3) :=
        abs_lastSite_triple_edges_le_test path i u e f d W hW
      _ = _ := canonicalCube6_eq_test path i u
  have h := normalizedScore_average_bound_test path i P
    (cavityCube4_nonneg path i u) hterm
  have hcard : Fintype.card (ReplicaEdge 4) = 6 := by decide
  norm_num [hcard] at h ⊢
  simpa [P] using h

def e4_01 : ReplicaEdge 4 := ⟨(0, 1), by decide⟩
def e4_02 : ReplicaEdge 4 := ⟨(0, 2), by decide⟩
def e4_23 : ReplicaEdge 4 := ⟨(2, 3), by decide⟩

noncomputable def cavityQuadratic4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f : ReplicaEdge 4) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u (fun σs =>
    cavityOverlapAt q i σs e.1.1 e.1.2 * cavityOverlapAt q i σs f.1.1 f.1.2)

noncomputable def cavityQuadraticDeriv4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f : ReplicaEdge 4) : ℝ :=
  s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
    cavityOverlapAt q i (initialReplicas σs) e.1.1 e.1.2 *
      cavityOverlapAt q i (initialReplicas σs) f.1.1 f.1.2 *
      normalizedCavityScoreObservable (n := 4) q i σs)

@[simp] lemma cavityOverlapAt_initialReplicas_test {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N (n + 2)) (a b : Fin n) :
    cavityOverlapAt q i (initialReplicas σs) a b =
      cavityOverlapAt q i σs (Fin.castAdd 2 a) (Fin.castAdd 2 b) := rfl

lemma hasDerivAt_cavityQuadratic4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin N) (e f : ReplicaEdge 4) :
    HasDerivAt (fun v => cavityQuadratic4_test (s := s) path i v e f)
      (cavityQuadraticDeriv4_test (s := s) path i u e f) u := by
  let F : ReplicaFun N 4 := fun σs =>
    cavityOverlapAt q i σs e.1.1 e.1.2 * cavityOverlapAt q i σs f.1.1 f.1.2
  have hder := hasDerivAt_lastSiteQuenchedAverage_fixedScore path i hs hu F
  simpa [cavityQuadratic4_test, cavityQuadraticDeriv4_test, F] using hder

lemma abs_cavityQuadraticDeriv4_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) (u : ℝ) (e f : ReplicaEdge 4) :
    |cavityQuadraticDeriv4_test (s := s) path i u e f| ≤
      32 * β ^ 2 * cavityCube4 (s := s) path i u := by
  have hscore := abs_lastSite_QQ_score_four_le_test (s := s) path i u
    (scoreInternalEdge_test e) (scoreInternalEdge_test f)
  dsimp only [scoreInternalEdge_test] at hscore
  unfold cavityQuadraticDeriv4_test
  simp only [cavityOverlapAt_initialReplicas_test]
  rw [abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg (sq_nonneg β)]
  calc
    s * β ^ 2 * _ ≤ 1 * β ^ 2 * (32 * cavityCube4 (s := s) path i u) := by
      gcongr
      exact hs.2
    _ = _ := by ring

lemma abs_cavityQuadratic4_one_sub_zero_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (e f : ReplicaEdge 4) :
    |cavityQuadratic4_test (s := s) path i 1 e f -
      cavityQuadratic4_test (s := s) path i 0 e f| ≤
      32 * β ^ 2 * (Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3))) := by
  let F : ℝ → ℝ := fun u => cavityQuadratic4_test (s := s) path i u e f
  let F' : ℝ → ℝ := fun u => cavityQuadraticDeriv4_test (s := s) path i u e f
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F F' (by norm_num)
    ((continuous_lastSiteQuenchedAverage path i
      (fun σs : Replicas N 4 => cavityOverlapAt q i σs e.1.1 e.1.2 *
        cavityOverlapAt q i σs f.1.1 f.1.2)).continuousOn)
    (fun u hu => hasDerivAt_cavityQuadratic4_test path hs hu i e f)
  have hcube := cavityCube4_uniform_test path hN hqI hs ⟨hc.1.le, hc.2.le⟩ i
  have hd := abs_cavityQuadraticDeriv4_le_test path hs i c e f
  change |F' c| ≤ 32 * β ^ 2 * cavityCube4 (s := s) path i c at hd
  rw [show F' c = F 1 - F 0 by simpa using hslope] at hd
  exact hd.trans (by gcongr)

lemma linearMap_normalizedScore_bound_test
    {N n : ℕ} {q M : ℝ} (i : Fin N)
    (L : ReplicaFun N (n + 2) →ₗ[ℝ] ℝ) (hM : 0 ≤ M)
    (hterm : ∀ e : ReplicaEdge (n + 2),
      |L (fun σs => cavityInteractionAt q i (σs e.1.1) (σs e.1.2))| ≤ M) :
    |L (normalizedCavityScoreObservable (n := n) q i)| ≤
      ((Fintype.card (ReplicaEdge n) : ℝ) + (n : ℝ) * n +
        (n : ℝ) * ((n : ℝ) + 1) / 2) * M := by
  let A : ReplicaEdge n → ReplicaFun N (n + 2) := fun e σs =>
    cavityInteractionAt q i
      (σs (scoreInternalEdge_test e).1.1) (σs (scoreInternalEdge_test e).1.2)
  let B : Fin n → ReplicaFun N (n + 2) := fun a σs =>
    cavityInteractionAt q i
      (σs (scoreFreshEdge_test a).1.1) (σs (scoreFreshEdge_test a).1.2)
  let D : ReplicaFun N (n + 2) := fun σs =>
    cavityInteractionAt q i
      (σs (scoreLastEdge_test n).1.1) (σs (scoreLastEdge_test n).1.2)
  have hobs : normalizedCavityScoreObservable (n := n) q i =
      (∑ e, A e) - (n : ℝ) • (∑ a, B a) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) • D := by
    funext σs
    unfold normalizedCavityScoreObservable
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, A, B, D, scoreInternalEdge_test, scoreFreshEdge_test,
      scoreLastEdge_test, initialReplicas, firstFreshReplica, secondFreshReplica]
  rw [hobs]
  simp only [map_add, map_sub, map_smul, map_sum, smul_eq_mul]
  have hA : |∑ e, L (A e)| ≤ (Fintype.card (ReplicaEdge n) : ℝ) * M := by
    calc
      _ ≤ ∑ e, |L (A e)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : ReplicaEdge n, M := by
        gcongr with e
        simpa [A] using hterm (scoreInternalEdge_test e)
      _ = _ := by simp [nsmul_eq_mul]
  have hB : |∑ a, L (B a)| ≤ (n : ℝ) * M := by
    calc
      _ ≤ ∑ a, |L (B a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, M := by
        gcongr with a
        simpa [B] using hterm (scoreFreshEdge_test a)
      _ = _ := by simp [nsmul_eq_mul]
  have hD : |L D| ≤ M := by simpa [D] using hterm (scoreLastEdge_test n)
  calc
    |∑ e, L (A e) - (n : ℝ) * ∑ a, L (B a) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * L D| ≤
      |∑ e, L (A e)| + |(n : ℝ) * ∑ a, L (B a)| +
        |((n : ℝ) * ((n : ℝ) + 1) / 2) * L D| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (Fintype.card (ReplicaEdge n) : ℝ) * M +
        (n : ℝ) * ((n : ℝ) * M) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * M := by
      rw [abs_mul, abs_mul]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [abs_of_nonneg hn]
      have hc : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by positivity
      rw [abs_of_nonneg hc]
      gcongr
    _ = _ := by ring

noncomputable def weightedInitialLinearMap8_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (P : ReplicaFun N 8) : ReplicaFun N 6 →ₗ[ℝ] ℝ where
  toFun F := lastSiteQuenchedAverage (s := s) path i u (fun σs => P σs * F (initialReplicas σs))
  map_add' F G := by
    change lastSiteAverageLinearMap_test (s := s) path i u _ = _
    rw [show (fun σs : Replicas N 8 => P σs * (F + G) (initialReplicas σs)) =
        (fun σs => P σs * F (initialReplicas σs)) +
          (fun σs => P σs * G (initialReplicas σs)) by
      funext σs; simp; ring]
    exact map_add _ _ _
  map_smul' c F := by
    change lastSiteAverageLinearMap_test (s := s) path i u _ = _
    rw [show (fun σs : Replicas N 8 => P σs * (c • F) (initialReplicas σs)) =
        c • (fun σs => P σs * F (initialReplicas σs)) by
      funext σs; simp [smul_eq_mul]; ring]
    exact map_smul _ _ _

lemma abs_embeddedScore_four_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u M : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (P : ReplicaFun N 8) (hM : 0 ≤ M)
    (hterm : ∀ e : ReplicaEdge 6,
      |lastSiteQuenchedAverage (s := s) path i u (fun σs => P σs *
        cavityInteractionAt q i (initialReplicas σs e.1.1) (initialReplicas σs e.1.2))| ≤ M) :
    |lastSiteQuenchedAverage (s := s) path i u (fun σs => P σs *
      normalizedCavityScoreObservable (n := 4) q i (initialReplicas σs))| ≤ 32 * M := by
  let L := weightedInitialLinearMap8_test (s := s) path i u P
  have ht (e : ReplicaEdge 6) :
      |L (fun τs => cavityInteractionAt q i (τs e.1.1) (τs e.1.2))| ≤ M := hterm e
  have h := linearMap_normalizedScore_bound_test i L hM ht
  have hcard : Fintype.card (ReplicaEdge 4) = 6 := by decide
  norm_num [hcard] at h ⊢
  exact h

noncomputable def spinPairAt_test {N n : ℕ} (i : Fin N) (e : ReplicaEdge n)
    (σs : Replicas N n) : ℝ :=
  SpinGlass.spin N (σs e.1.1) i * SpinGlass.spin N (σs e.1.2) i

lemma abs_spinPairAt_test {N n : ℕ} (i : Fin N) (e : ReplicaEdge n)
    (σs : Replicas N n) : |spinPairAt_test i e σs| = 1 := by
  unfold spinPairAt_test
  rw [abs_mul]
  cases h1 : σs e.1.1 i <;> cases h2 : σs e.1.2 i <;>
    simp [SpinGlass.spin, h1, h2]

lemma abs_centeredSpinPair_le_two_test {N n : ℕ} {q : ℝ}
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) (e : ReplicaEdge n)
    (σs : Replicas N n) : |spinPairAt_test i e σs - q| ≤ 2 := by
  calc
    _ ≤ |spinPairAt_test i e σs| + |q| := abs_sub _ _
    _ = 1 + q := by rw [abs_spinPairAt_test, abs_of_nonneg hqI.1]
    _ ≤ 2 := by linarith [hqI.2]

lemma abs_offdiag_nestedScore_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) (u : ℝ)
    (target : ReplicaEdge 6) :
    |lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 8 =>
      cavityOverlapAt q i (initialReplicas σs) 0 1 *
        (spinPairAt_test i target (initialReplicas σs) - q) *
        normalizedCavityScoreObservable (n := 4) q i (initialReplicas σs) *
        normalizedCavityScoreObservable (n := 6) q i σs)| ≤
      4608 * cavityCube4 (s := s) path i u := by
  let Base : ReplicaFun N 8 := fun σs =>
    cavityOverlapAt q i (initialReplicas σs) 0 1 *
      (spinPairAt_test i target (initialReplicas σs) - q) *
      normalizedCavityScoreObservable (n := 4) q i (initialReplicas σs)
  have houter (d : ReplicaEdge 8) :
      |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
        Base σs * cavityInteractionAt q i (σs d.1.1) (σs d.1.2))| ≤
        64 * cavityCube4 (s := s) path i u := by
    let P : ReplicaFun N 8 := fun σs =>
      cavityOverlapAt q i (initialReplicas σs) 0 1 *
        (spinPairAt_test i target (initialReplicas σs) - q) *
        cavityInteractionAt q i (σs d.1.1) (σs d.1.2)
    have hinner (e : ReplicaEdge 6) :
        |lastSiteQuenchedAverage (s := s) path i u (fun σs => P σs *
          cavityInteractionAt q i (initialReplicas σs e.1.1)
            (initialReplicas σs e.1.2))| ≤
          2 * cavityCube4 (s := s) path i u := by
      let e0 : ReplicaEdge 8 := scoreInternalEdge_test ee01
      let et : ReplicaEdge 8 := scoreInternalEdge_test target
      let ei : ReplicaEdge 8 := scoreInternalEdge_test e
      let W : ReplicaFun N 8 := fun σs =>
        ((spinPairAt_test i et σs - q) / 2) * spinPairAt_test i d σs *
          spinPairAt_test i ei σs
      have hW : ∀ σs, |W σs| ≤ 1 := by
        intro σs
        rw [abs_mul, abs_mul, abs_div,
          abs_spinPairAt_test, abs_spinPairAt_test, mul_one, mul_one]
        norm_num
        have ht := abs_centeredSpinPair_le_two_test hqI i et σs
        linarith
      have htriple := abs_lastSite_triple_edges_le_test (s := s) path i u e0 d ei W hW
      rw [canonicalCube8_eq_test] at htriple
      calc
        _ = |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
            2 * (W σs * cavityOverlapAt q i σs e0.1.1 e0.1.2 *
              cavityOverlapAt q i σs d.1.1 d.1.2 *
              cavityOverlapAt q i σs ei.1.1 ei.1.2))| := by
          congr 2
          funext σs
          dsimp only [P]
          rw [cavityInteractionAt_eq_spin_mul_overlap_test,
            cavityInteractionAt_eq_spin_mul_overlap_test]
          dsimp [W, e0, et, ei, spinPairAt_test, initialReplicas,
            scoreInternalEdge_test]
          simp only [ee01]
          have h0 : Fin.castAdd 2 (0 : Fin 6) = (0 : Fin 8) := rfl
          have h1 : Fin.castAdd 2 (1 : Fin 6) = (1 : Fin 8) := rfl
          rw [h0, h1]
          ring
        _ = 2 * |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
            W σs * cavityOverlapAt q i σs e0.1.1 e0.1.2 *
              cavityOverlapAt q i σs d.1.1 d.1.2 *
              cavityOverlapAt q i σs ei.1.1 ei.1.2)| := by
          rw [lastSiteQuenchedAverage_const_mul_test, abs_mul]
          norm_num
        _ ≤ 2 * cavityCube4 (s := s) path i u := by gcongr
    have hemb := abs_embeddedScore_four_le_test path i P
      (mul_nonneg (by norm_num) (cavityCube4_nonneg path i u)) hinner
    calc
      _ = |lastSiteQuenchedAverage (s := s) path i u (fun σs => P σs *
          normalizedCavityScoreObservable (n := 4) q i (initialReplicas σs))| := by
        congr 2
        funext σs
        dsimp [Base, P]
        ring
      _ ≤ 32 * (2 * cavityCube4 (s := s) path i u) := hemb
      _ = _ := by ring
  have hout := normalizedScore_average_bound_test path i Base
    (mul_nonneg (by norm_num) (cavityCube4_nonneg path i u)) houter
  have hcard : Fintype.card (ReplicaEdge 6) = 15 := by decide
  norm_num [hcard] at hout ⊢
  calc
    _ ≤ 72 * (64 * cavityCube4 (s := s) path i u) := by simpa [Base] using hout
    _ = _ := by ring

noncomputable def cavityOffdiag4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u (fun σs =>
    cavityOverlapAt q i σs 0 1 * (spinPairAt_test i target σs - q))

noncomputable def cavityOffdiagDeriv4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) : ℝ :=
  s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
    cavityOverlapAt q i σs 0 1 *
      (spinPairAt_test i (scoreInternalEdge_test target) σs - q) *
      normalizedCavityScoreObservable (n := 4) q i σs)

noncomputable def cavityOffdiagSecondDeriv4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) : ℝ :=
  (s * β ^ 2) ^ 2 * lastSiteQuenchedAverage (s := s) path i u
    (fun σs : Replicas N 8 =>
      cavityOverlapAt q i (initialReplicas σs) 0 1 *
        (spinPairAt_test i (scoreInternalEdge_test target) (initialReplicas σs) - q) *
        normalizedCavityScoreObservable (n := 4) q i (initialReplicas σs) *
        normalizedCavityScoreObservable (n := 6) q i σs)

lemma hasDerivAt_cavityOffdiag4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin N) (target : ReplicaEdge 4) :
    HasDerivAt (fun v => cavityOffdiag4_test (s := s) path i v target)
      (cavityOffdiagDeriv4_test (s := s) path i u target) u := by
  let F : ReplicaFun N 4 := fun σs =>
    cavityOverlapAt q i σs 0 1 * (spinPairAt_test i target σs - q)
  have hder := hasDerivAt_lastSiteQuenchedAverage_fixedScore path i hs hu F
  simpa [cavityOffdiag4_test, cavityOffdiagDeriv4_test, F, spinPairAt_test,
    scoreInternalEdge_test, initialReplicas] using hder

lemma hasDerivAt_cavityOffdiagDeriv4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin N) (target : ReplicaEdge 4) :
    HasDerivAt (fun v => cavityOffdiagDeriv4_test (s := s) path i v target)
      (cavityOffdiagSecondDeriv4_test (s := s) path i u target) u := by
  let F : ReplicaFun N 6 := fun σs =>
    cavityOverlapAt q i σs 0 1 *
      (spinPairAt_test i (scoreInternalEdge_test target) σs - q) *
      normalizedCavityScoreObservable (n := 4) q i σs
  have hder := hasDerivAt_lastSiteQuenchedAverage_fixedScore path i hs hu F
  have hscaled := (hder.const_mul (s * β ^ 2))
  simpa [cavityOffdiagDeriv4_test, cavityOffdiagSecondDeriv4_test, F,
    mul_assoc, pow_two] using hscaled

lemma abs_cavityOffdiagSecondDeriv4_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) :
    |cavityOffdiagSecondDeriv4_test (s := s) path i u target| ≤
      4608 * β ^ 4 * cavityCube4 (s := s) path i u := by
  have hnested := abs_offdiag_nestedScore_le_test (s := s) path hqI i u
    (scoreInternalEdge_test target)
  unfold cavityOffdiagSecondDeriv4_test
  rw [abs_mul, abs_pow, abs_mul, abs_pow, abs_of_nonneg hs.1,
    sq_abs]
  calc
    (s * β ^ 2) ^ 2 * _ ≤ (1 * β ^ 2) ^ 2 *
        (4608 * cavityCube4 (s := s) path i u) := by
      have hb0 : 0 ≤ s * β ^ 2 := mul_nonneg hs.1 (sq_nonneg β)
      have hb : s * β ^ 2 ≤ 1 * β ^ 2 :=
        mul_le_mul_of_nonneg_right hs.2 (sq_nonneg β)
      have hsq := pow_le_pow_left₀ hb0 hb 2
      exact mul_le_mul hsq hnested (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma cavityOffdiag4_zero_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (target : ReplicaEdge 4) : cavityOffdiag4_test (s := s) path i 0 target = 0 := by
  let t6 : ReplicaEdge 6 := scoreInternalEdge_test target
  let Fbulk : (Fin 6 → SiteBaseConfig N i) → ℝ := fun ρs =>
    bulkEdgeCavity6 q i ee01 ρs
  have hspin := lastSite_zero_bulk_spin_two_test (s := s) path hN hh hq i Fbulk
    (edgeFinset6 t6) (edgeFinset6_card t6)
  have hobs : (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs 0 1 * (spinPairAt_test i t6 σs - q)) =
      (fun σs => Fbulk (replicasSplitSiteEquiv i σs).1 *
        ∏ a ∈ edgeFinset6 t6, SpinGlass.spin N (σs a) i) -
      fun σs => q * Fbulk (replicasSplitSiteEquiv i σs).1 := by
    funext σs
    rw [show spinPairAt_test i t6 σs = edgeSpin6 i t6 σs by rfl,
      edgeSpin6_eq_prod]
    dsimp [Fbulk]
    rw [bulkEdgeCavity6_split_test]
    simp only [ee01]
    ring
  unfold cavityOffdiag4_test
  rw [← lastSiteAverage_initialReplicas_test (n := 4) (s := s) path i 0]
  rw [show (fun σs : Replicas N 6 =>
      (fun τs : Replicas N 4 => cavityOverlapAt q i τs 0 1 *
        (spinPairAt_test i target τs - q)) (initialReplicas σs)) =
      fun σs => cavityOverlapAt q i σs 0 1 * (spinPairAt_test i t6 σs - q) by
    funext σs
    dsimp [spinPairAt_test, t6, scoreInternalEdge_test, initialReplicas]]
  rw [hobs]
  change lastSiteQuenchedAverage (s := s) path i 0 (fun σs =>
    Fbulk (replicasSplitSiteEquiv i σs).1 *
      ∏ a ∈ edgeFinset6 t6, SpinGlass.spin N (σs a) i -
    q * Fbulk (replicasSplitSiteEquiv i σs).1) = 0
  rw [lastSiteQuenchedAverage_sub_test,
    lastSiteQuenchedAverage_const_mul_test]
  change _ - q * lastSiteQuenchedAverage (s := s) path i 0
    (fun σs => Fbulk (replicasSplitSiteEquiv i σs).1) = 0
  rw [hspin]
  ring

lemma cavityOffdiag4_taylor_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N) (target : ReplicaEdge 4) :
    |cavityOffdiag4_test (s := s) path i 1 target -
      cavityOffdiagDeriv4_test (s := s) path i 0 target| ≤
      4608 * β ^ 4 * (Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3))) := by
  let G : ℝ → ℝ := fun u => cavityOffdiag4_test (s := s) path i u target
  let D : ℝ → ℝ := fun u => cavityOffdiagDeriv4_test (s := s) path i u target
  let D' : ℝ → ℝ := fun u => cavityOffdiagSecondDeriv4_test (s := s) path i u target
  obtain ⟨c, hc, hGc⟩ := exists_hasDerivAt_eq_slope G D (by norm_num)
    ((continuous_lastSiteQuenchedAverage path i
      (fun σs : Replicas N 4 => cavityOverlapAt q i σs 0 1 *
        (spinPairAt_test i target σs - q))).continuousOn)
    (fun u hu => hasDerivAt_cavityOffdiag4_test path hs hu i target)
  have hG0 := cavityOffdiag4_zero_test (s := s) path hN hh hq i target
  have hGc' : G 1 = D c := by
    dsimp [G, D] at hGc ⊢
    norm_num at hGc
    linarith [hG0]
  obtain ⟨d, hd, hDd⟩ := exists_hasDerivAt_eq_slope D D' hc.1
    ((continuous_const.mul (continuous_lastSiteQuenchedAverage path i
      (fun σs : Replicas N 6 => cavityOverlapAt q i σs 0 1 *
        (spinPairAt_test i (scoreInternalEdge_test target) σs - q) *
        normalizedCavityScoreObservable (n := 4) q i σs))).continuousOn)
    (fun u hu => hasDerivAt_cavityOffdiagDeriv4_test path hs
      ⟨hu.1, hu.2.trans hc.2⟩ i target)
  have hcube := cavityCube4_uniform_test path hN hqI hs
    ⟨hd.1.le, hd.2.le.trans hc.2.le⟩ i
  have hsecond := abs_cavityOffdiagSecondDeriv4_le_test path hqI hs i d target
  have hDd' : D c - D 0 = D' d * c := by
    have heq : D' d * c = D c - D 0 :=
      (eq_div_iff hc.1.ne').mp (by simpa using hDd)
    exact heq.symm
  change |G 1 - D 0| ≤ _
  rw [hGc']
  rw [hDd']
  rw [abs_mul]
  calc
    |D' d| * |c| ≤ (4608 * β ^ 4 * cavityCube4 (s := s) path i d) * 1 := by
      apply mul_le_mul hsecond
      · rw [abs_of_nonneg hc.1.le]
        exact hc.2.le
      · exact abs_nonneg _
      · exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          (cavityCube4_nonneg path i d)
    _ ≤ (4608 * β ^ 4 *
        (Real.exp (64 * β ^ 2) *
          (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)))) * 1 := by
      gcongr
    _ = _ := by ring

lemma rpow_neg_half_sq_test {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / (N : ℝ) := by
  have hNr : 0 ≤ (N : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNr]
  norm_num [Real.rpow_neg_one, one_div]

lemma rpow_neg_half_cube_test {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 3 = (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hNr : 0 ≤ (N : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNr]
  congr 1
  ring

lemma inv_pow_three_le_rpow_test {N : ℕ} (hN : 0 < N) :
    (1 / (N : ℝ)) ^ 3 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hp := Real.rpow_le_rpow_of_exponent_le hNr
    (by norm_num : (-(3 : ℝ)) ≤ -(3 : ℝ) / 2)
  rw [show (1 / (N : ℝ)) ^ 3 = (N : ℝ) ^ (-(3 : ℝ)) by
    rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN0]
    norm_num] 
  exact hp

lemma inv_pow_two_le_rpow_test {N : ℕ} (hN : 0 < N) :
    (1 / (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hp := Real.rpow_le_rpow_of_exponent_le hNr
    (by norm_num : (-(2 : ℝ)) ≤ -(3 : ℝ) / 2)
  rw [show (1 / (N : ℝ)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ)) by
    rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN0]
    norm_num]
  exact hp

lemma young_abs_div_N_test {N : ℕ} (hN : 0 < N) (x : ℝ) :
    |x| / (N : ℝ) ≤ (|x| ^ 3 + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3 := by
  let y : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2)
  have hy : 0 ≤ y := Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _
  have hy2 : y ^ 2 = 1 / (N : ℝ) := rpow_neg_half_sq_test hN
  have hy3 : y ^ 3 = (N : ℝ) ^ (-(3 : ℝ) / 2) := rpow_neg_half_cube_test hN
  have hyoung : 3 * |x| * y ^ 2 ≤ |x| ^ 3 + 2 * y ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (|x| - y))
      (by positivity : 0 ≤ |x| + 2 * y)]
  rw [hy2, hy3] at hyoung
  rw [div_eq_mul_inv]
  ring_nf at hyoung ⊢
  nlinarith

noncomputable def cavityAbs4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u
    (fun σs : Replicas N 4 => |cavityOverlapAt q i σs 0 1|)

lemma lastSite_abs_edge_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e : ReplicaEdge (n + 2)) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N (n + 2) =>
      |cavityOverlapAt q i σs e.1.1 e.1.2|) =
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N (n + 2) =>
      |cavityOverlapAt q i σs 0 1|) := by
  let F : ReplicaFun N (n + 2) := fun σs => |cavityOverlapAt q i σs 0 1|
  have hr := quenchedReplicaAverage_relabel
    (lastSiteHamiltonian (s := s) path i u) F (pairPerm_test e)
  have hp : (fun σs => F (replicaRelabelEquiv (pairPerm_test e) σs)) =
      fun σs => |cavityOverlapAt q i σs e.1.1 e.1.2| := by
    funext σs
    dsimp only [F]
    change |cavityOverlapAt q i σs (pairPerm_test e 0) (pairPerm_test e 1)| = _
    rw [pairPerm_zero_test, pairPerm_one_test]
  rw [hp] at hr
  exact hr

lemma canonicalAbs6_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
      |cavityOverlapAt q i σs 0 1|) = cavityAbs4_test (s := s) path i u := by
  let F : ReplicaFun N 4 := fun σs => |cavityOverlapAt q i σs 0 1|
  have hp : (fun σs : Replicas N 6 => |cavityOverlapAt q i σs 0 1|) =
      fun σs => F (initialReplicas σs) := by rfl
  rw [hp, lastSiteAverage_initialReplicas_test]
  rfl

lemma cavityAbs4_div_N_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (i : Fin N) (u : ℝ) :
    cavityAbs4_test (s := s) path i u / (N : ℝ) ≤
      (cavityCube4 (s := s) path i u +
        2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3 := by
  let Q : ReplicaFun N 4 := fun σs => |cavityOverlapAt q i σs 0 1|
  have hmono := quenchedReplicaAverage_mono
    (lastSiteHamiltonian (s := s) path i u) (measurable_lastSiteHamiltonian path i u)
    (fun σs => Q σs / (N : ℝ))
    (fun σs => (Q σs ^ 3 + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3)
    (fun σs => young_abs_div_N_test hN (cavityOverlapAt q i σs 0 1))
  have hNr : (N : ℝ) ≠ 0 := by positivity
  change lastSiteQuenchedAverage (s := s) path i u
      (fun σs => Q σs / (N : ℝ)) ≤
    lastSiteQuenchedAverage (s := s) path i u
      (fun σs => (Q σs ^ 3 + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) at hmono
  rw [show (fun σs => Q σs / (N : ℝ)) =
      fun σs => (1 / (N : ℝ)) * Q σs by funext σs; ring,
    lastSiteQuenchedAverage_const_mul_test] at hmono
  rw [show (fun σs => (Q σs ^ 3 +
      2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) =
      (3 : ℝ)⁻¹ • ((fun σs => Q σs ^ 3) +
        fun _ => 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) by
      funext σs; simp [smul_eq_mul]; ring] at hmono
  change (1 / (N : ℝ)) * lastSiteQuenchedAverage (s := s) path i u Q ≤
    lastSiteAverageLinearMap_test (s := s) path i u _ at hmono
  simp only [map_smul, map_add, lastSiteAverageLinearMap_apply_test, smul_eq_mul] at hmono
  rw [show (fun _ : Replicas N 4 => 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) =
      fun σs => (2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) * (1 : ℝ) by
      funext σs; ring,
    lastSiteQuenchedAverage_const_mul_test, lastSiteQuenchedAverage_one_test] at hmono
  change cavityAbs4_test (s := s) path i u / (N : ℝ) ≤ _
  convert hmono using 1 <;> simp [cavityAbs4_test, cavityCube4, Q, div_eq_mul_inv] <;> ring

noncomputable def cavityDiagonal4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) : ℝ :=
  lastSiteQuenchedAverage (s := s) path i u (fun σs =>
    spinPairAt_test i e4_01 σs * (spinPairAt_test i target σs - q))

noncomputable def cavityDiagonalDeriv4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) : ℝ :=
  s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
    spinPairAt_test i (scoreInternalEdge_test e4_01) σs *
      (spinPairAt_test i (scoreInternalEdge_test target) σs - q) *
      normalizedCavityScoreObservable (n := 4) q i σs)

lemma hasDerivAt_cavityDiagonal4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin N) (target : ReplicaEdge 4) :
    HasDerivAt (fun v => cavityDiagonal4_test (s := s) path i v target)
      (cavityDiagonalDeriv4_test (s := s) path i u target) u := by
  let F : ReplicaFun N 4 := fun σs =>
    spinPairAt_test i e4_01 σs * (spinPairAt_test i target σs - q)
  have hder := hasDerivAt_lastSiteQuenchedAverage_fixedScore path i hs hu F
  simpa [cavityDiagonal4_test, cavityDiagonalDeriv4_test, F, spinPairAt_test,
    scoreInternalEdge_test, initialReplicas, e4_01] using hder

lemma abs_cavityDiagonalDeriv4_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (u : ℝ) (target : ReplicaEdge 4) :
    |cavityDiagonalDeriv4_test (s := s) path i u target| ≤
      64 * β ^ 2 * cavityAbs4_test (s := s) path i u := by
  let P : ReplicaFun N 6 := fun σs =>
    spinPairAt_test i (scoreInternalEdge_test e4_01) σs *
      (spinPairAt_test i (scoreInternalEdge_test target) σs - q)
  have hterm (d : ReplicaEdge 6) :
      |lastSiteQuenchedAverage (s := s) path i u (fun σs =>
        P σs * cavityInteractionAt q i (σs d.1.1) (σs d.1.2))| ≤
        2 * cavityAbs4_test (s := s) path i u := by
    calc
      _ ≤ lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
          2 * |cavityOverlapAt q i σs d.1.1 d.1.2|) := by
        apply abs_lastSiteAverage_le_test
        intro σs
        rw [abs_mul, abs_cavityInteractionAt_replicas_eq_test]
        have hP : |P σs| ≤ 2 := by
          dsimp [P]
          rw [abs_mul, abs_spinPairAt_test, one_mul]
          exact abs_centeredSpinPair_le_two_test hqI i
            (scoreInternalEdge_test target) σs
        nlinarith [abs_nonneg (cavityOverlapAt q i σs d.1.1 d.1.2)]
      _ = 2 * lastSiteQuenchedAverage (s := s) path i u (fun σs : Replicas N 6 =>
          |cavityOverlapAt q i σs d.1.1 d.1.2|) := by
        rw [lastSiteQuenchedAverage_const_mul_test]
      _ = 2 * cavityAbs4_test (s := s) path i u := by
        rw [lastSite_abs_edge_eq_test, canonicalAbs6_eq_test]
  have hscore := normalizedScore_average_bound_test path i P
    (mul_nonneg (by norm_num) (by
      unfold cavityAbs4_test lastSiteQuenchedAverage quenchedReplicaAverage
      apply integral_nonneg
      intro ω
      apply replicaGibbsAverage_nonneg
      intro σs
      exact abs_nonneg _)) hterm
  have hcard : Fintype.card (ReplicaEdge 4) = 6 := by decide
  norm_num [hcard] at hscore ⊢
  unfold cavityDiagonalDeriv4_test
  change |s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u
      (fun σs => P σs * normalizedCavityScoreObservable (n := 4) q i σs)| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg (sq_nonneg β)]
  calc
    s * β ^ 2 * _ ≤ 1 * β ^ 2 * (32 * (2 * cavityAbs4_test (s := s) path i u)) := by
      gcongr
      exact hs.2
    _ = _ := by ring

lemma cavityDiagonal4_zero_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (target : ReplicaEdge 4) :
    cavityDiagonal4_test (s := s) path i 0 target =
      decoupledSpinCoefficient q (rsR β h)
        (edgeRelation (scoreInternalEdge_test target) ee01) := by
  let t6 : ReplicaEdge 6 := scoreInternalEdge_test target
  let F : (Fin 6 → SiteBaseConfig N i) → ℝ := fun _ => 1
  have hfac := lastSite_zero_centered_edge_factor_test (s := s) path hN hh hq i F t6 ee01
  have hone : lastSiteQuenchedAverage (s := s) path i 0
      (fun σs : Replicas N 6 => F (replicasSplitSiteEquiv i σs).1) = 1 := by
    simpa [F] using lastSiteQuenchedAverage_one_test (n := 6) (s := s) path i 0
  rw [hone, mul_one] at hfac
  unfold cavityDiagonal4_test
  rw [← lastSiteAverage_initialReplicas_test (n := 4) (s := s) path i 0]
  rw [show (fun σs : Replicas N 6 =>
      (fun τs : Replicas N 4 => spinPairAt_test i e4_01 τs *
        (spinPairAt_test i target τs - q)) (initialReplicas σs)) =
      fun σs => F (replicasSplitSiteEquiv i σs).1 *
        ((edgeSpin6 i t6 σs - q) * edgeSpin6 i ee01 σs) by
    funext σs
    dsimp [F, spinPairAt_test, edgeSpin6, t6, scoreInternalEdge_test,
      initialReplicas, e4_01, ee01]
    ring]
  exact hfac

lemma cavityDiagonal4_endpoint_error_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (target : ReplicaEdge 4) :
    (1 / (N : ℝ)) * |cavityDiagonal4_test (s := s) path i 1 target -
      cavityDiagonal4_test (s := s) path i 0 target| ≤
      64 * β ^ 2 * ((Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)) +
          2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) := by
  let E : ℝ → ℝ := fun u => cavityDiagonal4_test (s := s) path i u target
  let E' : ℝ → ℝ := fun u => cavityDiagonalDeriv4_test (s := s) path i u target
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope E E' (by norm_num)
    ((continuous_lastSiteQuenchedAverage path i
      (fun σs : Replicas N 4 => spinPairAt_test i e4_01 σs *
        (spinPairAt_test i target σs - q))).continuousOn)
    (fun u hu => hasDerivAt_cavityDiagonal4_test path hs hu i target)
  have hd := abs_cavityDiagonalDeriv4_le_test path hqI hs i c target
  have habs : |E 1 - E 0| ≤ 64 * β ^ 2 * cavityAbs4_test (s := s) path i c := by
    change |E' c| ≤ _ at hd
    have hslope' : E' c = E 1 - E 0 := by simpa using hslope
    rw [hslope'] at hd
    exact hd
  have hNr : 0 ≤ 1 / (N : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left habs hNr
  have hyoung := cavityAbs4_div_N_le_test (s := s) path hN i c
  have hcube := cavityCube4_uniform_test path hN hqI hs ⟨hc.1.le, hc.2.le⟩ i
  change (1 / (N : ℝ)) * |E 1 - E 0| ≤ _
  calc
    (1 / (N : ℝ)) * |E 1 - E 0| ≤
        (1 / (N : ℝ)) * (64 * β ^ 2 * cavityAbs4_test (s := s) path i c) := hscaled
    _ = 64 * β ^ 2 * (cavityAbs4_test (s := s) path i c / (N : ℝ)) := by ring
    _ ≤ 64 * β ^ 2 * ((cavityCube4 (s := s) path i c +
        2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) := by gcongr
    _ ≤ 64 * β ^ 2 * ((Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)) +
          2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) := by gcongr

noncomputable def fullCenteredMoment4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (e f : ReplicaEdge 4) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s) (fun σs =>
    centeredOverlap q σs e.1.1 e.1.2 * centeredOverlap q σs f.1.1 f.1.2)

lemma lastSite_one_centered_cube_edge_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (e : ReplicaEdge 4) :
    lastSiteQuenchedAverage (s := s) path i 1 (fun σs =>
      |centeredOverlap q σs e.1.1 e.1.2| ^ 3) = thirdMoment path s := by
  let F : ReplicaFun N 4 := fun σs => |centeredOverlap q σs 0 1| ^ 3
  have hr := quenchedReplicaAverage_relabel (fullPathHamiltonian path s) F (pairPerm_test e)
  have hp : (fun σs => F (replicaRelabelEquiv (pairPerm_test e) σs)) =
      fun σs => |centeredOverlap q σs e.1.1 e.1.2| ^ 3 := by
    funext σs
    dsimp only [F, replicaRelabelEquiv]
    change |centeredOverlap q σs (pairPerm_test e 0) (pairPerm_test e 1)| ^ 3 = _
    rw [pairPerm_zero_test, pairPerm_one_test]
  rw [hp] at hr
  unfold thirdMoment
  rw [show lastSiteQuenchedAverage (s := s) path i 1 =
      quenchedReplicaAverage (fullPathHamiltonian path s) by
    funext G
    unfold lastSiteQuenchedAverage
    congr 1
    funext ω
    rw [lastSiteHamiltonian_one]]
  exact hr

lemma lastSite_one_centered_abs_div_N_le_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (i : Fin N) (e : ReplicaEdge 4) :
    (1 / (N : ℝ)) * lastSiteQuenchedAverage (s := s) path i 1 (fun σs =>
      |centeredOverlap q σs e.1.1 e.1.2|) ≤
      (thirdMoment path s + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3 := by
  have hmono := quenchedReplicaAverage_mono
    (lastSiteHamiltonian (s := s) path i 1) (measurable_lastSiteHamiltonian path i 1)
    (fun σs : Replicas N 4 => |centeredOverlap q σs e.1.1 e.1.2| / (N : ℝ))
    (fun σs => (|centeredOverlap q σs e.1.1 e.1.2| ^ 3 +
      2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3)
    (fun σs => young_abs_div_N_test hN (centeredOverlap q σs e.1.1 e.1.2))
  change lastSiteQuenchedAverage (s := s) path i 1
      (fun σs => |centeredOverlap q σs e.1.1 e.1.2| / (N : ℝ)) ≤ _ at hmono
  let L := lastSiteAverageLinearMap_test (n := 4) (s := s) path i 1
  change L _ ≤ L _ at hmono
  rw [show (fun σs : Replicas N 4 => |centeredOverlap q σs e.1.1 e.1.2| / (N : ℝ)) =
      (1 / (N : ℝ)) • (fun σs => |centeredOverlap q σs e.1.1 e.1.2|) by
      funext σs; simp [smul_eq_mul]; ring] at hmono
  rw [show (fun σs : Replicas N 4 =>
      (|centeredOverlap q σs e.1.1 e.1.2| ^ 3 +
        2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) =
      (1 / 3 : ℝ) • ((fun σs => |centeredOverlap q σs e.1.1 e.1.2| ^ 3) +
        fun _ => 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) by
      funext σs; simp [smul_eq_mul]; ring] at hmono
  simp only [map_smul, map_add, L, lastSiteAverageLinearMap_apply_test, smul_eq_mul] at hmono
  rw [lastSite_one_centered_cube_edge_test path i e] at hmono
  rw [show (fun _ : Replicas N 4 => 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) =
      fun σs => (2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) * (1 : ℝ) by
      funext σs; ring,
    lastSiteQuenchedAverage_const_mul_test, lastSiteQuenchedAverage_one_test] at hmono
  convert hmono using 1 <;> ring

lemma cavityQuadratic4_one_full_error_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (i : Fin N) (e f : ReplicaEdge 4) :
    |cavityQuadratic4_test (s := s) path i 1 e f - fullCenteredMoment4_test (s := s) path e f| ≤
      thirdMoment path s + 3 * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
  let invN : ℝ := 1 / (N : ℝ)
  let δ : ReplicaEdge 4 → ReplicaFun N 4 := fun a σs =>
    invN * spinPairAt_test i a σs
  let Q : ReplicaEdge 4 → ReplicaFun N 4 := fun a σs =>
    centeredOverlap q σs a.1.1 a.1.2
  have hδabs (a : ReplicaEdge 4) (σs : Replicas N 4) : |δ a σs| = invN := by
    dsimp [δ, invN]
    rw [abs_mul, abs_spinPairAt_test, mul_one, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
  have hpoint (σs : Replicas N 4) :
      |cavityOverlapAt q i σs e.1.1 e.1.2 * cavityOverlapAt q i σs f.1.1 f.1.2 -
        Q e σs * Q f σs| ≤
      invN * |Q e σs| + invN * |Q f σs| + invN ^ 2 := by
    have he : cavityOverlapAt q i σs e.1.1 e.1.2 = Q e σs - δ e σs := by
      unfold cavityOverlapAt
      dsimp [Q, δ, invN, spinPairAt_test]
      ring
    have hf : cavityOverlapAt q i σs f.1.1 f.1.2 = Q f σs - δ f σs := by
      unfold cavityOverlapAt
      dsimp [Q, δ, invN, spinPairAt_test]
      ring
    rw [he, hf]
    have ht := abs_add_three (-(Q e σs * δ f σs))
      (-(Q f σs * δ e σs)) (δ e σs * δ f σs)
    rw [abs_neg, abs_neg, abs_mul (Q e σs), hδabs f,
      abs_mul (Q f σs), hδabs e, abs_mul (δ e σs), hδabs e, hδabs f] at ht
    rw [show (Q e σs - δ e σs) * (Q f σs - δ f σs) -
        Q e σs * Q f σs =
        -(Q e σs * δ f σs) + -(Q f σs * δ e σs) +
          δ e σs * δ f σs by ring]
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using ht
  have hmeas := measurable_lastSiteHamiltonian (s := s) path i 1
  have havg := abs_quenchedReplicaAverage_le_abs_average
    (lastSiteHamiltonian (s := s) path i 1) hmeas
    (fun σs : Replicas N 4 => cavityOverlapAt q i σs e.1.1 e.1.2 *
      cavityOverlapAt q i σs f.1.1 f.1.2 - Q e σs * Q f σs)
  have hmono := quenchedReplicaAverage_mono
    (lastSiteHamiltonian (s := s) path i 1) hmeas _ _ hpoint
  have heY := lastSite_one_centered_abs_div_N_le_test (s := s) path hN i e
  have hfY := lastSite_one_centered_abs_div_N_le_test (s := s) path hN i f
  have hinv2 := inv_pow_two_le_rpow_test hN
  calc
    _ = |lastSiteQuenchedAverage (s := s) path i 1 (fun σs =>
        cavityOverlapAt q i σs e.1.1 e.1.2 * cavityOverlapAt q i σs f.1.1 f.1.2 -
          Q e σs * Q f σs)| := by
      unfold cavityQuadratic4_test
      rw [show fullCenteredMoment4_test (s := s) path e f =
          lastSiteQuenchedAverage (s := s) path i 1 (fun σs => Q e σs * Q f σs) by
        unfold fullCenteredMoment4_test lastSiteQuenchedAverage
        congr 1
        funext ω
        rw [lastSiteHamiltonian_one]]
      rw [lastSiteQuenchedAverage_sub_test]
    _ ≤ lastSiteQuenchedAverage (s := s) path i 1 (fun σs =>
        invN * |Q e σs| + invN * |Q f σs| + invN ^ 2) := havg.trans hmono
    _ = invN * lastSiteQuenchedAverage (s := s) path i 1 (fun σs => |Q e σs|) +
        invN * lastSiteQuenchedAverage (s := s) path i 1 (fun σs => |Q f σs|) + invN ^ 2 := by
      let L := lastSiteAverageLinearMap_test (n := 4) (s := s) path i 1
      change L _ = _
      rw [show (fun σs => invN * |Q e σs| + invN * |Q f σs| + invN ^ 2) =
          invN • (fun σs => |Q e σs|) + invN • (fun σs => |Q f σs|) +
            (invN ^ 2) • (fun _ => (1 : ℝ)) by
        funext σs; simp [smul_eq_mul]]
      simp only [map_add, map_smul, L, lastSiteAverageLinearMap_apply_test, smul_eq_mul,
        lastSiteQuenchedAverage_one_test, mul_one]
    _ ≤ (thirdMoment path s + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3 +
        (thirdMoment path s + 2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3 +
        (N : ℝ) ^ (-(3 : ℝ) / 2) := by
      dsimp [invN]
      gcongr
    _ ≤ thirdMoment path s + 3 * (N : ℝ) ^ (-(3 : ℝ) / 2) := by
      have ht0 : 0 ≤ thirdMoment path s := by
        unfold thirdMoment quenchedReplicaAverage
        apply integral_nonneg
        intro ω
        apply replicaGibbsAverage_nonneg
        intro σs
        positivity
      have hn0 : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
      linarith

noncomputable def cavityMinusVectorAt_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) : Fin 3 → ℝ :=
  ![cavityQuadratic4_test (s := s) path i 0 e4_01 e4_01,
    cavityQuadratic4_test (s := s) path i 0 e4_01 e4_02,
    cavityQuadratic4_test (s := s) path i 0 e4_01 e4_23]

def targetEdge4_test : Fin 3 → ReplicaEdge 4 := ![e4_01, e4_02, e4_23]

lemma scoreInternal_e4_01_test : scoreInternalEdge_test e4_01 = ee01 := by rfl
lemma scoreInternal_e4_02_test : scoreInternalEdge_test e4_02 = ee02 := by rfl
lemma scoreInternal_e4_23_test : scoreInternalEdge_test e4_23 = ee23 := by rfl

lemma cavityMoment6_internal_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (e f : ReplicaEdge 4) :
    cavityMoment6 (s := s) path i u (scoreInternalEdge_test e) (scoreInternalEdge_test f) =
      cavityQuadratic4_test (s := s) path i u e f := by
  unfold cavityMoment6 cavityQuadratic4_test
  let F : ReplicaFun N 4 := fun σs => cavityOverlapAt q i σs e.1.1 e.1.2 *
    cavityOverlapAt q i σs f.1.1 f.1.2
  rw [show (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs (scoreInternalEdge_test e).1.1
        (scoreInternalEdge_test e).1.2 *
      cavityOverlapAt q i σs (scoreInternalEdge_test f).1.1
        (scoreInternalEdge_test f).1.2) = fun σs => F (initialReplicas σs) by
    funext σs
    rfl]
  exact lastSiteAverage_initialReplicas_test path i u F

lemma beta_sq_abstractRow_eq_matrix_test (β q r A B C : ℝ) (k : Fin 3) :
    β ^ 2 * abstractRow q r A B C (scoreInternalEdge_test (targetEdge4_test k)) =
      (cavityMatrix β q r).mulVec ![A, B, C] k := by
  fin_cases k
  · norm_num [targetEdge4_test, scoreInternal_e4_01_test, abstractRow, abstractTerm,
      momentCoeff, ee01, ee02, ee03, ee12, ee13, ee23, ee04, ee14, ee24,
      ee34, ee45, edgeRelation, decoupledSpinCoefficient, cavityMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    try simp (disch := decide)
    ring
  · norm_num [targetEdge4_test, scoreInternal_e4_02_test, abstractRow, abstractTerm,
      momentCoeff, ee01, ee02, ee03, ee12, ee13, ee23, ee04, ee14, ee24,
      ee34, ee45, edgeRelation, decoupledSpinCoefficient, cavityMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    try simp (disch := decide)
    ring
  · norm_num [targetEdge4_test, scoreInternal_e4_23_test, abstractRow, abstractTerm,
      momentCoeff, ee01, ee02, ee03, ee12, ee13, ee23, ee04, ee14, ee24,
      ee34, ee45, edgeRelation, decoupledSpinCoefficient, cavityMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    try simp (disch := decide)
    ring

lemma cavityOffdiagDeriv4_zero_eq_matrix_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N) (k : Fin 3) :
    cavityOffdiagDeriv4_test (s := s) path i 0 (targetEdge4_test k) =
      s * (cavityMatrix β q (rsR β h)).mulVec (cavityMinusVectorAt_test (s := s) path i) k := by
  have hend := endpoint_fullScore_test (s := s) path hN hh hq i
    (scoreInternalEdge_test (targetEdge4_test k))
  unfold cavityOffdiagDeriv4_test
  rw [show lastSiteQuenchedAverage (s := s) path i 0 (fun σs : Replicas N 6 =>
      cavityOverlapAt q i σs 0 1 *
        (spinPairAt_test i (scoreInternalEdge_test (targetEdge4_test k)) σs - q) *
        normalizedCavityScoreObservable (n := 4) q i σs) =
      abstractRow q (rsR β h)
        (cavityMoment6 (s := s) path i 0 ee01 ee01)
        (cavityMoment6 (s := s) path i 0 ee01 ee02)
        (cavityMoment6 (s := s) path i 0 ee01 ee23)
        (scoreInternalEdge_test (targetEdge4_test k)) by
    simpa [scoreTermObs6, spinPairAt_test, edgeSpin6] using hend]
  rw [← scoreInternal_e4_01_test, ← scoreInternal_e4_02_test,
    ← scoreInternal_e4_23_test,
    cavityMoment6_internal_eq_test, cavityMoment6_internal_eq_test,
    cavityMoment6_internal_eq_test]
  unfold cavityMinusVectorAt_test
  calc
    s * β ^ 2 * abstractRow q (rsR β h)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_01)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_02)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_23)
        (scoreInternalEdge_test (targetEdge4_test k)) =
      s * (β ^ 2 * abstractRow q (rsR β h)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_01)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_02)
        (cavityQuadratic4_test (s := s) path i 0 e4_01 e4_23)
        (scoreInternalEdge_test (targetEdge4_test k))) := by ring
    _ = _ := by rw [beta_sq_abstractRow_eq_matrix_test]

lemma cavityDiagonal4_zero_eq_theta_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N) (k : Fin 3) :
    cavityDiagonal4_test (s := s) path i 0 (targetEdge4_test k) =
      theta q (rsR β h) k := by
  rw [cavityDiagonal4_zero_test path hN hh hq]
  fin_cases k <;>
    norm_num [targetEdge4_test, scoreInternal_e4_01_test, scoreInternal_e4_02_test,
      scoreInternal_e4_23_test, ee01, ee02, ee23, edgeRelation,
      decoupledSpinCoefficient, theta] <;>
    try simp (disch := decide)

lemma fullCenteredMoment4_target_eq_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (k : Fin 3) :
    fullCenteredMoment4_test (s := s) path e4_01 (targetEdge4_test k) = cavityVector path s k := by
  fin_cases k
  · unfold fullCenteredMoment4_test targetEdge4_test cavityVector A
    congr 1
    funext σs
    simp [e4_01]
    ring
  · rfl
  · rfl

noncomputable def siteMixed4_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (target : ReplicaEdge 4) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s) (fun σs =>
    centeredOverlap q σs 0 1 * (spinPairAt_test i target σs - q))

lemma siteMixed4_decompose_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (target : ReplicaEdge 4) :
    siteMixed4_test (s := s) path i target =
      cavityOffdiag4_test (s := s) path i 1 target +
        (1 / (N : ℝ)) * cavityDiagonal4_test (s := s) path i 1 target := by
  unfold siteMixed4_test
  rw [show quenchedReplicaAverage (fullPathHamiltonian path s)
      (fun σs : Replicas N 4 => centeredOverlap q σs 0 1 *
        (spinPairAt_test i target σs - q)) =
      lastSiteQuenchedAverage (s := s) path i 1 (fun σs : Replicas N 4 =>
        centeredOverlap q σs 0 1 * (spinPairAt_test i target σs - q)) by
    unfold lastSiteQuenchedAverage
    congr 1
    funext ω
    rw [lastSiteHamiltonian_one]]
  rw [show (fun σs : Replicas N 4 => centeredOverlap q σs 0 1 *
      (spinPairAt_test i target σs - q)) =
      (fun σs => cavityOverlapAt q i σs 0 1 *
        (spinPairAt_test i target σs - q)) +
      (1 / (N : ℝ)) • (fun σs => spinPairAt_test i e4_01 σs *
        (spinPairAt_test i target σs - q)) by
    funext σs
    rw [centeredOverlap_eq_cavityOverlapAt_add q i σs 0 1]
    simp [smul_eq_mul, spinPairAt_test, e4_01]
    ring]
  change lastSiteAverageLinearMap_test (s := s) path i 1 _ = _
  simp only [map_add, map_smul, lastSiteAverageLinearMap_apply_test, smul_eq_mul,
    cavityOffdiag4_test, cavityDiagonal4_test]

lemma centeredOverlap_eq_site_sum_test {N n : ℕ} (hN : 0 < N) (q : ℝ)
    (σs : Replicas N n) (a b : Fin n) :
    centeredOverlap q σs a b = (1 / (N : ℝ)) * ∑ i : Fin N,
      (SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i - q) := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  unfold centeredOverlap replicaOverlap SpinGlass.overlap
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hNr]

lemma quenchedReplicaAverage_sum_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (hH : Measurable H)
    {m : ℕ} (F : Fin m → ReplicaFun N n) :
    quenchedReplicaAverage H (fun σs => ∑ i, F i σs) =
      ∑ i, quenchedReplicaAverage H (F i) := by
  unfold quenchedReplicaAverage
  rw [show (fun ω => replicaGibbsAverage (H ω) (fun σs => ∑ i, F i σs)) =
      fun ω => ∑ i, replicaGibbsAverage (H ω) (F i) by
    funext ω
    unfold replicaGibbsAverage
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]]
  rw [integral_finset_sum]
  intro i hi
  exact integrable_replicaGibbsAverage_comp H hH (F i)

lemma cavityVector_eq_siteAverage_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (k : Fin 3) :
    cavityVector path s k = (1 / (N : ℝ)) * ∑ i : Fin N,
      siteMixed4_test (s := s) path i (targetEdge4_test k) := by
  let i0 : Fin N := ⟨0, hN⟩
  have hmeas : Measurable (fullPathHamiltonian path s) := by
    rw [← show lastSiteHamiltonian (s := s) path i0 1 = fullPathHamiltonian path s by
      funext ω; rw [lastSiteHamiltonian_one]]
    exact measurable_lastSiteHamiltonian path i0 1
  rw [← fullCenteredMoment4_target_eq_test path k]
  unfold fullCenteredMoment4_test siteMixed4_test
  rw [show (fun σs : Replicas N 4 =>
      centeredOverlap q σs e4_01.1.1 e4_01.1.2 *
        centeredOverlap q σs (targetEdge4_test k).1.1 (targetEdge4_test k).1.2) =
      (1 / (N : ℝ)) • (fun σs => ∑ i : Fin N,
        centeredOverlap q σs 0 1 *
          (spinPairAt_test i (targetEdge4_test k) σs - q)) by
    funext σs
    rw [centeredOverlap_eq_site_sum_test hN q σs
      (targetEdge4_test k).1.1 (targetEdge4_test k).1.2]
    simp only [Pi.smul_apply, smul_eq_mul, e4_01, spinPairAt_test]
    rw [Finset.mul_sum, Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [show ((1 / (N : ℝ)) • (fun σs : Replicas N 4 => ∑ i : Fin N,
      centeredOverlap q σs 0 1 *
        (spinPairAt_test i (targetEdge4_test k) σs - q))) =
      fun σs => (1 / (N : ℝ)) * (∑ i : Fin N,
        centeredOverlap q σs 0 1 *
          (spinPairAt_test i (targetEdge4_test k) σs - q)) by rfl,
    quenchedReplicaAverage_const_mul]
  rw [quenchedReplicaAverage_sum_test (fullPathHamiltonian path s) hmeas]

lemma abs_cavityMatrix_entry_le_test (β q r : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 3) : |cavityMatrix β q r i j| ≤ 20 * β ^ 2 := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2le : q ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
  have hqq : 0 ≤ q - q ^ 2 := by
    nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
  have hA0 : |1 - q ^ 2| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hA1 : |q - q ^ 2| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hA2 : |r - q ^ 2| ≤ 1 := abs_le.mpr ⟨by nlinarith [hr.1], by nlinarith [hr.2]⟩
  have hb0 : |β ^ 2 * (1 - q ^ 2)| ≤ β ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    simpa using mul_le_mul_of_nonneg_left hA0 (sq_nonneg β)
  have hb1 : |β ^ 2 * (q - q ^ 2)| ≤ β ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    simpa using mul_le_mul_of_nonneg_left hA1 (sq_nonneg β)
  have hb2 : |β ^ 2 * (r - q ^ 2)| ≤ β ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    simpa using mul_le_mul_of_nonneg_left hA2 (sq_nonneg β)
  have hb0' := abs_le.mp hb0
  have hb1' := abs_le.mp hb1
  have hb2' := abs_le.mp hb2
  fin_cases i <;> fin_cases j <;>
    norm_num [cavityMatrix]
  all_goals first
    | nlinarith [hb0, hb1, hb2, sq_nonneg β]
    | (rw [abs_le]; constructor <;> linarith [hb0'.1, hb0'.2, hb1'.1, hb1'.2,
        hb2'.1, hb2'.2, sq_nonneg β])

lemma abs_cavityMatrix_mulVec_le_test (β q r R : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hR : 0 ≤ R) (x : Fin 3 → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Fin 3) :
    |(cavityMatrix β q r).mulVec x i| ≤ 60 * β ^ 2 * R := by
  unfold Matrix.mulVec dotProduct
  calc
    |∑ j, cavityMatrix β q r i j * x j| ≤
        ∑ j, |cavityMatrix β q r i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (20 * β ^ 2) * R := by
      gcongr with j
      rw [abs_mul]
      exact mul_le_mul (abs_cavityMatrix_entry_le_test β q r hq hr i j) (hx j)
        (abs_nonneg _) (by positivity)
    _ = 60 * β ^ 2 * R := by simp [nsmul_eq_mul]; ring

lemma cavityMinusVectorAt_error_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (k : Fin 3) :
    |cavityMinusVectorAt_test (s := s) path i k - cavityVector path s k| ≤
      (128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) *
        (thirdMoment path s + (N : ℝ) ^ (-(3 : ℝ) / 2)) := by
  have hinterp := abs_cavityQuadratic4_one_sub_zero_le_test path hN hqI hs i
    e4_01 (targetEdge4_test k)
  have hfull := cavityQuadratic4_one_full_error_test (s := s) path hN i e4_01 (targetEdge4_test k)
  have hinv3 := inv_pow_three_le_rpow_test hN
  have htri := abs_sub_le
    (cavityQuadratic4_test (s := s) path i 0 e4_01 (targetEdge4_test k))
    (cavityQuadratic4_test (s := s) path i 1 e4_01 (targetEdge4_test k))
    (fullCenteredMoment4_test (s := s) path e4_01 (targetEdge4_test k))
  rw [abs_sub_comm] at hinterp
  have hsum := htri.trans (add_le_add hinterp hfull)
  rw [fullCenteredMoment4_target_eq_test] at hsum
  change |cavityMinusVectorAt_test (s := s) path i k - cavityVector path s k| ≤ _
  rw [show cavityMinusVectorAt_test (s := s) path i k =
      cavityQuadratic4_test (s := s) path i 0 e4_01 (targetEdge4_test k) by
    fin_cases k <;> rfl]
  calc
    _ ≤ 32 * β ^ 2 * (Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3))) +
        (thirdMoment path s + 3 * (N : ℝ) ^ (-(3 : ℝ) / 2)) := hsum
    _ ≤ 32 * β ^ 2 * (Real.exp (64 * β ^ 2) *
        (4 * (thirdMoment path s + (N : ℝ) ^ (-(3 : ℝ) / 2)))) +
        (thirdMoment path s + 3 * (N : ℝ) ^ (-(3 : ℝ) / 2)) := by
      gcongr
    _ ≤ _ := by
      have ht : 0 ≤ thirdMoment path s := by
        unfold thirdMoment quenchedReplicaAverage
        apply integral_nonneg
        intro ω
        apply replicaGibbsAverage_nonneg
        intro σs
        positivity
      ring_nf
      nlinarith

lemma localCavityCoordinate_error_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hrI : rsR β h ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) (k : Fin 3) :
    |siteMixed4_test (s := s) path i (targetEdge4_test k) -
        s * (cavityMatrix β q (rsR β h)).mulVec (cavityVector path s) k -
        (1 / (N : ℝ)) * theta q (rsR β h) k| ≤
      30000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) *
        (thirdMoment path s + (N : ℝ) ^ (-(3 : ℝ) / 2)) := by
  let eta : ℝ := thirdMoment path s + (N : ℝ) ^ (-(3 : ℝ) / 2)
  let x : Fin 3 → ℝ := cavityMinusVectorAt_test (s := s) path i - cavityVector path s
  have heta0 : 0 ≤ eta := by
    have ht : 0 ≤ thirdMoment path s := by
      unfold thirdMoment quenchedReplicaAverage
      apply integral_nonneg
      intro ω
      apply replicaGibbsAverage_nonneg
      intro σs
      positivity
    exact add_nonneg ht (Real.rpow_nonneg (by positivity) _)
  have hT := cavityOffdiag4_taylor_test path hN hqI hs hh hq i (targetEdge4_test k)
  have hinv3 := inv_pow_three_le_rpow_test hN
  have hT' : |cavityOffdiag4_test (s := s) path i 1 (targetEdge4_test k) -
      cavityOffdiagDeriv4_test (s := s) path i 0 (targetEdge4_test k)| ≤
      18432 * β ^ 4 * Real.exp (64 * β ^ 2) * eta := by
    calc
      _ ≤ 4608 * β ^ 4 * (Real.exp (64 * β ^ 2) *
          (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3))) := hT
      _ ≤ 4608 * β ^ 4 * (Real.exp (64 * β ^ 2) * (4 * eta)) := by
        gcongr
        dsimp [eta]
        linarith
      _ = _ := by ring
  have hx (j : Fin 3) : |x j| ≤
      (128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta := by
    exact cavityMinusVectorAt_error_test path hN hqI hs i j
  have hR0 : 0 ≤ (128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta := by positivity
  have hMx := abs_cavityMatrix_mulVec_le_test β q (rsR β h)
    ((128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta)
    hqI hrI hR0 x hx k
  have hMx' : |s * (cavityMatrix β q (rsR β h)).mulVec x k| ≤
      60 * β ^ 2 * ((128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta) := by
    rw [abs_mul, abs_of_nonneg hs.1]
    calc
      s * _ ≤ 1 * (60 * β ^ 2 *
          ((128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta)) := by
        gcongr
        exact hs.2
      _ = _ := one_mul _
  have hD := cavityDiagonal4_endpoint_error_test path hN hqI hs i (targetEdge4_test k)
  have hD' : (1 / (N : ℝ)) *
      |cavityDiagonal4_test (s := s) path i 1 (targetEdge4_test k) -
        cavityDiagonal4_test (s := s) path i 0 (targetEdge4_test k)| ≤
      64 * β ^ 2 * ((4 * Real.exp (64 * β ^ 2) + 2) / 3 * eta) := by
    calc
      _ ≤ 64 * β ^ 2 * ((Real.exp (64 * β ^ 2) *
          (4 * (thirdMoment path s + (1 / (N : ℝ)) ^ 3)) +
            2 * (N : ℝ) ^ (-(3 : ℝ) / 2)) / 3) := hD
      _ ≤ 64 * β ^ 2 * ((4 * Real.exp (64 * β ^ 2) + 2) / 3 * eta) := by
        gcongr
        dsimp [eta]
        have hp := mul_le_mul_of_nonneg_left hinv3 (Real.exp_pos (64 * β ^ 2)).le
        have ht : 0 ≤ thirdMoment path s := by
          unfold thirdMoment quenchedReplicaAverage
          apply integral_nonneg
          intro ω
          apply replicaGibbsAverage_nonneg
          intro σs
          positivity
        nlinarith
  have hid : siteMixed4_test (s := s) path i (targetEdge4_test k) -
        s * (cavityMatrix β q (rsR β h)).mulVec (cavityVector path s) k -
        (1 / (N : ℝ)) * theta q (rsR β h) k =
      (cavityOffdiag4_test (s := s) path i 1 (targetEdge4_test k) -
        cavityOffdiagDeriv4_test (s := s) path i 0 (targetEdge4_test k)) +
      s * (cavityMatrix β q (rsR β h)).mulVec x k +
      (1 / (N : ℝ)) *
        (cavityDiagonal4_test (s := s) path i 1 (targetEdge4_test k) -
          cavityDiagonal4_test (s := s) path i 0 (targetEdge4_test k)) := by
    rw [siteMixed4_decompose_test,
      cavityOffdiagDeriv4_zero_eq_matrix_test path hN hh hq,
      cavityDiagonal4_zero_eq_theta_test path hN hh hq]
    dsimp [x]
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  rw [hid]
  have htri := abs_add_three
    (cavityOffdiag4_test (s := s) path i 1 (targetEdge4_test k) -
      cavityOffdiagDeriv4_test (s := s) path i 0 (targetEdge4_test k))
    (s * (cavityMatrix β q (rsR β h)).mulVec x k)
    ((1 / (N : ℝ)) *
      (cavityDiagonal4_test (s := s) path i 1 (targetEdge4_test k) -
        cavityDiagonal4_test (s := s) path i 0 (targetEdge4_test k)))
  have hNinv : 0 ≤ 1 / (N : ℝ) := by positivity
  rw [abs_mul (1 / (N : ℝ)), abs_of_nonneg hNinv] at htri
  have hsum := htri.trans (add_le_add (add_le_add hT' hMx') hD')
  calc
    _ ≤ 18432 * β ^ 4 * Real.exp (64 * β ^ 2) * eta +
        60 * β ^ 2 * ((128 * β ^ 2 * Real.exp (64 * β ^ 2) + 3) * eta) +
        64 * β ^ 2 * ((4 * Real.exp (64 * β ^ 2) + 2) / 3 * eta) := hsum
    _ ≤ 30000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) * eta := by
      let E := Real.exp (64 * β ^ 2)
      have hE : 1 ≤ E := Real.one_le_exp (by positivity)
      have hz : β ^ 2 ≤ 1 + β ^ 4 := by nlinarith [sq_nonneg (β ^ 2 - 1)]
      have hzE : β ^ 2 * E ≤ (1 + β ^ 4) * E := by gcongr
      have hz2E : β ^ 4 * E ≤ (1 + β ^ 4) * E := by
        gcongr
        linarith
      have hprod : 0 ≤ (1 + β ^ 4) * (E - 1) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hE)
      have hz0E : β ^ 2 ≤ (1 + β ^ 4) * E := hz.trans (by nlinarith)
      dsimp [E] at *
      nlinarith

lemma cavityRemainder_eq_siteAverage_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (k : Fin 3) :
    cavityRemainder path s k = (1 / (N : ℝ)) * ∑ i : Fin N,
      (siteMixed4_test (s := s) path i (targetEdge4_test k) -
        s * (cavityMatrix β q (rsR β h)).mulVec (cavityVector path s) k -
        (1 / (N : ℝ)) * theta q (rsR β h) k) := by
  have hvec := cavityVector_eq_siteAverage_test (s := s) path hN k
  have hNr : (N : ℝ) ≠ 0 := by positivity
  unfold cavityRemainder
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hvec, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hNr]

lemma cavityRemainder_coordinate_bound_test
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hrI : rsR β h ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (k : Fin 3) :
    |cavityRemainder path s k| ≤
      30000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) * cavityErrorScale path s := by
  let R : ℝ := 30000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) *
    (thirdMoment path s + (N : ℝ) ^ (-(3 : ℝ) / 2))
  let loc : Fin N → ℝ := fun i =>
    siteMixed4_test (s := s) path i (targetEdge4_test k) -
      s * (cavityMatrix β q (rsR β h)).mulVec (cavityVector path s) k -
      (1 / (N : ℝ)) * theta q (rsR β h) k
  have hlocal (i : Fin N) : |loc i| ≤ R :=
    localCavityCoordinate_error_test path hN hh hq hqI hrI hs i k
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have ht : 0 ≤ thirdMoment path s := by
      unfold thirdMoment quenchedReplicaAverage
      apply integral_nonneg
      intro ω
      apply replicaGibbsAverage_nonneg
      intro σs
      positivity
    positivity
  rw [cavityRemainder_eq_siteAverage_test path hN]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
  calc
    (1 / (N : ℝ)) * |∑ i, loc i| ≤
        (1 / (N : ℝ)) * ∑ i, |loc i| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (N : ℝ)) * ∑ _i : Fin N, R := by
      gcongr with i
      exact hlocal i
    _ = R := by
      simp [nsmul_eq_mul]
      have hNr : (N : ℝ) ≠ 0 := by positivity
      field_simp [hNr]
    _ = _ := by dsimp [R, cavityErrorScale]; ring

lemma abs_cavityChangeMatrix_mulVec_le_test (R : ℝ) (hR : 0 ≤ R)
    (x : Fin 3 → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Fin 3) :
    |cavityChangeMatrix.mulVec x i| ≤ 12 * R := by
  unfold Matrix.mulVec dotProduct
  calc
    |∑ j, cavityChangeMatrix i j * x j| ≤
        ∑ j, |cavityChangeMatrix i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, 4 * R := by
      gcongr with j
      rw [abs_mul]
      have he : |cavityChangeMatrix i j| ≤ 4 := by
        fin_cases i <;> fin_cases j <;> norm_num [cavityChangeMatrix]
      exact mul_le_mul he (hx j) (abs_nonneg _) (by norm_num)
    _ = 12 * R := by simp [nsmul_eq_mul]; ring

lemma cavityModeRemainder_norm_bound
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h)
    (hqI : q ∈ Set.Icc (0 : ℝ) 1) (hrI : rsR β h ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ ≤
      360000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) * cavityErrorScale path s := by
  let R : ℝ := 30000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) *
    cavityErrorScale path s
  have hcoord (k : Fin 3) : |cavityRemainder path s k| ≤ R :=
    cavityRemainder_coordinate_bound_test path hN hh hq hqI hrI hs k
  have hscale : 0 ≤ cavityErrorScale path s := by
    unfold cavityErrorScale
    have ht : 0 ≤ thirdMoment path s := by
      unfold thirdMoment quenchedReplicaAverage
      apply integral_nonneg
      intro ω
      apply replicaGibbsAverage_nonneg
      intro σs
      positivity
    positivity
  have hR0 : 0 ≤ R := by positivity
  have hnorm : ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ ≤ 12 * R := by
    rw [pi_norm_le_iff_of_nonneg (show 0 ≤ 12 * R by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_cavityChangeMatrix_mulVec_le_test R hR0 _ hcoord i
  calc
    ‖cavityChangeMatrix.mulVec (cavityRemainder path s)‖ ≤ 12 * R := hnorm
    _ = 360000 * (1 + β ^ 4) * Real.exp (64 * β ^ 2) *
        cavityErrorScale path s := by dsimp [R]; ring

end CavityEstimates
end SpinGlass.AT
