module

public import Targets.ParisiListRegularity

@[expose] public section

/-!
# Strict sorting of scalar Parisi cascades

For the genuine `log cosh` terminal, any inverted pair of positive-variance
operators makes sorting strictly increase the cascade. Zero-variance entries
remain in the list: the strict order assertion ignores them, and propagation
through a zero-variance outer operator uses its exact identity action.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Pointwise strict order propagates through a nonnegative-mass Gaussian
operator, including its zero-variance identity face. -/
theorem parisiStep_lt_of_forall_lt {A B : ℝ → ℝ} {m v : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ v) (hA : HasLinearGrowth A) (hB : HasLinearGrowth B)
    (hcA : Continuous A) (hcB : Continuous B) (hlt : ∀ z, A z < B z) (x : ℝ) :
    parisiStep m v A x < parisiStep m v B x := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0, parisiStep_zero_var, parisiStep_zero_var]
    exact hlt x
  · exact parisiStep_lt_of_continuous_le hm hvpos hA hB hcA hcB
      (fun z => (hlt z).le) (hlt 0) x

private theorem logcosh_growth : HasLinearGrowth (fun x => Real.log (Real.cosh x)) :=
  (scalarFieldCascade_props (fun _ => 0) (fun _ => 0) 0).2.1

private theorem logcosh_measurable : Measurable (fun x => Real.log (Real.cosh x)) :=
  (scalarFieldCascade_props (fun _ => 0) (fun _ => 0) 0).1

private theorem nonneg_of_admissible {l : List (ℝ × ℝ)}
    (hl : ∀ v ∈ l, v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2) :
    ∀ v ∈ l, 0 ≤ v.1 ∧ 0 ≤ v.2 := fun v hv => ⟨(hl v hv).1.1, (hl v hv).2⟩

/-- Inserting a positive-variance operator past a lower-mass positive-variance
entry gives a strict gain. Intermediate zero-variance entries are allowed. -/
theorem parisiListCascade_orderedInsert_lt (mv : ℝ × ℝ) (l : List (ℝ × ℝ))
    (hmv : mv.1 ∈ Set.Icc 0 1 ∧ 0 ≤ mv.2)
    (hl : ∀ v ∈ l, v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2)
    (hs : l.Pairwise (fun p q => p.1 ≤ q.1)) (hmvp : 0 < mv.2)
    (hw : ∃ v ∈ l, 0 < v.2 ∧ v.1 < mv.1) (x : ℝ) :
    parisiListCascade (mv :: l) (fun x => Real.log (Real.cosh x)) x <
      parisiListCascade (l.orderedInsert (fun p q : ℝ × ℝ => p.1 ≤ q.1) mv)
        (fun x => Real.log (Real.cosh x)) x := by
  classical
  induction l generalizing x with
  | nil => simp at hw
  | cons v l ih =>
    have hv := hl v List.mem_cons_self
    have hl' : ∀ w ∈ l, w.1 ∈ Set.Icc 0 1 ∧ 0 ≤ w.2 :=
      fun w hw => hl w (List.mem_cons_of_mem v hw)
    have hs' := (List.pairwise_cons.mp hs).2
    have hvm : v.1 < mv.1 := by
      obtain ⟨w, hw, _, hwm⟩ := hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hwm
      · exact ((List.pairwise_cons.mp hs).1 w hw).trans_lt hwm
    have hins : ∀ w ∈ l.orderedInsert (fun p q : ℝ × ℝ => p.1 ≤ q.1) mv,
        w.1 ∈ Set.Icc 0 1 ∧ 0 ≤ w.2 := by
      intro w hw
      rcases List.mem_cons.mp ((List.perm_orderedInsert _ _ _).mem_iff.mp hw) with rfl | hw
      · exact hmv
      · exact hl' w hw
    rw [List.orderedInsert_of_not_le (fun p q : ℝ × ℝ => p.1 ≤ q.1) l
      (not_le_of_gt hvm), parisiListCascade_cons]
    by_cases hvp : 0 < v.2
    · have hi := parisiStep_interchange_parisiListCascade_strict l
        (fun w hw => (hl' w hw).1) hmv.1 hv.1.1 hvm hmvp hvp x
      have hm := parisiStep_mono_of_growth (v := v.2) hv.1.1
        (parisiListCascade_props (mv :: l) logcosh_growth logcosh_measurable).1
        (parisiListCascade_props (mv :: l) logcosh_growth logcosh_measurable).2
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).1
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).2
        (fun y => parisiListCascade_orderedInsert_le mv l logcosh_growth logcosh_measurable
          ⟨hmv.1.1, hmv.2⟩ (nonneg_of_admissible hl') y) x
      exact hi.trans_le hm
    · have hw' : ∃ w ∈ l, 0 < w.2 ∧ w.1 < mv.1 := by
        obtain ⟨w, hw, hwp, hwm⟩ := hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact (hvp hwp).elim
        · exact ⟨w, hw, hwp, hwm⟩
      have hi := parisiStep_interchange
        (parisiListCascade_props l logcosh_growth logcosh_measurable).1
        (parisiListCascade_props l logcosh_growth logcosh_measurable).2
        hv.1.1 hvm.le hmv.2 hv.2 x
      have hm := parisiStep_lt_of_forall_lt hv.1.1 hv.2
        (parisiListCascade_props (mv :: l) logcosh_growth logcosh_measurable).1
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).1
        (continuous_parisiListCascade_logcosh (mv :: l) (by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hmv.1
          · exact (hl' w hw).1))
        (continuous_parisiListCascade_logcosh _ (fun w hw => (hins w hw).1))
        (fun y => ih hl' hs' hw' y) x
      exact hi.trans_lt hm

/-- The relevant order ignores exactly the zero-variance operators. -/
def ParisiPositiveMassOrder (l : List (ℝ × ℝ)) : Prop :=
  l.Pairwise (fun p q => 0 < p.2 → 0 < q.2 → p.1 ≤ q.1)

/-- Any positive-variance mass inversion, adjacent or not, forces a strict
gain under the genuine insertion sort of the scalar operator list. -/
theorem parisiListCascade_insertionSort_lt_of_not_positive_order (l : List (ℝ × ℝ))
    (hl : ∀ v ∈ l, v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2)
    (hnot : ¬ParisiPositiveMassOrder l) (x : ℝ) :
    parisiListCascade l (fun x => Real.log (Real.cosh x)) x <
      parisiListCascade (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1))
        (fun x => Real.log (Real.cosh x)) x := by
  classical
  induction l generalizing x with
  | nil => exact (hnot (by simp [ParisiPositiveMassOrder])).elim
  | cons mv l ih =>
    have hmv := hl mv List.mem_cons_self
    have hl' : ∀ v ∈ l, v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2 :=
      fun v hv => hl v (List.mem_cons_of_mem mv hv)
    have hs : ∀ v ∈ l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1),
        v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2 := by
      intro v hv
      exact hl' v ((List.mem_insertionSort _).mp hv)
    rw [List.insertionSort_cons]
    by_cases htail : ParisiPositiveMassOrder l
    · have hhead : ¬∀ v ∈ l, 0 < mv.2 → 0 < v.2 → mv.1 ≤ v.1 := by
        intro H
        exact hnot (List.pairwise_cons.mpr ⟨H, htail⟩)
      push Not at hhead
      obtain ⟨v, hv, hmvp, hvp, hvm⟩ := hhead
      have hsorted : (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1)).Pairwise
          (fun p q => p.1 ≤ q.1) := by
        letI : Std.Total (fun p q : ℝ × ℝ => p.1 ≤ q.1) := ⟨fun p q => le_total _ _⟩
        letI : IsTrans (ℝ × ℝ) (fun p q => p.1 ≤ q.1) := ⟨fun _ _ _ => le_trans⟩
        exact List.pairwise_insertionSort _ _
      have hm := parisiStep_mono_of_growth (v := mv.2) hmv.1.1
        (parisiListCascade_props l logcosh_growth logcosh_measurable).1
        (parisiListCascade_props l logcosh_growth logcosh_measurable).2
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).1
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).2
        (fun y => parisiListCascade_insertionSort_le l logcosh_growth logcosh_measurable
          (nonneg_of_admissible hl') y) x
      exact hm.trans_lt (parisiListCascade_orderedInsert_lt mv _ hmv hs hsorted hmvp
        ⟨v, (List.mem_insertionSort _).mpr hv, hvp, hvm⟩ x)
    · have hm := parisiStep_lt_of_forall_lt hmv.1.1 hmv.2
        (parisiListCascade_props l logcosh_growth logcosh_measurable).1
        (parisiListCascade_props _ logcosh_growth logcosh_measurable).1
        (continuous_parisiListCascade_logcosh l (fun v hv => (hl' v hv).1))
        (continuous_parisiListCascade_logcosh _ (fun v hv => (hs v hv).1))
        (fun y => ih hl' htail y) x
      exact hm.trans_le (parisiListCascade_orderedInsert_le mv _ logcosh_growth
        logcosh_measurable ⟨hmv.1.1, hmv.2⟩ (nonneg_of_admissible hs) x)

/-- Equality at even one external field forces the mass order on every
positive-variance pair. No strictness is imposed on zero-variance levels. -/
theorem parisiListCascade_positive_order_of_sorting_eq (l : List (ℝ × ℝ))
    (hl : ∀ v ∈ l, v.1 ∈ Set.Icc 0 1 ∧ 0 ≤ v.2) (x : ℝ)
    (he : parisiListCascade l (fun x => Real.log (Real.cosh x)) x =
      parisiListCascade (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1))
        (fun x => Real.log (Real.cosh x)) x) :
    ParisiPositiveMassOrder l := by
  by_contra hn
  exact (parisiListCascade_insertionSort_lt_of_not_positive_order l hl hn x).ne he

end SpinGlass.Targets
