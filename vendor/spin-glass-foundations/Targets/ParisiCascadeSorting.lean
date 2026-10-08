module

public import Targets.ParisiStepInterchange
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# Finite scalar Parisi cascades and sorting by mass

The list is ordered from the outermost operator to the innermost. Sorting it
by increasing mass raises the actual scalar cascade, by the proved Gaussian
interchange inequality. Equal neighboring masses combine by the genuine
Gaussian semigroup, including mass and variance zero.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- A finite list of actual scalar Gaussian Parisi operators, outermost first. -/
noncomputable def parisiListCascade (steps : List (ℝ × ℝ)) (Q : ℝ → ℝ) : ℝ → ℝ :=
  steps.foldr (fun mv A => parisiStep mv.1 mv.2 A) Q

@[simp] theorem parisiListCascade_nil (Q : ℝ → ℝ) : parisiListCascade [] Q = Q := rfl

@[simp] theorem parisiListCascade_cons (mv : ℝ × ℝ) (l : List (ℝ × ℝ)) (Q : ℝ → ℝ) :
    parisiListCascade (mv :: l) Q = parisiStep mv.1 mv.2 (parisiListCascade l Q) := rfl

theorem parisiListCascade_append (l₁ l₂ : List (ℝ × ℝ)) (Q : ℝ → ℝ) :
    parisiListCascade (l₁ ++ l₂) Q = parisiListCascade l₁ (parisiListCascade l₂ Q) := by
  simp only [parisiListCascade, List.foldr_append]

/-- The finite composition remains measurable with linear growth, even
without ordering or sign restrictions on the operator parameters. -/
theorem parisiListCascade_props (l : List (ℝ × ℝ)) {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    HasLinearGrowth (parisiListCascade l Q) ∧ Measurable (parisiListCascade l Q) := by
  induction l with
  | nil => exact ⟨hQ, hmQ⟩
  | cons mv l ih =>
    exact ⟨hasLinearGrowth_parisiStep ih.1 ih.2 mv.1 mv.2,
      measurable_parisiStep ih.2 mv.1 mv.2⟩

theorem hasLinearGrowth_parisiListCascade (l : List (ℝ × ℝ)) {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    HasLinearGrowth (parisiListCascade l Q) := (parisiListCascade_props l hQ hmQ).1

theorem measurable_parisiListCascade (l : List (ℝ × ℝ)) {Q : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    Measurable (parisiListCascade l Q) := (parisiListCascade_props l hQ hmQ).2

/-- Nonnegative-mass finite compositions preserve pointwise order. -/
theorem parisiListCascade_mono (l : List (ℝ × ℝ))
    (hl : ∀ mv ∈ l, 0 ≤ mv.1) {Q R : ℝ → ℝ}
    (hQ : HasLinearGrowth Q) (hmQ : Measurable Q)
    (hR : HasLinearGrowth R) (hmR : Measurable R)
    (hQR : ∀ x, Q x ≤ R x) (x : ℝ) :
    parisiListCascade l Q x ≤ parisiListCascade l R x := by
  induction l generalizing x with
  | nil => exact hQR x
  | cons mv l ih =>
    have hl' : ∀ v ∈ l, 0 ≤ v.1 := fun v hv => hl v (List.mem_cons_of_mem mv hv)
    exact parisiStep_mono_of_growth (hl mv (List.mem_cons_self))
      (parisiListCascade_props l hQ hmQ).1 (parisiListCascade_props l hQ hmQ).2
      (parisiListCascade_props l hR hmR).1 (parisiListCascade_props l hR hmR).2
      (fun y => ih hl' y) x

/-- Two adjacent equal-mass operators merge their nonnegative variances. -/
theorem parisiListCascade_merge_cons (m : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (l : List (ℝ × ℝ)) {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade ((m, a) :: (m, b) :: l) Q =
      parisiListCascade ((m, a + b) :: l) Q := by
  simpa only [parisiListCascade_cons] using
    (parisiStep_add m a b ha hb (parisiListCascade_props l hQ hmQ).1
      (parisiListCascade_props l hQ hmQ).2).symm

/-- Equal-mass merging is valid at any position of the actual composition. -/
theorem parisiListCascade_merge (outer suffix : List (ℝ × ℝ)) (m : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade (outer ++ (m, a) :: (m, b) :: suffix) Q =
      parisiListCascade (outer ++ (m, a + b) :: suffix) Q := by
  rw [parisiListCascade_append, parisiListCascade_append,
    parisiListCascade_merge_cons m ha hb suffix hQ hmQ]

/-- Inserting one operator in mass order raises the actual composition.
This uses the proved Gaussian operator interchange at each crossed operator. -/
theorem parisiListCascade_orderedInsert_le (mv : ℝ × ℝ) (l : List (ℝ × ℝ))
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q)
    (hmv : 0 ≤ mv.1 ∧ 0 ≤ mv.2) (hl : ∀ v ∈ l, 0 ≤ v.1 ∧ 0 ≤ v.2) (x : ℝ) :
    parisiListCascade (mv :: l) Q x ≤
      parisiListCascade (l.orderedInsert (fun p q : ℝ × ℝ => p.1 ≤ q.1) mv) Q x := by
  classical
  induction l generalizing x with
  | nil => rw [List.orderedInsert_nil]
  | cons v l ih =>
    have hv := hl v List.mem_cons_self
    have hl' : ∀ w ∈ l, 0 ≤ w.1 ∧ 0 ≤ w.2 :=
      fun w hw => hl w (List.mem_cons_of_mem v hw)
    by_cases hle : mv.1 ≤ v.1
    · rw [List.orderedInsert_cons_of_le (fun p q : ℝ × ℝ => p.1 ≤ q.1) l hle]
    · rw [List.orderedInsert_of_not_le (fun p q : ℝ × ℝ => p.1 ≤ q.1) l hle]
      have hi := parisiStep_interchange (parisiListCascade_props l hQ hmQ).1
        (parisiListCascade_props l hQ hmQ).2 hv.1 (le_of_not_ge hle) hmv.2 hv.2 x
      have hm := parisiStep_mono_of_growth (v := v.2) hv.1
        (parisiListCascade_props (mv :: l) hQ hmQ).1
        (parisiListCascade_props (mv :: l) hQ hmQ).2
        (parisiListCascade_props (l.orderedInsert (fun p q : ℝ × ℝ => p.1 ≤ q.1) mv) hQ hmQ).1
        (parisiListCascade_props (l.orderedInsert (fun p q : ℝ × ℝ => p.1 ≤ q.1) mv) hQ hmQ).2
        (fun y => ih hl' y) x
      exact hi.trans hm

/-- Sorting by nondecreasing mass raises the actual finite scalar cascade.
Permutation/sortedness metadata comes from Mathlib's insertion sort; the
comparison itself is proved here for the Gaussian operators. -/
theorem parisiListCascade_insertionSort_le (l : List (ℝ × ℝ))
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q)
    (hl : ∀ mv ∈ l, 0 ≤ mv.1 ∧ 0 ≤ mv.2) (x : ℝ) :
    parisiListCascade l Q x ≤
      parisiListCascade (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1)) Q x := by
  classical
  induction l generalizing x with
  | nil => rw [List.insertionSort_nil]
  | cons mv l ih =>
    have hmv := hl mv List.mem_cons_self
    have hl' : ∀ v ∈ l, 0 ≤ v.1 ∧ 0 ≤ v.2 :=
      fun v hv => hl v (List.mem_cons_of_mem mv hv)
    have hs : ∀ v ∈ l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1), 0 ≤ v.1 ∧ 0 ≤ v.2 := by
      intro v hv
      exact hl' v ((List.mem_insertionSort _).mp hv)
    have hm := parisiStep_mono_of_growth (v := mv.2) hmv.1
      (parisiListCascade_props l hQ hmQ).1 (parisiListCascade_props l hQ hmQ).2
      (parisiListCascade_props (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1)) hQ hmQ).1
      (parisiListCascade_props (l.insertionSort (fun p q : ℝ × ℝ => p.1 ≤ q.1)) hQ hmQ).2
      (fun y => ih hl' y) x
    simpa only [List.insertionSort_cons, parisiListCascade_cons] using
      hm.trans (parisiListCascade_orderedInsert_le mv _ hQ hmQ hmv hs x)

end SpinGlass.Targets
