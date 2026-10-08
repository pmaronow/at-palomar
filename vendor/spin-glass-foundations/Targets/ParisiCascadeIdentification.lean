module

public import Targets.ParisiCascadeSorting

@[expose] public section

/-!
# Exact identification of sorted scalar Gaussian cascades

Equal-mass operators commute and merge by the proved Gaussian semigroup.
Consequently the actual cascade is independent of tie order in a sorted list.
All variance-zero and mass-zero branches are retained.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem equal_mass_commute (m a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiStep m a (parisiStep m b Q) = parisiStep m b (parisiStep m a Q) := by
  calc
    _ = parisiStep m (a + b) Q := (parisiStep_add m a b ha hb hQ hmQ).symm
    _ = parisiStep m (b + a) Q := by rw [add_comm a b]
    _ = _ := parisiStep_add m b a hb ha hQ hmQ

private theorem move_equal_head (a : ℝ × ℝ) (outer suffix : List (ℝ × ℝ))
    (ha : 0 ≤ a.2) (hp : ∀ b ∈ outer, b.1 = a.1 ∧ 0 ≤ b.2)
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade (outer ++ a :: suffix) Q =
      parisiStep a.1 a.2 (parisiListCascade (outer ++ suffix) Q) := by
  induction outer with
  | nil => rfl
  | cons b outer ih =>
    have hb := hp b List.mem_cons_self
    have hp' : ∀ c ∈ outer, c.1 = a.1 ∧ 0 ≤ c.2 :=
      fun c hc => hp c (List.mem_cons_of_mem b hc)
    simp only [List.cons_append, parisiListCascade_cons, ih hp', hb.1]
    exact equal_mass_commute a.1 b.2 a.2 hb.2 ha
      (parisiListCascade_props (outer ++ suffix) hQ hmQ).1
      (parisiListCascade_props (outer ++ suffix) hQ hmQ).2

/-- Two permutations already sorted by mass define the same actual cascade.
The tie order may differ, and masses need not be distinct or nonnegative. -/
theorem parisiListCascade_eq_of_perm_of_sorted
    {l₁ l₂ : List (ℝ × ℝ)} (hp : l₁.Perm l₂)
    (hs₁ : l₁.Pairwise (fun a b => a.1 ≤ b.1))
    (hs₂ : l₂.Pairwise (fun a b => a.1 ≤ b.1))
    (hv : ∀ a ∈ l₁, 0 ≤ a.2)
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade l₁ Q = parisiListCascade l₂ Q := by
  induction l₁ generalizing l₂ with
  | nil =>
    have he : l₂ = [] := List.perm_nil.mp hp.symm
    rw [he]
  | cons a l ih =>
    obtain ⟨outer, suffix, rfl⟩ := List.mem_iff_append.mp
      (hp.mem_iff.mp List.mem_cons_self)
    have hshead := (List.pairwise_cons.mp hs₁).1
    have hprefix : ∀ b ∈ outer, b.1 = a.1 ∧ 0 ≤ b.2 := by
      intro b hb
      have hb' : b ∈ a :: l := hp.mem_iff.mpr (List.mem_append_left _ hb)
      have hba : b.1 ≤ a.1 :=
        (List.pairwise_append.mp hs₂).2.2 b hb a List.mem_cons_self
      have hab : a.1 ≤ b.1 := by
        rcases List.mem_cons.mp hb' with rfl | hbl
        · exact le_rfl
        · exact hshead b hbl
      exact ⟨le_antisymm hba hab, hv b hb'⟩
    have hptail : l.Perm (outer ++ suffix) :=
      (hp.trans List.perm_middle).cons_inv
    have hstail : (outer ++ suffix).Pairwise (fun a b : ℝ × ℝ => a.1 ≤ b.1) :=
      hs₂.sublist ((List.sublist_cons_self a suffix).append_left outer)
    rw [move_equal_head a outer suffix (hv a List.mem_cons_self) hprefix hQ hmQ,
      parisiListCascade_cons,
      ih hptail (List.pairwise_cons.mp hs₁).2 hstail
        (fun b hb => hv b (List.mem_cons_of_mem a hb))]

/-- A block with constant mass is exactly one operator whose variance is the
sum of the original variances. An empty block gives the identity operator. -/
theorem parisiListCascade_constant_mass (m : ℝ) (variances : List ℝ)
    (hv : ∀ v ∈ variances, 0 ≤ v)
    {Q : ℝ → ℝ} (hQ : HasLinearGrowth Q) (hmQ : Measurable Q) :
    parisiListCascade (variances.map (fun v => (m, v))) Q =
      parisiStep m variances.sum Q := by
  induction variances with
  | nil =>
    funext x
    by_cases hm : m = 0
    · simp [parisiListCascade, parisiStep, hm]
    · simp [parisiListCascade, parisiStep, hm]
  | cons v vs ih =>
    have hvs : ∀ a ∈ vs, 0 ≤ a := fun a ha => hv a (List.mem_cons_of_mem v ha)
    simp only [List.map_cons, List.sum_cons, parisiListCascade_cons, ih hvs]
    exact (parisiStep_add m v vs.sum (hv v List.mem_cons_self)
      (List.sum_nonneg hvs) hQ hmQ).symm

end SpinGlass.Targets
