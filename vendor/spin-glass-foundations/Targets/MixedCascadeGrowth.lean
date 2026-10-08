module

public import Targets.Section5InterleavedEndpoint

@[expose] public section

/-!
# Growth and order for arbitrary mixed paired Gaussian cascades

The opposite step is an ordinary shared step conjugated by second-field
reflection. Thus all three modes reuse the checked Gaussian growth and order
theorems. The terminal function can be genuinely constrained.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

theorem CoupledGrowth.flip_second {n : ℕ}
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) :
    CoupledGrowth (fun x y => F x (-y)) := by
  obtain ⟨C, D, hD, hb⟩ := hF.bound
  refine ⟨hF.measurable.comp (measurable_fst.prodMk measurable_snd.neg), C, D, hD, ?_⟩
  intro x y
  simpa only [l1, Pi.neg_apply, abs_neg] using hb x (-y)

theorem mixedVectorStep_shared_eq (n : ℕ) (m v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    mixedVectorStep n .shared m v F = sharedStepPi n (2 * m) v F := by
  funext x y
  simpa only [mixedVectorStep, show 2 * m / 2 = m by ring] using
    (sharedStepPi_eq_gtVectorStep n (2 * m) v F x y).symm

theorem mixedVectorStep_independent_eq {n : ℕ} (m v : ℝ)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) :
    mixedVectorStep n .independent m v F = independentStepPi n m v F :=
  funext fun x => funext fun y => (independentStepPi_eq_gtVectorSteps m v hF x y).symm

theorem mixedVectorStep_opposite_eq (n : ℕ) (m v : ℝ)
    (F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    mixedVectorStep n .opposite m v F x y =
      sharedStepPi n (2 * m) v (fun x y => F x (-y)) x (-y) := by
  rw [sharedStepPi_eq_gtVectorStep]
  simp only [mixedVectorStep, show 2 * m / 2 = m by ring, AT.gtVectorStep,
    Pi.neg_apply, neg_mul]
  have he (z : Fin n → ℝ) : (fun i => y i + -(Real.sqrt v * z i)) =
      -(fun i => -y i + Real.sqrt v * z i) := by
    funext i
    simp only [Pi.neg_apply]
    ring
  simp_rw [he]

theorem CoupledGrowth.mixedStep {n : ℕ}
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (mode : Section5GaussianMode) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledGrowth (mixedVectorStep n mode m v F) := by
  cases mode with
  | independent =>
    rw [mixedVectorStep_independent_eq m v hF]
    exact hF.independentStep hm hv
  | shared =>
    rw [mixedVectorStep_shared_eq]
    exact hF.sharedStep (by positivity) hv
  | opposite =>
    have H := (hF.flip_second.sharedStep (by positivity : 0 ≤ 2 * m) hv).flip_second
    convert H using 1
    funext x y
    exact mixedVectorStep_opposite_eq n m v F x y

theorem mixedVectorStep_mono {n : ℕ} (mode : Section5GaussianMode) {m v : ℝ}
    (hm : 0 ≤ m) {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : CoupledGrowth F) (hG : CoupledGrowth G) (hle : ∀ x y, F x y ≤ G x y)
    (x y : Fin n → ℝ) : mixedVectorStep n mode m v F x y ≤ mixedVectorStep n mode m v G x y := by
  cases mode with
  | independent =>
    rw [mixedVectorStep_independent_eq m v hF, mixedVectorStep_independent_eq m v hG]
    exact independentStepPi_mono hm hF hG hle x y
  | shared =>
    rw [mixedVectorStep_shared_eq, mixedVectorStep_shared_eq]
    exact sharedStepPi_mono (by positivity) hF hG hle x y
  | opposite =>
    rw [mixedVectorStep_opposite_eq, mixedVectorStep_opposite_eq]
    exact sharedStepPi_mono (by positivity) hF.flip_second hG.flip_second (fun x y => hle x (-y)) x (-y)

theorem mixedVectorStep_const_add {n : ℕ} (mode : Section5GaussianMode) (m v c : ℝ)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) (x y : Fin n → ℝ) :
    mixedVectorStep n mode m v (fun x y => c + F x y) x y =
      c + mixedVectorStep n mode m v F x y := by
  cases mode with
  | independent =>
    rw [mixedVectorStep_independent_eq m v (hF.const_add c), mixedVectorStep_independent_eq m v hF]
    exact independentStepPi_const_add c m v hF x y
  | shared =>
    rw [mixedVectorStep_shared_eq, mixedVectorStep_shared_eq]
    exact sharedStepPi_const_add c (2 * m) v hF x y
  | opposite =>
    rw [mixedVectorStep_opposite_eq, mixedVectorStep_opposite_eq]
    exact sharedStepPi_const_add c (2 * m) v hF.flip_second x (-y)

theorem CoupledGrowth.mixedList {α : Type*} {n : ℕ}
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F)
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a) :
    CoupledGrowth (mixedVectorListCascade n mode m v l F) := by
  induction l with
  | nil => exact hF
  | cons a l ih =>
    exact (ih (fun b hb => hm b (List.mem_cons_of_mem a hb))
      (fun b hb => hv b (List.mem_cons_of_mem a hb))).mixedStep (mode a)
        (hm a List.mem_cons_self) (hv a List.mem_cons_self)

theorem mixedVectorListCascade_mono {α : Type*} {n : ℕ}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a)
    {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) (hG : CoupledGrowth G)
    (hle : ∀ x y, F x y ≤ G x y) (x y : Fin n → ℝ) :
    mixedVectorListCascade n mode m v l F x y ≤ mixedVectorListCascade n mode m v l G x y := by
  induction l generalizing x y with
  | nil => exact hle x y
  | cons a l ih =>
    have hm' : ∀ b ∈ l, 0 ≤ m b := fun b hb => hm b (List.mem_cons_of_mem a hb)
    have hv' : ∀ b ∈ l, 0 ≤ v b := fun b hb => hv b (List.mem_cons_of_mem a hb)
    exact mixedVectorStep_mono (mode a) (hm a List.mem_cons_self)
      (hF.mixedList mode m v l hm' hv') (hG.mixedList mode m v l hm' hv') (ih hm' hv') x y

theorem mixedVectorListCascade_const_add {α : Type*} {n : ℕ}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (hm : ∀ a ∈ l, 0 ≤ m a) (hv : ∀ a ∈ l, 0 ≤ v a) (c : ℝ)
    {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hF : CoupledGrowth F) (x y : Fin n → ℝ) :
    mixedVectorListCascade n mode m v l (fun x y => c + F x y) x y =
      c + mixedVectorListCascade n mode m v l F x y := by
  induction l generalizing x y with
  | nil => rfl
  | cons a l ih =>
    have hm' : ∀ b ∈ l, 0 ≤ m b := fun b hb => hm b (List.mem_cons_of_mem a hb)
    have hv' : ∀ b ∈ l, 0 ≤ v b := fun b hb => hv b (List.mem_cons_of_mem a hb)
    have he := funext fun x => funext fun y => ih hm' hv' x y
    change mixedVectorStep n (mode a) (m a) (v a)
      (mixedVectorListCascade n mode m v l (fun x y => c + F x y)) x y = _
    rw [he, mixedVectorStep_const_add (mode a) (m a) (v a) c (hF.mixedList mode m v l hm' hv')]
    rfl

end SpinGlass.Targets
