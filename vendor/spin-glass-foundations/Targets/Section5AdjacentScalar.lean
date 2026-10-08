module

public import Targets.Section5InterleavedScalarCore

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-! The scalar analogue of the tagged vector-list deletion lemma.  It is
 deliberately kept local to this boundary argument: the list order is the
 stable sorted order, while zero-variance entries may be deleted exactly. -/

noncomputable def mixedScalarStep' (mode : Section5GaussianMode) (m v : ℝ)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) : Unit → ℝ → ℝ × ℝ → ℝ :=
  match mode with
  | .independent => GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => Real.sqrt v)
      (fun _ => 0) (GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => 0)
        (fun _ => Real.sqrt v) F)
  | .shared => GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => Real.sqrt v)
      (fun _ => Real.sqrt v) F
  | .opposite => GTFrame.finiteStep (gaussianReal 0 1) m (fun _ => Real.sqrt v)
      (fun _ => -Real.sqrt v) F

noncomputable def mixedScalarListCascade' {α : Type*}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) : Unit → ℝ → ℝ × ℝ → ℝ :=
  l.foldr (fun a G => mixedScalarStep' (mode a) (m a) (v a) G) F

theorem mixedScalarStep'_zero_variance (mode : Section5GaussianMode) (m : ℝ)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) : mixedScalarStep' mode m 0 F = F := by
  cases mode <;> funext p l x <;> by_cases hm : m = 0 <;>
    simp [mixedScalarStep', GTFrame.finiteStep, GTFrame.step0, GTFrame.stepM, hm,
      Real.log_exp]

theorem mixedScalarListCascade'_filter {α : Type*}
    (mode : α → Section5GaussianMode) (m v : α → ℝ) (l : List α)
    (keep : α → Bool) (hzero : ∀ a ∈ l, keep a = false → v a = 0)
    (F : Unit → ℝ → ℝ × ℝ → ℝ) :
    mixedScalarListCascade' mode m v l F =
      mixedScalarListCascade' mode m v (l.filter keep) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => hzero b (List.mem_cons_of_mem a hb))
    cases hk : keep a with
    | false =>
      have hz := hzero a List.mem_cons_self hk
      simpa [mixedScalarListCascade', hk, hz, mixedScalarStep'_zero_variance] using ih'
    | true =>
      simpa [mixedScalarListCascade', hk] using
        congrArg (mixedScalarStep' (mode a) (m a) (v a)) ih'

theorem mixedScalarCascade'_ofFn_reverse {α : Type*} {N : ℕ}
    (mode : α → Section5GaussianMode) (m v : α → ℝ)
    (a : ℕ → α) (l : ℝ) (x : ℝ × ℝ) :
    mixedScalarCascade (fun i => mode (a (N - 1 - i)))
      (fun i => m (a (N - 1 - i)))
      (fun i (_ : Unit) => v (a (N - 1 - i))) N () l x =
      mixedScalarListCascade' mode m v
        (List.ofFn (fun p : Fin N => a p))
        (fun _ l z => coupledSite l z.1 z.2) () l x := by
  have H : ∀ (L : ℕ) (hL : L ≤ N),
      mixedScalarCascade (fun i => mode (a (N - 1 - i)))
        (fun i => m (a (N - 1 - i)))
        (fun i (_ : Unit) => v (a (N - 1 - i))) L =
      mixedScalarListCascade' mode m v
        (List.ofFn (fun p : Fin L => a (N - L + p)))
        (fun _ l z => coupledSite l z.1 z.2) := by
    intro L hL
    induction L with
    | zero => rfl
    | succ L ih =>
      rw [mixedScalarCascade]
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero]
      rw [show N - (L + 1) = N - 1 - L by omega]
      have htail : (fun p : Fin L => a (N - 1 - L + p.succ)) =
          (fun p : Fin L => a (N - L + p)) := by
        funext p
        congr 1
        simp only [Fin.val_succ]
        omega
      rw [htail]
      simp only [mixedScalarListCascade', List.foldr]
      cases hmode : mode (a (N - 1 - L)) <;>
        simp only [mixedScalarStep']
      all_goals rw [ih (by omega)]
      all_goals rfl
  have hH := H N le_rfl
  simpa only [Nat.sub_self, zero_add] using congrFun (congrFun (congrFun hH ()) l) x

end SpinGlass.Targets
