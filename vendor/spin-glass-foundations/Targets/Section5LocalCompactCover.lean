module

public import Targets.Section5CompactWitness

@[expose] public section

/-!
# Compactness from locally uniform gaps

This is the open-cover form of the final Section 5 compactness argument.  A
gap may be proved by a different interpolation in each neighborhood.  On a
compact parameter set only finitely many neighborhoods are needed, so the
minimum of their positive deficits is still positive.
-/

open Set Topology

namespace SpinGlass.Targets

theorem exists_compact_local_patch
    {X : Type*} [PseudoMetricSpace X]
    {S O : Set X} (hS : IsCompact S) (hO : IsOpen O) {x : X} (hx : x ∈ O) :
    ∃ T U : Set X, IsCompact T ∧ IsOpen U ∧ x ∈ U ∧
      S ∩ U ⊆ T ∧ T ⊆ S ∩ O := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let U := Metric.ball x (a / 2)
  let T := S ∩ Metric.closedBall x (a / 2)
  have hhalf : a / 2 < a := half_lt_self ha
  have hclosedOpen : Metric.closedBall x (a / 2) ⊆ O := by
    intro y hy
    apply hball
    exact lt_of_le_of_lt hy hhalf
  refine ⟨T, U, hS.inter_right Metric.isClosed_closedBall, Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos ha), ?_, ?_⟩
  · intro y hy
    exact ⟨hy.1, Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy.2).le⟩
  · intro y hy
    exact ⟨hy.1, hclosedOpen hy.2⟩

theorem exists_local_gap_of_compact_subsets
    {X : Type*} [PseudoMetricSpace X] {S O : Set X}
    (hS : IsCompact S) (hO : IsOpen O) {x : X} (hx : x ∈ O)
    (P : ℝ → X → Prop)
    (hgap : ∀ T : Set X, IsCompact T → T ⊆ S ∩ O →
      ∃ δ > (0 : ℝ), ∀ y ∈ T, P δ y) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ y ∈ S, y ∈ U → P δ y := by
  obtain ⟨T, U, hT, hU, hxU, hSUT, hTSO⟩ :=
    exists_compact_local_patch hS hO hx
  obtain ⟨δ, hδ, Hδ⟩ := hgap T hT hTSO
  exact ⟨U, hU, hxU, δ, hδ, fun y hyS hyU => Hδ y (hSUT ⟨hyS, hyU⟩)⟩

theorem exists_uniform_gap_of_compact_local_gaps
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) (P : ℝ → X → Prop)
    (hmono : ∀ {a b : ℝ} {x : X}, 0 < b → b ≤ a → P a x → P b x)
    (hloc : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ y ∈ S, y ∈ U → P δ y) :
    ∃ δ > (0 : ℝ), ∀ x ∈ S, P δ x := by
  classical
  choose U hUopen hxU δ hδ hP using hloc
  have hcover : S ⊆ ⋃ x : S, U x.1 x.2 := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU x hx⟩
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover
    (fun x : S => U x.1 x.2) (fun x => hUopen x.1 x.2) hcover
  by_cases hne : T.Nonempty
  · let δ₀ : ℝ := T.inf' hne (fun x => δ x.1 x.2)
    have hδ₀ : 0 < δ₀ := by
      dsimp [δ₀]
      exact (Finset.lt_inf'_iff hne).mpr (fun x _ => hδ x.1 x.2)
    refine ⟨δ₀, hδ₀, ?_⟩
    intro x hx
    obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.mp (hT hx)
    exact hmono hδ₀ (Finset.inf'_le _ hzT)
      (hP z.1 z.2 x hx hxz)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    obtain ⟨z, hzT, _⟩ := mem_iUnion₂.mp (hT hx)
    exact (hne ⟨z, hzT⟩).elim

end SpinGlass.Targets
