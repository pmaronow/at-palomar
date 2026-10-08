module

public import Targets.Section5CompactWitness
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

@[expose] public section

/-!
# Uniform witness tubes around compact slices

A pointwise family of strict continuous witnesses along a compact slice has
a whole uniform-width tube on which some witness remains strict.  Applying
the compact-witness minimum once more makes the positive margin uniform on
that tube.
-/

open Set Filter Topology

namespace SpinGlass.Targets

theorem exists_uniform_positive_near_compact_slice
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    (f : I → (X × ℝ) → ℝ) (hf : ∀ i, Continuous (f i)) (y₀ : ℝ)
    (hpos : ∀ x ∈ S, ∃ i, 0 < f i (x, y₀)) :
    ∃ η > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ x ∈ S, ∀ y, |y - y₀| ≤ η → ∃ i, δ ≤ f i (x, y) := by
  classical
  let N : Set (X × ℝ) := {z | ∃ i, 0 < f i z}
  have hNopen : IsOpen N := by
    rw [show N = ⋃ i, {z | 0 < f i z} by
      ext z
      simp only [N, mem_setOf_eq, mem_iUnion]]
    exact isOpen_iUnion (fun i => isOpen_lt continuous_const (hf i))
  have hslice : S ×ˢ ({y₀} : Set ℝ) ⊆ N := by
    intro z hz
    rcases z with ⟨x, y⟩
    rcases hz with ⟨hx, hy⟩
    change x ∈ S at hx
    change y ∈ ({y₀} : Set ℝ) at hy
    rw [mem_singleton_iff] at hy
    subst y
    change ∃ i, 0 < f i (x, y₀)
    exact hpos x hx
  obtain ⟨U, V, hUopen, hVopen, hSU, hyV, hUV⟩ :=
    generalized_tube_lemma hS isCompact_singleton hNopen hslice
  have hVnhds : V ∈ 𝓝 y₀ := hVopen.mem_nhds (hyV (mem_singleton y₀))
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hVnhds
  let η := a / 2
  have hη : 0 < η := half_pos ha
  let K : Set (X × ℝ) := S ×ˢ Icc (y₀ - η) (y₀ + η)
  have hK : IsCompact K := hS.prod isCompact_Icc
  have hKpos : ∀ z ∈ K, ∃ i, 0 < f i z := by
    intro z hz
    apply hUV
    refine ⟨hSU hz.1, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |z.2 - y₀| ≤ η := by
      exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact habs.trans_lt (half_lt_self ha)
  obtain ⟨δ, hδ, Hδ⟩ := exists_uniform_positive_of_compact_witnesses
    hK f (fun i => (hf i).continuousOn) hKpos
  refine ⟨η, hη, δ, hδ, ?_⟩
  intro x hx y hy
  apply Hδ (x, y)
  have habs := abs_le.mp hy
  exact ⟨hx, ⟨by linarith [habs.1], by linarith [habs.2]⟩⟩

end SpinGlass.Targets
