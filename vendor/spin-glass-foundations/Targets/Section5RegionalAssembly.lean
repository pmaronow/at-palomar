module

public import Targets.Section5QuadraticAssembly
public import Targets.TalagrandOverlapTail
public import Targets.Section5FiniteGapCover

@[expose] public section

/-!
# Quantifier-preserving regional assembly

This is the final elementary assembly step once the local and outside
estimates have been proved with constants uniform in time, overlap, system
size, and disorder.  It makes those two obligations explicit and produces the
exact eventual-in-system-size quantifier used by Theorem 2.4.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- A uniform local quadratic estimate and a uniform positive outside gap
combine into the desired quadratic estimate.  The regional hypotheses are
stated directly with the original constrained free energy and the supplied
SK disorder family; no endpoint, sign, or compactness conclusion is hidden
in this adapter. -/
theorem exists_uniform_quadratic_bound_of_regional
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {t₀ η a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hη : 0 < η)
    (hlocal : ∀ n, 0 < n → ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d,
      1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      |u - s.q (k + 2 - d)| ≤ η →
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t - a * (u - s.q (k + 2 - d)) ^ 2)
    (houtside : ∀ n, 0 < n → ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d,
      1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      η ≤ |u - s.q (k + 2 - d)| →
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t - c) :
    ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t -
            (u - s.q (k + 2 - d)) ^ 2 / K := by
  let K : ℝ := max (1 / a) (4 / c)
  have hKa : 1 / a ≤ K := le_max_left _ _
  have hKc : 4 / c ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le (by positivity : 0 < 1 / a) hKa
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro t ht d hd1 hdk u hu
  have hqlo : 0 ≤ s.q (k + 2 - d) :=
    s.q_nonneg (p := k + 2 - d) (by omega)
  have hqhi : s.q (k + 2 - d) ≤ 1 :=
    s.q_le_one (p := k + 2 - d) (by omega)
  by_cases hnear : |u - s.q (k + 2 - d)| ≤ η
  · have H := hlocal n hn t ht d hd1 hdk u hu hnear
    have hdiv : 1 / K ≤ a := by
      have hprod : 1 ≤ K * a := by
        apply (div_le_iff₀ ha).mp
        simpa only [one_div] using hKa
      exact (div_le_iff₀ hK).2 (by
        simpa only [one_mul, mul_comm] using hprod)
    have hquad : (u - s.q (k + 2 - d)) ^ 2 / K ≤
        a * (u - s.q (k + 2 - d)) ^ 2 := by
      calc
        (u - s.q (k + 2 - d)) ^ 2 / K =
            (1 / K) * (u - s.q (k + 2 - d)) ^ 2 := by ring
        _ ≤ a * (u - s.q (k + 2 - d)) ^ 2 :=
          mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
    linarith
  · have H := houtside n hn t ht d hd1 hdk u hu
      (le_of_not_ge hnear)
    have hdiff : |u - s.q (k + 2 - d)| ≤ 2 := by
      have huabs : |u| ≤ 1 := by
        obtain ⟨σ, τ, hστ⟩ := mem_attainableOverlaps.mp hu
        rw [← hστ]
        exact abs_overlap_le_one hn σ τ
      have hqabs : |s.q (k + 2 - d)| ≤ 1 := by
        rw [abs_of_nonneg hqlo]
        exact hqhi
      calc
        |u - s.q (k + 2 - d)| =
            |u + (-(s.q (k + 2 - d)))| := by rw [sub_eq_add_neg]
        _ ≤ |u| + |-(s.q (k + 2 - d))| := abs_add_le _ _
        _ = |u| + |s.q (k + 2 - d)| := by rw [abs_neg]
        _ ≤ 2 := by linarith
    have hsq : (u - s.q (k + 2 - d)) ^ 2 ≤ 4 := by
      rw [← sq_abs]
      nlinarith [sq_nonneg (|u - s.q (k + 2 - d)| - 2)]
    have hquad : (u - s.q (k + 2 - d)) ^ 2 / K ≤ c := by
      have hdiv : 4 / K ≤ c := by
        apply (div_le_iff₀ hK).2
        have hprod : 4 ≤ K * c := by
          exact (div_le_iff₀ hc).mp hKc
        simpa only [mul_comm] using hprod
      exact (div_le_div_of_nonneg_right hsq (le_of_lt hK)).trans hdiv
    linarith

/- A finite family of regional estimates can use different local and outside
constants at each physical level.  This is the quantifier-preserving bridge
used when the compact cover is assembled level by level.  In particular, the
constants are not allowed to depend on the system size or on the disorder. -/
theorem exists_uniform_quadratic_bound_of_finite_regional
    {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h)
    (a c : ℕ → ℝ) {t₀ η : ℝ}
    (hη : 0 < η)
    (ha : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < a d)
    (hc : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < c d)
    (hlocal : ∀ n, 0 < n → ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d,
      1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      |u - s.q (k + 2 - d)| ≤ η →
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t - a d * (u - s.q (k + 2 - d)) ^ 2)
    (houtside : ∀ n, 0 < n → ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d,
      1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      η ≤ |u - s.q (k + 2 - d)| →
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t - c d) :
    ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t -
            (u - s.q (k + 2 - d)) ^ 2 / K := by
  classical
  let D : Finset ℕ := Finset.Icc 1 (k + 1)
  have hDne : D.Nonempty := by
    exact ⟨1, by simp [D]⟩
  let a₀ : ℝ := D.inf' hDne a
  let c₀ : ℝ := D.inf' hDne c
  have ha₀ : 0 < a₀ := by
    have H : 0 < D.inf' hDne a := (Finset.lt_inf'_iff hDne).mpr (by
      intro d hd
      apply ha d
      · simpa [D] using (Finset.mem_Icc.mp hd).1
      · simpa [D] using (Finset.mem_Icc.mp hd).2)
    simpa [a₀] using H
  have hc₀ : 0 < c₀ := by
    have H : 0 < D.inf' hDne c := (Finset.lt_inf'_iff hDne).mpr (by
      intro d hd
      apply hc d
      · simpa [D] using (Finset.mem_Icc.mp hd).1
      · simpa [D] using (Finset.mem_Icc.mp hd).2)
    simpa [c₀] using H
  have haa : ∀ d, 1 ≤ d → d ≤ k + 1 → a₀ ≤ a d := by
    intro d hd1 hdk
    exact Finset.inf'_le a (by simp [D, hd1, hdk])
  have hcc : ∀ d, 1 ≤ d → d ≤ k + 1 → c₀ ≤ c d := by
    intro d hd1 hdk
    exact Finset.inf'_le c (by simp [D, hd1, hdk])
  exact exists_uniform_quadratic_bound_of_regional s β h sk
    (t₀ := t₀) (η := η) (a := a₀) (c := c₀)
    ha₀ hc₀ hη
    (fun n hn t ht d hd1 hdk u hu hnear => by
      have H := hlocal n hn t ht d hd1 hdk u hu hnear
      have hcoef : a₀ * (u - s.q (k + 2 - d)) ^ 2 ≤
          a d * (u - s.q (k + 2 - d)) ^ 2 :=
        mul_le_mul_of_nonneg_right (haa d hd1 hdk) (sq_nonneg _)
      linarith)
    (fun n hn t ht d hd1 hdk u hu hfar => by
      have H := houtside n hn t ht d hd1 hdk u hu hfar
      linarith [hcc d hd1 hdk])

/- This is the compact-cover specialization used by the global assembly.  The
sets `S d j` are the closed compact pieces for level `d`; `hcover` is required
only on the far region, while `hlocal` handles the complementary quadratic
neighborhood.  Thus endpoint gluing and sign-specific estimates remain
explicit inputs rather than being hidden in this bookkeeping theorem. -/
theorem exists_uniform_quadratic_bound_of_local_and_finite_compact_cover
    {J : Type*} [Fintype J] {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) (a : ℕ → ℝ)
    {t₀ η : ℝ} (hη : 0 < η)
    (ha : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < a d)
    (hlocal : ∀ n, 0 < n → ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ d,
      1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      |u - s.q (k + 2 - d)| ≤ η →
      constrainedPhi n s β h (sk n).U d t u ≤
        2 * guerraPsi s β h t - a d * (u - s.q (k + 2 - d)) ^ 2)
    (X : Set (ℝ × ℝ)) (S : ℕ → J → Set (ℝ × ℝ))
    (hS : ∀ d j, IsCompact (S d j))
    (hcover : ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ z ∈ X,
      η ≤ |z.2 - s.q (k + 2 - d)| → ∃ j, z ∈ S d j)
    (hgap : ∀ d j, 1 ≤ d → d ≤ k + 1 → ∃ δ > (0 : ℝ),
      ∀ z ∈ S d j, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U d z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - δ)
    (hX : ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ {n : ℕ}, ∀ u ∈ attainableOverlaps n,
      (t, u) ∈ X) :
    ∃ K > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t -
            (u - s.q (k + 2 - d)) ^ 2 / K := by
  classical
  let Xd : ℕ → Set (ℝ × ℝ) := fun d =>
    {z | z ∈ X ∧ η ≤ |z.2 - s.q (k + 2 - d)|}
  have hfinite : ∀ d, 1 ≤ d → d ≤ k + 1 →
      ∃ δ > (0 : ℝ), ∀ z ∈ Xd d, ∀ {n : ℕ}, 0 < n →
        ∀ sk : SKDisorder (Ω := Ω) n β h,
        (∃ σ τ : Config n, overlap n σ τ = z.2) →
        constrainedPhi n s β h sk.U d z.1 z.2 ≤
          2 * guerraPsi s β h z.1 - δ := by
    intro d hd1 hdk
    exact exists_uniform_constrainedPhi_gap_of_finite_compact_cover_at_level
      (Ω := Ω) s β h d (Xd d) (S d) (hS d)
      (fun z hz => hcover d hd1 hdk z hz.1 hz.2)
      (fun j => hgap d j hd1 hdk)
  let c : ℕ → ℝ := fun d => if hd : 1 ≤ d ∧ d ≤ k + 1 then
    Classical.choose (hfinite d hd.1 hd.2) else 1
  have hc : ∀ d, 1 ≤ d → d ≤ k + 1 → 0 < c d := by
    intro d hd1 hdk
    have H := (Classical.choose_spec (hfinite d hd1 hdk)).1
    simpa [c, hd1, hdk] using H
  have hcout : ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ z ∈ Xd d, ∀ {n : ℕ}, 0 < n →
      ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U d z.1 z.2 ≤
        2 * guerraPsi s β h z.1 - c d := by
    intro d hd1 hdk z hz n hn sk hatt
    have H := (Classical.choose_spec (hfinite d hd1 hdk)).2 z hz hn sk hatt
    simpa [c, hd1, hdk] using H
  apply exists_uniform_quadratic_bound_of_finite_regional s β h sk a c
    hη ha hc hlocal
  intro n hn t ht d hd1 hdk u hu hfar
  have hzX : (t, u) ∈ X := hX t ht u hu
  obtain ⟨σ, τ, hστ⟩ := mem_attainableOverlaps.mp hu
  have H := hcout d hd1 hdk (t, u) ⟨hzX, hfar⟩ hn (sk n) ⟨σ, τ, hστ⟩
  simpa using H

end SpinGlass.Targets
