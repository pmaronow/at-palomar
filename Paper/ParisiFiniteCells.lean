module

public import Paper.ParisiFiniteGlue
public import Paper.ParisiGridCDF

@[expose] public section

/-! Identification of a glued finite Parisi potential with its genuine
Cole--Hopf slab, including the mesh boundary by continuity. -/

open Set MeasureTheory ProbabilityTheory Real

namespace Paper

open SpinGlass SpinGlass.Targets

theorem parisiFinitePotentialAux_eq_slab {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {p j : ℕ} (hp : p ≤ k + 1) (hjp : k + 2 - p ≤ j) (hj : j ≤ k + 2)
    {t : ℝ} (ht : t ∈ Ioc (s.q p) (s.q (p + 1))) (x : ℝ) :
    parisiFinitePotentialAux s β j t x =
      parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : j + 1 = k + 2 - p
    · have hji : j = k + 1 - p := by omega
      have hmi : k + 1 - j = p := by omega
      have hqi : k + 2 - j = p + 1 := by omega
      change (if t ≤ s.q (k + 2 - j) then
        parisiSlabPotential s β j (s.m (k + 1 - j)) (s.q (k + 2 - j)) t x
        else parisiFinitePotentialAux s β j t x) = _
      rw [hmi, hqi, ite_eq_left ht.2, hji]
    · have hbase : k + 2 - p ≤ j := by omega
      have hq : s.q (k + 2 - j) ≤ s.q p :=
        s.q_mono' p (by omega) (k + 2 - j) (by omega)
      have hnot : ¬t ≤ s.q (k + 2 - j) := by linarith [ht.1]
      simpa only [parisiFinitePotentialAux, ite_eq_right hnot] using ih hbase (by omega)

theorem parisiFinitePotentialAux_eq_slab_closed {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {p : ℕ} (hp : p ≤ k + 1) (hq : s.q p < s.q (p + 1))
    {t : ℝ} (ht : t ∈ Icc (s.q p) (s.q (p + 1))) (x : ℝ) :
    parisiFinitePotentialAux s β (k + 2) t x =
      parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x := by
  have hU := (continuous_parisiFiniteAux s β (j := k + 2) le_rfl).1.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  have hS := (continuous_parisiSlab s β (k + 1 - p)
    (s.m_nonneg (p := p) (by omega)) (s.q (p + 1))).1.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
  have hclosed : IsClosed {r : ℝ | parisiFinitePotentialAux s β (k + 2) r x =
      parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) r x} :=
    isClosed_eq hU hS
  have hsub : Ioc (s.q p) (s.q (p + 1)) ⊆
      {r : ℝ | parisiFinitePotentialAux s β (k + 2) r x =
        parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) r x} :=
    fun r hr => parisiFinitePotentialAux_eq_slab s β hp (by omega) le_rfl hr x
  apply closure_minimal hsub hclosed
  rw [closure_Ioc hq.ne]
  exact ht

theorem parisiFinitePotential_eq_slab {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {p : ℕ} (hp : p ≤ k + 1) (hq : s.q p < s.q (p + 1))
    {t : ℝ} (ht : t ∈ Icc (s.q p) (s.q (p + 1))) (x : ℝ) :
    parisiFinitePotential s β (t, x) =
      parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x := by
  have ht0 : 0 ≤ t := (s.q_nonneg (p := p) (by omega)).trans ht.1
  have ht1 : t ≤ 1 := ht.2.trans (s.q_le_one (p := p + 1) (by omega))
  simpa only [parisiFinitePotential, Prod.fst, Prod.snd,
    min_eq_right ht1, max_eq_right ht0] using
    parisiFinitePotentialAux_eq_slab_closed s β hp hq ht x

theorem hasDerivAt_parisiFinitePotential_spatial {k : ℕ} (s : RSBScheme k)
    (β t x : ℝ) :
    HasDerivAt (fun y => parisiFinitePotential s β (t, y))
      (parisiFiniteGradient s β (t, x)) x :=
  (parisiFiniteAux_C2 s β (k + 2) (max 0 (min 1 t))).1 x

theorem parisiFiniteGradient_eq_slab {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {p : ℕ} (hp : p ≤ k + 1) (hq : s.q p < s.q (p + 1))
    {t : ℝ} (ht : t ∈ Icc (s.q p) (s.q (p + 1))) (x : ℝ) :
    parisiFiniteGradient s β (t, x) =
      parisiSlabGradient s β (k + 1 - p) (s.m p) (s.q (p + 1)) t x := by
  have hd := hasDerivAt_parisiFinitePotential_spatial s β t x
  have he : (fun y => parisiFinitePotential s β (t, y)) =
      parisiSlabPotential s β (k + 1 - p) (s.m p) (s.q (p + 1)) t :=
    funext (parisiFinitePotential_eq_slab s β hp hq ht)
  rw [he] at hd
  exact hd.unique (hasDerivAt_parisiSlabPotential_spatial s β (k + 1 - p)
    (s.m p) (s.q (p + 1)) t x)

theorem exists_parisiFinite_right_cell {k : ℕ} (s : RSBScheme k) {t : ℝ}
    (ht : t ∈ Ico 0 1) :
    ∃ p : ℕ, p ≤ k + 1 ∧ t ∈ Ico (s.q p) (s.q (p + 1)) ∧ s.q p < s.q (p + 1) := by
  have hex : ∃ i : ℕ, i ≤ k + 2 ∧ t < s.q i :=
    ⟨k + 2, le_rfl, by simpa only [s.q_top] using ht.2⟩
  let i := Nat.find hex
  have hi : i ≤ k + 2 ∧ t < s.q i := Nat.find_spec hex
  have hi0 : 0 < i := by
    by_contra hn
    have he : i = 0 := by omega
    rw [he, s.q_zero] at hi
    linarith [ht.1]
  let p := i - 1
  have hp : p ≤ k + 1 := by dsimp [p]; omega
  have he : p + 1 = i := by dsimp [p]; omega
  have hlow : s.q p ≤ t := by
    by_contra hn
    have hpred : p ≤ k + 2 ∧ t < s.q p := ⟨by omega, lt_of_not_ge hn⟩
    have hmin : i ≤ p := Nat.find_min' hex hpred
    dsimp [p] at hmin
    omega
  have hupp : t < s.q (p + 1) := by simpa only [he] using hi.2
  exact ⟨p, hp, ⟨hlow, hupp⟩, hlow.trans_lt hupp⟩

end Paper
