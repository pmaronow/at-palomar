module

/-
# The finite-overlap deduction in Proposition 2.3

Theorem 2.4 is kept as an explicit hypothesis in this reusable module. It combines a quadratic
constrained-pressure bound with the proved Proposition 2.5, then sums over the
actual finite set of attainable overlaps. It does not assert the missing
quadratic bound or remove the strict-positive-mass restriction; both are supplied
by downstream modules.
-/
public import Targets.TalagrandProposition25
public import Targets.ReplicaMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

/-- The actual attainable overlaps, without multiplicities of spin pairs. -/
noncomputable def attainableOverlaps (n : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun p : Config n × Config n => overlap n p.1 p.2)

theorem mem_attainableOverlaps {n : ℕ} {u : ℝ} :
    u ∈ attainableOverlaps n ↔ ∃ σ τ : Config n, overlap n σ τ = u := by
  classical
  simp [attainableOverlaps]

/-- In the Ising SK model there are at most `N+1` overlaps (a slightly sharper
count than the paper's sufficient `2N+1`). The zero-size convention also works. -/
theorem card_attainableOverlaps_le (n : ℕ) : (attainableOverlaps n).card ≤ n + 1 := by
  classical
  let f : ℕ → ℝ := fun j => (1 / (n : ℝ)) * (2 * j - n)
  have hsub : attainableOverlaps n ⊆ (Finset.range (n + 1)).image f := by
    intro u hu
    obtain ⟨σ, τ, rfl⟩ := mem_attainableOverlaps.mp hu
    let I := Finset.univ.filter (fun i : Fin n => σ i = τ i)
    refine Finset.mem_image.mpr ⟨I.card, ?_, ?_⟩
    · have hcard : I.card ≤ n := by
        simpa using (Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => σ i = τ i))
      exact Finset.mem_range.mpr (by omega)
    · have hspin (i : Fin n) : spin n σ i * spin n τ i =
          2 * (if σ i = τ i then (1 : ℝ) else 0) - 1 := by
        simp only [spin]
        cases hσ : σ i <;> cases hτ : τ i <;> norm_num
      simp only [f, overlap, hspin, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      congr 2
      simp [I]
  exact (Finset.card_le_card hsub).trans (by
    simpa using (Finset.card_image_le (s := Finset.range (n + 1)) (f := f)))

theorem guerraOuterAvg_finset_sum {ι : Type*} {n k : ℕ} (s : RSBScheme k)
    (β : ℝ) (U : EnergySpace n) (h : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d l : ℕ) (I : Finset ι) (F : ι → (Fin n → ℝ) → ℝ) (C : ι → ℝ)
    (hF : ∀ i ∈ I, Measurable (F i)) (hb : ∀ i ∈ I, ∀ x, |F i x| ≤ C i)
    (x : Fin n → ℝ) :
    guerraOuterAvg n s β U h t d (fun y => ∑ i ∈ I, F i y) l x =
      ∑ i ∈ I, guerraOuterAvg n s β U h t d (F i) l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    simp only [guerraOuterAvg, show guerraOuterAvg n s β U h t d
      (fun y => ∑ i ∈ I, F i y) l =
      (fun y => ∑ i ∈ I, guerraOuterAvg n s β U h t d (F i) l y) from funext ih]
    exact guerraStepAvg_finset_sum n s β U h ht (d + l) I _ (fun i hi =>
      GuerraGrowth.of_bound (measurable_guerraOuterAvg n s β U h t d (hF i hi) l)
        (guerraOuterAvg_abs_le n s β U h ht d l (hF i hi) (hb i hi))) x

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Finite additivity for the genuine replica functional; all nested and outer
integrals are justified using the existing bounded-observable estimates. -/
theorem guerraReplicaMeasure_finset_sum {ι : Type*} {n k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {U : Ω → EnergySpace n} (hU : Measurable U)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (d : ℕ) (I : Finset ι)
    (K : ι → Config n → Config n → ℝ) (C : ι → ℝ)
    (hb : ∀ i ∈ I, ∀ σ τ, |K i σ τ| ≤ C i) :
    guerraReplicaMeasure n s β h U t d (fun σ τ => ∑ i ∈ I, K i σ τ) =
      ∑ i ∈ I, guerraReplicaMeasure n s β h U t d (K i) := by
  have havg (V : EnergySpace n) (y : Fin n → ℝ) :
      guerraReplicaAvg n s β V h t d (fun σ τ => ∑ i ∈ I, K i σ τ) y =
        ∑ i ∈ I, guerraReplicaAvg n s β V h t d (K i) y := by
    simp only [guerraReplicaAvg, Finset.mul_sum]
    calc
      _ = ∑ σ, ∑ i ∈ I, ∑ τ,
          guerraProb n s β V h t d σ y * guerraProb n s β V h t d τ y * K i σ τ :=
        Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  unfold guerraReplicaMeasure
  simp_rw [show ∀ V, guerraReplicaAvg n s β V h t d
    (fun σ τ => ∑ i ∈ I, K i σ τ) =
    (fun y => ∑ i ∈ I, guerraReplicaAvg n s β V h t d (K i) y) from
      fun V => funext (havg V)]
  calc
    _ = ∫ ω, ∑ i ∈ I, guerraOuterAvg n s β (U ω) h t d
        (guerraReplicaAvg n s β (U ω) h t d (K i)) (k + 2 - d) 0 ∂ℙ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact guerraOuterAvg_finset_sum s β (U ω) h ht d (k + 2 - d) I _ C
        (fun i _ => (measurable_guerraReplicaAvg_joint s β h t d (K i)).comp
          (measurable_const.prodMk measurable_id))
        (fun i hi => guerraReplicaAvg_abs_le n s β (U ω) h ht d (hb i hi)) 0
    _ = _ := integral_finsetSum I (fun i hi =>
      integrable_guerraOuterReplica s β h hU ht d (k + 2 - d) (hb i hi) 0)

/-- A union bound over overlap values, rather than over exponentially many spin
pairs. Its factor is linear in the system size and uniform in the split. -/
theorem guerraReplicaMeasure_overlapTail_le {n k : ℕ} (s : RSBScheme k)
    (β h : ℝ) {U : Ω → EnergySpace n} (hU : Measurable U)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (d : ℕ) (q a : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ u ∈ attainableOverlaps n, a ≤ (u - q) ^ 2 →
      guerraReplicaMeasure n s β h U t d (overlapEvent n u) ≤ B) :
    guerraReplicaMeasure n s β h U t d
      (fun σ τ => if a ≤ (overlap n σ τ - q) ^ 2 then 1 else 0) ≤ (n + 1 : ℝ) * B := by
  classical
  let I := (attainableOverlaps n).filter (fun u => a ≤ (u - q) ^ 2)
  have he : (fun σ τ : Config n => if a ≤ (overlap n σ τ - q) ^ 2 then (1 : ℝ) else 0) =
      (fun σ τ => ∑ u ∈ I, overlapEvent n u σ τ) := by
    funext σ τ
    have hm := mem_attainableOverlaps.mpr ⟨σ, τ, rfl⟩
    simp [I, overlapEvent, hm]
  rw [he, guerraReplicaMeasure_finset_sum s β h hU ht d I (overlapEvent n)
    (fun _ => 1) (fun u _ σ τ => by unfold overlapEvent; split_ifs <;> norm_num)]
  calc
    _ ≤ ∑ _u ∈ I, B := Finset.sum_le_sum (fun u hu =>
      hpoint u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2)
    _ = (I.card : ℝ) * B := by simp
    _ ≤ (n + 1 : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc : I.card ≤ n + 1 := (Finset.card_filter_le (s := attainableOverlaps n)
        (p := fun u => a ≤ (u - q) ^ (2 : ℕ))).trans (card_attainableOverlaps_le n)
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_le (α := ℝ).mpr hc)

/-- The finite-size deduction on p. 232, conditional on the quadratic bound
of Theorem 2.4. In the exact-covariance SK model `c(N)=0`, so no additional
large-size error is needed to apply Proposition 2.5 with deficit `η/K`. -/
theorem talagrand_replica_tail_of_quadratic_bound {n k : ℕ}
    (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k) (hn : 0 < n)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) (hd : d ≤ k + 1) {K η : ℝ} (hK : 0 < K) (hη : 0 < η)
    (hquad : ∀ u ∈ attainableOverlaps n,
      constrainedPhi n s β h sk.U d t u ≤
        2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    guerraReplicaMeasure n s β h sk.U t d
      (fun σ τ => if 2 * K * guerraGap n s β h sk.U t + η ≤
        (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0) ≤
      (n + 1 : ℝ) * (talagrandEventConstant s β (η / K) *
        Real.exp (-(n : ℝ) / talagrandEventConstant s β (η / K))) := by
  have hε : 0 < η / K := div_pos hη hK
  apply guerraReplicaMeasure_overlapTail_le s β h sk.hU.repr_measurable ht d
    (s.q (k + 2 - d)) _
    (mul_nonneg (talagrandEventConstant_pos s β hs hε).le (Real.exp_pos _).le)
  intro u hu htail
  apply talagrand_proposition_2_5 sk s hn hs ht u (mem_attainableOverlaps.mp hu) d hd hε
  have he : 2 * guerraGap n s β h sk.U t + η / K ≤
      (u - s.q (k + 2 - d)) ^ 2 / K := by
    apply (le_div_iff₀ hK).mpr
    have hc : η / K * K = η := div_mul_cancel₀ η hK.ne'
    nlinarith only [htail, hc]
  dsimp only [guerraGap] at he
  linarith only [hquad u hu, he]

/-- The same bound for the actual mass-weighted overlap tail in the Guerra
remainder. No summation factor depending on the number of RSB levels is lost. -/
theorem guerraOverlapTail_of_quadratic_bound {n k : ℕ}
    (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k) (hn : 0 < n)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {K η : ℝ} (hK : 0 < K) (hη : 0 < η)
    (hquad : ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
      constrainedPhi n s β h sk.U d t u ≤
        2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    guerraOverlapTail n s β h sk.U t (2 * K * guerraGap n s β h sk.U t + η) ≤
      (n + 1 : ℝ) * (talagrandEventConstant s β (η / K) *
        Real.exp (-(n : ℝ) / talagrandEventConstant s β (η / K))) := by
  apply guerraOverlapTail_le_of_replicaMeasure s β h sk.hU.repr_measurable ht
  intro d hd1 hd
  exact talagrand_replica_tail_of_quadratic_bound sk s hn hs ht d hd hK hη (hquad d hd1 hd)

/-- The linear overlap-count factor is absorbed by exponential decay. -/
theorem tendsto_overlap_union_bound {C : ℝ} (hC : 0 < C) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) * (C * Real.exp (-(n : ℝ) / C))) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(1 / C) * n)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / C) (by positivity)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (fun n : ℕ => Real.exp (-(1 / C) * n)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, Function.comp_def] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / C) (by positivity)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  convert ((hfirst.add hzero).mul_const C) using 1
  · funext n
    rw [show -(1 / C) * (n : ℝ) = -(n : ℝ) / C by ring]
    ring
  · simp

/-- Proposition 2.3's per-level conclusion, conditional only on a uniform
Theorem 2.4 quadratic estimate for the fixed positive-mass scheme. The tail
coefficient `2*K` is independent of `η`, `N`, `t`, and the replica level. -/
theorem talagrand_proposition_2_3_of_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    (hs : 0 < s.m 1) {t₀ K : ℝ} (ht₀ : t₀ < 1) (hK : 0 < K)
    (hquad : ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 →
        guerraReplicaMeasure n s β h (sk n).U t d
          (fun σ τ => if 2 * K * guerraGap n s β h (sk n).U t + η ≤
            (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0) ≤ η := by
  intro η hη
  have hC := talagrandEventConstant_pos s β hs (div_pos hη hK)
  have hsmall := (tendsto_overlap_union_bound hC).eventually (gt_mem_nhds hη)
  filter_upwards [hquad, eventually_gt_atTop 0, hsmall] with n hquadn hn hsmalln
  intro t ht d hd1 hd
  exact (talagrand_replica_tail_of_quadratic_bound (sk n) s hn hs ⟨ht.1, ht.2.trans ht₀⟩
    d hd hK hη (hquadn t ht d hd1 hd)).trans hsmalln.le

/-- The conditional finite-overlap argument supplies exactly the mass-weighted
concentration input required by `guerraPhi_uniform_of_overlap_concentration`.
The quadratic estimate and positive first mass are still hypotheses. -/
theorem guerraOverlapTail_eventually_of_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    (hs : 0 < s.m 1) {t₀ K : ℝ} (ht₀ : t₀ < 1) (hK : 0 < K)
    (hquad : ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      guerraOverlapTail n s β h (sk n).U t
        (2 * K * guerraGap n s β h (sk n).U t + η) ≤ η := by
  intro η hη
  filter_upwards [talagrand_proposition_2_3_of_quadratic_bound β h sk s hs ht₀ hK hquad η hη]
    with n hn
  intro t ht
  exact guerraOverlapTail_le_of_replicaMeasure s β h (sk n).hU.repr_measurable
    ⟨ht.1, ht.2.trans ht₀⟩ (hn t ht)

/-- For a fixed positive-mass scheme, a uniform Theorem 2.4 estimate now gives
the full endpoint-safe convergence conclusion through the existing argument.
This is a deduction, not a proof of the quadratic estimate or the coincident-
level reduction required by the original Theorem 2.2. -/
theorem guerraPhi_uniform_of_quadratic_bound (β h : ℝ)
    (sk : ∀ n : ℕ, SKDisorder (Ω := Ω) n β h) {k : ℕ} (s : RSBScheme k)
    (hs : 0 < s.m 1) {t₀ K : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) 1) (hK : 0 < K)
    (hquad : ∀ᶠ n in atTop, ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ k + 1 → ∀ u ∈ attainableOverlaps n,
        constrainedPhi n s β h (sk n).U d t u ≤
          2 * guerraPsi s β h t - (u - s.q (k + 2 - d)) ^ 2 / K) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) t₀,
      |guerraPhi n s β h (sk n).U t - guerraPsi s β h t| < ε := by
  exact guerraPhi_uniform_of_overlap_concentration β h sk s ht₀
    (K := 2 * K) (by positivity)
    (guerraOverlapTail_eventually_of_quadratic_bound β h sk s hs ht₀.2 hK hquad)

end SpinGlass.Targets
