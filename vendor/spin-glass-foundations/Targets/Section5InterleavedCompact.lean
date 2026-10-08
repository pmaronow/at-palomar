module

public import Targets.Section5CompactWitness
public import Targets.Section5InterleavedScalarContinuity
public import Targets.Section5InterleavedTimeZero

@[expose] public section

/-!
# Uniform scalar comparison on compact trial domains

The actual scalar gap is continuous on each admissible trial strip. Compact
sets of strict scalar witnesses therefore give uniform original-free-energy
bounds. This is not yet the global Theorem 2.4: adjacent trial domains and
the other overlap regimes must still be assembled.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace SpinGlass.Targets

/-- Continuity of the genuine scalar deficit, including the sign boundary
when it belongs to the trial strip, at every fixed lambda. -/
theorem continuousOn_section5InterleavedLambdaDeficit_trial {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) (r : ℕ) {j : ℕ}
    (hj : j ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ)
      {z | |z.2| ∈ Icc (s.q (j - 1)) (s.q j)} := by
  exact (continuousOn_const.sub
    (continuousOn_section5InterleavedScalarV_trial s β h r hj ℓ)).add
    (continuousOn_const.mul continuous_snd.continuousOn)

/-- Compactness upgrades actual scalar witnesses on one trial strip to a
uniform positive gap before every system size and disorder. Positivity of
the scalar witnesses remains an explicit input of this reusable adapter. -/
theorem exists_uniform_constrainedPhi_gap_on_compact_trial
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) 1)
    (hu : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j))
    (hpos : ∀ z ∈ S, ∃ ℓ, 0 < section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤ 2 * guerraPsi s β h z.1 - δ := by
  obtain ⟨δ, hδ, H⟩ := exists_uniform_positive_of_compact_witnesses hS
    (fun ℓ z => section5InterleavedLambdaDeficit s β h r j z.1 z.2 ℓ)
    (fun ℓ => (continuousOn_section5InterleavedLambdaDeficit_trial s β h r hj ℓ).mono hu)
    hpos
  refine ⟨δ, hδ, ?_⟩
  intro z hz n hn sk hatt
  obtain ⟨ℓ, hℓ⟩ := H z hz
  have HB := constrainedPhi_le_guerraPsi_sub_interleavedLambdaDeficit hn s β h sk
    hr0 hr hj0 hj (ht z hz) (hu z hz) hatt ℓ
  linarith

/-- A genuine compact uniform bound in the left outside-neighbor region.
The trial interval is left-closed/right-open so the active witness persists;
physical time zero is included by a proved nonzero-lambda scalar gain.
Stationarity is the actual baseline-slope identity already proved for reduced
minimizers, not an assumed pressure estimate. -/
theorem exists_uniform_constrainedPhi_left_outside_trial
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ}
    (hβ : β ≠ 0) (hr : r ≤ k + 1) (hj0 : 1 ≤ j) (hjr : j < r)
    (hm : StrictMono (fun p : Fin (k + 2) => s.m p))
    (hq : s.q (r - 1) < s.q r)
    (hQ : section4TVarianceQ s β h r (s.m (r - 1)) 0 = s.q r)
    {t₀ : ℝ} (ht₀ : t₀ < 1) {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (ht : ∀ z ∈ S, z.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ z ∈ S, z.2 ∈ Ico (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, ∀ z ∈ S, ∀ {n : ℕ}, 0 < n → ∀ sk : SKDisorder (Ω := Ω) n β h,
      (∃ σ τ : Config n, overlap n σ τ = z.2) →
      constrainedPhi n s β h sk.U (k + 2 - r) z.1 z.2 ≤ 2 * guerraPsi s β h z.1 - δ := by
  have hr0 : 1 ≤ r := by omega
  have hj : j ≤ k + 1 := by omega
  have hu0 : ∀ z ∈ S, 0 ≤ z.2 := fun z hz =>
    (s.q_nonneg (p := j - 1) (by omega)).trans (hu z hz).1
  have htrial : ∀ z ∈ S, |z.2| ∈ Icc (s.q (j - 1)) (s.q j) := by
    intro z hz
    rw [abs_of_nonneg (hu0 z hz)]
    exact ⟨(hu z hz).1, (hu z hz).2.le⟩
  apply exists_uniform_constrainedPhi_gap_on_compact_trial s β h hr0 hr hj0 hj hS
    (fun z hz => ⟨(ht z hz).1, (ht z hz).2.trans ht₀.le⟩) htrial
  intro z hz
  by_cases htzero : z.1 = 0
  · obtain ⟨ℓ, H⟩ := section5InterleavedScalarV_time_zero_lambda_gain_Q s β h hr0 hr hj z.2
    rw [hQ] at H
    have hlt : z.2 < s.q r :=
      (hu z hz).2.trans_le (s.q_mono' r (by omega) j hjr.le)
    have hsq : 0 < (s.q r - z.2) ^ 2 / 2 :=
      div_pos (sq_pos_of_pos (sub_pos.mpr hlt)) (by norm_num)
    refine ⟨ℓ, ?_⟩
    dsimp only [section5InterleavedLambdaDeficit]
    rw [htzero]
    linarith
  · have htp : 0 < z.1 := lt_of_le_of_ne (ht z hz).1 (Ne.symm htzero)
    have htime : z.1 < 1 := (ht z hz).2.trans_lt ht₀
    have H := section5InterleavedScalarV_zero_lt_left_outside s β h
      ⟨htp.le, htime.le⟩ hr hj0 hjr (htrial z hz) hm
      (by rw [abs_of_nonneg (hu0 z hz)];
          exact mul_pos htp (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr (hu z hz).2)))
      (mul_pos (sub_pos.mpr htime) (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq)))
    refine ⟨0, ?_⟩
    simp only [section5InterleavedLambdaDeficit, zero_mul, add_zero]
    exact sub_pos.mpr H

end SpinGlass.Targets
