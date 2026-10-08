module

public import Targets.Section5InterleavedStrict
public import Targets.Section5MixedReflection

@[expose] public section

/-!
# Negative-overlap strictness inside neighboring intervals

The first positive-mass interpolation tag is opposite. An earlier physical
shared tag has positive variance when either the first overlap is positive,
or the first overlap is zero and the physical cutoff is at least two. Stable
source ordering includes the equal-mass physical/interpolation tie exactly.
These explicit witnesses give genuine strictness of the actual mixed scalar
endpoint; no active-tag or ordering conclusion is assumed in the final results.
The reflected dual mechanism includes the first trial interval and its exact
endpoint when the first overlap is positive. The assembled theorem covers all
negative overlaps in the current trial indexing for physical cutoff at least
two, including zero first overlap. It does not include the final trial interval
above `q_(k+1)` or a full varying-time pressure comparison.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

private theorem strict_reference_of_opposite_shared {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (t u : ℝ)
    (b c : Section5MassTag k)
    (hbc : (section5Interleaving s r j).symm b < (section5Interleaving s r j).symm c)
    (hb : section5TaggedMode r j (decide (u < 0)) b = .shared)
    (hc : section5TaggedMode r j (decide (u < 0)) c = .opposite)
    (hcm : 0 < section5TaggedMass s r j c)
    (hbv : 0 < section5TaggedVariance s β t |u| j b)
    (hcv : 0 < section5TaggedVariance s β t |u| j c) :
    section5InterleavedScalarV s β h r j t u 0 <
      2 * section5InterleavedScalarReference s β r j t u h := by
  let bi := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm b).val
  let ci := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm c).val
  have hib : bi < (k + 2) + (k + 3) := by dsimp [bi]; omega
  have hicb : ci < bi := by dsimp [ci, bi]; omega
  have hbt : section5ReverseTag s r j bi = b := section5ReverseTag_at_tag s r j b
  have hct : section5ReverseTag s r j ci = c := section5ReverseTag_at_tag s r j c
  have H := mixedScalarCascade_lt_of_opposite_before_shared
    (section5ReverseMode s r j (decide (u < 0))) (section5ReverseMass s r j)
    (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    (section5ReverseMass_nonneg s r hj) (fun _ => continuous_const)
    (section5ReverseMode_scalarMass_mem_Icc s r hj (decide (u < 0))) hicb hib ()
    (by simpa only [section5ReverseMode, hct] using hc)
    (by simpa only [section5ReverseMass, hct] using hcm)
    (by simpa only [section5ReverseVariance, hct] using hcv)
    (by simpa only [section5ReverseMode, hbt] using hb)
    (by simpa only [section5ReverseVariance, hbt] using hbv) h h
  simpa only [section5InterleavedScalarV, section5InterleavedScalarReference, two_mul] using H

private theorem interpolation_one_variance_pos {k : ℕ} (s : RSBScheme k)
    {β t u : ℝ} {j : ℕ} (hβ : β ≠ 0) (ht : 0 < t) (hj : 2 ≤ j)
    (hq : s.q 1 < s.q 2) (hu : s.q 1 < |u|) :
    0 < section5TaggedVariance s β t |u| j (Sum.inr ⟨1, by omega⟩) := by
  change 0 < t * (β ^ 2 * (section5Rho s j |u| 2 - section5Rho s j |u| 1))
  apply mul_pos ht
  apply mul_pos (sq_pos_of_ne_zero hβ)
  by_cases hj2 : j = 2
  · subst j
    simpa [section5Rho] using sub_pos.mpr hu
  · have h2j : 2 < j := by omega
    simpa only [section5Rho, if_pos h2j, if_pos (show 1 < j by omega)] using sub_pos.mpr hq

private theorem interpolation_one_mass_pos {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : 2 ≤ j) (hm : 0 < s.m 1) :
    0 < section5TaggedMass s r j (Sum.inr ⟨1, by omega⟩) := by
  simpa only [section5TaggedMass, Sum.elim_inr, section5Mass,
    if_pos (show 1 < j by omega)] using div_pos hm (by norm_num : (0 : ℝ) < 2)

private theorem physical_zero_before_interpolation_one {k : ℕ} (s : RSBScheme k)
    {r j : ℕ} (hr : 1 ≤ r) (hj0 : 2 ≤ j) (hj : j ≤ k + 1) :
    (section5Interleaving s r j).symm (Sum.inl ⟨0, by omega⟩) <
      (section5Interleaving s r j).symm (Sum.inr ⟨1, by omega⟩) := by
  have H := section5Interleaving_physical_before_interpolating_of_eq s r j
    ⟨0, by omega⟩ ⟨0, by omega⟩ (by
      simp only [section5PhysicalMass, section5Mass, if_pos (show 0 < r by omega),
        if_pos (show 0 < j by omega)])
  exact H.trans (strictMono_section5Interleaving_interpolating s r hj
    (show (⟨0, by omega⟩ : Fin (k + 3)) < ⟨1, by omega⟩ by change (0 : ℕ) < 1; omega))

private theorem physical_one_before_interpolation_one {k : ℕ} (s : RSBScheme k)
    {r j : ℕ} (hr : 2 ≤ r) (hj : 2 ≤ j) :
    (section5Interleaving s r j).symm (Sum.inl ⟨1, by omega⟩) <
      (section5Interleaving s r j).symm (Sum.inr ⟨1, by omega⟩) := by
  apply section5Interleaving_physical_before_interpolating_of_eq
  simp only [section5PhysicalMass, section5Mass, if_pos (show 1 < r by omega),
    if_pos (show 1 < j by omega)]

private theorem reference_le_original {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    (r : ℕ) {j : ℕ} {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    2 * section5InterleavedScalarReference s β r j t u h ≤ 2 * parisiF s β (k + 2) h := by
  rw [section5InterleavedScalarReference_eq_list]
  exact mul_le_mul_of_nonneg_left
    (section5InterleavedScalarSteps_cascade_le_parisiF s β r ht hj0 hj hu h) (by norm_num)

/-- For positive first overlap, the mass-zero frozen physical field spreads
the strict opposite-field comparison to every external field. The active
opposite tag is proved from `m₁>0`, `q₂>q₁` and `|u|>q₁`. -/
theorem section5InterleavedScalarV_zero_lt_negative_of_q1_pos {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 1 ≤ r)
    (hj0 : 2 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu1 : s.q 1 < |u|) (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  have H := strict_reference_of_opposite_shared s β h r hj t u
    (Sum.inl ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)
    (physical_zero_before_interpolation_one s hr hj0 hj)
    (by simp [section5TaggedMode, show 0 < r by omega])
    (by simp [section5TaggedMode, show 1 < j by omega, huneg])
    (interpolation_one_mass_pos s r hj0 hm)
    (by
      simpa only [section5TaggedVariance, Sum.elim_inl, s.q_zero, sub_zero] using
        mul_pos (sub_pos.mpr ht.2) (mul_pos (sq_pos_of_ne_zero hβ) hq1))
    (interpolation_one_variance_pos s hβ ht.1 hj0 hq hu1)
  exact H.trans_le (reference_le_original s β h r ⟨ht.1.le, ht.2.le⟩ (by omega) hj hu)

/-- If the physical cutoff is at least two, physical tag one works even when
the first overlap vanishes. Its tie with interpolation tag one is handled by
the actual stable physical-before-interpolation ordering. -/
theorem section5InterleavedScalarV_zero_lt_negative_of_two_le_r {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 2 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0) (hu1 : s.q 1 < |u|)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  have H := strict_reference_of_opposite_shared s β h r hj t u
    (Sum.inl ⟨1, by omega⟩) (Sum.inr ⟨1, by omega⟩)
    (physical_one_before_interpolation_one s hr hj0)
    (by simp [section5TaggedMode, show 1 < r by omega])
    (by simp [section5TaggedMode, show 1 < j by omega, huneg])
    (interpolation_one_mass_pos s r hj0 hm)
    (mul_pos (sub_pos.mpr ht.2) (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq)))
    (interpolation_one_variance_pos s hβ ht.1 hj0 hq hu1)
  exact H.trans_le (reference_le_original s β h r ⟨ht.1.le, ht.2.le⟩ (by omega) hj hu)

/-- Zero first overlap leaves no negative initial interval: every negative
overlap covered by the existing trial indexing has the genuine strict bound,
provided the physical cutoff is at least two and the next overlap is positive. -/
theorem section5InterleavedScalarV_zero_lt_negative_of_q1_zero {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq1 : s.q 1 = 0) (hq2 : 0 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  have hup : 0 < |u| := abs_pos.mpr (ne_of_lt huneg)
  have hj2 : 2 ≤ j := by
    by_contra hn
    have hj1 : j = 1 := by omega
    have H := hu.2
    rw [hj1, hq1] at H
    linarith
  exact section5InterleavedScalarV_zero_lt_negative_of_two_le_r s β h hβ ht hr hj2 hj hm
    (by simpa only [hq1] using hq2) huneg (by simpa only [hq1] using hup) hu

private theorem strict_reference_of_shared_opposite {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (t u : ℝ)
    (b c : Section5MassTag k)
    (hbc : (section5Interleaving s r j).symm b < (section5Interleaving s r j).symm c)
    (hb : section5TaggedMode r j (decide (u < 0)) b = .opposite)
    (hc : section5TaggedMode r j (decide (u < 0)) c = .shared)
    (hcm : 0 < section5TaggedMass s r j c)
    (hbv : 0 < section5TaggedVariance s β t |u| j b)
    (hcv : 0 < section5TaggedVariance s β t |u| j c) :
    section5InterleavedScalarV s β h r j t u 0 <
      2 * section5InterleavedScalarReference s β r j t u h := by
  let bi := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm b).val
  let ci := (k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm c).val
  have hib : bi < (k + 2) + (k + 3) := by dsimp [bi]; omega
  have hicb : ci < bi := by dsimp [ci, bi]; omega
  have hbt : section5ReverseTag s r j bi = b := section5ReverseTag_at_tag s r j b
  have hct : section5ReverseTag s r j ci = c := section5ReverseTag_at_tag s r j c
  have H := mixedScalarCascade_lt_of_shared_before_opposite
    (section5ReverseMode s r j (decide (u < 0))) (section5ReverseMass s r j)
    (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    (section5ReverseMass_nonneg s r hj) (fun _ => continuous_const)
    (section5ReverseMode_scalarMass_mem_Icc s r hj (decide (u < 0))) hicb hib ()
    (by simpa only [section5ReverseMode, hct] using hc)
    (by simpa only [section5ReverseMass, hct] using hcm)
    (by simpa only [section5ReverseVariance, hct] using hcv)
    (by simpa only [section5ReverseMode, hbt] using hb)
    (by simpa only [section5ReverseVariance, hbt] using hbv) h h
  simpa only [section5InterleavedScalarV, section5InterleavedScalarReference, two_mul] using H

private theorem interpolation_zero_variance_pos {k : ℕ} (s : RSBScheme k)
    {β t u : ℝ} {j : ℕ} (hβ : β ≠ 0) (ht : 0 < t) (hj : 1 ≤ j)
    (hq : 0 < s.q 1) (hu : u < 0) :
    0 < section5TaggedVariance s β t |u| j (Sum.inr ⟨0, by omega⟩) := by
  change 0 < t * (β ^ 2 * (section5Rho s j |u| 1 - section5Rho s j |u| 0))
  apply mul_pos ht
  apply mul_pos (sq_pos_of_ne_zero hβ)
  by_cases hj1 : j = 1
  · subst j
    simpa [section5Rho, s.q_zero] using abs_pos.mpr (ne_of_lt hu)
  · have h1j : 1 < j := by omega
    simpa only [section5Rho, if_pos h1j, if_pos (show 0 < j by omega), s.q_zero,
      sub_zero] using hq

private theorem interpolation_zero_before_physical_one {k : ℕ} (s : RSBScheme k)
    {r j : ℕ} (hr : 2 ≤ r) (hj : 1 ≤ j) (hm : 0 < s.m 1) :
    (section5Interleaving s r j).symm (Sum.inr ⟨0, by omega⟩) <
      (section5Interleaving s r j).symm (Sum.inl ⟨1, by omega⟩) := by
  by_contra hn
  have H := monotone_section5InterleavedMass s r j (le_of_not_gt hn)
  simp only [section5InterleavedMass, Equiv.apply_symm_apply, section5TaggedMass,
    Sum.elim_inl, Sum.elim_inr, section5PhysicalMass, section5Mass,
    if_pos (show 1 < r by omega), if_pos (show 0 < j by omega), s.m_zero,
    zero_div] at H
  linarith

/-- The dual reflection mechanism covers every negative overlap in the current
trial indexing when `q₁>0` and the physical cutoff is at least two. In particular,
the exact boundary `|u|=q₁` and the first trial interval are included. -/
theorem section5InterleavedScalarV_zero_lt_negative_of_q1_pos_all_trials {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq1 : 0 < s.q 1) (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  have H := strict_reference_of_shared_opposite s β h r hj t u
    (Sum.inr ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩)
    (interpolation_zero_before_physical_one s hr hj0 hm)
    (by simp [section5TaggedMode, show 0 < j by omega, huneg])
    (by simp [section5TaggedMode, show 1 < r by omega])
    (by simpa only [section5TaggedMass, Sum.elim_inl, section5PhysicalMass,
      if_pos (show 1 < r by omega)] using div_pos hm (by norm_num : (0 : ℝ) < 2))
    (interpolation_zero_variance_pos s hβ ht.1 hj0 hq1 huneg)
    (mul_pos (sub_pos.mpr ht.2) (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq)))
  exact H.trans_le (reference_le_original s β h r ⟨ht.1.le, ht.2.le⟩ hj0 hj hu)

/-- All negative overlaps in the current trial indexing have a strict actual
mixed scalar endpoint for physical cutoff at least two. The first overlap may
be zero, and no outside-neighbor restriction or breakpoint exclusion is imposed. -/
theorem section5InterleavedScalarV_zero_lt_negative {k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    section5InterleavedScalarV s β h r j t u 0 < 2 * parisiF s β (k + 2) h := by
  rcases (s.q_nonneg (show 1 ≤ k + 2 by omega)).eq_or_lt with hzero | hpos
  · exact section5InterleavedScalarV_zero_lt_negative_of_q1_zero s β h hβ ht hr hj0 hj hm
      hzero.symm (by linarith) huneg hu
  · exact section5InterleavedScalarV_zero_lt_negative_of_q1_pos_all_trials s β h hβ ht hr
      hj0 hj hm hpos hq huneg hu

/-- A positive negative-overlap endpoint deficit is fixed before system size
and disorder. Its value is the actual scalar deficit, not an assumed constant. -/
theorem exists_section5Interleaved_zero_gap_negative
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {k : ℕ} (s : RSBScheme k) (β h : ℝ) {r j : ℕ} {t u : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j)) :
    ∃ δ > 0, δ = section5InterleavedScalarDeficit s β h r j t u ∧
      ∀ {n : ℕ} (_hn : 0 < n) (U : Ω → EnergySpace n),
        (∃ σ τ : Config n, overlap n σ τ = u) →
        section5InterleavedInterpolation n s β h U r j t u 0 ≤
          2 * Real.log 2 + 2 * parisiF s β (k + 2) h - δ := by
  refine ⟨section5InterleavedScalarDeficit s β h r j t u, ?_, rfl, ?_⟩
  · exact sub_pos.mpr (section5InterleavedScalarV_zero_lt_negative s β h hβ ht hr hj0 hj
      hm hq huneg hu)
  · intro n hn U hatt
    exact section5InterleavedInterpolation_zero_le_sub_deficit hn s β h U r hj
      ⟨ht.1.le, ht.2.le⟩ hu hatt

/-- Strictness for the actual negative-overlap zero-time interpolation endpoint. -/
theorem section5InterleavedInterpolation_zero_lt_negative
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0 < n) (s : RSBScheme k) (β h : ℝ) (U : Ω → EnergySpace n)
    {r j : ℕ} {t u : ℝ} (hβ : β ≠ 0) (ht : t ∈ Set.Ioo 0 1) (hr : 2 ≤ r)
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (hm : 0 < s.m 1)
    (hq : s.q 1 < s.q 2) (huneg : u < 0)
    (hu : |u| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hatt : ∃ σ τ : Config n, overlap n σ τ = u) :
    section5InterleavedInterpolation n s β h U r j t u 0 <
      2 * Real.log 2 + 2 * parisiF s β (k + 2) h := by
  have H := section5InterleavedInterpolation_zero_le hn s β h U r hj ⟨ht.1.le, ht.2.le⟩ hu hatt
  have H' := section5InterleavedScalarV_zero_lt_negative s β h hβ ht hr hj0 hj hm hq huneg hu
  linarith

end SpinGlass.Targets
