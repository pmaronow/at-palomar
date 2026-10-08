module

/- Adaptation for Lean 4.34.1: proof elaboration and API compatibility only; original theorem statements are retained. Source revisions and exact patch are recorded in PROVENANCE.json and COMPATIBILITY.patch. -/
public import Targets.Section5InterleavedScalarCore

@[expose] public section

/-!
# Joint continuity of the actual interleaved scalar comparison

Parameter substitution identifies the actual Unit-parameter definition with
the existing mixed Gaussian family. Its joint continuity is inherited from
the checked `GoodFam` theorem, not from continuity of a constrained free
energy in the overlap. Modes are fixed in each sign chart; masses are the
original fixed tagged masses, and vanishing variances require no derivatives.
-/

open MeasureTheory ProbabilityTheory Real

namespace SpinGlass.Targets

/-- Exact change of the auxiliary parameter space in the finite recursion.
This is a pointwise integral identity and has no regularity hypotheses. -/
theorem mixedScalarCascade_comp {P Q : Type*}
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (f : Q → P) (j : ℕ) (p : Q) (ℓ : ℝ) (x : ℝ × ℝ) :
    mixedScalarCascade mode m (fun i q => v i (f q)) j p ℓ x =
      mixedScalarCascade mode m v j (f p) ℓ x := by
  induction j generalizing p ℓ x with
  | zero => rfl
  | succ j ih =>
    simp only [mixedScalarCascade]
    cases mode j <;> simp only [GTFrame.finiteStep] <;>
      split_ifs <;> simp only [GTFrame.step0, GTFrame.stepM, ih]

/-- A zero-variance scalar level is exactly the identity, in every mode
and also at zero mass. -/
theorem mixedScalarCascade_succ_of_variance_zero {P : Type*}
    (mode : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (j : ℕ) (p : P) (hv : v j p = 0) (ℓ : ℝ) (x : ℝ × ℝ) :
    mixedScalarCascade mode m v (j + 1) p ℓ x = mixedScalarCascade mode m v j p ℓ x := by
  cases he : mode j <;> by_cases hm : m j = 0 <;>
    simp [mixedScalarCascade, he, GTFrame.finiteStep, GTFrame.step0, GTFrame.stepM, hm, hv]

/-- Changing modes on zero-variance levels does not change the actual
scalar recursion. Only visited nonzero levels need matching modes. -/
theorem mixedScalarCascade_congr_modes_on_nonzero {P : Type*}
    (mode mode' : ℕ → Section5GaussianMode) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (j : ℕ) (p : P)
    (hmodes : ∀ i, i < j → v i p ≠ 0 → mode i = mode' i) (ℓ : ℝ) (x : ℝ × ℝ) :
    mixedScalarCascade mode m v j p ℓ x = mixedScalarCascade mode' m v j p ℓ x := by
  induction j generalizing ℓ x with
  | zero => rfl
  | succ j ih =>
    have H := ih (fun i hi => hmodes i (by omega))
    by_cases hv : v j p = 0
    · rw [mixedScalarCascade_succ_of_variance_zero mode m v j p hv,
        mixedScalarCascade_succ_of_variance_zero mode' m v j p hv]
      exact H ℓ x
    · simp only [mixedScalarCascade, hmodes j (by omega) hv]
      cases mode' j <;> simp only [GTFrame.finiteStep] <;>
        split_ifs <;> simp only [GTFrame.step0, GTFrame.stepM, H]

/-- A fixed-sign chart of the genuine mixed lambda family. Both time and
overlap are parameters; the absolute overlap still sets the variances. -/
noncomputable def section5InterleavedScalarChart {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r j : ℕ) (negative : Bool) : (ℝ × ℝ) → ℝ → ℝ × ℝ → ℝ :=
  mixedScalarCascade (section5ReverseMode s r j negative) (section5ReverseMass s r j)
    (fun i z => section5ReverseVariance s β z.1 |z.2| r j i) ((k + 2) + (k + 3))

/-- The actual definition is exactly its fixed-sign chart at the actual sign. -/
theorem section5InterleavedScalarV_eq_chart {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r j : ℕ) (t u ℓ : ℝ) :
    section5InterleavedScalarV s β h r j t u ℓ =
      section5InterleavedScalarChart s β r j (decide (u < 0)) (t, u) ℓ (h, h) := by
  exact mixedScalarCascade_comp (section5ReverseMode s r j (decide (u < 0)))
    (section5ReverseMass s r j)
    (fun (i : ℕ) (z : ℝ × ℝ) => section5ReverseVariance s β z.1 |z.2| r j i)
    (fun _ : Unit => (t, u)) ((k + 2) + (k + 3)) () ℓ (h, h)

/-- Joint parameter/lambda/field continuity of each actual sign chart.
This includes zero masses and zero variances, with no time restriction. -/
theorem continuous_section5InterleavedScalarChart {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (negative : Bool) :
    Continuous (fun z : (ℝ × ℝ) × ℝ × (ℝ × ℝ) =>
      section5InterleavedScalarChart s β r j negative z.1 z.2.1 z.2.2) := by
  apply (mixedScalarCascade_good _ _ _ (section5ReverseMass_nonneg s r hj) ?_
    ((k + 2) + (k + 3))).contF
  intro i
  unfold section5ReverseVariance section5TaggedVariance
  cases section5ReverseTag s r j i with
  | inl p =>
    simp only [Sum.elim_inl]
    fun_prop
  | inr p =>
    simp only [Sum.elim_inr, section5Rho]
    split_ifs <;> fun_prop

/-- The actual scalar comparison varies jointly on the nonnegative sign chart. -/
theorem continuousOn_section5InterleavedScalarV_nonneg {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => section5InterleavedScalarV s β h r j z.1 z.2 ℓ)
      {z | 0 ≤ z.2} := by
  have H := (continuous_section5InterleavedScalarChart s β r hj false).comp
    (show Continuous (fun z : ℝ × ℝ => (z, ℓ, (h, h))) by fun_prop)
  apply H.continuousOn.congr
  intro z hz
  dsimp only [Function.comp_apply]
  rw [section5InterleavedScalarV_eq_chart]
  simp only [show ¬z.2 < 0 from not_lt_of_ge hz, decide_false]

/-- The actual scalar comparison varies jointly on the negative sign chart. -/
theorem continuousOn_section5InterleavedScalarV_neg {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => section5InterleavedScalarV s β h r j z.1 z.2 ℓ)
      {z | z.2 < 0} := by
  have H := (continuous_section5InterleavedScalarChart s β r hj true).comp
    (show Continuous (fun z : ℝ × ℝ => (z, ℓ, (h, h))) by fun_prop)
  apply H.continuousOn.congr
  intro z hz
  dsimp only [Function.comp_apply]
  rw [section5InterleavedScalarV_eq_chart]
  change z.2 < 0 at hz
  simp only [hz, decide_true]

/-- At zero overlap in an admissible trial interval, every interpolating
shared level has zero variance. Changing its sign is therefore an exact
identity, not an assumed symmetry in the external field. -/
theorem section5InterleavedScalarChart_zero_sign {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1)
    (hq : s.q (j - 1) = 0) (t ℓ : ℝ) (x : ℝ × ℝ) :
    section5InterleavedScalarChart s β r j true (t, 0) ℓ x =
      section5InterleavedScalarChart s β r j false (t, 0) ℓ x := by
  have hρ (p : ℕ) (hp : p ≤ j) : section5Rho s j 0 p = 0 := by
    unfold section5Rho
    split_ifs with hlt heq
    · apply le_antisymm
      · simpa only [hq] using s.q_mono' (j - 1) (by omega) p (by omega)
      · exact s.q_nonneg (by omega)
    · rfl
    · omega
  apply mixedScalarCascade_congr_modes_on_nonzero
  intro i _ hvi
  unfold section5ReverseMode
  unfold section5ReverseVariance at hvi
  cases htag : section5ReverseTag s r j i with
  | inl p => rfl
  | inr p =>
    by_cases hp : (p : ℕ) < j
    · have hv : section5TaggedVariance s β t 0 j (Sum.inr p) = 0 := by
        simp only [section5TaggedVariance, Sum.elim_inr, hρ (p + 1) (by omega),
          hρ p hp.le, sub_self, mul_zero]
      exact False.elim (hvi (by simpa only [htag, abs_zero] using hv))
    · simp only [section5TaggedMode, Sum.elim_inr, if_neg hp]

/-- Joint time/overlap continuity of the actual lambda comparison on the
entire closed admissible trial strip. The two signs are joined at zero by
the actual zero-variance identities. No positivity of time or variance is
needed, and the overlap constraint of the N-site pressure is not varied. -/
theorem continuousOn_section5InterleavedScalarV_trial {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (ℓ : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => section5InterleavedScalarV s β h r j z.1 z.2 ℓ)
      {z | |z.2| ∈ Set.Icc (s.q (j - 1)) (s.q j)} := by
  let S : Set (ℝ × ℝ) := {z | |z.2| ∈ Set.Icc (s.q (j - 1)) (s.q j)}
  have hc (negative : Bool) : Continuous (fun z : S =>
      section5InterleavedScalarChart s β r j negative z.1 ℓ (h, h)) :=
    (continuous_section5InterleavedScalarChart s β r hj negative).comp
      (show Continuous (fun z : S => (z.1, ℓ, (h, h))) by fun_prop)
  have hglue : ∀ z : S, (0 : ℝ) = z.1.2 →
      section5InterleavedScalarChart s β r j false z.1 ℓ (h, h) =
        section5InterleavedScalarChart s β r j true z.1 ℓ (h, h) := by
    rintro ⟨⟨t, u⟩, hz⟩ hzero
    dsimp only at hzero ⊢
    subst u
    have hq : s.q (j - 1) = 0 := by
      apply le_antisymm
      · simpa only [S, Set.mem_setOf_eq, Set.mem_Icc, abs_zero] using hz.1
      · exact s.q_nonneg (by omega)
    exact (section5InterleavedScalarChart_zero_sign s β r hj hq t ℓ (h, h)).symm
  have H := (hc false).if_le (hc true) continuous_const
    (show Continuous (fun z : S => z.1.2) by fun_prop) hglue
  rw [continuousOn_iff_continuous_domRestrict]
  apply H.congr
  intro z
  dsimp only [Set.domRestrict]
  rw [section5InterleavedScalarV_eq_chart]
  by_cases hu : 0 ≤ z.1.2
  · simp only [if_pos hu, show ¬z.1.2 < 0 from not_lt_of_ge hu, decide_false]
  · simp only [if_neg hu, lt_of_not_ge hu, decide_true]

end SpinGlass.Targets
