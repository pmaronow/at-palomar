module

/- Adaptation for Lean 4.34.1: proof elaboration and API compatibility only; original theorem statements are retained. Source revisions and exact patch are recorded in PROVENANCE.json and COMPATIBILITY.patch. -/
public import Targets.Section5InterleavedEndpoint
public import Targets.Section5ScalarIdentification

@[expose] public section

/-!
# The actual interleaved scalar endpoint and its reversed tag indices

The finite tagged list is outermost first, whereas the mixed scalar recursion
adds outer operators. This module fixes that reversal once for both the
zero-time tensorization and the strict comparison. The external field remains
`h` in both replicas; only interpolating shared fields change sign.
-/

namespace SpinGlass.Targets

/-- The tag visited by the bottom-up recursion. Unvisited natural indices
clamp harmlessly to the first forward position. -/
noncomputable def section5ReverseTag {k : ℕ} (s : RSBScheme k) (r j i : ℕ) :
    Section5MassTag k :=
  section5Interleaving s r j ⟨(k + 2) + (k + 3) - 1 - i, by omega⟩

/-- Actual mode at a reversed position. -/
noncomputable def section5ReverseMode {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (negative : Bool) (i : ℕ) : Section5GaussianMode :=
  section5TaggedMode r j negative (section5ReverseTag s r j i)

/-- Actual raw paired mass at a reversed position. -/
noncomputable def section5ReverseMass {k : ℕ} (s : RSBScheme k) (r j i : ℕ) : ℝ :=
  section5TaggedMass s r j (section5ReverseTag s r j i)

/-- Actual variance at a reversed position, at second time zero. -/
noncomputable def section5ReverseVariance {k : ℕ} (s : RSBScheme k)
    (β t u : ℝ) (r j i : ℕ) : ℝ :=
  section5TaggedVariance s β t u j (section5ReverseTag s r j i)

/-- The genuine signed or unsigned interleaved scalar lambda family. -/
noncomputable def section5InterleavedScalarV {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r j : ℕ) (t u l : ℝ) : ℝ :=
  mixedScalarCascade (section5ReverseMode s r j (decide (u < 0)))
    (section5ReverseMass s r j) (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    ((k + 2) + (k + 3)) () l (h, h)

/-- The scalar reference of the actual mixed family before scalar sorting. -/
noncomputable def section5InterleavedScalarReference {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r j : ℕ) (t u : ℝ) : ℝ → ℝ :=
  mixedScalarReference (section5ReverseMode s r j (decide (u < 0)))
    (section5ReverseMass s r j) (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    ((k + 2) + (k + 3)) ()

theorem section5ReverseTag_at_position {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (p : Fin ((k + 2) + (k + 3))) :
    section5ReverseTag s r j ((k + 2) + (k + 3) - 1 - p) =
      section5Interleaving s r j p := by
  unfold section5ReverseTag
  congr 1
  apply Fin.ext
  simp only
  omega

theorem section5ReverseTag_at_tag {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (tag : Section5MassTag k) :
    section5ReverseTag s r j
      ((k + 2) + (k + 3) - 1 - ((section5Interleaving s r j).symm tag).val) = tag := by
  rw [section5ReverseTag_at_position, Equiv.apply_symm_apply]

/-- Both signs double the scalar mass at shared tags; opposite sharing does
not change the reference scalar masses. -/
theorem section5TaggedMode_scalarMass {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    (negative : Bool) (tag : Section5MassTag k) :
    (section5TaggedMode r j negative tag).scalarMass (section5TaggedMass s r j tag) =
      section5TagScalarMass s r j tag := by
  cases tag with
  | inl p =>
    by_cases hp : p.val < r
    · simp [section5TaggedMode, section5TagScalarMass, section5TagShared,
        Section5GaussianMode.scalarMass, hp]
    · simp [section5TaggedMode, section5TagScalarMass, section5TagShared,
        Section5GaussianMode.scalarMass, hp]
  | inr p =>
    by_cases hp : p.val < j
    · cases negative <;> simp [section5TaggedMode, section5TagScalarMass,
        section5TagShared, Section5GaussianMode.scalarMass, hp]
    · simp [section5TaggedMode, section5TagScalarMass, section5TagShared,
        Section5GaussianMode.scalarMass, hp]

theorem section5TaggedMode_eq_independent_iff {k : ℕ} (r j : ℕ)
    (negative : Bool) (tag : Section5MassTag k) :
    section5TaggedMode r j negative tag = .independent ↔ ¬section5TagShared r j tag := by
  cases tag with
  | inl p =>
    simp only [section5TaggedMode, section5TagShared, Sum.elim_inl]
    split_ifs <;> simp_all
  | inr p =>
    simp only [section5TaggedMode, section5TagShared, Sum.elim_inr]
    split_ifs <;> simp_all

theorem section5ReverseMass_nonneg {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (i : ℕ) : 0 ≤ section5ReverseMass s r j i :=
  (section5TaggedMass_mem_Icc s r hj _).1

theorem section5ReverseMode_scalarMass_mem_Icc {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (negative : Bool) (i : ℕ) :
    (section5ReverseMode s r j negative i).scalarMass (section5ReverseMass s r j i) ∈
      Set.Icc 0 1 := by
  rw [section5ReverseMode, section5ReverseMass, section5TaggedMode_scalarMass,
    section5TagScalarMass_eq_original]
  exact ⟨s.m_nonneg (section5TagOriginalLevel_le hj _),
    s.m_le_one (section5TagOriginalLevel_le hj _)⟩

/-- A finite forward scalar list is exactly the backward indexed recursion.
This is an operator identity with no assumptions on masses or variances. -/
theorem parisiListCascade_ofFn_reverse {N : ℕ} (hN : 0 < N) (M V : Fin N → ℝ) :
    parisiListCascade (List.ofFn (fun p => (M p, V p)))
      (fun x => Real.log (Real.cosh x)) =
      scalarFieldCascade (fun i => M ⟨N - 1 - i, by omega⟩)
        (fun i => V ⟨N - 1 - i, by omega⟩) N := by
  have H (L : ℕ) (hL : L ≤ N) :
      parisiListCascade (List.ofFn (fun p : Fin L =>
        (M ⟨N - L + p, by omega⟩, V ⟨N - L + p, by omega⟩)))
        (fun x => Real.log (Real.cosh x)) =
        scalarFieldCascade (fun i => M ⟨N - 1 - i, by omega⟩)
          (fun i => V ⟨N - 1 - i, by omega⟩) L := by
    induction L with
    | zero => rfl
    | succ L ih =>
      rw [List.ofFn_succ, parisiListCascade_cons, scalarFieldCascade]
      have he : (fun p : Fin L =>
          (M ⟨N - (L + 1) + p.succ, by omega⟩, V ⟨N - (L + 1) + p.succ, by omega⟩)) =
          (fun p : Fin L => (M ⟨N - L + p, by omega⟩, V ⟨N - L + p, by omega⟩)) := by
        funext p
        have hi : (⟨N - (L + 1) + p.succ, by omega⟩ : Fin N) =
            ⟨N - L + p, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        rw [hi]
      rw [he, ih (by omega)]
      have hi : (⟨N - (L + 1) + (0 : Fin (L + 1)), by omega⟩ : Fin N) =
          ⟨N - 1 - L, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      rw [hi]
  simpa only [Nat.sub_self, zero_add, Fin.eta] using H N le_rfl

/-- The actual mixed scalar reference is exactly the unsorted tagged scalar
list. The sign of the trial overlap does not alter this scalar reference. -/
theorem section5InterleavedScalarReference_eq_list {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (r j : ℕ) (t u : ℝ) :
    section5InterleavedScalarReference s β r j t u =
      parisiListCascade (section5InterleavedScalarSteps s β t |u| r j)
        (fun x => Real.log (Real.cosh x)) := by
  rw [section5InterleavedScalarSteps, parisiListCascade_ofFn_reverse (by omega)]
  simp only [section5InterleavedScalarReference, mixedScalarReference,
    section5ReverseMode, section5ReverseMass, section5ReverseVariance,
    section5ReverseTag, section5TaggedMode_scalarMass]

/-- Non-strict comparison of the actual paired lambda-zero endpoint with its
actual scalar reference. No scalar mass ordering is assumed. -/
theorem section5InterleavedScalarV_zero_le_reference {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (t u : ℝ) :
    section5InterleavedScalarV s β h r j t u 0 ≤
      2 * section5InterleavedScalarReference s β r j t u h := by
  have H := mixedScalarCascade_zero_le (section5ReverseMode s r j (decide (u < 0)))
    (section5ReverseMass s r j)
    (fun i (_ : Unit) => section5ReverseVariance s β t |u| r j i)
    (section5ReverseMass_nonneg s r hj) (fun _ => continuous_const)
    ((k + 2) + (k + 3)) () h h
  simpa only [section5InterleavedScalarV, section5InterleavedScalarReference,
    mixedScalarReference, two_mul] using H

end SpinGlass.Targets
