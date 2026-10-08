module

public import Targets.Section5InterleavedEndpoint

@[expose] public section

/-!
# Adjacent inserted-overlap boundary identities

At a shared breakpoint the two inserted overlap sequences are literally the
same sequence: inserting `q j` immediately before or immediately after the
level gives the same cumulative values. This elementary identity is the
overlap part of the later adjacent-trial cascade gluing; it does not yet
identify the sorted tagged Gaussian operators.
-/

namespace SpinGlass.Targets

theorem section5Rho_adjacent_boundary {k : ℕ} (s : RSBScheme k)
    {j : ℕ} (_hj : j ≤ k + 1) (u : ℝ) (hu : u = s.q j) (p : ℕ) :
    section5Rho s j u p = section5Rho s (j + 1) u p := by
  subst u
  unfold section5Rho
  by_cases hlt : p < j
  · have hlt' : p < j + 1 := by omega
    simp only [if_pos hlt, if_pos hlt']
  · by_cases heq : p = j
    · subst p
      simp
    · have hlt' : ¬p < j + 1 := by omega
      by_cases heq' : p = j + 1
      · subst p
        simp
      · simp [hlt, heq, hlt', heq']

theorem section5Rho_adjacent_boundary_all {k : ℕ} (s : RSBScheme k)
    {j : ℕ} (hj : j ≤ k + 1) (p : ℕ) :
    section5Rho s j (s.q j) p = section5Rho s (j + 1) (s.q j) p :=
  section5Rho_adjacent_boundary s hj (s.q j) rfl p

theorem section5TaggedVariance_adjacent_boundary {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) {j : ℕ} (hj : j ≤ k + 1) (tag : Section5MassTag k) :
    section5TaggedVariance s β t (s.q j) j tag =
      section5TaggedVariance s β t (s.q j) (j + 1) tag := by
  rcases tag with p | p
  · rfl
  · simp only [section5TaggedVariance, Sum.elim_inr]
    rw [section5Rho_adjacent_boundary_all s hj p,
      section5Rho_adjacent_boundary_all s hj (p + 1)]

theorem section5TaggedMass_adjacent_boundary_of_ne
    {k : ℕ} (s : RSBScheme k) {r j : ℕ} (hj : j ≤ k + 1)
    (tag : Section5MassTag k)
    (htag : tag ≠ Sum.inr ⟨j, by omega⟩) :
    section5TaggedMass s r j tag = section5TaggedMass s r (j + 1) tag := by
  rcases tag with p | p
  · rfl
  · by_cases hp : (p : ℕ) < j
    · have hp' : (p : ℕ) < j + 1 := by omega
      simp only [section5TaggedMass, Sum.elim_inr, section5Mass,
        if_pos hp, if_pos hp']
    · by_cases he : (p : ℕ) = j
      · exfalso
        apply htag
        congr 1
        exact Fin.ext he
      · have hp' : ¬(p : ℕ) < j + 1 := by omega
        by_cases he' : (p : ℕ) = j + 1
        · simp only [section5TaggedMass, Sum.elim_inr, section5Mass,
            if_neg hp, if_neg he, if_neg hp', if_pos he', Nat.add_sub_cancel]
          have hsub : (p : ℕ) - 1 = j := by omega
          rw [hsub]
        · simp only [section5TaggedMass, Sum.elim_inr, section5Mass,
            if_neg hp, if_neg he, if_neg hp', if_neg he', Nat.add_sub_cancel]

theorem section5TaggedMode_adjacent_boundary_of_ne
    {k : ℕ} {r j : ℕ} (hj : j ≤ k + 1) (negative : Bool) (tag : Section5MassTag k)
    (htag : tag ≠ Sum.inr ⟨j, by omega⟩) :
    section5TaggedMode r j negative tag =
      section5TaggedMode r (j + 1) negative tag := by
  rcases tag with p | p
  · rfl
  · by_cases hp : (p : ℕ) < j
    · have hp' : (p : ℕ) < j + 1 := by omega
      simp only [section5TaggedMode, Sum.elim_inr, if_pos hp, if_pos hp']
    · by_cases he : (p : ℕ) = j
      · exfalso
        apply htag
        congr 1
        exact Fin.ext he
      · have hp' : ¬(p : ℕ) < j + 1 := by omega
        simp only [section5TaggedMode, Sum.elim_inr, if_neg hp,
          if_neg hp']

end SpinGlass.Targets
