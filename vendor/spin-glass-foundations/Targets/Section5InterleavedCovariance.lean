module

public import Targets.MixedCovarianceTelescope
public import Targets.Section5InterleavedEndpoint

@[expose] public section

/-!
# The actual signed trial matrix of the interleaved interpolation

Only interpolating tags change the covariance. The correlation of physical
tags need not match a single cutoff because their variance velocity is zero.
The algebra below records that fact explicitly and identifies the deterministic
correction. It does not claim the still-needed pressure derivative identity.
-/

open scoped BigOperators

namespace SpinGlass.Targets

def Section5GaussianMode.correlation : Section5GaussianMode → ℝ
  | .independent => 0
  | .shared => 1
  | .opposite => -1

/-- Unlike `sign`, this is also a unit sign at zero overlap. -/
noncomputable def section5TrialSign (u : ℝ) : ℝ := if u < 0 then -1 else 1

theorem section5TrialSign_sq (u : ℝ) : section5TrialSign u ^ 2 = 1 := by
  unfold section5TrialSign
  split_ifs <;> norm_num

theorem section5TrialSign_mul_abs (u : ℝ) : section5TrialSign u * |u| = u := by
  by_cases hu : u < 0
  · simp [section5TrialSign, hu, abs_of_neg hu]
  · simp [section5TrialSign, hu, abs_of_nonneg (le_of_not_gt hu)]

/-- Cumulative signed cross covariance; physical sharing itself is not reflected. -/
noncomputable def section5InterleavedCross {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) (i : ℕ) : ℝ :=
  section5TrialSign u * section5InterleavedRho s r j |u|
    (min i (section5InterleavingCutoff s r hj))

theorem section5InterleavedCross_endpoints {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (u : ℝ) :
    section5InterleavedCross s r hj u 0 = 0 ∧
      section5InterleavedCross s r hj u ((k + 2) + (k + 3)) = u := by
  have hρ := section5InterleavedRho_endpoints s r hj0 hj |u|
  constructor
  · simp [section5InterleavedCross, hρ.1]
  · rw [section5InterleavedCross, min_eq_right (Nat.le_of_lt (Fin.is_lt _)),
      section5InterleavedRho_at_cutoff s r hj, section5TrialSign_mul_abs]

theorem section5InterleavedCross_increment {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (u : ℝ) (i : Fin ((k + 2) + (k + 3))) :
    section5InterleavedCross s r hj u (i + 1) - section5InterleavedCross s r hj u i =
      (section5InterleavedRho s r j |u| (i + 1) - section5InterleavedRho s r j |u| i) *
        (section5TaggedMode r j (decide (u < 0)) (section5Interleaving s r j i)).correlation := by
  let τ := (section5InterleavingCutoff s r hj).val
  have hstop : section5InterleavedCross s r hj u (i + 1) -
      section5InterleavedCross s r hj u i =
      (section5InterleavedRho s r j |u| (i + 1) - section5InterleavedRho s r j |u| i) *
        (if i.val < τ then section5TrialSign u else 0) := by
    change section5TrialSign u * section5InterleavedRho s r j |u| (min (i.val + 1) τ) -
      section5TrialSign u * section5InterleavedRho s r j |u| (min i.val τ) = _
    by_cases hi : i.val < τ
    · simp only [min_eq_left (show i.val + 1 ≤ τ by omega), min_eq_left hi.le, if_pos hi]
      ring
    · simp only [min_eq_right (show τ ≤ i.val + 1 by omega),
        min_eq_right (show τ ≤ i.val by omega), if_neg hi, sub_self, mul_zero]
  rw [hstop]
  have he : i = (section5Interleaving s r j).symm (section5Interleaving s r j i) :=
    (Equiv.symm_apply_apply _ _).symm
  cases hi : section5Interleaving s r j i with
  | inl p =>
    rw [hi] at he
    rw [he, section5InterleavedRho_physical_succ]
    simp
  | inr p =>
    have hcut : i.val < τ ↔ (p : ℕ) < j := by
      rw [he, hi]
      exact (strictMono_section5Interleaving_interpolating s r hj).lt_iff_lt
    simp only [hcut, section5TaggedMode, Sum.elim_inr]
    by_cases hp : (p : ℕ) < j <;> by_cases hu : u < 0 <;>
      simp [hp, hu, section5TrialSign, Section5GaussianMode.correlation]

/-- The true mode at a tag gives precisely the signed trial-kernel increment,
even if its frozen physical sharing disagrees with the interpolation cutoff. -/
theorem section5Interleaved_covariance_increment {k n : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj : j ≤ k + 1) (β u : ℝ) (i : Fin ((k + 2) + (k + 3)))
    (a b : Config n × Config n) :
    pairFieldCovariance β
      (section5InterleavedRho s r j |u| (i + 1) - section5InterleavedRho s r j |u| i)
      (section5InterleavedCross s r hj u (i + 1) - section5InterleavedCross s r hj u i) a b =
      β ^ 2 * (section5InterleavedRho s r j |u| (i + 1) - section5InterleavedRho s r j |u| i) *
        pairFieldCovariance 1 1
          (section5TaggedMode r j (decide (u < 0)) (section5Interleaving s r j i)).correlation a b := by
  rw [section5InterleavedCross_increment]
  simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
  ring

/-- The signed cumulative matrix gives exactly the original correction. -/
theorem section5InterleavedCross_correction {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ) :
    pairCascadeCorrection β (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4) =
        2 * parisiCorrection s β :=
  section5Interleaved_pairCorrection s r hj0 hj β |u| (section5TrialSign_sq u)

theorem section5InterleavedMassNat_endpoints {k : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    section5InterleavedMassNat s r j 0 = 0 ∧
      section5InterleavedMassNat s r j (2 * k + 4) = 1 := by
  constructor
  · change section5InterleavedMassNat s r j (0 : Fin ((k + 2) + (k + 3))) = 0
    rw [section5InterleavedMassNat_coe, section5InterleavedMass_zero s r hj]
  · simpa [section5InterleavedMassNat, show 2 * k + 4 = (k + 2) + (k + 3) - 1 by omega]
      using section5InterleavedMass_last s r hj0 hj

theorem section5InterleavedMassNat_mono {k : ℕ} (s : RSBScheme k) (r j : ℕ)
    {i : ℕ} (hi : i < 2 * k + 4) :
    section5InterleavedMassNat s r j i ≤ section5InterleavedMassNat s r j (i + 1) := by
  simp only [section5InterleavedMassNat, dif_pos (show i < (k + 2) + (k + 3) by omega),
    dif_pos (show i + 1 < (k + 2) + (k + 3) by omega)]
  exact monotone_section5InterleavedMass s r j (by simp)

/-- Algebraic bound for normalized nonnegative split laws on the genuine tagged
trial matrix. The analytic identification with the pressure remains separate. -/
theorem section5InterleavedCovarianceExpression_le {k n : ℕ} (s : RSBScheme k) (r : ℕ)
    {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (β u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ0 : ∀ l < 2 * k + 4, ∀ p q, 0 ≤ μ l p q)
    (hμ1 : ∀ l < 2 * k + 4, ∑ p, ∑ q, μ l p q = 1) :
    pairCovarianceExpression β t u (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4) μ ≤
        -(2 * t * parisiCorrection s β) := by
  have hρ := section5InterleavedRho_endpoints s r hj0 hj |u|
  have hc := section5InterleavedCross_endpoints s r hj0 hj u
  have H := pairCovarianceExpression_le β u ht (section5InterleavedMassNat s r j)
    (section5InterleavedRho s r j |u|) (section5InterleavedCross s r hj u) (2 * k + 4)
    (section5InterleavedMassNat_endpoints s r hj0 hj).2
    (fun _ hi => section5InterleavedMassNat_mono s r j hi) hρ.1 hc.1
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hρ.2)
    (by simpa only [show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using hc.2) μ hμ0 hμ1
  rw [section5InterleavedCross_correction s r hj0 hj] at H
  exact H.trans_eq (by ring)

end SpinGlass.Targets
