module

public import Targets.CoupledReplicaWeights
public import Targets.CoupledNestedVariance

@[expose] public section

/-!
# Actual nested Hessian covariance expansion

Independent levels have two equal-mass tilts. Their middle covariance products
cancel pointwise, giving the same one-level rule as a shared tilt. Bounded
observable linearity then expands the genuine nested Hessian under the actual
split-level replica weights, preserving zero masses and zero variances.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

set_option autoImplicit false

namespace SpinGlass.Targets

variable {n : ℕ}

/-- The two intermediate covariance products cancel before integration.
No integrability or differentiability assumption is needed for this identity. -/
theorem pairedIndependentCovariance_eq_mean (mass variance : ℝ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    pairedIndependentCovariance mass variance A AW G GW x y =
      pairedIndependentMean mass variance A (fun x y => GW x y + mass * G x y * AW x y) x y -
        mass * pairedIndependentMean mass variance A G x y * pairedIndependentMean mass variance A AW x y := by
  unfold pairedIndependentCovariance pairedSecondCovariance
  have he : (fun y x =>
      (pairedSecondMean mass variance A (fun x y => GW x y + mass * G x y * AW x y) x y -
        mass * pairedSecondMean mass variance A G x y * pairedSecondMean mass variance A AW x y) +
        mass * pairedSecondMean mass variance A G x y * pairedSecondMean mass variance A AW x y) =
      fun y x => pairedSecondMean mass variance A
        (fun x y => GW x y + mass * G x y * AW x y) x y := by
    funext y x
    ring
  rw [he]
  rfl

/-- The original level's normalized derivative transport. -/
noncomputable def coupledLevelMean (m v : ℕ → ℝ) (d j : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  if j < d then pairedIndependentMean (m j) (v j) A G else pairedSharedMean (m j) (v j) A G

/-- Bounded measurability packages only the already-used observable hypotheses,
not any desired derivative or covariance identity. -/
structure CoupledBounded (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop where
  measurable : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2)
  bound : ∃ B : ℝ, ∀ x y, |G x y| ≤ B

theorem CoupledBounded.const (c : ℝ) : CoupledBounded (fun (_ _ : Fin n → ℝ) => c) :=
  ⟨measurable_const, |c|, fun _ _ => le_rfl⟩

theorem CoupledBounded.add {G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hH : CoupledBounded H) : CoupledBounded (fun x y => G x y + H x y) := by
  obtain ⟨B, hb⟩ := hG.bound
  obtain ⟨C, hc⟩ := hH.bound
  exact ⟨hG.measurable.add hH.measurable, B + C, fun x y =>
    (abs_add_le _ _).trans (add_le_add (hb x y) (hc x y))⟩

theorem CoupledBounded.sub {G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hH : CoupledBounded H) : CoupledBounded (fun x y => G x y - H x y) := by
  obtain ⟨B, hb⟩ := hG.bound
  obtain ⟨C, hc⟩ := hH.bound
  exact ⟨hG.measurable.sub hH.measurable, B + C, fun x y =>
    (abs_sub _ _).trans (add_le_add (hb x y) (hc x y))⟩

theorem CoupledBounded.mul {G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hH : CoupledBounded H) : CoupledBounded (fun x y => G x y * H x y) := by
  obtain ⟨B, hb⟩ := hG.bound
  obtain ⟨C, hc⟩ := hH.bound
  refine ⟨hG.measurable.mul hH.measurable, B * C, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hb x y) (hc x y) (abs_nonneg _) ((abs_nonneg _).trans (hb 0 0))

theorem CoupledBounded.const_mul {G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (c : ℝ) : CoupledBounded (fun x y => c * G x y) :=
  (CoupledBounded.const c).mul hG

theorem CoupledBounded.sum {I : Type*} [Fintype I]
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hG : ∀ i, CoupledBounded (G i)) :
    CoupledBounded (fun x y => ∑ i, G i x y) := by
  classical
  choose B hb using fun i => (hG i).bound
  exact ⟨Finset.measurable_sum _ fun i _ => (hG i).measurable,
    ∑ i, B i, fun x y => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => hb i x y)⟩

theorem CoupledBounded.cascade {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hA : CoupledGrowth A)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) :
    CoupledBounded (coupledFieldCascadeD m v d A G j) := by
  obtain ⟨B, hb⟩ := hG.bound
  have H := coupledFieldCascadeD_measurable_bound hA hG.measurable hb m v hm hv d j
  exact ⟨H.1, B, H.2⟩

theorem CoupledBounded.levelMean {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hA : CoupledGrowth A)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) :
    CoupledBounded (coupledLevelMean m v d j A G) := by
  obtain ⟨B, hb⟩ := hG.bound
  unfold coupledLevelMean
  split_ifs
  · have H := pairedIndependentMean_measurable_bound hA hG.measurable hb (hm j) (hv j)
    exact ⟨H.1, B, H.2⟩
  · have H := pairedSharedMean_measurable_bound hA hG.measurable hb (m j) (v j)
    exact ⟨H.1, B, H.2⟩

theorem coupledLevelMean_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : ∀ i, CoupledBounded (G i)) (c : I → ℝ)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledLevelMean m v d j A (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * coupledLevelMean m v d j A (G i) x y := by
  choose B hb using fun i => (hG i).bound
  unfold coupledLevelMean
  split_ifs
  · exact pairedIndependentMean_sum hA (fun i => (hG i).measurable) hb c (hm j) (hv j) x y
  · exact pairedSharedMean_sum hA (fun i => (hG i).measurable) hb c (m j) (v j) x y

theorem coupledLevelMean_add {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledLevelMean m v d j A (fun x y => G x y + H x y) x y =
      coupledLevelMean m v d j A G x y + coupledLevelMean m v d j A H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul] using coupledLevelMean_sum hA h (fun _ => 1) m v hm hv d j x y

theorem coupledLevelMean_const_mul {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (c : ℝ)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledLevelMean m v d j A (fun x y => c * G x y) x y = c * coupledLevelMean m v d j A G x y := by
  simpa using coupledLevelMean_sum (I := Unit) hA (fun _ => hG) (fun _ => c) m v hm hv d j x y

theorem coupledLevelMean_sub {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledLevelMean m v d j A (fun x y => G x y - H x y) x y =
      coupledLevelMean m v d j A G x y - coupledLevelMean m v d j A H x y := by
  have H' := coupledLevelMean_add hA hG (hH.const_mul (-1)) m v hm hv d j x y
  rw [coupledLevelMean_const_mul hA hH (-1) m v hm hv d j x y] at H'
  simpa only [neg_one_mul, sub_eq_add_neg] using H'

theorem coupledFieldCascadeDD_succ_mean
    (m v : ℕ → ℝ) (d j : ℕ)
    (A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeDD m v d A AW G GW (j + 1) x y =
      coupledLevelMean m v d j (coupledFieldCascade n m v d A j)
        (fun x y => coupledFieldCascadeDD m v d A AW G GW j x y +
          m j * coupledFieldCascadeD m v d A G j x y * coupledFieldCascadeD m v d A AW j x y) x y -
        m j * coupledFieldCascadeD m v d A G (j + 1) x y *
          coupledFieldCascadeD m v d A AW (j + 1) x y := by
  simp only [coupledFieldCascadeDD, coupledFieldCascadeD, coupledLevelMean]
  split_ifs
  · exact pairedIndependentCovariance_eq_mean _ _ _ _ _ _ _ _
  · rfl

theorem CoupledBounded.cascadeDD {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) :
    CoupledBounded (coupledFieldCascadeDD m v d A AW G GW j) := by
  induction j with
  | zero => exact hGW
  | succ j ih =>
    have hg := hG.cascade hA m v hm hv d j
    have haw := hAW.cascade hA m v hm hv d j
    have hg' := hG.cascade hA m v hm hv d (j + 1)
    have haw' := hAW.cascade hA m v hm hv d (j + 1)
    have H := ((ih.add ((hg.const_mul (m j)).mul haw)).levelMean
      (hA.fieldCascade m v hm hv d j) m v hm hv d j).sub ((hg'.const_mul (m j)).mul haw')
    simpa only [← coupledFieldCascadeDD_succ_mean] using H

/-- Actual transport from original level `l` through `r` outer levels. -/
noncomputable def coupledOuterMean (m v : ℕ → ℝ) (d : ℕ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (l r : ℕ)
    (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  coupledFieldCascadeD (fun i => m (l + i)) (fun i => v (l + i)) (d - l)
    (coupledFieldCascade n m v d A l) G r

theorem coupledOuterMean_zero (m v : ℕ → ℝ) (d l : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : coupledOuterMean m v d A l 0 G = G := rfl

theorem coupledOuterMean_from_zero (m v : ℕ → ℝ) (d j : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledOuterMean m v d A 0 j G = coupledFieldCascadeD m v d A G j := by
  simp only [coupledOuterMean, Nat.zero_add, Nat.sub_zero, coupledFieldCascade]

theorem coupledOuterMean_succ (m v : ℕ → ℝ) (d l r : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledOuterMean m v d A l (r + 1) G =
      coupledLevelMean m v d (l + r) (coupledFieldCascade n m v d A (l + r))
        (coupledOuterMean m v d A l r G) := by
  have he : (r < d - l) ↔ (l + r < d) := by omega
  simp only [coupledOuterMean, coupledFieldCascadeD, coupledLevelMean,
    coupledFieldCascade_add_levels, he]

theorem CoupledBounded.outerMean {A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : CoupledBounded G) (hA : CoupledGrowth A)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d l r : ℕ) :
    CoupledBounded (coupledOuterMean m v d A l r G) :=
  hG.cascade (hA.fieldCascade m v hm hv d l) _ _
    (fun i => hm (l + i)) (fun i => hv (l + i)) (d - l) r

theorem coupledOuterMean_sum {I : Type*} [Fintype I]
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {G : I → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : ∀ i, CoupledBounded (G i)) (c : I → ℝ)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d A l r (fun x y => ∑ i, c i * G i x y) x y =
      ∑ i, c i * coupledOuterMean m v d A l r (G i) x y := by
  choose B hb using fun i => (hG i).bound
  exact coupledFieldCascadeD_sum (hA.fieldCascade m v hm hv d l)
    (fun i => (hG i).measurable) hb c _ _
    (fun i => hm (l + i)) (fun i => hv (l + i)) (d - l) r x y

theorem coupledOuterMean_sub {A G H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hG : CoupledBounded G) (hH : CoupledBounded H)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d l r : ℕ) (x y : Fin n → ℝ) :
    coupledOuterMean m v d A l r (fun x y => G x y - H x y) x y =
      coupledOuterMean m v d A l r G x y - coupledOuterMean m v d A l r H x y := by
  have h : ∀ i : Fin 2, CoupledBounded (![G, H] i) := by intro i; fin_cases i <;> assumption
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul, neg_one_mul, sub_eq_add_neg] using
      coupledOuterMean_sum hA h (![1, -1]) m v hm hv d l r x y

theorem coupledOuterMean_cascadeD (m v : ℕ → ℝ) (d l r : ℕ)
    (A G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    coupledOuterMean m v d A l r (coupledFieldCascadeD m v d A G l) =
      coupledFieldCascadeD m v d A G (l + r) := by
  induction r with
  | zero => simp only [coupledOuterMean_zero, Nat.add_zero]
  | succ r ih =>
    rw [coupledOuterMean_succ, ih]
    change _ = coupledFieldCascadeD m v d A G ((l + r) + 1)
    rfl

/-- One covariance rule for both kinds of actual level. -/
theorem coupledFieldCascadeDD_succ_covariance
    {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledFieldCascadeDD m v d A AW G GW (j + 1) x y =
      coupledLevelMean m v d j (coupledFieldCascade n m v d A j)
        (coupledFieldCascadeDD m v d A AW G GW j) x y +
        m j * (coupledLevelMean m v d j (coupledFieldCascade n m v d A j)
          (fun x y => coupledFieldCascadeD m v d A G j x y * coupledFieldCascadeD m v d A AW j x y) x y -
          coupledFieldCascadeD m v d A G (j + 1) x y * coupledFieldCascadeD m v d A AW (j + 1) x y) := by
  have hP := (hG.cascade hA m v hm hv d j).mul (hAW.cascade hA m v hm hv d j)
  have H := coupledFieldCascadeDD_succ_mean m v d j A AW G GW x y
  simp only [mul_assoc] at H
  rw [coupledLevelMean_add (hA.fieldCascade m v hm hv d j)
    (CoupledBounded.cascadeDD hA hAW hG hGW m v hm hv d j) (hP.const_mul (m j)) m v hm hv d j x y,
    coupledLevelMean_const_mul (hA.fieldCascade m v hm hv d j) hP (m j) m v hm hv d j x y] at H
  rw [H]
  ring

/-- Full-depth covariance expansion of the checked nested Hessian recursion.
All remaining outer transports use the original potentials and levels. -/
theorem coupledFieldCascadeDD_expansion
    {A AW G GW : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hAW : CoupledBounded AW) (hG : CoupledBounded G) (hGW : CoupledBounded GW)
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (d j : ℕ) (x y : Fin n → ℝ) :
    coupledFieldCascadeDD m v d A AW G GW j x y =
      coupledOuterMean m v d A 0 j GW x y +
      ∑ l : Fin j, m l *
        (coupledOuterMean m v d A l (j - l)
          (fun x y => coupledFieldCascadeD m v d A G l x y * coupledFieldCascadeD m v d A AW l x y) x y -
        coupledOuterMean m v d A (l + 1) (j - (l + 1))
          (fun x y => coupledFieldCascadeD m v d A G (l + 1) x y *
            coupledFieldCascadeD m v d A AW (l + 1) x y) x y) := by
  classical
  let P (l : ℕ) := fun x y => coupledFieldCascadeD m v d A G l x y * coupledFieldCascadeD m v d A AW l x y
  have hP (l : ℕ) : CoupledBounded (P l) :=
    (hG.cascade hA m v hm hv d l).mul (hAW.cascade hA m v hm hv d l)
  induction j generalizing x y with
  | zero => simp only [coupledFieldCascadeDD, coupledOuterMean_zero, Fin.sum_univ_zero, add_zero]
  | succ j ih =>
    let R (l : Fin j) := fun x y =>
      coupledOuterMean m v d A l (j - l) (P l) x y -
        coupledOuterMean m v d A (l + 1) (j - (l + 1)) (P (l + 1)) x y
    have hR (l : Fin j) : CoupledBounded (R l) :=
      ((hP l).outerMean hA m v hm hv d l (j - l)).sub
        ((hP (l + 1)).outerMean hA m v hm hv d (l + 1) (j - (l + 1)))
    have he (l : Fin j) : coupledLevelMean m v d j (coupledFieldCascade n m v d A j) (R l) x y =
        coupledOuterMean m v d A l (j + 1 - l) (P l) x y -
          coupledOuterMean m v d A (l + 1) (j + 1 - (l + 1)) (P (l + 1)) x y := by
      have h1 : j + 1 - l = (j - l) + 1 := by omega
      have h2 : j + 1 - (l + 1) = (j - (l + 1)) + 1 := by omega
      have h3 : l + (j - l) = j := by omega
      have h4 : l + 1 + (j - (l + 1)) = j := by omega
      rw [h1, h2, coupledOuterMean_succ, coupledOuterMean_succ, h3, h4]
      exact coupledLevelMean_sub (hA.fieldCascade m v hm hv d j)
        ((hP l).outerMean hA m v hm hv d l (j - l))
        ((hP (l + 1)).outerMean hA m v hm hv d (l + 1) (j - (l + 1))) m v hm hv d j x y
    have hih : coupledFieldCascadeDD m v d A AW G GW j = fun x y =>
        coupledOuterMean m v d A 0 j GW x y + ∑ l : Fin j, m l * R l x y :=
      funext fun x => funext fun y => ih x y
    rw [coupledFieldCascadeDD_succ_covariance hA hAW hG hGW m v hm hv d j x y, hih,
      coupledLevelMean_add (hA.fieldCascade m v hm hv d j)
        (hGW.outerMean hA m v hm hv d 0 j)
        (CoupledBounded.sum (fun l => (hR l).const_mul (m l))) m v hm hv d j x y,
      coupledLevelMean_sum (hA.fieldCascade m v hm hv d j) hR (fun l => m l) m v hm hv d j x y]
    simp_rw [he]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel_left, Nat.sub_self,
      coupledOuterMean_zero, coupledOuterMean_succ, Nat.zero_add, Nat.add_zero]
    dsimp only [P]
    ring

/-- A bilinear observable under the actual product-before-transport replica law. -/
noncomputable def constrainedReplicaBilinear (m v : ℕ → ℝ) (d l r : ℕ)
    (U : EnergySpace n) (u : ℝ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ p, ∑ q, constrainedCascadeReplica m v d l r U u x y p q * f p * g q

/-- The full covariance telescope, with original-level indices. The first
diagonal term and the initial product term retain the finite-state covariance. -/
noncomputable def constrainedReplicaHessianExpression (m v : ℕ → ℝ) (d j : ℕ)
    (U : EnergySpace n) (u : ℝ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (∑ p, constrainedCascadeGibbs m v d j U u x y p * f p * g p) -
    constrainedReplicaBilinear m v d 0 j U u f g x y +
    ∑ l : Fin j, m l * (constrainedReplicaBilinear m v d l (j - l) U u f g x y -
      constrainedReplicaBilinear m v d (l + 1) (j - (l + 1)) U u f g x y)

private theorem bounded_terminalMean (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)] (f : AT.ConstrainedPair n u → ℝ) :
    CoupledBounded (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p) := by
  have hp (p : AT.ConstrainedPair n u) : CoupledBounded (fun x y => constrainedPairGibbs n U u x y p) := by
    refine ⟨measurable_constrainedPairGibbs_fields U u p, 1, fun x y => ?_⟩
    rw [abs_of_nonneg (constrainedPairGibbs_nonneg n U u x y p)]
    exact AT.gtStateGibbs_le_one _ _ _
  simpa only [mul_comm] using CoupledBounded.sum (fun p => (hp p).const_mul (f p))

/-- Actual finite-state covariance input gives the full split-replica expansion.
The only hypotheses are the model's nonempty constraint and nonnegative level
parameters; no covariance identity or differentiability is assumed. -/
theorem coupledFieldCascadeDD_constrained_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascadeDD m v d (constrainedPairFieldBase n U u)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * g p)
      (fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p)
      (fun x y => (∑ p, constrainedPairGibbs n U u x y p * (f p * g p)) -
        (∑ p, constrainedPairGibbs n U u x y p * f p) *
          (∑ p, constrainedPairGibbs n U u x y p * g p)) j x y =
      constrainedReplicaHessianExpression m v d j U u f g x y := by
  let A := constrainedPairFieldBase n U u
  let M (f : AT.ConstrainedPair n u → ℝ) := fun x y => ∑ p, constrainedPairGibbs n U u x y p * f p
  have hA : CoupledGrowth A := constrainedPairFieldCascade_growth U u m v hm hv d 0
  have hM (f : AT.ConstrainedPair n u → ℝ) : CoupledBounded (M f) := bounded_terminalMean U u f
  have hp (l r : ℕ) :
      coupledOuterMean m v d A l r
        (fun x y => coupledFieldCascadeD m v d A (M f) l x y *
          coupledFieldCascadeD m v d A (M g) l x y) x y =
        constrainedReplicaBilinear m v d l r U u f g x y := by
    dsimp only [coupledOuterMean, A, M, constrainedReplicaBilinear]
    simp_rw [constrainedCascadeGibbs_moment U u m v hm hv]
    exact constrainedCascadeReplica_product_moment U u m v hm hv d l r f g x y
  have H := coupledFieldCascadeDD_expansion hA (hM g) (hM f)
    ((hM (fun p => f p * g p)).sub ((hM f).mul (hM g))) m v hm hv d j x y
  rw [coupledOuterMean_sub hA (hM (fun p => f p * g p)) ((hM f).mul (hM g)) m v hm hv d 0 j x y] at H
  have hp0 : coupledOuterMean m v d A 0 j (fun x y => M f x y * M g x y) x y =
      constrainedReplicaBilinear m v d 0 j U u f g x y := by
    simpa only [coupledFieldCascadeD] using hp 0 j
  rw [hp0, coupledOuterMean_from_zero] at H
  simp_rw [hp] at H
  simpa only [A, M, constrainedCascadeGibbs_moment U u m v hm hv,
    constrainedReplicaHessianExpression, mul_assoc] using H

/-- The genuine full nested disorder Hessian equals its actual replica
covariance telescope, at every depth and independent/shared split. -/
theorem constrainedPairFieldCascadeSecond_eq_replica
    (U V W : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (x y : Fin n → ℝ) :
    constrainedPairFieldCascadeSecond m v d j U V W u x y =
      constrainedReplicaHessianExpression m v d j U u
        (fun p => V p.1.1 + V p.1.2) (fun p => W p.1.1 + W p.1.2) x y := by
  rw [constrainedPairFieldCascadeSecond_eq U V W u m v hm hv d j x y]
  have he : constrainedPairSecond n u U V W = fun x y =>
      (∑ p, constrainedPairGibbs n U u x y p * ((V p.1.1 + V p.1.2) * (W p.1.1 + W p.1.2))) -
      (∑ p, constrainedPairGibbs n U u x y p * (V p.1.1 + V p.1.2)) *
        (∑ p, constrainedPairGibbs n U u x y p * (W p.1.1 + W p.1.2)) := by
    funext x y
    simp only [constrainedPairSecond_eq_covariance, mul_assoc]
  rw [he]
  exact coupledFieldCascadeDD_constrained_replica U u m v hm hv d j _ _ x y

/-- Separate-replica spatial Hessians have exactly the same replica telescope,
with spin-field observables substituted for pair energy directions. -/
theorem constrainedPairCascadeSpatialSecond_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (A B C D x y : Fin n → ℝ) :
    constrainedPairCascadeSpatialSecond m v d j U u A B C D x y =
      constrainedReplicaHessianExpression m v d j U u
        (pairFieldPotential n u A B) (pairFieldPotential n u C D) x y := by
  rw [constrainedPairCascadeSpatialSecond_eq U u m v hm hv d j A B C D x y]
  unfold constrainedPairFieldCovariance constrainedPairFieldDirection
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    coupledFieldCascadeDD_constrained_replica U u m v hm hv d j
      (pairFieldPotential n u A B) (pairFieldPotential n u C D) x y

private theorem covariance_mass_sum (m B : ℕ → ℝ) (j : ℕ) :
    (∑ l ∈ Finset.range (j + 1), m l * (B l - B (l + 1))) =
      m 0 * B 0 - m j * B (j + 1) +
        ∑ l ∈ Finset.range j, (m (l + 1) - m l) * B (l + 1) := by
  induction j with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one, Finset.sum_range_zero, add_zero]; ring
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Adjacent masses telescope against the same actual split-level replica
weights. Endpoint coefficients are retained unless supplied by the scheme. -/
theorem constrainedReplicaHessianExpression_mass_telescope
    (m v : ℕ → ℝ) (d j : ℕ) (U : EnergySpace n) (u : ℝ)
    (f g : AT.ConstrainedPair n u → ℝ) (x y : Fin n → ℝ) :
    constrainedReplicaHessianExpression m v d (j + 1) U u f g x y =
      (∑ p, constrainedCascadeGibbs m v d (j + 1) U u x y p * f p * g p) +
        (m 0 - 1) * constrainedReplicaBilinear m v d 0 (j + 1) U u f g x y -
        m j * constrainedReplicaBilinear m v d (j + 1) 0 U u f g x y +
        ∑ l : Fin j, (m (l + 1) - m l) *
          constrainedReplicaBilinear m v d (l + 1) (j - l) U u f g x y := by
  let B := fun l => constrainedReplicaBilinear m v d l (j + 1 - l) U u f g x y
  have H := covariance_mass_sum m B j
  simp only [B, Nat.sub_zero, Nat.sub_self] at H
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at H
  have he (l : Fin j) : j + 1 - (l + 1) = j - l := by omega
  simp only [he] at H
  unfold constrainedReplicaHessianExpression
  rw [H]
  ring

/-- The actual Hessian-plus-square input of the variance heat generator is now
an explicit actual replica expression. Further outer heat transport is separate. -/
theorem constrainedSpatialHeat_eq_replica
    (U : EnergySpace n) (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d j : ℕ) (mass : ℝ) (A B x y : Fin n → ℝ) :
    constrainedSpatialHeat U u m v d j mass A B x y =
      constrainedReplicaHessianExpression m v d j U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y +
      mass * constrainedReplicaBilinear m v d j 0 U u
        (pairFieldPotential n u A B) (pairFieldPotential n u A B) x y := by
  have hp := constrainedCascadeReplica_spatial_product U u m v hm hv d j 0 A B A B x y
  simp only [coupledFieldCascadeD] at hp
  rw [constrainedSpatialHeat, constrainedPairCascadeSpatialSecond_eq_replica U u m v hm hv d j,
    pow_two, hp]
  rfl

end SpinGlass.Targets
