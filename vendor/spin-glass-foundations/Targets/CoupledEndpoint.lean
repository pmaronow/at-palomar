module

/-
# Site tensorization with independently specified masses and variances

This extends the existing interacting cascade only by exposing its level data.
The independent/shared integrals, growth, order, and constant rules are reused.
The scalar regularity and tensorization are imported from RSAT. This permits
the inserted level of Talagrand (5.5)--(5.13), not just the original RSB scheme.
-/
public import Targets.CoupledFiniteStep

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlass.Targets

/-- Masses here are the actual logarithmic-Laplace masses: a shared step does
not halve them again. Levels are traversed from the terminal towards the root. -/
noncomputable def coupledFieldCascade (n : ℕ) (m v : ℕ → ℝ) (d : ℕ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0 => A
  | j + 1 => if j < d then
      independentStepPi n (m j) (v j) (coupledFieldCascade n m v d A j)
    else sharedStepPi n (2 * m j) (v j) (coupledFieldCascade n m v d A j)

theorem CoupledGrowth.fieldCascade {n : ℕ}
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (m v : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) :
    CoupledGrowth (coupledFieldCascade n m v d A j) := by
  induction j with
  | zero => exact hA
  | succ j ih =>
    simp only [coupledFieldCascade]
    split_ifs
    · exact ih.independentStep (hm j) (hv j)
    · exact ih.sharedStep (mul_nonneg (by norm_num) (hm j)) (hv j)

theorem coupledFieldCascade_mono {n : ℕ} (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ)
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, A x y ≤ B x y) (x y : Fin n → ℝ) :
    coupledFieldCascade n m v d A j x y ≤ coupledFieldCascade n m v d B j x y := by
  induction j generalizing x y with
  | zero => exact hAB x y
  | succ j ih =>
    simp only [coupledFieldCascade]
    split_ifs
    · exact independentStepPi_mono (hm j)
        (hA.fieldCascade m v hm hv d j) (hB.fieldCascade m v hm hv d j) ih x y
    · exact sharedStepPi_mono (mul_nonneg (by norm_num) (hm j))
        (hA.fieldCascade m v hm hv d j) (hB.fieldCascade m v hm hv d j) ih x y

theorem coupledFieldCascade_const_add {n : ℕ} (m v : ℕ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, 0 ≤ v j) (d j : ℕ) (c : ℝ)
    {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A)
    (x y : Fin n → ℝ) :
    coupledFieldCascade n m v d (fun x y => c + A x y) j x y =
      c + coupledFieldCascade n m v d A j x y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he : coupledFieldCascade n m v d (fun x y => c + A x y) j =
        fun x y => c + coupledFieldCascade n m v d A j x y :=
      funext fun x => funext (ih x)
    simp only [coupledFieldCascade]
    rw [he]
    split_ifs
    · exact independentStepPi_const_add c _ _ (hA.fieldCascade m v hm hv d j) x y
    · exact sharedStepPi_const_add c _ _ (hA.fieldCascade m v hm hv d j) x y

variable {P : Type*}

/-- The scalar recursion for independent inner levels and shared outer levels.
Independent pairs are two scalar transforms of the same mass, by Fubini. -/
noncomputable def splitScalarCascade (m : ℕ → ℝ) (v : ℕ → P → ℝ) (d : ℕ) :
    ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ ℓ x => coupledSite ℓ x.1 x.2
  | j + 1 => if j < d then
      GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j))
    else GTFrame.finiteStep (gaussianReal 0 1) (m j)
      (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j)

/-- The actual recursively tilted lambda derivative. -/
noncomputable def splitScalarCascadeD (m : ℕ → ℝ) (v : ℕ → P → ℝ) (d : ℕ) :
    ℕ → P → ℝ → ℝ × ℝ → ℝ
  | 0 => fun _ ℓ x => GTFrame.fLbaseD ℓ x
  | j + 1 => if j < d then
      GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun p => Real.sqrt (v j p)) (fun _ => 0)
        (GTFrame.finiteStep (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j))
        (GTFrame.finiteStepD (gaussianReal 0 1) (m j) (fun _ => 0)
          (fun p => Real.sqrt (v j p)) (splitScalarCascade m v d j) (splitScalarCascadeD m v d j))
    else GTFrame.finiteStepD (gaussianReal 0 1) (m j)
      (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p))
      (splitScalarCascade m v d j) (splitScalarCascadeD m v d j)

variable [TopologicalSpace P] [FirstCountableTopology P]

/-- A small zero-mass-inclusive adapter to the imported Gaussian regularity theorem. -/
theorem finiteStep_good {F D : P → ℝ → ℝ × ℝ → ℝ} (h : GTFrame.GoodFam F D)
    {m : ℝ} (hm : 0 ≤ m) {a b : P → ℝ} (ha : Continuous a) (hb : Continuous b) :
    GTFrame.GoodFam (GTFrame.finiteStep (gaussianReal 0 1) m a b F)
      (GTFrame.finiteStepD (gaussianReal 0 1) m a b F D) := by
  simp only [GTFrame.finiteStep, GTFrame.finiteStepD]
  by_cases hm0 : m = 0
  · simp only [if_pos hm0]
    exact GTFrame.step0_good (GTFrame.expMoments_gaussianReal 0 1) h ha hb
  · simp only [if_neg hm0]
    exact GTFrame.stepM_good (GTFrame.expMoments_gaussianReal 0 1) h
      (lt_of_le_of_ne hm (Ne.symm hm0)) ha hb

theorem splitScalarCascade_good (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, Continuous (v j)) (d j : ℕ) :
    GTFrame.GoodFam (splitScalarCascade m v d j) (splitScalarCascadeD m v d j) := by
  induction j with
  | zero =>
    simpa only [splitScalarCascade, splitScalarCascadeD, coupledSite_eq_gtTerminal,
      GTFrame.fLbase] using (GTFrame.goodFam_fLbase (P := P))
  | succ j ih =>
    simp only [splitScalarCascade, splitScalarCascadeD]
    split_ifs
    · exact finiteStep_good (finiteStep_good ih (hm j) continuous_const (hv j).sqrt)
        (hm j) (hv j).sqrt continuous_const
    · exact finiteStep_good ih (hm j) (hv j).sqrt (hv j).sqrt

omit [FirstCountableTopology P] in
theorem gtVectorStep_sum_good {F D : P → ℝ → ℝ × ℝ → ℝ} (h : GTFrame.GoodFam F D)
    (n : ℕ) {m : ℝ} (hm : 0 ≤ m) (a b : P → ℝ) (p : P) (ℓ : ℝ)
    (x y : Fin n → ℝ) :
    AT.gtVectorStep n m (a p) (b p) (fun x y => ∑ i, F p ℓ (x i, y i)) x y =
      ∑ i, GTFrame.finiteStep (gaussianReal 0 1) m a b F p ℓ (x i, y i) := by
  have H := AT.gtVectorStep_sum m (a p) (b p) (fun _ x y => F p ℓ (x, y)) x y
    (fun i => h.integrable_shift (GTFrame.expMoments_gaussianReal 0 1)
      p ℓ (a p) (b p) (x i, y i))
    (fun _ i => GTFrame.integral_expShift_pos (GTFrame.expMoments_gaussianReal 0 1)
      h hm p ℓ (a p) (b p) (x i, y i))
  convert H using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [GTFrame.finiteStep, AT.gtScalarStep]
  split_ifs <;> rfl

theorem coupledSite_sum_growth (n : ℕ) (ℓ : ℝ) :
    CoupledGrowth (fun x y : Fin n → ℝ => ∑ i, coupledSite ℓ (x i) (y i)) := by
  have H := (lambdaCoupledBase_growth n (0 : EnergySpace n) 0 ℓ
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)).const_add
      (-(n : ℝ) * (2 * Real.log 2))
  simpa only [lambdaCoupledBase_time_zero, add_zero, neg_mul, neg_add_cancel_left] using H

/-- The interacting N-site cascade really tensorizes for the new level data. -/
theorem coupledFieldCascade_eq_sum (n : ℕ) (m : ℕ → ℝ) (v : ℕ → P → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hv : ∀ j, Continuous (v j))
    (d j : ℕ) (p : P) (hp : ∀ j, 0 ≤ v j p) (ℓ : ℝ) (x y : Fin n → ℝ) :
    coupledFieldCascade n m (fun j => v j p) d
        (fun x y => ∑ i, coupledSite ℓ (x i) (y i)) j x y =
      ∑ i, splitScalarCascade m v d j p ℓ (x i, y i) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have he : coupledFieldCascade n m (fun j => v j p) d
        (fun x y => ∑ i, coupledSite ℓ (x i) (y i)) j =
        fun x y => ∑ i, splitScalarCascade m v d j p ℓ (x i, y i) :=
      funext fun x => funext (ih x)
    have hgood := splitScalarCascade_good m v hm hv d j
    have hgrowth := (coupledSite_sum_growth n ℓ).fieldCascade
      m (fun j => v j p) hm hp d j
    simp only [coupledFieldCascade]
    by_cases hj : j < d
    · rw [if_pos hj, independentStepPi_eq_gtVectorSteps _ _ hgrowth, he]
      have hinner := fun x y => gtVectorStep_sum_good hgood n (hm j)
        (fun _ => 0) (fun p => Real.sqrt (v j p)) p ℓ x y
      rw [show AT.gtVectorStep n (m j) 0 (Real.sqrt (v j p))
          (fun x y => ∑ i, splitScalarCascade m v d j p ℓ (x i, y i)) = _ from
        funext fun x => funext (hinner x)]
      simpa only [splitScalarCascade, if_pos hj] using
        gtVectorStep_sum_good (finiteStep_good hgood (hm j) continuous_const (hv j).sqrt)
          n (hm j) (fun p => Real.sqrt (v j p)) (fun _ => 0) p ℓ x y
    · rw [if_neg hj, sharedStepPi_eq_gtVectorStep, he]
      rw [show 2 * m j / 2 = m j by ring]
      simpa only [splitScalarCascade, if_neg hj] using
        gtVectorStep_sum_good hgood n (hm j)
          (fun p => Real.sqrt (v j p)) (fun p => Real.sqrt (v j p)) p ℓ x y

/-- The field-only constrained endpoint bound, with all Gaussian integrability
hypotheses discharged. It applies in particular to the inserted Section 5 data. -/
theorem constrainedFieldCascade_le {n : ℕ} (hn : 0 < n)
    (m : ℕ → ℝ) (v : ℕ → P → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hv : ∀ j, Continuous (v j)) (d j : ℕ) (p : P) (hp : ∀ j, 0 ≤ v j p)
    (u ℓ h : ℝ) (hu : ∃ σ τ : Config n, overlap n σ τ = u) :
    coupledFieldCascade n m (fun j => v j p) d
        (constrainedBase n (0 : EnergySpace n) 0 0 u) j (fun _ => h) (fun _ => h) ≤
      n * (2 * Real.log 2 + splitScalarCascade m v d j p ℓ (h, h) - ℓ * u) := by
  let c := (n : ℝ) * (2 * Real.log 2) - ℓ * n * u
  have H := coupledFieldCascade_mono m (fun j => v j p) hm hp d j
    (constrainedBase_growth (0 : EnergySpace n) 0 u
      (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hu)
    ((coupledSite_sum_growth n ℓ).const_add c)
    (fun x y => by
      have H := constrainedBase_time_zero_le hn (0 : EnergySpace n) 0 u ℓ hu x y
      simp only [add_zero] at H
      convert H using 1
      dsimp [c]
      ring)
    (fun _ => h) (fun _ => h)
  rw [coupledFieldCascade_const_add m (fun j => v j p) hm hp d j c
    (coupledSite_sum_growth n ℓ), coupledFieldCascade_eq_sum n m v hm hv d j p hp] at H
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
  convert H using 1
  dsimp [c]
  ring

end SpinGlass.Targets
