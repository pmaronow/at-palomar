module

/-
# Stability of the constrained cascade in its Gaussian inputs

The estimates here use the maximum change of an individual Hamiltonian, not
the Euclidean norm of the vector of all configuration energies. Consequently
they do not introduce a factor exponential in the number of spins.
-/
public import Targets.ConstrainedCascade

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

theorem parisiStepPi_dist_le_growth {n : ℕ} {m v ε : ℝ}
    {A B : (Fin n → ℝ) → ℝ} (hA : GuerraGrowth A) (hB : GuerraGrowth B)
    (hAB : ∀ x, |A x - B x| ≤ ε) (x : Fin n → ℝ) :
    |parisiStepPi n m v A x - parisiStepPi n m v B x| ≤ ε := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  obtain ⟨C', D', hD', hb'⟩ := hB.bound
  exact parisiStepPi_dist_le hD hD' hb hb' hA.measurable hB.measurable hAB x

theorem CoupledGrowth.secondStep {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) {m v : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v) :
    CoupledGrowth (fun x y => parisiStepPi n m v (A x) y) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨measurable_secondStepPi hA.measurable m v, C + stepK n m v D, D, hD,
    fun x y => ?_⟩
  have H := parisiStepPi_abs_le (C := C + D * l1 x) hm hv hD
    (fun z => show |A x z| ≤ _ by nlinarith [hb x z]) (hA.section_right x).measurable y
  nlinarith

theorem CoupledGrowth.swap {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) : CoupledGrowth (fun x y => A y x) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  exact ⟨hA.measurable.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.2, p.1))
    measurable_swap, C, D, hD, fun x y => by simpa only [add_comm] using hb y x⟩

theorem independentStepPi_dist_le {n : ℕ} {m v ε : ℝ} (hm : 0 ≤ m) (hv : 0 ≤ v)
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, |A x y - B x y| ≤ ε) (x y : Fin n → ℝ) :
    |independentStepPi n m v A x y - independentStepPi n m v B x y| ≤ ε := by
  rw [independentStepPi_eq_nested m v hA, independentStepPi_eq_nested m v hB]
  exact parisiStepPi_dist_le_growth ((hA.secondStep hm hv).swap.section_right y)
    ((hB.secondStep hm hv).swap.section_right y)
    (fun w => parisiStepPi_dist_le_growth (hA.section_right w) (hB.section_right w) (hAB w) y) x

theorem sharedStepPi_dist_le {n : ℕ} {m v ε : ℝ}
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, |A x y - B x y| ≤ ε) (x y : Fin n → ℝ) :
    |sharedStepPi n m v A x y - sharedStepPi n m v B x y| ≤ ε :=
  parisiStepPi_dist_le_growth (hA.shared_shift x y) (hB.shared_shift x y) (fun _ => hAB _ _) 0

/-- Smoothing does not enlarge a uniform difference, at any depth or split. -/
theorem coupledCascade_dist_le {n k : ℕ} (s : RSBScheme k) (β : ℝ) (d j : ℕ) {ε : ℝ}
    {A B : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} (hA : CoupledGrowth A) (hB : CoupledGrowth B)
    (hAB : ∀ x y, |A x y - B x y| ≤ ε) (x y : Fin n → ℝ) :
    |coupledCascade n s β d A j x y - coupledCascade n s β d B j x y| ≤ ε := by
  induction j generalizing x y with
  | zero => exact hAB x y
  | succ j ih =>
    simp only [coupledCascade]
    split_ifs
    · exact independentStepPi_dist_le (s.m_nonneg (by omega)) (levelVar_nonneg s β j)
        (hA.cascade s β d j) (hB.cascade s β d j) ih x y
    · exact sharedStepPi_dist_le (hA.cascade s β d j) (hB.cascade s β d j) ih x y

theorem CoupledGrowth.translate {n : ℕ} {A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hA : CoupledGrowth A) (a b : Fin n → ℝ) :
    CoupledGrowth (fun x y => A (x + a) (y + b)) := by
  obtain ⟨C, D, hD, hb⟩ := hA.bound
  refine ⟨hA.measurable.comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    (p.1 + a, p.2 + b)) (by fun_prop), C + D * (l1 a + l1 b), D, hD, fun x y => ?_⟩
  nlinarith [hb (x + a) (y + b), l1_add_le x a, l1_add_le y b]

theorem coupledCascade_translate {n k : ℕ} (s : RSBScheme k) (β : ℝ) (d j : ℕ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (a b x y : Fin n → ℝ) :
    coupledCascade n s β d (fun x y => A (x + a) (y + b)) j x y =
      coupledCascade n s β d A j (x + a) (y + b) := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    simp only [coupledCascade]
    split_ifs
    · simp only [independentStepPi]
      simp_rw [ih]
      simp only [Pi.add_def, add_right_comm]
    · simp only [sharedStepPi, ih]
      congr 1
      funext z
      congr 1 <;> abel

/-- A restricted finite log partition function is nonexpansive in its energies.
Nonemptiness is essential: no logarithm of an empty partition sum is used. -/
theorem abs_log_sum_exp_sub_le_on {ι : Type*} [Fintype ι] (S : Finset ι)
    (hS : S.Nonempty) {f g : ι → ℝ} {ε : ℝ} (hε : ∀ i ∈ S, |f i - g i| ≤ ε) :
    |Real.log (∑ i ∈ S, Real.exp (f i)) - Real.log (∑ i ∈ S, Real.exp (g i))| ≤ ε := by
  have hf : 0 < ∑ i ∈ S, Real.exp (f i) := Finset.sum_pos (fun _ _ => Real.exp_pos _) hS
  have hg : 0 < ∑ i ∈ S, Real.exp (g i) := Finset.sum_pos (fun _ _ => Real.exp_pos _) hS
  have hfg : (∑ i ∈ S, Real.exp (f i)) ≤ Real.exp ε * ∑ i ∈ S, Real.exp (g i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hε i hi)).2]))
  have hgf : (∑ i ∈ S, Real.exp (g i)) ≤ Real.exp ε * ∑ i ∈ S, Real.exp (f i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hε i hi)).1]))
  have h1 := Real.log_le_log hf hfg
  have h2 := Real.log_le_log hg hgf
  rw [Real.log_mul (Real.exp_pos _).ne' hg.ne', Real.log_exp] at h1
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem constrainedBase_dist_le {n : ℕ} (U V : EnergySpace n) (h t u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (x y x' y' : Fin n → ℝ) {ε : ℝ}
    (hx : ∀ σ, |guerraH n U h t x σ - guerraH n V h t x' σ| ≤ ε)
    (hy : ∀ τ, |guerraH n U h t y τ - guerraH n V h t y' τ| ≤ ε) :
    |constrainedBase n U h t u x y - constrainedBase n V h t u x' y'| ≤ 2 * ε := by
  classical
  let S := Finset.univ.filter (fun p : Config n × Config n => overlap n p.1 p.2 = u)
  have hS : S.Nonempty := by
    obtain ⟨σ, τ, hστ⟩ := hu
    exact ⟨(σ, τ), by simp [S, hστ]⟩
  have hz (W : EnergySpace n) (a b : Fin n → ℝ) : constrainedZ n W h t u a b =
      ∑ p ∈ S, Real.exp (guerraH n W h t a p.1 + guerraH n W h t b p.2) := by
    simp only [S, Finset.sum_filter, Fintype.sum_prod_type, constrainedZ]
  unfold constrainedBase
  rw [hz, hz]
  apply abs_log_sum_exp_sub_le_on S hS
  intro p _
  have H := abs_add_le (guerraH n U h t x p.1 - guerraH n V h t x' p.1)
    (guerraH n U h t y p.2 - guerraH n V h t y' p.2)
  have he : guerraH n U h t x p.1 + guerraH n U h t y p.2 -
      (guerraH n V h t x' p.1 + guerraH n V h t y' p.2) =
      (guerraH n U h t x p.1 - guerraH n V h t x' p.1) +
      (guerraH n U h t y p.2 - guerraH n V h t y' p.2) := by ring
  rw [he]
  exact H.trans (by linarith [hx p.1, hy p.2])

theorem coupledBase_dist_le {n : ℕ} (U V : EnergySpace n) (h t : ℝ)
    (x y x' y' : Fin n → ℝ) {ε : ℝ}
    (hx : ∀ σ, |guerraH n U h t x σ - guerraH n V h t x' σ| ≤ ε)
    (hy : ∀ τ, |guerraH n U h t y τ - guerraH n V h t y' τ| ≤ ε) :
    |coupledBase n U h t x y - coupledBase n V h t x' y'| ≤ 2 * ε := by
  rw [coupledBase_eq, coupledBase_eq]
  have hx' := abs_log_sum_exp_sub_le hx
  have hy' := abs_log_sum_exp_sub_le hy
  change |guerraBase n U h t x - guerraBase n V h t x'| ≤ ε at hx'
  change |guerraBase n U h t y - guerraBase n V h t y'| ≤ ε at hy'
  have H := abs_add_le (guerraBase n U h t x - guerraBase n V h t x')
    (guerraBase n U h t y - guerraBase n V h t y')
  have he : guerraBase n U h t x + guerraBase n U h t y -
      (guerraBase n V h t x' + guerraBase n V h t y') =
      (guerraBase n U h t x - guerraBase n V h t x') +
      (guerraBase n U h t y - guerraBase n V h t y') := by ring
  rw [he]
  exact H.trans (by linarith)

/-- Lipschitz control in external inputs survives every constrained smoothing step. -/
theorem constrainedCascade_lipschitz {E : Type*} [PseudoMetricSpace E] {n k : ℕ}
    (s : RSBScheme k) (β h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ)
    (U : E → EnergySpace n) (X : E → (Fin n → ℝ)) {L : ℝ≥0}
    (hH : ∀ a σ, LipschitzWith L (fun z => guerraH n (U z) h t (a + X z) σ)) :
    LipschitzWith (2 * L) (fun z =>
      coupledCascade n s β d (constrainedBase n (U z) h t u) j (X z) (X z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have H := coupledCascade_dist_le s β d j
    ((constrainedBase_growth (U z) h u ht hu).translate (X z) (X z))
    ((constrainedBase_growth (U w) h u ht hu).translate (X w) (X w))
    (fun a b => constrainedBase_dist_le (U z) (U w) h t u hu _ _ _ _
      (fun σ => by simpa only [Real.dist_eq] using (hH a σ).dist_le_mul z w)
      (fun τ => by simpa only [Real.dist_eq] using (hH b τ).dist_le_mul z w)) 0 0
  simpa only [coupledCascade_translate, zero_add, Real.dist_eq, NNReal.coe_mul,
    NNReal.coe_ofNat, mul_assoc] using H

theorem coupledCascade_lipschitz {E : Type*} [PseudoMetricSpace E] {n k : ℕ}
    (s : RSBScheme k) (β h : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (d j : ℕ)
    (U : E → EnergySpace n) (X : E → (Fin n → ℝ)) {L : ℝ≥0}
    (hH : ∀ a σ, LipschitzWith L (fun z => guerraH n (U z) h t (a + X z) σ)) :
    LipschitzWith (2 * L) (fun z =>
      coupledCascade n s β d (coupledBase n (U z) h t) j (X z) (X z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have H := coupledCascade_dist_le s β d j
    ((coupledBase_growth n (U z) h ht).translate (X z) (X z))
    ((coupledBase_growth n (U w) h ht).translate (X w) (X w))
    (fun a b => coupledBase_dist_le (U z) (U w) h t _ _ _ _
      (fun σ => by simpa only [Real.dist_eq] using (hH a σ).dist_le_mul z w)
      (fun τ => by simpa only [Real.dist_eq] using (hH b τ).dist_le_mul z w)) 0 0
  simpa only [coupledCascade_translate, zero_add, Real.dist_eq, NNReal.coe_mul,
    NNReal.coe_ofNat, mul_assoc] using H

/-- The unnormalised pressure gap at an intermediate coupled-cascade depth. -/
noncomputable def coupledGap {k : ℕ} (n : ℕ) (s : RSBScheme k) (β : ℝ)
    (U : EnergySpace n) (h t u : ℝ) (d j : ℕ) (x : Fin n → ℝ) : ℝ :=
  coupledCascade n s β d (constrainedBase n U h t u) j x x -
    coupledCascade n s β d (coupledBase n U h t) j x x

theorem coupledGap_lipschitz {E : Type*} [PseudoMetricSpace E] {n k : ℕ}
    (s : RSBScheme k) (β h u : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ)
    (U : E → EnergySpace n) (X : E → (Fin n → ℝ)) {L : ℝ≥0}
    (hH : ∀ a σ, LipschitzWith L (fun z => guerraH n (U z) h t (a + X z) σ)) :
    LipschitzWith (4 * L) (fun z => coupledGap n s β (U z) h t u d j (X z)) := by
  have H := (constrainedCascade_lipschitz s β h u ht hu d j U X hH).sub
    (coupledCascade_lipschitz s β h ht d j U X hH)
  rw [show (2 * L + 2 * L : ℝ≥0) = 4 * L by ring] at H
  exact H

end SpinGlass.Targets
