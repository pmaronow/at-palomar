module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
/- Adapted for the paper formalization: replaced 1 native decision tactics with kernel decide. Original source and pinned revision are recorded in PROVENANCE.json. -/
public import Lemmas.AT.Definitions
public import Lemmas.SpinGlass.Replicas
public import Lemmas.SmartPath.IndependentGaussianAffineIBP
public import Lemmas.SmartPath.IndependentEndpoint
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal

set_option autoImplicit false

namespace SpinGlass.AT

universe u

/-!
# Last-site cavity interpolation

The definitions in this file split an energy into its even and odd parts under
flipping one spin.  This avoids changing the configuration type from `Fin N`
to `Fin (N - 1)` and makes the overlap-with-one-site-removed identity exact.
-/

/-- Flip one site of a spin configuration. -/
def flipSite {N : ℕ} (i : Fin N) (σ : SpinGlass.Config N) : SpinGlass.Config N :=
  Function.update σ i (!σ i)

@[simp] lemma flipSite_apply_same {N : ℕ} (i : Fin N)
    (σ : SpinGlass.Config N) : flipSite i σ i = !σ i := by
  simp [flipSite]

@[simp] lemma flipSite_apply_of_ne {N : ℕ} {i j : Fin N} (hji : j ≠ i)
    (σ : SpinGlass.Config N) : flipSite i σ j = σ j := by
  simp [flipSite, hji]

@[simp] lemma flipSite_involutive {N : ℕ} (i : Fin N)
    (σ : SpinGlass.Config N) : flipSite i (flipSite i σ) = σ := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipSite]
  · simp [flipSite, hji]

@[simp] lemma spin_flipSite_same {N : ℕ} (i : Fin N)
    (σ : SpinGlass.Config N) :
    SpinGlass.spin N (flipSite i σ) i = -SpinGlass.spin N σ i := by
  simp [SpinGlass.spin, flipSite]
  cases h : σ i <;> simp

@[simp] lemma spin_flipSite_of_ne {N : ℕ} {i j : Fin N} (hji : j ≠ i)
    (σ : SpinGlass.Config N) :
    SpinGlass.spin N (flipSite i σ) j = SpinGlass.spin N σ j := by
  simp [SpinGlass.spin, flipSite, hji]

/-- Even part of an energy under a one-site flip. -/
noncomputable def siteEvenCLM {N : ℕ} (i : Fin N) :
    SpinGlass.EnergySpace N →L[ℝ] SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => WithLp.toLp 2 (fun σ => (H σ + H (flipSite i σ)) / 2)
      map_add' := by
        intro H K
        ext σ
        simp
        ring
      map_smul' := by
        intro c H
        ext σ
        simp
        ring }

/-- Odd part of an energy under a one-site flip. -/
noncomputable def siteOddCLM {N : ℕ} (i : Fin N) :
    SpinGlass.EnergySpace N →L[ℝ] SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => WithLp.toLp 2 (fun σ => (H σ - H (flipSite i σ)) / 2)
      map_add' := by
        intro H K
        ext σ
        simp
        ring
      map_smul' := by
        intro c H
        ext σ
        simp
        ring }

@[simp] lemma siteEvenCLM_apply {N : ℕ} (i : Fin N)
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    siteEvenCLM i H σ = (H σ + H (flipSite i σ)) / 2 := rfl

@[simp] lemma siteOddCLM_apply {N : ℕ} (i : Fin N)
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    siteOddCLM i H σ = (H σ - H (flipSite i σ)) / 2 := rfl

lemma siteEven_add_siteOdd {N : ℕ} (i : Fin N)
    (H : SpinGlass.EnergySpace N) : siteEvenCLM i H + siteOddCLM i H = H := by
  ext σ
  simp
  ring

@[simp] lemma siteEven_flip {N : ℕ} (i : Fin N)
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    siteEvenCLM i H (flipSite i σ) = siteEvenCLM i H σ := by
  simp [siteEvenCLM_apply, add_comm]

@[simp] lemma siteOdd_flip {N : ℕ} (i : Fin N)
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    siteOddCLM i H (flipSite i σ) = -siteOddCLM i H σ := by
  simp [siteOddCLM_apply]
  ring

/-- The overlap with the contribution of site `i` removed, retaining the
normalization `1/N` used in the cavity calculation. -/
noncomputable def cavityOverlapAt {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) : ℝ :=
  centeredOverlap q σs a b -
    (1 / (N : ℝ)) * SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i

lemma centeredOverlap_eq_cavityOverlapAt_add {N n : ℕ} (q : ℝ) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) :
    centeredOverlap q σs a b = cavityOverlapAt q i σs a b +
      (1 / (N : ℝ)) * SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i := by
  simp [cavityOverlapAt]

lemma abs_cavityOverlapAt_le_two {N n : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (i : Fin N)
    (σs : Replicas N n) (a b : Fin n) :
    |cavityOverlapAt q i σs a b| ≤ 2 := by
  let x : Fin N → ℝ := fun j =>
    if j = i then 0 else SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j
  have hxlower : ∀ j, (-1 : ℝ) ≤ x j := by
    intro j
    simp only [x]
    split
    · norm_num
    · cases ha : σs a j <;> cases hb : σs b j <;>
        simp [SpinGlass.spin, ha, hb]
  have hxupper : ∀ j, x j ≤ (1 : ℝ) := by
    intro j
    simp only [x]
    split
    · norm_num
    · cases ha : σs a j <;> cases hb : σs b j <;>
        simp [SpinGlass.spin, ha, hb]
  have hsumlower : -(N : ℝ) ≤ ∑ j, x j := by
    calc
      -(N : ℝ) = ∑ _j : Fin N, (-1 : ℝ) := by simp
      _ ≤ ∑ j, x j := Finset.sum_le_sum fun j _ => hxlower j
  have hsumupper : ∑ j, x j ≤ (N : ℝ) := by
    calc
      ∑ j, x j ≤ ∑ _j : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hxupper j
      _ = (N : ℝ) := by simp
  have hsum : ∑ j, x j =
      ∑ j, SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j -
        SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i := by
    classical
    have hxerase : ∑ j ∈ (Finset.univ.erase i), x j =
        ∑ j ∈ (Finset.univ.erase i),
          SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [x, hji]
    have hfull := Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j)
      (Finset.mem_univ i)
    calc
      ∑ j, x j = ∑ j ∈ (Finset.univ.erase i), x j := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp [x]
      _ = ∑ j ∈ (Finset.univ.erase i),
          SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j := hxerase
      _ = ∑ j, SpinGlass.spin N (σs a) j * SpinGlass.spin N (σs b) j -
          SpinGlass.spin N (σs a) i * SpinGlass.spin N (σs b) i := by
        linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcav : cavityOverlapAt q i σs a b =
      (1 / (N : ℝ)) * (∑ j, x j) - q := by
    rw [cavityOverlapAt, centeredOverlap, replicaOverlap, SpinGlass.overlap, hsum]
    ring
  rw [hcav, abs_le]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hsumlower (by positivity : 0 ≤ (1 / (N : ℝ)))
    have hnorm : (1 / (N : ℝ)) * (-(N : ℝ)) = -1 := by field_simp
    rw [hnorm] at hmul
    linarith [hq.2]
  · have hmul := mul_le_mul_of_nonneg_left hsumupper (by positivity : 0 ≤ (1 / (N : ℝ)))
    have hnorm : (1 / (N : ℝ)) * (N : ℝ) = 1 := by field_simp
    rw [hnorm] at hmul
    linarith [hq.1]

/-- Uncentered overlap with site `i` removed and normalization `1/N`. -/
noncomputable def configCavityOverlapAt {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) : ℝ :=
  SpinGlass.overlap N σ τ -
    (1 / (N : ℝ)) * SpinGlass.spin N σ i * SpinGlass.spin N τ i

/-- The selected-spin covariance kernel with the RS contribution removed. -/
noncomputable def cavityInteractionAt {N : ℕ} (q : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) : ℝ :=
  SpinGlass.spin N σ i * SpinGlass.spin N τ i *
    (configCavityOverlapAt i σ τ - q)

lemma abs_cavityInteractionAt_le_two {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    |cavityInteractionAt q i σ τ| ≤ 2 := by
  let σs : Replicas N 2 := ![σ, τ]
  have hcav := abs_cavityOverlapAt_le_two hN hq i σs 0 1
  have hbracket : configCavityOverlapAt i σ τ - q =
      cavityOverlapAt q i σs 0 1 := by
    simp [cavityOverlapAt, centeredOverlap, replicaOverlap,
      configCavityOverlapAt, σs]
    ring
  have heq : cavityInteractionAt q i σ τ =
      SpinGlass.spin N σ i * SpinGlass.spin N τ i *
        cavityOverlapAt q i σs 0 1 := by
    rw [cavityInteractionAt, hbracket]
  rw [heq, abs_mul, abs_mul]
  have hσ : |SpinGlass.spin N σ i| = 1 := by
    cases hval : σ i <;> simp [SpinGlass.spin, hval]
  have hτ : |SpinGlass.spin N τ i| = 1 := by
    cases hval : τ i <;> simp [SpinGlass.spin, hval]
  simpa [hσ, hτ] using hcav

lemma cavityInteractionAt_comm {N : ℕ} (q : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    cavityInteractionAt q i σ τ = cavityInteractionAt q i τ σ := by
  have hoverlap : SpinGlass.overlap N σ τ = SpinGlass.overlap N τ σ := by
    unfold SpinGlass.overlap
    apply congrArg (fun x : ℝ => (1 / (N : ℝ)) * x)
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [cavityInteractionAt, configCavityOverlapAt]
  rw [hoverlap]
  ring

lemma cavityInteractionAt_diag {N : ℕ} (q : ℝ) (i : Fin N)
    (σ : SpinGlass.Config N) :
    cavityInteractionAt q i σ σ = 1 - (1 / (N : ℝ)) - q := by
  have hN : 0 < N := by
    exact Nat.pos_of_ne_zero (fun hN => by subst N; exact Fin.elim0 i)
  rw [cavityInteractionAt, configCavityOverlapAt,
    SpinGlass.overlap_self (N := N) hN σ]
  have hspin : SpinGlass.spin N σ i * SpinGlass.spin N σ i = 1 := by
    cases h : σ i <;> simp [SpinGlass.spin, h]
  have hterm : (1 / (N : ℝ)) * SpinGlass.spin N σ i * SpinGlass.spin N σ i =
      1 / (N : ℝ) := by
    calc
      _ = (1 / (N : ℝ)) *
          (SpinGlass.spin N σ i * SpinGlass.spin N σ i) := by ring
      _ = _ := by rw [hspin]; ring
  rw [hspin, hterm]
  ring

lemma cavityOverlapAt_eq_configCavityOverlapAt_sub {N n : ℕ} (q : ℝ)
    (i : Fin N) (σs : Replicas N n) (a b : Fin n) :
    cavityOverlapAt q i σs a b =
      configCavityOverlapAt i (σs a) (σs b) - q := by
  simp [cavityOverlapAt, configCavityOverlapAt, centeredOverlap, replicaOverlap]
  ring

lemma overlap_eq_configCavityOverlapAt_add {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    SpinGlass.overlap N σ τ = configCavityOverlapAt i σ τ +
      (1 / (N : ℝ)) * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  simp [configCavityOverlapAt]

private lemma sum_spin_flipSite_left {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    (∑ j, SpinGlass.spin N (flipSite i σ) j * SpinGlass.spin N τ j) =
      (∑ j, SpinGlass.spin N σ j * SpinGlass.spin N τ j) -
        2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => SpinGlass.spin N σ j * SpinGlass.spin N τ j) (Finset.mem_univ i)]
  have heq : ∑ j ∈ (Finset.univ.erase i),
      SpinGlass.spin N (flipSite i σ) j * SpinGlass.spin N τ j =
      ∑ j ∈ (Finset.univ.erase i),
        SpinGlass.spin N σ j * SpinGlass.spin N τ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [spin_flipSite_of_ne (Finset.ne_of_mem_erase hj)]
  rw [heq, spin_flipSite_same]
  ring

lemma overlap_flipSite_left {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    SpinGlass.overlap N (flipSite i σ) τ =
      SpinGlass.overlap N σ τ -
        (2 / (N : ℝ)) * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  rw [SpinGlass.overlap, SpinGlass.overlap, sum_spin_flipSite_left]
  ring

lemma overlap_flipSite_right {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    SpinGlass.overlap N σ (flipSite i τ) =
      SpinGlass.overlap N σ τ -
        (2 / (N : ℝ)) * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  simp only [SpinGlass.overlap]
  have hcomm : (∑ j, SpinGlass.spin N σ j * SpinGlass.spin N (flipSite i τ) j) =
      ∑ j, SpinGlass.spin N (flipSite i τ) j * SpinGlass.spin N σ j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcomm0 : (∑ j, SpinGlass.spin N τ j * SpinGlass.spin N σ j) =
      ∑ j, SpinGlass.spin N σ j * SpinGlass.spin N τ j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm, sum_spin_flipSite_left]
  have hNnat : N ≠ 0 := by
    intro h
    subst N
    exact Fin.elim0 i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  field_simp [hN]
  rw [hcomm0]

lemma overlap_flipSite_both {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    SpinGlass.overlap N (flipSite i σ) (flipSite i τ) =
      SpinGlass.overlap N σ τ := by
  rw [overlap_flipSite_left, overlap_flipSite_right, spin_flipSite_same]
  ring

@[simp] lemma configCavityOverlapAt_flip_left {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    configCavityOverlapAt i (flipSite i σ) τ =
      configCavityOverlapAt i σ τ := by
  simp only [configCavityOverlapAt]
  rw [overlap_flipSite_left, spin_flipSite_same]
  have hNnat : N ≠ 0 := by
    intro h
    subst N
    exact Fin.elim0 i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  field_simp [hN]
  ring

@[simp] lemma configCavityOverlapAt_flip_right {N : ℕ} (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    configCavityOverlapAt i σ (flipSite i τ) =
      configCavityOverlapAt i σ τ := by
  simp only [configCavityOverlapAt]
  rw [overlap_flipSite_right, spin_flipSite_same]
  have hNnat : N ≠ 0 := by
    intro h
    subst N
    exact Fin.elim0 i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  field_simp [hN]
  ring

lemma skKernel_odd_difference {N : ℕ} (β : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    (SpinGlass.sk_cov_kernel N β σ τ -
        SpinGlass.sk_cov_kernel N β (flipSite i σ) τ -
        SpinGlass.sk_cov_kernel N β σ (flipSite i τ) +
        SpinGlass.sk_cov_kernel N β (flipSite i σ) (flipSite i τ)) / 4 =
      β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
        configCavityOverlapAt i σ τ := by
  have hsσ : SpinGlass.spin N σ i ^ 2 = 1 := by
    cases h : σ i <;> simp [SpinGlass.spin, h]
  have hsτ : SpinGlass.spin N τ i ^ 2 = 1 := by
    cases h : τ i <;> simp [SpinGlass.spin, h]
  have hNnat : N ≠ 0 := by
    intro h
    subst N
    exact Fin.elim0 i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  rw [SpinGlass.sk_cov_kernel, SpinGlass.sk_cov_kernel,
    SpinGlass.sk_cov_kernel, SpinGlass.sk_cov_kernel,
    overlap_flipSite_left, overlap_flipSite_right,
    overlap_flipSite_both, configCavityOverlapAt]
  field_simp [hN]
  nlinarith

lemma simpleKernel_odd_difference {N : ℕ} (β q : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    (SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ -
        SpinGlass.simple_cov_kernel N β (fun x => q * x) (flipSite i σ) τ -
        SpinGlass.simple_cov_kernel N β (fun x => q * x) σ (flipSite i τ) +
        SpinGlass.simple_cov_kernel N β (fun x => q * x)
          (flipSite i σ) (flipSite i τ)) / 4 =
      β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  rw [SpinGlass.simple_cov_kernel, SpinGlass.simple_cov_kernel,
    SpinGlass.simple_cov_kernel, SpinGlass.simple_cov_kernel,
    overlap_flipSite_left, overlap_flipSite_right, overlap_flipSite_both]
  have hNnat : N ≠ 0 := by
    intro h
    subst N
    exact Fin.elim0 i
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  field_simp [hN]
  ring

lemma skKernel_even_odd_difference {N : ℕ} (β : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    (SpinGlass.sk_cov_kernel N β σ τ -
        SpinGlass.sk_cov_kernel N β σ (flipSite i τ) +
        SpinGlass.sk_cov_kernel N β (flipSite i σ) τ -
        SpinGlass.sk_cov_kernel N β (flipSite i σ) (flipSite i τ)) / 4 = 0 := by
  rw [SpinGlass.sk_cov_kernel, SpinGlass.sk_cov_kernel,
    SpinGlass.sk_cov_kernel, SpinGlass.sk_cov_kernel,
    overlap_flipSite_left, overlap_flipSite_right, overlap_flipSite_both]
  ring

lemma simpleKernel_even_odd_difference {N : ℕ} (β q : ℝ) (i : Fin N)
    (σ τ : SpinGlass.Config N) :
    (SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ -
        SpinGlass.simple_cov_kernel N β (fun x => q * x) σ (flipSite i τ) +
        SpinGlass.simple_cov_kernel N β (fun x => q * x) (flipSite i σ) τ -
        SpinGlass.simple_cov_kernel N β (fun x => q * x)
          (flipSite i σ) (flipSite i τ)) / 4 = 0 := by
  rw [SpinGlass.simple_cov_kernel, SpinGlass.simple_cov_kernel,
    SpinGlass.simple_cov_kernel, SpinGlass.simple_cov_kernel,
    overlap_flipSite_left, overlap_flipSite_right, overlap_flipSite_both]
  ring

lemma sk_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h : ℝ} (sk : SpinGlass.SKDisorder (Ω := Ω) N β h)
    (σ τ : SpinGlass.Config N) :
    (∑ k : sk.hU.ι, (sk.hU.τ k : ℝ) * sk.hU.w k σ * sk.hU.w k τ) =
      SpinGlass.sk_cov_kernel N β σ τ := by
  have hcov := sk.cov_eq σ τ
  simp only [PhysLean.Probability.GaussianIBP.covOp_apply,
    sum_inner, inner_smul_left, SpinGlass.inner_std_basis_apply,
    real_inner_comm] at hcov
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcov

lemma simple_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (σ τ : SpinGlass.Config N) :
    (∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) * sim.hV.w k σ * sim.hV.w k τ) =
      SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ := by
  have hcov := sim.cov_eq σ τ
  simp only [PhysLean.Probability.GaussianIBP.covOp_apply,
    sum_inner, inner_smul_left, SpinGlass.inner_std_basis_apply,
    real_inner_comm] at hcov
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcov

/-- Covariance of two continuous linear observations of a Gaussian Hilbert
random variable, expressed in its finite independent-coordinate model. -/
lemma gaussianHilbert_covariance_clm
    {Ω H : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (L₁ L₂ : H →L[ℝ] ℝ) :
    covariance (fun ω => L₁ (g ω)) (fun ω => L₂ (g ω)) volume =
      ∑ k : hg.ι, (hg.τ k : ℝ) * L₁ (hg.w k) * L₂ (hg.w k) := by
  classical
  have hcLaw (k : hg.ι) : HasGaussianLaw (hg.c k) volume :=
    HasLaw.hasGaussianLaw
      (HasLaw.mk (P := volume) (hg.c_meas k).aemeasurable (hg.c_gauss k))
  have hcMem (k : hg.ι) : MemLp (hg.c k) 2 volume := (hcLaw k).memLp_two
  have hcov (k l : hg.ι) :
      covariance (hg.c k) (hg.c l) volume =
        if k = l then (hg.τ k : ℝ) else 0 := by
    by_cases hkl : k = l
    · subst l
      rw [if_pos rfl, covariance_self (hg.c_meas k).aemeasurable]
      have hv := (HasLaw.mk (P := volume) (hg.c_meas k).aemeasurable
        (hg.c_gauss k)).variance_eq
      simpa [variance_id_gaussianReal] using hv
    · rw [if_neg hkl]
      exact (hg.c_indep.indepFun hkl).covariance_eq_zero (hcMem k) (hcMem l)
  have hL₁ : (fun ω => L₁ (g ω)) =
      fun ω => ∑ k : hg.ι, L₁ (hg.w k) * hg.c k ω := by
    funext ω
    rw [congrFun hg.repr ω]
    simp [mul_comm]
  have hL₂ : (fun ω => L₂ (g ω)) =
      fun ω => ∑ k : hg.ι, L₂ (hg.w k) * hg.c k ω := by
    funext ω
    rw [congrFun hg.repr ω]
    simp [mul_comm]
  rw [hL₁, hL₂, covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
    simp [mul_left_comm, mul_comm]
  · intro k
    exact (hcMem k).const_mul _
  · intro k
    exact (hcMem k).const_mul _

/-- A continuous bilinear form on the energy space, expanded in the
configuration basis. -/
lemma bilinear_expand_config {N : ℕ}
    (Q : SpinGlass.EnergySpace N →L[ℝ] SpinGlass.EnergySpace N →L[ℝ] ℝ)
    (v w : SpinGlass.EnergySpace N) :
    Q v w = ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      v σ * w τ * Q (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) := by
  classical
  have hcomplete (x : SpinGlass.EnergySpace N) :
      x = ∑ σ : SpinGlass.Config N, x σ • SpinGlass.std_basis N σ := by
    ext τ
    simp [SpinGlass.std_basis]
  conv_lhs =>
    rw [hcomplete v, hcomplete w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- The Gaussian eigenbasis trace of a continuous bilinear form, written as
a double sum over configurations. -/
lemma gaussianHilbert_bilinear_trace_eq_config
    {Ω H : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} {g : Ω → H}
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (A B : H →L[ℝ] SpinGlass.EnergySpace N)
    (Q : SpinGlass.EnergySpace N →L[ℝ] SpinGlass.EnergySpace N →L[ℝ] ℝ) :
    (∑ k : hg.ι, (hg.τ k : ℝ) * Q (B (hg.w k)) (A (hg.w k))) =
      ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        covariance
            (fun ω => B (g ω) σ)
            (fun ω => A (g ω) τ) volume *
          Q (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) := by
  classical
  have hcov (σ τ : SpinGlass.Config N) :
      covariance (fun ω => B (g ω) σ) (fun ω => A (g ω) τ) volume =
        ∑ k : hg.ι, (hg.τ k : ℝ) * B (hg.w k) σ * A (hg.w k) τ := by
    simpa using gaussianHilbert_covariance_clm hg
      ((SpinGlass.evalCLM (N := N) σ).comp B)
      ((SpinGlass.evalCLM (N := N) τ).comp A)
  calc
    (∑ k : hg.ι, (hg.τ k : ℝ) * Q (B (hg.w k)) (A (hg.w k))) =
        ∑ k : hg.ι, (hg.τ k : ℝ) *
          (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
            B (hg.w k) σ * A (hg.w k) τ *
              Q (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [bilinear_expand_config]
    _ = ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        covariance
            (fun ω => B (g ω) σ)
            (fun ω => A (g ω) τ) volume *
          Q (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) := by
      simp_rw [hcov, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro τ _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The abstract covariance operator of the simple disorder agrees with the
probabilistic covariance of point evaluations. -/
lemma simple_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (σ τ : SpinGlass.Config N) :
    covariance (fun ω => sim.V ω σ) (fun ω => sim.V ω τ) volume =
      SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ := by
  have hpair := gaussianHilbert_covariance_clm sim.hV
    (SpinGlass.evalCLM (N := N) σ) (SpinGlass.evalCLM (N := N) τ)
  calc
    covariance (fun ω => sim.V ω σ) (fun ω => sim.V ω τ) volume =
        ∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) *
          sim.hV.w k σ * sim.hV.w k τ := by simpa using hpair
    _ = SpinGlass.simple_cov_kernel N β (fun x => q * x) σ τ :=
      simple_basis_covariance_sum sim σ τ

lemma sk_siteOdd_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h : ℝ} (sk : SpinGlass.SKDisorder (Ω := Ω) N β h)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    (∑ k : sk.hU.ι, (sk.hU.τ k : ℝ) *
        siteOddCLM i (sk.hU.w k) σ * siteOddCLM i (sk.hU.w k) τ) =
      β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
        configCavityOverlapAt i σ τ := by
  rw [← skKernel_odd_difference β i σ τ]
  simp_rw [siteOddCLM_apply]
  rw [← sk_basis_covariance_sum sk σ τ,
    ← sk_basis_covariance_sum sk (flipSite i σ) τ,
    ← sk_basis_covariance_sum sk σ (flipSite i τ),
    ← sk_basis_covariance_sum sk (flipSite i σ) (flipSite i τ)]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  ring

lemma simple_siteOdd_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    (∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) *
        siteOddCLM i (sim.hV.w k) σ * siteOddCLM i (sim.hV.w k) τ) =
      β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  rw [← simpleKernel_odd_difference β q i σ τ]
  simp_rw [siteOddCLM_apply]
  rw [← simple_basis_covariance_sum sim σ τ,
    ← simple_basis_covariance_sum sim (flipSite i σ) τ,
    ← simple_basis_covariance_sum sim σ (flipSite i τ),
    ← simple_basis_covariance_sum sim (flipSite i σ) (flipSite i τ)]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- Covariance of two point evaluations of the odd SK component. -/
lemma sk_siteOdd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h : ℝ} (sk : SpinGlass.SKDisorder (Ω := Ω) N β h)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => siteOddCLM i (sk.U ω) σ)
      (fun ω => siteOddCLM i (sk.U ω) τ) volume =
        β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          configCavityOverlapAt i σ τ := by
  have hpair := gaussianHilbert_covariance_clm sk.hU
    ((SpinGlass.evalCLM (N := N) σ).comp (siteOddCLM i))
    ((SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i))
  calc
    covariance (fun ω => siteOddCLM i (sk.U ω) σ)
        (fun ω => siteOddCLM i (sk.U ω) τ) volume =
      ∑ k : sk.hU.ι, (sk.hU.τ k : ℝ) *
        siteOddCLM i (sk.hU.w k) σ * siteOddCLM i (sk.hU.w k) τ := by
          simpa using hpair
    _ = _ := sk_siteOdd_basis_covariance_sum sk i σ τ

/-- Covariance of two point evaluations of the odd simple component. -/
lemma simple_siteOdd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => siteOddCLM i (sim.V ω) σ)
      (fun ω => siteOddCLM i (sim.V ω) τ) volume =
        β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i := by
  have hpair := gaussianHilbert_covariance_clm sim.hV
    ((SpinGlass.evalCLM (N := N) σ).comp (siteOddCLM i))
    ((SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i))
  calc
    covariance (fun ω => siteOddCLM i (sim.V ω) σ)
        (fun ω => siteOddCLM i (sim.V ω) τ) volume =
      ∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) *
        siteOddCLM i (sim.hV.w k) σ * siteOddCLM i (sim.hV.w k) τ := by
          simpa using hpair
    _ = _ := simple_siteOdd_basis_covariance_sum sim i σ τ

lemma sk_siteEven_siteOdd_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h : ℝ} (sk : SpinGlass.SKDisorder (Ω := Ω) N β h)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    (∑ k : sk.hU.ι, (sk.hU.τ k : ℝ) *
        siteEvenCLM i (sk.hU.w k) σ * siteOddCLM i (sk.hU.w k) τ) = 0 := by
  rw [← skKernel_even_odd_difference β i σ τ]
  simp_rw [siteEvenCLM_apply, siteOddCLM_apply]
  rw [← sk_basis_covariance_sum sk σ τ,
    ← sk_basis_covariance_sum sk σ (flipSite i τ),
    ← sk_basis_covariance_sum sk (flipSite i σ) τ,
    ← sk_basis_covariance_sum sk (flipSite i σ) (flipSite i τ)]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

lemma simple_siteEven_siteOdd_basis_covariance_sum
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    (∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) *
        siteEvenCLM i (sim.hV.w k) σ * siteOddCLM i (sim.hV.w k) τ) = 0 := by
  rw [← simpleKernel_even_odd_difference β q i σ τ]
  simp_rw [siteEvenCLM_apply, siteOddCLM_apply]
  rw [← simple_basis_covariance_sum sim σ τ,
    ← simple_basis_covariance_sum sim σ (flipSite i τ),
    ← simple_basis_covariance_sum sim (flipSite i σ) τ,
    ← simple_basis_covariance_sum sim (flipSite i σ) (flipSite i τ)]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

/-- Point evaluations of the even and odd parts of the simple disorder have
zero cross covariance. -/
lemma simple_siteEven_siteOdd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β q : ℝ} (sim : SpinGlass.SimpleDisorder (Ω := Ω) N β q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => siteEvenCLM i (sim.V ω) σ)
      (fun ω => siteOddCLM i (sim.V ω) τ) volume = 0 := by
  have hpair := gaussianHilbert_covariance_clm sim.hV
    ((SpinGlass.evalCLM (N := N) σ).comp (siteEvenCLM i))
    ((SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i))
  calc
    covariance (fun ω => siteEvenCLM i (sim.V ω) σ)
        (fun ω => siteOddCLM i (sim.V ω) τ) volume =
      ∑ k : sim.hV.ι, (sim.hV.τ k : ℝ) *
        siteEvenCLM i (sim.hV.w k) σ *
          siteOddCLM i (sim.hV.w k) τ := by simpa using hpair
    _ = 0 := simple_siteEven_siteOdd_basis_covariance_sum sim i σ τ

/-- A continuous linear observation of a Gaussian Hilbert random variable is
square-integrable. -/
lemma gaussianHilbert_clm_memLp_two
    {Ω H : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {g : Ω → H} (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (L : H →L[ℝ] ℝ) :
    MemLp (fun ω => L (g ω)) 2 volume :=
  ((SpinGlass.GeneralizedLatala.gaussianHilbert_hasGaussianLaw hg).map_fun L).memLp_two

/-- The even SK component and odd simple component have zero cross covariance;
this is inherited from the independence already carried by the smart path. -/
lemma skEven_simpleOdd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => siteEvenCLM i (path.sk.U ω) σ)
      (fun ω => siteOddCLM i (path.simple.V ω) τ) volume = 0 := by
  let L₁ := (SpinGlass.evalCLM (N := N) σ).comp (siteEvenCLM i)
  let L₂ := (SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i)
  have hind : IndepFun (fun ω => L₁ (path.sk.U ω))
      (fun ω => L₂ (path.simple.V ω)) volume :=
    path.independent.comp (by fun_prop) (by fun_prop)
  have h₁ : MemLp (fun ω => L₁ (path.sk.U ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.sk.hU L₁
  have h₂ : MemLp (fun ω => L₂ (path.simple.V ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.simple.hV L₂
  simpa [L₁, L₂] using hind.covariance_eq_zero h₁ h₂

/-- The odd SK and odd simple point evaluations are independent, hence have
zero covariance. -/
lemma skOdd_simpleOdd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => siteOddCLM i (path.sk.U ω) σ)
      (fun ω => siteOddCLM i (path.simple.V ω) τ) volume = 0 := by
  let L₁ := (SpinGlass.evalCLM (N := N) σ).comp (siteOddCLM i)
  let L₂ := (SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i)
  have hind : IndepFun (fun ω => L₁ (path.sk.U ω))
      (fun ω => L₂ (path.simple.V ω)) volume :=
    path.independent.comp (by fun_prop) (by fun_prop)
  have h₁ : MemLp (fun ω => L₁ (path.sk.U ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.sk.hU L₁
  have h₂ : MemLp (fun ω => L₂ (path.simple.V ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.simple.hV L₂
  simpa [L₁, L₂] using hind.covariance_eq_zero h₁ h₂

/-! ## Joint Gaussian endpoint packaging -/

/-- The random bulk energy at the decoupled endpoint. -/
noncomputable def lastSiteBulkRandom
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) : SpinGlass.EnergySpace N :=
  Real.sqrt s • siteEvenCLM i (path.sk.U ω) +
    Real.sqrt (1 - s) • siteEvenCLM i (path.simple.V ω)

/-- The odd simple-disorder component used as the last-site reference field. -/
noncomputable def lastSiteOddRandom
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) : SpinGlass.EnergySpace N :=
  siteOddCLM i (path.simple.V ω)

/-- The linear map sending the joint disorder `(U,V)` to the decoupled
endpoint pair consisting of its even bulk and odd reference components. -/
noncomputable def lastSiteEvenOddCLM {N : ℕ} (i : Fin N) (s : ℝ) :
    WithLp 2 (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N × SpinGlass.EnergySpace N :=
  let unpack :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ
      (SpinGlass.EnergySpace N) (SpinGlass.EnergySpace N)).toContinuousLinearMap
  let first : WithLp 2 (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
    (ContinuousLinearMap.fst ℝ (SpinGlass.EnergySpace N)
      (SpinGlass.EnergySpace N)).comp unpack
  let second : WithLp 2 (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
    (ContinuousLinearMap.snd ℝ (SpinGlass.EnergySpace N)
      (SpinGlass.EnergySpace N)).comp unpack
  ((Real.sqrt s) • (siteEvenCLM i).comp first +
      (Real.sqrt (1 - s)) • (siteEvenCLM i).comp second).prod
    ((siteOddCLM i).comp second)

@[simp] lemma lastSiteEvenOddCLM_apply {N : ℕ} (i : Fin N) (s : ℝ)
    (U V : SpinGlass.EnergySpace N) :
    lastSiteEvenOddCLM i s (WithLp.toLp 2 (U, V)) =
      (Real.sqrt s • siteEvenCLM i U +
        Real.sqrt (1 - s) • siteEvenCLM i V,
        siteOddCLM i V) := by
  rfl

/-- The endpoint even/odd pair is jointly Gaussian. -/
lemma lastSite_evenOdd_hasGaussianLaw
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) :
    HasGaussianLaw
      (fun ω => (lastSiteBulkRandom (s := s) path i ω,
        lastSiteOddRandom path i ω)) (volume : Measure Ω) := by
  have hUV := SpinGlass.isGaussianHilbert_UV
    (N := N) (β := β) (h := h) (q := q)
    path.sk path.simple path.independent
  have hLaw :=
    SpinGlass.GeneralizedLatala.gaussianHilbert_hasGaussianLaw hUV
  have hmap := hLaw.map_fun (lastSiteEvenOddCLM i s)
  simpa [SpinGlass.UV, lastSiteBulkRandom, lastSiteOddRandom] using hmap

/-- Every point evaluation of the decoupled bulk has zero covariance with
every point evaluation of the odd reference field. -/
lemma lastSite_bulk_odd_point_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    covariance (fun ω => lastSiteBulkRandom (s := s) path i ω σ)
      (fun ω => lastSiteOddRandom path i ω τ) volume = 0 := by
  let Lsk := (SpinGlass.evalCLM (N := N) σ).comp (siteEvenCLM i)
  let LsimEven := (SpinGlass.evalCLM (N := N) σ).comp (siteEvenCLM i)
  let LsimOdd := (SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i)
  have hsk : MemLp (fun ω => Lsk (path.sk.U ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.sk.hU Lsk
  have hsimEven : MemLp (fun ω => LsimEven (path.simple.V ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.simple.hV LsimEven
  have hsimOdd : MemLp (fun ω => LsimOdd (path.simple.V ω)) 2 volume :=
    gaussianHilbert_clm_memLp_two path.simple.hV LsimOdd
  let X : Ω → ℝ := fun ω => Real.sqrt s * Lsk (path.sk.U ω)
  let Y : Ω → ℝ := fun ω => Real.sqrt (1 - s) * LsimEven (path.simple.V ω)
  let Z : Ω → ℝ := fun ω => LsimOdd (path.simple.V ω)
  change covariance (X + Y) Z volume = 0
  rw [covariance_add_left (hsk.const_mul _) (hsimEven.const_mul _) hsimOdd,
    covariance_const_mul_left, covariance_const_mul_left]
  have hcrossSk := skEven_simpleOdd_point_covariance path i σ τ
  have hcrossSim :=
    simple_siteEven_siteOdd_point_covariance path.simple i σ τ
  change covariance (fun ω => Lsk (path.sk.U ω))
      (fun ω => LsimOdd (path.simple.V ω)) volume = 0 at hcrossSk
  change covariance (fun ω => LsimEven (path.simple.V ω))
      (fun ω => LsimOdd (path.simple.V ω)) volume = 0 at hcrossSim
  rw [hcrossSk, hcrossSim]
  ring

/-- Inner products in the finite energy space are finite sums of point
evaluations. -/
lemma energy_inner_eq_sum_apply {N : ℕ}
    (x H : SpinGlass.EnergySpace N) :
    inner ℝ x H = ∑ σ : SpinGlass.Config N, x σ * H σ := by
  simp [PiLp.inner_apply, mul_comm]

/-- At the decoupled endpoint the even bulk disorder and the odd reference
field are independent.  The proof uses joint Gaussianity and the vanishing
cross covariance proved above. -/
lemma lastSite_bulk_indep_odd
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) :
    IndepFun (lastSiteBulkRandom (s := s) path i)
      (lastSiteOddRandom path i) volume := by
  have hLaw := lastSite_evenOdd_hasGaussianLaw (s := s) path i
  apply hLaw.indepFun_of_covariance_inner
  intro x y
  have hx : (fun ω => inner ℝ x (lastSiteBulkRandom (s := s) path i ω)) =
      fun ω => ∑ σ : SpinGlass.Config N,
        x σ * lastSiteBulkRandom (s := s) path i ω σ := by
    funext ω
    exact energy_inner_eq_sum_apply x _
  have hy : (fun ω => inner ℝ y (lastSiteOddRandom path i ω)) =
      fun ω => ∑ τ : SpinGlass.Config N,
        y τ * lastSiteOddRandom path i ω τ := by
    funext ω
    exact energy_inner_eq_sum_apply y _
  have hbulk (σ : SpinGlass.Config N) :
      MemLp (fun ω => lastSiteBulkRandom (s := s) path i ω σ) 2 volume :=
    (hLaw.fst.map_fun (SpinGlass.evalCLM (N := N) σ)).memLp_two
  have hodd (τ : SpinGlass.Config N) :
      MemLp (fun ω => lastSiteOddRandom path i ω τ) 2 volume :=
    (hLaw.snd.map_fun (SpinGlass.evalCLM (N := N) τ)).memLp_two
  rw [hx, hy, covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      lastSite_bulk_odd_point_covariance path i]
    simp
  · intro σ
    exact (hbulk σ).const_mul _
  · intro τ
    exact (hodd τ).const_mul _

/-! ## Explicit one-site form at the decoupled endpoint -/

/-- Projecting the explicit reference field onto its odd part keeps exactly
the coordinate at the selected site. -/
lemma siteOdd_referenceField_apply {N : ℕ} (β q : ℝ) (i : Fin N)
    (z : Fin N → ℝ) (σ : SpinGlass.Config N) :
    siteOddCLM i (SpinGlass.GeneralizedLatala.referenceField N β q z) σ =
      β * Real.sqrt q * z i * SpinGlass.spin N σ i := by
  classical
  rw [siteOddCLM_apply]
  simp_rw [SpinGlass.GeneralizedLatala.referenceField_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => z j * SpinGlass.spin N (flipSite i σ) j) (Finset.mem_univ i)]
  have hsum :
      ∑ j ∈ Finset.univ.erase i, z j * SpinGlass.spin N (flipSite i σ) j =
        ∑ j ∈ Finset.univ.erase i, z j * SpinGlass.spin N σ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [spin_flipSite_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsum, spin_flipSite_same]
  ring

/-- The odd part of the deterministic magnetic energy is the selected
one-site field. -/
lemma siteOdd_magnetic_field_apply {N : ℕ} (h : ℝ) (i : Fin N)
    (σ : SpinGlass.Config N) :
    siteOddCLM i (SpinGlass.magnetic_field_vector N h) σ =
      h * SpinGlass.spin N σ i := by
  classical
  rw [siteOddCLM_apply]
  simp only [SpinGlass.magnetic_field_vector, SpinGlass.magnetization]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => SpinGlass.spin N (flipSite i σ) j) (Finset.mem_univ i)]
  have hsum :
      ∑ j ∈ Finset.univ.erase i, SpinGlass.spin N (flipSite i σ) j =
        ∑ j ∈ Finset.univ.erase i, SpinGlass.spin N σ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [spin_flipSite_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hsum, spin_flipSite_same]
  ring

/-- The even part of any energy is invariant under the selected flip. -/
lemma siteEven_invariant {N : ℕ} (i : Fin N) (H : SpinGlass.EnergySpace N) :
    ∀ σ, siteEvenCLM i H (flipSite i σ) = siteEvenCLM i H σ := by
  exact siteEven_flip i H

/-- The odd simple component has the law of the selected coordinate of the
explicit reference field. -/
lemma lastSiteOddRandom_law_eq_reference
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hq : 0 ≤ q) (i : Fin N) :
    Measure.map (lastSiteOddRandom path i) volume =
      Measure.map
        (fun z : Fin N → ℝ =>
          siteOddCLM i (SpinGlass.GeneralizedLatala.referenceField N β q z))
        (SpinGlass.GeneralizedLatala.gaussianProduct N) := by
  have hlaw := SpinGlass.GeneralizedLatala.simpleDisorder_law_eq_reference
    N β q path.simple hN hq
  calc
    Measure.map (lastSiteOddRandom path i) volume =
        Measure.map (siteOddCLM i) (Measure.map path.simple.V volume) := by
      rw [Measure.map_map]
      · rfl
      · exact (siteOddCLM i).continuous.measurable
      · exact path.simple.hV.repr_measurable
    _ = Measure.map (siteOddCLM i)
        (Measure.map (SpinGlass.GeneralizedLatala.referenceField N β q)
          (SpinGlass.GeneralizedLatala.gaussianProduct N)) := by rw [hlaw]
    _ = Measure.map
        (fun z : Fin N → ℝ =>
          siteOddCLM i (SpinGlass.GeneralizedLatala.referenceField N β q z))
        (SpinGlass.GeneralizedLatala.gaussianProduct N) := by
      rw [Measure.map_map]
      · rfl
      · exact (siteOddCLM i).continuous.measurable
      · exact
          (SpinGlass.GeneralizedLatala.referenceFieldCLM N β q).continuous.measurable

/-- Configurations with the selected site fixed to `false`. -/
abbrev SiteBaseConfig (N : ℕ) (i : Fin N) :=
  {σ : SpinGlass.Config N // σ i = false}

/-- Split a configuration into all spins except the selected one and its
selected Boolean coordinate. -/
def configSplitSiteEquiv {N : ℕ} (i : Fin N) :
    SpinGlass.Config N ≃ SiteBaseConfig N i × Bool where
  toFun σ := ⟨⟨Function.update σ i false, by simp⟩, σ i⟩
  invFun p := Function.update p.1.1 i p.2
  left_inv σ := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  right_inv p := by
    rcases p with ⟨⟨ρ, hρ⟩, b⟩
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [hρ]
      · simp [hji]
    · simp

@[simp] lemma configSplitSiteEquiv_symm_apply_same {N : ℕ} (i : Fin N)
    (p : SiteBaseConfig N i × Bool) :
    (configSplitSiteEquiv i).symm p i = p.2 := by
  simp [configSplitSiteEquiv]

@[simp] lemma configSplitSiteEquiv_symm_flip {N : ℕ} (i : Fin N)
    (p : SiteBaseConfig N i × Bool) :
    flipSite i ((configSplitSiteEquiv i).symm p) =
      (configSplitSiteEquiv i).symm (p.1, !p.2) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [configSplitSiteEquiv, flipSite]
  · simp [configSplitSiteEquiv, flipSite, hji]

/-- A scalar energy supported at one site. -/
noncomputable def oneSiteEnergy {N : ℕ} (i : Fin N) (x : ℝ) :
    SpinGlass.EnergySpace N :=
  WithLp.toLp 2 (fun σ => x * SpinGlass.spin N σ i)

@[simp] lemma oneSiteEnergy_apply {N : ℕ} (i : Fin N) (x : ℝ)
    (σ : SpinGlass.Config N) :
    oneSiteEnergy i x σ = x * SpinGlass.spin N σ i := rfl

/-- Partition-function factorization for an even bulk energy and one selected
site field. -/
lemma Z_even_add_oneSiteEnergy {N : ℕ} (i : Fin N)
    (B : SpinGlass.EnergySpace N)
    (hB : ∀ σ, B (flipSite i σ) = B σ) (x : ℝ) :
    SpinGlass.Z N (B + oneSiteEnergy i x) =
      (∑ ρ : SiteBaseConfig N i, Real.exp (-B ρ.1)) *
        (∑ b : Bool, Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin b))) := by
  classical
  rw [SpinGlass.Z]
  rw [Fintype.sum_equiv (configSplitSiteEquiv i)
    (fun σ : SpinGlass.Config N => Real.exp (-(B + oneSiteEnergy i x) σ))
    (fun p : SiteBaseConfig N i × Bool =>
      Real.exp (-B p.1.1) *
        Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin p.2))) (by
      intro σ
      have hbase : B (Function.update σ i false) = B σ := by
        by_cases hi : σ i = false
        · have hupd : Function.update σ i false = σ := by
            funext j
            by_cases hji : j = i
            · subst j; simp [hi]
            · simp [hji]
          rw [hupd]
        · have hit : σ i = true := Bool.eq_true_of_not_eq_false hi
          have hflip : flipSite i σ = Function.update σ i false := by
            funext j
            by_cases hji : j = i
            · subst j; simp [flipSite, hit]
            · simp [flipSite, hji]
          rw [← hflip, hB]
      change Real.exp (-(B σ + x * SpinGlass.spin N σ i)) =
        Real.exp (-B (Function.update σ i false)) *
          Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin (σ i)))
      rw [hbase, SpinGlass.GeneralizedLatala.spin_eq_boolSpin, neg_add,
        Real.exp_add])]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.mul_sum]

noncomputable def siteBaseWeight {N : ℕ} {i : Fin N}
    (B : SpinGlass.EnergySpace N) (ρ : SiteBaseConfig N i) : ℝ :=
  Real.exp (-B ρ.1) / ∑ τ : SiteBaseConfig N i, Real.exp (-B τ.1)

lemma sum_siteBaseWeight {N : ℕ} {i : Fin N}
    (B : SpinGlass.EnergySpace N) :
    ∑ ρ : SiteBaseConfig N i, siteBaseWeight B ρ = 1 := by
  unfold siteBaseWeight
  have hpos : 0 < ∑ τ : SiteBaseConfig N i, Real.exp (-B τ.1) := by
    refine Finset.sum_pos (fun τ _ => Real.exp_pos _) ?_
    exact ⟨⟨fun _ => false, rfl⟩, Finset.mem_univ _⟩
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

noncomputable def oneSiteWeight (x : ℝ) (b : Bool) : ℝ :=
  Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin b)) /
    ∑ c : Bool, Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin c))

/-- The Gibbs probability itself factors into the bulk and selected-site
probabilities. -/
lemma gibbs_pmf_even_add_oneSiteEnergy {N : ℕ} (i : Fin N)
    (B : SpinGlass.EnergySpace N)
    (hB : ∀ σ, B (flipSite i σ) = B σ) (x : ℝ)
    (ρ : SiteBaseConfig N i) (b : Bool) :
    SpinGlass.gibbs_pmf N (B + oneSiteEnergy i x)
        ((configSplitSiteEquiv i).symm (ρ, b)) =
      siteBaseWeight B ρ * oneSiteWeight x b := by
  rw [SpinGlass.gibbs_pmf, Z_even_add_oneSiteEnergy i B hB x]
  simp only [PiLp.add_apply, oneSiteEnergy_apply,
    configSplitSiteEquiv_symm_apply_same,
    SpinGlass.GeneralizedLatala.spin_eq_boolSpin, siteBaseWeight, oneSiteWeight]
  have hbase : B ((configSplitSiteEquiv i).symm (ρ, b)) = B ρ.1 := by
    change B (Function.update ρ.1 i b) = B ρ.1
    cases b
    · have hupd : Function.update ρ.1 i false = ρ.1 := by
        funext j
        by_cases hji : j = i
        · subst j; simp [ρ.2]
        · simp [hji]
      rw [hupd]
    · have hflip : flipSite i (Function.update ρ.1 i true) = ρ.1 := by
        funext j
        by_cases hji : j = i
        · subst j; simp [flipSite, ρ.2]
        · simp [flipSite, hji]
      calc
        B (Function.update ρ.1 i true) =
            B (flipSite i (Function.update ρ.1 i true)) := (hB _).symm
        _ = B ρ.1 := congrArg B hflip
  rw [hbase, neg_add, Real.exp_add]
  ring

/-- Split every replica into its bulk configuration and its selected spin. -/
def replicasSplitSiteEquiv {N n : ℕ} (i : Fin N) :
    Replicas N n ≃ (Fin n → SiteBaseConfig N i) × (Fin n → Bool) where
  toFun σs :=
    (fun a => (configSplitSiteEquiv i (σs a)).1,
      fun a => (configSplitSiteEquiv i (σs a)).2)
  invFun p a := (configSplitSiteEquiv i).symm (p.1 a, p.2 a)
  left_inv σs := by
    funext a
    exact (configSplitSiteEquiv i).left_inv (σs a)
  right_inv p := by
    apply Prod.ext <;> funext a
    · exact congrArg Prod.fst ((configSplitSiteEquiv i).right_inv (p.1 a, p.2 a))
    · exact congrArg Prod.snd ((configSplitSiteEquiv i).right_inv (p.1 a, p.2 a))

/-- Fixed-disorder replica factorization at a decoupled selected site. -/
lemma replicaGibbsAverage_even_oneSite_factor {N n : ℕ} (i : Fin N)
    (B : SpinGlass.EnergySpace N)
    (hB : ∀ σ, B (flipSite i σ) = B σ) (x : ℝ)
    (F : (Fin n → SiteBaseConfig N i) → ℝ)
    (G : (Fin n → Bool) → ℝ) :
    replicaGibbsAverage (B + oneSiteEnergy i x)
        (fun σs => F (replicasSplitSiteEquiv i σs).1 *
          G (replicasSplitSiteEquiv i σs).2) =
      (∑ ρs, (∏ a, siteBaseWeight B (ρs a)) * F ρs) *
        (∑ bs, (∏ a, oneSiteWeight x (bs a)) * G bs) := by
  classical
  unfold replicaGibbsAverage
  rw [Fintype.sum_equiv (replicasSplitSiteEquiv i)
    (fun σs =>
      (∏ a, SpinGlass.gibbs_pmf N (B + oneSiteEnergy i x) (σs a)) *
        (F (replicasSplitSiteEquiv i σs).1 *
          G (replicasSplitSiteEquiv i σs).2))
    (fun p => ((∏ a, siteBaseWeight B (p.1 a)) * F p.1) *
      ((∏ a, oneSiteWeight x (p.2 a)) * G p.2)) (by
      intro σs
      have hpmf (a : Fin n) :
          SpinGlass.gibbs_pmf N (B + oneSiteEnergy i x) (σs a) =
            siteBaseWeight B ((replicasSplitSiteEquiv i σs).1 a) *
              oneSiteWeight x ((replicasSplitSiteEquiv i σs).2 a) := by
        rw [show σs a = (configSplitSiteEquiv i).symm
            ((replicasSplitSiteEquiv i σs).1 a,
              (replicasSplitSiteEquiv i σs).2 a) by
          exact (configSplitSiteEquiv i).left_inv (σs a) |>.symm]
        exact gibbs_pmf_even_add_oneSiteEnergy i B hB x _ _
      simp_rw [hpmf]
      rw [Finset.prod_mul_distrib]
      ring)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ρs _
  rw [Finset.mul_sum]

lemma sum_oneSiteWeight (x : ℝ) : ∑ b : Bool, oneSiteWeight x b = 1 := by
  unfold oneSiteWeight
  have hpos : 0 < ∑ c : Bool,
      Real.exp (-(x * SpinGlass.GeneralizedLatala.boolSpin c)) := by
    positivity
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

lemma sum_oneSiteWeight_mul_boolSpin (x : ℝ) :
    ∑ b : Bool, oneSiteWeight x b * SpinGlass.GeneralizedLatala.boolSpin b =
      -Real.tanh x := by
  simp [oneSiteWeight, SpinGlass.GeneralizedLatala.boolSpin]
  rw [Real.tanh_eq]
  field_simp
  ring

lemma sum_replica_siteBaseWeight {N n : ℕ} {i : Fin N}
    (B : SpinGlass.EnergySpace N) :
    ∑ ρs : Fin n → SiteBaseConfig N i,
      ∏ a, siteBaseWeight B (ρs a) = 1 := by
  classical
  rw [← Fintype.prod_sum (R := ℝ)
    (fun _a : Fin n => fun ρ : SiteBaseConfig N i => siteBaseWeight B ρ)]
  simp [sum_siteBaseWeight]

/-- Moments of distinct replicas at a single site are powers of the one-spin
mean. -/
lemma oneSiteReplicaMoment {n : ℕ} (x : ℝ) (S : Finset (Fin n)) :
    ∑ bs : Fin n → Bool,
        (∏ a, oneSiteWeight x (bs a)) *
          (∏ a ∈ S, SpinGlass.GeneralizedLatala.boolSpin (bs a)) =
      (-Real.tanh x) ^ S.card := by
  classical
  rw [show (∑ bs : Fin n → Bool,
      (∏ a, oneSiteWeight x (bs a)) *
        (∏ a ∈ S, SpinGlass.GeneralizedLatala.boolSpin (bs a))) =
      ∑ bs : Fin n → Bool, ∏ a,
        (oneSiteWeight x (bs a) *
          if a ∈ S then SpinGlass.GeneralizedLatala.boolSpin (bs a) else 1) by
      apply Finset.sum_congr rfl
      intro bs _
      rw [Finset.prod_mul_distrib]
      simp]
  change (∑ bs : Fin n → Bool, ∏ a,
      (fun b => oneSiteWeight x b *
        if a ∈ S then SpinGlass.GeneralizedLatala.boolSpin b else 1) (bs a)) = _
  rw [← Fintype.prod_sum (R := ℝ) (fun a : Fin n => fun b : Bool =>
    oneSiteWeight x b *
      if a ∈ S then SpinGlass.GeneralizedLatala.boolSpin b else 1)]
  have hlocal (a : Fin n) :
      (∑ b : Bool, oneSiteWeight x b *
        if a ∈ S then SpinGlass.GeneralizedLatala.boolSpin b else 1) =
      if a ∈ S then -Real.tanh x else 1 := by
    by_cases ha : a ∈ S
    · simpa only [ha, if_true] using sum_oneSiteWeight_mul_boolSpin x
    · simpa only [ha, if_false, mul_one] using sum_oneSiteWeight x
  simp_rw [hlocal]
  simp

/-- The even endpoint bulk, including the even part of the deterministic
magnetic field. -/
noncomputable def lastSiteBulkEnergy
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) : SpinGlass.EnergySpace N :=
  lastSiteBulkRandom (s := s) path i ω +
    siteEvenCLM i (SpinGlass.magnetic_field_vector N h)

lemma lastSiteBulkEnergy_invariant
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) (σ : SpinGlass.Config N) :
    lastSiteBulkEnergy (s := s) path i ω (flipSite i σ) =
      lastSiteBulkEnergy (s := s) path i ω σ := by
  simp only [lastSiteBulkEnergy, lastSiteBulkRandom, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, siteEvenCLM_apply, flipSite_involutive]
  ring

/-- After replacing the odd endpoint field by its explicit reference law,
the selected site is a scalar one-site energy. -/
lemma reference_endpoint_eq_even_oneSite
    {N : ℕ} (β h q : ℝ) (i : Fin N)
    (B : SpinGlass.EnergySpace N) (z : Fin N → ℝ) :
    B + siteOddCLM i (SpinGlass.GeneralizedLatala.referenceField N β q z) +
        siteOddCLM i (SpinGlass.magnetic_field_vector N h) =
      B + oneSiteEnergy i (h + β * Real.sqrt q * z i) := by
  ext σ
  simp only [PiLp.add_apply, oneSiteEnergy_apply]
  rw [siteOdd_referenceField_apply, siteOdd_magnetic_field_apply]
  ring

/-- Replica expectations are measurable as functions of the finite-volume
energy. -/
lemma measurable_replicaGibbsAverage {N n : ℕ} (F : ReplicaFun N n) :
    Measurable (fun H : SpinGlass.EnergySpace N => replicaGibbsAverage H F) := by
  unfold replicaGibbsAverage
  apply Finset.measurable_sum
  intro σs _
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro a _
    exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs a)).continuous.measurable
  · exact measurable_const

/-- A crude finite bound used only to justify endpoint changes of variables. -/
lemma abs_replicaGibbsAverage_le_sum_abs {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    |replicaGibbsAverage H F| ≤ ∑ σs, |F σs| := by
  classical
  unfold replicaGibbsAverage
  calc
    |∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs| ≤
        ∑ σs, |(∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σs, |F σs| := by
      apply Finset.sum_le_sum
      intro σs _
      rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun a _ =>
        SpinGlass.gibbs_pmf_nonneg N H (σs a))]
      have hp : ∏ a, SpinGlass.gibbs_pmf N H (σs a) ≤ 1 := by
        exact Finset.prod_le_one₀ (fun a _ => SpinGlass.gibbs_pmf_nonneg N H (σs a))
          (fun a _ => SpinGlass.gibbs_pmf_le_one N H (σs a))
      exact mul_le_of_le_one_left (abs_nonneg _) hp

lemma replicaGibbsAverage_nonneg {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n)
    (hF : ∀ σs, 0 ≤ F σs) :
    0 ≤ replicaGibbsAverage H F := by
  unfold replicaGibbsAverage
  apply Finset.sum_nonneg
  intro σs _
  exact mul_nonneg
    (Finset.prod_nonneg fun a _ => SpinGlass.gibbs_pmf_nonneg N H (σs a))
    (hF σs)

lemma abs_replicaGibbsAverage_le_abs_average {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    |replicaGibbsAverage H F| ≤
      replicaGibbsAverage H (fun σs => |F σs|) := by
  classical
  unfold replicaGibbsAverage
  calc
    |∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs| ≤
        ∑ σs, |(∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σs _
      rw [abs_mul, abs_of_nonneg]
      exact Finset.prod_nonneg fun a _ => SpinGlass.gibbs_pmf_nonneg N H (σs a)

lemma replicaGibbsAverage_mono {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F G : ReplicaFun N n)
    (hFG : ∀ σs, F σs ≤ G σs) :
    replicaGibbsAverage H F ≤ replicaGibbsAverage H G := by
  unfold replicaGibbsAverage
  apply Finset.sum_le_sum
  intro σs _
  exact mul_le_mul_of_nonneg_left (hFG σs)
    (Finset.prod_nonneg fun a _ => SpinGlass.gibbs_pmf_nonneg N H (σs a))

lemma replicaGibbsAverage_const_mul {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (c : ℝ) (F : ReplicaFun N n) :
    replicaGibbsAverage H (fun σs => c * F σs) =
      c * replicaGibbsAverage H F := by
  classical
  unfold replicaGibbsAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σs _
  ring

lemma integrable_replicaGibbsAverage_comp
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (hH : Measurable H)
    (F : ReplicaFun N n) :
    Integrable (fun ω => replicaGibbsAverage (H ω) F)
      (volume : Measure Ω) := by
  have hmeas := (measurable_replicaGibbsAverage F).comp hH
  apply Integrable.of_bound hmeas.aestronglyMeasurable (∑ σs, |F σs|)
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using abs_replicaGibbsAverage_le_sum_abs (H ω) F

lemma abs_quenchedReplicaAverage_le_abs_average
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (hH : Measurable H)
    (F : ReplicaFun N n) :
    |quenchedReplicaAverage H F| ≤
      quenchedReplicaAverage H (fun σs => |F σs|) := by
  unfold quenchedReplicaAverage
  have hint := integrable_replicaGibbsAverage_comp H hH F
  have habsint := integrable_replicaGibbsAverage_comp H hH (fun σs => |F σs|)
  calc
    |∫ ω, replicaGibbsAverage (H ω) F ∂volume| ≤
        ∫ ω, |replicaGibbsAverage (H ω) F| ∂volume := by
          simpa [Real.norm_eq_abs] using
            MeasureTheory.norm_integral_le_integral_norm
              (fun ω => replicaGibbsAverage (H ω) F)
    _ ≤ ∫ ω, replicaGibbsAverage (H ω) (fun σs => |F σs|) ∂volume := by
      apply MeasureTheory.integral_mono_ae hint.norm habsint
      filter_upwards with ω
      exact abs_replicaGibbsAverage_le_abs_average (H ω) F

lemma quenchedReplicaAverage_mono
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (hH : Measurable H)
    (F G : ReplicaFun N n) (hFG : ∀ σs, F σs ≤ G σs) :
    quenchedReplicaAverage H F ≤ quenchedReplicaAverage H G := by
  unfold quenchedReplicaAverage
  apply MeasureTheory.integral_mono
    (integrable_replicaGibbsAverage_comp H hH F)
    (integrable_replicaGibbsAverage_comp H hH G)
  intro ω
  exact replicaGibbsAverage_mono (H ω) F G hFG

lemma quenchedReplicaAverage_const_mul
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (c : ℝ)
    (F : ReplicaFun N n) :
    quenchedReplicaAverage H (fun σs => c * F σs) =
      c * quenchedReplicaAverage H F := by
  unfold quenchedReplicaAverage
  simp_rw [replicaGibbsAverage_const_mul]
  exact MeasureTheory.integral_const_mul c _


/-! ## Replica relabeling -/

/-- Relabel a finite replica family by a permutation. -/
def replicaRelabelEquiv {N n : ℕ} (e : Fin n ≃ Fin n) :
    Replicas N n ≃ Replicas N n where
  toFun σs a := σs (e a)
  invFun σs a := σs (e.symm a)
  left_inv σs := by
    funext a
    simp
  right_inv σs := by
    funext a
    simp

/-- Product Gibbs expectations are invariant under a permutation of replica
labels. -/
lemma replicaGibbsAverage_relabel {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n)
    (e : Fin n ≃ Fin n) :
    replicaGibbsAverage H (fun σs => F (replicaRelabelEquiv e σs)) =
      replicaGibbsAverage H F := by
  unfold replicaGibbsAverage
  let E := replicaRelabelEquiv (N := N) e
  let g : Replicas N n → ℝ := fun σs =>
    (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs
  have hsum := E.sum_comp g
  calc
    (∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
        F (replicaRelabelEquiv e σs)) =
        ∑ σs, (∏ a, SpinGlass.gibbs_pmf N H
          ((replicaRelabelEquiv e σs) a)) *
            F (replicaRelabelEquiv e σs) := by
      apply Finset.sum_congr rfl
      intro σs _
      congr 1
      change (∏ a, SpinGlass.gibbs_pmf N H (σs a)) =
        ∏ a, SpinGlass.gibbs_pmf N H (σs (e a))
      exact (e.prod_comp fun a => SpinGlass.gibbs_pmf N H (σs a)).symm
    _ = ∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs := by
      simpa only [E, g, replicaRelabelEquiv, Equiv.coe_fn_mk] using hsum

/-- Quenched replica expectations are invariant under a permutation of
replica labels. -/
lemma quenchedReplicaAverage_relabel
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (F : ReplicaFun N n)
    (e : Fin n ≃ Fin n) :
    quenchedReplicaAverage H (fun σs => F (replicaRelabelEquiv e σs)) =
      quenchedReplicaAverage H F := by
  unfold quenchedReplicaAverage
  congr 1
  funext ω
  exact replicaGibbsAverage_relabel (H ω) F e

/-- Split a family of replicas into an initial block and a final block. -/
def replicasAppendEquiv (N n m : ℕ) :
    (Replicas N n × Replicas N m) ≃ Replicas N (n + m) where
  toFun p := Fin.append p.1 p.2
  invFun σs :=
    (fun a => σs (Fin.castAdd m a), fun b => σs (Fin.natAdd n b))
  left_inv p := by
    ext a <;> simp
  right_inv σs := by
    funext a
    exact Fin.addCases (fun b => by simp) (fun b => by simp) a

def initialReplicas {N n : ℕ} (σs : Replicas N (n + 2)) : Replicas N n :=
  fun a => σs (Fin.castAdd 2 a)

def firstFreshReplica {N n : ℕ} (σs : Replicas N (n + 2)) :
    SpinGlass.Config N :=
  σs (Fin.natAdd n (0 : Fin 2))

def secondFreshReplica {N n : ℕ} (σs : Replicas N (n + 2)) :
    SpinGlass.Config N :=
  σs (Fin.natAdd n (1 : Fin 2))

@[simp] lemma initialReplicas_append {N n : ℕ} (σs : Replicas N n)
    (τs : Replicas N 2) :
    initialReplicas (Fin.append σs τs) = σs := by
  funext a
  simp [initialReplicas]

lemma replicaGibbsAverage_eq_sum_append {N n m : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N (n + m)) :
    replicaGibbsAverage H F =
      ∑ σs : Replicas N n,
        (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
          ∑ τs : Replicas N m,
            (∏ b, SpinGlass.gibbs_pmf N H (τs b)) *
              F (Fin.append σs τs) := by
  classical
  let E := replicasAppendEquiv N n m
  have hsum := Fintype.sum_equiv E
    (fun p : Replicas N n × Replicas N m =>
      ((∏ a, SpinGlass.gibbs_pmf N H (p.1 a)) *
        ∏ b, SpinGlass.gibbs_pmf N H (p.2 b)) * F (E p))
    (fun σs : Replicas N (n + m) =>
      (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs)
    (fun p => by
      rw [Fin.prod_univ_add]
      simp [E, replicasAppendEquiv])
  unfold replicaGibbsAverage
  rw [← hsum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σs _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τs _
  simp only [E, replicasAppendEquiv, Equiv.coe_fn_mk]
  ring

def configPairEquivReplicasTwo (N : ℕ) :
    (SpinGlass.Config N × SpinGlass.Config N) ≃ Replicas N 2 where
  toFun p := ![p.1, p.2]
  invFun σs := (σs 0, σs 1)
  left_inv p := by simp
  right_inv σs := by
    funext a
    fin_cases a <;> simp

lemma replicaGibbsAverage_two {N : ℕ} (H : SpinGlass.EnergySpace N)
    (F : ReplicaFun N 2) :
    replicaGibbsAverage H F =
      ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
          F ![σ, τ] := by
  classical
  let E := configPairEquivReplicasTwo N
  have hsum := Fintype.sum_equiv E
    (fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.gibbs_pmf N H p.1 * SpinGlass.gibbs_pmf N H p.2 * F (E p))
    (fun σs : Replicas N 2 =>
      (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs)
    (fun p => by
      simp [E, configPairEquivReplicasTwo, Fin.prod_univ_succ])
  unfold replicaGibbsAverage
  rw [← hsum, Fintype.sum_prod_type]
  simp only [E, configPairEquivReplicasTwo, Equiv.coe_fn_mk]

lemma replicaGibbsAverage_initialReplicas {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    replicaGibbsAverage H (fun σs : Replicas N (n + 2) =>
      F (initialReplicas σs)) = replicaGibbsAverage H F := by
  classical
  rw [replicaGibbsAverage_eq_sum_append]
  unfold replicaGibbsAverage
  apply Finset.sum_congr rfl
  intro σs _
  simp only [initialReplicas_append]
  calc
    (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
        ∑ τs : Replicas N 2,
          (∏ b, SpinGlass.gibbs_pmf N H (τs b)) * F σs =
      (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
        ((∑ τs : Replicas N 2,
          ∏ b, SpinGlass.gibbs_pmf N H (τs b)) * F σs) := by
            rw [Finset.sum_mul]
    _ = _ := by rw [SpinGlass.sum_prod_gibbs_pmf_eq_one, one_mul]

lemma quenchedReplicaAverage_initialReplicas
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    quenchedReplicaAverage H (fun σs : Replicas N (n + 2) =>
      F (initialReplicas σs)) = quenchedReplicaAverage H F := by
  unfold quenchedReplicaAverage
  congr 1
  funext ω
  exact replicaGibbsAverage_initialReplicas (H ω) F

/-- The last-site interpolation.  At `u=1` it is the original smart path.
At `u=0` the odd SK part is replaced by the odd part of the independent
simple field, whose covariance is exactly the RS one-site covariance. -/
noncomputable def lastSiteOddInterpolated
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (ω : Ω) : SpinGlass.EnergySpace N :=
  Real.sqrt (s * u) • siteOddCLM i (path.sk.U ω) +
    Real.sqrt (1 - s * u) • siteOddCLM i (path.simple.V ω)

/-- The covariance of the interpolated odd field is affine in `u`. -/
lemma lastSiteOddInterpolated_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu : s * u ∈ Set.Icc (0 : ℝ) 1)
    (σ τ : SpinGlass.Config N) :
    covariance (fun ω => lastSiteOddInterpolated (s := s) path i u ω σ)
      (fun ω => lastSiteOddInterpolated (s := s) path i u ω τ) volume =
      s * u * (β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          configCavityOverlapAt i σ τ) +
        (1 - s * u) *
          (β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i) := by
  let Xσ : Ω → ℝ := fun ω => siteOddCLM i (path.sk.U ω) σ
  let Xτ : Ω → ℝ := fun ω => siteOddCLM i (path.sk.U ω) τ
  let Yσ : Ω → ℝ := fun ω => siteOddCLM i (path.simple.V ω) σ
  let Yτ : Ω → ℝ := fun ω => siteOddCLM i (path.simple.V ω) τ
  have hXσ : MemLp Xσ 2 volume := gaussianHilbert_clm_memLp_two path.sk.hU
    ((SpinGlass.evalCLM (N := N) σ).comp (siteOddCLM i))
  have hXτ : MemLp Xτ 2 volume := gaussianHilbert_clm_memLp_two path.sk.hU
    ((SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i))
  have hYσ : MemLp Yσ 2 volume := gaussianHilbert_clm_memLp_two path.simple.hV
    ((SpinGlass.evalCLM (N := N) σ).comp (siteOddCLM i))
  have hYτ : MemLp Yτ 2 volume := gaussianHilbert_clm_memLp_two path.simple.hV
    ((SpinGlass.evalCLM (N := N) τ).comp (siteOddCLM i))
  change covariance
    ((fun ω => Real.sqrt (s * u) * Xσ ω) +
      (fun ω => Real.sqrt (1 - s * u) * Yσ ω))
    ((fun ω => Real.sqrt (s * u) * Xτ ω) +
      (fun ω => Real.sqrt (1 - s * u) * Yτ ω))
      volume = _
  rw [covariance_add_left (hXσ.const_mul _) (hYσ.const_mul _)
      ((hXτ.const_mul _).add (hYτ.const_mul _)),
    covariance_add_right (hXσ.const_mul _) (hXτ.const_mul _) (hYτ.const_mul _),
    covariance_add_right (hYσ.const_mul _) (hXτ.const_mul _) (hYτ.const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [
    sk_siteOdd_point_covariance path.sk i σ τ,
    simple_siteOdd_point_covariance path.simple i σ τ,
    skOdd_simpleOdd_point_covariance path i σ τ]
  have hcross : covariance Yσ Xτ volume = 0 := by
    rw [covariance_comm]
    exact skOdd_simpleOdd_point_covariance path i τ σ
  rw [hcross]
  simp only [mul_zero, add_zero, zero_add]
  calc
    Real.sqrt (s * u) *
          (Real.sqrt (s * u) *
            (β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
              configCavityOverlapAt i σ τ)) +
        Real.sqrt (1 - s * u) *
          (Real.sqrt (1 - s * u) *
            (β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i)) =
      Real.sqrt (s * u) ^ 2 *
          (β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
            configCavityOverlapAt i σ τ) +
        Real.sqrt (1 - s * u) ^ 2 *
          (β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i) := by ring
    _ = _ := by
      rw [Real.sq_sqrt hu.1, Real.sq_sqrt (sub_nonneg.mpr hu.2)]

/-- Exact covariance increment.  The coefficient of `u - v` is the cavity
kernel used by normalized Gibbs differentiation. -/
lemma lastSiteOddInterpolated_covariance_sub
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u v : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu : s * u ∈ Set.Icc (0 : ℝ) 1)
    (hv : s * v ∈ Set.Icc (0 : ℝ) 1)
    (σ τ : SpinGlass.Config N) :
    covariance (fun ω => lastSiteOddInterpolated (s := s) path i u ω σ)
        (fun ω => lastSiteOddInterpolated (s := s) path i u ω τ) volume -
      covariance (fun ω => lastSiteOddInterpolated (s := s) path i v ω σ)
        (fun ω => lastSiteOddInterpolated (s := s) path i v ω τ) volume =
      (u - v) * s * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
        (configCavityOverlapAt i σ τ - q) := by
  rw [lastSiteOddInterpolated_covariance path i hu σ τ,
    lastSiteOddInterpolated_covariance path i hv σ τ]
  ring

/-- Replica form of the covariance increment. -/
lemma lastSiteOddInterpolated_covariance_sub_replica
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u v : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu : s * u ∈ Set.Icc (0 : ℝ) 1)
    (hv : s * v ∈ Set.Icc (0 : ℝ) 1)
    (σs : Replicas N n) (a b : Fin n) :
    covariance
        (fun ω => lastSiteOddInterpolated (s := s) path i u ω (σs a))
        (fun ω => lastSiteOddInterpolated (s := s) path i u ω (σs b)) volume -
      covariance
        (fun ω => lastSiteOddInterpolated (s := s) path i v ω (σs a))
        (fun ω => lastSiteOddInterpolated (s := s) path i v ω (σs b)) volume =
      (u - v) * s * β ^ 2 * SpinGlass.spin N (σs a) i *
        SpinGlass.spin N (σs b) i * cavityOverlapAt q i σs a b := by
  rw [lastSiteOddInterpolated_covariance_sub path i hu hv]
  rw [cavityOverlapAt_eq_configCavityOverlapAt_sub]

noncomputable def lastSiteHamiltonian
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (ω : Ω) : SpinGlass.EnergySpace N :=
  Real.sqrt s • siteEvenCLM i (path.sk.U ω) +
    Real.sqrt (1 - s) • siteEvenCLM i (path.simple.V ω) +
    lastSiteOddInterpolated (s := s) path i u ω +
    SpinGlass.magnetic_field_vector N h

lemma lastSiteHamiltonian_zero
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) :
    lastSiteHamiltonian (s := s) path i 0 ω =
      lastSiteBulkRandom (s := s) path i ω +
        lastSiteOddRandom path i ω + SpinGlass.magnetic_field_vector N h := by
  simp [lastSiteHamiltonian, lastSiteOddInterpolated, lastSiteBulkRandom,
    lastSiteOddRandom]

/-- The decoupled Hamiltonian written as an even bulk plus an odd endpoint
field. -/
lemma lastSiteHamiltonian_zero_split
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) :
    lastSiteHamiltonian (s := s) path i 0 ω =
      lastSiteBulkEnergy (s := s) path i ω +
        lastSiteOddRandom path i ω +
          siteOddCLM i (SpinGlass.magnetic_field_vector N h) := by
  rw [lastSiteHamiltonian_zero]
  unfold lastSiteBulkEnergy
  let M := SpinGlass.magnetic_field_vector N h
  have hM : siteEvenCLM i M + siteOddCLM i M = M := siteEven_add_siteOdd i M
  calc
    lastSiteBulkRandom (s := s) path i ω + lastSiteOddRandom path i ω + M =
        lastSiteBulkRandom (s := s) path i ω + lastSiteOddRandom path i ω +
          (siteEvenCLM i M + siteOddCLM i M) :=
      congrArg (fun X => lastSiteBulkRandom (s := s) path i ω +
        lastSiteOddRandom path i ω + X) hM.symm
    _ = (lastSiteBulkRandom (s := s) path i ω + siteEvenCLM i M) +
        lastSiteOddRandom path i ω + siteOddCLM i M := by abel

/-- Quenched Gibbs expectation along the selected-site interpolation. -/
noncomputable def lastSiteQuenchedAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) : ℝ :=
  quenchedReplicaAverage (lastSiteHamiltonian (s := s) path i u) F

/-- Pointwise derivative of the selected-site Hamiltonian on the open
interpolation interval. -/
noncomputable def lastSiteHamiltonianDeriv
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (ω : Ω) : SpinGlass.EnergySpace N :=
  (s / (2 * Real.sqrt (s * u))) • siteOddCLM i (path.sk.U ω) -
    (s / (2 * Real.sqrt (1 - s * u))) • siteOddCLM i (path.simple.V ω)

lemma measurable_lastSiteHamiltonian
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    Measurable (lastSiteHamiltonian (s := s) path i u) := by
  have hU : Measurable path.sk.U := path.sk.hU.repr_measurable
  have hV : Measurable path.simple.V := path.simple.hV.repr_measurable
  have hUeven := (siteEvenCLM i).continuous.measurable.comp hU
  have hVeven := (siteEvenCLM i).continuous.measurable.comp hV
  have hUodd := (siteOddCLM i).continuous.measurable.comp hU
  have hVodd := (siteOddCLM i).continuous.measurable.comp hV
  exact (((hUeven.const_smul (Real.sqrt s)).add
    (hVeven.const_smul (Real.sqrt (1 - s)))).add
      ((hUodd.const_smul (Real.sqrt (s * u))).add
        (hVodd.const_smul (Real.sqrt (1 - s * u))))).add measurable_const

lemma measurable_lastSiteHamiltonianDeriv
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) :
    Measurable (lastSiteHamiltonianDeriv (s := s) path i u) := by
  have hU : Measurable path.sk.U := path.sk.hU.repr_measurable
  have hV : Measurable path.simple.V := path.simple.hV.repr_measurable
  exact ((siteOddCLM i).continuous.measurable.comp hU).const_smul
      (s / (2 * Real.sqrt (s * u))) |>.sub
    (((siteOddCLM i).continuous.measurable.comp hV).const_smul
      (s / (2 * Real.sqrt (1 - s * u))))

lemma hasDerivAt_lastSiteHamiltonian
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hs : 0 ≤ s) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hsu : s * u < 1) (ω : Ω) :
    HasDerivAt (fun v => lastSiteHamiltonian (s := s) path i v ω)
      (lastSiteHamiltonianDeriv (s := s) path i u ω) u := by
  by_cases hs0 : s = 0
  · subst s
    have hfun : (fun v => lastSiteHamiltonian (s := 0) path i v ω) =
        fun _ => lastSiteHamiltonian (s := 0) path i u ω := by
      funext v
      simp [lastSiteHamiltonian, lastSiteOddInterpolated]
    rw [hfun]
    simpa [lastSiteHamiltonianDeriv] using
      (hasDerivAt_const (x := u)
        (c := lastSiteHamiltonian (s := 0) path i u ω))
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsu0 : s * u ≠ 0 := mul_ne_zero hs0 (ne_of_gt hu.1)
    have h1su0 : 1 - s * u ≠ 0 := ne_of_gt (sub_pos.mpr hsu)
    have hmul : HasDerivAt (fun v : ℝ => s * v) s u := by
      simpa using (hasDerivAt_id u).const_mul s
    have hsub : HasDerivAt (fun v : ℝ => 1 - s * v) (-s) u := by
      simpa using (HasDerivAt.const_sub (c := (1 : ℝ)) hmul)
    have hodd :=
      (((Real.hasDerivAt_sqrt hsu0).comp u hmul).smul_const
        (siteOddCLM i (path.sk.U ω))).add
      (((Real.hasDerivAt_sqrt h1su0).comp u hsub).smul_const
        (siteOddCLM i (path.simple.V ω)))
    have hcsk : 1 / (2 * Real.sqrt (s * u)) * s =
        s / (2 * Real.sqrt (s * u)) := by ring
    have hcsim : 1 / (2 * Real.sqrt (1 - s * u)) * (-s) =
        -(s / (2 * Real.sqrt (1 - s * u))) := by ring
    rw [hcsk, hcsim] at hodd
    simpa [lastSiteHamiltonian, lastSiteOddInterpolated,
      lastSiteHamiltonianDeriv, sub_eq_add_neg, neg_smul, neg_div] using
      hodd.add_const
        (Real.sqrt s • siteEvenCLM i (path.sk.U ω) +
          Real.sqrt (1 - s) • siteEvenCLM i (path.simple.V ω) +
          SpinGlass.magnetic_field_vector N h)

lemma replicaGibbsAverage_eq_gibbs_average_n_det
    {N n : ℕ} (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    replicaGibbsAverage H F =
      SpinGlass.gibbs_average_n_det (N := N) (n := n) H F := by
  unfold replicaGibbsAverage SpinGlass.gibbs_average_n_det
  apply Finset.sum_congr rfl
  intro σs _
  ring

lemma contDiff_gibbs_average_n_det
    {N n : ℕ} (F : ReplicaFun N n) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun H : SpinGlass.EnergySpace N =>
        SpinGlass.gibbs_average_n_det (N := N) (n := n) H F) := by
  classical
  have hprod (T : Finset (Fin n)) (σs : Replicas N n) :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun H : SpinGlass.EnergySpace N =>
          ∏ a ∈ T, SpinGlass.gibbs_pmf N H (σs a)) := by
    induction T using Finset.induction_on with
    | empty => simpa using
        (contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : SpinGlass.EnergySpace N => (1 : ℝ)))
    | @insert a T ha ih =>
        simpa [Finset.prod_insert ha] using
          (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs a)).mul ih
  unfold SpinGlass.gibbs_average_n_det
  simpa using
    (ContDiff.sum (s := (Finset.univ : Finset (Replicas N n)))
      (f := fun σs H => F σs * ∏ a, SpinGlass.gibbs_pmf N H (σs a))
      (fun σs _ => contDiff_const.mul (by
        simpa using hprod Finset.univ σs)))

lemma continuous_lastSiteHamiltonian
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) :
    Continuous (fun u => lastSiteHamiltonian (s := s) path i u ω) := by
  unfold lastSiteHamiltonian lastSiteOddInterpolated
  fun_prop

lemma continuous_lastSiteQuenchedAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (F : ReplicaFun N n) :
    Continuous (fun u => lastSiteQuenchedAverage (s := s) path i u F) := by
  let G : ℝ → Ω → ℝ := fun u ω =>
    replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω) F
  have hmeas : ∀ u, AEStronglyMeasurable (G u) (volume : Measure Ω) := by
    intro u
    exact ((measurable_replicaGibbsAverage F).comp
      (measurable_lastSiteHamiltonian path i u)).aestronglyMeasurable
  have hbound : ∀ u, ∀ᵐ ω ∂(volume : Measure Ω),
      ‖G u ω‖ ≤ (∑ σs, |F σs|) := by
    intro u
    filter_upwards with ω
    simpa [G, Real.norm_eq_abs] using
      abs_replicaGibbsAverage_le_sum_abs
        (lastSiteHamiltonian (s := s) path i u ω) F
  have hcont : ∀ᵐ ω ∂(volume : Measure Ω), Continuous (fun u => G u ω) := by
    filter_upwards with ω
    rw [show (fun u => G u ω) = fun u =>
        SpinGlass.gibbs_average_n_det (N := N) (n := n)
          (lastSiteHamiltonian (s := s) path i u ω) F by
      funext u
      exact replicaGibbsAverage_eq_gibbs_average_n_det _ _]
    exact (contDiff_gibbs_average_n_det F).continuous.comp
      (continuous_lastSiteHamiltonian path i ω)
  have hmain := MeasureTheory.continuous_of_dominated
    (F := G) (bound := fun _ => ∑ σs, |F σs|)
    hmeas hbound (integrable_const _) hcont
  simpa [lastSiteQuenchedAverage, quenchedReplicaAverage, G] using hmain

/-- Gibbs expectation of an energy direction. -/
noncomputable def gibbsEnergyMean {N : ℕ}
    (H v : SpinGlass.EnergySpace N) : ℝ :=
  ∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * v σ

noncomputable def energyPointwiseMul {N : ℕ}
    (u v : SpinGlass.EnergySpace N) : SpinGlass.EnergySpace N :=
  WithLp.toLp 2 (fun σ => u σ * v σ)

@[simp] lemma energyPointwiseMul_apply {N : ℕ}
    (u v : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    energyPointwiseMul u v σ = u σ * v σ := rfl

/-- Log-density variation of an `n`-replica product Gibbs weight. -/
noncomputable def replicaEnergyScore {N n : ℕ}
    (H v : SpinGlass.EnergySpace N) (σs : Replicas N n) : ℝ :=
  ∑ a : Fin n, (gibbsEnergyMean H v - v (σs a))

lemma fderiv_gibbsEnergyMean_apply {N : ℕ}
    (H u v : SpinGlass.EnergySpace N) :
    fderiv ℝ (fun K => gibbsEnergyMean K u) H v =
      gibbsEnergyMean H u * gibbsEnergyMean H v -
        gibbsEnergyMean H (energyPointwiseMul u v) := by
  classical
  unfold gibbsEnergyMean
  have hdiff : ∀ σ : SpinGlass.Config N,
      DifferentiableAt ℝ (fun K : SpinGlass.EnergySpace N =>
        SpinGlass.gibbs_pmf N K σ * u σ) H := by
    intro σ
    exact (SpinGlass.differentiableAt_gibbs_pmf
      (N := N) (H := H) σ).mul_const (u σ)
  rw [fderiv_fun_sum (u := (Finset.univ : Finset (SpinGlass.Config N)))
    (A := fun σ K => SpinGlass.gibbs_pmf N K σ * u σ)
    (x := H) (fun σ _ => hdiff σ)]
  simp only [ContinuousLinearMap.sum_apply]
  have hterm (σ : SpinGlass.Config N) :
      (fderiv ℝ (fun K : SpinGlass.EnergySpace N =>
        SpinGlass.gibbs_pmf N K σ * u σ) H) v =
        SpinGlass.gibbs_pmf N H σ *
          (gibbsEnergyMean H v - v σ) * u σ := by
    have hd := ((SpinGlass.differentiableAt_gibbs_pmf
      (N := N) (H := H) σ).hasFDerivAt.mul_const (u σ)).fderiv
    have happ := congrArg (fun L : SpinGlass.EnergySpace N →L[ℝ] ℝ => L v) hd
    simpa [SpinGlass.fderiv_gibbs_pmf_apply, gibbsEnergyMean,
      ContinuousLinearMap.mul_apply, mul_comm, mul_left_comm, mul_assoc] using happ
  simp_rw [hterm]
  simp_rw [mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  apply congrArg₂ (fun x y : ℝ => x - y)
  · calc
      (∑ σ, SpinGlass.gibbs_pmf N H σ *
          (gibbsEnergyMean H v * u σ)) =
          ∑ σ, (SpinGlass.gibbs_pmf N H σ * u σ) *
            gibbsEnergyMean H v := by
              apply Finset.sum_congr rfl
              intro σ _
              ring
      _ = (∑ σ, SpinGlass.gibbs_pmf N H σ * u σ) *
          gibbsEnergyMean H v := by rw [Finset.sum_mul]
      _ = _ := rfl
  · apply Finset.sum_congr rfl
    intro σ _
    rw [energyPointwiseMul_apply]
    ring

lemma fderiv_gibbs_average_n_det_score {N n : ℕ}
    (H v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    fderiv ℝ
        (fun K => SpinGlass.gibbs_average_n_det (N := N) (n := n) K F) H v =
      replicaGibbsAverage H
        (fun σs => F σs * replicaEnergyScore H v σs) := by
  rw [SpinGlass.fderiv_gibbs_average_n_det_apply]
  unfold replicaGibbsAverage replicaEnergyScore gibbsEnergyMean
  apply Finset.sum_congr rfl
  intro σs _
  ring

lemma fderiv_replicaEnergyScore_apply {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (σs : Replicas N n) :
    fderiv ℝ (fun K => replicaEnergyScore K u σs) H v =
      (n : ℝ) *
        (gibbsEnergyMean H u * gibbsEnergyMean H v -
          gibbsEnergyMean H (energyPointwiseMul u v)) := by
  classical
  unfold replicaEnergyScore
  have hdiff : ∀ a : Fin n, DifferentiableAt ℝ
      (fun K : SpinGlass.EnergySpace N => gibbsEnergyMean K u - u (σs a)) H := by
    intro a
    have hm : DifferentiableAt ℝ (fun K : SpinGlass.EnergySpace N =>
        gibbsEnergyMean K u) H := by
      unfold gibbsEnergyMean
      apply DifferentiableAt.fun_sum
      intro σ _
      exact (SpinGlass.differentiableAt_gibbs_pmf
        (N := N) (H := H) σ).mul_const (u σ)
    exact hm.sub_const _
  rw [fderiv_fun_sum (u := (Finset.univ : Finset (Fin n)))
    (A := fun a K => gibbsEnergyMean K u - u (σs a))
    (x := H) (fun a _ => hdiff a)]
  simp only [ContinuousLinearMap.sum_apply]
  have hterm (a : Fin n) :
      (fderiv ℝ (fun K : SpinGlass.EnergySpace N =>
        gibbsEnergyMean K u - u (σs a)) H) v =
        gibbsEnergyMean H u * gibbsEnergyMean H v -
          gibbsEnergyMean H (energyPointwiseMul u v) := by
    have hm : DifferentiableAt ℝ (fun K : SpinGlass.EnergySpace N =>
        gibbsEnergyMean K u) H := by
      unfold gibbsEnergyMean
      apply DifferentiableAt.fun_sum
      intro σ _
      exact (SpinGlass.differentiableAt_gibbs_pmf
        (N := N) (H := H) σ).mul_const (u σ)
    have hd := (hm.hasFDerivAt.sub_const (u (σs a))).fderiv
    have happ := congrArg (fun L : SpinGlass.EnergySpace N →L[ℝ] ℝ => L v) hd
    rw [happ]
    exact fderiv_gibbsEnergyMean_apply H u v
  simp_rw [hterm]
  simp
  ring

lemma differentiableAt_replicaEnergyScore {N n : ℕ}
    (H u : SpinGlass.EnergySpace N) (σs : Replicas N n) :
    DifferentiableAt ℝ
      (fun K : SpinGlass.EnergySpace N => replicaEnergyScore K u σs) H := by
  unfold replicaEnergyScore
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.sub_const
  unfold gibbsEnergyMean
  apply DifferentiableAt.fun_sum
  intro σ _
  exact (SpinGlass.differentiableAt_gibbs_pmf
    (N := N) (H := H) σ).mul_const (u σ)

/-- Explicit second Hamiltonian variation of a normalized replicated Gibbs
average. -/
noncomputable def gibbsReplicaSecondVariation {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) : ℝ :=
  replicaGibbsAverage H (fun σs =>
    F σs *
      (replicaEnergyScore H u σs * replicaEnergyScore H v σs +
        (n : ℝ) *
          (gibbsEnergyMean H u * gibbsEnergyMean H v -
            gibbsEnergyMean H (energyPointwiseMul u v))))

@[simp] lemma gibbsEnergyMean_std_basis {N : ℕ}
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N) :
    gibbsEnergyMean H (SpinGlass.std_basis N σ) =
      SpinGlass.gibbs_pmf N H σ := by
  classical
  simp [gibbsEnergyMean, SpinGlass.std_basis]

@[simp] lemma gibbsEnergyMean_pointwiseMul_std_basis {N : ℕ}
    (H : SpinGlass.EnergySpace N) (σ τ : SpinGlass.Config N) :
    gibbsEnergyMean H
        (energyPointwiseMul (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ)) =
      if σ = τ then SpinGlass.gibbs_pmf N H σ else 0 := by
  classical
  by_cases hστ : σ = τ
  · subst τ
    simp [gibbsEnergyMean, energyPointwiseMul, SpinGlass.std_basis]
  · simp [gibbsEnergyMean, energyPointwiseMul, SpinGlass.std_basis, hστ]

@[simp] lemma replicaEnergyScore_std_basis {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N)
    (σs : Replicas N n) :
    replicaEnergyScore H (SpinGlass.std_basis N σ) σs =
      ∑ a : Fin n,
        (SpinGlass.gibbs_pmf N H σ - if σs a = σ then 1 else 0) := by
  classical
  unfold replicaEnergyScore
  rw [gibbsEnergyMean_std_basis]
  apply Finset.sum_congr rfl
  intro a _
  simp [SpinGlass.std_basis, eq_comm]

noncomputable def replicaConfigCount {N n : ℕ} (σs : Replicas N n)
    (σ : SpinGlass.Config N) : ℝ :=
  ∑ a : Fin n, if σs a = σ then 1 else 0

lemma replicaEnergyScore_std_basis_count {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (σ : SpinGlass.Config N)
    (σs : Replicas N n) :
    replicaEnergyScore H (SpinGlass.std_basis N σ) σs =
      (n : ℝ) * SpinGlass.gibbs_pmf N H σ - replicaConfigCount σs σ := by
  rw [replicaEnergyScore_std_basis]
  simp [replicaConfigCount, Finset.sum_sub_distrib]

lemma sum_kernel_mul_replicaConfigCount {N n : ℕ}
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (σs : Replicas N n) (τ : SpinGlass.Config N) :
    (∑ σ : SpinGlass.Config N, K σ τ * replicaConfigCount σs σ) =
      ∑ a : Fin n, K (σs a) τ := by
  classical
  unfold replicaConfigCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

lemma sum_replicaConfigCount_mul_kernel {N n : ℕ}
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (σs : Replicas N n) (σ : SpinGlass.Config N) :
    (∑ τ : SpinGlass.Config N, replicaConfigCount σs τ * K σ τ) =
      ∑ a : Fin n, K σ (σs a) := by
  classical
  unfold replicaConfigCount
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

lemma sum_kernel_mul_two_replicaConfigCounts {N n : ℕ}
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (σs : Replicas N n) :
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      K σ τ * replicaConfigCount σs σ * replicaConfigCount σs τ) =
      ∑ a : Fin n, ∑ b : Fin n, K (σs a) (σs b) := by
  classical
  have hinner (σ : SpinGlass.Config N) :
      (∑ τ : SpinGlass.Config N,
        K σ τ * replicaConfigCount σs σ * replicaConfigCount σs τ) =
        replicaConfigCount σs σ * ∑ b : Fin n, K σ (σs b) := by
    calc
      (∑ τ : SpinGlass.Config N,
          K σ τ * replicaConfigCount σs σ * replicaConfigCount σs τ) =
          replicaConfigCount σs σ *
            ∑ τ : SpinGlass.Config N, replicaConfigCount σs τ * K σ τ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = _ := by rw [sum_replicaConfigCount_mul_kernel]
  calc
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * replicaConfigCount σs σ * replicaConfigCount σs τ) =
        ∑ σ : SpinGlass.Config N,
          replicaConfigCount σs σ * ∑ b : Fin n, K σ (σs b) := by
      simp_rw [hinner]
    _ = ∑ σ : SpinGlass.Config N, ∑ b : Fin n,
        replicaConfigCount σs σ * K σ (σs b) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ b : Fin n, ∑ σ : SpinGlass.Config N,
        replicaConfigCount σs σ * K σ (σs b) := Finset.sum_comm
    _ = ∑ b : Fin n, ∑ a : Fin n, K (σs a) (σs b) := by
      apply Finset.sum_congr rfl
      intro b _
      simpa [mul_comm] using
        sum_kernel_mul_replicaConfigCount K σs (σs b)
    _ = _ := Finset.sum_comm

lemma kernel_score_contraction {N n : ℕ}
    (H : SpinGlass.EnergySpace N)
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (hK : ∀ σ τ, K σ τ = K τ σ) (σs : Replicas N n) :
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      K σ τ *
        (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
            replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
          (n : ℝ) *
            (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                gibbsEnergyMean H (SpinGlass.std_basis N τ) -
              gibbsEnergyMean H
                (energyPointwiseMul (SpinGlass.std_basis N σ)
                  (SpinGlass.std_basis N τ))))) =
      (∑ a : Fin n, ∑ b : Fin n, K (σs a) (σs b)) -
        2 * (n : ℝ) *
          (∑ a : Fin n, ∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H τ * K (σs a) τ) +
        (n : ℝ) * ((n : ℝ) + 1) *
          (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * K σ τ) -
        (n : ℝ) *
          (∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * K σ σ) := by
  classical
  simp_rw [replicaEnergyScore_std_basis_count,
    gibbsEnergyMean_std_basis, gibbsEnergyMean_pointwiseMul_std_basis]
  ring_nf
  have hpc :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * SpinGlass.gibbs_pmf N H σ * replicaConfigCount σs τ) =
        ∑ a : Fin n, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H τ * K (σs a) τ := by
    calc
      _ = ∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ *
          ∑ τ : SpinGlass.Config N, replicaConfigCount σs τ * K σ τ := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = ∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ *
          ∑ a : Fin n, K σ (σs a) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [sum_replicaConfigCount_mul_kernel]
      _ = ∑ σ : SpinGlass.Config N, ∑ a : Fin n,
          SpinGlass.gibbs_pmf N H σ * K σ (σs a) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ a : Fin n, ∑ σ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * K σ (σs a) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro τ _
        rw [hK τ (σs a)]
  have hcp :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * replicaConfigCount σs σ * SpinGlass.gibbs_pmf N H τ) =
        ∑ a : Fin n, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H τ * K (σs a) τ := by
    calc
      _ = ∑ σ : SpinGlass.Config N, replicaConfigCount σs σ *
          (∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H τ * K σ τ) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = _ := by
        unfold replicaConfigCount
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        simp
  have hdiag :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (if σ = τ then SpinGlass.gibbs_pmf N H σ else 0)) =
        ∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * K σ σ := by
    simp [mul_comm]
  have hnpp :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (n : ℝ) * SpinGlass.gibbs_pmf N H σ *
          SpinGlass.gibbs_pmf N H τ) =
        (n : ℝ) * ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * K σ τ := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  have hn2pp :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (n : ℝ) ^ 2 * SpinGlass.gibbs_pmf N H σ *
          SpinGlass.gibbs_pmf N H τ) =
        (n : ℝ) ^ 2 * ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * K σ τ := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  have hnpc :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (n : ℝ) * SpinGlass.gibbs_pmf N H σ *
          replicaConfigCount σs τ) =
        (n : ℝ) * ∑ a : Fin n, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H τ * K (σs a) τ := by
    calc
      _ = (n : ℝ) * ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          K σ τ * SpinGlass.gibbs_pmf N H σ * replicaConfigCount σs τ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = _ := by rw [hpc]
  have hncp :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (n : ℝ) * replicaConfigCount σs σ *
          SpinGlass.gibbs_pmf N H τ) =
        (n : ℝ) * ∑ a : Fin n, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H τ * K (σs a) τ := by
    calc
      _ = (n : ℝ) * ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          K σ τ * replicaConfigCount σs σ * SpinGlass.gibbs_pmf N H τ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = _ := by rw [hcp]
  have hndiag :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        K σ τ * (n : ℝ) *
          (if σ = τ then SpinGlass.gibbs_pmf N H σ else 0)) =
        (n : ℝ) * ∑ σ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * K σ σ := by
    calc
      _ = (n : ℝ) * ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          K σ τ * (if σ = τ then SpinGlass.gibbs_pmf N H σ else 0) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = _ := by rw [hdiag]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hnpp, hnpc, hncp, hndiag, hn2pp,
    sum_kernel_mul_two_replicaConfigCounts K σs]
  ring

noncomputable def normalizedKernelScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N)
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (σs : Replicas N n) : ℝ :=
  (∑ a : Fin n, ∑ b : Fin n, K (σs a) (σs b)) -
    2 * (n : ℝ) *
      (∑ a : Fin n, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H τ * K (σs a) τ) +
    (n : ℝ) * ((n : ℝ) + 1) *
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * K σ τ) -
    (n : ℝ) *
      (∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * K σ σ)

lemma kernel_score_contraction_eq_normalizedKernelScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N)
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (hK : ∀ σ τ, K σ τ = K τ σ) (σs : Replicas N n) :
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      K σ τ *
        (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
            replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
          (n : ℝ) *
            (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                gibbsEnergyMean H (SpinGlass.std_basis N τ) -
              gibbsEnergyMean H
                (energyPointwiseMul (SpinGlass.std_basis N σ)
                  (SpinGlass.std_basis N τ))))) =
      normalizedKernelScore H K σs := by
  exact kernel_score_contraction H K hK σs

lemma kernel_secondVariation_contraction {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n)
    (K : SpinGlass.Config N → SpinGlass.Config N → ℝ)
    (hK : ∀ σ τ, K σ τ = K τ σ) :
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      K σ τ * gibbsReplicaSecondVariation H
        (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F) =
      replicaGibbsAverage H (fun σs => F σs * normalizedKernelScore H K σs) := by
  classical
  unfold gibbsReplicaSecondVariation replicaGibbsAverage
  simp_rw [Finset.mul_sum]
  let W : Replicas N n → ℝ := fun σs =>
    ∏ a : Fin n, SpinGlass.gibbs_pmf N H (σs a)
  have hreorder :
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        ∑ σs : Replicas N n,
          K σ τ *
            (W σs * (F σs *
              (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
                  replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
                (n : ℝ) *
                  (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                      gibbsEnergyMean H (SpinGlass.std_basis N τ) -
                    gibbsEnergyMean H
                      (energyPointwiseMul (SpinGlass.std_basis N σ)
                        (SpinGlass.std_basis N τ)))))) =
        ∑ σs : Replicas N n, F σs * W σs *
          (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
            K σ τ *
              (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
                  replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
                (n : ℝ) *
                  (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                      gibbsEnergyMean H (SpinGlass.std_basis N τ) -
                    gibbsEnergyMean H
                      (energyPointwiseMul (SpinGlass.std_basis N σ)
                        (SpinGlass.std_basis N τ)))))) := by
    simp_rw [Finset.mul_sum]
    rw [show
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        ∑ σs : Replicas N n, K σ τ *
          (W σs * (F σs *
            (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
                replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
              (n : ℝ) *
                (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                    gibbsEnergyMean H (SpinGlass.std_basis N τ) -
                  gibbsEnergyMean H
                    (energyPointwiseMul (SpinGlass.std_basis N σ)
                      (SpinGlass.std_basis N τ)))))) =
        ∑ σ : SpinGlass.Config N, ∑ σs : Replicas N n,
          ∑ τ : SpinGlass.Config N, K σ τ *
            (W σs * (F σs *
              (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
                  replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
                (n : ℝ) *
                  (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                      gibbsEnergyMean H (SpinGlass.std_basis N τ) -
                    gibbsEnergyMean H
                      (energyPointwiseMul (SpinGlass.std_basis N σ)
                        (SpinGlass.std_basis N τ))))))) by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σs _
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  calc
    _ = ∑ σs : Replicas N n, F σs * W σs *
        (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          K σ τ *
            (replicaEnergyScore H (SpinGlass.std_basis N σ) σs *
                replicaEnergyScore H (SpinGlass.std_basis N τ) σs +
              (n : ℝ) *
                (gibbsEnergyMean H (SpinGlass.std_basis N σ) *
                    gibbsEnergyMean H (SpinGlass.std_basis N τ) -
                  gibbsEnergyMean H
                    (energyPointwiseMul (SpinGlass.std_basis N σ)
                      (SpinGlass.std_basis N τ))))) := by
      exact hreorder
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σs _
      rw [kernel_score_contraction_eq_normalizedKernelScore H K hK σs]
      dsimp only [W]
      ring

noncomputable def normalizedCavityOrderedScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) : ℝ :=
  (1 / 2 : ℝ) *
      (∑ a : Fin n, ∑ b ∈ (Finset.univ.erase a),
        cavityInteractionAt q i (σs a) (σs b)) -
    (n : ℝ) *
      (∑ a : Fin n, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H τ * cavityInteractionAt q i (σs a) τ) +
    ((n : ℝ) * ((n : ℝ) + 1) / 2) *
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
          cavityInteractionAt q i σ τ)

lemma half_sum_offdiag_eq_sum_replicaEdge {n : ℕ}
    (f : Fin n → Fin n → ℝ) (hf : ∀ a b, f a b = f b a) :
    (1 / 2 : ℝ) *
        (∑ a : Fin n, ∑ b ∈ ((Finset.univ : Finset (Fin n)).erase a), f a b) =
      ∑ e : ReplicaEdge n, f e.1.1 e.1.2 := by
  classical
  let upper : ℝ :=
    ∑ a : Fin n, ∑ b ∈ (Finset.univ.filter (fun b : Fin n => a < b)), f a b
  let lower : ℝ :=
    ∑ a : Fin n, ∑ b ∈ (Finset.univ.filter (fun b : Fin n => b < a)), f a b
  have hpart (a : Fin n) :
      (Finset.univ : Finset (Fin n)).erase a =
        Finset.univ.filter (fun b : Fin n => a < b) ∪
          Finset.univ.filter (fun b : Fin n => b < a) := by
    ext b
    simp
    omega
  have hdisj (a : Fin n) : Disjoint
      (Finset.univ.filter (fun b : Fin n => a < b))
      (Finset.univ.filter (fun b : Fin n => b < a)) := by
    rw [Finset.disjoint_left]
    intro b hab hba
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab hba
    omega
  have hsplit :
      (∑ a : Fin n, ∑ b ∈ ((Finset.univ : Finset (Fin n)).erase a), f a b) =
        upper + lower := by
    dsimp only [upper, lower]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [hpart a, Finset.sum_union (hdisj a)]
  have hlower : lower = upper := by
    dsimp only [lower, upper]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a < b
    · simp [hab, hf b a]
    · simp [hab]
  have hedge : upper = ∑ e : ReplicaEdge n, f e.1.1 e.1.2 := by
    let s : Finset (Fin n × Fin n) :=
      Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
    have hs := Finset.sum_subtype
      (p := fun p : Fin n × Fin n => p.1 < p.2)
      (F := inferInstanceAs (Fintype (ReplicaEdge n))) s (by
      intro p
      simp [s]) (fun p : Fin n × Fin n => f p.1 p.2)
    dsimp only [upper]
    rw [← hs]
    simp [s, Finset.sum_filter, Fintype.sum_prod_type]
  rw [hsplit, hlower, hedge]
  ring

lemma half_normalizedKernelScore_cavityInteraction {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) :
    (1 / 2 : ℝ) * normalizedKernelScore H (cavityInteractionAt q i) σs =
      normalizedCavityOrderedScore H q i σs := by
  classical
  let d : ℝ := 1 - (1 / (N : ℝ)) - q
  have hsplit :
      (∑ a : Fin n, ∑ b : Fin n,
        cavityInteractionAt q i (σs a) (σs b)) =
        (∑ a : Fin n, cavityInteractionAt q i (σs a) (σs a)) +
          ∑ a : Fin n, ∑ b ∈ (Finset.univ.erase a),
            cavityInteractionAt q i (σs a) (σs b) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun b => cavityInteractionAt q i (σs a) (σs b)) (Finset.mem_univ a)]
    ring
  have hdiagRep :
      (∑ a : Fin n, cavityInteractionAt q i (σs a) (σs a)) = (n : ℝ) * d := by
    simp_rw [cavityInteractionAt_diag]
    simp [d]
    ring
  have hdiagGibbs :
      (∑ σ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * cavityInteractionAt q i σ σ) = d := by
    simp_rw [cavityInteractionAt_diag]
    rw [← Finset.sum_mul, SpinGlass.sum_gibbs_pmf]
    simp [d]
  unfold normalizedKernelScore normalizedCavityOrderedScore
  rw [hsplit, hdiagRep, hdiagGibbs]
  ring

noncomputable def normalizedCavityReplicaScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) : ℝ :=
  (∑ e : ReplicaEdge n,
      cavityInteractionAt q i (σs e.1.1) (σs e.1.2)) -
    (n : ℝ) *
      (∑ a : Fin n, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H τ * cavityInteractionAt q i (σs a) τ) +
    ((n : ℝ) * ((n : ℝ) + 1) / 2) *
      (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
          cavityInteractionAt q i σ τ)

/-- The normalized score written as a fixed observable of two additional
replicas. -/
noncomputable def normalizedCavityScoreObservable {N n : ℕ}
    (q : ℝ) (i : Fin N) (σs : Replicas N (n + 2)) : ℝ :=
  (∑ e : ReplicaEdge n,
      cavityInteractionAt q i
        (initialReplicas σs e.1.1) (initialReplicas σs e.1.2)) -
    (n : ℝ) *
      (∑ a : Fin n, cavityInteractionAt q i
        (initialReplicas σs a) (firstFreshReplica σs)) +
    ((n : ℝ) * ((n : ℝ) + 1) / 2) *
      cavityInteractionAt q i (firstFreshReplica σs) (secondFreshReplica σs)

lemma abs_normalizedCavityScoreObservable_four_le
    {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (σs : Replicas N 6) :
    |normalizedCavityScoreObservable (n := 4) q i σs| ≤ 64 := by
  classical
  let X : ReplicaEdge 4 → ℝ := fun e =>
    cavityInteractionAt q i
      (initialReplicas σs e.1.1) (initialReplicas σs e.1.2)
  let Y : Fin 4 → ℝ := fun a =>
    cavityInteractionAt q i (initialReplicas σs a) (firstFreshReplica σs)
  let Z : ℝ :=
    cavityInteractionAt q i (firstFreshReplica σs) (secondFreshReplica σs)
  have hedge : |∑ e : ReplicaEdge 4, X e| ≤ 12 := by
    calc
      |∑ e : ReplicaEdge 4, X e| ≤ ∑ e : ReplicaEdge 4, |X e| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : ReplicaEdge 4, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        exact abs_cavityInteractionAt_le_two hN hq i _ _
      _ = 12 := by
        have hcard : Fintype.card (ReplicaEdge 4) = 6 := by decide
        simp [hcard, nsmul_eq_mul]
        norm_num
  have hvertex : |∑ a : Fin 4, Y a| ≤ 8 := by
    calc
      |∑ a : Fin 4, Y a| ≤ ∑ a : Fin 4, |Y a| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin 4, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_cavityInteractionAt_le_two hN hq i _ _
      _ = 8 := by simp [nsmul_eq_mul]; norm_num
  have hfresh : |Z| ≤ 2 :=
    abs_cavityInteractionAt_le_two hN hq i _ _
  unfold normalizedCavityScoreObservable
  change |(∑ e : ReplicaEdge 4, X e) - (4 : ℝ) * (∑ a : Fin 4, Y a) +
    ((4 : ℝ) * ((4 : ℝ) + 1) / 2) * Z| ≤ 64
  norm_num
  calc
    |(∑ e : ReplicaEdge 4, X e) - 4 * (∑ a : Fin 4, Y a) + 10 * Z| ≤
        |∑ e : ReplicaEdge 4, X e| + |4 * (∑ a : Fin 4, Y a)| + |10 * Z| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 12 + 4 * 8 + 10 * 2 := by
      rw [abs_mul, abs_mul]
      norm_num
      nlinarith [hedge, hvertex, hfresh]
    _ = 64 := by norm_num

lemma replicaGibbsAverage_two_score_append {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) :
    replicaGibbsAverage H (fun τs : Replicas N 2 =>
      normalizedCavityScoreObservable q i (Fin.append σs τs)) =
        normalizedCavityReplicaScore H q i σs := by
  classical
  rw [replicaGibbsAverage_two]
  unfold normalizedCavityScoreObservable normalizedCavityReplicaScore
  simp only [initialReplicas, firstFreshReplica, secondFreshReplica,
    Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one]
  let A : ℝ := ∑ e : ReplicaEdge n,
    cavityInteractionAt q i (σs e.1.1) (σs e.1.2)
  let B : SpinGlass.Config N → ℝ := fun σ =>
    (n : ℝ) * ∑ a : Fin n, cavityInteractionAt q i (σs a) σ
  let D : SpinGlass.Config N → SpinGlass.Config N → ℝ := fun σ τ =>
    ((n : ℝ) * ((n : ℝ) + 1) / 2) * cavityInteractionAt q i σ τ
  have hB :
      (n : ℝ) * (∑ a : Fin n, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H τ * cavityInteractionAt q i (σs a) τ) =
        ∑ τ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H τ * B τ := by
    calc
      _ = ∑ a : Fin n, ∑ τ : SpinGlass.Config N,
          (n : ℝ) * (SpinGlass.gibbs_pmf N H τ *
            cavityInteractionAt q i (σs a) τ) := by
              simp_rw [Finset.mul_sum]
      _ = ∑ τ : SpinGlass.Config N, ∑ a : Fin n,
          (n : ℝ) * (SpinGlass.gibbs_pmf N H τ *
            cavityInteractionAt q i (σs a) τ) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro τ _
        dsimp [B]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  have hD :
      ((n : ℝ) * ((n : ℝ) + 1) / 2) *
          (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
              cavityInteractionAt q i σ τ) =
        ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * D σ τ := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    dsimp [D]
    ring
  rw [hB, hD]
  change (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
        (A - B σ + D σ τ)) =
    A - (∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * B σ) +
      ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * D σ τ
  have hinner (σ : SpinGlass.Config N) :
      (∑ τ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ *
          (A - B σ + D σ τ)) =
        SpinGlass.gibbs_pmf N H σ * (A - B σ) +
          ∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * D σ τ := by
    calc
      _ = ∑ τ : SpinGlass.Config N,
          (SpinGlass.gibbs_pmf N H τ *
              (SpinGlass.gibbs_pmf N H σ * (A - B σ)) +
            SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * D σ τ) := by
              apply Finset.sum_congr rfl
              intro τ _
              ring
      _ = (∑ τ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H τ) *
            (SpinGlass.gibbs_pmf N H σ * (A - B σ)) +
          ∑ τ : SpinGlass.Config N,
            SpinGlass.gibbs_pmf N H σ * SpinGlass.gibbs_pmf N H τ * D σ τ := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by rw [SpinGlass.sum_gibbs_pmf, one_mul]
  simp_rw [hinner, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ σ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * (A - B σ)) =
        (∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ) * A -
          ∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * B σ := by
            simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by rw [SpinGlass.sum_gibbs_pmf, one_mul]

lemma replicaGibbsAverage_mul_normalizedCavityScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (F : ReplicaFun N n) :
    replicaGibbsAverage H
        (fun σs => F σs * normalizedCavityReplicaScore H q i σs) =
      replicaGibbsAverage H (fun σs : Replicas N (n + 2) =>
        F (initialReplicas σs) * normalizedCavityScoreObservable q i σs) := by
  classical
  rw [replicaGibbsAverage_eq_sum_append]
  unfold replicaGibbsAverage
  apply Finset.sum_congr rfl
  intro σs _
  rw [Finset.mul_sum]
  simp only [initialReplicas_append]
  rw [← Finset.mul_sum]
  congr 1
  calc
    F σs * normalizedCavityReplicaScore H q i σs =
        F σs * replicaGibbsAverage H (fun τs : Replicas N 2 =>
          normalizedCavityScoreObservable q i (Fin.append σs τs)) := by
            rw [replicaGibbsAverage_two_score_append]
    _ = ∑ τs : Replicas N 2,
        (∏ b, SpinGlass.gibbs_pmf N H (τs b)) *
          (F σs * normalizedCavityScoreObservable q i (Fin.append σs τs)) := by
            unfold replicaGibbsAverage
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro τs _
            ring

lemma normalizedCavityOrderedScore_eq_replicaScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) :
    normalizedCavityOrderedScore H q i σs =
      normalizedCavityReplicaScore H q i σs := by
  unfold normalizedCavityOrderedScore normalizedCavityReplicaScore
  rw [half_sum_offdiag_eq_sum_replicaEdge
    (fun a b => cavityInteractionAt q i (σs a) (σs b))]
  intro a b
  exact cavityInteractionAt_comm q i (σs a) (σs b)

lemma half_normalizedKernelScore_eq_replicaScore {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (q : ℝ) (i : Fin N)
    (σs : Replicas N n) :
    (1 / 2 : ℝ) * normalizedKernelScore H (cavityInteractionAt q i) σs =
      normalizedCavityReplicaScore H q i σs := by
  rw [half_normalizedKernelScore_cavityInteraction,
    normalizedCavityOrderedScore_eq_replicaScore]

lemma lastSite_secondVariation_contraction_replica {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n)
    (β q s : ℝ) (i : Fin N) :
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
      ((s / 2) * β ^ 2 * cavityInteractionAt q i σ τ) *
        gibbsReplicaSecondVariation H
          (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F) =
      s * β ^ 2 * replicaGibbsAverage H
        (fun σs => F σs * normalizedCavityReplicaScore H q i σs) := by
  classical
  have hkernel := kernel_secondVariation_contraction H F
    (cavityInteractionAt q i) (cavityInteractionAt_comm q i)
  calc
    (∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        ((s / 2) * β ^ 2 * cavityInteractionAt q i σ τ) *
          gibbsReplicaSecondVariation H
            (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F) =
        ((s / 2) * β ^ 2) *
          ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
            cavityInteractionAt q i σ τ *
              gibbsReplicaSecondVariation H
                (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ = ((s / 2) * β ^ 2) * replicaGibbsAverage H
        (fun σs => F σs * normalizedKernelScore H (cavityInteractionAt q i) σs) := by
      rw [hkernel]
    _ = _ := by
      unfold replicaGibbsAverage
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σs _
      simp only
      rw [← half_normalizedKernelScore_eq_replicaScore H q i σs]
      ring

lemma fderiv_gibbs_firstVariation_apply {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    fderiv ℝ
        (fun K => fderiv ℝ
          (fun L => SpinGlass.gibbs_average_n_det (N := N) (n := n) L F) K u)
        H v = gibbsReplicaSecondVariation H u v F := by
  classical
  let Φ : SpinGlass.EnergySpace N → ℝ := fun K =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) K F
  have hfun : (fun K => fderiv ℝ Φ K u) = fun K =>
      ∑ σs : Replicas N n,
        F σs * (∏ a, SpinGlass.gibbs_pmf N K (σs a)) *
          replicaEnergyScore K u σs := by
    funext K
    rw [show fderiv ℝ Φ K u =
        replicaGibbsAverage K
          (fun σs => F σs * replicaEnergyScore K u σs) by
      exact fderiv_gibbs_average_n_det_score K u F]
    unfold replicaGibbsAverage
    apply Finset.sum_congr rfl
    intro σs _
    ring
  change fderiv ℝ (fun K => fderiv ℝ Φ K u) H v = _
  rw [hfun]
  have hdiff (σs : Replicas N n) : DifferentiableAt ℝ
      (fun K : SpinGlass.EnergySpace N =>
        F σs * (∏ a, SpinGlass.gibbs_pmf N K (σs a)) *
          replicaEnergyScore K u σs) H := by
    have hw := SpinGlass.differentiableAt_prod_gibbs_pmf
      (N := N) (n := n) H σs
    have hs := differentiableAt_replicaEnergyScore H u σs
    exact (hw.const_mul (F σs)).mul hs
  rw [fderiv_fun_sum (u := (Finset.univ : Finset (Replicas N n)))
    (A := fun σs K => F σs *
      (∏ a, SpinGlass.gibbs_pmf N K (σs a)) * replicaEnergyScore K u σs)
    (x := H) (fun σs _ => hdiff σs)]
  simp only [ContinuousLinearMap.sum_apply]
  have hterm (σs : Replicas N n) :
      (fderiv ℝ (fun K : SpinGlass.EnergySpace N =>
        F σs * (∏ a, SpinGlass.gibbs_pmf N K (σs a)) *
          replicaEnergyScore K u σs) H) v =
        F σs * (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
          (replicaEnergyScore H v σs * replicaEnergyScore H u σs +
            (n : ℝ) *
              (gibbsEnergyMean H u * gibbsEnergyMean H v -
                gibbsEnergyMean H (energyPointwiseMul u v))) := by
    have hw := SpinGlass.differentiableAt_prod_gibbs_pmf
      (N := N) (n := n) H σs
    have hs := differentiableAt_replicaEnergyScore H u σs
    have hd := ((hw.const_mul (F σs)).hasFDerivAt.mul hs.hasFDerivAt).fderiv
    have happ := congrArg (fun L : SpinGlass.EnergySpace N →L[ℝ] ℝ => L v) hd
    have hwapp := SpinGlass.fderiv_prod_gibbs_pmf_apply
      (N := N) (n := n) H v σs
    have hsapp := fderiv_replicaEnergyScore_apply H u v σs
    have hFw := congrArg (fun L : SpinGlass.EnergySpace N →L[ℝ] ℝ => L v)
      ((hw.hasFDerivAt.const_mul (F σs)).fderiv)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at happ hFw
    rw [hFw, hwapp, hsapp] at happ
    unfold replicaEnergyScore gibbsEnergyMean at happ ⊢
    simp only [energyPointwiseMul_apply] at happ ⊢
    convert happ using 1 <;> first | rfl | (congr 1 <;> ring) | ring
  simp_rw [hterm]
  unfold gibbsReplicaSecondVariation replicaGibbsAverage
  apply Finset.sum_congr rfl
  intro σs _
  ring

lemma abs_gibbsEnergyMean_le {N : ℕ}
    (H v : SpinGlass.EnergySpace N) :
    |gibbsEnergyMean H v| ≤ ‖v‖ := by
  classical
  unfold gibbsEnergyMean
  calc
    |∑ σ : SpinGlass.Config N, SpinGlass.gibbs_pmf N H σ * v σ| ≤
        ∑ σ : SpinGlass.Config N,
          |SpinGlass.gibbs_pmf N H σ * v σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (SpinGlass.gibbs_pmf_nonneg N H σ)]
      exact mul_le_mul_of_nonneg_left (SpinGlass.abs_apply_le_norm N v σ)
        (SpinGlass.gibbs_pmf_nonneg N H σ)
    _ = ‖v‖ := by
      rw [← Finset.sum_mul, SpinGlass.sum_gibbs_pmf, one_mul]

lemma abs_gibbsEnergyMean_mul_le {N : ℕ}
    (H u v : SpinGlass.EnergySpace N) :
    |gibbsEnergyMean H (energyPointwiseMul u v)| ≤ ‖u‖ * ‖v‖ := by
  classical
  unfold gibbsEnergyMean
  calc
    |∑ σ : SpinGlass.Config N,
        SpinGlass.gibbs_pmf N H σ * energyPointwiseMul u v σ| ≤
        ∑ σ : SpinGlass.Config N,
          |SpinGlass.gibbs_pmf N H σ * energyPointwiseMul u v σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : SpinGlass.Config N,
          SpinGlass.gibbs_pmf N H σ * (‖u‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [energyPointwiseMul_apply, abs_mul, abs_mul,
        abs_of_nonneg (SpinGlass.gibbs_pmf_nonneg N H σ)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (SpinGlass.abs_apply_le_norm N u σ)
          (SpinGlass.abs_apply_le_norm N v σ) (abs_nonneg _) (norm_nonneg _))
        (SpinGlass.gibbs_pmf_nonneg N H σ)
    _ = ‖u‖ * ‖v‖ := by
      rw [← Finset.sum_mul, SpinGlass.sum_gibbs_pmf, one_mul]

lemma abs_replicaEnergyScore_le {N n : ℕ}
    (H v : SpinGlass.EnergySpace N) (σs : Replicas N n) :
    |replicaEnergyScore H v σs| ≤ 2 * (n : ℝ) * ‖v‖ := by
  classical
  unfold replicaEnergyScore
  calc
    |∑ a : Fin n, (gibbsEnergyMean H v - v (σs a))| ≤
        ∑ a : Fin n, |gibbsEnergyMean H v - v (σs a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, (2 * ‖v‖) := by
      apply Finset.sum_le_sum
      intro a _
      calc
        |gibbsEnergyMean H v - v (σs a)| ≤
            |gibbsEnergyMean H v| + |v (σs a)| := abs_sub _ _
        _ ≤ ‖v‖ + ‖v‖ := add_le_add (abs_gibbsEnergyMean_le H v)
          (SpinGlass.abs_apply_le_norm N v (σs a))
        _ = 2 * ‖v‖ := by ring
    _ = 2 * (n : ℝ) * ‖v‖ := by simp; ring

lemma abs_gibbsReplicaSecondVariation_le {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    |gibbsReplicaSecondVariation H u v F| ≤
      (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)) *
        (∑ σs : Replicas N n, |F σs|) * ‖u‖ * ‖v‖ := by
  classical
  let C : ℝ := 4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (σs : Replicas N n) :
      |F σs *
        (replicaEnergyScore H u σs * replicaEnergyScore H v σs +
          (n : ℝ) * (gibbsEnergyMean H u * gibbsEnergyMean H v -
            gibbsEnergyMean H (energyPointwiseMul u v)))| ≤
        |F σs| * (C * ‖u‖ * ‖v‖) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hscoreU := abs_replicaEnergyScore_le H u σs
    have hscoreV := abs_replicaEnergyScore_le H v σs
    have hscoreProd :
        |replicaEnergyScore H u σs| * |replicaEnergyScore H v σs| ≤
          (2 * (n : ℝ) * ‖u‖) * (2 * (n : ℝ) * ‖v‖) :=
      mul_le_mul hscoreU hscoreV (abs_nonneg _) (by positivity)
    have hcov :
        |gibbsEnergyMean H u * gibbsEnergyMean H v -
          gibbsEnergyMean H (energyPointwiseMul u v)| ≤
            2 * (‖u‖ * ‖v‖) := by
      calc
        |gibbsEnergyMean H u * gibbsEnergyMean H v -
            gibbsEnergyMean H (energyPointwiseMul u v)| ≤
            |gibbsEnergyMean H u| * |gibbsEnergyMean H v| +
              |gibbsEnergyMean H (energyPointwiseMul u v)| := by
          simpa only [abs_mul] using
            (abs_sub (gibbsEnergyMean H u * gibbsEnergyMean H v)
              (gibbsEnergyMean H (energyPointwiseMul u v)))
        _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ :=
          add_le_add
            (mul_le_mul (abs_gibbsEnergyMean_le H u)
              (abs_gibbsEnergyMean_le H v) (abs_nonneg _) (norm_nonneg _))
            (abs_gibbsEnergyMean_mul_le H u v)
        _ = 2 * (‖u‖ * ‖v‖) := by ring
    calc
      |replicaEnergyScore H u σs * replicaEnergyScore H v σs +
          (n : ℝ) * (gibbsEnergyMean H u * gibbsEnergyMean H v -
            gibbsEnergyMean H (energyPointwiseMul u v))| ≤
          |replicaEnergyScore H u σs| * |replicaEnergyScore H v σs| +
            (n : ℝ) *
              |gibbsEnergyMean H u * gibbsEnergyMean H v -
                gibbsEnergyMean H (energyPointwiseMul u v)| := by
        calc
          |_ + _| ≤ |replicaEnergyScore H u σs *
              replicaEnergyScore H v σs| +
              |(n : ℝ) * (gibbsEnergyMean H u * gibbsEnergyMean H v -
                gibbsEnergyMean H (energyPointwiseMul u v))| := abs_add_le _ _
          _ = _ := by
            have hnabs : |(n : ℝ)| = (n : ℝ) :=
              abs_of_nonneg (Nat.cast_nonneg n)
            simp only [abs_mul, hnabs]
      _ ≤ (2 * (n : ℝ) * ‖u‖) * (2 * (n : ℝ) * ‖v‖) +
          (n : ℝ) * (2 * (‖u‖ * ‖v‖)) := by
        exact add_le_add hscoreProd
          (mul_le_mul_of_nonneg_left hcov (Nat.cast_nonneg n))
      _ = C * ‖u‖ * ‖v‖ := by dsimp [C]; ring
  unfold gibbsReplicaSecondVariation
  calc
    |replicaGibbsAverage H (fun σs => F σs *
        (replicaEnergyScore H u σs * replicaEnergyScore H v σs +
          (n : ℝ) * (gibbsEnergyMean H u * gibbsEnergyMean H v -
            gibbsEnergyMean H (energyPointwiseMul u v))))| ≤
        ∑ σs : Replicas N n, |F σs *
          (replicaEnergyScore H u σs * replicaEnergyScore H v σs +
            (n : ℝ) * (gibbsEnergyMean H u * gibbsEnergyMean H v -
              gibbsEnergyMean H (energyPointwiseMul u v)))| :=
      abs_replicaGibbsAverage_le_sum_abs _ _
    _ ≤ ∑ σs : Replicas N n, |F σs| * (C * ‖u‖ * ‖v‖) :=
      Finset.sum_le_sum (fun σs _ => hpoint σs)
    _ = (∑ σs : Replicas N n, |F σs|) * (C * ‖u‖ * ‖v‖) := by
      rw [Finset.sum_mul]
    _ = C * (∑ σs : Replicas N n, |F σs|) * ‖u‖ * ‖v‖ := by ring
    _ = _ := by rfl

lemma gibbsReplicaSecondVariation_comm {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    gibbsReplicaSecondVariation H u v F =
      gibbsReplicaSecondVariation H v u F := by
  have huv : energyPointwiseMul u v = energyPointwiseMul v u := by
    ext σ
    simp [energyPointwiseMul]
    ring
  unfold gibbsReplicaSecondVariation replicaGibbsAverage
  rw [huv]
  apply Finset.sum_congr rfl
  intro σs _
  ring

/-- The bundled second Fréchet derivative, with its two directions exposed. -/
lemma fderiv_fderiv_gibbs_average_n_det_apply {N n : ℕ}
    (H u v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    (fderiv ℝ
        (fderiv ℝ
          (fun K => SpinGlass.gibbs_average_n_det (N := N) (n := n) K F)) H v) u =
      gibbsReplicaSecondVariation H u v F := by
  let Φ : SpinGlass.EnergySpace N → ℝ := fun K =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) K F
  have hgradCD : ContDiff ℝ 1 (fderiv ℝ Φ) :=
    (contDiff_gibbs_average_n_det F).fderiv_right
      (m := (1 : WithTop ℕ∞)) (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hgrad : DifferentiableAt ℝ (fderiv ℝ Φ) H :=
    (hgradCD.differentiable (by norm_num)).differentiableAt
  rw [← fderiv_gibbs_firstVariation_apply H u v F]
  change (fderiv ℝ (fderiv ℝ Φ) H v) u =
    fderiv ℝ (fun K => fderiv ℝ Φ K u) H v
  rw [fderiv_clm_apply hgrad (differentiableAt_const (c := u))]
  simp

lemma fderiv_gibbsFirstVariation_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N n : ℕ} (A : E →L[ℝ] SpinGlass.EnergySpace N)
    (field v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) (x y : E) :
    fderiv ℝ
        (fun z : E => fderiv ℝ
          (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
          (A z + field) v) x y =
      gibbsReplicaSecondVariation (A x + field) (A y) v F := by
  let Φ : SpinGlass.EnergySpace N → ℝ := fun H =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H F
  have hgrad : ContDiff ℝ 1 (fderiv ℝ Φ) :=
    (contDiff_gibbs_average_n_det F).fderiv_right
      (m := (1 : WithTop ℕ∞)) (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have hc : HasFDerivAt
      (fun z : E => fderiv ℝ Φ (A z + field))
      ((fderiv ℝ (fderiv ℝ Φ) (A x + field)).comp A) x := by
    apply HasFDerivAt.comp x
    · exact (hgrad.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    · simpa using A.hasFDerivAt.add_const field
  have hv := hc.clm_apply (hasFDerivAt_const (x := x) (c := v))
  have hbase : HasFDerivAt (fderiv ℝ Φ)
      (fderiv ℝ (fderiv ℝ Φ) (A x + field)) (A x + field) :=
    (hgrad.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hfixed := hbase.clm_apply
    (hasFDerivAt_const (x := A x + field) (c := v))
  have hmixed := congrArg
    (fun L : SpinGlass.EnergySpace N →L[ℝ] ℝ => L (A y)) hfixed.fderiv
  rw [hv.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hmixed ⊢
  rw [show ((fderiv ℝ (fderiv ℝ Φ) (A x + field)).comp A).flip v y =
      (fderiv ℝ (fderiv ℝ Φ) (A x + field)).flip v (A y) by rfl]
  simp only [map_zero, zero_add] at hmixed ⊢
  rw [← hmixed]
  have hmain := fderiv_gibbs_firstVariation_apply (A x + field) v (A y) F
  have hcomm := gibbsReplicaSecondVariation_comm (A x + field) v (A y) F
  exact hmain.trans hcomm

noncomputable def hasModerateGrowth_gibbsFirstVariation_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N n : ℕ} (A : E →L[ℝ] SpinGlass.EnergySpace N)
    (field v : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    PhysLean.Probability.GaussianIBP.HasModerateGrowth
      (fun x : E => fderiv ℝ
        (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
        (A x + field) v) := by
  let S : ℝ := ∑ σs : Replicas N n, |F σs|
  let C₁ : ℝ := 2 * (n : ℝ) * S * ‖v‖
  let C₂ : ℝ := (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)) * S * ‖A‖ * ‖v‖
  let C : ℝ := 1 + C₁ + C₂
  have hS : 0 ≤ S := Finset.sum_nonneg (fun σs _ => abs_nonneg (F σs))
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  refine ⟨C, 0, by dsimp [C]; positivity, ?_, ?_⟩
  · intro x
    rw [pow_zero, mul_one]
    have hop := SpinGlass.norm_fderiv_gibbs_average_n_det_le
      (N := N) (n := n) (H := A x + field) F
    have happ := ContinuousLinearMap.le_opNorm
      (fderiv ℝ
        (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
        (A x + field)) v
    rw [← Real.norm_eq_abs]
    calc
      ‖(fderiv ℝ
          (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
          (A x + field)) v‖ ≤
          ‖fderiv ℝ
            (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
            (A x + field)‖ * ‖v‖ := happ
      _ ≤ C₁ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        simpa [C₁, S, Real.norm_eq_abs, mul_assoc] using hop
      _ ≤ C := by dsimp [C]; linarith
  · intro x
    rw [pow_zero, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by dsimp [C]; positivity) ?_
    intro y
    rw [fderiv_gibbsFirstVariation_affine A field v F x y]
    rw [Real.norm_eq_abs]
    calc
      |gibbsReplicaSecondVariation (A x + field) (A y) v F| ≤
          (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)) * S * ‖A y‖ * ‖v‖ := by
        simpa [S] using abs_gibbsReplicaSecondVariation_le
          (A x + field) (A y) v F
      _ ≤ C₂ * ‖y‖ := by
        have hAy := A.le_opNorm y
        have hfac : 0 ≤
            (4 * (n : ℝ) ^ 2 + 2 * (n : ℝ)) * S := by positivity
        have hv : 0 ≤ ‖v‖ := norm_nonneg v
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAy hfac) hv
        simpa [C₂, mul_assoc, mul_comm, mul_left_comm] using hm
      _ ≤ C * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
        dsimp [C]
        linarith

/-- Linear image of the joint disorder giving the random part of the
selected-site Hamiltonian. -/
noncomputable def lastSiteIBPPathCLM {N : ℕ} (i : Fin N) (s u : ℝ) :
    WithLp 2 (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        Real.sqrt s • siteEvenCLM i (WithLp.ofLp p).1 +
          Real.sqrt (1 - s) • siteEvenCLM i (WithLp.ofLp p).2 +
          Real.sqrt (s * u) • siteOddCLM i (WithLp.ofLp p).1 +
          Real.sqrt (1 - s * u) • siteOddCLM i (WithLp.ofLp p).2
      map_add' := by
        intro x y
        simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, map_add, smul_add]
        abel
      map_smul' := by
        intro c x
        simp [smul_add, smul_smul, mul_comm] }

/-- Linear image of the joint disorder giving the time derivative. -/
noncomputable def lastSiteIBPDerivCLM {N : ℕ} (i : Fin N) (s u : ℝ) :
    WithLp 2 (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        (s / (2 * Real.sqrt (s * u))) • siteOddCLM i (WithLp.ofLp p).1 -
          (s / (2 * Real.sqrt (1 - s * u))) • siteOddCLM i (WithLp.ofLp p).2
      map_add' := by
        intro x y
        simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, map_add, smul_add,
          sub_eq_add_neg, neg_add_rev]
        abel
      map_smul' := by
        intro c x
        simp [smul_sub, smul_smul, mul_comm] }

@[simp] lemma lastSiteIBPPathCLM_left {N : ℕ} (i : Fin N) (s u : ℝ)
    (U : SpinGlass.EnergySpace N) :
    lastSiteIBPPathCLM i s u (WithLp.toLp 2 (U, 0)) =
      Real.sqrt s • siteEvenCLM i U + Real.sqrt (s * u) • siteOddCLM i U := by
  simp [lastSiteIBPPathCLM]

@[simp] lemma lastSiteIBPPathCLM_right {N : ℕ} (i : Fin N) (s u : ℝ)
    (V : SpinGlass.EnergySpace N) :
    lastSiteIBPPathCLM i s u (WithLp.toLp 2 (0, V)) =
      Real.sqrt (1 - s) • siteEvenCLM i V +
        Real.sqrt (1 - s * u) • siteOddCLM i V := by
  simp [lastSiteIBPPathCLM]

@[simp] lemma lastSiteIBPDerivCLM_left {N : ℕ} (i : Fin N) (s u : ℝ)
    (U : SpinGlass.EnergySpace N) :
    lastSiteIBPDerivCLM i s u (WithLp.toLp 2 (U, 0)) =
      (s / (2 * Real.sqrt (s * u))) • siteOddCLM i U := by
  simp [lastSiteIBPDerivCLM]

@[simp] lemma lastSiteIBPDerivCLM_right {N : ℕ} (i : Fin N) (s u : ℝ)
    (V : SpinGlass.EnergySpace N) :
    lastSiteIBPDerivCLM i s u (WithLp.toLp 2 (0, V)) =
      -(s / (2 * Real.sqrt (1 - s * u))) • siteOddCLM i V := by
  simp [lastSiteIBPDerivCLM]

lemma lastSiteIBP_joint_basis_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (σ τ : SpinGlass.Config N) :
    (∑ j : (SpinGlass.isGaussianHilbert_UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) path.independent).ι,
      ((SpinGlass.isGaussianHilbert_UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) path.independent).τ j : ℝ) *
        lastSiteIBPDerivCLM i s u
          ((SpinGlass.isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) path.independent).w j) σ *
        lastSiteIBPPathCLM i s u
          ((SpinGlass.isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) path.independent).w j) τ) =
      (s / (2 * Real.sqrt (s * u))) * Real.sqrt (s * u) *
          (β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
            configCavityOverlapAt i σ τ) -
        (s / (2 * Real.sqrt (1 - s * u))) * Real.sqrt (1 - s * u) *
          (β ^ 2 * q * SpinGlass.spin N σ i * SpinGlass.spin N τ i) := by
  classical
  rw [show
    @Finset.univ
        (SpinGlass.isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) path.independent).ι
        (SpinGlass.isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) path.independent).fintype_ι =
      @Finset.univ (path.sk.hU.ι ⊕ path.simple.hV.ι) inferInstance by
    ext j
    simp only [Finset.mem_univ]]
  simp only [SpinGlass.isGaussianHilbert_UV,
    OrthonormalBasis.prod_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, LinearMap.inl_apply, LinearMap.inr_apply,
    Function.comp_apply]
  simp only [lastSiteIBPDerivCLM_left, lastSiteIBPDerivCLM_right,
    lastSiteIBPPathCLM_left, lastSiteIBPPathCLM_right,
    PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hskCross :
      (∑ x : path.sk.hU.ι, (path.sk.hU.τ x : ℝ) *
        ((s / (2 * Real.sqrt (s * u))) * siteOddCLM i (path.sk.hU.w x) σ) *
        (Real.sqrt s * siteEvenCLM i (path.sk.hU.w x) τ)) =
      (s / (2 * Real.sqrt (s * u))) * Real.sqrt s *
        ∑ x : path.sk.hU.ι, (path.sk.hU.τ x : ℝ) *
          siteEvenCLM i (path.sk.hU.w x) τ *
          siteOddCLM i (path.sk.hU.w x) σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hskOdd :
      (∑ x : path.sk.hU.ι, (path.sk.hU.τ x : ℝ) *
        ((s / (2 * Real.sqrt (s * u))) * siteOddCLM i (path.sk.hU.w x) σ) *
        (Real.sqrt (s * u) * siteOddCLM i (path.sk.hU.w x) τ)) =
      (s / (2 * Real.sqrt (s * u))) * Real.sqrt (s * u) *
        ∑ x : path.sk.hU.ι, (path.sk.hU.τ x : ℝ) *
          siteOddCLM i (path.sk.hU.w x) σ *
          siteOddCLM i (path.sk.hU.w x) τ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsimCross :
      (∑ x : path.simple.hV.ι, (path.simple.hV.τ x : ℝ) *
        ((-(s / (2 * Real.sqrt (1 - s * u)))) *
          siteOddCLM i (path.simple.hV.w x) σ) *
        (Real.sqrt (1 - s) * siteEvenCLM i (path.simple.hV.w x) τ)) =
      (-(s / (2 * Real.sqrt (1 - s * u)))) * Real.sqrt (1 - s) *
        ∑ x : path.simple.hV.ι, (path.simple.hV.τ x : ℝ) *
          siteEvenCLM i (path.simple.hV.w x) τ *
          siteOddCLM i (path.simple.hV.w x) σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsimOdd :
      (∑ x : path.simple.hV.ι, (path.simple.hV.τ x : ℝ) *
        ((-(s / (2 * Real.sqrt (1 - s * u)))) *
          siteOddCLM i (path.simple.hV.w x) σ) *
        (Real.sqrt (1 - s * u) * siteOddCLM i (path.simple.hV.w x) τ)) =
      (-(s / (2 * Real.sqrt (1 - s * u)))) * Real.sqrt (1 - s * u) *
        ∑ x : path.simple.hV.ι, (path.simple.hV.τ x : ℝ) *
          siteOddCLM i (path.simple.hV.w x) σ *
          siteOddCLM i (path.simple.hV.w x) τ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hskCross, hskOdd, hsimCross, hsimOdd]
  rw [sk_siteEven_siteOdd_basis_covariance_sum path.sk i τ σ,
    simple_siteEven_siteOdd_basis_covariance_sum path.simple i τ σ,
    sk_siteOdd_basis_covariance_sum path.sk i σ τ,
    simple_siteOdd_basis_covariance_sum path.simple i σ τ]
  ring

lemma lastSiteIBP_mixed_covariance
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu0 : 0 < s * u) (hu1 : s * u < 1)
    (σ τ : SpinGlass.Config N) :
    covariance
        (fun ω => lastSiteIBPDerivCLM i s u
          (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) ω) σ)
        (fun ω => lastSiteIBPPathCLM i s u
          (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) ω) τ) volume =
      (s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
        (configCavityOverlapAt i σ τ - q) := by
  let hg := SpinGlass.isGaussianHilbert_UV
    (N := N) (β := β) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) path.independent
  have hpair := gaussianHilbert_covariance_clm hg
    ((SpinGlass.evalCLM (N := N) σ).comp (lastSiteIBPDerivCLM i s u))
    ((SpinGlass.evalCLM (N := N) τ).comp (lastSiteIBPPathCLM i s u))
  have hpair' :
      covariance
          (fun ω => lastSiteIBPDerivCLM i s u
            (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
              (sk := path.sk) (sim := path.simple) ω) σ)
          (fun ω => lastSiteIBPPathCLM i s u
            (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
              (sk := path.sk) (sim := path.simple) ω) τ) volume =
        ∑ j : (SpinGlass.isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) path.independent).ι,
          ((SpinGlass.isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) path.independent).τ j : ℝ) *
            lastSiteIBPDerivCLM i s u
              ((SpinGlass.isGaussianHilbert_UV
                (N := N) (β := β) (h := h) (q := q)
                (sk := path.sk) (sim := path.simple) path.independent).w j) σ *
            lastSiteIBPPathCLM i s u
              ((SpinGlass.isGaussianHilbert_UV
                (N := N) (β := β) (h := h) (q := q)
                (sk := path.sk) (sim := path.simple) path.independent).w j) τ := by
    simpa [hg] using hpair
  rw [hpair', lastSiteIBP_joint_basis_covariance path i σ τ]
  have hsqrt0 : Real.sqrt (s * u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu0)
  have hsqrt1 : Real.sqrt (1 - s * u) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (sub_pos.mpr hu1)
  field_simp [hsqrt0, hsqrt1]

lemma lastSiteIBP_trace_eq_config
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu0 : 0 < s * u) (hu1 : s * u < 1)
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) :
    (∑ j : (SpinGlass.isGaussianHilbert_UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) path.independent).ι,
      ((SpinGlass.isGaussianHilbert_UV
        (N := N) (β := β) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) path.independent).τ j : ℝ) *
        gibbsReplicaSecondVariation H
          (lastSiteIBPDerivCLM i s u
            ((SpinGlass.isGaussianHilbert_UV
              (N := N) (β := β) (h := h) (q := q)
              (sk := path.sk) (sim := path.simple) path.independent).w j))
          (lastSiteIBPPathCLM i s u
            ((SpinGlass.isGaussianHilbert_UV
              (N := N) (β := β) (h := h) (q := q)
              (sk := path.sk) (sim := path.simple) path.independent).w j)) F) =
      ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        ((s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          (configCavityOverlapAt i σ τ - q)) *
          gibbsReplicaSecondVariation H
            (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F := by
  let g := SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple)
  let hg := SpinGlass.isGaussianHilbert_UV
    (N := N) (β := β) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) path.independent
  let A := lastSiteIBPPathCLM i s u
  let B := lastSiteIBPDerivCLM i s u
  let Φ : SpinGlass.EnergySpace N → ℝ := fun K =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) K F
  let Q := (fderiv ℝ (fderiv ℝ Φ) H).flip
  have hQ (v w : SpinGlass.EnergySpace N) :
      Q v w = gibbsReplicaSecondVariation H v w F := by
    exact fderiv_fderiv_gibbs_average_n_det_apply H v w F
  have hcov (σ τ : SpinGlass.Config N) :
      covariance (fun ω => B (g ω) σ) (fun ω => A (g ω) τ) volume =
        (s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          (configCavityOverlapAt i σ τ - q) := by
    simpa [g, A, B] using lastSiteIBP_mixed_covariance path i hu0 hu1 σ τ
  have htrace := gaussianHilbert_bilinear_trace_eq_config hg A B Q
  have hcov' (σ τ : SpinGlass.Config N) :
      covariance
          (fun ω => B (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) ω) σ)
          (fun ω => A (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) ω) τ) volume =
        (s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          (configCavityOverlapAt i σ τ - q) := by
    simpa only [g] using hcov σ τ
  have htrace' :
      (∑ j : hg.ι, (hg.τ j : ℝ) *
        gibbsReplicaSecondVariation H (B (hg.w j)) (A (hg.w j)) F) =
        ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
          ((s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
            (configCavityOverlapAt i σ τ - q)) *
            gibbsReplicaSecondVariation H
              (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F := by
    simpa only [hQ, hcov'] using htrace
  exact htrace'

@[simp] lemma lastSiteIBPPathCLM_UV
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (ω : Ω) :
    lastSiteIBPPathCLM i s u
        (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) ω) +
        SpinGlass.magnetic_field_vector N h =
      lastSiteHamiltonian (s := s) path i u ω := by
  simp [lastSiteIBPPathCLM, SpinGlass.UV, lastSiteHamiltonian,
    lastSiteOddInterpolated]
  abel

@[simp] lemma lastSiteIBPDerivCLM_UV
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (ω : Ω) :
    lastSiteIBPDerivCLM i s u
        (SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) ω) =
      lastSiteHamiltonianDeriv (s := s) path i u ω := by
  rfl

/-- The fixed-disorder derivative before Gaussian integration by parts. -/
noncomputable def lastSiteGibbsDerivative
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) (ω : Ω) : ℝ :=
  fderiv ℝ (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
    (lastSiteHamiltonian (s := s) path i u ω)
    (lastSiteHamiltonianDeriv (s := s) path i u ω)

lemma measurable_lastSiteGibbsDerivative
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) :
    Measurable (lastSiteGibbsDerivative (s := s) path i u F) := by
  let Φ : SpinGlass.EnergySpace N → ℝ := fun H =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H F
  have hgrad : Continuous (fun H => fderiv ℝ Φ H) :=
    (contDiff_gibbs_average_n_det F).continuous_fderiv (by simp)
  have happ : Continuous
      (fun p : SpinGlass.EnergySpace N × SpinGlass.EnergySpace N =>
        fderiv ℝ Φ p.1 p.2) :=
    ((hgrad.comp continuous_fst).clm_apply continuous_snd)
  have hpair : Measurable (fun ω =>
      (lastSiteHamiltonian (s := s) path i u ω,
        lastSiteHamiltonianDeriv (s := s) path i u ω)) :=
    (measurable_lastSiteHamiltonian path i u).prodMk
      (measurable_lastSiteHamiltonianDeriv path i u)
  exact happ.measurable.comp hpair

set_option maxHeartbeats 1200000 in
lemma integral_lastSiteGibbsDerivative_ibp
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (u : ℝ) (F : ReplicaFun N n) :
    (∫ ω, lastSiteGibbsDerivative (s := s) path i u F ω ∂volume) =
      ∫ ω,
        ∑ j : (SpinGlass.isGaussianHilbert_UV
          (N := N) (β := β) (h := h) (q := q)
          (sk := path.sk) (sim := path.simple) path.independent).ι,
          ((SpinGlass.isGaussianHilbert_UV
            (N := N) (β := β) (h := h) (q := q)
            (sk := path.sk) (sim := path.simple) path.independent).τ j : ℝ) *
            gibbsReplicaSecondVariation
              (lastSiteHamiltonian (s := s) path i u ω)
              (lastSiteIBPDerivCLM i s u
                ((SpinGlass.isGaussianHilbert_UV
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := path.sk) (sim := path.simple) path.independent).w j))
              (lastSiteIBPPathCLM i s u
                ((SpinGlass.isGaussianHilbert_UV
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := path.sk) (sim := path.simple) path.independent).w j)) F
        ∂volume := by
  let g := SpinGlass.UV (N := N) (β := β) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple)
  let hg := SpinGlass.isGaussianHilbert_UV
    (N := N) (β := β) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) path.independent
  let A := lastSiteIBPPathCLM i s u
  let B := lastSiteIBPDerivCLM i s u
  let field := SpinGlass.magnetic_field_vector N h
  let Φ : SpinGlass.EnergySpace N → ℝ := fun H =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H F
  have hFi_diff : ∀ j : hg.ι, ContDiff ℝ 1
      (fun x => fderiv ℝ Φ (A x + field) (B (hg.w j))) := by
    intro j
    have hgrad : ContDiff ℝ 1 (fderiv ℝ Φ) :=
      (contDiff_gibbs_average_n_det F).fderiv_right
        (m := (1 : WithTop ℕ∞)) (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)
    exact (hgrad.comp (A.contDiff.add contDiff_const)).clm_apply contDiff_const
  have hFi_growth : ∀ j : hg.ι,
      PhysLean.Probability.GaussianIBP.HasModerateGrowth
        (fun x => fderiv ℝ Φ (A x + field) (B (hg.w j))) := by
    intro j
    exact hasModerateGrowth_gibbsFirstVariation_affine A field (B (hg.w j)) F
  have hmain := SpinGlass.GeneralizedLatala.gaussian_ibp_gradient_linear
    g hg A B field Φ hFi_diff hFi_growth
  have hleft :
      (∫ ω, lastSiteGibbsDerivative (s := s) path i u F ω ∂volume) =
        ∫ ω, fderiv ℝ Φ (A (g ω) + field) (B (g ω)) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    simp [g, A, B, field, Φ, lastSiteGibbsDerivative]
  rw [hleft, hmain]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with ω
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_gibbsFirstVariation_affine A field (B (hg.w j)) F (g ω) (hg.w j)]
  rw [gibbsReplicaSecondVariation_comm]
  simp [g, hg, A, B, field]

lemma integral_lastSiteGibbsDerivative_config
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu0 : 0 < s * u) (hu1 : s * u < 1)
    (F : ReplicaFun N n) :
    (∫ ω, lastSiteGibbsDerivative (s := s) path i u F ω ∂volume) =
      ∫ ω, ∑ σ : SpinGlass.Config N, ∑ τ : SpinGlass.Config N,
        ((s / 2) * β ^ 2 * SpinGlass.spin N σ i * SpinGlass.spin N τ i *
          (configCavityOverlapAt i σ τ - q)) *
          gibbsReplicaSecondVariation
            (lastSiteHamiltonian (s := s) path i u ω)
            (SpinGlass.std_basis N σ) (SpinGlass.std_basis N τ) F ∂volume := by
  rw [integral_lastSiteGibbsDerivative_ibp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with ω
  exact lastSiteIBP_trace_eq_config path i hu0 hu1
    (lastSiteHamiltonian (s := s) path i u ω) F

lemma integral_lastSiteGibbsDerivative_replica
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hu0 : 0 < s * u) (hu1 : s * u < 1)
    (F : ReplicaFun N n) :
    (∫ ω, lastSiteGibbsDerivative (s := s) path i u F ω ∂volume) =
      s * β ^ 2 *
        ∫ ω, replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω)
          (fun σs => F σs * normalizedCavityReplicaScore
            (lastSiteHamiltonian (s := s) path i u ω) q i σs) ∂volume := by
  rw [integral_lastSiteGibbsDerivative_config path i hu0 hu1 F]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with ω
  simpa [cavityInteractionAt, mul_assoc] using
    lastSite_secondVariation_contraction_replica
      (lastSiteHamiltonian (s := s) path i u ω) F β q s i

lemma hasDerivAt_lastSiteReplicaGibbsAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hs : 0 ≤ s) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hsu : s * u < 1) (F : ReplicaFun N n) (ω : Ω) :
    HasDerivAt
      (fun v => SpinGlass.gibbs_average_n_det (N := N) (n := n)
        (lastSiteHamiltonian (s := s) path i v ω) F)
      (lastSiteGibbsDerivative (s := s) path i u F ω) u := by
  let Φ : SpinGlass.EnergySpace N → ℝ := fun H =>
    SpinGlass.gibbs_average_n_det (N := N) (n := n) H F
  have hΦ : DifferentiableAt ℝ Φ
      (lastSiteHamiltonian (s := s) path i u ω) := by
    dsimp only [Φ]
    unfold SpinGlass.gibbs_average_n_det
    apply DifferentiableAt.fun_sum
    intro σs _
    exact (SpinGlass.differentiableAt_prod_gibbs_pmf
      (N := N) (n := n) (lastSiteHamiltonian (s := s) path i u ω) σs).const_mul
        (F σs)
  have hcomp := hΦ.hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_lastSiteHamiltonian path i hs hu hsu ω)
  change HasDerivAt (Φ ∘ fun v => lastSiteHamiltonian (s := s) path i v ω)
    (lastSiteGibbsDerivative (s := s) path i u F ω) u
  simpa only [lastSiteGibbsDerivative, Φ] using hcomp

set_option maxHeartbeats 1200000 in
lemma hasDerivAt_lastSiteQuenchedAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (F : ReplicaFun N n) :
    HasDerivAt (fun v => lastSiteQuenchedAverage (s := s) path i v F)
      (∫ ω, lastSiteGibbsDerivative (s := s) path i u F ω ∂volume) u := by
  classical
  by_cases hs0 : s = 0
  · subst s
    have hfun : (fun v => lastSiteQuenchedAverage (s := 0) path i v F) =
        fun _ => lastSiteQuenchedAverage (s := 0) path i u F := by
      funext v
      unfold lastSiteQuenchedAverage quenchedReplicaAverage
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      simp [lastSiteHamiltonian, lastSiteOddInterpolated]
    have hzero :
        (∫ ω, lastSiteGibbsDerivative (s := 0) path i u F ω ∂volume) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with ω
      simp [lastSiteGibbsDerivative, lastSiteHamiltonianDeriv]
    rw [hfun, hzero]
    exact hasDerivAt_const (x := u)
      (c := lastSiteQuenchedAverage (s := 0) path i u F)
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have h1u0 : 0 < 1 - u := by linarith
    let ε : ℝ := min u (1 - u) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    have hball : ∀ x ∈ Metric.ball u ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
      intro x hx
      have hdist : |x - u| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
      have hleft : u - x < ε := (abs_sub_lt_iff.1 hdist).2
      have hright : x - u < ε := (abs_sub_lt_iff.1 hdist).1
      have hεu : ε ≤ u / 2 := by
        dsimp [ε]
        have hmin := min_le_left u (1 - u)
        linarith
      have hε1u : ε ≤ (1 - u) / 2 := by
        dsimp [ε]
        have hmin := min_le_right u (1 - u)
        linarith
      constructor <;> linarith
    let G : ℝ → Ω → ℝ := fun x ω =>
      SpinGlass.gibbs_average_n_det (N := N) (n := n)
        (lastSiteHamiltonian (s := s) path i x ω) F
    let G' : ℝ → Ω → ℝ := fun x ω =>
      lastSiteGibbsDerivative (s := s) path i x F ω
    have hGmeas : ∀ᶠ x in nhds u, AEStronglyMeasurable (G x) (volume : Measure Ω) := by
      refine Filter.Eventually.of_forall fun x => ?_
      have hcont : Continuous (fun H : SpinGlass.EnergySpace N =>
          SpinGlass.gibbs_average_n_det (N := N) (n := n) H F) :=
        (contDiff_gibbs_average_n_det F).continuous
      exact (hcont.measurable.comp
        (measurable_lastSiteHamiltonian path i x)).aestronglyMeasurable
    have hGint : Integrable (G u) (volume : Measure Ω) := by
      have hmeas : AEStronglyMeasurable (G u) (volume : Measure Ω) :=
        hGmeas.self_of_nhds
      apply Integrable.of_bound hmeas (∑ σs, |F σs|)
      filter_upwards with ω
      have habs := abs_replicaGibbsAverage_le_sum_abs
        (lastSiteHamiltonian (s := s) path i u ω) F
      rw [replicaGibbsAverage_eq_gibbs_average_n_det] at habs
      simpa [G, Real.norm_eq_abs] using habs
    let CF : ℝ := (2 * (n : ℝ)) * (∑ σs, ‖F σs‖)
    have hCF : 0 ≤ CF := by
      dsimp [CF]
      positivity
    let O : ℝ := ‖siteOddCLM i‖
    have hO : 0 ≤ O := by dsimp [O]; positivity
    let cU : ℝ := s / (2 * Real.sqrt (s * (u / 2)))
    let cV : ℝ := s / (2 * Real.sqrt ((1 - u) / 2))
    have hcU : 0 ≤ cU := by dsimp [cU]; positivity
    have hcV : 0 ≤ cV := by dsimp [cV]; positivity
    let bound : Ω → ℝ := fun ω =>
      CF * (cU * O * ‖path.sk.U ω‖ + cV * O * ‖path.simple.V ω‖)
    have hboundInt : Integrable bound (volume : Measure Ω) := by
      have hUint : Integrable (fun ω => ‖path.sk.U ω‖) (volume : Measure Ω) :=
        PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian path.sk.hU
      have hVint : Integrable (fun ω => ‖path.simple.V ω‖) (volume : Measure Ω) :=
        PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian path.simple.hV
      have hUint' := hUint.const_mul (cU * O)
      have hVint' := hVint.const_mul (cV * O)
      simpa [bound, mul_assoc] using (hUint'.add hVint').const_mul CF
    have hG'meas : AEStronglyMeasurable (G' u) (volume : Measure Ω) := by
      exact (measurable_lastSiteGibbsDerivative path i u F).aestronglyMeasurable
    have hbound : ∀ᵐ ω ∂(volume : Measure Ω), ∀ x ∈ Metric.ball u ε,
        ‖G' x ω‖ ≤ bound ω := by
      refine ae_of_all _ fun ω => ?_
      intro x hx
      have hxIoo := hball x hx
      have hdist : |x - u| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
      have hxLower : u / 2 ≤ x := by
        have hleft : u - x < ε := (abs_sub_lt_iff.1 hdist).2
        have hεu : ε ≤ u / 2 := by
          dsimp [ε]
          have hmin := min_le_left u (1 - u)
          linarith
        linarith
      have hxUpper : x ≤ (1 + u) / 2 := by
        have hright : x - u < ε := (abs_sub_lt_iff.1 hdist).1
        have hε1u : ε ≤ (1 - u) / 2 := by
          dsimp [ε]
          have hmin := min_le_right u (1 - u)
          linarith
        linarith
      have hCoeffU :
          |s / (2 * Real.sqrt (s * x))| ≤ cU := by
        have hlower : s * (u / 2) ≤ s * x :=
          mul_le_mul_of_nonneg_left hxLower hs.1
        have hsqrt := Real.sqrt_le_sqrt hlower
        have hdenPos : 0 < 2 * Real.sqrt (s * (u / 2)) := by positivity
        have hdenLe : 2 * Real.sqrt (s * (u / 2)) ≤
            2 * Real.sqrt (s * x) := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt (s * x)) ≤
            1 / (2 * Real.sqrt (s * (u / 2))) := by
          simpa [one_div] using one_div_le_one_div_of_le hdenPos hdenLe
        have hmul := mul_le_mul_of_nonneg_left hrecip hs.1
        have hnonneg : 0 ≤ s / (2 * Real.sqrt (s * x)) := by positivity
        rw [abs_of_nonneg hnonneg]
        simpa [cU, div_eq_mul_inv] using hmul
      have hCoeffV :
          |s / (2 * Real.sqrt (1 - s * x))| ≤ cV := by
        have hsx : s * x ≤ x := by
          exact mul_le_of_le_one_left (le_of_lt hxIoo.1) hs.2
        have hlower : (1 - u) / 2 ≤ 1 - s * x := by
          linarith
        have hsqrt := Real.sqrt_le_sqrt hlower
        have hdenPos : 0 < 2 * Real.sqrt ((1 - u) / 2) := by positivity
        have hdenLe : 2 * Real.sqrt ((1 - u) / 2) ≤
            2 * Real.sqrt (1 - s * x) := by nlinarith
        have hrecip : 1 / (2 * Real.sqrt (1 - s * x)) ≤
            1 / (2 * Real.sqrt ((1 - u) / 2)) := by
          simpa [one_div] using one_div_le_one_div_of_le hdenPos hdenLe
        have hmul := mul_le_mul_of_nonneg_left hrecip hs.1
        have hnonneg : 0 ≤ s / (2 * Real.sqrt (1 - s * x)) := by positivity
        rw [abs_of_nonneg hnonneg]
        simpa [cV, div_eq_mul_inv] using hmul
      have hOddU : ‖siteOddCLM i (path.sk.U ω)‖ ≤ O * ‖path.sk.U ω‖ := by
        simpa [O] using ContinuousLinearMap.le_opNorm (siteOddCLM i) (path.sk.U ω)
      have hOddV : ‖siteOddCLM i (path.simple.V ω)‖ ≤ O * ‖path.simple.V ω‖ := by
        simpa [O] using ContinuousLinearMap.le_opNorm (siteOddCLM i) (path.simple.V ω)
      have hdH : ‖lastSiteHamiltonianDeriv (s := s) path i x ω‖ ≤
          cU * O * ‖path.sk.U ω‖ + cV * O * ‖path.simple.V ω‖ := by
        calc
          ‖lastSiteHamiltonianDeriv (s := s) path i x ω‖ ≤
              |s / (2 * Real.sqrt (s * x))| * ‖siteOddCLM i (path.sk.U ω)‖ +
                |s / (2 * Real.sqrt (1 - s * x))| *
                  ‖siteOddCLM i (path.simple.V ω)‖ := by
                    simpa only [lastSiteHamiltonianDeriv, norm_smul,
                      Real.norm_eq_abs] using
                      norm_sub_le
                        ((s / (2 * Real.sqrt (s * x))) • siteOddCLM i (path.sk.U ω))
                        ((s / (2 * Real.sqrt (1 - s * x))) •
                          siteOddCLM i (path.simple.V ω))
          _ ≤ cU * O * ‖path.sk.U ω‖ + cV * O * ‖path.simple.V ω‖ := by
            calc
              |s / (2 * Real.sqrt (s * x))| * ‖siteOddCLM i (path.sk.U ω)‖ +
                    |s / (2 * Real.sqrt (1 - s * x))| *
                      ‖siteOddCLM i (path.simple.V ω)‖ ≤
                  cU * (O * ‖path.sk.U ω‖) +
                    cV * (O * ‖path.simple.V ω‖) := by
                      exact add_le_add
                        (mul_le_mul hCoeffU hOddU (norm_nonneg _) hcU)
                        (mul_le_mul hCoeffV hOddV (norm_nonneg _) hcV)
              _ = _ := by ring
      have hop :
          ‖fderiv ℝ (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
              (lastSiteHamiltonian (s := s) path i x ω)‖ ≤ CF := by
        simpa [CF] using SpinGlass.norm_fderiv_gibbs_average_n_det_le
          (N := N) (n := n)
          (H := lastSiteHamiltonian (s := s) path i x ω) (f := F)
      have happ : ‖G' x ω‖ ≤ CF *
          ‖lastSiteHamiltonianDeriv (s := s) path i x ω‖ := by
        have hnorm := ContinuousLinearMap.le_opNorm
          (fderiv ℝ (fun H => SpinGlass.gibbs_average_n_det (N := N) (n := n) H F)
            (lastSiteHamiltonian (s := s) path i x ω))
          (lastSiteHamiltonianDeriv (s := s) path i x ω)
        exact le_trans hnorm (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      exact le_trans happ (by
        simpa [bound, G', mul_assoc] using
          mul_le_mul_of_nonneg_left hdH hCF)
    have hdiff : ∀ᵐ ω ∂(volume : Measure Ω), ∀ x ∈ Metric.ball u ε,
        HasDerivAt (fun v => G v ω) (G' x ω) x := by
      refine ae_of_all _ fun ω => ?_
      intro x hx
      have hxIoo := hball x hx
      have hsx : s * x < 1 := by
        calc
          s * x ≤ 1 * x := mul_le_mul_of_nonneg_right hs.2 (le_of_lt hxIoo.1)
          _ < 1 := by simpa using hxIoo.2
      simpa [G, G'] using
        hasDerivAt_lastSiteReplicaGibbsAverage path i hs.1 hxIoo hsx F ω
    have hmain :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := (volume : Measure Ω)) (F := G) (F' := G') (x₀ := u) (bound := bound)
        (s := Metric.ball u ε) (hs := Metric.ball_mem_nhds u hεpos)
        hGmeas hGint hG'meas hbound hboundInt hdiff).2
    simpa [lastSiteQuenchedAverage, quenchedReplicaAverage, G, G',
      replicaGibbsAverage_eq_gibbs_average_n_det] using hmain

lemma hasDerivAt_lastSiteQuenchedAverage_replica
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (F : ReplicaFun N n) :
    HasDerivAt (fun v => lastSiteQuenchedAverage (s := s) path i v F)
      (s * β ^ 2 *
        ∫ ω, replicaGibbsAverage (lastSiteHamiltonian (s := s) path i u ω)
          (fun σs => F σs * normalizedCavityReplicaScore
            (lastSiteHamiltonian (s := s) path i u ω) q i σs) ∂volume) u := by
  by_cases hs0 : s = 0
  · subst s
    simpa [lastSiteGibbsDerivative, lastSiteHamiltonianDeriv] using
      hasDerivAt_lastSiteQuenchedAverage path i hs hu F
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hsu0 : 0 < s * u := mul_pos hspos hu.1
    have hsu1 : s * u < 1 := by
      calc
        s * u ≤ 1 * u := mul_le_mul_of_nonneg_right hs.2 (le_of_lt hu.1)
        _ < 1 := by simpa using hu.2
    have hderiv := hasDerivAt_lastSiteQuenchedAverage path i hs hu F
    rw [integral_lastSiteGibbsDerivative_replica path i hsu0 hsu1 F] at hderiv
    exact hderiv

lemma hasDerivAt_lastSiteQuenchedAverage_fixedScore
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s u : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (F : ReplicaFun N n) :
    HasDerivAt (fun v => lastSiteQuenchedAverage (s := s) path i v F)
      (s * β ^ 2 * lastSiteQuenchedAverage (s := s) path i u
        (fun σs : Replicas N (n + 2) =>
          F (initialReplicas σs) * normalizedCavityScoreObservable q i σs)) u := by
  have hderiv := hasDerivAt_lastSiteQuenchedAverage_replica path i hs hu F
  simp_rw [replicaGibbsAverage_mul_normalizedCavityScore] at hderiv
  simpa [lastSiteQuenchedAverage, quenchedReplicaAverage] using hderiv

set_option maxHeartbeats 2000000 in
/-- Endpoint factorization before evaluating the remaining one-dimensional
Gaussian moment. -/
lemma lastSiteQuenchedAverage_zero_factor
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hq : 0 ≤ q) (i : Fin N)
    (F : (Fin n → SiteBaseConfig N i) → ℝ) (S : Finset (Fin n)) :
    lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => F (replicasSplitSiteEquiv i σs).1 *
          ∏ a ∈ S, SpinGlass.spin N (σs a) i) =
      (∫ ω, ∑ ρs, (∏ a, siteBaseWeight
          (lastSiteBulkEnergy (s := s) path i ω) (ρs a)) * F ρs ∂volume) *
        standardGaussianExpectation (fun z =>
          (-Real.tanh (h + β * Real.sqrt q * z)) ^ S.card) := by
  classical
  let Y : Ω → SpinGlass.EnergySpace N := lastSiteBulkEnergy (s := s) path i
  let X : Ω → SpinGlass.EnergySpace N := lastSiteOddRandom path i
  let obs : ReplicaFun N n := fun σs =>
    F (replicasSplitSiteEquiv i σs).1 *
      ∏ a ∈ S, SpinGlass.spin N (σs a) i
  let φ : SpinGlass.EnergySpace N → SpinGlass.EnergySpace N → ℝ :=
    fun B O => replicaGibbsAverage
      (B + O + siteOddCLM i (SpinGlass.magnetic_field_vector N h)) obs
  have hY : Measurable Y := by
    dsimp [Y, lastSiteBulkEnergy, lastSiteBulkRandom]
    have hsk : Measurable (fun ω => siteEvenCLM i (path.sk.U ω)) :=
      (siteEvenCLM i).continuous.measurable.comp path.sk.hU.repr_measurable
    have hsim : Measurable (fun ω => siteEvenCLM i (path.simple.V ω)) :=
      (siteEvenCLM i).continuous.measurable.comp path.simple.hV.repr_measurable
    exact ((hsk.const_smul (Real.sqrt s)).add
      (hsim.const_smul (Real.sqrt (1 - s)))).add measurable_const
  have hX : Measurable X := by
    dsimp [X, lastSiteOddRandom]
    exact (siteOddCLM i).continuous.measurable.comp path.simple.hV.repr_measurable
  have hIndep : IndepFun Y X volume := by
    have hi := lastSite_bulk_indep_odd (s := s) path i
    exact hi.comp (continuous_id.add continuous_const).measurable measurable_id
  have hφ : Measurable (fun p : SpinGlass.EnergySpace N × SpinGlass.EnergySpace N =>
      φ p.1 p.2) := by
    apply (measurable_replicaGibbsAverage obs).comp
    fun_prop
  have hInt : Integrable (fun ω => φ (Y ω) (X ω)) volume := by
    apply Integrable.of_bound
      ((hφ.comp (hY.prodMk hX)).aestronglyMeasurable)
      (∑ σs, |obs σs|)
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using
      abs_replicaGibbsAverage_le_sum_abs
        (Y ω + X ω + siteOddCLM i (SpinGlass.magnetic_field_vector N h)) obs
  have hprod := PhysLean.Probability.GaussianIBP.integral_pair_via_prod
    Y X hY hX hIndep hφ hInt
  rw [lastSiteQuenchedAverage, quenchedReplicaAverage]
  simp_rw [lastSiteHamiltonian_zero_split]
  change (∫ ω, φ (Y ω) (X ω) ∂volume) = _
  rw [hprod]
  rw [lastSiteOddRandom_law_eq_reference path hN hq i]
  let oddRef : (Fin N → ℝ) → SpinGlass.EnergySpace N := fun z =>
    siteOddCLM i (SpinGlass.GeneralizedLatala.referenceField N β q z)
  let BF : SpinGlass.EnergySpace N → ℝ := fun B =>
    ∑ ρs, (∏ a, siteBaseWeight B (ρs a)) * F ρs
  let g : ℝ → ℝ := fun z =>
    (-Real.tanh (h + β * Real.sqrt q * z)) ^ S.card
  have hOddRef : Measurable oddRef := by
    exact (siteOddCLM i).continuous.measurable.comp
      (SpinGlass.GeneralizedLatala.referenceFieldCLM N β q).continuous.measurable
  have hBF : Measurable BF := by
    dsimp [BF, siteBaseWeight]
    apply Finset.measurable_sum
    intro ρs _
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro a _
      apply Measurable.div
      · exact Real.measurable_exp.comp
          ((SpinGlass.evalCLM (N := N) (ρs a).1).continuous.measurable.neg)
      · apply Finset.measurable_sum
        intro τ _
        exact Real.measurable_exp.comp
          ((SpinGlass.evalCLM (N := N) τ.1).continuous.measurable.neg)
    · exact measurable_const
  have hgCont : Continuous g := by
    dsimp [g]
    have htanh : Continuous Real.tanh := by
      rw [show Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => (Real.cosh_pos x).ne')
    exact (htanh.comp (by fun_prop)).neg.pow _
  have hgInt : Integrable g (gaussianReal 0 1) := by
    apply Integrable.of_bound hgCont.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by
      simpa only [abs_neg] using (Real.abs_tanh_lt_one (h + β * Real.sqrt q * z)).le)
  have hEven : ∀ᵐ B ∂Measure.map Y volume,
      ∀ σ, B (flipSite i σ) = B σ := by
    have hset : MeasurableSet
        {B : SpinGlass.EnergySpace N | ∀ σ, B (flipSite i σ) = B σ} := by
      rw [show {B : SpinGlass.EnergySpace N |
          ∀ σ, B (flipSite i σ) = B σ} =
          ⋂ σ : SpinGlass.Config N,
            {B : SpinGlass.EnergySpace N | B (flipSite i σ) = B σ} by
        ext B
        simp]
      exact MeasurableSet.iInter fun σ => measurableSet_eq_fun
        (SpinGlass.evalCLM (N := N) (flipSite i σ)).continuous.measurable
        (SpinGlass.evalCLM (N := N) σ).continuous.measurable
    rw [ae_map_iff hY.aemeasurable hset]
    exact Filter.Eventually.of_forall fun ω => lastSiteBulkEnergy_invariant path i ω
  have hinner : ∀ᵐ B ∂Measure.map Y volume,
      (∫ O, φ B O ∂Measure.map oddRef
        (SpinGlass.GeneralizedLatala.gaussianProduct N)) =
        BF B * standardGaussianExpectation g := by
    filter_upwards [hEven] with B hB
    rw [MeasureTheory.integral_map hOddRef.aemeasurable]
    · rw [show (fun z => φ B (oddRef z)) = fun z => BF B * g (z i) by
        funext z
        dsimp [φ, oddRef]
        rw [reference_endpoint_eq_even_oneSite]
        have hobs : obs = fun σs =>
            F (replicasSplitSiteEquiv i σs).1 *
              (fun bs => ∏ a ∈ S,
                SpinGlass.GeneralizedLatala.boolSpin (bs a))
                (replicasSplitSiteEquiv i σs).2 := by
          funext σs
          dsimp [obs, replicasSplitSiteEquiv]
          simp [SpinGlass.GeneralizedLatala.spin_eq_boolSpin,
            configSplitSiteEquiv]
        rw [hobs]
        have hfac := replicaGibbsAverage_even_oneSite_factor i B hB
          (h + β * Real.sqrt q * z i) F
          (fun bs => ∏ a ∈ S, SpinGlass.GeneralizedLatala.boolSpin (bs a))
        rw [oneSiteReplicaMoment] at hfac
        simpa [BF, g] using hfac]
      rw [integral_const_mul]
      have hcoord :
          (∫ a : Fin N → ℝ, g (a i)
              ∂SpinGlass.GeneralizedLatala.gaussianProduct N) =
            ∫ z, g z ∂gaussianReal 0 1 := by
        unfold SpinGlass.GeneralizedLatala.gaussianProduct
        exact MeasureTheory.integral_comp_eval hgInt.aestronglyMeasurable
      rw [hcoord]
      unfold standardGaussianExpectation
      rfl
    · have hφB : Measurable (φ B) := by
        simpa [Function.comp_def] using
          hφ.comp (measurable_const.prodMk measurable_id)
      exact hφB.aestronglyMeasurable
  rw [integral_congr_ae hinner]
  rw [integral_mul_const]
  rw [MeasureTheory.integral_map hY.aemeasurable hBF.aestronglyMeasurable]

/-- Every product of two distinct selected-site replica spins has endpoint
expectation `q`.  Cardinality records distinctness without fixing labels. -/
lemma lastSite_spinMoment_two
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hh : 0 < h) (hq : q = rsQ β h) (i : Fin N)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    lastSiteQuenchedAverage (s := s) path i 0
      (fun σs => ∏ a ∈ S, SpinGlass.spin N (σs a) i) = q := by
  subst q
  have hfac := lastSiteQuenchedAverage_zero_factor (s := s) path hN
    (rsQ_mem_Icc β h).1 i (fun _ => 1) S
  have hbulk :
      (∫ ω, ∑ ρs : Fin n → SiteBaseConfig N i, (∏ a, siteBaseWeight
          (lastSiteBulkEnergy (s := s) path i ω) (ρs a)) * (1 : ℝ) ∂volume) = 1 := by
    simp_rw [mul_one, sum_replica_siteBaseWeight]
    simp
  rw [hbulk, one_mul, hS] at hfac
  calc
    lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => ∏ a ∈ S, SpinGlass.spin N (σs a) i) =
      standardGaussianExpectation (fun z =>
        (-Real.tanh (h + β * Real.sqrt (rsQ β h) * z)) ^ 2) := by
          simpa only [one_mul] using hfac
    _ = standardGaussianExpectation (fun z =>
        Real.tanh (h + β * Real.sqrt (rsQ β h) * z) ^ 2) := by
      congr 1
      funext z
      ring
    _ = rsQ β h := (rsQ_eq_gaussian_tanh_sq hh).symm

/-- Every product of four distinct selected-site replica spins has endpoint
expectation `r`. -/
lemma lastSite_spinMoment_four
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (hN : 0 < N) (hq : q = rsQ β h) (i : Fin N)
    (S : Finset (Fin n)) (hS : S.card = 4) :
    lastSiteQuenchedAverage (s := s) path i 0
      (fun σs => ∏ a ∈ S, SpinGlass.spin N (σs a) i) = rsR β h := by
  subst q
  have hfac := lastSiteQuenchedAverage_zero_factor (s := s) path hN
    (rsQ_mem_Icc β h).1 i (fun _ => 1) S
  have hbulk :
      (∫ ω, ∑ ρs : Fin n → SiteBaseConfig N i, (∏ a, siteBaseWeight
          (lastSiteBulkEnergy (s := s) path i ω) (ρs a)) * (1 : ℝ) ∂volume) = 1 := by
    simp_rw [mul_one, sum_replica_siteBaseWeight]
    simp
  rw [hbulk, one_mul, hS] at hfac
  calc
    lastSiteQuenchedAverage (s := s) path i 0
        (fun σs => ∏ a ∈ S, SpinGlass.spin N (σs a) i) =
      standardGaussianExpectation (fun z =>
        (-Real.tanh (h + β * Real.sqrt (rsQ β h) * z)) ^ 4) := by
          simpa only [one_mul] using hfac
    _ = standardGaussianExpectation (fun z =>
        Real.tanh (h + β * Real.sqrt (rsQ β h) * z) ^ 4) := by
      congr 1
      funext z
      ring
    _ = rsR β h := by
      rw [rsR_eq_gaussian_tanh_fourth]

lemma lastSiteHamiltonian_one
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N : ℕ} {β h q s : ℝ} (path : RSSmartPathDisorder Ω N β h q)
    (i : Fin N) (ω : Ω) :
    lastSiteHamiltonian (s := s) path i 1 ω = fullPathHamiltonian path s ω := by
  rw [lastSiteHamiltonian, lastSiteOddInterpolated, fullPathHamiltonian]
  simp only [mul_one]
  calc
    Real.sqrt s • siteEvenCLM i (path.sk.U ω) +
          Real.sqrt (1 - s) • siteEvenCLM i (path.simple.V ω) +
          (Real.sqrt s • siteOddCLM i (path.sk.U ω) +
            Real.sqrt (1 - s) • siteOddCLM i (path.simple.V ω)) +
          SpinGlass.magnetic_field_vector N h =
        Real.sqrt s • (siteEvenCLM i (path.sk.U ω) + siteOddCLM i (path.sk.U ω)) +
          Real.sqrt (1 - s) •
            (siteEvenCLM i (path.simple.V ω) + siteOddCLM i (path.simple.V ω)) +
          SpinGlass.magnetic_field_vector N h := by
            simp only [smul_add]
            abel
    _ = Real.sqrt s • path.sk.U ω + Real.sqrt (1 - s) • path.simple.V ω +
          SpinGlass.magnetic_field_vector N h := by
      rw [siteEven_add_siteOdd, siteEven_add_siteOdd]

end SpinGlass.AT
