module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
public import Lemmas.Concentration.Coupled
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! Law transport from abstract smart-path disorder to Gaussian coordinates. -/

open MeasureTheory ProbabilityTheory Real BigOperators
open PhysLean.Probability.GaussianIBP

set_option autoImplicit false

namespace SpinGlass.AT

lemma coupledDisorderCoefficient_inner
    (N : ℕ) (beta q s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (sigma tau : SpinGlass.Config N) :
    inner ℝ (coupledDisorderCoefficient N beta q s sigma)
      (coupledDisorderCoefficient N beta q s tau) =
      smartPathCovKernel N beta q s sigma tau := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [coupledDisorderCoefficient, smartPathCovKernel,
      SpinGlass.sk_cov_kernel, SpinGlass.simple_cov_kernel,
      PiLp.inner_apply]
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hs0 : 0 ≤ s := hs.1
    have h1s0 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    have hsqrt2N : Real.sqrt (2 * (N : ℝ)) ^ 2 = 2 * N :=
      Real.sq_sqrt (by positivity)
    have hsqrts : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
    have hsqrtq : Real.sqrt ((1 - s) * q) ^ 2 = (1 - s) * q :=
      Real.sq_sqrt (mul_nonneg h1s0 hq)
    rw [PiLp.inner_apply, Fintype.sum_sum_type]
    simp only [coupledDisorderCoefficient, RCLike.inner_apply, conj_trivial]
    change
      (∑ ij : Fin N × Fin N,
        (beta * Real.sqrt s / Real.sqrt (2 * N) *
            (SpinGlass.spin N tau ij.1 * SpinGlass.spin N tau ij.2)) *
          (beta * Real.sqrt s / Real.sqrt (2 * N) *
            (SpinGlass.spin N sigma ij.1 * SpinGlass.spin N sigma ij.2))) +
      ∑ i : Fin N,
        (beta * Real.sqrt ((1 - s) * q) * SpinGlass.spin N tau i) *
          (beta * Real.sqrt ((1 - s) * q) * SpinGlass.spin N sigma i) = _
    simp_rw [show ∀ ij : Fin N × Fin N,
        (beta * Real.sqrt s / Real.sqrt (2 * N) *
            (SpinGlass.spin N tau ij.1 * SpinGlass.spin N tau ij.2)) *
          (beta * Real.sqrt s / Real.sqrt (2 * N) *
            (SpinGlass.spin N sigma ij.1 * SpinGlass.spin N sigma ij.2)) =
          (beta ^ 2 * s / (2 * N)) *
            ((SpinGlass.spin N sigma ij.1 * SpinGlass.spin N tau ij.1) *
             (SpinGlass.spin N sigma ij.2 * SpinGlass.spin N tau ij.2)) by
      intro ij
      field_simp [Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < 2 * N)]
      rw [hsqrt2N, hsqrts]
      ring]
    simp_rw [show ∀ i : Fin N,
        (beta * Real.sqrt ((1 - s) * q) * SpinGlass.spin N tau i) *
          (beta * Real.sqrt ((1 - s) * q) * SpinGlass.spin N sigma i) =
          beta ^ 2 * (1 - s) * q *
            (SpinGlass.spin N sigma i * SpinGlass.spin N tau i) by
      intro i
      calc
        _ = beta ^ 2 * Real.sqrt ((1 - s) * q) ^ 2 *
            (SpinGlass.spin N sigma i * SpinGlass.spin N tau i) := by ring
        _ = _ := by rw [hsqrtq]; ring]
    have hedgeSum :
        (∑ ij : Fin N × Fin N,
          (beta ^ 2 * s / (2 * N)) *
            ((SpinGlass.spin N sigma ij.1 * SpinGlass.spin N tau ij.1) *
             (SpinGlass.spin N sigma ij.2 * SpinGlass.spin N tau ij.2))) =
          (beta ^ 2 * s / (2 * N)) *
            (∑ i : Fin N, SpinGlass.spin N sigma i * SpinGlass.spin N tau i) ^ 2 := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ i : Fin N, ∑ j : Fin N,
            (beta ^ 2 * s / (2 * N)) *
              ((SpinGlass.spin N sigma i * SpinGlass.spin N tau i) *
               (SpinGlass.spin N sigma j * SpinGlass.spin N tau j))) =
            ∑ i : Fin N,
              ((beta ^ 2 * s / (2 * N)) *
                (SpinGlass.spin N sigma i * SpinGlass.spin N tau i)) *
              (∑ j : Fin N,
                SpinGlass.spin N sigma j * SpinGlass.spin N tau j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (beta ^ 2 * s / (2 * N)) *
              (∑ i : Fin N,
                SpinGlass.spin N sigma i * SpinGlass.spin N tau i) *
              (∑ j : Fin N,
                SpinGlass.spin N sigma j * SpinGlass.spin N tau j) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = _ := by
          rw [show (∑ i : Fin N,
              SpinGlass.spin N sigma i * SpinGlass.spin N tau i) ^ 2 =
              (∑ i : Fin N,
                SpinGlass.spin N sigma i * SpinGlass.spin N tau i) *
              (∑ i : Fin N,
                SpinGlass.spin N sigma i * SpinGlass.spin N tau i) by
            exact pow_two _]
          rw [mul_assoc]
    rw [hedgeSum, ← Finset.mul_sum]
    unfold smartPathCovKernel SpinGlass.sk_cov_kernel
      SpinGlass.simple_cov_kernel SpinGlass.overlap
    simp_rw [pow_two]
    field_simp [hNr]

private noncomputable def flipConfig (N : ℕ) :
    SpinGlass.Config N ≃ SpinGlass.Config N where
  toFun sigma i := !sigma i
  invFun sigma i := !sigma i
  left_inv sigma := by ext i; simp
  right_inv sigma := by ext i; simp

private lemma spin_flip (N : ℕ) (sigma : SpinGlass.Config N) (i : Fin N) :
    SpinGlass.spin N (flipConfig N sigma) i = -SpinGlass.spin N sigma i := by
  cases h : sigma i <;> simp [flipConfig, SpinGlass.spin, h]

private lemma overlap_flip (N : ℕ) (sigma tau : SpinGlass.Config N) :
    SpinGlass.overlap N (flipConfig N sigma) (flipConfig N tau) =
      SpinGlass.overlap N sigma tau := by
  unfold SpinGlass.overlap
  apply congrArg ((1 / (N : ℝ)) * ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [spin_flip, spin_flip]
  ring

private noncomputable def flipEnergyCLM (N : ℕ) :
    SpinGlass.EnergySpace N →L[ℝ] SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap {
    toFun := fun H => WithLp.toLp 2 (fun sigma => H (flipConfig N sigma))
    map_add' := by intro H G; ext sigma; rfl
    map_smul' := by intro c H; ext sigma; rfl }

private noncomputable def coordinateRandomCLM
    (N : ℕ) (beta q s : ℝ) :
    EuclideanSpace ℝ (CoupledGaussianIndex N) →L[ℝ]
      SpinGlass.EnergySpace N :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun sigma =>
      -inner ℝ (coupledDisorderCoefficient N beta q s sigma) x)
    map_add' := by intro x y; ext sigma; simp [inner_add_right, add_comm]
    map_smul' := by intro c x; ext sigma; simp [inner_smul_right] }

private noncomputable def smartRandomPairCLM
    (N : ℕ) (s : ℝ) :
    (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
  Real.sqrt s • ContinuousLinearMap.fst ℝ _ _ +
    Real.sqrt (1 - s) • ContinuousLinearMap.snd ℝ _ _

private noncomputable def flippedSmartRandomPairCLM
    (N : ℕ) (s : ℝ) :
    (SpinGlass.EnergySpace N × SpinGlass.EnergySpace N) →L[ℝ]
      SpinGlass.EnergySpace N :=
  (flipEnergyCLM N).comp (smartRandomPairCLM N s)

lemma gaussianHilbert_hasGaussianLaw
    {Omega H : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {g : Omega → H} (hg : IsGaussianHilbert g) :
    HasGaussianLaw g volume := by
  have hc : ∀ i, HasGaussianLaw (hg.c i) volume := by
    intro i
    exact HasLaw.hasGaussianLaw
      (HasLaw.mk (P := volume) (hg.c_meas i).aemeasurable (hg.c_gauss i))
  have hterm : ∀ i, HasGaussianLaw (fun omega => (hg.c i omega) • hg.w i) volume := by
    intro i
    exact (hc i).map_fun ((ContinuousLinearMap.id ℝ ℝ).smulRight (hg.w i))
  have hind : iIndepFun (fun i omega => (hg.c i omega) • hg.w i) volume :=
    hg.c_indep.comp (fun i x => x • hg.w i) (fun i => by fun_prop)
  have hsum : HasGaussianLaw (fun omega => ∑ i, (hg.c i omega) • hg.w i) volume :=
    hind.hasGaussianLaw_fun_sum hterm
  exact hsum.congr (Filter.Eventually.of_forall fun omega => by
    simpa using congrFun hg.repr omega |>.symm)

private lemma gaussianHilbert_map_mean_zero
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {g : Omega → SpinGlass.EnergySpace N}
    (hg : IsGaussianHilbert g) :
    ∫ x, id x ∂Measure.map g volume = 0 := by
  have hgLaw := gaussianHilbert_hasGaussianLaw hg
  have hmap : ∫ x, id x ∂Measure.map g volume = ∫ omega, g omega ∂volume := by
    exact integral_map hgLaw.aemeasurable aestronglyMeasurable_id
  rw [hmap]
  have hcMean : ∀ i, ∫ omega, hg.c i omega ∂volume = 0 := by
    intro i
    have hmapc := integral_map (μ := volume) (hg.c_meas i).aemeasurable
      aestronglyMeasurable_id
    rw [hg.c_gauss i] at hmapc
    simpa using hmapc.symm.trans integral_id_gaussianReal
  rw [hg.repr, integral_finset_sum]
  · simp [integral_smul_const, hcMean]
  · intro i _
    have hci : HasGaussianLaw (hg.c i) volume := HasLaw.hasGaussianLaw
      (HasLaw.mk (P := volume) (hg.c_meas i).aemeasurable (hg.c_gauss i))
    exact hci.integrable.smul_const _

private lemma gaussianHilbert_coord_secondMoment
    {Omega H : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {g : Omega → H} (hg : IsGaussianHilbert g) [DecidableEq hg.ι]
    (i j : hg.ι) :
    ∫ omega, hg.c i omega * hg.c j omega ∂volume =
      if i = j then (hg.τ i : ℝ) else 0 := by
  classical
  have hc (k : hg.ι) : HasGaussianLaw (hg.c k) volume := HasLaw.hasGaussianLaw
    (HasLaw.mk (P := volume) (hg.c_meas k).aemeasurable (hg.c_gauss k))
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp only [← pow_two]
    have hmap := integral_map (μ := volume) (hg.c_meas i).aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 2)
          (Measure.map (hg.c i) volume) by fun_prop)
    rw [hg.c_gauss i] at hmap
    simpa using hmap.symm.trans (integral_sq_gaussianReal_centered (hg.τ i))
  · rw [if_neg hij]
    have hmul := hg.c_indep.indepFun hij |>.integral_mul_eq_mul_integral
      (hg.c_meas i).aestronglyMeasurable (hg.c_meas j).aestronglyMeasurable
    have hmean (k : hg.ι) : ∫ omega, hg.c k omega ∂volume = 0 := by
      have hmap := integral_map (μ := volume) (hg.c_meas k).aemeasurable
        aestronglyMeasurable_id
      rw [hg.c_gauss k] at hmap
      simpa using hmap.symm.trans integral_id_gaussianReal
    simpa [hmean] using hmul

private lemma gaussianHilbert_energy_pairing
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {g : Omega → SpinGlass.EnergySpace N}
    (hg : IsGaussianHilbert g) (sigma tau : SpinGlass.Config N) :
    ∫ omega, g omega sigma * g omega tau ∂volume =
      inner ℝ ((covOp (g := g) hg) (SpinGlass.std_basis N sigma))
        (SpinGlass.std_basis N tau) := by
  classical
  have hpoint (omega : Omega) (rho : SpinGlass.Config N) :
      g omega rho = ∑ i, hg.c i omega * hg.w i rho := by
    have h := congrFun hg.repr omega
    rw [h]
    simp
  have hterm (i j : hg.ι) :
      Integrable (fun omega =>
        hg.c i omega * hg.w i sigma * (hg.c j omega * hg.w j tau)) volume := by
    have hc (k : hg.ι) : HasGaussianLaw (hg.c k) volume := HasLaw.hasGaussianLaw
      (HasLaw.mk (P := volume) (hg.c_meas k).aemeasurable (hg.c_gauss k))
    have hij : Integrable (fun omega => hg.c i omega * hg.c j omega) volume := by
      exact ((hc i).memLp_two.integrable_mul (hc j).memLp_two).congr
        (Filter.Eventually.of_forall fun omega => by rfl)
    convert hij.const_mul (hg.w i sigma * hg.w j tau) using 1 <;> ext omega <;> ring
  simp_rw [hpoint, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hterm i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hterm _ j)]
  simp_rw [show ∀ i j, (fun omega =>
      hg.c i omega * hg.w i sigma * (hg.c j omega * hg.w j tau)) =
      fun omega => (hg.w i sigma * hg.w j tau) *
        (hg.c i omega * hg.c j omega) by
    intro i j; funext omega; ring,
    integral_const_mul, gaussianHilbert_coord_secondMoment hg]
  simp [covOp_apply, sum_inner, inner_smul_left, real_inner_comm,
    SpinGlass.inner_std_basis_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma gaussianHilbert_energy_cov
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {g : Omega → SpinGlass.EnergySpace N}
    (hg : IsGaussianHilbert g) (sigma tau : SpinGlass.Config N) :
    cov[fun omega => g omega sigma, fun omega => g omega tau; volume] =
      inner ℝ ((covOp (g := g) hg) (SpinGlass.std_basis N sigma))
        (SpinGlass.std_basis N tau) := by
  unfold covariance
  rw [show ∫ omega, g omega sigma ∂volume = 0 by
      have hmap := gaussianHilbert_map_mean_zero hg
      have hglaw := gaussianHilbert_hasGaussianLaw hg
      rw [integral_map hglaw.aemeasurable aestronglyMeasurable_id] at hmap
      have hvec : ∫ x, g x ∂volume = 0 := by simpa only [id_eq] using hmap
      rw [← eval_integral_piLp (fun rho => hglaw.integrable.eval_piLp rho) sigma,
        hvec]
      rfl,
    show ∫ omega, g omega tau ∂volume = 0 by
      have hmap := gaussianHilbert_map_mean_zero hg
      have hglaw := gaussianHilbert_hasGaussianLaw hg
      rw [integral_map hglaw.aemeasurable aestronglyMeasurable_id] at hmap
      have hvec : ∫ x, g x ∂volume = 0 := by simpa only [id_eq] using hmap
      rw [← eval_integral_piLp (fun rho => hglaw.integrable.eval_piLp rho) tau,
        hvec]
      rfl]
  simp only [mul_zero, sub_zero]
  exact gaussianHilbert_energy_pairing hg sigma tau

private lemma gaussianHilbert_energy_integral_eq_zero
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {g : Omega → SpinGlass.EnergySpace N}
    (hg : IsGaussianHilbert g) :
    ∫ omega, g omega ∂(volume : Measure Omega) = 0 := by
  have h := gaussianHilbert_map_mean_zero hg
  rw [integral_map (gaussianHilbert_hasGaussianLaw hg).aemeasurable
    aestronglyMeasurable_id] at h
  simpa only [id_eq] using h

private lemma flippedSmart_cov
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (s : Set.Icc (0 : ℝ) 1) (sigma tau : SpinGlass.Config N) :
    cov[
      fun omega => flippedSmartRandomPairCLM N s.1
        (path.sk.U omega, path.simple.V omega) sigma,
      fun omega => flippedSmartRandomPairCLM N s.1
        (path.sk.U omega, path.simple.V omega) tau;
      volume] = smartPathCovKernel N beta q s.1 sigma tau := by
  let sigma' := flipConfig N sigma
  let tau' := flipConfig N tau
  have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
  have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
  have hUs : MemLp (fun omega => path.sk.U omega sigma') 2 volume := by
    simpa using (hUlaw.map_fun (SpinGlass.evalCLM (N := N) sigma')).memLp_two
  have hUt : MemLp (fun omega => path.sk.U omega tau') 2 volume := by
    simpa using (hUlaw.map_fun (SpinGlass.evalCLM (N := N) tau')).memLp_two
  have hVs : MemLp (fun omega => path.simple.V omega sigma') 2 volume := by
    simpa using (hVlaw.map_fun (SpinGlass.evalCLM (N := N) sigma')).memLp_two
  have hVt : MemLp (fun omega => path.simple.V omega tau') 2 volume := by
    simpa using (hVlaw.map_fun (SpinGlass.evalCLM (N := N) tau')).memLp_two
  have hind (rho eta : SpinGlass.Config N) :
      (fun omega => path.sk.U omega rho) ⟂ᵢ[volume]
        (fun omega => path.simple.V omega eta) := by
    simpa [Function.comp_def] using path.independent.comp
      (SpinGlass.evalCLM (N := N) rho).measurable
      (SpinGlass.evalCLM (N := N) eta).measurable
  have hUV : cov[fun omega => path.sk.U omega sigma',
      fun omega => path.simple.V omega tau'; volume] = 0 :=
    (hind sigma' tau').covariance_eq_zero hUs hVt
  have hVU : cov[fun omega => path.simple.V omega sigma',
      fun omega => path.sk.U omega tau'; volume] = 0 := by
    rw [covariance_comm]
    exact (hind tau' sigma').covariance_eq_zero hUt hVs
  change cov[
    (fun omega => Real.sqrt s.1 * path.sk.U omega sigma') +
      (fun omega => Real.sqrt (1 - s.1) * path.simple.V omega sigma'),
    (fun omega => Real.sqrt s.1 * path.sk.U omega tau') +
      (fun omega => Real.sqrt (1 - s.1) * path.simple.V omega tau');
    volume] = _
  rw [covariance_add_left (hUs.const_mul _) (hVs.const_mul _)
      ((hUt.const_mul _).add (hVt.const_mul _)),
    covariance_add_right (hUs.const_mul _) (hUt.const_mul _) (hVt.const_mul _),
    covariance_add_right (hVs.const_mul _) (hUt.const_mul _) (hVt.const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [gaussianHilbert_energy_cov path.sk.hU,
    gaussianHilbert_energy_cov path.simple.hV, path.sk.cov_eq, path.simple.cov_eq,
    hUV, hVU]
  have hs_sq : Real.sqrt s.1 * Real.sqrt s.1 = s.1 := by
    simpa [pow_two] using Real.sq_sqrt s.2.1
  have h1s_sq : Real.sqrt (1 - s.1) * Real.sqrt (1 - s.1) = 1 - s.1 := by
    simpa [pow_two] using Real.sq_sqrt (sub_nonneg.mpr s.2.2)
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [← mul_assoc, hs_sq, ← mul_assoc, h1s_sq]
  unfold smartPathCovKernel
  dsimp [sigma', tau']
  unfold SpinGlass.sk_cov_kernel SpinGlass.simple_cov_kernel
  rw [overlap_flip]

private lemma bilin_eq_sum_std
    (N : ℕ)
    (C : SpinGlass.EnergySpace N →L[ℝ]
      SpinGlass.EnergySpace N →L[ℝ] ℝ)
    (x y : SpinGlass.EnergySpace N) :
    C x y = ∑ sigma, ∑ tau, x sigma * y tau *
      C (SpinGlass.std_basis N sigma) (SpinGlass.std_basis N tau) := by
  classical
  have hx : x = ∑ sigma : SpinGlass.Config N,
      (x sigma) • SpinGlass.std_basis N sigma := by
    ext rho
    simp [SpinGlass.std_basis]
  have hy : y = ∑ tau : SpinGlass.Config N,
      (y tau) • SpinGlass.std_basis N tau := by
    ext rho
    simp [SpinGlass.std_basis]
  calc
    C x y = C (∑ sigma, (x sigma) • SpinGlass.std_basis N sigma)
        (∑ tau, (y tau) • SpinGlass.std_basis N tau) :=
      congrArg₂ (fun a b => C a b) hx hy
    _ = _ := by
      simp [map_sum, map_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      apply Finset.sum_congr rfl
      intro tau _
      ring

private theorem smartPath_coordinate_random_law
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (s : Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) :
    Measure.map (fun omega => flippedSmartRandomPairCLM N s.1
        (path.sk.U omega, path.simple.V omega)) volume =
      Measure.map (coordinateRandomCLM N beta q s.1)
        (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
  let pair : Omega → SpinGlass.EnergySpace N × SpinGlass.EnergySpace N :=
    fun omega => (path.sk.U omega, path.simple.V omega)
  have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
  have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
  have hpair : HasGaussianLaw pair volume :=
    path.independent.hasGaussianLaw hUlaw hVlaw
  have hleft : HasGaussianLaw (fun omega => flippedSmartRandomPairCLM N s.1
      (pair omega)) volume := hpair.map_fun (flippedSmartRandomPairCLM N s.1)
  have hright : HasGaussianLaw (coordinateRandomCLM N beta q s.1)
      (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) :=
    IsGaussian.hasGaussianLaw_id.map_fun (coordinateRandomCLM N beta q s.1)
  let mu := Measure.map (fun omega => flippedSmartRandomPairCLM N s.1
      (pair omega)) volume
  let nu := Measure.map (coordinateRandomCLM N beta q s.1)
      (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N))
  letI : IsGaussian mu := hleft.isGaussian_map
  letI : IsGaussian nu := hright.isGaussian_map
  apply ProbabilityTheory.IsGaussian.ext
  · have hUint := gaussianHilbert_energy_integral_eq_zero path.sk.hU
    have hVint := gaussianHilbert_energy_integral_eq_zero path.simple.hV
    have hpint : ∫ omega, pair omega ∂volume = (0, 0) := by
      apply Prod.ext
      · change (ContinuousLinearMap.fst ℝ _ _)
          (∫ omega, pair omega ∂volume) = 0
        calc
          _ = ∫ omega, (ContinuousLinearMap.fst ℝ _ _) (pair omega)
                ∂volume :=
            ((ContinuousLinearMap.fst ℝ _ _).integral_comp_comm
              hpair.integrable).symm
          _ = 0 := by simpa [pair] using hUint
      · change (ContinuousLinearMap.snd ℝ _ _)
          (∫ omega, pair omega ∂volume) = 0
        calc
          _ = ∫ omega, (ContinuousLinearMap.snd ℝ _ _) (pair omega)
                ∂volume :=
            ((ContinuousLinearMap.snd ℝ _ _).integral_comp_comm
              hpair.integrable).symm
          _ = 0 := by simpa [pair] using hVint
    rw [integral_map hleft.aemeasurable aestronglyMeasurable_id,
      integral_map hright.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq]
    calc
      (∫ omega, flippedSmartRandomPairCLM N s.1 (pair omega) ∂volume) =
          flippedSmartRandomPairCLM N s.1 (∫ omega, pair omega ∂volume) :=
        (flippedSmartRandomPairCLM N s.1).integral_comp_comm hpair.integrable
      _ = 0 := by rw [hpint]; exact map_zero _
      _ = coordinateRandomCLM N beta q s.1
          (∫ x, x ∂SYK.standardGaussianMeasureOnEuclidean
            (CoupledGaussianIndex N)) := by
        have hzero := SYK.standardGaussianMeasureOnEuclidean_integral_id
          (ι := CoupledGaussianIndex N)
        have hzero' : ∫ x, x ∂SYK.standardGaussianMeasureOnEuclidean
            (CoupledGaussianIndex N) = 0 := by simpa only [id_eq] using hzero
        rw [hzero']
        exact (map_zero _).symm
      _ = ∫ x, coordinateRandomCLM N beta q s.1 x
            ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) :=
        ((coordinateRandomCLM N beta q s.1).integral_comp_comm
          IsGaussian.integrable_id).symm
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    calc
      covarianceBilin mu x y =
          ∑ sigma, ∑ tau, x sigma * y tau *
            covarianceBilin mu (SpinGlass.std_basis N sigma)
              (SpinGlass.std_basis N tau) := bilin_eq_sum_std N _ x y
      _ = ∑ sigma, ∑ tau, x sigma * y tau *
            covarianceBilin nu (SpinGlass.std_basis N sigma)
              (SpinGlass.std_basis N tau) := by
        apply Finset.sum_congr rfl
        intro sigma _
        apply Finset.sum_congr rfl
        intro tau _
        congr 1
        rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
          covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
          covariance_map, covariance_map]
        · rw [show ((fun u => inner ℝ (SpinGlass.std_basis N sigma) u) ∘
                fun omega => flippedSmartRandomPairCLM N s.1 (pair omega)) =
              fun omega => flippedSmartRandomPairCLM N s.1
                (path.sk.U omega, path.simple.V omega) sigma by
            funext omega
            simp [pair, SpinGlass.inner_std_basis_apply],
            show ((fun u => inner ℝ (SpinGlass.std_basis N tau) u) ∘
                fun omega => flippedSmartRandomPairCLM N s.1 (pair omega)) =
              fun omega => flippedSmartRandomPairCLM N s.1
                (path.sk.U omega, path.simple.V omega) tau by
            funext omega
            simp [pair, SpinGlass.inner_std_basis_apply],
            show ((fun u => inner ℝ (SpinGlass.std_basis N sigma) u) ∘
                coordinateRandomCLM N beta q s.1) =
              fun z => coordinateRandomCLM N beta q s.1 z sigma by
            funext z
            simp [SpinGlass.inner_std_basis_apply],
            show ((fun u => inner ℝ (SpinGlass.std_basis N tau) u) ∘
                coordinateRandomCLM N beta q s.1) =
              fun z => coordinateRandomCLM N beta q s.1 z tau by
            funext z
            simp [SpinGlass.inner_std_basis_apply]]
          dsimp only [coordinateRandomCLM]
          rw [flippedSmart_cov path s sigma tau]
          let gamma := SYK.standardGaussianMeasureOnEuclidean
            (CoupledGaussianIndex N)
          have hgamma : gamma = stdGaussian
              (EuclideanSpace ℝ (CoupledGaussianIndex N)) := by
            exact ProbabilityTheory.map_pi_eq_stdGaussian
          change smartPathCovKernel N beta q s.1 sigma tau =
            cov[fun z => -inner ℝ
                (coupledDisorderCoefficient N beta q s.1 sigma) z,
              fun z => -inner ℝ
                (coupledDisorderCoefficient N beta q s.1 tau) z; gamma]
          rw [show (fun z => -inner ℝ
                (coupledDisorderCoefficient N beta q s.1 sigma) z) =
              -(fun z => inner ℝ
                (coupledDisorderCoefficient N beta q s.1 sigma) z) by rfl,
            show (fun z => -inner ℝ
                (coupledDisorderCoefficient N beta q s.1 tau) z) =
              -(fun z => inner ℝ
                (coupledDisorderCoefficient N beta q s.1 tau) z) by rfl]
          rw [covariance_neg_left, covariance_neg_right, neg_neg, hgamma,
            ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
            ProbabilityTheory.covarianceBilin_stdGaussian]
          change smartPathCovKernel N beta q s.1 sigma tau =
            inner ℝ (coupledDisorderCoefficient N beta q s.1 sigma)
              (coupledDisorderCoefficient N beta q s.1 tau)
          exact (coupledDisorderCoefficient_inner N beta q s.1 s.2 hq sigma tau).symm
        all_goals fun_prop
      _ = covarianceBilin nu x y := (bilin_eq_sum_std N _ x y).symm

private lemma flipEnergy_fullPathHamiltonian
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q) (s : ℝ) (omega : Omega) :
    flipEnergyCLM N (fullPathHamiltonian path s omega) =
      flippedSmartRandomPairCLM N s (path.sk.U omega, path.simple.V omega) -
        SpinGlass.magnetic_field_vector N h := by
  ext sigma
  simp [flipEnergyCLM, fullPathHamiltonian, flippedSmartRandomPairCLM,
    smartRandomPairCLM, SpinGlass.magnetic_field_vector,
    SpinGlass.magnetization, spin_flip]
  ring

private lemma coordinateHamiltonian_eq_random_sub_field
    (N : ℕ) (beta h q s : ℝ)
    (x : EuclideanSpace ℝ (CoupledGaussianIndex N)) :
    coupledCoordinateHamiltonian N beta h q s x =
      coordinateRandomCLM N beta q s x -
        SpinGlass.magnetic_field_vector N h := by
  ext sigma
  simp [coupledCoordinateHamiltonian, coordinateRandomCLM,
    SpinGlass.magnetic_field_vector, SpinGlass.magnetization]
  ring

private lemma fullPath_flipped_energy_law
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (s : Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) :
    Measure.map (fun omega => flipEnergyCLM N
        (fullPathHamiltonian path s.1 omega)) volume =
      Measure.map (coupledCoordinateHamiltonian N beta h q s.1)
        (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
  have hlaw := smartPath_coordinate_random_law path s hq
  let addField : SpinGlass.EnergySpace N → SpinGlass.EnergySpace N :=
    fun H => H - SpinGlass.magnetic_field_vector N h
  have hadd : Measurable addField := by fun_prop
  have hmap := congrArg (Measure.map addField) hlaw
  have hleftAE : AEMeasurable (fun omega => flippedSmartRandomPairCLM N s.1
      (path.sk.U omega, path.simple.V omega)) volume := by
    have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
    have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
    exact (path.independent.hasGaussianLaw hUlaw hVlaw).map_fun
      (flippedSmartRandomPairCLM N s.1) |>.aemeasurable
  have hrightMeas : Measurable (coordinateRandomCLM N beta q s.1) :=
    (coordinateRandomCLM N beta q s.1).measurable
  rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable hleftAE,
    AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable
      hrightMeas.aemeasurable] at hmap
  rw [show (fun omega => flipEnergyCLM N
          (fullPathHamiltonian path s.1 omega)) =
        addField ∘ (fun omega => flippedSmartRandomPairCLM N s.1
          (path.sk.U omega, path.simple.V omega)) by
      funext omega
      exact flipEnergy_fullPathHamiltonian path s.1 omega,
    show coupledCoordinateHamiltonian N beta h q s.1 =
        addField ∘ coordinateRandomCLM N beta q s.1 by
      funext x
      exact coordinateHamiltonian_eq_random_sub_field N beta h q s.1 x]
  exact hmap

private lemma constrainedPartition_flipEnergy
    {N : ℕ} (H : SpinGlass.EnergySpace N) (v : ℝ) :
    constrainedPartition (flipEnergyCLM N H) v = constrainedPartition H v := by
  classical
  let e : SpinGlass.Config N × SpinGlass.Config N ≃
      SpinGlass.Config N × SpinGlass.Config N :=
    (flipConfig N).prodCongr (flipConfig N)
  unfold constrainedPartition
  apply Fintype.sum_equiv e
  intro p
  simp [e, flipEnergyCLM, overlap_flip]

private lemma quadraticCoupledPartition_flipEnergy
    {N : ℕ} (H : SpinGlass.EnergySpace N) (q rho : ℝ) :
    quadraticCoupledPartition (flipEnergyCLM N H) q rho =
      quadraticCoupledPartition H q rho := by
  classical
  let e : SpinGlass.Config N × SpinGlass.Config N ≃
      SpinGlass.Config N × SpinGlass.Config N :=
    (flipConfig N).prodCongr (flipConfig N)
  unfold quadraticCoupledPartition
  apply Fintype.sum_equiv e
  intro p
  simp [e, flipEnergyCLM, overlap_flip]

/-- The log ratio of the quadratically coupled partition function to its
uncoupled value has the canonical Gaussian-coordinate law. -/
theorem quadraticCoupled_log_ratio_law
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (s : Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) (rho : ℝ) :
    Measure.map (fun omega =>
        Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q rho) -
        Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q 0)) volume =
      Measure.map (fun x =>
        quadraticCoupledCoordinateLogPartition N beta h q s.1 rho x -
        quadraticCoupledCoordinateLogPartition N beta h q s.1 0 x)
        (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
  let Phi : SpinGlass.EnergySpace N → ℝ := fun H =>
    Real.log (quadraticCoupledPartition H q rho) -
      Real.log (quadraticCoupledPartition H q 0)
  have hPhi : Measurable Phi := by
    unfold Phi quadraticCoupledPartition
    fun_prop
  have hlaw := fullPath_flipped_energy_law path s hq
  have hmap := congrArg (Measure.map Phi) hlaw
  have hleftAE : AEMeasurable (fun omega => flipEnergyCLM N
      (fullPathHamiltonian path s.1 omega)) volume := by
    rw [show (fun omega => flipEnergyCLM N
        (fullPathHamiltonian path s.1 omega)) =
      fun omega => flippedSmartRandomPairCLM N s.1
        (path.sk.U omega, path.simple.V omega) -
          SpinGlass.magnetic_field_vector N h by
      funext omega
      exact flipEnergy_fullPathHamiltonian path s.1 omega]
    have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
    have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
    exact ((path.independent.hasGaussianLaw hUlaw hVlaw).map_fun
      (flippedSmartRandomPairCLM N s.1)).aemeasurable.sub aemeasurable_const
  have hrightMeas : Measurable (coupledCoordinateHamiltonian N beta h q s.1) := by
    rw [show coupledCoordinateHamiltonian N beta h q s.1 =
        fun x => coordinateRandomCLM N beta q s.1 x -
          SpinGlass.magnetic_field_vector N h by
      funext x
      exact coordinateHamiltonian_eq_random_sub_field N beta h q s.1 x]
    fun_prop
  rw [AEMeasurable.map_map_of_aemeasurable hPhi.aemeasurable hleftAE,
    AEMeasurable.map_map_of_aemeasurable hPhi.aemeasurable
      hrightMeas.aemeasurable] at hmap
  rw [show (fun omega =>
        Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q rho) -
        Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q 0)) =
      Phi ∘ (fun omega => flipEnergyCLM N
        (fullPathHamiltonian path s.1 omega)) by
      funext omega
      simp [Phi, quadraticCoupledPartition_flipEnergy],
    show (fun x =>
        quadraticCoupledCoordinateLogPartition N beta h q s.1 rho x -
        quadraticCoupledCoordinateLogPartition N beta h q s.1 0 x) =
      Phi ∘ coupledCoordinateHamiltonian N beta h q s.1 by rfl]
  exact hmap

/-- Uniform upper-tail concentration for the logarithm of the coupled Gibbs
moment along an arbitrary realization of the smart path. -/
theorem quadraticCoupled_log_ratio_upper_tail_path
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    {N : ℕ} (hN : 0 < N) {beta h : ℝ}
    (hp : (beta, h) ∈ K)
    (s : Set.Icc (0 : ℝ) 1)
    (path : RSSmartPathDisorder Omega N beta h (rsQ beta h))
    (rho t : ℝ) (ht : 0 < t) :
    volume {omega |
        (Real.log (quadraticCoupledPartition
            (fullPathHamiltonian path s.1 omega) (rsQ beta h) rho) -
          Real.log (quadraticCoupledPartition
            (fullPathHamiltonian path s.1 omega) (rsQ beta h) 0)) -
          ∫ eta,
            (Real.log (quadraticCoupledPartition
                (fullPathHamiltonian path s.1 eta) (rsQ beta h) rho) -
              Real.log (quadraticCoupledPartition
                (fullPathHamiltonian path s.1 eta) (rsQ beta h) 0))
            ∂volume > t} ≤
      ENNReal.ofReal (Real.exp
        (-t ^ 2 / (2 * (4 * data.βmax * Real.sqrt N) ^ 2))) := by
  let Y : Omega → ℝ := fun omega =>
    Real.log (quadraticCoupledPartition
        (fullPathHamiltonian path s.1 omega) (rsQ beta h) rho) -
      Real.log (quadraticCoupledPartition
        (fullPathHamiltonian path s.1 omega) (rsQ beta h) 0)
  let F : EuclideanSpace ℝ (CoupledGaussianIndex N) → ℝ := fun x =>
    quadraticCoupledCoordinateLogPartition N beta h (rsQ beta h) s.1 rho x -
      quadraticCoupledCoordinateLogPartition N beta h (rsQ beta h) s.1 0 x
  let gamma := SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)
  have hsmall := quadraticCoupledCoordinateLogRatio_lipschitz
    N beta h (rsQ beta h) s.1 rho hN s.2 (rsQ_mem_Icc beta h)
  have hbeta : |beta| ≤ data.βmax := by
    rw [abs_of_pos (data.β_pos (beta, h) hp)]
    exact data.β_bound (beta, h) hp
  have hconst : 4 * |beta| * Real.sqrt N ≤
      4 * data.βmax * Real.sqrt N := by gcongr
  have hlargeNonneg : 0 ≤ 4 * data.βmax * Real.sqrt N :=
    mul_nonneg (mul_nonneg (by norm_num) data.βmax_pos.le)
      (Real.sqrt_nonneg _)
  have hLip : LipschitzWith
      (4 * data.βmax * Real.sqrt N).toNNReal F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdist := hsmall.dist_le_mul x y
    rw [Real.coe_toNNReal _ (by positivity :
      0 ≤ 4 * |beta| * Real.sqrt N)] at hdist
    rw [Real.coe_toNNReal _ hlargeNonneg]
    exact hdist.trans (mul_le_mul_of_nonneg_right hconst dist_nonneg)
  have hFmeas : Measurable F := hLip.continuous.measurable
  have hfullAE : AEMeasurable (fullPathHamiltonian path s.1) volume := by
    have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
    have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
    have hpairAE : AEMeasurable
        (fun omega => (path.sk.U omega, path.simple.V omega)) volume :=
      hUlaw.aemeasurable.prodMk hVlaw.aemeasurable
    rw [show fullPathHamiltonian path s.1 = fun omega =>
        smartRandomPairCLM N s.1 (path.sk.U omega, path.simple.V omega) +
          SpinGlass.magnetic_field_vector N h by
      funext omega
      simp [fullPathHamiltonian, smartRandomPairCLM]]
    exact ((smartRandomPairCLM N s.1).measurable.comp_aemeasurable hpairAE).add
      aemeasurable_const
  have hPhi : Measurable (fun H : SpinGlass.EnergySpace N =>
      Real.log (quadraticCoupledPartition H (rsQ beta h) rho) -
        Real.log (quadraticCoupledPartition H (rsQ beta h) 0)) := by
    unfold quadraticCoupledPartition
    fun_prop
  have hYAE : AEMeasurable Y volume := by
    change AEMeasurable
      ((fun H : SpinGlass.EnergySpace N =>
        Real.log (quadraticCoupledPartition H (rsQ beta h) rho) -
          Real.log (quadraticCoupledPartition H (rsQ beta h) 0)) ∘
        fullPathHamiltonian path s.1) volume
    exact hPhi.aemeasurable.comp_aemeasurable hfullAE
  have hlaw : Measure.map Y volume = Measure.map F gamma := by
    simpa [Y, F, gamma] using quadraticCoupled_log_ratio_law
      path s (rsQ_mem_Icc beta h).1 rho
  have hmean : ∫ omega, Y omega ∂volume = ∫ x, F x ∂gamma := by
    calc
      ∫ omega, Y omega ∂volume = ∫ z, z ∂Measure.map Y volume :=
        (integral_map hYAE aestronglyMeasurable_id).symm
      _ = ∫ z, z ∂Measure.map F gamma := by rw [hlaw]
      _ = ∫ x, F x ∂gamma :=
        integral_map hFmeas.aemeasurable aestronglyMeasurable_id
  have hset : MeasurableSet {z : ℝ | z - ∫ x, F x ∂gamma > t} := by
    change MeasurableSet
      ((fun z : ℝ => z - ∫ x, F x ∂gamma) ⁻¹' Set.Ioi t)
    exact (measurable_id.sub measurable_const) measurableSet_Ioi
  have hevent : volume {omega | Y omega - ∫ eta, Y eta ∂volume > t} =
      gamma {x | F x - ∫ y, F y ∂gamma > t} := by
    rw [hmean]
    calc
      volume {omega | Y omega - ∫ x, F x ∂gamma > t} =
          (Measure.map Y volume) {z | z - ∫ x, F x ∂gamma > t} := by
        rw [Measure.map_apply_of_aemeasurable hYAE hset]
        rfl
      _ = (Measure.map F gamma) {z | z - ∫ x, F x ∂gamma > t} := by
        rw [hlaw]
      _ = gamma {x | F x - ∫ y, F y ∂gamma > t} := by
        rw [Measure.map_apply_of_aemeasurable hFmeas.aemeasurable hset]
        rfl
  change volume {omega | Y omega - ∫ eta, Y eta ∂volume > t} ≤ _
  rw [hevent]
  exact SYK.product_standardGaussian_upper_tail F
    (4 * data.βmax * Real.sqrt N) t
      (mul_pos (mul_pos (by norm_num) data.βmax_pos)
        (Real.sqrt_pos.2 (by exact_mod_cast hN))) ht hLip

/-- The joint vector of constrained log-partition functions for an arbitrary
smart-path realization has the same law as the canonical coordinate vector. -/
theorem coupled_constrained_log_partition_vector_law
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (s : Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) :
    Measure.map (fun omega =>
        fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
          Real.log (constrainedPartition
            (fullPathHamiltonian path s.1 omega) v.1)) volume =
      Measure.map (fun x =>
        fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
          coupledConstrainedLogPartition N beta h q s.1 v.1 x)
        (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
  let Phi : SpinGlass.EnergySpace N →
      ({v : ℝ // v ∈ attainableOverlaps N} → ℝ) :=
    fun H v => Real.log (constrainedPartition H v.1)
  have hPhi : Measurable Phi := by
    apply Measurable.of_eval
    intro v
    unfold Phi constrainedPartition
    apply Measurable.log
    apply Finset.measurable_sum
    intro p _
    by_cases hpv : SpinGlass.overlap N p.1 p.2 = v.1
    · simp only [if_pos hpv]
      fun_prop
    · simp only [if_neg hpv]
      fun_prop
  have hlaw := fullPath_flipped_energy_law path s hq
  have hmap := congrArg (Measure.map Phi) hlaw
  have hleftAE : AEMeasurable (fun omega => flipEnergyCLM N
      (fullPathHamiltonian path s.1 omega)) volume := by
    rw [show (fun omega => flipEnergyCLM N
        (fullPathHamiltonian path s.1 omega)) =
      fun omega => flippedSmartRandomPairCLM N s.1
        (path.sk.U omega, path.simple.V omega) -
          SpinGlass.magnetic_field_vector N h by
      funext omega
      exact flipEnergy_fullPathHamiltonian path s.1 omega]
    have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
    have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
    exact ((path.independent.hasGaussianLaw hUlaw hVlaw).map_fun
      (flippedSmartRandomPairCLM N s.1)).aemeasurable.sub aemeasurable_const
  have hrightMeas : Measurable (coupledCoordinateHamiltonian N beta h q s.1) := by
    rw [show coupledCoordinateHamiltonian N beta h q s.1 =
        fun x => coordinateRandomCLM N beta q s.1 x -
          SpinGlass.magnetic_field_vector N h by
      funext x
      exact coordinateHamiltonian_eq_random_sub_field N beta h q s.1 x]
    fun_prop
  rw [AEMeasurable.map_map_of_aemeasurable hPhi.aemeasurable hleftAE,
    AEMeasurable.map_map_of_aemeasurable hPhi.aemeasurable
      hrightMeas.aemeasurable] at hmap
  rw [show (fun omega =>
        fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
          Real.log (constrainedPartition
            (fullPathHamiltonian path s.1 omega) v.1)) =
      Phi ∘ (fun omega => flipEnergyCLM N
        (fullPathHamiltonian path s.1 omega)) by
      funext omega v
      simp [Phi, constrainedPartition_flipEnergy],
    show (fun x =>
        fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
          coupledConstrainedLogPartition N beta h q s.1 v.1 x) =
      Phi ∘ coupledCoordinateHamiltonian N beta h q s.1 by rfl]
  exact hmap

/-- Arbitrary-realization form of the coupled Gaussian maximum estimate. -/
theorem coupled_log_partition_gaussian_max_path
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    (N : ℕ) (beta h : ℝ) (s : Set.Icc (0 : ℝ) 1)
    (hp : (beta, h) ∈ K)
    (path : RSSmartPathDisorder Omega N beta h (rsQ beta h)) :
    (∫ omega, Finset.univ.sup' Finset.univ_nonempty
        (fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
          Real.log (constrainedPartition
              (fullPathHamiltonian path s.1 omega) v.1) -
            ∫ eta, Real.log (constrainedPartition
              (fullPathHamiltonian path s.1 eta) v.1) ∂volume)
        ∂volume) ≤
      2 * data.βmax * Real.sqrt N *
        Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
  let I := {v : ℝ // v ∈ attainableOverlaps N}
  let X : Omega → I → ℝ := fun omega v =>
    Real.log (constrainedPartition (fullPathHamiltonian path s.1 omega) v.1)
  let Y : EuclideanSpace ℝ (CoupledGaussianIndex N) → I → ℝ :=
    fun x v => coupledConstrainedLogPartition N beta h (rsQ beta h) s.1 v.1 x
  have hlaw : Measure.map X volume = Measure.map Y
      (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
    simpa [X, Y] using coupled_constrained_log_partition_vector_law
      path s (rsQ_mem_Icc beta h).1
  let Phi : SpinGlass.EnergySpace N → I → ℝ :=
    fun H v => Real.log (constrainedPartition H v.1)
  have hPhi : Measurable Phi := by
    apply Measurable.of_eval
    intro v
    unfold Phi constrainedPartition
    apply Measurable.log
    apply Finset.measurable_sum
    intro p _
    by_cases hpv : SpinGlass.overlap N p.1 p.2 = v.1
    · simp only [if_pos hpv]
      fun_prop
    · simp only [if_neg hpv]
      fun_prop
  have hUlaw := gaussianHilbert_hasGaussianLaw path.sk.hU
  have hVlaw := gaussianHilbert_hasGaussianLaw path.simple.hV
  have hpairAE : AEMeasurable
      (fun omega => (path.sk.U omega, path.simple.V omega)) volume :=
    hUlaw.aemeasurable.prodMk hVlaw.aemeasurable
  have hfullAE : AEMeasurable (fullPathHamiltonian path s.1) volume := by
    rw [show fullPathHamiltonian path s.1 = fun omega =>
        smartRandomPairCLM N s.1 (path.sk.U omega, path.simple.V omega) +
          SpinGlass.magnetic_field_vector N h by
      funext omega
      simp [fullPathHamiltonian, smartRandomPairCLM]]
    exact ((smartRandomPairCLM N s.1).measurable.comp_aemeasurable hpairAE).add
      aemeasurable_const
  have hXaemeas : AEMeasurable X volume := by
    change AEMeasurable (Phi ∘ fullPathHamiltonian path s.1) volume
    exact hPhi.aemeasurable.comp_aemeasurable hfullAE
  have hcoordMeas : Measurable
      (coupledCoordinateHamiltonian N beta h (rsQ beta h) s.1) := by
    rw [show coupledCoordinateHamiltonian N beta h (rsQ beta h) s.1 =
        fun x => coordinateRandomCLM N beta (rsQ beta h) s.1 x -
          SpinGlass.magnetic_field_vector N h by
      funext x
      exact coordinateHamiltonian_eq_random_sub_field N beta h
        (rsQ beta h) s.1 x]
    fun_prop
  have hYmeas : Measurable Y := by
    change Measurable (Phi ∘
      coupledCoordinateHamiltonian N beta h (rsQ beta h) s.1)
    exact hPhi.comp hcoordMeas
  have hmean (v : I) :
      (∫ omega, X omega v ∂volume) =
        ∫ x, Y x v ∂SYK.standardGaussianMeasureOnEuclidean
          (CoupledGaussianIndex N) := by
    calc
      (∫ omega, X omega v ∂volume) =
          ∫ z, z v ∂Measure.map X volume :=
        (integral_map hXaemeas
          (measurable_pi_apply v).aestronglyMeasurable).symm
      _ = ∫ z, z v ∂Measure.map Y
          (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
        rw [hlaw]
      _ = ∫ x, Y x v ∂SYK.standardGaussianMeasureOnEuclidean
          (CoupledGaussianIndex N) := integral_map hYmeas.aemeasurable
            (measurable_pi_apply v).aestronglyMeasurable
  let center : (I → ℝ) → ℝ := fun z =>
    Finset.univ.sup' Finset.univ_nonempty fun v =>
      z v - ∫ x, Y x v ∂SYK.standardGaussianMeasureOnEuclidean
        (CoupledGaussianIndex N)
  have hcenter : Measurable center := by
    unfold center
    let f : I → (I → ℝ) → ℝ := fun v z =>
      z v - ∫ x, Y x v ∂SYK.standardGaussianMeasureOnEuclidean
        (CoupledGaussianIndex N)
    have hf : ∀ v ∈ (Finset.univ : Finset I), Measurable (f v) := by
      intro v _
      exact (measurable_pi_apply v).sub measurable_const
    have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty f) :=
      Finset.measurable_sup' Finset.univ_nonempty hf
    rw [show (fun z => Finset.univ.sup' Finset.univ_nonempty fun v =>
          z v - ∫ x, Y x v ∂SYK.standardGaussianMeasureOnEuclidean
            (CoupledGaussianIndex N)) =
        Finset.univ.sup' Finset.univ_nonempty f by
      funext z
      exact (Finset.sup'_apply Finset.univ_nonempty f z).symm]
    exact hsup
  have hintegral :
      (∫ omega, center (X omega) ∂volume) =
        ∫ x, center (Y x) ∂SYK.standardGaussianMeasureOnEuclidean
          (CoupledGaussianIndex N) := by
    calc
      (∫ omega, center (X omega) ∂volume) =
          ∫ z, center z ∂Measure.map X volume :=
        (integral_map hXaemeas hcenter.aestronglyMeasurable).symm
      _ = ∫ z, center z ∂Measure.map Y
          (SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) := by
        rw [hlaw]
      _ = ∫ x, center (Y x)
          ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) :=
        integral_map hYmeas.aemeasurable hcenter.aestronglyMeasurable
  have hbound := coupled_log_partition_gaussian_max data N beta h s hp
  rw [show (∫ omega, Finset.univ.sup' Finset.univ_nonempty
        (fun v : I => X omega v - ∫ eta, X eta v ∂volume) ∂volume) =
      ∫ omega, center (X omega) ∂volume by
    congr 1
    funext omega
    apply Finset.sup'_congr
    · rfl
    · intro v _
      rw [hmean v]]
  rw [hintegral]
  change (∫ x, centeredGaussianMax Finset.univ_nonempty
      (fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
        coupledConstrainedLogPartition N beta h (rsQ beta h) s.1 v.1) x
      ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) ≤ _
  exact hbound

end SpinGlass.AT
