module

/- Compatibility adaptation: state the already-reduced set-membership goal directly. -/
public import Lemmas.Concentration.Transport
public import Lemmas.GuerraTalagrand.Flatness
public import Lemmas.GuerraTalagrand.Bound
public import Lemmas.SmartPath.Interpolation

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators Filter

set_option autoImplicit false

namespace SpinGlass.AT

universe u

private lemma integrable_log_sum_exp
    {Omega I : Type*} [MeasureSpace Omega] [IsFiniteMeasure (volume : Measure Omega)]
    [Fintype I] [Nonempty I]
    (F : I → Omega → ℝ) (hF : ∀ i, Integrable (F i)) :
    Integrable (fun omega => Real.log (∑ i, Real.exp (F i omega))) := by
  let A : Omega → ℝ := fun omega => ∑ i, |F i omega|
  have hA : Integrable A := integrable_finsetSum Finset.univ fun i _ => (hF i).abs
  have hmeas : AEStronglyMeasurable
      (fun omega => Real.log (∑ i, Real.exp (F i omega))) := by
    exact ((Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
      (hF i).aemeasurable.exp).log).aestronglyMeasurable
  have hcard : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hlogcard : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hcard
  refine (hA.add (integrable_const (Real.log (Fintype.card I : ℝ)))).mono' hmeas ?_
  filter_upwards [] with omega
  have hsumpos : 0 < ∑ i, Real.exp (F i omega) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hupper : Real.log (∑ i, Real.exp (F i omega)) ≤
      Real.log (Fintype.card I : ℝ) + A omega := by
    have hsum : (∑ i, Real.exp (F i omega)) ≤
        (Fintype.card I : ℝ) * Real.exp (A omega) := by
      calc
        (∑ i, Real.exp (F i omega)) ≤ ∑ _i : I, Real.exp (A omega) := by
          apply Finset.sum_le_sum
          intro i _
          apply Real.exp_le_exp.mpr
          exact (le_abs_self _).trans (Finset.single_le_sum
            (fun j _ => abs_nonneg (F j omega)) (Finset.mem_univ i))
        _ = _ := by simp
    have hlog := Real.log_le_log hsumpos hsum
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
    exact hlog
  let i0 : I := Classical.choice inferInstance
  have hlower : -(A omega) ≤ Real.log (∑ i, Real.exp (F i omega)) := by
    have hone : Real.exp (F i0 omega) ≤ ∑ i, Real.exp (F i omega) :=
      Finset.single_le_sum (fun i _ => Real.exp_nonneg (F i omega))
        (Finset.mem_univ i0)
    have hlog := Real.log_le_log (Real.exp_pos _) hone
    rw [Real.log_exp] at hlog
    have hFi : -(A omega) ≤ F i0 omega := by
      have hi := Finset.single_le_sum (fun j _ => abs_nonneg (F j omega))
        (Finset.mem_univ i0)
      exact (neg_le_neg hi).trans (neg_abs_le (F i0 omega))
    exact hFi.trans hlog
  rw [Real.norm_eq_abs]
  change |Real.log (∑ i, Real.exp (F i omega))| ≤
    A omega + Real.log (Fintype.card I : ℝ)
  apply abs_le.mpr
  constructor <;> linarith

private lemma integral_log_sum_exp_le
    {Omega I : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    [Fintype I] [Nonempty I]
    (F : I → Omega → ℝ) (a : I → ℝ) (B : ℝ)
    (hF : ∀ i, Integrable (F i))
    (hB : ∀ i, a i + ∫ omega, F i omega ∂volume ≤ B) :
    (∫ omega, Real.log (∑ i, Real.exp (a i + F i omega)) ∂volume) ≤
      B + Real.log (Fintype.card I : ℝ) +
        ∫ omega, Finset.univ.sup' Finset.univ_nonempty
          (fun i => F i omega - ∫ eta, F i eta ∂volume) ∂volume := by
  let X : I → Omega → ℝ := fun i omega =>
    F i omega - ∫ eta, F i eta ∂volume
  let M : Omega → ℝ := fun omega =>
    Finset.univ.sup' Finset.univ_nonempty fun i => X i omega
  have hX (i : I) : Integrable (X i) := (hF i).sub (integrable_const _)
  have hM : Integrable M := by
    have hsup : Integrable (Finset.univ.sup' Finset.univ_nonempty fun i => X i) := by
      exact Finset.sup'_induction Finset.univ_nonempty (fun i => X i)
        (p := fun f : Omega → ℝ => Integrable f)
        (fun _ hf _ hg => hf.sup hg) (fun i _ => hX i)
    refine hsup.congr ?_
    filter_upwards [] with omega
    exact Finset.sup'_apply Finset.univ_nonempty (fun i => X i) omega
  have hlog : Integrable (fun omega =>
      Real.log (∑ i, Real.exp (a i + F i omega))) := by
    apply integrable_log_sum_exp (fun i omega => a i + F i omega)
    intro i
    exact (integrable_const _).add (hF i)
  have hrhs : Integrable (fun omega =>
      B + Real.log (Fintype.card I : ℝ) + M omega) :=
    (integrable_const _).add hM
  have hpoint (omega : Omega) :
      Real.log (∑ i, Real.exp (a i + F i omega)) ≤
        B + Real.log (Fintype.card I : ℝ) + M omega := by
    have hterm (i : I) : a i + F i omega ≤ B + M omega := by
      have hi : X i omega ≤ M omega :=
        Finset.le_sup' (fun i => X i omega) (Finset.mem_univ i)
      dsimp [X] at hi
      linarith [hB i]
    have hsum : (∑ i, Real.exp (a i + F i omega)) ≤
        (Fintype.card I : ℝ) * Real.exp (B + M omega) := by
      calc
        _ ≤ ∑ _i : I, Real.exp (B + M omega) :=
          Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (hterm i)
        _ = _ := by simp
    have hsumpos : 0 < ∑ i, Real.exp (a i + F i omega) :=
      Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    have hcardpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
    have h := Real.log_le_log hsumpos hsum
    rw [Real.log_mul hcardpos.ne' (Real.exp_ne_zero _), Real.log_exp] at h
    linarith
  calc
    (∫ omega, Real.log (∑ i, Real.exp (a i + F i omega)) ∂volume) ≤
        ∫ omega, B + Real.log (Fintype.card I : ℝ) + M omega ∂volume :=
      integral_mono hlog hrhs hpoint
    _ = B + Real.log (Fintype.card I : ℝ) + ∫ omega, M omega ∂volume := by
      rw [integral_add (integrable_const _) hM]
      simp
    _ = _ := rfl

private lemma fullPath_eval_integrable
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q s : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (sigma : SpinGlass.Config N) :
    Integrable (fun omega => fullPathHamiltonian path s omega sigma) := by
  have hU := (show HasGaussianLaw path.sk.U volume from by
      -- The public law bridge guarantees measurability and Gaussian moments.
      exact SpinGlass.AT.gaussianHilbert_hasGaussianLaw path.sk.hU)
  have hV := (show HasGaussianLaw path.simple.V volume from by
      exact SpinGlass.AT.gaussianHilbert_hasGaussianLaw path.simple.hV)
  have hUeval : Integrable (fun omega => path.sk.U omega sigma) := by
    simpa using (hU.map_fun (SpinGlass.evalCLM (N := N) sigma)).integrable
  have hVeval : Integrable (fun omega => path.simple.V omega sigma) := by
    simpa using (hV.map_fun (SpinGlass.evalCLM (N := N) sigma)).integrable
  change Integrable (fun omega =>
    Real.sqrt s * path.sk.U omega sigma +
      Real.sqrt (1 - s) * path.simple.V omega sigma +
        SpinGlass.magnetic_field_vector N h sigma)
  exact ((hUeval.const_mul _).add (hVeval.const_mul _)).add (integrable_const _)

private lemma constrained_log_integrable
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} {beta h q s v : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (hv : v ∈ attainableOverlaps N) :
    Integrable (fun omega => Real.log
      (constrainedPartition (fullPathHamiltonian path s omega) v)) := by
  classical
  let P := {p : SpinGlass.Config N × SpinGlass.Config N //
    SpinGlass.overlap N p.1 p.2 = v}
  rw [attainableOverlaps, Finset.mem_image] at hv
  obtain ⟨p, _hp, hpv⟩ := hv
  letI : Nonempty P := ⟨⟨p, hpv⟩⟩
  let F : P → Omega → ℝ := fun p omega =>
    -(fullPathHamiltonian path s omega p.1.1 +
      fullPathHamiltonian path s omega p.1.2)
  have hF (p : P) : Integrable (F p) :=
    ((fullPath_eval_integrable path p.1.1).add
      (fullPath_eval_integrable path p.1.2)).neg
  have hint := integrable_log_sum_exp F hF
  convert hint using 1
  funext omega
  congr 1
  unfold constrainedPartition
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
    SpinGlass.overlap N p.1 p.2 = v)
    (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.overlap N p.1 p.2 = v) (by simp)]

/-- Every overlap attained by two configurations lies in `[-1,1]`. -/
theorem attainableOverlap_mem_Icc
    {N : ℕ} (hN : 0 < N) {v : ℝ}
    (hv : v ∈ attainableOverlaps N) : v ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  rw [attainableOverlaps, Finset.mem_image] at hv
  obtain ⟨p, _hp, rfl⟩ := hv
  have hterm (i : Fin N) :
      -1 ≤ SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i ∧
        SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i ≤ 1 := by
    cases h1 : p.1 i <;> cases h2 : p.2 i <;>
      simp [SpinGlass.spin, h1, h2]
  have hlo : -(N : ℝ) ≤
      ∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i := by
    calc
      -(N : ℝ) = ∑ _i : Fin N, (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => (hterm i).1
  have hhi : (∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i) ≤
      (N : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hterm i).2
      _ = (N : ℝ) := by simp
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold SpinGlass.overlap
  have hinv : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNr
  constructor
  · calc
      (-1 : ℝ) = (1 / (N : ℝ)) * (-(N : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hinv.le
  · calc
      (1 / (N : ℝ)) *
          ∑ i, SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i ≤
          (1 / (N : ℝ)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hhi hinv.le
      _ = 1 := by field_simp

private lemma rsPathValue_nonneg (beta h q : ℝ) (s : Set.Icc (0 : ℝ) 1) :
    0 ≤ rsPathValue beta h q s.1 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hint : 0 ≤ standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + beta * Real.sqrt q * z))) := by
    unfold standardGaussianExpectation
    exact integral_nonneg fun z => Real.log_nonneg (Real.one_le_cosh _)
  have hcorr : 0 ≤ s.1 * beta ^ 2 / 4 * (1 - q) ^ 2 :=
    mul_nonneg
      (div_nonneg (mul_nonneg s.2.1 (sq_nonneg beta)) (by norm_num))
      (sq_nonneg (1 - q))
  unfold rsPathValue
  linarith

/-- A uniform sublinear bound for the quadratically coupled pressure along
the replica-symmetric smart path, including the degenerate case `N = 0`. -/
theorem quadraticCoupledPressure_sublinear
    {Omega : Type*} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ rho0 > 0, ∃ C > 0,
      ∀ {N : ℕ},
      ∀ {beta h : ℝ}, (beta, h) ∈ K →
      ∀ s : Set.Icc (0 : ℝ) 1,
      ∀ path : RSSmartPathDisorder Omega N beta h (rsQ beta h),
        quadraticCoupledPressure path s.1 rho0 ≤
          rsPathValue beta h (rsQ beta h) s.1 +
            C * Real.sqrt
              (Real.log ((N : ℝ) + 1) / (N : ℝ)) := by
  obtain ⟨c, hc, hgap⟩ := gtFunctional_uniform_quadratic_gap data
  refine ⟨c, hc, 1 + 2 * data.βmax, by nlinarith [data.βmax_pos], ?_⟩
  intro N beta h hp s path
  by_cases hN : N = 0
  · subst N
    simp only [quadraticCoupledPressure, Nat.cast_zero, mul_zero, div_zero,
      zero_mul, zero_add, Real.log_one, Real.sqrt_zero]
    simpa using rsPathValue_nonneg beta h (rsQ beta h) s
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hβ : 0 < beta := by
      simpa using data.β_pos (beta, h) hp
    have hh : 0 < h := by
      simpa using data.h_pos (beta, h) hp
    let I := {v : ℝ // v ∈ attainableOverlaps N}
    let q := rsQ beta h
    have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [q]
      exact ⟨rsQ_pos hβ hh, rsQ_lt_one hβ hh⟩
    let P := rsPathValue beta h q s.1
    let F : I → Omega → ℝ := fun v omega =>
      Real.log (constrainedPartition
        (fullPathHamiltonian path s.1 omega) v.1)
    let a : I → ℝ := fun v => c * (N : ℝ) / 2 * (v.1 - q) ^ 2
    have hF (v : I) : Integrable (F v) := constrained_log_integrable path v.2
    have hB (v : I) :
        a v + ∫ omega, F v omega ∂volume ≤ 2 * (N : ℝ) * P := by
      have hvIcc : v.1 ∈ Set.Icc (-1 : ℝ) 1 :=
        attainableOverlap_mem_Icc hNpos v.2
      obtain ⟨lam, hlam, hflat⟩ :=
        hgap hp rfl s.2 hvIcc
      have hgt := twoReplica_GT_bound path lam hNpos hβ hh hq s.2 v.2
      have hcombined := hgt.trans hflat
      unfold expectedConstrainedFreeEnergy at hcombined
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
      have hscaled := mul_le_mul_of_nonneg_left hcombined hNr.le
      have hmean :
          (∫ omega, F v omega ∂volume) ≤
            (N : ℝ) * (2 * P - c * (v.1 - q) ^ 2) := by
        calc
          (∫ omega, F v omega ∂volume) =
              (N : ℝ) * (1 / (N : ℝ) *
                ∫ omega, F v omega ∂volume) := by field_simp
          _ ≤ (N : ℝ) * (2 * P - c * (v.1 - q) ^ 2) := by
            simpa [F, P, q] using hscaled
      dsimp [a]
      nlinarith [sq_nonneg (v.1 - q), mul_pos hNr hc]
    have hsum := integral_log_sum_exp_le F a (2 * (N : ℝ) * P) hF hB
    have hpartition (omega : Omega) :
        Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q c) =
          Real.log (∑ v : I, Real.exp (a v + F v omega)) := by
      congr 1
      rw [quadraticCoupledPartition_eq_sum_constrained]
      symm
      rw [Finset.sum_subtype (p := fun v : ℝ => v ∈ attainableOverlaps N)
        (attainableOverlaps N) (by simp)]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp [a, F, q]
      rw [Real.exp_add, Real.exp_log
        (constrainedPartition_pos_of_attainable _ v.2)]
    have hsum' :
        (∫ omega, Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q c) ∂volume) ≤
          2 * (N : ℝ) * P + Real.log (Fintype.card I : ℝ) +
            ∫ omega, Finset.univ.sup' Finset.univ_nonempty
              (fun v : I => F v omega - ∫ eta, F v eta ∂volume) ∂volume := by
      simpa only [hpartition] using hsum
    have hmax := coupled_log_partition_gaussian_max_path
      data N beta h s hp path
    have hmax' :
        (∫ omega, Finset.univ.sup' Finset.univ_nonempty
          (fun v : I => F v omega - ∫ eta, F v eta ∂volume) ∂volume) ≤
          2 * data.βmax * Real.sqrt N *
            Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
      simpa [I, F] using hmax
    have hcard : Fintype.card I ≤ N + 1 := by
      simpa [I] using card_attainableOverlaps_le N
    have hcardpos : 0 < (Fintype.card I : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hcardreal : (Fintype.card I : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast hcard
    have hlogcard : Real.log (Fintype.card I : ℝ) ≤
        Real.log ((N : ℝ) + 1) :=
      Real.log_le_log hcardpos hcardreal
    have htotal :
        (∫ omega, Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q c) ∂volume) ≤
          2 * (N : ℝ) * P + Real.log ((N : ℝ) + 1) +
            2 * data.βmax * Real.sqrt N *
              Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
      linarith
    let n : ℝ := N
    let ell : ℝ := Real.log (n + 1)
    let x : ℝ := ell / n
    let r : ℝ := Real.sqrt x
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast hNpos
    have hn1 : 1 ≤ n + 1 := by linarith
    have hell : 0 ≤ ell := Real.log_nonneg hn1
    have hell_le : ell ≤ n := by
      have := Real.log_le_sub_one_of_pos (show 0 < n + 1 by linarith)
      dsimp [ell]
      linarith
    have hx : 0 ≤ x := div_nonneg hell hn.le
    have hx_le : x ≤ 1 := (div_le_one hn).2 hell_le
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hr_sq : r ^ 2 = x := by
      dsimp [r]
      exact Real.sq_sqrt hx
    have hx_sqrt : x ≤ r := by
      nlinarith
    have hsqrt_two : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    have hsqrt_product : Real.sqrt (2 * ell) ≤ 2 * Real.sqrt ell := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right hsqrt_two (Real.sqrt_nonneg ell)
    have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hsqrtn_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
    have hratio : Real.sqrt n * Real.sqrt ell / n = r := by
      have hrform : r = Real.sqrt ell / Real.sqrt n := by
        dsimp [r, x]
        rw [Real.sqrt_div hell]
      rw [hrform]
      field_simp [hn.ne', hsqrtn.ne']
      rw [hsqrtn_sq]
      ring
    have hlog_error : (1 / (2 * n)) * ell ≤ r := by
      have heq : (1 / (2 * n)) * ell = x / 2 := by
        dsimp [x]
        field_simp [hn.ne']
      rw [heq]
      linarith
    have hgaussian_error :
        (1 / (2 * n)) *
            (2 * data.βmax * Real.sqrt n * Real.sqrt (2 * ell)) ≤
          2 * data.βmax * r := by
      calc
        (1 / (2 * n)) *
            (2 * data.βmax * Real.sqrt n * Real.sqrt (2 * ell)) ≤
            (1 / (2 * n)) *
              (2 * data.βmax * Real.sqrt n *
                (2 * Real.sqrt ell)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left hsqrt_product
            exact mul_nonneg
              (mul_nonneg (by norm_num) data.βmax_pos.le)
              (Real.sqrt_nonneg n)
          · positivity
        _ = 2 * data.βmax * r := by
          rw [← hratio]
          field_simp [hn.ne']
    have herror :
        (1 / (2 * n)) *
            (ell + 2 * data.βmax * Real.sqrt n * Real.sqrt (2 * ell)) ≤
          (1 + 2 * data.βmax) * r := by
      rw [mul_add]
      nlinarith
    unfold quadraticCoupledPressure
    change (1 / (2 * n)) *
        ∫ omega, Real.log (quadraticCoupledPartition
          (fullPathHamiltonian path s.1 omega) q c) ∂volume ≤
        P + (1 + 2 * data.βmax) * r
    calc
      (1 / (2 * n)) *
          ∫ omega, Real.log (quadraticCoupledPartition
            (fullPathHamiltonian path s.1 omega) q c) ∂volume ≤
          (1 / (2 * n)) *
            (2 * n * P + ell +
              2 * data.βmax * Real.sqrt n * Real.sqrt (2 * ell)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [n, ell, q, P] using htotal
        · positivity
      _ = P + (1 / (2 * n)) *
            (ell + 2 * data.βmax * Real.sqrt n * Real.sqrt (2 * ell)) := by
        field_simp [hn.ne']
        ring
      _ ≤ P + (1 + 2 * data.βmax) * r := by
        simpa [add_comm] using add_le_add_left herror P

/-- A four-replica observable depending only on the first pair has the same
expectation as the corresponding two-replica observable. -/
theorem fourReplica_firstPair_eq_two
    {N : ℕ} (H : SpinGlass.EnergySpace N) (q : ℝ) (f : ℝ → ℝ) :
    replicaGibbsAverage H
        (fun σs : Replicas N 4 => f (centeredOverlap q σs 0 1)) =
      SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
        (fun σs => f (SpinGlass.overlap N (σs 0) (σs 1) - q)) := by
  classical
  let e0a := Equiv.prodPiEquivSumPi
    (fun _ : Fin 2 => SpinGlass.Config N)
    (fun _ : Fin 2 => SpinGlass.Config N)
  let e0b : ((i : Fin 2 ⊕ Fin 2) →
      Sum.elim (fun _ : Fin 2 => SpinGlass.Config N)
        (fun _ : Fin 2 => SpinGlass.Config N) i) ≃
      (Fin 2 ⊕ Fin 2 → SpinGlass.Config N) :=
    Equiv.piCongrRight fun i => by cases i <;> exact Equiv.refl _
  let e0 : (Replicas N 2 × Replicas N 2) ≃
      (Fin 2 ⊕ Fin 2 → SpinGlass.Config N) := e0a.trans e0b
  let e1 : (Fin 2 ⊕ Fin 2 → SpinGlass.Config N) ≃ Replicas N 4 :=
    Equiv.piCongrLeft (fun _ : Fin 4 => SpinGlass.Config N) finSumFinEquiv
  let e := e0.trans e1
  have he0 (p : Replicas N 2 × Replicas N 2) : e p 0 = p.1 0 := by
    simp [e, e0, e0a, e0b, e1, Equiv.piCongrLeft_apply,
      Equiv.piCongrRight_apply, Equiv.sumPiEquivProdPi,
      finSumFinEquiv, Fin.addCases]
    rfl
  have he1 (p : Replicas N 2 × Replicas N 2) : e p 1 = p.1 1 := by
    simp [e, e0, e0a, e0b, e1, Equiv.piCongrLeft_apply,
      Equiv.piCongrRight_apply, Equiv.sumPiEquivProdPi,
      finSumFinEquiv, Fin.addCases]
    rfl
  have he2 (p : Replicas N 2 × Replicas N 2) : e p 2 = p.2 0 := by
    simp [e, e0, e0a, e0b, e1, Equiv.piCongrLeft_apply,
      Equiv.piCongrRight_apply, Equiv.sumPiEquivProdPi,
      finSumFinEquiv, Fin.addCases]
    rfl
  have he3 (p : Replicas N 2 × Replicas N 2) : e p 3 = p.2 1 := by
    simp [e, e0, e0a, e0b, e1, Equiv.piCongrLeft_apply,
      Equiv.piCongrRight_apply, Equiv.sumPiEquivProdPi,
      finSumFinEquiv, Fin.addCases]
    rfl
  unfold replicaGibbsAverage SpinGlass.gibbs_average_n_det
  rw [show (∑ σs : Replicas N 4,
      (∏ a, SpinGlass.gibbs_pmf N H (σs a)) *
        f (centeredOverlap q σs 0 1)) =
      ∑ p : Replicas N 2 × Replicas N 2,
        (∏ a, SpinGlass.gibbs_pmf N H (e p a)) *
          f (centeredOverlap q (e p) 0 1) by
    symm
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.prod_univ_four, he0, he1, he2, he3]
  simp_rw [centeredOverlap, replicaOverlap, he0, he1]
  have hsum :
      (∑ τs : Replicas N 2,
        SpinGlass.gibbs_pmf N H (τs 0) *
          SpinGlass.gibbs_pmf N H (τs 1)) = 1 := by
    simpa [Fin.prod_univ_two] using
      (SpinGlass.sum_prod_gibbs_pmf_eq_one (N := N) (n := 2) H)
  apply Finset.sum_congr rfl
  intro σs _
  calc
    (∑ τs : Replicas N 2,
        SpinGlass.gibbs_pmf N H (σs 0) * SpinGlass.gibbs_pmf N H (σs 1) *
          SpinGlass.gibbs_pmf N H (τs 0) * SpinGlass.gibbs_pmf N H (τs 1) *
            f (SpinGlass.overlap N (σs 0) (σs 1) - q)) =
        (f (SpinGlass.overlap N (σs 0) (σs 1) - q) *
          ∏ l, SpinGlass.gibbs_pmf N H (σs l)) *
          ∑ τs : Replicas N 2,
            SpinGlass.gibbs_pmf N H (τs 0) *
              SpinGlass.gibbs_pmf N H (τs 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τs _
      simp only [Fin.prod_univ_two]
      ring
    _ = f (SpinGlass.overlap N (σs 0) (σs 1) - q) *
          ∏ l, SpinGlass.gibbs_pmf N H (σs l) := by rw [hsum, mul_one]

/-- The four-replica definition of `A` agrees with the two-replica smart-path
variance. -/
theorem A_eq_overlapVariance
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q) (t : ℝ) :
    A path t =
      SpinGlass.GeneralizedLatala.overlapVariance
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) t := by
  unfold A quenchedReplicaAverage
    SpinGlass.GeneralizedLatala.overlapVariance SpinGlass.nu
    SpinGlass.gibbs_average_n
  apply integral_congr_ae
  filter_upwards with omega
  change replicaGibbsAverage (fullPathHamiltonian path t omega)
      (fun σs : Replicas N 4 => centeredOverlap q σs 0 1 ^ 2) =
    SpinGlass.gibbs_average_n_det (N := N) (n := 2)
      (fullPathHamiltonian path t omega)
      (fun σs => (SpinGlass.overlap N (σs 0) (σs 1) - q) ^ 2)
  exact fourReplica_firstPair_eq_two (fullPathHamiltonian path t omega) q
    (fun x => x ^ 2)

private lemma rsFreeEnergyGap_hasDerivAt
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (rsFreeEnergyGap path) (beta ^ 2 / 4 * A path t) t := by
  have hrs : HasDerivAt (rsPathValue beta h q)
      (beta ^ 2 / 4 * (1 - q) ^ 2) t := by
    unfold rsPathValue
    let c := Real.log 2 + standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + beta * Real.sqrt q * z)))
    have hraw := (((hasDerivAt_id t).mul_const (beta ^ 2 / 4)).mul_const
      ((1 - q) ^ 2)).const_add c
    rw [show (fun s : ℝ => c + s * beta ^ 2 / 4 * (1 - q) ^ 2) =
        (fun s : ℝ => c + (s * (beta ^ 2 / 4)) * (1 - q) ^ 2) by
      funext s
      ring]
    exact hraw.congr_deriv (by ring)
  have hp := SpinGlass.GeneralizedLatala.pressure_derivative
    (N := N) (β := beta) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) hN path.independent ht
  have heq : pathFreeEnergy path =
      SpinGlass.GeneralizedLatala.interpolatedPressure
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) := by
    rfl
  rw [A_eq_overlapVariance (path := path) t]
  change HasDerivAt
    (fun s => rsPathValue beta h q s - pathFreeEnergy path s) _ t
  rw [heq]
  exact (hrs.sub hp).congr_deriv (by ring)

private lemma rsFreeEnergyGap_continuousOn
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q) :
    ContinuousOn (rsFreeEnergyGap path) (Set.Icc (0 : ℝ) 1) := by
  have heq : pathFreeEnergy path =
      SpinGlass.GeneralizedLatala.interpolatedPressure
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) := by
    rfl
  change ContinuousOn
    (fun s => rsPathValue beta h q s - pathFreeEnergy path s) _
  rw [heq]
  apply ContinuousOn.sub
  · unfold rsPathValue
    fun_prop
  · exact SpinGlass.GeneralizedLatala.interpolatedPressure_continuousOn_Icc
      (N := N) (β := beta) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple)

private lemma rsFreeEnergyGap_zero
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (hN : 0 < N) (hq : 0 ≤ q) :
    rsFreeEnergyGap path 0 = 0 := by
  have hp := SpinGlass.GeneralizedLatala.interpolatedPressure_zero
    (N := N) (β := beta) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) hN hq
  have heq : pathFreeEnergy path =
      SpinGlass.GeneralizedLatala.interpolatedPressure
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) := by
    rfl
  rw [rsFreeEnergyGap, heq, hp]
  unfold rsPathValue SpinGlass.AT.standardGaussianExpectation
    SpinGlass.GeneralizedLatala.standardGaussianExpectation
  ring

private lemma quadraticCoupledPartition_eq_tilted
    {N : ℕ} (H : SpinGlass.EnergySpace N) (q rho : ℝ) :
    quadraticCoupledPartition H q rho =
      SpinGlass.Z N H ^ 2 *
        SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => Real.exp
            ((rho / 2) * (N : ℝ) *
              SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs)) := by
  classical
  unfold quadraticCoupledPartition SpinGlass.gibbs_average_n_det
  rw [Finset.mul_sum]
  rw [show (∑ σs : SpinGlass.ReplicaSpace N 2,
      SpinGlass.Z N H ^ 2 *
        (Real.exp
          ((rho / 2) * (N : ℝ) *
            SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs) *
          ∏ l, SpinGlass.gibbs_pmf N H (σs l))) =
      ∑ p : SpinGlass.Config N × SpinGlass.Config N,
        SpinGlass.Z N H ^ 2 *
          (Real.exp
            ((rho / 2) * (N : ℝ) *
              SpinGlass.GeneralizedLatala.centeredOverlapSq N q
                ((finTwoArrowEquiv (SpinGlass.Config N)).symm p)) *
            ∏ l, SpinGlass.gibbs_pmf N H
              ((finTwoArrowEquiv (SpinGlass.Config N)).symm p l)) by
    exact Fintype.sum_equiv (finTwoArrowEquiv (SpinGlass.Config N)) _ _
      (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro p _
  have he0 : (finTwoArrowEquiv (SpinGlass.Config N)).symm p 0 = p.1 := by rfl
  have he1 : (finTwoArrowEquiv (SpinGlass.Config N)).symm p 1 = p.2 := by rfl
  simp only [Fin.prod_univ_two,
    SpinGlass.GeneralizedLatala.centeredOverlapSq, SpinGlass.gibbs_pmf]
  rw [he0, he1]
  have hZ : SpinGlass.Z N H ≠ 0 := ne_of_gt (SpinGlass.Z_pos N H)
  field_simp [hZ]
  rw [← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  ring

private lemma normalized_log_quadraticCoupledPartition_eq
    {N : ℕ} (hN : 0 < N) (H : SpinGlass.EnergySpace N) (q rho : ℝ) :
    (1 / (2 * (N : ℝ))) * Real.log (quadraticCoupledPartition H q rho) =
      SpinGlass.GeneralizedLatala.coupledFreeEnergyDet
        (N := N) (q := q) H rho := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  rw [quadraticCoupledPartition_eq_tilted]
  have hZ : SpinGlass.Z N H ≠ 0 := ne_of_gt (SpinGlass.Z_pos N H)
  have htilt : SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
      (fun σs => Real.exp
        ((rho / 2) * (N : ℝ) *
          SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs)) ≠ 0 := by
    exact ne_of_gt
      (SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H (rho / 2))
  rw [Real.log_mul (pow_ne_zero 2 hZ) htilt, pow_two,
    Real.log_mul hZ hZ]
  unfold SpinGlass.GeneralizedLatala.coupledFreeEnergyDet
    SpinGlass.free_energy_density
    SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNr]
  ring

private lemma quadraticCoupledPressure_eq_coupledFreeEnergy
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (hN : 0 < N) (t rho : ℝ) :
    quadraticCoupledPressure path t rho =
      SpinGlass.GeneralizedLatala.coupledFreeEnergy
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) t rho := by
  rw [SpinGlass.GeneralizedLatala.coupledFreeEnergy_eq_integral_det]
  unfold quadraticCoupledPressure
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with omega
  change (1 / (2 * (N : ℝ))) *
      Real.log (quadraticCoupledPartition
        (fullPathHamiltonian path t omega) q rho) =
    SpinGlass.GeneralizedLatala.coupledFreeEnergyDet
      (N := N) (q := q) (fullPathHamiltonian path t omega) rho
  exact normalized_log_quadraticCoupledPartition_eq hN _ q rho

private lemma overlap_le_coupledPressure_gap
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {N : ℕ} [NeZero N] {beta h q : ℝ}
    (path : RSSmartPathDisorder Omega N beta h q)
    (hN : 0 < N) {rho : ℝ} (hrho : 0 ≤ rho) (t : ℝ) :
    rho / 4 * A path t ≤
      quadraticCoupledPressure path t rho - pathFreeEnergy path t := by
  have hj := SpinGlass.GeneralizedLatala.scaled_overlapVariance_le_logQuadraticMoment
    (N := N) (β := beta) (h := h) (q := q)
    (sk := path.sk) (sim := path.simple) (rho / 2) (by positivity) t
  rw [← A_eq_overlapVariance (path := path) t] at hj
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hscaled := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ 1 / (2 * (N : ℝ)) by positivity)
  rw [quadraticCoupledPressure_eq_coupledFreeEnergy path hN]
  have heq : pathFreeEnergy path =
      SpinGlass.GeneralizedLatala.interpolatedPressure
        (N := N) (β := beta) (h := h) (q := q)
        (sk := path.sk) (sim := path.simple) := by
    rfl
  rw [heq]
  simp only [SpinGlass.GeneralizedLatala.coupledFreeEnergy, add_sub_cancel_left]
  change rho / 4 * A path t ≤
    SpinGlass.GeneralizedLatala.coupledExcess
      (N := N) (β := beta) (h := h) (q := q)
      (sk := path.sk) (sim := path.simple) t rho
  unfold SpinGlass.GeneralizedLatala.coupledExcess
    SpinGlass.GeneralizedLatala.physicalLogQuadraticMoment
  calc
    rho / 4 * A path t =
        (1 / (2 * (N : ℝ))) * ((rho / 2) * (N : ℝ) * A path t) := by
      field_simp
      ring
    _ ≤ _ := hscaled

/-- Lemma 3.2: weak concentration along the replica-symmetric smart path. -/
theorem preconcentration
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) :
    ∃ C > 0,
      ∀ {N : ℕ}, 0 < N →
      ∀ {beta h : ℝ}, (beta, h) ∈ K →
      ∀ s : Set.Icc (0 : ℝ) 1,
      ∀ path : RSSmartPathDisorder Omega N beta h (rsQ beta h),
        rsFreeEnergyGap path s.1 ≤
            C * Real.sqrt
              (Real.log ((N : ℝ) + 1) / (N : ℝ)) ∧
        A path s.1 ≤
            C * Real.sqrt
              (Real.log ((N : ℝ) + 1) / (N : ℝ)) := by
  obtain ⟨rho, hrho, C0, hC0, hquad⟩ :=
    quadraticCoupledPressure_sublinear (Omega := Omega) data
  let kmax : ℝ := data.βmax ^ 2 / rho
  let Cstar : ℝ := C0 * Real.exp kmax * (1 + 8 / rho) + 1
  have hkmax : 0 ≤ kmax := by
    dsimp [kmax]
    positivity
  have hCstar : 0 < Cstar := by
    dsimp [Cstar]
    positivity
  refine ⟨Cstar, hCstar, ?_⟩
  intro N hN beta h hp s path
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let r : ℝ := Real.sqrt (Real.log ((N : ℝ) + 1) / (N : ℝ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have herror : 0 ≤ C0 * r := mul_nonneg hC0.le hr
  have hbeta : 0 < beta := data.β_pos (beta, h) hp
  have hbetaMax : beta ≤ data.βmax := data.β_bound (beta, h) hp
  have hbetaSq : beta ^ 2 ≤ data.βmax ^ 2 := by nlinarith
  have hAcontrol : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      A path t ≤ 4 / rho * (rsFreeEnergyGap path t + C0 * r) := by
    intro t ht
    have hj := overlap_le_coupledPressure_gap path hN hrho.le t
    have hq := hquad hp ⟨t, ht⟩ path
    unfold rsFreeEnergyGap
    have hcombined : rho / 4 * A path t ≤
        rsPathValue beta h (rsQ beta h) t - pathFreeEnergy path t + C0 * r := by
      linarith
    calc
      A path t = 4 / rho * (rho / 4 * A path t) := by field_simp
      _ ≤ 4 / rho *
          (rsPathValue beta h (rsQ beta h) t - pathFreeEnergy path t + C0 * r) := by
        exact mul_le_mul_of_nonneg_left hcombined (by positivity)
  have hcont : ContinuousOn
      (fun t => rsFreeEnergyGap path t + C0 * r)
      (Set.Icc (0 : ℝ) s.1) := by
    apply ContinuousOn.add
    · exact (rsFreeEnergyGap_continuousOn path).mono (by
        intro t ht
        exact ⟨ht.1, ht.2.trans s.2.2⟩)
    · fun_prop
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) s.1, ∃ d : ℝ,
      HasDerivAt (fun x => rsFreeEnergyGap path x + C0 * r) d t ∧
        d ≤ (beta ^ 2 / rho) *
          (rsFreeEnergyGap path t + C0 * r) := by
    intro t ht
    have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_le s.2.2⟩
    let d : ℝ := beta ^ 2 / 4 * A path t
    refine ⟨d, ?_, ?_⟩
    · exact (rsFreeEnergyGap_hasDerivAt path hN ht01).add_const (C0 * r)
    · have hAt := hAcontrol t ⟨ht.1.le, ht01.2.le⟩
      have hmul := mul_le_mul_of_nonneg_left hAt
        (show 0 ≤ beta ^ 2 / 4 by positivity)
      dsimp [d]
      calc
        beta ^ 2 / 4 * A path t ≤
            beta ^ 2 / 4 * (4 / rho *
              (rsFreeEnergyGap path t + C0 * r)) := hmul
        _ = beta ^ 2 / rho *
              (rsFreeEnergyGap path t + C0 * r) := by field_simp
  have hgronwall := SpinGlass.GeneralizedLatala.gronwall_le_endpoint
    (f := fun t => rsFreeEnergyGap path t + C0 * r)
    (a := beta ^ 2 / rho) (u := s.1) s.2.1 hcont hderiv
  rw [rsFreeEnergyGap_zero path hN (rsQ_mem_Icc beta h).1,
    zero_add] at hgronwall
  have hk : beta ^ 2 / rho * s.1 ≤ kmax := by
    dsimp [kmax]
    have hsMul : beta ^ 2 * s.1 ≤ data.βmax ^ 2 := by
      calc
        beta ^ 2 * s.1 ≤ beta ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left s.2.2 (sq_nonneg beta)
        _ ≤ data.βmax ^ 2 := by simpa using hbetaSq
    calc
      beta ^ 2 / rho * s.1 = beta ^ 2 * s.1 / rho := by field_simp
      _ ≤ data.βmax ^ 2 / rho :=
        (div_le_div_iff_of_pos_right hrho).2 hsMul
  have hexp : Real.exp (beta ^ 2 / rho * s.1) ≤ Real.exp kmax :=
    Real.exp_le_exp.mpr hk
  have hgronwall' : rsFreeEnergyGap path s.1 + C0 * r ≤
      Real.exp kmax * (C0 * r) := by
    exact hgronwall.trans
      (mul_le_mul_of_nonneg_right hexp herror)
  have hgap : rsFreeEnergyGap path s.1 ≤
      C0 * Real.exp kmax * r := by
    have hexp0 : 0 ≤ Real.exp kmax := Real.exp_nonneg _
    nlinarith
  have hAs := hAcontrol s.1 s.2
  have hArough : A path s.1 ≤
      (8 / rho) * (C0 * Real.exp kmax) * r := by
    have hexp1 : 1 ≤ Real.exp kmax := Real.one_le_exp hkmax
    have hsum : rsFreeEnergyGap path s.1 + C0 * r ≤
        2 * (C0 * Real.exp kmax * r) := by
      have hC0r : C0 * r ≤ C0 * Real.exp kmax * r := by
        calc
          C0 * r = C0 * 1 * r := by ring
          _ ≤ C0 * Real.exp kmax * r := by gcongr
      linarith
    calc
      A path s.1 ≤ 4 / rho *
          (rsFreeEnergyGap path s.1 + C0 * r) := hAs
      _ ≤ 4 / rho * (2 * (C0 * Real.exp kmax * r)) := by
        gcongr
      _ = (8 / rho) * (C0 * Real.exp kmax) * r := by ring
  have hgapCoeff : C0 * Real.exp kmax ≤ Cstar := by
    dsimp [Cstar]
    have h8 : 0 ≤ 8 / rho := by positivity
    nlinarith [mul_nonneg (mul_nonneg hC0.le (Real.exp_nonneg kmax)) h8]
  have hACoeff : (8 / rho) * (C0 * Real.exp kmax) ≤ Cstar := by
    dsimp [Cstar]
    have hbase : 0 ≤ C0 * Real.exp kmax :=
      mul_nonneg hC0.le (Real.exp_nonneg _)
    nlinarith [mul_nonneg hbase (show 0 ≤ 8 / rho by positivity)]
  constructor
  · change rsFreeEnergyGap path s.1 ≤ Cstar * r
    exact hgap.trans (mul_le_mul_of_nonneg_right hgapCoeff hr)
  · change A path s.1 ≤ Cstar * r
    exact hArough.trans (mul_le_mul_of_nonneg_right hACoeff hr)

private lemma quadraticCoupled_log_ratio_eq_log_tilted
    {N : ℕ} (hN : 0 < N) (H : SpinGlass.EnergySpace N) (q rho : ℝ) :
    Real.log (quadraticCoupledPartition H q rho) -
        Real.log (quadraticCoupledPartition H q 0) =
      Real.log (SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
        (fun σs => Real.exp
          ((rho / 2) * (N : ℝ) *
            SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs))) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hZ : SpinGlass.Z N H ≠ 0 := ne_of_gt (SpinGlass.Z_pos N H)
  have htilt : SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
      (fun σs => Real.exp
        ((rho / 2) * (N : ℝ) *
          SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs)) ≠ 0 :=
    ne_of_gt (SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet_pos
      (N := N) (q := q) H (rho / 2))
  have hone : SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
      (fun σs => Real.exp (((0 : ℝ) / 2) * (N : ℝ) *
        SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs)) = 1 := by
    simp only [zero_div, zero_mul, Real.exp_zero]
    unfold SpinGlass.gibbs_average_n_det
    simpa using SpinGlass.sum_prod_gibbs_pmf_eq_one
      (N := N) (n := 2) H
  rw [quadraticCoupledPartition_eq_tilted,
    quadraticCoupledPartition_eq_tilted, hone, mul_one,
    Real.log_mul (pow_ne_zero 2 hZ) htilt]
  ring

private lemma gibbs_tail_le_exp_log_ratio
    {N : ℕ} (hN : 0 < N) (H : SpinGlass.EnergySpace N)
    (q rho epsilon : ℝ) (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
        (fun σs => if epsilon ≤
          |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0) ≤
      Real.exp (-(rho * (N : ℝ) / 2 * epsilon ^ 2) +
        (Real.log (quadraticCoupledPartition H q rho) -
          Real.log (quadraticCoupledPartition H q 0))) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let a : ℝ := rho * (N : ℝ) / 2 * epsilon ^ 2
  let W : SpinGlass.ReplicaSpace N 2 → ℝ := fun σs =>
    (rho / 2) * (N : ℝ) *
      SpinGlass.GeneralizedLatala.centeredOverlapSq N q σs
  have hpoint (σs : SpinGlass.ReplicaSpace N 2) :
      (if epsilon ≤ |SpinGlass.overlap N (σs 0) (σs 1) - q|
        then (1 : ℝ) else 0) ≤ Real.exp (-a) * Real.exp (W σs) := by
    split_ifs with htail
    · have hsquare : epsilon ^ 2 ≤
          (SpinGlass.overlap N (σs 0) (σs 1) - q) ^ 2 := by
        have habs := sq_abs (SpinGlass.overlap N (σs 0) (σs 1) - q)
        nlinarith [sq_nonneg
          (|SpinGlass.overlap N (σs 0) (σs 1) - q| - epsilon)]
      have hNr : 0 ≤ (N : ℝ) := by positivity
      have hexponent : 0 ≤ -a + W σs := by
        dsimp [a, W, SpinGlass.GeneralizedLatala.centeredOverlapSq]
        have hfac : 0 ≤ (rho / 2) * (N : ℝ) :=
          mul_nonneg (div_nonneg hrho.le (by norm_num)) hNr
        have hmul := mul_le_mul_of_nonneg_left hsquare hfac
        nlinarith
      rw [← Real.exp_add]
      exact Real.one_le_exp hexponent
    · positivity
  have hweighted :
      SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => if epsilon ≤
            |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0) ≤
        Real.exp (-a) *
          SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
            (fun σs => Real.exp (W σs)) := by
    unfold SpinGlass.gibbs_average_n_det
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σs _
    have hw : 0 ≤ ∏ l, SpinGlass.gibbs_pmf N H (σs l) :=
      Finset.prod_nonneg fun l _ =>
        SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σs l)
    have hp := mul_le_mul_of_nonneg_right (hpoint σs) hw
    simpa [mul_assoc] using hp
  have hlog := quadraticCoupled_log_ratio_eq_log_tilted hN H q rho
  have htiltpos : 0 < SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
      (fun σs => Real.exp (W σs)) := by
    change 0 < SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet
      (N := N) (q := q) H (rho / 2)
    exact SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet_pos
      (N := N) (q := q) H (rho / 2)
  calc
    _ ≤ Real.exp (-a) *
        SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => Real.exp (W σs)) := hweighted
    _ = Real.exp (-a +
        (Real.log (quadraticCoupledPartition H q rho) -
          Real.log (quadraticCoupledPartition H q 0))) := by
      rw [hlog, Real.exp_add, Real.exp_log htiltpos]

private lemma gibbs_tail_mem_Icc
    {N : ℕ} (H : SpinGlass.EnergySpace N) (q epsilon : ℝ) :
    SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
        (fun σs => if epsilon ≤
          |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0) ∈
      Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · unfold SpinGlass.gibbs_average_n_det
    apply Finset.sum_nonneg
    intro σs _
    apply mul_nonneg
    · dsimp
      split_ifs <;> norm_num
    · exact Finset.prod_nonneg fun l _ =>
        SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σs l)
  · calc
      SpinGlass.gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => if epsilon ≤
            |SpinGlass.overlap N (σs 0) (σs 1) - q| then 1 else 0) ≤
          ∑ σs : SpinGlass.ReplicaSpace N 2,
            (1 : ℝ) * ∏ l, SpinGlass.gibbs_pmf N H (σs l) := by
        unfold SpinGlass.gibbs_average_n_det
        apply Finset.sum_le_sum
        intro σs _
        have hw : 0 ≤ ∏ l, SpinGlass.gibbs_pmf N H (σs l) :=
          Finset.prod_nonneg fun l _ =>
            SpinGlass.gibbs_pmf_nonneg (N := N) (H := H) (σs l)
        have hi : (if epsilon ≤
            |SpinGlass.overlap N (σs 0) (σs 1) - q| then (1 : ℝ) else 0) ≤ 1 := by
          split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_right hi hw
      _ = 1 := by
        simpa using SpinGlass.sum_prod_gibbs_pmf_eq_one
          (N := N) (n := 2) H

/-- Exponential tail concentration of the centered two-replica overlap,
uniformly on a compact subset of the strict AT region and along the full
smart path. -/
theorem overlap_tail
    {Omega : Type u} [MeasureSpace Omega]
    [IsProbabilityMeasure (volume : Measure Omega)]
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c > 0, ∃ C > 0,
      ∀ {N : ℕ}, 0 < N →
      ∀ {beta h : ℝ}, (beta, h) ∈ K →
      ∀ s : Set.Icc (0 : ℝ) 1,
      ∀ path : RSSmartPathDisorder Omega N beta h (rsQ beta h),
        SpinGlass.nu
            (N := N) (β := beta) (h := h) (q := rsQ beta h)
            (sk := path.sk) (sim := path.simple) 2 s.1
            (fun σs => if epsilon ≤
              |SpinGlass.overlap N (σs 0) (σs 1) - rsQ beta h|
              then 1 else 0) ≤
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨rho, hrho, Cq, hCq, hquad⟩ :=
    quadraticCoupledPressure_sublinear (Omega := Omega) data
  obtain ⟨Cp, hCp, hpre⟩ := preconcentration (Omega := Omega) data
  let D : ℝ := Cq + Cp
  have hD : 0 < D := add_pos hCq hCp
  let delta : ℝ := rho * epsilon ^ 2 / (16 * D)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hadd : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hratio : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 1) / (N : ℝ))
      atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) (-1 : ℝ) 1 one_ne_zero
    have hcomp := hbase.comp hadd
    convert hcomp using 1
    funext N
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hsqrt : Tendsto
      (fun N : ℕ => Real.sqrt
        (Real.log ((N : ℝ) + 1) / (N : ℝ)))
      atTop (nhds 0) := by
    simpa using hratio.sqrt
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hsqrt) delta hdelta
  let c₁ : ℝ := rho * epsilon ^ 2 / 4
  let c₂ : ℝ := rho ^ 2 * epsilon ^ 4 / (2048 * data.βmax ^ 2)
  let c : ℝ := min c₁ c₂
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    exact div_pos
      (mul_pos (sq_pos_of_pos hrho) (pow_pos hepsilon 4))
      (mul_pos (by norm_num) (sq_pos_of_pos data.βmax_pos))
  have hc : 0 < c := lt_min hc₁ hc₂
  let C : ℝ := 2 * Real.exp (c * (N₀ : ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, hc, C, hC, ?_⟩
  intro N hN beta h hp s path
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let tail : SpinGlass.ReplicaFun N 2 := fun σs =>
    if epsilon ≤
      |SpinGlass.overlap N (σs 0) (σs 1) - rsQ beta h| then 1 else 0
  let G : Omega → ℝ := SpinGlass.gibbs_average_n
    (N := N) (β := beta) (h := h) (q := rsQ beta h)
    (sk := path.sk) (sim := path.simple) 2 s.1 tail
  let Y : Omega → ℝ := fun omega =>
    Real.log (quadraticCoupledPartition
        (fullPathHamiltonian path s.1 omega) (rsQ beta h) rho) -
      Real.log (quadraticCoupledPartition
        (fullPathHamiltonian path s.1 omega) (rsQ beta h) 0)
  let a : ℝ := rho * (N : ℝ) / 2 * epsilon ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hGint : Integrable G := by
    exact SpinGlass.integrable_gibbs_average_n
      (N := N) (β := beta) (h := h) (q := rsQ beta h)
      (sk := path.sk) (sim := path.simple) (n := 2) (t := s.1) (f := tail)
  have hGbounds (omega : Omega) : G omega ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [G, tail, SpinGlass.gibbs_average_n, SpinGlass.H_t,
      SpinGlass.H_gauss, SpinGlass.H_field, fullPathHamiltonian] using
      gibbs_tail_mem_Icc (fullPathHamiltonian path s.1 omega)
        (rsQ beta h) epsilon
  by_cases hlarge : N₀ ≤ N
  · have hrsmall : Real.sqrt
        (Real.log ((N : ℝ) + 1) / (N : ℝ)) < delta := by
      have hdist := hN₀ N hlarge
      simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using hdist
    have hquadN := hquad hp s path
    have hpreN := (hpre hN hp s path).1
    let r : ℝ := Real.sqrt
      (Real.log ((N : ℝ) + 1) / (N : ℝ))
    have hexcess : normalizedCouplingExcess path s.1 rho ≤ D * r := by
      unfold normalizedCouplingExcess rsFreeEnergyGap at *
      dsimp [D, r] at *
      linarith
    have hlogpoint (omega : Omega) :
        Y omega = Real.log
          (SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet
            (N := N) (q := rsQ beta h)
            (fullPathHamiltonian path s.1 omega) (rho / 2)) := by
      simpa [Y, SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet] using
        quadraticCoupled_log_ratio_eq_log_tilted hN
          (fullPathHamiltonian path s.1 omega) (rsQ beta h) rho
    have hmoment : (∫ omega, Y omega ∂volume) =
        SpinGlass.GeneralizedLatala.physicalLogQuadraticMoment
          (N := N) (β := beta) (h := h) (q := rsQ beta h)
          (sk := path.sk) (sim := path.simple) s.1 rho := by
      unfold SpinGlass.GeneralizedLatala.physicalLogQuadraticMoment
        SpinGlass.GeneralizedLatala.logQuadraticMoment
        SpinGlass.gibbs_average_n
      apply integral_congr_ae
      filter_upwards with omega
      rw [hlogpoint omega]
      unfold SpinGlass.GeneralizedLatala.tiltedReplicaPartitionDet
      rfl
    have hnormalized : normalizedCouplingExcess path s.1 rho =
        (1 / (2 * (N : ℝ))) *
          SpinGlass.GeneralizedLatala.physicalLogQuadraticMoment
            (N := N) (β := beta) (h := h) (q := rsQ beta h)
            (sk := path.sk) (sim := path.simple) s.1 rho := by
      have hpEq := quadraticCoupledPressure_eq_coupledFreeEnergy path hN s.1 rho
      unfold normalizedCouplingExcess
      rw [hpEq]
      change SpinGlass.GeneralizedLatala.coupledFreeEnergy
          (N := N) (β := beta) (h := h) (q := rsQ beta h)
          (sk := path.sk) (sim := path.simple) s.1 rho -
        SpinGlass.GeneralizedLatala.interpolatedPressure
          (N := N) (β := beta) (h := h) (q := rsQ beta h)
          (sk := path.sk) (sim := path.simple) s.1 = _
      unfold SpinGlass.GeneralizedLatala.coupledFreeEnergy
        SpinGlass.GeneralizedLatala.coupledExcess
      ring
    have hmeanEq : (∫ omega, Y omega ∂volume) =
        2 * (N : ℝ) * normalizedCouplingExcess path s.1 rho := by
      rw [hmoment, hnormalized]
      field_simp
    have hmean : (∫ omega, Y omega ∂volume) ≤ a / 4 := by
      rw [hmeanEq]
      have hscaled := mul_le_mul_of_nonneg_left hexcess
        (show 0 ≤ 2 * (N : ℝ) by positivity)
      have hrdelta : r < delta := by simpa [r] using hrsmall
      have hDr : D * r < D * delta :=
        mul_lt_mul_of_pos_left hrdelta hD
      dsimp [a, delta]
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      exact (calc
        2 * (N : ℝ) * normalizedCouplingExcess path s.1 rho ≤
            2 * (N : ℝ) * (D * r) := hscaled
        _ < 2 * (N : ℝ) * (D * delta) :=
          mul_lt_mul_of_pos_left hDr (mul_pos (by norm_num) hNr)
        _ = rho * (N : ℝ) / 2 * epsilon ^ 2 / 4 := by
          change 2 * (N : ℝ) *
            (D * (rho * epsilon ^ 2 / (16 * D))) = _
          field_simp [hD.ne']
          ring).le
    let bad : Set Omega := {omega | a / 2 < Y omega}
    let badM : Set Omega := toMeasurable volume bad
    have hbadMeas : MeasurableSet badM := measurableSet_toMeasurable _ _
    have hbadSubM : bad ⊆ badM := subset_toMeasurable _ _
    have hbadSubset : bad ⊆
        {omega | Y omega - ∫ eta, Y eta ∂volume > a / 4} := by
      intro omega homega
      dsimp [bad] at homega
      change Y omega - (∫ eta, Y eta ∂volume) > a / 4
      linarith
    have hconc := quadraticCoupled_log_ratio_upper_tail_path
      data hN hp s path rho (a / 4) (by positivity)
    have hbadENN : volume bad ≤ ENNReal.ofReal
        (Real.exp (-(a / 4) ^ 2 /
          (2 * (4 * data.βmax * Real.sqrt N) ^ 2))) :=
      (measure_mono hbadSubset).trans hconc
    have hbadReal : volume.real badM ≤ Real.exp (-c₂ * (N : ℝ)) := by
      have hbadEq : volume badM = volume bad := by
        exact measure_toMeasurable bad
      have htoReal := ENNReal.toReal_mono (by simp) hbadENN
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at htoReal
      rw [measureReal_def, hbadEq]
      convert htoReal using 1
      dsimp [a, c₂]
      congr 1
      have hsq : (4 * data.βmax * Real.sqrt N) ^ 2 =
          16 * data.βmax ^ 2 * (N : ℝ) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt
          (show 0 ≤ (N : ℝ) by positivity)]
        ring
      rw [hsq]
      field_simp
      ring
    have hpoint (omega : Omega) :
        G omega ≤ Real.exp (-a / 2) + badM.indicator (fun _ => (1 : ℝ)) omega := by
      by_cases homega : omega ∈ badM
      · rw [Set.indicator_of_mem homega]
        linarith [hGbounds omega |>.2, Real.exp_pos (-a / 2)]
      · rw [Set.indicator_of_notMem homega, add_zero]
        have hmarkov : G omega ≤ Real.exp (-a + Y omega) := by
          simpa [G, tail, SpinGlass.gibbs_average_n, SpinGlass.H_t,
            SpinGlass.H_gauss, SpinGlass.H_field, fullPathHamiltonian, Y, a] using
            gibbs_tail_le_exp_log_ratio hN
              (fullPathHamiltonian path s.1 omega) (rsQ beta h)
              rho epsilon hrho hepsilon
        have hnotbad : omega ∉ bad := fun hmem => homega (hbadSubM hmem)
        have hYgood : Y omega ≤ a / 2 := le_of_not_gt hnotbad
        exact hmarkov.trans (by
          apply Real.exp_le_exp.mpr
          linarith)
    have hconstInt : Integrable (fun _ : Omega => Real.exp (-a / 2)) :=
      integrable_const _
    have hindInt : Integrable (badM.indicator (fun _ : Omega => (1 : ℝ))) :=
      (integrable_const (1 : ℝ)).indicator hbadMeas
    have hrhsInt : Integrable
        (fun omega => Real.exp (-a / 2) +
          badM.indicator (fun _ => (1 : ℝ)) omega) :=
      hconstInt.add hindInt
    have hintegral := integral_mono hGint hrhsInt hpoint
    have hlargeBound : ∫ omega, G omega ∂volume ≤
        2 * Real.exp (-c * (N : ℝ)) := by
      rw [integral_add hconstInt hindInt, integral_const,
        integral_indicator_const (1 : ℝ) hbadMeas] at hintegral
      simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hintegral
      have hc1le : c ≤ c₁ := min_le_left _ _
      have hc2le : c ≤ c₂ := min_le_right _ _
      have hexp1 : Real.exp (-a / 2) ≤ Real.exp (-c * (N : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [a, c₁] at *
        have hNr : 0 ≤ (N : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hc1le hNr]
      have hexp2 : Real.exp (-c₂ * (N : ℝ)) ≤
          Real.exp (-c * (N : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hc2le
          (show 0 ≤ (N : ℝ) by positivity)
        linarith
      calc
        ∫ omega, G omega ∂volume ≤
            Real.exp (-a / 2) + volume.real badM := by simpa using hintegral
        _ ≤ Real.exp (-c * (N : ℝ)) +
            Real.exp (-c * (N : ℝ)) :=
          add_le_add hexp1 (hbadReal.trans hexp2)
        _ = 2 * Real.exp (-c * (N : ℝ)) := by ring
    unfold SpinGlass.nu
    change (∫ omega, G omega ∂volume) ≤ C * Real.exp (-c * (N : ℝ))
    calc
      _ ≤ 2 * Real.exp (-c * (N : ℝ)) := hlargeBound
      _ ≤ C * Real.exp (-c * (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        dsimp [C]
        nlinarith [Real.one_le_exp (mul_nonneg hc.le (by positivity : 0 ≤ (N₀ : ℝ)))]
  · have hsmallN : N ≤ N₀ := Nat.le_of_lt (lt_of_not_ge hlarge)
    have hnuOne : (∫ omega, G omega ∂volume) ≤ 1 := by
      simpa using integral_mono hGint (integrable_const (1 : ℝ))
        (fun omega => hGbounds omega |>.2)
    unfold SpinGlass.nu
    change (∫ omega, G omega ∂volume) ≤ C * Real.exp (-c * (N : ℝ))
    calc
      _ ≤ 1 := hnuOne
      _ ≤ C * Real.exp (-c * (N : ℝ)) := by
        dsimp [C]
        have hcast : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hsmallN
        have hexp : 1 ≤ Real.exp (c * (N₀ : ℝ) - c * (N : ℝ)) :=
          Real.one_le_exp (sub_nonneg.mpr
            (mul_le_mul_of_nonneg_left hcast hc.le))
        calc
          1 ≤ 2 * Real.exp (c * (N₀ : ℝ) - c * (N : ℝ)) := by
            nlinarith [Real.exp_pos (c * (N₀ : ℝ) - c * (N : ℝ))]
          _ = 2 * (Real.exp (c * (N₀ : ℝ)) *
              Real.exp (-c * (N : ℝ))) := by
            rw [← Real.exp_add]
            congr 2
            ring
          _ = 2 * Real.exp (c * (N₀ : ℝ)) *
              Real.exp (-c * (N : ℝ)) := by ring

end SpinGlass.AT
