module

public import Lemmas.Gaussian.Max
public import Lemmas.AT.Definitions
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

private lemma lipschitzWith_log_sum_exp
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] [Nonempty I]
    (A : I → E →L[ℝ] ℝ) (b : I → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) :
    LipschitzWith C.toNNReal
      (fun x => Real.log (∑ i, Real.exp (A i x + b i))) := by
  let Z : E → ℝ := fun x => ∑ i, Real.exp (A i x + b i)
  have hZpos (x : E) : 0 < Z x := by
    dsimp [Z]
    apply Finset.sum_pos'
    · exact fun i _ => (Real.exp_pos _).le
    · let i : I := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, Real.exp_pos _⟩
  have hlog (x y : E) :
      Real.log (Z x) ≤ Real.log (Z y) + C * dist x y := by
    have hterm (i : I) :
        A i x + b i ≤ A i y + b i + C * dist x y := by
      have hop := (A i).le_opNorm (x - y)
      have hnorm : ‖A i (x - y)‖ ≤ C * ‖x - y‖ :=
        hop.trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      have hle : A i (x - y) ≤ C * ‖x - y‖ :=
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)
      rw [map_sub] at hle
      rw [dist_eq_norm]
      linarith
    have hsum : Z x ≤ Real.exp (C * dist x y) * Z y := by
      dsimp [Z]
      calc
        (∑ i, Real.exp (A i x + b i))
            ≤ ∑ i, Real.exp (A i y + b i + C * dist x y) :=
          Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (hterm i)
        _ = Real.exp (C * dist x y) *
              ∑ i, Real.exp (A i y + b i) := by
          simp_rw [Real.exp_add]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    have h := Real.log_le_log (hZpos x) hsum
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (hZpos y)), Real.log_exp] at h
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (Real.log (Z x)) (Real.log (Z y)) ≤ (C.toNNReal : ℝ) * dist x y
  rw [Real.coe_toNNReal _ hC, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have := hlog y x
    rw [dist_comm] at this
    linarith
  · linarith [hlog x y]

/-- Coordinates of the standard smart-path realization: the `g_{ij}`
coordinates followed by the independent one-site coordinates `z_i`. -/
abbrev CoupledGaussianIndex (N : ℕ) := (Fin N × Fin N) ⊕ Fin N

/-- The Gaussian coefficient vector of one configuration in the smart-path
Hamiltonian.  We use the ordered-pair normalization from the paper. -/
noncomputable def coupledDisorderCoefficient
    (N : ℕ) (β q s : ℝ) (σ : SpinGlass.Config N) :
    EuclideanSpace ℝ (CoupledGaussianIndex N) :=
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl ij =>
        β * Real.sqrt s / Real.sqrt (2 * N) *
          (SpinGlass.spin N σ ij.1 * SpinGlass.spin N σ ij.2)
    | Sum.inr i =>
        β * Real.sqrt ((1 - s) * q) * SpinGlass.spin N σ i

/-- A concrete standard-Gaussian realization of `H_{N,s}` compatible with
the sign convention `exp (-H)` used by `constrainedPartition`. -/
noncomputable def coupledCoordinateHamiltonian
    (N : ℕ) (β h q s : ℝ)
    (x : EuclideanSpace ℝ (CoupledGaussianIndex N)) :
    SpinGlass.EnergySpace N :=
  WithLp.toLp 2 fun σ =>
    -(inner ℝ (coupledDisorderCoefficient N β q s σ) x +
      h * ∑ i : Fin N, SpinGlass.spin N σ i)

/-- The existing constrained two-replica partition function, viewed as a
function of its independent standard Gaussian coordinates. -/
noncomputable def coupledConstrainedLogPartition
    (N : ℕ) (β h q s v : ℝ)
    (x : EuclideanSpace ℝ (CoupledGaussianIndex N)) : ℝ :=
  Real.log
    (constrainedPartition (coupledCoordinateHamiltonian N β h q s x) v)

/-- The quadratically coupled log-partition function in canonical Gaussian
coordinates. -/
noncomputable def quadraticCoupledCoordinateLogPartition
    (N : ℕ) (β h q s rho : ℝ)
    (x : EuclideanSpace ℝ (CoupledGaussianIndex N)) : ℝ :=
  Real.log
    (quadraticCoupledPartition
      (coupledCoordinateHamiltonian N β h q s x) q rho)

private lemma coupled_pair_coefficient_norm_le
    (N : ℕ) (β q s : ℝ) (hN : 0 < N)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (σ τ : SpinGlass.Config N) :
    ‖coupledDisorderCoefficient N β q s σ +
        coupledDisorderCoefficient N β q s τ‖ ≤
      2 * |β| * Real.sqrt N := by
  classical
  let c := coupledDisorderCoefficient N β q s σ +
    coupledDisorderCoefficient N β q s τ
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q ≤ 1 := hq.2
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have htwoN : 0 < (2 : ℝ) * N := mul_pos (by norm_num) hNreal
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNreal
  have hsqrtTwoN : 0 < Real.sqrt (2 * N) := Real.sqrt_pos.2 htwoN
  have hedge (ij : Fin N × Fin N) :
      (c (Sum.inl ij)) ^ 2 ≤ 2 * β ^ 2 * s / (N : ℝ) := by
    let a := SpinGlass.spin N σ ij.1 * SpinGlass.spin N σ ij.2
    let b := SpinGlass.spin N τ ij.1 * SpinGlass.spin N τ ij.2
    have ha : a ^ 2 = 1 := by
      dsimp [a]
      rw [mul_pow]
      simp [SpinGlass.spin]
    have hb : b ^ 2 = 1 := by
      dsimp [b]
      rw [mul_pow]
      simp [SpinGlass.spin]
    have hab : (a + b) ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (a - b)]
    change ((β * Real.sqrt s / Real.sqrt (2 * N) * a) +
      (β * Real.sqrt s / Real.sqrt (2 * N) * b)) ^ 2 ≤ _
    rw [← mul_add]
    have hsqrt_sq : Real.sqrt (2 * (N : ℝ)) ^ 2 = 2 * N :=
      Real.sq_sqrt htwoN.le
    have hs_sq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
    calc
      (β * Real.sqrt s / Real.sqrt (2 * N) * (a + b)) ^ 2
          = (β ^ 2 * s / (2 * N)) * (a + b) ^ 2 := by
            field_simp [hsqrtTwoN.ne']
            rw [hsqrt_sq, hs_sq]
            ring
      _ ≤ (β ^ 2 * s / (2 * N)) * 4 := by
        exact mul_le_mul_of_nonneg_left hab (by positivity)
      _ = 2 * β ^ 2 * s / (N : ℝ) := by
        field_simp [hNreal.ne']
        ring
  have hsite (i : Fin N) :
      (c (Sum.inr i)) ^ 2 ≤ 4 * β ^ 2 * (1 - s) * q := by
    let a := SpinGlass.spin N σ i
    let b := SpinGlass.spin N τ i
    have ha : a ^ 2 = 1 := by simp [a, SpinGlass.spin]
    have hb : b ^ 2 = 1 := by simp [b, SpinGlass.spin]
    have hab : (a + b) ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (a - b)]
    have harg : 0 ≤ (1 - s) * q :=
      mul_nonneg (sub_nonneg.mpr hs1) hq0
    have hsqrt_sq : Real.sqrt ((1 - s) * q) ^ 2 = (1 - s) * q :=
      Real.sq_sqrt harg
    change ((β * Real.sqrt ((1 - s) * q) * a) +
      (β * Real.sqrt ((1 - s) * q) * b)) ^ 2 ≤ _
    rw [← mul_add]
    calc
      (β * Real.sqrt ((1 - s) * q) * (a + b)) ^ 2
          = (β ^ 2 * ((1 - s) * q)) * (a + b) ^ 2 := by
            rw [mul_pow, mul_pow, hsqrt_sq]
      _ ≤ (β ^ 2 * ((1 - s) * q)) * 4 := by
        exact mul_le_mul_of_nonneg_left hab (by positivity)
      _ = 4 * β ^ 2 * (1 - s) * q := by ring
  have hsq : ‖c‖ ^ 2 ≤ 4 * β ^ 2 * (N : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
    calc
      (∑ ij : Fin N × Fin N, (c (Sum.inl ij)) ^ 2) +
          ∑ i : Fin N, (c (Sum.inr i)) ^ 2
        ≤ (∑ _ij : Fin N × Fin N, 2 * β ^ 2 * s / (N : ℝ)) +
            ∑ _i : Fin N, 4 * β ^ 2 * (1 - s) * q :=
          add_le_add (Finset.sum_le_sum fun ij _ => hedge ij)
            (Finset.sum_le_sum fun i _ => hsite i)
      _ ≤ 4 * β ^ 2 * (N : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp [hNreal.ne']
        have hβ : 0 ≤ β ^ 2 := sq_nonneg β
        have hqmul : (1 - s) * q ≤ 1 - s :=
          mul_le_of_le_one_right (sub_nonneg.mpr hs1) hq1
        ring_nf
        nlinarith [mul_le_mul_of_nonneg_left hqmul hβ]
  rw [← sq_le_sq₀ (norm_nonneg c) (by positivity)]
  have hrhs : (2 * |β| * Real.sqrt N) ^ 2 = 4 * β ^ 2 * (N : ℝ) := by
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hNreal.le]
    ring
  rw [hrhs]
  exact hsq

/-- For every attainable overlap `v`, the constrained two-replica log
partition function `log Z^{(2)}_{N,s}(v)` is
`2 |β| √N`-Lipschitz in the independent standard Gaussian coordinates. -/
theorem coupled_constrained_log_partition_lipschitz
    (N : ℕ) (β h q s v : ℝ)
    (hN : 0 < N)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    LipschitzWith (2 * |β| * Real.sqrt N).toNNReal
      (coupledConstrainedLogPartition N β h q s v) := by
  classical
  let P := {p : SpinGlass.Config N × SpinGlass.Config N //
    SpinGlass.overlap N p.1 p.2 = v}
  rw [attainableOverlaps, Finset.mem_image] at hv
  obtain ⟨p, _hp, hpv⟩ := hv
  letI : Nonempty P := ⟨⟨p, hpv⟩⟩
  let A : P → EuclideanSpace ℝ (CoupledGaussianIndex N) →L[ℝ] ℝ :=
    fun p => innerSL ℝ
      (coupledDisorderCoefficient N β q s p.1.1 +
        coupledDisorderCoefficient N β q s p.1.2)
  let b : P → ℝ := fun p =>
    h * ((∑ i : Fin N, SpinGlass.spin N p.1.1 i) +
      ∑ i : Fin N, SpinGlass.spin N p.1.2 i)
  have hA (p : P) : ‖A p‖ ≤ 2 * |β| * Real.sqrt N := by
    change ‖innerSL ℝ (coupledDisorderCoefficient N β q s p.1.1 +
      coupledDisorderCoefficient N β q s p.1.2)‖ ≤ _
    rw [innerSL_apply_norm]
    exact coupled_pair_coefficient_norm_le N β q s hN hs hq p.1.1 p.1.2
  have hC : 0 ≤ 2 * |β| * Real.sqrt N := by positivity
  have hLip := lipschitzWith_log_sum_exp A b
    (2 * |β| * Real.sqrt N) hC hA
  have hfun : coupledConstrainedLogPartition N β h q s v =
      fun x => Real.log (∑ p : P, Real.exp (A p x + b p)) := by
    funext x
    unfold coupledConstrainedLogPartition constrainedPartition
    congr 1
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.overlap N p.1 p.2 = v)
      (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
        SpinGlass.overlap N p.1 p.2 = v) (by simp)]
    apply Finset.sum_congr rfl
    intro p _hp
    congr 1
    simp [A, b, coupledCoordinateHamiltonian]
    ring
  rw [hfun]
  exact hLip

/-- The quadratically coupled two-replica log-partition function is
`2 |β| √N`-Lipschitz in the canonical Gaussian coordinates. -/
theorem quadraticCoupledCoordinateLogPartition_lipschitz
    (N : ℕ) (β h q s rho : ℝ)
    (hN : 0 < N)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (2 * |β| * Real.sqrt N).toNNReal
      (quadraticCoupledCoordinateLogPartition N β h q s rho) := by
  classical
  let A : (SpinGlass.Config N × SpinGlass.Config N) →
      EuclideanSpace ℝ (CoupledGaussianIndex N) →L[ℝ] ℝ := fun p =>
    innerSL ℝ
      (coupledDisorderCoefficient N β q s p.1 +
        coupledDisorderCoefficient N β q s p.2)
  let b : (SpinGlass.Config N × SpinGlass.Config N) → ℝ := fun p =>
    h * ((∑ i : Fin N, SpinGlass.spin N p.1 i) +
      ∑ i : Fin N, SpinGlass.spin N p.2 i) +
      rho * (N : ℝ) / 2 * (SpinGlass.overlap N p.1 p.2 - q) ^ 2
  have hA (p : SpinGlass.Config N × SpinGlass.Config N) :
      ‖A p‖ ≤ 2 * |β| * Real.sqrt N := by
    change ‖innerSL ℝ (coupledDisorderCoefficient N β q s p.1 +
      coupledDisorderCoefficient N β q s p.2)‖ ≤ _
    rw [innerSL_apply_norm]
    exact coupled_pair_coefficient_norm_le N β q s hN hs hq p.1 p.2
  have hC : 0 ≤ 2 * |β| * Real.sqrt N := by positivity
  have hLip := lipschitzWith_log_sum_exp A b
    (2 * |β| * Real.sqrt N) hC hA
  have hfun : quadraticCoupledCoordinateLogPartition N β h q s rho =
      fun x => Real.log (∑ p, Real.exp (A p x + b p)) := by
    funext x
    unfold quadraticCoupledCoordinateLogPartition quadraticCoupledPartition
    congr 2
    funext p
    simp [A, b, coupledCoordinateHamiltonian]
    ring
  rw [hfun]
  exact hLip

/-- The logarithm of the coupled Gibbs moment, written as the difference of
the coupled log-partition functions at `rho` and at zero, is
`4 |β| √N`-Lipschitz. -/
theorem quadraticCoupledCoordinateLogRatio_lipschitz
    (N : ℕ) (β h q s rho : ℝ)
    (hN : 0 < N)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (4 * |β| * Real.sqrt N).toNNReal
      (fun x => quadraticCoupledCoordinateLogPartition N β h q s rho x -
        quadraticCoupledCoordinateLogPartition N β h q s 0 x) := by
  have hρ := quadraticCoupledCoordinateLogPartition_lipschitz
    N β h q s rho hN hs hq
  have h₀ := quadraticCoupledCoordinateLogPartition_lipschitz
    N β h q s 0 hN hs hq
  have hconst : (4 * |β| * Real.sqrt N).toNNReal =
      (2 * |β| * Real.sqrt N).toNNReal +
        (2 * |β| * Real.sqrt N).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 4 * |β| * Real.sqrt N),
      Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * |β| * Real.sqrt N)]
    ring
  rw [hconst]
  exact hρ.sub h₀

/-- The spin-product sum is determined by the number of coordinates on which
the two configurations agree. -/
private lemma sum_spin_mul_eq_agreement_count
    (N : ℕ) (σ τ : SpinGlass.Config N) :
    (∑ i : Fin N, SpinGlass.spin N σ i * SpinGlass.spin N τ i) =
      2 * ((Finset.univ.filter fun i : Fin N => σ i = τ i).card : ℝ) - N := by
  classical
  have hspin (i : Fin N) :
      SpinGlass.spin N σ i * SpinGlass.spin N τ i =
        if σ i = τ i then (1 : ℝ) else -1 := by
    cases hσ : σ i <;> cases hτ : τ i <;> simp [SpinGlass.spin, hσ, hτ]
  simp_rw [hspin]
  calc
    (∑ i : Fin N, if σ i = τ i then (1 : ℝ) else -1)
        = ∑ i : Fin N,
            (2 * (if σ i = τ i then (1 : ℝ) else 0) - 1) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> norm_num
    _ = 2 * ((Finset.univ.filter fun i : Fin N => σ i = τ i).card : ℝ) - N := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum]
      congr 1
      simp

private def configAgreementLevel
    (N : ℕ) (σ τ : SpinGlass.Config N) : Fin (N + 1) :=
  ⟨(Finset.univ.filter fun i : Fin N => σ i = τ i).card,
    Nat.lt_succ_iff.mpr (by
      simpa using (Finset.univ.filter fun i : Fin N => σ i = τ i).card_le_univ)⟩

private lemma overlap_eq_of_agreementLevel_eq
    (N : ℕ) {σ τ σ' τ' : SpinGlass.Config N}
    (hlevel : configAgreementLevel N σ τ = configAgreementLevel N σ' τ') :
    SpinGlass.overlap N σ τ = SpinGlass.overlap N σ' τ' := by
  have hcard := congrArg Fin.val hlevel
  change (Finset.univ.filter fun i : Fin N => σ i = τ i).card =
    (Finset.univ.filter fun i : Fin N => σ' i = τ' i).card at hcard
  unfold SpinGlass.overlap
  rw [sum_spin_mul_eq_agreement_count, sum_spin_mul_eq_agreement_count]
  rw [hcard]

private noncomputable def attainableOverlapPair
    (N : ℕ) (v : {v : ℝ // v ∈ attainableOverlaps N}) :
    SpinGlass.Config N × SpinGlass.Config N :=
  Classical.choose (Finset.mem_image.mp v.2)

private lemma attainableOverlapPair_spec
    (N : ℕ) (v : {v : ℝ // v ∈ attainableOverlaps N}) :
    SpinGlass.overlap N (attainableOverlapPair N v).1
      (attainableOverlapPair N v).2 = v.1 :=
  (Classical.choose_spec (Finset.mem_image.mp v.2)).2

noncomputable instance attainableOverlapNonempty (N : ℕ) :
    Nonempty {v : ℝ // v ∈ attainableOverlaps N} := by
  let σ : SpinGlass.Config N := fun _ => false
  refine ⟨⟨SpinGlass.overlap N σ σ, ?_⟩⟩
  unfold attainableOverlaps
  exact Finset.mem_image.mpr ⟨(σ, σ), Finset.mem_univ _, rfl⟩

/-- Two configurations have only `N + 1` possible overlap values. -/
lemma card_attainableOverlaps_le (N : ℕ) :
    Fintype.card {v : ℝ // v ∈ attainableOverlaps N} ≤ N + 1 := by
  let level : {v : ℝ // v ∈ attainableOverlaps N} → Fin (N + 1) := fun v =>
    configAgreementLevel N (attainableOverlapPair N v).1
      (attainableOverlapPair N v).2
  have hlevel : Function.Injective level := by
    intro v w hvw
    apply Subtype.ext
    rw [← attainableOverlapPair_spec N v, ← attainableOverlapPair_spec N w]
    exact overlap_eq_of_agreementLevel_eq N hvw
  simpa using Fintype.card_le_of_injective level hlevel

/-- Arithmetic estimate for the squared Lipschitz constant of
`L_v = log Z^{(2)}_{N,s}(v)`.
The first term comes from the `N(N-1)/2` variables `g_{ij}`,
and the second from the `N` variables `z_i`.
-/
lemma coupled_log_partition_grad_sq_le
    (N : ℕ) (β q s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    2 * β ^ 2 * s * ((N : ℝ) - 1) +
        4 * β ^ 2 * (1 - s) * q * (N : ℝ)
      ≤ 4 * β ^ 2 * (N : ℝ) := by
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hq1 : q ≤ 1 := hq.2
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hβ : 0 ≤ β ^ 2 := sq_nonneg β
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hqmul :
      (1 - s) * q ≤ 1 - s := by
    exact mul_le_of_le_one_right h1s hq1
  have hz :
      4 * β ^ 2 * (1 - s) * q * (N : ℝ)
        ≤ 4 * β ^ 2 * (1 - s) * (N : ℝ) := by
    have hfac : 0 ≤ 4 * β ^ 2 * (N : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hqmul hfac]
  have hg :
      2 * β ^ 2 * s * ((N : ℝ) - 1)
        ≤ 2 * β ^ 2 * s * (N : ℝ) := by
    have hfac : 0 ≤ 2 * β ^ 2 * s := by positivity
    nlinarith
  calc
    2 * β ^ 2 * s * ((N : ℝ) - 1) +
          4 * β ^ 2 * (1 - s) * q * (N : ℝ)
        ≤ 2 * β ^ 2 * s * (N : ℝ) +
          4 * β ^ 2 * (1 - s) * (N : ℝ) := add_le_add hg hz
    _ ≤ 4 * β ^ 2 * (N : ℝ) := by
      have hnonneg :
          0 ≤ β ^ 2 * (N : ℝ) * s := by positivity
      nlinarith

/-- If the derivative computation gives
`‖D L_v‖ ≤ 2 |β| √N`, then `L_v` is Lipschitz
with that constant. -/
lemma coupled_log_partition_lipschitz
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (β : ℝ)
    (L : E → ℝ)
    (hL : Differentiable ℝ L)
    (hderiv :
      ∀ x, ‖fderiv ℝ L x‖ ≤
        2 * |β| * Real.sqrt N) :
    LipschitzWith
      (2 * |β| * Real.sqrt N).toNNReal L := by
  apply lipschitzWith_of_nnnorm_fderiv_le hL
  intro x
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm]
  have hnonneg :
      0 ≤ 2 * |β| * Real.sqrt N := by positivity
  simpa [Real.coe_toNNReal _ hnonneg] using hderiv x

/-- Gaussian-max concentration for a coupled log-partition family on a
compact subset of the strict AT region.  The hypothesis `hcard` records that
there are at most `N + 1` attainable overlap values.  Thus the right-hand
side is a constant depending only on `K`, through `data.βmax`, times
`√(N log(N + 1))`. -/
private theorem coupled_log_partition_gaussian_max_of_lipschitz
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    {ι I : Type*} [Fintype ι] [Fintype I] [Nonempty I]
    (N : ℕ)
    (F : I → EuclideanSpace ℝ ι → ℝ)
    (hcard : Fintype.card I ≤ N + 1)
    (hLip : ∀ v,
      LipschitzWith
        (2 * data.βmax * Real.sqrt N).toNNReal (F v)) :
    (∫ x, centeredGaussianMax Finset.univ_nonempty F x
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      2 * data.βmax * Real.sqrt N *
        Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
  have hL : 0 ≤ 2 * data.βmax * Real.sqrt N := by
    exact mul_nonneg (mul_nonneg (by norm_num) data.βmax_pos.le) (Real.sqrt_nonneg _)
  calc
    (∫ x, centeredGaussianMax Finset.univ_nonempty F x
          ∂SYK.standardGaussianMeasureOnEuclidean ι)
        ≤ (2 * data.βmax * Real.sqrt N) *
            Real.sqrt (2 * Real.log (Fintype.card I : ℝ)) :=
      gaussian_max_estimate F (2 * data.βmax * Real.sqrt N) hL hLip
    _ ≤ 2 * data.βmax * Real.sqrt N *
          Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
      gcongr
      exact_mod_cast hcard

/-- The expected centered maximum of the constrained two-replica log
partition functions is bounded by a compact-set constant times
`√(N log (N + 1))`.  Here `q` is the canonical replica-symmetric fixed point
and `s` is intrinsically restricted to the smart-path interval.  Thus the
only proposition hypothesis is `(β, h) ∈ K`. -/
theorem coupled_log_partition_gaussian_max
    {K : Set (ℝ × ℝ)}
    (data : UniformATData K)
    (N : ℕ) (β h : ℝ) (s : Set.Icc (0 : ℝ) 1)
    (hp : (β, h) ∈ K) :
    (∫ x, centeredGaussianMax Finset.univ_nonempty
          (fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
            coupledConstrainedLogPartition N β h (rsQ β h) s.1 v.1) x
          ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N)) ≤
      2 * data.βmax * Real.sqrt N *
        Real.sqrt (2 * Real.log ((N : ℝ) + 1)) := by
  have hβpos : 0 < β := data.β_pos (β, h) hp
  have hβ : |β| ≤ data.βmax := by
    rw [abs_of_pos hβpos]
    exact data.β_bound (β, h) hp
  have hLip (v : {v : ℝ // v ∈ attainableOverlaps N}) :
      LipschitzWith
        (2 * data.βmax * Real.sqrt N).toNNReal
        (coupledConstrainedLogPartition N β h (rsQ β h) s.1 v.1) := by
    by_cases hNzero : N = 0
    · subst N
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have hxy : x = y := Subsingleton.elim x y
      subst y
      simp
    · have hN : 0 < N := Nat.pos_of_ne_zero hNzero
      have hsmall := coupled_constrained_log_partition_lipschitz
        N β h (rsQ β h) s.1 v.1 hN s.2 (rsQ_mem_Icc β h) v.2
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have hconst :
          2 * |β| * Real.sqrt N ≤ 2 * data.βmax * Real.sqrt N := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hβ (by norm_num)) (Real.sqrt_nonneg _)
      calc
        dist (coupledConstrainedLogPartition N β h (rsQ β h) s.1 v.1 x)
            (coupledConstrainedLogPartition N β h (rsQ β h) s.1 v.1 y)
          ≤ ((2 * |β| * Real.sqrt N).toNNReal : ℝ) * dist x y :=
            hsmall.dist_le_mul x y
        _ ≤ ((2 * data.βmax * Real.sqrt N).toNNReal : ℝ) * dist x y := by
          have hsmall_nonneg : 0 ≤ 2 * |β| * Real.sqrt N := by positivity
          have hlarge_nonneg : 0 ≤ 2 * data.βmax * Real.sqrt N := by
            exact mul_nonneg (mul_nonneg (by norm_num) data.βmax_pos.le)
              (Real.sqrt_nonneg _)
          rw [Real.coe_toNNReal _ hsmall_nonneg,
            Real.coe_toNNReal _ hlarge_nonneg]
          exact mul_le_mul_of_nonneg_right hconst dist_nonneg
  exact coupled_log_partition_gaussian_max_of_lipschitz data N
    (fun v : {v : ℝ // v ∈ attainableOverlaps N} =>
      coupledConstrainedLogPartition N β h (rsQ β h) s.1 v.1)
    (card_attainableOverlaps_le N) hLip

end SpinGlass.AT
