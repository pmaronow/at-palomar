module

/- Compatibility adaptation: current coordinatewise measurability and ordered real-product interfaces where applicable. -/
public import Lemmas.GuerraTalagrand.Bound.Comparison
public import Lemmas.GuerraTalagrand.Bound.Transport
public import Lemmas.GuerraTalagrand.Bound.FiniteStep
public import Lemmas.GuerraTalagrand.Gaussian

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SpinGlass.AT

/-- A subfamily of independent product coordinates is again the corresponding
product measure. -/
lemma gaussianProduct_restrict_map
    {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Function.Injective e) :
    Measure.map (fun z : I → ℝ => fun j => z (e j))
        (Measure.pi (fun _ : I => gaussianReal 0 1)) =
      Measure.pi (fun _ : J => gaussianReal 0 1) := by
  let X : I → (I → ℝ) → ℝ := fun i z => z i
  have hX : iIndepFun X (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hsub : iIndepFun (fun j => X (e j))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := hX.precomp he
  rw [hsub.map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : I => gaussianReal 0 1) (e j)).map_eq

lemma integral_gaussianProduct_restrict
    {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Function.Injective e) (f : (J → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f
      (Measure.pi (fun _ : J => gaussianReal 0 1))) :
    (∫ z : I → ℝ, f (fun j => z (e j))
        ∂Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ z : J → ℝ, f z
        ∂Measure.pi (fun _ : J => gaussianReal 0 1) := by
  have hp : Measurable (fun z : I → ℝ => fun j => z (e j)) := by
    fun_prop
  rw [← integral_map hp.aemeasurable]
  · rw [gaussianProduct_restrict_map e he]
  · rw [gaussianProduct_restrict_map e he]
    exact hf

noncomputable def gtFourGaussianTuple
    (p : ℝ × (ℝ × (ℝ × ℝ))) : Fin 4 → ℝ :=
  ![p.1, p.2.1, p.2.2.1, p.2.2.2]

lemma gaussianFinFour_eq_map_tuple :
    Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) =
      Measure.map gtFourGaussianTuple
        ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod
          ((gaussianReal 0 1).prod (gaussianReal 0 1)))) := by
  apply Measure.pi_eq
  intro sets hsets
  have hm : Measurable gtFourGaussianTuple := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp [gtFourGaussianTuple] <;> fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hsets)]
  rw [show gtFourGaussianTuple ⁻¹' Set.univ.pi sets =
      sets 0 ×ˢ (sets 1 ×ˢ (sets 2 ×ˢ sets 3)) by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_prod]
    constructor
    · intro hp
      exact ⟨by simpa [gtFourGaussianTuple] using hp 0,
        by simpa [gtFourGaussianTuple] using hp 1,
        by simpa [gtFourGaussianTuple] using hp 2,
        by simpa [gtFourGaussianTuple] using hp 3⟩
    · rintro ⟨h₀, h₁, h₂, h₃⟩ i
      fin_cases i <;> simp [gtFourGaussianTuple, h₀, h₁, h₂, h₃]]
  simp [Measure.prod_prod, Fin.prod_univ_four]
  ring

lemma integral_gaussianFinFour_eq_iterated
    (f : (Fin 4 → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1))) :
    (∫ z : Fin 4 → ℝ, f z ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) =
      ∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
        f ![z₀, z₁, z₂, z₃] ∂gaussianReal 0 1
        ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  let μ := (gaussianReal 0 1).prod ((gaussianReal 0 1).prod
    ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  have hm : Measurable gtFourGaussianTuple := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp [gtFourGaussianTuple] <;> fun_prop
  have hfm : Integrable f (Measure.map gtFourGaussianTuple μ) := by
    rw [← gaussianFinFour_eq_map_tuple]
    exact hf
  have hc : Integrable (f ∘ gtFourGaussianTuple) μ := hfm.comp_measurable hm
  have hc' : Integrable (fun p => f (gtFourGaussianTuple p)) μ := by
    simpa [Function.comp_def] using hc
  rw [gaussianFinFour_eq_map_tuple]
  rw [integral_map hm.aemeasurable hfm.aestronglyMeasurable]
  rw [integral_prod _ hc']
  apply integral_congr_ae
  filter_upwards [hc'.prod_right_ae] with z₀ hz₀
  rw [integral_prod _ hz₀]
  apply integral_congr_ae
  filter_upwards [hz₀.prod_right_ae] with z₁ hz₁
  rw [integral_prod _ hz₁]
  rfl

/-- Four independent site coordinates used below the breakpoint in the ordinary branch. -/
abbrev GTOrdinarySiteIndex (N : ℕ) := Fin N × Fin 4

/-- Canonical physical coordinates, scalar compensation coordinates, and trial site coordinates. -/
abbrev GTOrdinaryIndex (N : ℕ) :=
  CoupledGaussianIndex N ⊕ ((Fin 2 × Fin 2) ⊕ GTOrdinarySiteIndex N)

noncomputable def gtPairPhysicalCoefficient
    (N : ℕ) (β q s : ℝ) (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (CoupledGaussianIndex N) :=
  coupledDisorderCoefficient N β q s p.1 +
    coupledDisorderCoefficient N β q s p.2

noncomputable def gtPairPotential
    (N : ℕ) (h lam v : ℝ) (p : SpinGlass.Config N × SpinGlass.Config N) : ℝ :=
  h * ((∑ i : Fin N, SpinGlass.spin N p.1 i) +
    ∑ i : Fin N, SpinGlass.spin N p.2 i) +
  lam * ((∑ i : Fin N,
    SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i) - (N : ℝ) * v)

/-- Physical pair coefficient, augmented by the state-independent scalar compensation. -/
noncomputable def gtOrdinaryPhysicalCoefficient
    (N : ℕ) (β q s v : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (GTOrdinaryIndex N) :=
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl j => gtPairPhysicalCoefficient N β q s p j
    | Sum.inr (Sum.inl ab) =>
        Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q ab.1 ab.2
    | Sum.inr (Sum.inr _) => 0

/-- The physical coefficient without an explicit scalar-compensation
coordinate. The compensation will be used as a covariance shift, which leaves
the finite-state Gibbs covariance unchanged. -/
noncomputable def gtOrdinaryBarePhysicalCoefficient
    (N : ℕ) (β q s : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (GTOrdinaryIndex N) :=
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl j => gtPairPhysicalCoefficient N β q s p j
    | Sum.inr _ => 0

/-- Trial coefficient for the branch `|v| < q`. -/
noncomputable def gtOrdinaryTrialCoefficient
    (N : ℕ) (β q s v : ℝ)
    (p : SpinGlass.Config N × SpinGlass.Config N) :
    EuclideanSpace ℝ (GTOrdinaryIndex N) :=
  let r := |v|
  let sign := gtPathSign v
  let e := β * Real.sqrt ((1 - s) * q)
  let a := gtIncrementScale β s 0 r
  let b := gtIncrementScale β s r q
  WithLp.toLp 2 fun k =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (i, j)) =>
        if j = 0 then
          e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)
        else if j = 1 then
          a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)
        else if j = 2 then
          b * SpinGlass.spin N p.1 i
        else
          b * SpinGlass.spin N p.2 i

noncomputable def gtOrdinaryTrialFieldOne
    (N : ℕ) (β h q s v : ℝ) (z : GTOrdinarySiteIndex N → ℝ)
    (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z (i, 0) +
    gtIncrementScale β s 0 |v| * z (i, 1) +
    gtIncrementScale β s |v| q * z (i, 2)

noncomputable def gtOrdinaryTrialFieldTwo
    (N : ℕ) (β h q s v : ℝ) (z : GTOrdinarySiteIndex N → ℝ)
    (i : Fin N) : ℝ :=
  h + β * Real.sqrt ((1 - s) * q) * z (i, 0) +
    gtPathSign v * gtIncrementScale β s 0 |v| * z (i, 1) +
    gtIncrementScale β s |v| q * z (i, 3)

lemma gtOrdinary_coefficients_orthogonal
    (N : ℕ) (β q s v : ℝ)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryPhysicalCoefficient N β q s v p)
      (gtOrdinaryTrialCoefficient N β q s v r) = 0 := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp [gtOrdinaryPhysicalCoefficient, gtOrdinaryTrialCoefficient,
    RCLike.inner_apply]

lemma gtOrdinaryBare_coefficients_orthogonal
    (N : ℕ) (β q s v : ℝ)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
      (gtOrdinaryTrialCoefficient N β q s v r) = 0 := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp [gtOrdinaryBarePhysicalCoefficient, gtOrdinaryTrialCoefficient,
    RCLike.inner_apply]

lemma smartPathCovKernel_eq_gtCovarianceFunction
    {N : ℕ} (hN : 0 < N) (β q s : ℝ)
    (σ τ : SpinGlass.Config N) :
    smartPathCovKernel N β q s σ τ =
      (N : ℝ) * gtCovarianceFunction β q s (SpinGlass.overlap N σ τ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold smartPathCovKernel gtCovarianceFunction SpinGlass.sk_cov_kernel
    SpinGlass.simple_cov_kernel SpinGlass.overlap
  field_simp [hNr]
  ring

lemma gtPairPhysicalCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtPairPhysicalCoefficient N β q s p)
      (gtPairPhysicalCoefficient N β q s r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceFunction β q s
          (pairOverlapMatrix p r a b) := by
  unfold gtPairPhysicalCoefficient
  rw [inner_add_left, inner_add_right, inner_add_right]
  rw [coupledDisorderCoefficient_inner N β q s hs hq0,
    coupledDisorderCoefficient_inner N β q s hs hq0,
    coupledDisorderCoefficient_inner N β q s hs hq0,
    coupledDisorderCoefficient_inner N β q s hs hq0]
  simp_rw [smartPathCovKernel_eq_gtCovarianceFunction hN]
  simp only [pairOverlapMatrix, pairConfig]
  norm_num [Fin.sum_univ_two]
  ring

lemma gtOrdinaryBarePhysicalCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
      (gtOrdinaryBarePhysicalCoefficient N β q s r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceFunction β q s (pairOverlapMatrix p r a b) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [gtOrdinaryBarePhysicalCoefficient, RCLike.inner_apply, conj_trivial,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [show (∑ j : CoupledGaussianIndex N,
      gtPairPhysicalCoefficient N β q s r j *
        gtPairPhysicalCoefficient N β q s p j) =
      inner ℝ (gtPairPhysicalCoefficient N β q s p)
        (gtPairPhysicalCoefficient N β q s r) by
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply]]
  exact gtPairPhysicalCoefficient_inner hN hs hq0 p r

lemma gtOrdinaryPhysicalCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryPhysicalCoefficient N β q s v p)
      (gtOrdinaryPhysicalCoefficient N β q s v r) =
      (N : ℝ) *
        ((∑ a : Fin 2, ∑ b : Fin 2,
          gtCovarianceFunction β q s (pairOverlapMatrix p r a b)) +
          gtScalarVariance β s v q) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [gtOrdinaryPhysicalCoefficient, RCLike.inner_apply, conj_trivial]
  rw [show (∑ j : CoupledGaussianIndex N,
      gtPairPhysicalCoefficient N β q s r j *
        gtPairPhysicalCoefficient N β q s p j) =
      inner ℝ (gtPairPhysicalCoefficient N β q s p)
        (gtPairPhysicalCoefficient N β q s r) by
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply]]
  rw [gtPairPhysicalCoefficient_inner hN hs hq0]
  rw [Fintype.sum_sum_type]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  have hNr : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hs2 : Real.sqrt (s / 2) ^ 2 = s / 2 :=
    Real.sq_sqrt (div_nonneg hs.1 (by norm_num))
  have hscalar :
      (∑ ab : Fin 2 × Fin 2,
        (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q ab.1 ab.2) *
          (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q ab.1 ab.2)) =
        (N : ℝ) * gtScalarVariance β s v q := by
    rw [gtScalarVariance_eq_matrix_sum (β := β) (s := s) (v := v) (u := q) hq0]
    rw [Fintype.sum_prod_type]
    have hterm : ∀ a b : Fin 2,
        (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q a b) *
          (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q a b) =
        (N : ℝ) * (s * β ^ 2 / 2 * signedMatrixPath v q a b ^ 2) := by
      intro a b
      calc
        (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q a b) *
            (Real.sqrt N * β * Real.sqrt (s / 2) * signedMatrixPath v q a b) =
          Real.sqrt N ^ 2 * β ^ 2 * Real.sqrt (s / 2) ^ 2 *
            signedMatrixPath v q a b ^ 2 := by ring
        _ = _ := by rw [hNr, hs2]; ring
    simp_rw [hterm]
    calc
      (∑ a : Fin 2, ∑ b : Fin 2,
          (N : ℝ) * (s * β ^ 2 / 2 * signedMatrixPath v q a b ^ 2)) =
          ((N : ℝ) * (s * β ^ 2 / 2)) *
            ∑ a : Fin 2, ∑ b : Fin 2, signedMatrixPath v q a b ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (N : ℝ) * (s * β ^ 2 / 2 *
          ∑ a : Fin 2, ∑ b : Fin 2, signedMatrixPath v q a b ^ 2) := by ring
  rw [hscalar]
  ring

lemma spin_pair_sum_eq_overlap
    {N : ℕ} (hN : 0 < N)
    (p r : SpinGlass.Config N × SpinGlass.Config N) (a b : Fin 2) :
    (∑ i : Fin N,
      SpinGlass.spin N (pairConfig p a) i *
        SpinGlass.spin N (pairConfig r b) i) =
      (N : ℝ) * pairOverlapMatrix p r a b := by
  simp only [pairOverlapMatrix]
  exact spin_sum_eq_mul_overlap hN _ _

lemma gtOrdinaryTrialCoefficient_inner
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hrq : |v| ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryTrialCoefficient N β q s v p)
      (gtOrdinaryTrialCoefficient N β q s v r) =
      (N : ℝ) * ∑ a : Fin 2, ∑ b : Fin 2,
        gtCovarianceMatrix β q s v q a b * pairOverlapMatrix p r a b := by
  classical
  let rv : ℝ := |v|
  let sign : ℝ := gtPathSign v
  let e : ℝ := β * Real.sqrt ((1 - s) * q)
  let a : ℝ := gtIncrementScale β s 0 rv
  let b : ℝ := gtIncrementScale β s rv q
  have he : e ^ 2 = β ^ 2 * (1 - s) * q := by
    dsimp [e]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hs.2) hq0)]
    ring
  have ha : a ^ 2 = β ^ 2 * s * rv := by
    simpa [rv] using gtIncrementScale_sq (β := β) (s := s)
      (lower := 0) (upper := rv) hs.1 (abs_nonneg v)
  have hb : b ^ 2 = β ^ 2 * s * (q - rv) := by
    simpa [rv] using gtIncrementScale_sq (β := β) (s := s)
      (lower := rv) (upper := q) hs.1 hrq
  have hsignsq : sign ^ 2 = 1 := by simpa [sign] using gtPathSign_sq v
  have hsignrv : sign * rv = v := by simpa [sign, rv] using gtPathSign_mul_abs v
  have habssign : |v| * gtPathSign v = v := by
    rw [mul_comm]
    exact gtPathSign_mul_abs v
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [gtOrdinaryTrialCoefficient, RCLike.inner_apply, conj_trivial,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sum_type]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  simp only [show (0 : Fin 4) = 0 by rfl, if_true,
    show (1 : Fin 4) ≠ 0 by decide, if_false,
    show (1 : Fin 4) = 1 by rfl,
    show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (2 : Fin 4) = 2 by rfl,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide]
  change (∑ i : Fin N, (
        e * (SpinGlass.spin N r.1 i + SpinGlass.spin N r.2 i) *
          (e * (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)) +
        a * (SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
          (a * (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)) +
        b * SpinGlass.spin N r.1 i * (b * SpinGlass.spin N p.1 i) +
        b * SpinGlass.spin N r.2 i * (b * SpinGlass.spin N p.2 i))) = _
  simp_rw [show ∀ x y : ℝ, e * x * (e * y) = e ^ 2 * (x * y) by
    intro x y; ring]
  simp_rw [show ∀ x y : ℝ, a * x * (a * y) = a ^ 2 * (x * y) by
    intro x y; ring]
  simp_rw [show ∀ x y : ℝ, b * x * (b * y) = b ^ 2 * (x * y) by
    intro x y; ring]
  rw [he, ha, hb]
  rw [show (∑ i : Fin N,
      (β ^ 2 * (1 - s) * q *
          ((SpinGlass.spin N r.1 i + SpinGlass.spin N r.2 i) *
            (SpinGlass.spin N p.1 i + SpinGlass.spin N p.2 i)) +
        β ^ 2 * s * rv *
          ((SpinGlass.spin N r.1 i + sign * SpinGlass.spin N r.2 i) *
            (SpinGlass.spin N p.1 i + sign * SpinGlass.spin N p.2 i)) +
        β ^ 2 * s * (q - rv) *
          (SpinGlass.spin N r.1 i * SpinGlass.spin N p.1 i) +
        β ^ 2 * s * (q - rv) *
          (SpinGlass.spin N r.2 i * SpinGlass.spin N p.2 i))) =
      β ^ 2 * (1 - s) * q *
          ((∑ i : Fin N, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
           (∑ i : Fin N, SpinGlass.spin N p.1 i * SpinGlass.spin N r.2 i) +
           (∑ i : Fin N, SpinGlass.spin N p.2 i * SpinGlass.spin N r.1 i) +
           (∑ i : Fin N, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) +
      β ^ 2 * s * rv *
          ((∑ i : Fin N, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
           sign * (∑ i : Fin N, SpinGlass.spin N p.1 i * SpinGlass.spin N r.2 i) +
           sign * (∑ i : Fin N, SpinGlass.spin N p.2 i * SpinGlass.spin N r.1 i) +
           sign ^ 2 * (∑ i : Fin N, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) +
      β ^ 2 * s * (q - rv) *
          ((∑ i : Fin N, SpinGlass.spin N p.1 i * SpinGlass.spin N r.1 i) +
           (∑ i : Fin N, SpinGlass.spin N p.2 i * SpinGlass.spin N r.2 i)) by
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  simp_rw [spin_sum_eq_mul_overlap hN]
  simp only [pairOverlapMatrix, pairConfig, Fin.sum_univ_two]
  unfold gtCovarianceMatrix signedMatrixPath
  simp only [min_eq_right hrq, Matrix.add_apply, Matrix.smul_apply]
  rw [hsignsq]
  simp [sign, rv, hsignrv, habssign]
  conv_rhs => rw [← habssign]
  ring

/-- Square completion for the ordinary branch, with the scalar term kept as a
state-independent covariance shift. -/
lemma gtOrdinary_covariance_square_completion
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hrq : |v| ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
        (gtOrdinaryBarePhysicalCoefficient N β q s r) +
      (N : ℝ) * gtScalarVariance β s v q -
      inner ℝ (gtOrdinaryTrialCoefficient N β q s v p)
        (gtOrdinaryTrialCoefficient N β q s v r) =
      (N : ℝ) * (s * β ^ 2 / 2) *
        ∑ a : Fin 2, ∑ b : Fin 2,
          (pairOverlapMatrix p r a b - signedMatrixPath v q a b) ^ 2 := by
  rw [gtOrdinaryBarePhysicalCoefficient_inner hN hs hq0,
    gtOrdinaryTrialCoefficient_inner hN hs hq0 hrq,
    gtScalarVariance_eq_matrix_sum hq0]
  unfold gtCovarianceFunction gtCovarianceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_two]
  norm_num
  ring

lemma gtOrdinary_covariance_shifted_order
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hrq : |v| ≤ q)
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    inner ℝ (gtOrdinaryTrialCoefficient N β q s v p)
        (gtOrdinaryTrialCoefficient N β q s v r) ≤
      inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p)
        (gtOrdinaryBarePhysicalCoefficient N β q s r) +
      (N : ℝ) * gtScalarVariance β s v q := by
  have hsβ : 0 ≤ s * β ^ 2 / 2 :=
    div_nonneg (mul_nonneg hs.1 (sq_nonneg β)) (by norm_num)
  have hsum : 0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      (pairOverlapMatrix p r a b - signedMatrixPath v q a b) ^ 2 := by
    positivity
  have hNr : 0 ≤ (N : ℝ) := by positivity
  have hnonneg : 0 ≤ (N : ℝ) * (s * β ^ 2 / 2) *
      ∑ a : Fin 2, ∑ b : Fin 2,
        (pairOverlapMatrix p r a b - signedMatrixPath v q a b) ^ 2 :=
    mul_nonneg (mul_nonneg hNr hsβ) hsum
  have heq := gtOrdinary_covariance_square_completion
    (N := N) (β := β) hN hs hq0 hrq p r
  linarith

lemma gtOrdinary_self_variance_difference
    {N : ℕ} (hN : 0 < N) {β q s v : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hrq : |v| ≤ q) (hv : v ∈ attainableOverlaps N)
    (p : ConstrainedPair N v) :
    inner ℝ (gtOrdinaryBarePhysicalCoefficient N β q s p.1)
        (gtOrdinaryBarePhysicalCoefficient N β q s p.1) -
      inner ℝ (gtOrdinaryTrialCoefficient N β q s v p.1)
        (gtOrdinaryTrialCoefficient N β q s v p.1) =
      (N : ℝ) * (s * β ^ 2 * (1 - q) ^ 2) -
        (N : ℝ) * gtScalarVariance β s v q := by
  have hsq := gtOrdinary_covariance_square_completion
    (N := N) (β := β) hN hs hq0 hrq p.1 p.1
  rw [pairOverlapMatrix_self_eq_signedMatrixPath_one hN hv p] at hsq
  have hv1 : |v| ≤ 1 := abs_le.2 (gtAttainableOverlap_mem_Icc hN hv)
  have hmatrix :
      (∑ a : Fin 2, ∑ b : Fin 2,
        (signedMatrixPath v 1 a b - signedMatrixPath v q a b) ^ 2) =
        2 * (1 - q) ^ 2 := by
    unfold signedMatrixPath
    simp only [min_eq_right hv1, min_eq_right hrq, Fin.sum_univ_two]
    rw [gtPathSign_mul_abs]
    norm_num
    ring
  rw [hmatrix] at hsq
  nlinarith

noncomputable def gtConstrainedOrdinaryPressure
    (N : ℕ) (β h q s v lam : ℝ) (hv : v ∈ attainableOverlaps N)
    (t : ℝ) : ℝ := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  exact gtOrdinaryPressure
    (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
    (fun p : ConstrainedPair N v =>
      gtOrdinaryBarePhysicalCoefficient N β q s p.1)
    (fun p : ConstrainedPair N v =>
      gtOrdinaryTrialCoefficient N β q s v p.1)
    0 t

noncomputable def gtUnconstrainedOrdinaryPressure
    (N : ℕ) (β h q s v lam t : ℝ) : ℝ :=
  gtOrdinaryPressure
    (fun p : SpinGlass.Config N × SpinGlass.Config N =>
      gtPairPotential N h lam v p)
    (fun p : SpinGlass.Config N × SpinGlass.Config N =>
      gtOrdinaryBarePhysicalCoefficient N β q s p)
    (fun p : SpinGlass.Config N × SpinGlass.Config N =>
      gtOrdinaryTrialCoefficient N β q s v p)
    0 t

lemma gtOrdinaryPhysical_stateLogPartition_eq_canonical
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (pnonempty : v ∈ attainableOverlaps N)
    (z : GTOrdinaryIndex N → ℝ) :
    gtStateLogPartition
        (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
        (gtOrdinaryField
          (fun p : ConstrainedPair N v =>
            gtOrdinaryBarePhysicalCoefficient N β q s p.1)
          (fun p : ConstrainedPair N v =>
            gtOrdinaryTrialCoefficient N β q s v p.1)
          0 1 (WithLp.toLp 2 z)) =
      coupledConstrainedLogPartition N β h q s v
        (WithLp.toLp 2 (fun j : CoupledGaussianIndex N => z (Sum.inl j))) := by
  classical
  letI := constrainedPair_nonempty pnonempty
  unfold gtOrdinaryField
  simp only [Real.sqrt_one, one_smul, sub_self, Real.sqrt_zero, zero_smul,
    add_zero]
  unfold gtStateLogPartition gtStatePartition coupledConstrainedLogPartition
  rw [constrainedPartition_eq_sum_constrainedPair]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [gtCoefficientCLM_apply]
  unfold gtOrdinaryBarePhysicalCoefficient gtPairPhysicalCoefficient
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [RCLike.inner_apply, conj_trivial, mul_zero, Finset.sum_const_zero,
    add_zero]
  simp only [gtPairPotential, coupledCoordinateHamiltonian, PiLp.add_apply,
    PiLp.toLp_apply]
  have hlam : lam * ((∑ i : Fin N,
      SpinGlass.spin N p.1.1 i * SpinGlass.spin N p.1.2 i) -
        (N : ℝ) * v) = 0 := by
    rw [spin_sum_eq_mul_overlap hN, p.2]
    ring
  rw [hlam]
  simp only [add_zero]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, PiLp.toLp_apply]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

lemma gtOrdinaryPressure_one_eq_canonical
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ attainableOverlaps N) :
    gtConstrainedOrdinaryPressure N β h q s v lam hv 1 =
      ∫ x, coupledConstrainedLogPartition N β h q s v x
        ∂SYK.standardGaussianMeasureOnEuclidean (CoupledGaussianIndex N) := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedOrdinaryPressure gtOrdinaryPressure
  simp_rw [gtOrdinaryPhysical_stateLogPartition_eq_canonical hN hv]
  let f : (CoupledGaussianIndex N → ℝ) → ℝ := fun z =>
    coupledConstrainedLogPartition N β h q s v (WithLp.toLp 2 z)
  have hf : AEStronglyMeasurable f
      (Measure.pi (fun _ : CoupledGaussianIndex N => gaussianReal 0 1)) := by
    exact ((coupled_constrained_log_partition_lipschitz N β h q s v
      hN hs hq hv).continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
  rw [integral_gaussianProduct_restrict
    (fun j : CoupledGaussianIndex N => (Sum.inl j : GTOrdinaryIndex N))
    (by intro a b hab; exact Sum.inl.inj hab) f hf]
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [integral_map (by fun_prop)
    ((coupled_constrained_log_partition_lipschitz N β h q s v
      hN hs hq hv).continuous.aestronglyMeasurable)]

lemma gtConstrainedOrdinaryPressure_one_le_zero
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq0 : 0 ≤ q)
    (hrq : |v| ≤ q) (hv : v ∈ attainableOverlaps N) :
    gtConstrainedOrdinaryPressure N β h q s v lam hv 1 ≤
      gtConstrainedOrdinaryPressure N β h q s v lam hv 0 +
        (N : ℝ) * (s * β ^ 2 * (1 - q) ^ 2) / 2 := by
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedOrdinaryPressure
  exact gtOrdinaryPressure_one_le_zero_add_shiftedDiagonalGap
    (V := fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
    (H₀ := 0)
    (hAB := fun p r =>
      gtOrdinaryBare_coefficients_orthogonal N β q s v p.1 r.1)
    (shift := (N : ℝ) * gtScalarVariance β s v q)
    (gap := (N : ℝ) * (s * β ^ 2 * (1 - q) ^ 2))
    (hdiag := fun p => gtOrdinary_self_variance_difference
      (N := N) (β := β) hN hs hq0 hrq hv p)
    (hcov := fun p r => gtOrdinary_covariance_shifted_order
      (N := N) (β := β) hN hs hq0 hrq p.1 r.1)

lemma gtConstrainedOrdinaryPressure_zero_le_unconstrained
    {N : ℕ} {β h q s v lam : ℝ} (hv : v ∈ attainableOverlaps N) :
    gtConstrainedOrdinaryPressure N β h q s v lam hv 0 ≤
      gtUnconstrainedOrdinaryPressure N β h q s v lam 0 := by
  classical
  letI : Nonempty (ConstrainedPair N v) := constrainedPair_nonempty hv
  unfold gtConstrainedOrdinaryPressure gtUnconstrainedOrdinaryPressure
  unfold gtOrdinaryPressure
  apply integral_mono
  · exact integrable_gtStateLogPartition_gtOrdinaryField
      (fun p : ConstrainedPair N v => gtPairPotential N h lam v p.1)
      (fun p : ConstrainedPair N v =>
        gtOrdinaryBarePhysicalCoefficient N β q s p.1)
      (fun p : ConstrainedPair N v =>
        gtOrdinaryTrialCoefficient N β q s v p.1) 0 0
  · exact integrable_gtStateLogPartition_gtOrdinaryField
      (fun p : SpinGlass.Config N × SpinGlass.Config N =>
        gtPairPotential N h lam v p)
      (fun p : SpinGlass.Config N × SpinGlass.Config N =>
        gtOrdinaryBarePhysicalCoefficient N β q s p)
      (fun p : SpinGlass.Config N × SpinGlass.Config N =>
        gtOrdinaryTrialCoefficient N β q s v p) 0 0
  · intro z
    unfold gtStateLogPartition
    apply Real.log_le_log
    · exact gtStatePartition_pos _ _
    · unfold gtStatePartition
      simp only [gtOrdinaryField, Real.sqrt_zero, zero_smul, sub_zero,
        Real.sqrt_one, one_smul, zero_add, add_zero, gtCoefficientCLM_apply]
      rw [← Finset.sum_subtype
        (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
          SpinGlass.overlap N p.1 p.2 = v)
        (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
          SpinGlass.overlap N p.1 p.2 = v) (by simp)
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          Real.exp (inner ℝ (gtOrdinaryTrialCoefficient N β q s v p)
            (WithLp.toLp 2 z) + gtPairPotential N h lam v p))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Real.exp_nonneg _)

/-- At the independent endpoint, the unrestricted finite-state partition is
the product of the local two-spin terminal partitions. -/
lemma gtUnconstrainedOrdinary_zero_integrand_eq_terminal_sum
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (z : GTOrdinaryIndex N → ℝ) :
    gtStateLogPartition
        (fun p : SpinGlass.Config N × SpinGlass.Config N =>
          gtPairPotential N h lam v p)
        (gtOrdinaryField
          (fun p : SpinGlass.Config N × SpinGlass.Config N =>
            gtOrdinaryBarePhysicalCoefficient N β q s p)
          (fun p : SpinGlass.Config N × SpinGlass.Config N =>
            gtOrdinaryTrialCoefficient N β q s v p)
          0 0 (WithLp.toLp 2 z)) =
      2 * (N : ℝ) * Real.log 2 +
        ∑ i : Fin N,
          gtTerminal lam
            (gtOrdinaryTrialFieldOne N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i)
            (gtOrdinaryTrialFieldTwo N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i) -
        lam * (N : ℝ) * v := by
  classical
  have hpart :
      gtStatePartition
          (fun p : SpinGlass.Config N × SpinGlass.Config N =>
            gtPairPotential N h lam v p)
          (gtOrdinaryField
            (fun p : SpinGlass.Config N × SpinGlass.Config N =>
              gtOrdinaryBarePhysicalCoefficient N β q s p)
            (fun p : SpinGlass.Config N × SpinGlass.Config N =>
              gtOrdinaryTrialCoefficient N β q s v p)
            0 0 (WithLp.toLp 2 z)) =
        pairFieldPartition N lam v
          (gtOrdinaryTrialFieldOne N β h q s v
            (fun ij => z (Sum.inr (Sum.inr ij))))
          (gtOrdinaryTrialFieldTwo N β h q s v
            (fun ij => z (Sum.inr (Sum.inr ij)))) := by
    unfold gtStatePartition pairFieldPartition gtOrdinaryField
    simp only [Real.sqrt_zero, zero_smul, sub_zero, Real.sqrt_one, one_smul,
      zero_add, add_zero, gtCoefficientCLM_apply]
    apply Finset.sum_congr rfl
    intro p _
    apply congrArg Real.exp
    rw [PiLp.inner_apply]
    simp only [gtOrdinaryTrialCoefficient, RCLike.inner_apply, conj_trivial,
      PiLp.toLp_apply, gtPairPotential, gtOrdinaryTrialFieldOne,
      gtOrdinaryTrialFieldTwo]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_sum_type]
    simp only [mul_zero, Finset.sum_const_zero, zero_add]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) = 0 by rfl, if_true,
      show (1 : Fin 4) ≠ 0 by decide, if_false,
      show (1 : Fin 4) = 1 by rfl,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
      show (2 : Fin 4) = 2 by rfl,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
    repeat rw [← Finset.sum_add_distrib]
    apply add_left_cancel (a := lam * (N : ℝ) * v)
    ring_nf
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold gtStateLogPartition
  rw [hpart, log_pairFieldPartition]

/-- A terminal function evaluated along two affine finite-dimensional Gaussian
fields is integrable.  Keeping this lemma in coefficient-vector form avoids
repeating coordinatewise Gaussian estimates in the endpoint calculation. -/
lemma integrable_gtTerminal_affine_gaussianProduct
    {I : Type*} [Fintype I]
    (lam x₁ x₂ : ℝ) (c₁ c₂ : EuclideanSpace ℝ I) :
    Integrable (fun z : I → ℝ =>
      gtTerminal lam
        (x₁ + inner ℝ c₁ (WithLp.toLp 2 z))
        (x₂ + inner ℝ c₂ (WithLp.toLp 2 z)))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  let C : ℝ := ‖c₁‖ + ‖c₂‖
  let M : ℝ := |gtTerminal lam x₁ x₂|
  let bound : (I → ℝ) → ℝ := fun z =>
    M + C * ‖(WithLp.toLp 2 z : EuclideanSpace ℝ I)‖
  have hbound : Integrable bound
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    have hn := integrable_norm_gaussianProduct (I := I)
    simpa [bound] using (integrable_const M).add (hn.const_mul C)
  apply hbound.mono
  · have hmap : Continuous (fun z : I → ℝ =>
        (lam, (x₁ + inner ℝ c₁ (WithLp.toLp 2 z),
          x₂ + inner ℝ c₂ (WithLp.toLp 2 z)))) := by
      fun_prop
    exact (GTFrame.continuous_fLbase.comp hmap).aestronglyMeasurable
  · filter_upwards with z
    let zE : EuclideanSpace ℝ I := WithLp.toLp 2 z
    have hlip := GTFrame.fLbase_lipx lam
      (x₁ + inner ℝ c₁ zE, x₂ + inner ℝ c₂ zE) (x₁, x₂)
    have hc₁ : |inner ℝ c₁ zE| ≤ ‖c₁‖ * ‖zE‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm c₁ zE
    have hc₂ : |inner ℝ c₂ zE| ≤ ‖c₂‖ * ‖zE‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm c₂ zE
    have habs := abs_sub_abs_le_abs_sub
      (gtTerminal lam (x₁ + inner ℝ c₁ zE)
        (x₂ + inner ℝ c₂ zE))
      (gtTerminal lam x₁ x₂)
    rw [Real.norm_eq_abs]
    dsimp [bound, M, C]
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
      (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)))]
    have hfield₁ :
        |(x₁ + inner ℝ c₁ zE) - x₁| = |inner ℝ c₁ zE| := by
      ring_nf
    have hfield₂ :
        |(x₂ + inner ℝ c₂ zE) - x₂| = |inner ℝ c₂ zE| := by
      ring_nf
    rw [hfield₁, hfield₂] at hlip
    nlinarith [norm_nonneg c₁, norm_nonneg c₂, norm_nonneg zE]

/-- An additive constant may be pulled through the four scalar Gaussian
expectations used by the explicit ordinary endpoint. -/
lemma integral_gaussianFour_const_add_gtTerminal
    (c lam x₁ x₂ a₀ a₁ a₂ b₀ b₁ b₃ : ℝ) :
    (∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
      c + gtTerminal lam
        (x₁ + a₀ * z₀ + a₁ * z₁ + a₂ * z₂)
        (x₂ + b₀ * z₀ + b₁ * z₁ + b₃ * z₃)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1
      ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      c + ∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
        gtTerminal lam
          (x₁ + a₀ * z₀ + a₁ * z₁ + a₂ * z₂)
          (x₂ + b₀ * z₀ + b₁ * z₁ + b₃ * z₃)
        ∂gaussianReal 0 1 ∂gaussianReal 0 1
        ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  let g : (Fin 4 → ℝ) → ℝ := fun z =>
    gtTerminal lam
      (x₁ + a₀ * z 0 + a₁ * z 1 + a₂ * z 2)
      (x₂ + b₀ * z 0 + b₁ * z 1 + b₃ * z 3)
  let c₁ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![a₀, a₁, a₂, 0]
  let c₂ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![b₀, b₁, 0, b₃]
  have hg : Integrable g
      (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := by
    have hi := integrable_gtTerminal_affine_gaussianProduct lam x₁ x₂ c₁ c₂
    apply hi.congr
    filter_upwards with z
    dsimp [g, c₁, c₂]
    simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
      conj_trivial, PiLp.toLp_apply]
    apply congrArg₂ (gtTerminal lam) <;>
      simp [Fin.sum_univ_four] <;> ring
  have hcg : Integrable (fun z => c + g z)
      (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) :=
    (integrable_const c).add hg
  calc
    _ = ∫ z : Fin 4 → ℝ, c + g z
          ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
        simpa [g] using
          (integral_gaussianFinFour_eq_iterated (fun z => c + g z) hcg).symm
    _ = (∫ _z : Fin 4 → ℝ, c
          ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) +
        ∫ z : Fin 4 → ℝ, g z
          ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
        exact integral_add (integrable_const c) hg
    _ = c + ∫ z : Fin 4 → ℝ, g z
          ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by simp
    _ = _ := by
      rw [integral_gaussianFinFour_eq_iterated g hg]
      rfl

/-- Three-dimensional version of
`integral_gaussianFour_const_add_gtTerminal`. -/
lemma integral_gaussianThree_const_add_gtTerminal
    (c lam x₁ x₂ a₀ a₁ b₀ b₂ : ℝ) :
    (∫ z₀, ∫ z₁, ∫ z₂,
      c + gtTerminal lam
        (x₁ + a₀ * z₀ + a₁ * z₁)
        (x₂ + b₀ * z₀ + b₂ * z₂)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      c + ∫ z₀, ∫ z₁, ∫ z₂,
        gtTerminal lam
          (x₁ + a₀ * z₀ + a₁ * z₁)
          (x₂ + b₀ * z₀ + b₂ * z₂)
        ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  simpa using integral_gaussianFour_const_add_gtTerminal
    c lam x₁ x₂ a₀ a₁ 0 b₀ 0 b₂

lemma integral_gaussianFour_gtTerminal_add_const
    (c lam x₁ x₂ a₀ a₁ a₂ b₀ b₁ b₃ : ℝ) :
    (∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
      gtTerminal lam
        (x₁ + a₀ * z₀ + a₁ * z₁ + a₂ * z₂)
        (x₂ + b₀ * z₀ + b₁ * z₁ + b₃ * z₃) + c
      ∂gaussianReal 0 1 ∂gaussianReal 0 1
      ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      (∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
        gtTerminal lam
          (x₁ + a₀ * z₀ + a₁ * z₁ + a₂ * z₂)
          (x₂ + b₀ * z₀ + b₁ * z₁ + b₃ * z₃)
        ∂gaussianReal 0 1 ∂gaussianReal 0 1
        ∂gaussianReal 0 1 ∂gaussianReal 0 1) + c := by
  simpa [add_comm] using integral_gaussianFour_const_add_gtTerminal
    c lam x₁ x₂ a₀ a₁ a₂ b₀ b₁ b₃

lemma integral_gaussianThree_gtTerminal_add_const
    (c lam x₁ x₂ a₀ a₁ b₀ b₂ : ℝ) :
    (∫ z₀, ∫ z₁, ∫ z₂,
      gtTerminal lam
        (x₁ + a₀ * z₀ + a₁ * z₁)
        (x₂ + b₀ * z₀ + b₂ * z₂) + c
      ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      (∫ z₀, ∫ z₁, ∫ z₂,
        gtTerminal lam
          (x₁ + a₀ * z₀ + a₁ * z₁)
          (x₂ + b₀ * z₀ + b₂ * z₂)
        ∂gaussianReal 0 1 ∂gaussianReal 0 1 ∂gaussianReal 0 1) + c := by
  simpa [add_comm] using integral_gaussianThree_const_add_gtTerminal
    c lam x₁ x₂ a₀ a₁ b₀ b₂

/-- Explicit four-scalar Gaussian formula for the unrestricted ordinary
trial endpoint. -/
lemma gtUnconstrainedOrdinaryPressure_zero_eq_four_integrals
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ} :
    gtUnconstrainedOrdinaryPressure N β h q s v lam 0 =
      2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v +
        (N : ℝ) * ∫ z₀, ∫ z₁, ∫ z₂, ∫ z₃,
          gtTerminal lam
            (h + β * Real.sqrt ((1 - s) * q) * z₀ +
              gtIncrementScale β s 0 |v| * z₁ +
              gtIncrementScale β s |v| q * z₂)
            (h + β * Real.sqrt ((1 - s) * q) * z₀ +
              gtPathSign v * gtIncrementScale β s 0 |v| * z₁ +
              gtIncrementScale β s |v| q * z₃)
          ∂gaussianReal 0 1 ∂gaussianReal 0 1
          ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  classical
  let μ := Measure.pi (fun _ : GTOrdinaryIndex N => gaussianReal 0 1)
  let g : (Fin 4 → ℝ) → ℝ := fun z =>
    gtTerminal lam
      (h + β * Real.sqrt ((1 - s) * q) * z 0 +
        gtIncrementScale β s 0 |v| * z 1 +
        gtIncrementScale β s |v| q * z 2)
      (h + β * Real.sqrt ((1 - s) * q) * z 0 +
        gtPathSign v * gtIncrementScale β s 0 |v| * z 1 +
        gtIncrementScale β s |v| q * z 3)
  have hfour : Integrable g
      (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := by
    let c₁ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2
      ![β * Real.sqrt ((1 - s) * q), gtIncrementScale β s 0 |v|,
        gtIncrementScale β s |v| q, 0]
    let c₂ : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2
      ![β * Real.sqrt ((1 - s) * q),
        gtPathSign v * gtIncrementScale β s 0 |v|, 0,
        gtIncrementScale β s |v| q]
    have hi := integrable_gtTerminal_affine_gaussianProduct lam h h c₁ c₂
    apply hi.congr
    filter_upwards with z
    dsimp [g, c₁, c₂]
    simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply,
      conj_trivial, PiLp.toLp_apply]
    apply congrArg₂ (gtTerminal lam) <;>
      simp [Fin.sum_univ_four] <;> ring
  let f : Fin N → (GTOrdinaryIndex N → ℝ) → ℝ := fun i z =>
    gtTerminal lam
      (gtOrdinaryTrialFieldOne N β h q s v
        (fun ij => z (Sum.inr (Sum.inr ij))) i)
      (gtOrdinaryTrialFieldTwo N β h q s v
        (fun ij => z (Sum.inr (Sum.inr ij))) i)
  have hf (i : Fin N) : Integrable (f i) μ := by
    let e : Fin 4 → GTOrdinaryIndex N := fun a => Sum.inr (Sum.inr (i, a))
    have he : Function.Injective e := by
      intro a b hab
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hab))
    let φ : (GTOrdinaryIndex N → ℝ) → (Fin 4 → ℝ) := fun z a => z (e a)
    have hmp : MeasurePreserving φ μ
        (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := by
      refine ⟨by fun_prop, ?_⟩
      simpa [φ, μ] using gaussianProduct_restrict_map e he
    have hc : Integrable (fun z : GTOrdinaryIndex N → ℝ => g (φ z)) μ :=
      (hmp.integrable_comp hfour.1).2 hfour
    simpa [f, g, e, gtOrdinaryTrialFieldOne,
      gtOrdinaryTrialFieldTwo, φ] using hc
  unfold gtUnconstrainedOrdinaryPressure gtOrdinaryPressure
  simp_rw [gtUnconstrainedOrdinary_zero_integrand_eq_terminal_sum hN]
  have hpoint (z : GTOrdinaryIndex N → ℝ) :
      2 * (N : ℝ) * Real.log 2 +
          ∑ i, gtTerminal lam
            (gtOrdinaryTrialFieldOne N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i)
            (gtOrdinaryTrialFieldTwo N β h q s v
              (fun ij => z (Sum.inr (Sum.inr ij))) i) -
        lam * (N : ℝ) * v =
      (2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v) + ∑ i, f i z := by
    dsimp [f]
    ring
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  change (∫ z, (2 * (N : ℝ) * Real.log 2 - lam * (N : ℝ) * v) +
      ∑ i, f i z ∂μ) = _
  rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => hf i)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul]
  rw [integral_finset_sum Finset.univ (fun i _ => hf i)]
  have hone (i : Fin N) :
      (∫ z, f i z ∂μ) =
        ∫ z : Fin 4 → ℝ, g z
          ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1) := by
    let e : Fin 4 → GTOrdinaryIndex N := fun a => Sum.inr (Sum.inr (i, a))
    have hg : AEStronglyMeasurable g
        (Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)) := hfour.1
    have he : Function.Injective e := by
      intro a b hab
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hab))
    have hr := integral_gaussianProduct_restrict e
      he g hg
    simpa [μ, f, e, g, gtOrdinaryTrialFieldOne,
      gtOrdinaryTrialFieldTwo] using hr
  simp_rw [hone]
  rw [integral_gaussianFinFour_eq_iterated g hfour]
  dsimp [g]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The ordinary trial endpoint, together with its interpolation diagonal
remainder, is exactly the finite GT functional in the branch `|v| < q`. -/
lemma gtUnconstrainedOrdinaryPressure_zero_add_gap_eq_gtFunctional
    {N : ℕ} (hN : 0 < N) {β h q s v lam : ℝ}
    (hs0 : 0 ≤ s) (hq0 : 0 < q) (hq1 : q ≤ 1) (hrq : |v| < q) :
    gtUnconstrainedOrdinaryPressure N β h q s v lam 0 +
        (N : ℝ) * (s * β ^ 2 * (1 - q) ^ 2) / 2 =
      (N : ℝ) * gtFunctional β h q s lam v := by
  rw [gtUnconstrainedOrdinaryPressure_zero_eq_four_integrals hN]
  have hscale :
      gtIncrementScale β s q 1 ^ 2 = β ^ 2 * s * (1 - q) :=
    gtIncrementScale_sq hs0 hq1
  have hupper (x₁ x₂ : ℝ) :
      gtDiagonalStep 1 (gtIncrementScale β s q 1) (gtTerminal lam) x₁ x₂ =
        gtTerminal lam x₁ x₂ + β ^ 2 * s * (1 - q) := by
    rw [gtDiagonalStep_one_terminal, hscale]
  have hupper_fun :
      gtDiagonalStep 1 (gtIncrementScale β s q 1) (gtTerminal lam) =
        fun x₁ x₂ => gtTerminal lam x₁ x₂ + β ^ 2 * s * (1 - q) := by
    funext x₁ x₂
    exact hupper x₁ x₂
  by_cases hvzero : |v| = 0
  · rw [gtFunctional_formula_abs_v_eq_zero β h q s lam v hq0 hvzero]
    have hv : v = 0 := abs_eq_zero.mp hvzero
    subst v
    rw [hupper_fun]
    simp only [gtDiagonalStep, gtRankOneStep, zero_ne_one, if_false,
      if_pos rfl, gtIncrementScale, sub_self, Real.sqrt_zero, mul_zero,
      add_zero, standardGaussianExpectation, if_true]
    simp only [abs_zero, Real.sqrt_zero, mul_zero, zero_mul, add_zero, sub_zero]
    rw [integral_gaussianThree_gtTerminal_add_const]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      one_smul]
    unfold gtCorrection
    ring
  · have hvpos : 0 < |v| := lt_of_le_of_ne (abs_nonneg v) (Ne.symm hvzero)
    rw [gtFunctional_formula_abs_v_lt_q β h q s lam v hvpos hrq]
    rw [hupper_fun]
    simp only [gtRankOneStep, gtDiagonalStep, if_pos rfl,
      standardGaussianExpectation, if_true]
    rw [integral_gaussianFour_gtTerminal_add_const]
    unfold gtCorrection
    ring

end SpinGlass.AT
