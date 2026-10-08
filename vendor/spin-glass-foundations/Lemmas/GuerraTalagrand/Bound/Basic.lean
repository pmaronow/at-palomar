module

public import Lemmas.AT.Definitions

@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

lemma gt_integrable_log_sum_exp
    {Ω I : Type*} [MeasureSpace Ω] [IsFiniteMeasure (volume : Measure Ω)]
    [Fintype I] [Nonempty I]
    (F : I → Ω → ℝ) (hF : ∀ i, Integrable (F i)) :
    Integrable (fun ω => Real.log (∑ i, Real.exp (F i ω))) := by
  let A : Ω → ℝ := fun ω => ∑ i, |F i ω|
  have hA : Integrable A := integrable_finsetSum Finset.univ fun i _ => (hF i).abs
  have hmeas : AEStronglyMeasurable
      (fun ω => Real.log (∑ i, Real.exp (F i ω))) :=
    ((Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
      (hF i).aemeasurable.exp).log).aestronglyMeasurable
  have hcard : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hlogcard : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hcard
  refine (hA.add (integrable_const (Real.log (Fintype.card I : ℝ)))).mono' hmeas ?_
  filter_upwards [] with ω
  have hsumpos : 0 < ∑ i, Real.exp (F i ω) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hupper : Real.log (∑ i, Real.exp (F i ω)) ≤
      Real.log (Fintype.card I : ℝ) + A ω := by
    have hsum : (∑ i, Real.exp (F i ω)) ≤
        (Fintype.card I : ℝ) * Real.exp (A ω) := by
      calc
        (∑ i, Real.exp (F i ω)) ≤ ∑ _i : I, Real.exp (A ω) := by
          apply Finset.sum_le_sum
          intro i _
          apply Real.exp_le_exp.mpr
          exact (le_abs_self _).trans (Finset.single_le_sum
            (fun j _ => abs_nonneg (F j ω)) (Finset.mem_univ i))
        _ = _ := by simp
    have hlog := Real.log_le_log hsumpos hsum
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
    exact hlog
  let i₀ : I := Classical.choice inferInstance
  have hlower : -(A ω) ≤ Real.log (∑ i, Real.exp (F i ω)) := by
    have hone : Real.exp (F i₀ ω) ≤ ∑ i, Real.exp (F i ω) :=
      Finset.single_le_sum (fun i _ => Real.exp_nonneg (F i ω))
        (Finset.mem_univ i₀)
    have hlog := Real.log_le_log (Real.exp_pos _) hone
    rw [Real.log_exp] at hlog
    have hFi : -(A ω) ≤ F i₀ ω := by
      have hi := Finset.single_le_sum (fun j _ => abs_nonneg (F j ω))
        (Finset.mem_univ i₀)
      exact (neg_le_neg hi).trans (neg_abs_le (F i₀ ω))
    exact hFi.trans hlog
  rw [Real.norm_eq_abs]
  change |Real.log (∑ i, Real.exp (F i ω))| ≤
    A ω + Real.log (Fintype.card I : ℝ)
  apply abs_le.mpr
  constructor <;> linarith

/-- A constrained pair, represented without an indicator function. -/
abbrev ConstrainedPair (N : ℕ) (v : ℝ) :=
  {p : SpinGlass.Config N × SpinGlass.Config N //
    SpinGlass.overlap N p.1 p.2 = v}

lemma constrainedPair_nonempty {N : ℕ} {v : ℝ}
    (hv : v ∈ attainableOverlaps N) : Nonempty (ConstrainedPair N v) := by
  classical
  rw [attainableOverlaps, Finset.mem_image] at hv
  obtain ⟨p, _hp, hpv⟩ := hv
  exact ⟨⟨p, hpv⟩⟩

/-- Rewrite the indicator-form constrained partition function as a subtype sum. -/
lemma constrainedPartition_eq_sum_constrainedPair
    {N : ℕ} (H : SpinGlass.EnergySpace N) (v : ℝ) :
    constrainedPartition H v =
      ∑ p : ConstrainedPair N v,
        Real.exp (-(H p.1.1 + H p.1.2)) := by
  classical
  unfold constrainedPartition
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.overlap N p.1 p.2 = v)
    (Finset.univ.filter fun p : SpinGlass.Config N × SpinGlass.Config N =>
      SpinGlass.overlap N p.1 p.2 = v) (by simp)]

lemma constrainedPartition_pos_of_attainable
    {N : ℕ} (H : SpinGlass.EnergySpace N) {v : ℝ}
    (hv : v ∈ attainableOverlaps N) :
    0 < constrainedPartition H v := by
  classical
  rw [constrainedPartition_eq_sum_constrainedPair]
  letI := constrainedPair_nonempty hv
  exact Finset.sum_pos' (fun p _ => (Real.exp_pos _).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩

/-- The unnormalized spin product sum equals `N` times the overlap. -/
lemma spin_sum_eq_mul_overlap
    {N : ℕ} (hN : 0 < N) (σ τ : SpinGlass.Config N) :
    (∑ i : Fin N, SpinGlass.spin N σ i * SpinGlass.spin N τ i) =
      (N : ℝ) * SpinGlass.overlap N σ τ := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold SpinGlass.overlap
  field_simp

/-- The Lagrange contribution vanishes on the constrained pair subtype. -/
lemma lagrange_term_eq_zero
    {N : ℕ} (hN : 0 < N) {v lam : ℝ} (p : ConstrainedPair N v) :
    lam * (∑ i : Fin N,
      SpinGlass.spin N p.1.1 i * SpinGlass.spin N p.1.2 i) -
        lam * (N : ℝ) * v = 0 := by
  rw [spin_sum_eq_mul_overlap hN, p.2]
  ring

/-- Lagrange relaxation of the overlap constraint, before taking logarithms. -/
lemma constrainedPartition_le_lagrange_sum
    {N : ℕ} (hN : 0 < N) (H : SpinGlass.EnergySpace N)
    (v lam : ℝ) :
    constrainedPartition H v ≤
      ∑ p : SpinGlass.Config N × SpinGlass.Config N,
        Real.exp (-(H p.1 + H p.2) +
          lam * ((∑ i : Fin N,
            SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i) -
              (N : ℝ) * v)) := by
  classical
  unfold constrainedPartition
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : SpinGlass.overlap N p.1 p.2 = v
  · rw [if_pos hp]
    have hz : (∑ i : Fin N,
        SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i) -
          (N : ℝ) * v = 0 := by
      rw [spin_sum_eq_mul_overlap hN, hp]
      ring
    simp [hz]
  · rw [if_neg hp]
    positivity

lemma log_constrainedPartition_le_log_lagrange_sum
    {N : ℕ} (hN : 0 < N) (H : SpinGlass.EnergySpace N)
    {v : ℝ} (hv : v ∈ attainableOverlaps N) (lam : ℝ) :
    Real.log (constrainedPartition H v) ≤
      Real.log (∑ p : SpinGlass.Config N × SpinGlass.Config N,
        Real.exp (-(H p.1 + H p.2) +
          lam * ((∑ i : Fin N,
            SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i) -
              (N : ℝ) * v))) := by
  apply Real.log_le_log (constrainedPartition_pos_of_attainable H hv)
  exact constrainedPartition_le_lagrange_sum hN H v lam

/-- Pairing two configuration functions site by site. -/
def pairConfigEquiv (N : ℕ) :
    (SpinGlass.Config N × SpinGlass.Config N) ≃ (Fin N → Bool × Bool) where
  toFun p i := (p.1 i, p.2 i)
  invFun bs := (fun i => (bs i).1, fun i => (bs i).2)
  left_inv p := by ext <;> rfl
  right_inv bs := by ext <;> rfl

/-- A finite sum whose exponent is additive over sites factorizes sitewise. -/
lemma sum_pair_exp_sum_eq_prod_sum_exp
    {N : ℕ} (f : Fin N → Bool × Bool → ℝ) :
    (∑ p : SpinGlass.Config N × SpinGlass.Config N,
      Real.exp (∑ i, f i (p.1 i, p.2 i))) =
      ∏ i : Fin N, ∑ b : Bool × Bool, Real.exp (f i b) := by
  classical
  calc
    (∑ p : SpinGlass.Config N × SpinGlass.Config N,
        Real.exp (∑ i, f i (p.1 i, p.2 i))) =
      ∑ bs : Fin N → Bool × Bool,
        Real.exp (∑ i, f i (bs i)) := by
      apply Fintype.sum_equiv (pairConfigEquiv N)
      intro p
      rfl
    _ = ∑ bs : Fin N → Bool × Bool,
        ∏ i, Real.exp (f i (bs i)) := by
      apply Finset.sum_congr rfl
      intro bs _
      rw [Real.exp_sum]
    _ = _ := (Fintype.prod_sum (fun i b => Real.exp (f i b))).symm

/-- Every attainable overlap is between `-1` and `1`. -/
lemma gtAttainableOverlap_mem_Icc
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

lemma overlap_comm {N : ℕ} (σ τ : SpinGlass.Config N) :
    SpinGlass.overlap N σ τ = SpinGlass.overlap N τ σ := by
  unfold SpinGlass.overlap
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Select one of the two configurations in a pair. -/
def pairConfig {N : ℕ}
    (p : SpinGlass.Config N × SpinGlass.Config N) (a : Fin 2) :
    SpinGlass.Config N :=
  if a = 0 then p.1 else p.2

/-- The four replica overlaps between two pair states. -/
noncomputable def pairOverlapMatrix {N : ℕ}
    (p r : SpinGlass.Config N × SpinGlass.Config N) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => SpinGlass.overlap N (pairConfig p a) (pairConfig r b)

lemma pairOverlapMatrix_self
    {N : ℕ} (hN : 0 < N) {v : ℝ} (p : ConstrainedPair N v) :
    pairOverlapMatrix p.1 p.1 = !![(1 : ℝ), v; v, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pairOverlapMatrix, pairConfig, SpinGlass.overlap_self N hN,
      p.2, overlap_comm]

lemma gtPathSign_sq (v : ℝ) : gtPathSign v ^ 2 = 1 := by
  unfold gtPathSign
  split <;> norm_num

lemma gtPathSign_mul_abs (v : ℝ) : gtPathSign v * |v| = v := by
  unfold gtPathSign
  by_cases hv : 0 ≤ v
  · simp [hv, abs_of_nonneg hv]
  · have hv' : v < 0 := lt_of_not_ge hv
    simp [hv, abs_of_neg hv']

lemma signedMatrixPath_zero (v : ℝ) :
    signedMatrixPath v 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [signedMatrixPath]

lemma signedMatrixPath_one {v : ℝ} (hv : |v| ≤ 1) :
    signedMatrixPath v 1 = !![(1 : ℝ), v; v, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [signedMatrixPath, min_eq_right hv, gtPathSign_mul_abs]

lemma pairOverlapMatrix_self_eq_signedMatrixPath_one
    {N : ℕ} (hN : 0 < N) {v : ℝ}
    (hv : v ∈ attainableOverlaps N) (p : ConstrainedPair N v) :
    pairOverlapMatrix p.1 p.1 = signedMatrixPath v 1 := by
  rw [pairOverlapMatrix_self hN]
  exact (signedMatrixPath_one (abs_le.2 (gtAttainableOverlap_mem_Icc hN hv))).symm

lemma gtIncrementScale_sq
    {β s lower upper : ℝ} (hs : 0 ≤ s) (hlu : lower ≤ upper) :
    gtIncrementScale β s lower upper ^ 2 =
      β ^ 2 * s * (upper - lower) := by
  unfold gtIncrementScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hs,
    Real.sq_sqrt (sub_nonneg.mpr hlu)]

/-- Exact quadratic remainder of the GT covariance function. -/
lemma gtCovariance_remainder (β q s x y : ℝ) :
    gtCovarianceFunction β q s x - gtCovarianceFunction β q s y -
        (β ^ 2 * (1 - s) * q + s * β ^ 2 * y) * (x - y) =
      s * β ^ 2 / 2 * (x - y) ^ 2 := by
  unfold gtCovarianceFunction
  ring

/-- The scalar compensation is the squared matrix-path norm. -/
lemma gtScalarVariance_eq_matrix_sum
    {β s v u : ℝ} (hu : 0 ≤ u) :
    gtScalarVariance β s v u =
      s * β ^ 2 / 2 * ∑ a : Fin 2, ∑ b : Fin 2,
        signedMatrixPath v u a b ^ 2 := by
  unfold gtScalarVariance
  by_cases hur : u ≤ |v|
  · rw [if_pos hur]
    have hmin : min u |v| = u := min_eq_left hur
    simp [signedMatrixPath, hmin]
    rw [mul_pow, gtPathSign_sq]
    ring
  · rw [if_neg hur]
    have hru : |v| ≤ u := le_of_lt (lt_of_not_ge hur)
    have hmin : min u |v| = |v| := min_eq_right hru
    simp [signedMatrixPath, hmin]
    rw [mul_pow, gtPathSign_sq, sq_abs]
    ring

lemma gtCorrection_finiteSum_q_le_abs
    {β q s v : ℝ} (hq0 : 0 ≤ q) (hqr : q ≤ |v|) (hr1 : |v| ≤ 1) :
    (1 / 2 : ℝ) * ((1 / 2) *
        (gtScalarVariance β s v |v| - gtScalarVariance β s v q) +
      (gtScalarVariance β s v 1 - gtScalarVariance β s v |v|)) =
        gtCorrection β q s := by
  unfold gtScalarVariance gtCorrection
  rw [if_pos hqr, if_pos le_rfl]
  by_cases hr : |v| = 1
  · rw [hr]
    simp
    ring
  · have hnot : ¬(1 : ℝ) ≤ |v| :=
      not_le.mpr (lt_of_le_of_ne hr1 hr)
    rw [if_neg hnot]
    rw [sq_abs]
    ring

lemma gtCorrection_finiteSum_abs_lt_q
    {β q s v : ℝ} (hrq : |v| < q) (hq1 : q ≤ 1) :
    (1 / 2 : ℝ) *
      (gtScalarVariance β s v 1 - gtScalarVariance β s v q) =
        gtCorrection β q s := by
  have hr1 : |v| < 1 := lt_of_lt_of_le hrq hq1
  unfold gtScalarVariance gtCorrection
  rw [if_neg (not_le.mpr hrq), if_neg (not_le.mpr hr1)]
  ring

/-- The four one-site spin weights are exactly the numerator defining `gtTerminal`. -/
lemma sum_bool_pair_exp_eq_four_mul_exp_gtTerminal
    (lam x₁ x₂ : ℝ) :
    (∑ p : Bool × Bool,
      Real.exp (x₁ * (if p.1 then 1 else -1) +
        x₂ * (if p.2 then 1 else -1) +
        lam * (if p.1 then 1 else -1) * (if p.2 then 1 else -1))) =
      4 * Real.exp (gtTerminal lam x₁ x₂) := by
  have hpos : 0 <
      (Real.exp (x₁ + x₂ + lam) +
        Real.exp (x₁ - x₂ - lam) +
        Real.exp (-x₁ + x₂ - lam) +
        Real.exp (-x₁ - x₂ + lam)) / 4 := by positivity
  rw [gtTerminal, Real.exp_log hpos]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring_nf

/-- The unrestricted pair partition function in deterministic site fields. -/
noncomputable def pairFieldPartition
    (N : ℕ) (lam v : ℝ) (x₁ x₂ : Fin N → ℝ) : ℝ :=
  ∑ p : SpinGlass.Config N × SpinGlass.Config N,
    Real.exp ((∑ i : Fin N, (
      x₁ i * SpinGlass.spin N p.1 i +
      x₂ i * SpinGlass.spin N p.2 i +
      lam * SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i)) -
        lam * (N : ℝ) * v)

lemma pairFieldPartition_eq
    (N : ℕ) (lam v : ℝ) (x₁ x₂ : Fin N → ℝ) :
    pairFieldPartition N lam v x₁ x₂ =
      Real.exp (-lam * (N : ℝ) * v) *
        ∏ i : Fin N, 4 * Real.exp (gtTerminal lam (x₁ i) (x₂ i)) := by
  classical
  unfold pairFieldPartition
  have hsplit :
      (∑ p : SpinGlass.Config N × SpinGlass.Config N,
        Real.exp ((∑ i : Fin N, (
          x₁ i * SpinGlass.spin N p.1 i +
          x₂ i * SpinGlass.spin N p.2 i +
          lam * SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i)) -
            lam * (N : ℝ) * v)) =
        Real.exp (-lam * (N : ℝ) * v) *
          ∑ p : SpinGlass.Config N × SpinGlass.Config N,
            Real.exp (∑ i : Fin N, (
              x₁ i * SpinGlass.spin N p.1 i +
              x₂ i * SpinGlass.spin N p.2 i +
              lam * SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  congr 1
  let f : Fin N → Bool × Bool → ℝ := fun i b =>
    x₁ i * (if b.1 then 1 else -1) +
      x₂ i * (if b.2 then 1 else -1) +
      lam * (if b.1 then 1 else -1) * (if b.2 then 1 else -1)
  calc
    (∑ p : SpinGlass.Config N × SpinGlass.Config N,
        Real.exp (∑ i : Fin N, (
          x₁ i * SpinGlass.spin N p.1 i +
          x₂ i * SpinGlass.spin N p.2 i +
          lam * SpinGlass.spin N p.1 i * SpinGlass.spin N p.2 i))) =
      ∏ i : Fin N, ∑ b : Bool × Bool, Real.exp (f i b) := by
        simpa [f, SpinGlass.spin] using sum_pair_exp_sum_eq_prod_sum_exp f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simpa [f] using
        sum_bool_pair_exp_eq_four_mul_exp_gtTerminal lam (x₁ i) (x₂ i)

lemma pairFieldPartition_pos
    (N : ℕ) (lam v : ℝ) (x₁ x₂ : Fin N → ℝ) :
    0 < pairFieldPartition N lam v x₁ x₂ := by
  rw [pairFieldPartition_eq]
  positivity

lemma log_pairFieldPartition
    (N : ℕ) (lam v : ℝ) (x₁ x₂ : Fin N → ℝ) :
    Real.log (pairFieldPartition N lam v x₁ x₂) =
      2 * (N : ℝ) * Real.log 2 +
        ∑ i : Fin N, gtTerminal lam (x₁ i) (x₂ i) -
          lam * (N : ℝ) * v := by
  rw [pairFieldPartition_eq, Real.log_mul (Real.exp_ne_zero _) (by positivity),
    Real.log_exp, Real.log_prod (fun i _ => by positivity)]
  simp_rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show Real.log (4 : ℝ) = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring]
  ring

end SpinGlass.AT
