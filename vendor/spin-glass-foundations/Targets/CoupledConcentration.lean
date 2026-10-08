module

/- Compatibility adaptation: set-membership reduction may already be complete after modern elaboration. -/
/-
# Gaussian concentration for the coupled pressure gap

We realise the SK covariance using its spectral coefficients, together with
independent coordinates for the shared outer field. The resulting Lipschitz
bound is uniform in the interpolation time, overlap, cascade depth and split.
-/
public import Targets.CoupledLipschitz
public import Targets.CoupledMeasurability
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped BigOperators NNReal

namespace SpinGlass.Targets

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n k : ℕ}

/-- Standard Gaussian coordinates for the disorder and the shared outer field. -/
abbrev CoupledGaussianSpace (sk : SKDisorder (Ω := Ω) n β h) :=
  EuclideanSpace ℝ (sk.hU.ι ⊕ Fin n)

/-- The spectral SK Hamiltonian evaluated on independent standard coordinates. -/
noncomputable def coupledGaussianU (sk : SKDisorder (Ω := Ω) n β h)
    (z : CoupledGaussianSpace sk) : EnergySpace n :=
  ∑ i, (Real.sqrt (sk.hU.τ i) * z (Sum.inl i)) • sk.hU.w i

/-- The remaining shared field, whose variance is `β² q₁`. -/
noncomputable def coupledGaussianX (sk : SKDisorder (Ω := Ω) n β h) (s : RSBScheme k)
    (z : CoupledGaussianSpace sk) (i : Fin n) : ℝ :=
  Real.sqrt (β ^ 2 * s.q 1) * z (Sum.inr i)

/-- Coefficients of one interpolated Hamiltonian in all its external coordinates. -/
noncomputable def coupledGaussianCoeff (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t : ℝ) (σ : Config n) : CoupledGaussianSpace sk :=
  WithLp.toLp 2 (Sum.elim
    (fun i => Real.sqrt t * Real.sqrt (sk.hU.τ i) * sk.hU.w i σ)
    (fun i => Real.sqrt (1 - t) * Real.sqrt (β ^ 2 * s.q 1) * spin n σ i))

theorem coupledGaussianCoeff_norm_sq (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Config n) :
    ‖coupledGaussianCoeff sk s t σ‖ ^ 2 =
      t * (n * β ^ 2 / 2) + (1 - t) * (β ^ 2 * s.q 1) * n := by
  have hq := s.q_nonneg (show 1 ≤ k + 2 by omega)
  have hspin : ∀ i, (spin n σ i) ^ 2 = 1 := by
    intro i
    simp only [spin]
    split_ifs <;> norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [coupledGaussianCoeff, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_pow, Real.sq_sqrt ht.1, Real.sq_sqrt (sub_nonneg.mpr ht.2),
    Real.sq_sqrt (mul_nonneg (sq_nonneg β) hq), Real.sq_sqrt (NNReal.coe_nonneg _), hspin,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc := sk_covariance_spectral_sum β h sk σ σ
  rw [sk_cov_kernel, overlap_self n hn σ, one_pow, mul_one] at hc
  have he : (∑ i : sk.hU.ι, t * (sk.hU.τ i : ℝ) * (sk.hU.w i σ) ^ 2) =
      t * ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * (sk.hU.w i σ * sk.hU.w i σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hc]
  ring

/-- The deliberately loose constant is positive even at `β = 0`. -/
noncomputable def coupledGaussianLip (n : ℕ) (β : ℝ) : ℝ :=
  (1 + |β|) * Real.sqrt n

theorem coupledGaussianLip_pos {n : ℕ} (hn : 0 < n) (β : ℝ) :
    0 < coupledGaussianLip n β :=
  mul_pos (by positivity) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))

theorem coupledGaussianCoeff_norm_le (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Config n) : ‖coupledGaussianCoeff sk s t σ‖ ≤ coupledGaussianLip n β := by
  have hq0 := s.q_nonneg (show 1 ≤ k + 2 by omega)
  have hq1 := s.q_le_one (show 1 ≤ k + 2 by omega)
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb : 0 ≤ β ^ 2 := sq_nonneg β
  have hbound : ‖coupledGaussianCoeff sk s t σ‖ ^ 2 ≤ (n : ℝ) * β ^ 2 := by
    rw [coupledGaussianCoeff_norm_sq sk s hn ht σ]
    have H := mul_le_mul_of_nonneg_left hq1 (mul_nonneg (sub_nonneg.mpr ht.2) hb)
    have H' := mul_le_mul_of_nonneg_right H hN
    nlinarith [mul_nonneg ht.1 (mul_nonneg hN hb)]
  have hL := (coupledGaussianLip_pos hn β).le
  have hs := Real.sq_sqrt hN
  have ha : |β| ^ 2 = β ^ 2 := sq_abs β
  have hLsq : (n : ℝ) * β ^ 2 ≤ (coupledGaussianLip n β) ^ 2 := by
    unfold coupledGaussianLip
    rw [mul_pow, hs]
    nlinarith [mul_nonneg hN (abs_nonneg β)]
  nlinarith [norm_nonneg (coupledGaussianCoeff sk s t σ)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem guerraH_coupledGaussian_eq (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t : ℝ) (a : Fin n → ℝ) (σ : Config n) (z : CoupledGaussianSpace sk) :
    guerraH n (coupledGaussianU sk z) h t (a + coupledGaussianX sk s z) σ =
      inner ℝ (coupledGaussianCoeff sk s t σ) z +
        ∑ i, spin n σ i * (Real.sqrt (1 - t) * a i + h) := by
  simp only [guerraH, coupledGaussianU, coupledGaussianX, coupledGaussianCoeff,
    PiLp.inner_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    RCLike.inner_apply, conj_trivial, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, Pi.add_apply]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm]

theorem guerraH_coupledGaussian_lipschitz (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin n → ℝ) (σ : Config n) :
    LipschitzWith (coupledGaussianLip n β).toNNReal
      (fun z => guerraH n (coupledGaussianU sk z) h t (a + coupledGaussianX sk s z) σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [guerraH_coupledGaussian_eq, add_sub_add_right_eq_sub,
    ← inner_sub_right, Real.coe_toNNReal _ (coupledGaussianLip_pos hn β).le, dist_eq_norm]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (coupledGaussianCoeff_norm_le sk s hn ht σ) (norm_nonneg _))

/-- The actual constrained/unrestricted gap in standard Gaussian coordinates. -/
noncomputable def gaussianCoupledGap (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t u : ℝ) (d j : ℕ) (z : CoupledGaussianSpace sk) : ℝ :=
  coupledGap n s β (coupledGaussianU sk z) h t u d j (coupledGaussianX sk s z)

theorem gaussianCoupledGap_lipschitz (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    LipschitzWith (4 * coupledGaussianLip n β).toNNReal (gaussianCoupledGap sk s t u d j) := by
  have H := coupledGap_lipschitz s β h u ht hu d j (coupledGaussianU sk) (coupledGaussianX sk s)
    (guerraH_coupledGaussian_lipschitz sk s hn ht)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [gaussianCoupledGap, Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 4), Real.toNNReal_ofNat] using!
    H.dist_le_mul z w

/-- Gaussian upper tail, with a variance proxy linear in `n`. No concentration
hypothesis is assumed: the Lipschitz estimate above supplies it. -/
theorem gaussianCoupledGap_upper_tail (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)).real
      {z | a ≤ gaussianCoupledGap sk s t u d j z -
        ∫ w, gaussianCoupledGap sk s t u d j w
          ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)} ≤
      Real.exp (-a ^ 2 / (32 * (1 + |β|) ^ 2 * n)) := by
  have H := (SYK.product_standardGaussian_hasSubgaussianMGF (gaussianCoupledGap sk s t u d j)
    (4 * coupledGaussianLip n β) (mul_pos (by norm_num) (coupledGaussianLip_pos hn β))
    (gaussianCoupledGap_lipschitz sk s hn ht u hu d j)).measure_ge_le ha
  rw [Real.coe_toNNReal _ (sq_nonneg _)] at H
  have he : 2 * (4 * coupledGaussianLip n β) ^ 2 = 32 * (1 + |β|) ^ 2 * n := by
    unfold coupledGaussianLip
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  rwa [he] at H

theorem integrable_gaussianCoupledGap (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    Integrable (gaussianCoupledGap sk s t u d j)
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) := by
  have H := (SYK.product_standardGaussian_hasSubgaussianMGF (gaussianCoupledGap sk s t u d j)
    (4 * coupledGaussianLip n β) (mul_pos (by norm_num) (coupledGaussianLip_pos hn β))
    (gaussianCoupledGap_lipschitz sk s hn ht u hu d j)).integrable
  simpa only [Pi.add_def, sub_add_cancel] using H.add (integrable_const
    (∫ z, gaussianCoupledGap sk s t u d j z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)))

/-- Splitting at `F = -r` converts an exponential comparison into an expectation bound. -/
theorem integral_event_le_exp_add_tail {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {F Q : E → ℝ} {m r : ℝ}
    (hF : Measurable F) (hQ : Measurable Q) (hm : 0 ≤ m)
    (hQ0 : ∀ z, 0 ≤ Q z) (hQ1 : ∀ z, Q z ≤ 1)
    (hQF : ∀ z, Q z ≤ Real.exp (m * F z)) :
    (∫ z, Q z ∂μ) ≤ Real.exp (-m * r) + μ.real {z | -r ≤ F z} := by
  let S : Set E := {z | -r ≤ F z}
  have hS : MeasurableSet S := measurableSet_le measurable_const hF
  have hQi : Integrable Q μ := (integrable_const (1 : ℝ)).mono' hQ.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_of_nonneg (hQ0 z)] using hQ1 z))
  have hI : Integrable (fun z => Real.exp (-m * r) + S.indicator (fun _ => (1 : ℝ)) z) μ :=
    (integrable_const _).add ((integrable_const _).indicator hS)
  have H := integral_mono hQi hI (fun z => show Q z ≤ _ from by
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz]
      linarith [hQ1 z, Real.exp_pos (-m * r)]
    · simp only [Set.indicator_of_notMem hz, add_zero]
      apply (hQF z).trans
      apply Real.exp_le_exp.mpr
      have hz' : F z < -r := lt_of_not_ge hz
      nlinarith)
  have hc : Integrable (fun _ : E => Real.exp (-m * r)) μ := integrable_const _
  have hi : Integrable (S.indicator (fun _ : E => (1 : ℝ))) μ :=
    (integrable_const _).indicator hS
  rw [integral_add hc hi, integral_const, probReal_univ, one_smul] at H
  have he : (∫ z, S.indicator (fun _ : E => (1 : ℝ)) z ∂μ) = μ.real S :=
    integral_indicator_one hS
  rwa [he] at H

/-- The weighted overlap event before the last, zero-mass Gaussian average. -/
noncomputable def gaussianCoupledEvent (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t u : ℝ) (d : ℕ) (z : CoupledGaussianSpace sk) : ℝ :=
  coupledObservable n s β (coupledGaussianU sk z) h t d (overlapEvent n u) (k + 1)
    (coupledGaussianX sk s z) (coupledGaussianX sk s z)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurable_gaussianCoupledEvent (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (t u : ℝ) (d : ℕ) : Measurable (gaussianCoupledEvent sk s t u d) := by
  have hU : Measurable (coupledGaussianU sk) := by unfold coupledGaussianU; fun_prop
  have hX : Measurable (coupledGaussianX sk s) := by unfold coupledGaussianX; fun_prop
  exact (measurable_coupledObservable_joint s β h t d (overlapEvent n u) (k + 1)).comp
    (f := fun z : CoupledGaussianSpace sk =>
      (coupledGaussianU sk z, (coupledGaussianX sk s z, coupledGaussianX sk s z)))
    (hU.prodMk (hX.prodMk hX))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integrable_gaussianCoupledEvent (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) :
    Integrable (gaussianCoupledEvent sk s t u d)
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_gaussianCoupledEvent sk s t u d).aestronglyMeasurable ?_
  filter_upwards with z
  unfold gaussianCoupledEvent
  rw [Real.norm_of_nonneg (le_of_lt
    (coupledEvent_pos s hs β _ h u ht hu d (k + 1) (by omega) _ _))]
  exact coupledEvent_le_one s hs β _ h u ht hu d (k + 1) le_rfl _ _

/-- The concentration/expectation conclusion of Lemma 2.6 in standard Gaussian
coordinates. Its mean hypothesis and conclusion are transferred to `sk.U` in
`Targets.CoupledOuterExpectation`; this theorem does not assume a concentration bound. -/
theorem gaussianCoupledEvent_small (sk : SKDisorder (Ω := Ω) n β h)
    (s : RSBScheme k) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ z, gaussianCoupledGap sk s t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ≤ -ε * n) :
    (∫ z, gaussianCoupledEvent sk s t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) +
        Real.exp (-(ε ^ 2 / (128 * (1 + |β|) ^ 2)) * n) := by
  let μ := SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)
  let F := gaussianCoupledGap sk s t u d (k + 1)
  let Q := gaussianCoupledEvent sk s t u d
  have hF : Measurable F := (gaussianCoupledGap_lipschitz sk s hn ht u hu d (k + 1)).continuous.measurable
  have hm := coupledMass_pos s hs d (k + 1) le_rfl
  have hsplit := integral_event_le_exp_add_tail μ hF
    (measurable_gaussianCoupledEvent sk s t u d) hm.le
    (fun z => (coupledEvent_pos s hs β _ h u ht hu d (k + 1) (by omega) _ _).le)
    (fun z => coupledEvent_le_one s hs β _ h u ht hu d (k + 1) le_rfl _ _)
    (fun z => coupledEvent_le_exp_gap s hs β _ h u ht hu d (k + 1) le_rfl _ _)
    (r := ε * n / 2)
  have htail := gaussianCoupledGap_upper_tail sk s hn ht u hu d (k + 1)
    (a := ε * n / 2) (by positivity)
  have hset : {z | -(ε * n / 2) ≤ F z} ⊆ {z | ε * n / 2 ≤ F z - ∫ w, F w ∂μ} := by
    intro z hz
    try dsimp only [Set.mem_ofPred_eq] at hz ⊢
    change (∫ z, F z ∂μ) ≤ -ε * n at hmean
    linarith
  have hmass : s.m 1 / 2 ≤ coupledMass s d (k + 1) := by
    simp only [coupledMass, Nat.add_sub_cancel_left]
    split_ifs <;> linarith
  have hexp : Real.exp (-coupledMass s d (k + 1) * (ε * n / 2)) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hmass (show 0 ≤ ε * n by positivity)]
  have he : -(ε * (n : ℝ) / 2) ^ 2 / (32 * (1 + |β|) ^ 2 * n) =
      -(ε ^ 2 / (128 * (1 + |β|) ^ 2)) * n := by
    have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    have hb : (1 + |β|) ≠ 0 := by positivity
    field_simp
    ring
  rw [he] at htail
  exact hsplit.trans (add_le_add hexp ((measureReal_mono hset).trans htail))

end SpinGlass.Targets
