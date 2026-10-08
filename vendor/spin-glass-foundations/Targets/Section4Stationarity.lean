module

public import Targets.Section4UEndpoints
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
# Endpoint optimality for the actual Section 4 variance factor

The normalized factor remains meaningful when the inserted variance is zero.
The left overlap variation gives one of the two inequalities in Proposition 4.7;
it is an actual consequence of fixed-level minimality, not an assumed
stationarity condition. The opposite variation is a separate obligation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace SpinGlass.Targets

/-- At zero variance the spatial derivative is the original spatial derivative,
including mass zero. -/
theorem stepD1_parisiF_zero_variance {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (m x : ℝ) :
    stepD1 (parisiF s β j) (parisiFDeriv s β j) m 0 x = parisiFDeriv s β j x := by
  have H := hasDerivAt_parisiStep_spatial (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) (parisiF_C2_props s β j).2.1
    (parisiF_C2_props s β j).1.1 (parisiF_C2_props s β j).1.abs_first_le_one m 0 x
  have he : parisiStep m 0 (parisiF s β j) = parisiF s β j := by
    funext y
    exact parisiStep_zero_var m _ y
  rw [he] at H
  exact H.unique ((parisiF_C2_props s β j).1.1 x)

/-- Every outer potential at zero split variance is independent of the new mass. -/
theorem section4Cascade_zero_variance_mass_independent {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m m' : ℝ)
    {j : ℕ} (hj : j ≤ r - 1) :
    scalarFieldCascade (fun l => section4Mass s r m (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) 0) (k + 2 - r + 2 + j) =
    scalarFieldCascade (fun l => section4Mass s r m' (k + 2 - l))
      (fun l => section5Variance s β r (k + 2 - l) 0) (k + 2 - r + 2 + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, section4Cascade_split s β hr0 hr]
    congr 1
    funext x
    simp only [parisiStep_zero_var]
  | succ j ih =>
    rw [show k + 2 - r + 2 + (j + 1) = (k + 2 - r + 2 + j) + 1 by omega,
      scalarFieldCascade, scalarFieldCascade, ih (by omega)]
    have hp : k + 2 - (k + 2 - r + 2 + j) < r := by omega
    simp only [section4Mass, if_pos hp]

/-- The normalized endpoint observable is independent of the inserted mass;
there is no division by a mass gap. -/
theorem section4VarianceQ_zero_mass_independent {k : ℕ} (s : RSBScheme k) (β : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m m' : ℝ)
    {j : ℕ} (hj : j ≤ r - 1) (x y : Fin 1 → ℝ) :
    section4VarianceQ s β r m j 0 x y = section4VarianceQ s β r m' j 0 x y := by
  induction j generalizing x y with
  | zero =>
    simp only [section4VarianceQ, parisiStep_zero_var, stepD1_parisiF_zero_variance]
  | succ j ih =>
    have hF := section4Cascade_zero_variance_mass_independent s β hr0 hr m m'
      (j := j) (by omega)
    have hQ : section4VarianceQ s β r m j 0 = section4VarianceQ s β r m' j 0 := by
      funext x y
      exact ih (by omega) x y
    simp only [section4VarianceQ, hF, hQ]

theorem section4TVarianceQ_zero_mass_independent {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (m m' : ℝ) :
    section4TVarianceQ s β h r m 0 = section4TVarianceQ s β h r m' 0 :=
  section4VarianceQ_zero_mass_independent s β hr0 hr m m' le_rfl _ _

/-- The actual variance derivative of T extends inward to both endpoints.
The closed-interval statement does not assert a two-sided endpoint derivative. -/
theorem hasDerivWithinAt_section4T_variance_factor {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {v : ℝ}
    (hv : v ∈ Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) :
    HasDerivWithinAt (section4T s β h r m)
      ((m - s.m (r - 1)) / 2 * section4TVarianceQ s β h r m v)
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) v := by
  let a := β ^ 2 * (s.q r - s.q (r - 1))
  have ha : 0 ≤ a := hv.1.trans hv.2
  let Q := section4TVarianceQ s β h r m
  let Qe : ℝ → ℝ := fun z => Q (Set.projIcc 0 a ha z)
  have hc : ContinuousOn Q (Set.Icc 0 a) :=
    continuousOn_section4TVarianceQ_variance s β h hr0 hr hm
  have hce : Continuous Qe := hc.restrict.comp continuous_projIcc
  have heq (z : ℝ) (hz : z ∈ Set.Icc 0 a) : Qe z = Q z := by
    simp only [Qe, Set.projIcc_of_mem ha hz]
  have hT (z : ℝ) (hz : z ∈ Set.Icc 0 a) :
      section4T s β h r m z = section4T s β h r m 0 +
        (m - s.m (r - 1)) / 2 * ∫ w in (0 : ℝ)..z, Qe w := by
    have H := section4T_sub_eq_massGap_mul_integral s β h hr0 hr hm hmm
      (v := 0) ⟨le_rfl, ha⟩ hz hz.1
    have HI : (∫ w in (0 : ℝ)..z, Qe w) = ∫ w in (0 : ℝ)..z, Q w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le hz.1] at hw
      exact heq w ⟨hw.1, hw.2.trans hz.2⟩
    rw [HI]
    linarith
  have H := ((intervalIntegral.integral_hasDerivAt_right (hce.intervalIntegrable 0 v)
    hce.stronglyMeasurable.stronglyMeasurableAtFilter hce.continuousAt).const_mul
      ((m - s.m (r - 1)) / 2)).const_add (section4T s β h r m 0)
  rw [heq v hv] at H
  exact H.hasDerivWithinAt.congr_of_mem hT hv

/-- The overlap derivative of the actual inserted functional, on the closed
admissible interval. This is (4.55) with the correction differentiated. -/
theorem hasDerivWithinAt_section4Phi_overlap {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m : ℝ}
    (hm : m ∈ Set.Icc 0 1) (hmm : s.m (r - 1) ≤ m) {u : ℝ}
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) :
    HasDerivWithinAt (section4Phi s β h r m)
      (β ^ 2 * (m - s.m (r - 1)) / 2 *
        (u - section4TVarianceQ s β h r m (β ^ 2 * (s.q r - u))))
      (Set.Icc (s.q (r - 1)) (s.q r)) u := by
  have hmap : Set.MapsTo (fun z => β ^ 2 * (s.q r - z))
      (Set.Icc (s.q (r - 1)) (s.q r))
      (Set.Icc 0 (β ^ 2 * (s.q r - s.q (r - 1)))) := by
    intro z hz
    exact ⟨mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left (by linarith [hz.1]) (sq_nonneg β)⟩
  have H := (hasDerivWithinAt_section4T_variance_factor s β h hr0 hr hm hmm
    (hmap hu)).comp u
      (((hasDerivAt_id u).const_sub (s.q r)).const_mul (β ^ 2)).hasDerivWithinAt hmap
  have HP := (((((hasDerivAt_id u).pow 2).const_sub (s.q r ^ 2)).const_mul
    (β ^ 2 / 4)).const_mul (s.m (r - 1) - m)).hasDerivWithinAt
      (s := Set.Icc (s.q (r - 1)) (s.q r))
  convert! ((H.const_add (Real.log 2)).sub_const (parisiCorrection s β)).add HP using 1
  simp only [id_eq]
  ring

/-- A minimum at the right endpoint forces the inward derivative to be
nonpositive. This reuses Mathlib's tangent-cone version of Fermat's theorem. -/
theorem derivative_nonpos_of_min_at_right {f : ℝ → ℝ} {a b d : ℝ}
    (hab : a < b) (hmin : ∀ x ∈ Set.Icc a b, f b ≤ f x)
    (hd : HasDerivWithinAt f d (Set.Icc a b) b) : d ≤ 0 := by
  have hlocal : IsLocalMinOn f (Set.Icc a b) b :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  have ht : a - b ∈ posTangentConeAt (Set.Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨hab.le, le_rfl⟩ ⟨le_rfl, hab.le⟩)
  have H := hlocal.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt ht
  change 0 ≤ (a - b) * d at H
  nlinarith

/-- Left-half stationarity for an actual fixed-level minimizer. A positive
overlap gap is needed only to have an inward direction at the upper endpoint. -/
theorem section4_overlap_le_endpointQ_of_min {k : ℕ} (s : RSBScheme k) (β h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) (hβ : β ≠ 0)
    (hm : s.m (r - 1) < s.m r) (hq : s.q (r - 1) < s.q r)
    (hmin : ∀ s' : RSBScheme k, parisiFunctional s β h ≤ parisiFunctional s' β h) :
    s.q r ≤ section4TVarianceQ s β h r (s.m (r - 1)) 0 := by
  have hd := hasDerivWithinAt_section4Phi_overlap s β h hr0 hr
    ⟨s.m_nonneg hr, s.m_le_one hr⟩ hm.le (u := s.q r) ⟨hq.le, le_rfl⟩
  simp only [sub_self, mul_zero] at hd
  rw [section4TVarianceQ_zero_mass_independent s β h hr0 hr (s.m r) (s.m (r - 1))] at hd
  have H := derivative_nonpos_of_min_at_right hq (f := section4Phi s β h r (s.m r))
    (fun u hu => by
      rw [section4Phi_at_upper_overlap s β h hr0 hr]
      simpa only [section4Phi_baseline s β h hr0 hr hu] using
        section4Phi_upper_mass_min s β h hr0 hr hu hmin) hd
  have hc : 0 < β ^ 2 * (s.m r - s.m (r - 1)) / 2 :=
    div_pos (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hm)) (by norm_num)
  nlinarith

end SpinGlass.Targets
